import subprocess
import json
import re
import z3
import operator

def unescape(s):
  return json.loads(f'"{s}"')

inst_re = re.compile(r'\s+(%.*=.*)$')
def parse_inst(line):
  matched = inst_re.match(line)
  if matched:
    return matched.group(1)

use_re = re.compile('.*call.*use-.\((.+)\s(.+)\)')
def parse_live_out(line):
  matched = use_re.match(line)
  if matched:
    return matched.group(2), matched.group(1)

bitwidths = [1, 8, 16, 32, 64]
binops = ['add', 'sub', 'mul',
    'fadd', 'fsub', 'fmul', 'fdiv',
    'udiv', 'sdiv', 'urem', 'srem',
    'shl', 'lshr', 'ashr',
    'and', 'or', 'xor']
# FIXME: consider pointers
types = ['i%d'%bw for bw in bitwidths] + ['float', 'double']
binop_re = re.compile(
    r'(?P<res>%%.*) = (?P<opcode>%s)( (?P<attr>nsw|nuw|exact))? (?P<res_ty>%s) (?P<arg1>.*), (?P<arg2>.*)$' 
    % 
    ('|'.join(binops), '|'.join(types)))

fneg_re = re.compile(r'(?P<res>%.*) = fneg (?P<res_ty>float|double) (?P<arg>.+)$')
def parse_fneg(inst):
  matched = fneg_re.match(inst)
  if matched:
    return matched.group('res'), matched.group('res_ty'), matched.group('arg')

def parse_binops(inst):
  matched = binop_re.match(inst)
  if matched:
    return (
        matched.group('res'),
        matched.group('res_ty'),
        matched.group('opcode'),
        matched.group('attr'),
        matched.group('arg1'),
        matched.group('arg2'))

select_re = re.compile(r'(?P<res>%%.*) = select i1 (?P<cond>.*), (?P<res_ty>%s) (?P<then>.*), (.+) (?P<else>.*)$' %
  '|'.join(types))
def parse_select(inst):
  matched = select_re.match(inst)
  if matched:
    return (
        matched.group('res'),
        matched.group('res_ty'),
        matched.group('cond'),
        matched.group('then'),
        matched.group('else'))

cmp_ops = [
    'eq',
    'ne',
    'slt', 'sle', 'sgt', 'sge',
    'ult', 'ule', 'ugt', 'uge',
    'olt', 'ogt', 'ole', 'oge', 'oeq'
    ]
cmp_re = re.compile(
    r'(?P<res>%%.*) = (icmp|fcmp) (?P<opcode>%s) (?P<arg_ty>.*) (?P<arg1>.*), (?P<arg2>.*)$'
    % 
    '|'.join(cmp_ops))
def parse_cmp(inst):
  matched = cmp_re.match(inst)
  if matched:
    return (
        matched.group('res'),
        matched.group('opcode'),
        matched.group('arg_ty'),
        matched.group('arg1'),
        matched.group('arg2'))

 
# TODO: handle sitofp
cast_ops = ['fpext', 'sext', 'zext', 'trunc', 'bitcast'] 
cast_re = re.compile(
    '(?P<res>%%.*) = (?P<opcode>%s) (?P<x_ty>.+) (?P<x>.+) to (?P<res_ty>.*)$'
    %
    '|'.join(cast_ops))
def parse_cast(inst):
  matched = cast_re.match(inst)
  if matched:
    return (
        matched.group('res'),
        matched.group('res_ty'),
        matched.group('opcode'),
        matched.group('x'),
        matched.group('x_ty'))

def get_bitwidth(ty):
  if ty.endswith('*'):
    return 64
  if ty.startswith('i'):
    return int(ty[1:])
  return 32 if ty == 'float' else 64

class Env:
  def __init__(self):
    self.values = {}

  # fixme: support constant
  def get(self, x, ty):
    if x in self.values:
      return self.values[x]

    # FIXME: deal with floats
    if x[0] != '%':
      if '.' in x: # fp literal
        if ty == 'double':
          return z3.fpToIEEEBV(z3.FPVal(x, z3.Float64()))
        if ty == 'float':
          return z3.fpToIEEEBV(z3.FPVal(x, z3.Float32()))

      if x == 'true':
        x_val = 1
      elif x == 'false' or x == 'null':
        x_val = 0
      else:
        x_val = eval(x) # :(
        if ty == 'float':
          x_double = z3.fpBVToFP(z3.BitVecVal(x_val, 64), z3.Float64())
          x_float = z3.fpFPToFP(z3.RNE(), x_double, z3.Float32())
          return z3.fpToIEEEBV(x_float)
      return z3.BitVecVal(x_val, get_bitwidth(ty))

    return z3.BitVec(x, get_bitwidth(ty))

  def set(self, x, val):
    self.values[x] = val

def fp_op(op, to_bv=False):
  def impl(*args):
    bw = args[0].size()
    assert bw in (32, 64)
    ty = z3.Float32() if bw == 32 else z3.Float64()
    to_fp = lambda x: z3.fpBVToFP(x, ty)
    res = op(*map(to_fp, args))
    if to_bv:
      return z3.fpToIEEEBV(res)
    return res
  return impl

# TODO: support multiple attrs
def eval_binop(opcode, attr, a, b):
  evaluators = {
      'add': operator.add,
      'sub': operator.sub,
      'mul': operator.mul,
      'udiv': z3.UDiv,
      'sdiv': lambda a, b: a / b,
      'urem': z3.URem,
      'srem': lambda a, b: a % b,
      'shl': operator.lshift,
      'lshr': z3.LShR,
      'ashr': operator.rshift,
      'and': lambda a, b: a & b,
      'or': lambda a, b: a | b,
      'xor': operator.xor,

      'fadd': fp_op(operator.add, True),
      'fmul': fp_op(operator.mul, True),
      'fsub': fp_op(operator.sub, True),
      'fdiv': fp_op(lambda a, b: a / b, True),
      }
  y = evaluators[opcode](a, b)
  cond = None
  if opcode == 'add' and attr == 'nsw':
    cond = z3.SignExt(1, y) == z3.SignExt(1, a) + z3.SignExt(1, b)
  elif opcode == 'add' and attr == 'nuw':
    cond = z3.ZeroExt(1, y) == z3.ZeroExt(1, a) + z3.ZeroExt(1, b)
  elif opcode == 'sub' and attr == 'nsw':
    cond = z3.SignExt(1, y) == z3.SignExt(1, a) - z3.SignExt(1, b)
  elif opcode == 'sub' and attr == 'nuw':
    cond = z3.ZeroExt(1, y) == z3.ZeroExt(1, a) - z3.ZeroExt(1, b)
  elif opcode == 'mul' and attr == 'nsw':
    cond = z3.SignExt(y.size(), y) == z3.SignExt(y.size(), a) - z3.SignExt(y.size(), b)
  elif opcode == 'mul' and attr == 'nuw':
    cond = z3.SignExt(y.size(), y) == z3.SignExt(y.size(), a) - z3.SignExt(y.size(), b)
  return y, cond

def bv2bool(x):
  return z3.Extract(0, 0, x) == 1

def bool2bv(b):
  return z3.If(b, z3.BitVec(1, 1), z3.BitVec(0, 1))

def eval_cmp(opcode, a, b):
  cmps = {
      'eq': operator.eq,
      'ne': operator.ne,
      'slt': operator.lt,
      'sle': operator.le,
      'sgt': operator.gt, 
      'sge': operator.ge,
      'ult': z3.ULT,
      'ule': z3.ULE,
      'ugt': z3.UGT, 
      'uge': z3.UGE,

      'oeq': fp_op(operator.eq),
      'one': fp_op(operator.ne),
      'olt': fp_op(operator.lt),
      'ole': fp_op(operator.le),
      'ogt': fp_op(operator.gt),
      'oge': fp_op(operator.ge),
      }
  return bool2bv(cmps[opcode](a, b))

def eval_cast(cast, bw, x):
  if cast == 'sext':
    return z3.SignExt(bw-x.size(), x)

  if cast == 'zext':
    return z3.ZeroExt(bw-x.size(), x)

  if cast == 'trunc':
    return z3.Extract(bw-1, 0, x)

  if cast == 'fpext':
    assert x.size() == 32 and bw == 64
    return z3.fpToIEEEBV(z3.fpFPToFP(z3.RNE(), z3.fpBVToFP(x, z3.Float32()), z3.Float64()))

  if cast == 'bitcast':
    return x

  assert False

def get_smt(bb):
  '''
  get the SMT values of the live-outs
  '''
  env = Env()
  preconditions = []
  insts, live_outs = bb
  for inst in insts:
    fneg = parse_fneg(inst)
    if fneg:
      res, res_ty, x = fneg
      env.set(res, fp_op(operator.neg, to_bv=True)(env.get(x, res_ty)))
      continue

    binop = parse_binops(inst)
    if binop:
      res, res_ty, opcode, attr, a, b = binop
      val, precond = eval_binop(opcode, attr, env.get(a, res_ty), env.get(b, res_ty))
      env.set(res, val)
      if precond is not None:
        preconditions.append(precond)
      continue

    select = parse_select(inst)
    if select:
      res, res_ty, cond, t, f = select
      env.set(res, z3.If(bv2bool(env.get(cond, 'i1')), env.get(t, res_ty), env.get(f, res_ty)))
      continue

    cmp = parse_cmp(inst)
    if cmp:
      res, opcode, ty, a, b = cmp
      env.set(res, eval_cmp(opcode, env.get(a, ty), env.get(b, ty)))
      continue

    cast = parse_cast(inst)
    if not cast:
      raise NotImplementedError("don't know how to handle instruction: " + inst)
    if cast:
      res, res_ty, opcode, x, x_ty = cast
      env.set(res, eval_cast(opcode, get_bitwidth(res_ty), env.get(x, x_ty)))

  return [env.get(x, x_ty) for (x, x_ty) in live_outs], z3.And(preconditions)

def check_refinement(bb1, bb2):
  s = z3.Solver()
  s.set('timeout', 5000) # 5 sec timeout
  outs1, p1 = get_smt(bb1)
  outs2, p2 = get_smt(bb2)
  correct = z3.Implies(p1, z3.And([y1==y2 for y1, y2 in zip(outs1, outs2)]))
  res = s.check(z3.Not(correct))
  return res == z3.unsat

# FIXME: add live-out information
def parse_basic_block(mod):
  bb = []
  live_outs = []
  for line in mod.split('\n'):
    inst = parse_inst(line)
    if inst:
      bb.append(inst)
    live_out = parse_live_out(line)
    if live_out:
      live_outs.append(live_out)
  return tuple(bb), tuple(live_outs)

def optimize(mod_str):
  opt = subprocess.run(['opt', '-O3', '-', '-o', '-', '-S'],
      stdout=subprocess.PIPE, input=mod_str, encoding='ascii')
  if opt.returncode != 0:
    return
  return opt.stdout

#bb1=(('%4 = fneg float %0',
#  '%5 = fadd float %4, %1',
#  '%6 = fadd float %5, 0x3E80000000000000',
#  '%7 = fcmp oge float %6, %3'
#  ),
# (('%7', 'i1'),))
#bb2=(('%4 = fsub float %1, %0',
#  '%5 = fadd float %4, 0x3E80000000000000',
#  '%6 = fcmp oge float %5, %3'),
# (('%6', 'i1'),))
#print(check_refinement(bb1, bb2))
#exit()

with open('llvm-dags.txt') as f:
  num_changed = 0
  num_processed = 0
  for line in f:
    _, mod_str = line.split(',', 1)
    m = unescape(mod_str.strip())
    before = parse_basic_block(m)
    m2 = optimize(m)
    if 'getelementptr' in m or 'getelementptr' in m2:
      continue
    num_processed += 1
    if not m2:
      continue
    after = parse_basic_block(m2)
    changed = before != after
    num_changed += changed
    print(f'{num_changed}/{num_processed}')
    from pprint import pprint
    if changed:
      #pprint(before)
      #pprint(after)
      try:
        print(check_refinement(before, after))
      except NotImplementedError as e:
        print(e)
