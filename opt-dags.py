import subprocess
import json
import re

def unescape(s):
  return json.loads(f'"{s}"')

inst_re = re.compile(r'\s+(%.*=.*)$')
def parse_basic_block(mod):
  bb = []
  for line in mod.split('\n'):
    matched = inst_re.match(line)
    if matched:
      bb.append(matched.group(1))
  return tuple(bb)


def optimize(mod_str):
  opt = subprocess.run(['opt', '-O3', '-', '-o', '-', '-S'],
      stdout=subprocess.PIPE, input=mod_str, encoding='ascii')
  if opt.returncode != 0:
    return
  return opt.stdout

with open('llvm-dags.txt') as f:
  num_changed = 0
  num_processed = 0
  for line in f:
    _, mod_str = line.split(',', 1)
    m = unescape(mod_str.strip())
    before = parse_basic_block(m)
    m2 = optimize(m)
    num_processed += 1
    if not m2:
      continue
    after = parse_basic_block(m2)
    changed = before != after
    num_changed += changed
    print(f'{num_changed}/{num_processed}')
