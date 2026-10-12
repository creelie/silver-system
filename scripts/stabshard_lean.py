"""stabshard_lean.py NS TAG j n p sizes dmin flags leaves lratdir outdir

Write one chunk of the Lean check of a shard (scripts/stabshard.sh) of a cube-and-conquer refutation of
Stab.encode n p sizes dmin flags: outdir/NS/TAG/K<j>.lean, the list StabCert.NS.TAG.cubes<j> of the cubes
in the file leaves (one line "id lit lit ..." per cube), and outdir/NS/TAG/C<j>.lean, the theorem
StabCert.NS.TAG.chunk<j> that every one of them is refuted, by Stab.checkAll on the LRAT certificates
lratdir/c<id>.lrat. scripts/stabfinal_lean.py combines the chunks of all shards."""
import os, sys
ns, tag, j, n, p, sizes, dmin, flags, leaves, lrd, out = sys.argv[1:12]
d = os.path.join(out, ns, tag); os.makedirs(d, exist_ok=True)
link = os.path.join(d, 'lrat')
if not os.path.islink(link): os.symlink(os.path.abspath(lrd), link)
F = f'(Stab.encode {n} {p} [{sizes.replace(",", ", ")}] {dmin} "{flags}")'
mod = f'StabCert.{ns}.{tag}'
cubes = []
for line in open(leaves):
    xs = line.split()
    if xs: cubes.append((xs[0], [int(x) for x in xs[1:]]))
HDR = 'module\n\n'
with open(os.path.join(d, f'K{j}.lean'), 'w') as f:
    f.write(HDR + 'public import BiplanarF.Stab\n\n@[expose] public section\n\nnamespace ' + mod + '\n\n')
    f.write(f'/-- Cubes {cubes[0][0]}–{cubes[-1][0]}. -/\n')
    f.write(f'def cubes{j} : List (List Int) := [\n  ' + ',\n  '.join('([' + ', '.join(map(str, c)) + '] : List Int)' for _, c in cubes) + ']\n\n')
    f.write('end ' + mod + '\n\nend\n')
with open(os.path.join(d, f'C{j}.lean'), 'w') as f:
    f.write(HDR + ''.join(f'public import {m}\npublic meta import {m}\n' for m in ['BiplanarF.Stab', f'{mod}.K{j}']))
    f.write('public meta import Std.Tactic.BVDecide.Reflect\n\npublic section\n\nnamespace ' + mod + '\n\n')
    f.write(f'/-- Every cube of `cubes{j}` is refuted (one LRAT certificate per cube). -/\n')
    f.write(f'theorem chunk{j} : ∀ c ∈ cubes{j}, (Stab.withCube {F} c).Unsat :=\n')
    f.write(f'  Stab.of_checkAll (certs := [\n    ' + ',\n    '.join(f'include_str "lrat/c{cid}.lrat"' for cid, _ in cubes) + '])\n')
    f.write('    (by native_decide)\n\n')
    f.write(f'#print axioms chunk{j}\n\nend ' + mod + '\n\nend\n')
print(f'chunk {j}: {len(cubes)} cubes')
