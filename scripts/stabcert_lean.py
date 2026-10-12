"""stabcert_lean.py NS n p sizes dmin flags leaves.txt lratdir outdir chunk_mb

Write the Lean sources that check a cube-and-conquer refutation of Stab.encode n p sizes dmin flags:
outdir/NS/C<k>.lean (a chunk of cubes, each with its LRAT certificate, checked by Stab.checkAll) and
outdir/NS/Final.lean (the cover certificate and the theorem StabCert.NS.unsat). leaves.txt has one line
"id lit lit ..." per cube; the certificate of cube id is lratdir/c<id>.lrat, the cover one lratdir/cover.lrat."""
import os, sys
ns, n, p, sizes, dmin, flags, leaves, lrd, out, chunk_mb = sys.argv[1:11]
d = os.path.join(out, ns); os.makedirs(d, exist_ok=True)
link = os.path.join(d, 'lrat')
if os.path.islink(link) or os.path.exists(link): os.remove(link)
os.symlink(os.path.abspath(lrd), link)
F = f'(Stab.encode {n} {p} [{sizes.replace(",", ", ")}] {dmin} "{flags}")'
cubes = []
for line in open(leaves):
    xs = line.split()
    if xs: cubes.append((xs[0], [int(x) for x in xs[1:]]))
lim = int(chunk_mb) * 2**20; chunks = [[]]; size = 0
for cid, c in cubes:
    s = os.path.getsize(os.path.join(lrd, f'c{cid}.lrat'))
    if chunks[-1] and size + s > lim: chunks.append([]); size = 0
    chunks[-1].append((cid, c)); size += s
HDR = 'module\n\n'
def meta_imports(extra):
    return ''.join(f'public import {m}\npublic meta import {m}\n' for m in extra) + 'public meta import Std.Tactic.BVDecide.Reflect\n'
with open(os.path.join(d, 'Cubes.lean'), 'w') as f:
    f.write(HDR + 'public import BiplanarF.Stab\n\n@[expose] public section\n\nnamespace StabCert.' + ns + '\n\n')
    for k, ch in enumerate(chunks):
        f.write(f'/-- Cubes {ch[0][0]}–{ch[-1][0]}. -/\n')
        f.write(f'def cubes{k} : List (List Int) := [\n  ' + ',\n  '.join('([' + ', '.join(map(str, c)) + '] : List Int)' for _, c in ch) + ']\n\n')
    f.write('end StabCert.' + ns + '\n\nend\n')
for k, ch in enumerate(chunks):
    with open(os.path.join(d, f'C{k}.lean'), 'w') as f:
        f.write(HDR + meta_imports(['BiplanarF.Stab', f'StabCert.{ns}.Cubes']) + '\npublic section\n\nnamespace StabCert.' + ns + '\n\n')
        f.write(f'/-- Every cube of `cubes{k}` is refuted (one LRAT certificate per cube). -/\n')
        f.write(f'theorem chunk{k} : ∀ c ∈ cubes{k}, (Stab.withCube {F} c).Unsat :=\n')
        f.write(f'  Stab.of_checkAll (certs := [\n    ' + ',\n    '.join(f'include_str "lrat/c{cid}.lrat"' for cid, _ in ch) + '])\n')
        f.write('    (by native_decide)\n\n')
        f.write(f'#print axioms chunk{k}\n\nend StabCert.' + ns + '\n\nend\n')
K = len(chunks)
with open(os.path.join(d, 'Final.lean'), 'w') as f:
    f.write(HDR + ''.join(f'public import StabCert.{ns}.C{k}\n' for k in range(K)))
    f.write(meta_imports(['BiplanarF.Stab', f'StabCert.{ns}.Cubes']) + '\npublic section\n\nnamespace StabCert.' + ns + '\n\n')
    allc = '[' + ', '.join(f'cubes{k}' for k in range(K)) + '].flatten'
    f.write(f'/-- The {len(cubes)} cubes cover every assignment. -/\n')
    f.write(f'theorem cover_ok : (Stab.cover {allc}).Unsat :=\n')
    f.write('  Std.Tactic.BVDecide.Reflect.verifyCert_correct _ (include_str "lrat/cover.lrat") (by native_decide)\n\n')
    f.write(f'/-- The model `{F}` has no solution. -/\n')
    f.write(f'theorem unsat : {F}.Unsat :=\n')
    f.write(f'  Stab.unsat_of_cubes _ _ cover_ok (Stab.forall_flatten (by\n')
    f.write('    intro L hL\n    simp only [List.mem_cons, List.not_mem_nil, or_false] at hL\n')
    f.write('    rcases hL with ' + ' | '.join(['rfl'] * K) + '\n')
    f.write(''.join(f'    · exact chunk{k}\n' for k in range(K)).rstrip('\n') + '))\n\n')
    f.write('#print axioms unsat\n\nend StabCert.' + ns + '\n\nend\n')
print(f'{len(cubes)} cubes in {K} chunks')
