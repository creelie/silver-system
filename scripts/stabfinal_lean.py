"""stabfinal_lean.py NS n p sizes dmin flags leandir TAG...

Write leandir/NS/Final.lean: from the shard modules StabCert.NS.TAG.C<k> (scripts/stabshard_lean.py),
whose theorems chunk<k> say that every cube of StabCert.NS.TAG.cubes<k> (module K<k>) is refuted, and the certificate
leandir/NS/lrat/cover.lrat that the cubes of all shards cover every assignment, the theorem
StabCert.NS.unsat: (Stab.encode n p sizes dmin flags).Unsat. Also leandir/NS/Final.setup.json, the
import list for compiling Final.lean with plain lean: like lake, it names only the public parts of the
imported modules (.olean, .olean.server, .ir), so the shards' certificates (.olean.private) are not
needed again."""
import json, os, re, sys
ns, n, p, sizes, dmin, flags, leandir = sys.argv[1:8]
tags = sys.argv[8:]
F = f'(Stab.encode {n} {p} [{sizes.replace(",", ", ")}] {dmin} "{flags}")'
chunks = []   # (tag, k)
for t in tags:
    ks = sorted(int(m.group(1)) for f in os.listdir(os.path.join(leandir, ns, t))
                if (m := re.fullmatch(r'C(\d+)\.lean', f)))
    chunks += [(t, k) for k in ks]
mods = [f'StabCert.{ns}.{t}.C{k}' for t, k in chunks]
cubemods = ['BiplanarF.Stab'] + [f'StabCert.{ns}.{t}.K{k}' for t, k in chunks]
names = [f'{t}.cubes{k}' for t, k in chunks]
with open(os.path.join(leandir, ns, 'Final.lean'), 'w') as f:
    f.write('module\n\n' + ''.join(f'public import {m}\n' for m in mods))
    f.write(''.join(f'public import {m}\npublic meta import {m}\n' for m in cubemods))
    f.write('public meta import Std.Tactic.BVDecide.Reflect\n\npublic section\n\nnamespace StabCert.' + ns + '\n\n')
    allc = '[' + ', '.join(names) + '].flatten'
    f.write(f'/-- The refuted cubes of {len(tags)} shards ({len(chunks)} chunks) cover every assignment. -/\n')
    f.write(f'theorem cover_ok : (Stab.cover {allc}).Unsat :=\n')
    f.write('  Std.Tactic.BVDecide.Reflect.verifyCert_correct _ (include_str "lrat/cover.lrat") (by native_decide)\n\n')
    f.write(f'/-- The model `{F}` has no solution. -/\n')
    f.write(f'theorem unsat : {F}.Unsat :=\n')
    f.write('  Stab.unsat_of_cubes _ _ cover_ok (Stab.forall_flatten (by\n')
    f.write('    intro L hL\n    simp only [List.mem_cons, List.not_mem_nil, or_false] at hL\n')
    f.write('    rcases hL with ' + ' | '.join(['rfl'] * len(chunks)) + '\n')
    f.write(''.join(f'    · exact {t}.chunk{k}\n' for t, k in chunks).rstrip('\n') + '))\n\n')
    f.write('#print axioms unsat\n\nend StabCert.' + ns + '\n\nend\n')
lib = os.path.join(os.path.dirname(os.path.abspath(leandir)), '.lake', 'build', 'lib', 'lean')
def arts(m):
    b = os.path.join(lib, *m.split('.'))
    return [[b + '.olean', b + '.olean.server'], [b + '.ir.sig', b + '.ir']]
setup = {'plugins': [], 'package': 'BiplanarF', 'options': {}, 'name': f'StabCert.{ns}.Final', 'isModule': True,
         'importArts': {m: arts(m) for m in mods + cubemods}, 'dynlibs': []}
with open(os.path.join(leandir, ns, 'Final.setup.json'), 'w') as f: json.dump(setup, f, indent=1)
print(f'{len(tags)} shards, {len(chunks)} chunks')
