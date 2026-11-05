# Declaration names added by a PR

Every PR build records, after its audits and lints, the constant names the PR adds to each
module it touches, read from the compiled module headers (`constNames`) at the tested
integration commit and at the merge base. The merge queue uses the record to keep two
batch-mates that both add the same name in different modules out of the same staging
candidate, so the collision costs seconds at batch construction instead of a full staging
build. The post-build duplicate-declaration audit in `scripts/Axioms.lean` remains the
authority; the record is advisory and only ever removes a staging round.

`scripts/DeclarationNames.lean` prints one line:

```text
DECLARATION-NAMES {"version":1,"head":"<PR head>","base":"<merge base>","tested":"<integration commit>","complete":true,"added":{"TauCeti.Geometry.Manifold.Morse.Cell.Band":["TauCeti.isZero_singularHomology_sublevelPair_of_mfderiv_ne_zero"]}}
```

The trusted `sandbox-build.sh` copies each changed module's restored `main` header aside
before `lake build` and runs the script after the lint phases, as a final phase that cannot
change the build's verdict. Staging batches never produce the record.

Coverage, stated honestly: user-declared, non-private names added by the PR. Private names
cannot collide across modules. Auxiliary names are excluded by a structural superset of
Lean's environment-dependent reserved-name predicates (numeric or `_`-prefixed components,
`Name.isInternalDetail`, and generated suffixes such as `rec`, `casesOn`, `noConfusion`,
`eq_def`, `fun_cases`, `injEq`), so a user-written `.eq_1` with a declaration range is not
enforced early; the audit still checks it. Bounds: 4,096 modules, 16,384 added names and
1 MiB; over any bound, or with an unreadable tested header or an unreadable existing base
header, the record is `"complete": false` with no names, which the consumer treats as unknown.

Run the fixture check with the pinned toolchain:

```sh
python3 scripts/test_declaration_names.py
```
