/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Category.CompactlyGenerated.Coreflection
public import TauCeti.Topology.CWComplex.Classical.DeltaGenerated

/-!
# Compact generation of CW complexes and the coreflection counit

Every Hausdorff relative CW complex over a `u`-compactly generated base is `u`-compactly generated
for every universe `u` (`TauCeti.uCompactlyGeneratedSpace_of_relCWComplex`), so the coreflection
counit `CompactlyGenerated.adjCounit` is an isomorphism at every Hausdorff CW complex
(`CompactlyGenerated.isIso_adjCounit_app_of_cwComplex`, `isIso_adjCounit_app_of_cwComplex_univ`).

## References

* N. E. Steenrod, *A convenient category of topological spaces*, Michigan Math. J. 14 (1967),
  133–152.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Appendix,
  Proposition A.2.
-/

public section

universe u w

open CategoryTheory Topology

/-- A Hausdorff relative CW complex over a `u`-compactly generated base is `u`-compactly generated
for every test universe `u`. -/
theorem TauCeti.uCompactlyGeneratedSpace_of_relCWComplex {X : Type w} [TopologicalSpace X]
    [T2Space X] {C D : Set X} [RelCWComplex C D] [UCompactlyGeneratedSpace.{u} D] :
    UCompactlyGeneratedSpace.{u} C :=
  (isGeneratedBy_compHaus_iff C).1 isQuotientMap_sumElim_base_map.isGeneratedBy

namespace CompactlyGenerated

/-- For a Hausdorff CW complex `C` in `X : Type w`, `adjCounit.app (TopCat.of C)` is an isomorphism
for every test universe `u`. -/
theorem isIso_adjCounit_app_of_cwComplex {X : Type w} [TopologicalSpace X] [T2Space X]
    (C : Set X) [CWComplex C] : IsIso (adjCounit.{u, w}.app (TopCat.of C)) := inferInstance

/-- For a Hausdorff space `X : Type w` with `[CWComplex (Set.univ : Set X)]`,
`adjCounit.app (TopCat.of X)` is an isomorphism for every test universe `u`. -/
theorem isIso_adjCounit_app_of_cwComplex_univ (X : Type w) [TopologicalSpace X] [T2Space X]
    [CWComplex (Set.univ : Set X)] : IsIso (adjCounit.{u, w}.app (TopCat.of X)) := inferInstance

end CompactlyGenerated

end
