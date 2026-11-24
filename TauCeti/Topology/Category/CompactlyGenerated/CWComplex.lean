/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CWComplex.Classical.CompactlyGenerated
public import TauCeti.Topology.Category.CompactlyGenerated.Coreflection

/-!
# CW complexes and the `CompactlyGenerated` coreflection

Every Hausdorff relative CW complex over a `u`-compactly generated base is `u`-compactly generated
(`TauCeti.uCompactlyGeneratedSpace_of_relCWComplex`), and every Hausdorff CW complex is
delta-generated (`TauCeti.instDeltaGeneratedSpaceCWComplex`), hence `u`-compactly generated for
every test universe `u`. Consequently, the counit `kX ⟶ X` of the coreflection
`CompactlyGenerated.adj : compactlyGeneratedToTop ⊣ TopCat.toCompactlyGenerated` is an isomorphism
in `TopCat` on such spaces.

## Main declarations

* `CompactlyGenerated.isIso_counit_app_of_relCWComplex`: the coreflection counit `kC ⟶ C` is an
  isomorphism for every Hausdorff relative CW complex `C` over a `u`-compactly generated base `D`.
* `CompactlyGenerated.isIso_counit_app_of_cwComplex`: the coreflection counit `kC ⟶ C` is an
  isomorphism for every Hausdorff CW complex `C : Set X`.
* `CompactlyGenerated.isIso_counit_app_of_cwComplex_univ`: the coreflection counit `kX ⟶ X` is an
  isomorphism for every Hausdorff space `X` carrying a CW structure on `Set.univ`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Appendix,
  Proposition A.2.
-/

public section

open CategoryTheory Topology

universe u w

namespace CompactlyGenerated

/-- On any Hausdorff relative CW complex `C` over a `u`-compactly generated base `D`, the counit
`kC ⟶ C` is an isomorphism in `TopCat`. -/
theorem isIso_counit_app_of_relCWComplex {X : Type w} [TopologicalSpace X] [T2Space X]
    {C D : Set X} [RelCWComplex C D] [UCompactlyGeneratedSpace.{u} D] :
    IsIso (adj.{u, w}.counit.app (TopCat.of C)) :=
  have := TauCeti.uCompactlyGeneratedSpace_of_relCWComplex.{u} (C := C) (D := D)
  inferInstance

/-- On any Hausdorff CW complex `C : Set X`, the counit `kC ⟶ C` is an isomorphism in `TopCat` for
every test universe `u`. -/
theorem isIso_counit_app_of_cwComplex {X : Type w} [TopologicalSpace X] [T2Space X]
    (C : Set X) [CWComplex C] : IsIso (adj.{u, w}.counit.app (TopCat.of C)) := inferInstance

/-- On any Hausdorff space carrying a CW structure on `Set.univ`, the counit `kX ⟶ X` is an
isomorphism in `TopCat` for every test universe `u`. -/
theorem isIso_counit_app_of_cwComplex_univ (X : Type w) [TopologicalSpace X] [T2Space X]
    [CWComplex (Set.univ : Set X)] : IsIso (adj.{u, w}.counit.app (TopCat.of X)) := inferInstance

end CompactlyGenerated

end
