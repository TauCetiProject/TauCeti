/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CWComplex.Classical.DeltaGenerated
public import TauCeti.Topology.Category.CompactlyGenerated.Coreflection

/-!
# CW complexes and the `CompactlyGenerated` coreflection

Every Hausdorff CW complex is delta-generated (`TauCeti.instDeltaGeneratedSpaceCWComplex`), hence
`u`-compactly generated for every test universe `u`. Consequently, the counit `kX ⟶ X` of the
coreflection `CompactlyGenerated.adj : compactlyGeneratedToTop ⊣ TopCat.toCompactlyGenerated` is an
isomorphism in `TopCat` on every Hausdorff CW complex.

## Main declarations

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
