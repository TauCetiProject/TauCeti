/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.TopRep.Res
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Functoriality

/-!
# Continuous cohomology along an isomorphism of topological groups

For an isomorphism of topological groups `e : H ≃ₜ* G` and a topological representation `X` of
`G`, the compatible pair `(e, 𝟙)` induces an isomorphism

```text
Hⁿ(G, X) ≅ Hⁿ(H, Res_e X),
```

whose inverse is the compatible pair `(e⁻¹, 𝟙)`: restricting along `e` and then along `e⁻¹` gives
back `X` (`TopRep.res_symm_res`). This is how a cohomology group computed for one model of a
profinite group, such as an open subgroup of an absolute Galois group, is read for another, such as
the absolute Galois group of the corresponding finite extension.

## Main definitions

* `ContinuousMulEquiv.continuousCohomologyIso`: the isomorphism `Hⁿ(G, X) ≅ Hⁿ(H, Res_e X)`.

## Main results

* `ContinuousMulEquiv.continuousCohomologyIso_hom`,
  `ContinuousMulEquiv.continuousCohomologyIso_inv`: it is the map of the compatible pair
  `(e, 𝟙)`, with inverse that of `(e⁻¹, 𝟙)`.
* `ContinuousMulEquiv.natCard_continuousCohomology_res`: the two cohomology groups have the same
  cardinality.
-/

public section

open CategoryTheory

namespace ContinuousMulEquiv

universe u v

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G H : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- **Continuous cohomology along an isomorphism of topological groups.** For `e : H ≃ₜ* G`, the
compatible pair `(e, 𝟙)` induces `Hⁿ(G, X) ≅ Hⁿ(H, Res_e X)`, with inverse the compatible pair of
`e⁻¹` and the identity of `X`. -/
noncomputable def continuousCohomologyIso (e : H ≃ₜ* G) (X : TopRep R G) (n : ℕ) :
    continuousCohomology n X ≅ continuousCohomology n (TopRep.res ((e : H →ₜ* G) : H →* G) X) where
  hom := ContinuousCohomology.map (e : H →ₜ* G) (𝟙 _) n
  inv := ContinuousCohomology.map (e.symm : G →ₜ* H) (eqToHom (TopRep.res_symm_res e.toMulEquiv X)) n
  hom_inv_id := by
    rw [← ContinuousCohomology.map_comp, ← ContinuousCohomology.map_id]
    refine TauCeti.ContinuousCohomology.map_congr
      (ContinuousMonoidHom.ext e.apply_symm_apply) ?_ n
    exact (heq_of_eq ((congrArg (· ≫ eqToHom _) ((TopRep.resFunctor _).map_id _)).trans
      (Category.id_comp _))).trans (eqToHom_heq_id_cod _ _ _)
  inv_hom_id := by
    rw [← ContinuousCohomology.map_comp, ← ContinuousCohomology.map_id]
    refine TauCeti.ContinuousCohomology.map_congr
      (ContinuousMonoidHom.ext e.symm_apply_apply) ?_ n
    exact (heq_of_eq ((Category.comp_id _).trans (eqToHom_map _ _))).trans
      (eqToHom_heq_id_cod _ _ _)

/-- `continuousCohomologyIso` is the map of the compatible pair `(e, 𝟙)`. -/
@[simp]
theorem continuousCohomologyIso_hom (e : H ≃ₜ* G) (X : TopRep R G) (n : ℕ) :
    (e.continuousCohomologyIso X n).hom = ContinuousCohomology.map (e : H →ₜ* G) (𝟙 _) n :=
  (rfl)

/-- The inverse of `continuousCohomologyIso` is the map of the compatible pair `(e⁻¹, 𝟙)`, the
identity being transported along `TopRep.res_symm_res`. -/
@[simp]
theorem continuousCohomologyIso_inv (e : H ≃ₜ* G) (X : TopRep R G) (n : ℕ) :
    (e.continuousCohomologyIso X n).inv =
      ContinuousCohomology.map (e.symm : G →ₜ* H) (eqToHom (TopRep.res_symm_res e.toMulEquiv X)) n :=
  (rfl)

/-- Restriction along an isomorphism of topological groups does not change the cardinality of
continuous cohomology. -/
theorem natCard_continuousCohomology_res (e : H ≃ₜ* G) (X : TopRep R G) (n : ℕ) :
    Nat.card (continuousCohomology n (TopRep.res ((e : H →ₜ* G) : H →* G) X)) =
      Nat.card (continuousCohomology n X) :=
  (Nat.card_congr (e.continuousCohomologyIso X n).toContinuousLinearEquiv.toEquiv).symm

end ContinuousMulEquiv
