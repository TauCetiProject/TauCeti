/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Functoriality

/-!
# Continuous cohomology along an isomorphism of topological groups

For an isomorphism of topological groups `e : H ≃ₜ* G` and a topological representation `X` of
`G`, the compatible pair `(e, 𝟙)` induces an isomorphism

```text
Hⁿ(G, X) ≅ Hⁿ(H, Res_e X),
```

whose inverse is the compatible pair `(e⁻¹, 𝟙)`: restricting along `e` and then along `e⁻¹` gives
back `X`. This is how a cohomology group computed for one model of a profinite group, such as an
open subgroup of an absolute Galois group, is read for another, such as the absolute Galois group
of the corresponding finite extension.

## Main definitions

* `TauCeti.ContinuousCohomology.mapContinuousMulEquiv`: the isomorphism
  `Hⁿ(G, X) ≅ Hⁿ(H, Res_e X)`.

## Main results

* `TauCeti.ContinuousCohomology.mapContinuousMulEquiv_hom`: it is the map of the compatible pair
  `(e, 𝟙)`.
* `TauCeti.ContinuousCohomology.natCard_continuousCohomology_res_continuousMulEquiv`: the two
  cohomology groups have the same cardinality.
-/

public section

open CategoryTheory

namespace TauCeti.ContinuousCohomology

universe u v

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G H : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- Restricting along `e : H ≃ₜ* G` and then along `e⁻¹` gives back the representation. -/
private theorem res_symm_res (e : H ≃ₜ* G) (X : TopRep R G) :
    TopRep.res ((e.symm : G →ₜ* H) : G →* H) (TopRep.res ((e : H →ₜ* G) : H →* G) X) = X := by
  have h : ((e : H →ₜ* G) : H →* G).comp ((e.symm : G →ₜ* H) : G →* H) = MonoidHom.id G :=
    MonoidHom.ext e.apply_symm_apply
  -- Restriction along a composite is the iterated restriction.
  change TopRep.res (((e : H →ₜ* G) : H →* G).comp ((e.symm : G →ₜ* H) : G →* H)) X = X
  rw [h]
  rfl

/-- **Continuous cohomology along an isomorphism of topological groups.** For `e : H ≃ₜ* G`, the
compatible pair `(e, 𝟙)` induces `Hⁿ(G, X) ≅ Hⁿ(H, Res_e X)`, with inverse the compatible pair of
`e⁻¹` and the identity of `X`. -/
noncomputable def mapContinuousMulEquiv (e : H ≃ₜ* G) (X : TopRep R G) (n : ℕ) :
    continuousCohomology n X ≅ continuousCohomology n (TopRep.res ((e : H →ₜ* G) : H →* G) X) where
  hom := _root_.ContinuousCohomology.map (e : H →ₜ* G) (𝟙 _) n
  inv := _root_.ContinuousCohomology.map (e.symm : G →ₜ* H) (eqToHom (res_symm_res e X)) n
  hom_inv_id := by
    rw [← _root_.ContinuousCohomology.map_comp, ← _root_.ContinuousCohomology.map_id]
    refine map_congr (ContinuousMonoidHom.ext e.apply_symm_apply) ?_ n
    exact (heq_of_eq ((congrArg (· ≫ eqToHom _) ((TopRep.resFunctor _).map_id _)).trans
      (Category.id_comp _))).trans (eqToHom_heq_id_cod _ _ _)
  inv_hom_id := by
    rw [← _root_.ContinuousCohomology.map_comp, ← _root_.ContinuousCohomology.map_id]
    refine map_congr (ContinuousMonoidHom.ext e.symm_apply_apply) ?_ n
    exact (heq_of_eq ((Category.comp_id _).trans (eqToHom_map _ _))).trans
      (eqToHom_heq_id_cod _ _ _)

/-- `mapContinuousMulEquiv` is the map of the compatible pair `(e, 𝟙)`. -/
@[simp]
theorem mapContinuousMulEquiv_hom (e : H ≃ₜ* G) (X : TopRep R G) (n : ℕ) :
    (mapContinuousMulEquiv e X n).hom =
      _root_.ContinuousCohomology.map (e : H →ₜ* G) (𝟙 _) n :=
  (rfl)

/-- Restriction along an isomorphism of topological groups does not change the cardinality of
continuous cohomology. -/
theorem natCard_continuousCohomology_res_continuousMulEquiv (e : H ≃ₜ* G) (X : TopRep R G)
    (n : ℕ) :
    Nat.card (continuousCohomology n (TopRep.res ((e : H →ₜ* G) : H →* G) X)) =
      Nat.card (continuousCohomology n X) :=
  (Nat.card_congr (mapContinuousMulEquiv e X n).toContinuousLinearEquiv.toEquiv).symm

end TauCeti.ContinuousCohomology
