/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Coinvariants

/-!
# The transfer identifies the homology of the base of a finite quotient covering with invariants

Let a finite group `G` act on a space `E` so that `p : E ⟶ B` is the quotient covering map of the
action, in the sense of Mathlib's `IsQuotientCoveringMap`. The transfer
`t : C(B; R) ⟶ C(E; R)` of the finite covering `p` sends a singular simplex to the sum of its
lifts. Each `g : G` permutes those lifts, so `t ≫ g_* = t`: the transfer is a cone
`hG.transferCone R` over the action of `G` on `C(E; R)`.

This file shows that, when multiplication by `|G|` is invertible on the coefficients `R`, the
transfer exhibits `Hₙ(B; R)` as the invariants `Hₙ(E; R)^G`:

* `IsQuotientCoveringMap.isLimitMapConeTransferCone`: every additive functor out of chain
  complexes, and in particular homology, sends `hG.transferCone R` to a limit cone.
* `IsQuotientCoveringMap.isLimitHomologyMapConeTransferCone`: `Hₙ(B; R)` is the limit
  `Hₙ(E; R)^G` of the action of `G` on `Hₙ(E; R)`, with leg the transfer.

The argument is the one for coinvariants
(`IsQuotientCoveringMap.isColimitMapCoconeSingularHomology`) read backwards: `t ≫ p_* = |G| • 𝟙`
and `p_* ≫ t = ∑_{g ∈ G} g_*`, so `|G|⁻¹ • p_*` retracts the transfer onto the invariants
(`CategoryTheory.Limits.SingleObj.isLimitOfTransfer`). Without the invertibility of `|G|` the
statement fails, already for the double cover of `ℝP²` by `S²` with coefficients `ℤ` in degree
zero, where the transfer is multiplication by `2` on `ℤ`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.G (Proposition 3G.1), for the transfer and the averaging argument, stated there for
  cohomology with field coefficients and invariants; the homology form here is its dual.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

universe w v u

namespace IsQuotientCoveringMap

variable {E B : TopCat.{w}} {p : E ⟶ B} {G : Type*} [Group G] [MulAction G E]
  (hG : IsQuotientCoveringMap p G)
  {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] (R : C)

/-- **The transfer as a cone over the action.** For the quotient covering map `p : E ⟶ B` of an
action of a finite group `G`, the transfer `C(B; R) ⟶ C(E; R)` is invariant under the action of
`G` on `C(E; R)` by the chain maps `g_*`, so it is a cone over that action with point `C(B; R)`. -/
@[expose, simps]
def transferCone [Finite G] :
    Cone (@TopCat.actionFunctor E G _ _ hG.toContinuousConstSMul ⋙
      (singularChainComplexFunctor C).obj R) where
  pt := ((singularChainComplexFunctor C).obj R).obj B
  π :=
    { app _ := hG.isCoveringMap.singularTransfer hG.finite_fiber R
      naturality _ _ g := by
        have := hG.toContinuousConstSMul
        refine (Category.id_comp _).trans ?_
        exact (hG.isCoveringMap.singularTransfer_comp_chainComplexMap_of_comp_eq hG.finite_fiber
          R (f := TopCat.ofHom ⟨(g • ·), hG.continuous_const_smul g⟩) (MulAction.bijective g)
          (by ext e; exact hG.map_smul g)).symm }

/-- **The transfer exhibits invariants.** For the quotient covering map `p : E ⟶ B` of an action of
a finite group `G`, and coefficients `R` on which multiplication by `|G|` is invertible, every
additive functor `F` out of chain complexes sends the transfer `C(B; R) ⟶ C(E; R)` to a limit cone:
`F(C(B; R))` is the object of invariants `F(C(E; R))^G`. -/
def isLimitMapConeTransferCone [Fintype G] [IsIso (Fintype.card G • 𝟙 R)] {D : Type*} [Category D]
    [Preadditive D] (F : ChainComplex C ℕ ⥤ D) [F.Additive] :
    IsLimit (F.mapCone (hG.transferCone R)) := by
  have := hG.toContinuousConstSMul
  -- Singular chains are additive in the coefficients, so `|G|` stays invertible on `C(E; R)` and
  -- `C(B; R)`, and the additive functor `F` keeps it invertible on their images. By
  -- `TopCat.actionFunctor_obj` and `transferCone_pt` (both `rfl`), these are the images of the
  -- acted-on object and of the cone point of `hG.transferCone R`.
  have : IsIso (Fintype.card G • 𝟙 (((E.actionFunctor G ⋙
      (singularChainComplexFunctor C).obj R) ⋙ F).obj (SingleObj.star G))) :=
    (singularChainComplexFunctor C ⋙ (evaluation _ _).obj E ⋙ F).isIso_nsmul_id_obj _ R
  have : IsIso (Fintype.card G • 𝟙 (F.mapCone (hG.transferCone R)).pt) :=
    (singularChainComplexFunctor C ⋙ (evaluation _ _).obj B ⋙ F).isIso_nsmul_id_obj _ R
  refine SingleObj.isLimitMapConeOfTransfer (hG.transferCone R)
    (SSet.chainComplexMap (TopCat.toSSet.map p) R) F ?_ ?_
  · exact hG.isCoveringMap.singularTransfer_comp_chainComplexMap hG.finite_fiber R fun b ↦ by
      obtain ⟨e, he⟩ := hG.surjective b
      rw [Nat.card_congr (hG.fiberEquivGroup ⟨e, he⟩), Nat.card_eq_fintype_card]
  -- The functor `(singularChainComplexFunctor C).obj R` sends the action of `g` to `(g • ·)_*`.
  · simp only [Functor.comp_map, TopCat.actionFunctor_map]
    exact hG.chainComplexMap_comp_singularTransfer R

/-- **The singular homology of the base of a finite quotient covering is invariants.** For the
quotient covering map `p : E ⟶ B` of an action of a finite group `G`, and coefficients `R` on
which multiplication by `|G|` is invertible, the transfer `Hₙ(B; R) ⟶ Hₙ(E; R)` exhibits
`Hₙ(B; R)` as the limit `Hₙ(E; R)^G` of the action of `G` on `Hₙ(E; R)`. -/
def isLimitHomologyMapConeTransferCone [Fintype G] [CategoryWithHomology C] (n : ℕ)
    [IsIso (Fintype.card G • 𝟙 R)] :
    IsLimit ((HomologicalComplex.homologyFunctor C _ n).mapCone (hG.transferCone R)) :=
  hG.isLimitMapConeTransferCone R _

end IsQuotientCoveringMap
