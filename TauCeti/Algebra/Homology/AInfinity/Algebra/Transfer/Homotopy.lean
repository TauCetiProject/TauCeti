/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Transfer.Basic
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Homotopy
public import TauCeti.Algebra.Homology.Contraction.TensorTrick.Perturbation.Homotopy

/-!
# Homotopy equivalence with the transferred A-infinity structure

A graded special contraction transfers an A-infinity structure together with an inclusion `I`
and a projection `P`. Already `P I = id`; this file constructs the complementary homotopy
`id ⇒ I P`. Its bar map is the perturbed tensor-trick homotopy `K - K X K`, and its linear
component is the original contraction homotopy. Thus transfer gives a homotopy equivalence,
not merely a pair of quasi-isomorphisms. The construction works over a commutative ring with
an explicit graded contraction, without a field or splitting assumption.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.3 and 3.7.
* V. K. A. M. Gugenheim, L. A. Lambe, and J. D. Stasheff, *Perturbation theory in differential
  homological algebra II*, Illinois Journal of Mathematics 35 (1991), 357--373.
-/

public section

open scoped DirectSum

namespace TauCeti.AInfinityAlgebra

open ReducedTensorWords

universe uR uA uH

variable {R : Type uR} {A : Type uA} {H : Type uH} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup H] [Module R H]
  (𝒜 : AInfinityAlgebra R A) {GH : InternalGrading R H} {dH : Module.End R H}
  (c : LinearSpecialContraction 𝒜.differential dH)
  (hh : LinearMap.IsHomogeneous c.homotopy 𝒜.grading.piece 𝒜.grading.piece (-1))
  (hincl : LinearMap.IsHomogeneous c.incl GH.piece 𝒜.grading.piece 0)
  (hproj : LinearMap.IsHomogeneous c.proj 𝒜.grading.piece GH.piece 0)

/-- The homotopy from the identity of an A-infinity algebra to its transferred inclusion composed
with its transferred projection. On bar constructions this is `K - K X K`, where `K` is the
tensor-trick homotopy and `X` the perturbation operator. -/
noncomputable def transferHomotopy :
    AInfinityHom.Homotopy (AInfinityHom.id 𝒜)
      ((𝒜.transferInclusion c hh hincl hproj).comp (𝒜.transferProjection c hh hincl hproj)) where
  barHomotopy := (𝒜.barTensorTrick c hh hincl hproj).homotopy -
    (𝒜.barTensorTrick c hh hincl hproj).homotopy ∘ₗ
      (𝒜.barTensorTrick c hh hincl hproj).perturbationSeries 𝒜.higherBarDifferential ∘ₗ
        (𝒜.barTensorTrick c hh hincl hproj).homotopy
  isGradedCoderivationAlong_barHomotopy := by
    have hd : LinearMap.IsHomogeneous 𝒜.differential (𝒜.grading.shift 1).piece
        (𝒜.grading.shift 1).piece 1 :=
      LinearMap.isHomogeneous_shift_piece_iff.2 <| LinearMap.isHomogeneous_def.2
        fun _ _ hx ↦ 𝒜.differential_mem_piece hx
    have hc := c.isGradedCoderivationAlong_reducedTensorWords_perturb_homotopy hd
      (LinearMap.isHomogeneous_shift_piece_iff.2 hh)
      (LinearMap.isHomogeneous_shift_piece_iff.2 hincl)
      (LinearMap.isHomogeneous_shift_piece_iff.2 hproj)
      𝒜.gradedCoderiv_differential_add_higherBarDifferential_comp_self
      (by
        rw [← barTensorTrick_def]
        exact 𝒜.isUnit_one_add_higherBarDifferential_mul_barTensorTrick_homotopy c hh hincl hproj)
      𝒜.isGradedCoderivation_higherBarDifferential
    simpa only [AInfinityHom.barMap_id, AInfinityHom.barMap_comp, barMap_transferInclusion,
      barMap_transferProjection, LinearSpecialContraction.perturb_incl,
      LinearSpecialContraction.perturb_proj, LinearSpecialContraction.perturb_homotopy,
      ← barTensorTrick_def 𝒜 c hh hincl hproj hd,
      barTensorTrick_incl, barTensorTrick_proj, barTensorTrick_homotopy] using hc
  isHomogeneous_barHomotopy := by
    have hK := c.isHomogeneous_reducedTensorWordsHomotopy (𝒜.grading.shift 1)
      (LinearMap.isHomogeneous_shift_piece_iff.2 hh)
      (LinearMap.isHomogeneous_shift_piece_iff.2 hincl)
      (LinearMap.isHomogeneous_shift_piece_iff.2 hproj)
    have hKXK := hK.comp ((𝒜.isHomogeneous_perturbationSeries c hh hincl hproj).comp hK)
    rw [neg_add_cancel, zero_add] at hKXK
    rw [barTensorTrick_homotopy]
    exact hK.sub hKXK
  barMap_sub_barMap := by
    have hc := ((𝒜.barTensorTrick c hh hincl hproj).perturb 𝒜.higherBarDifferential
      𝒜.gradedCoderiv_differential_add_higherBarDifferential_comp_self
      (𝒜.isUnit_one_add_higherBarDifferential_mul_barTensorTrick_homotopy c hh hincl hproj))
      |>.dM_comp_homotopy_add_homotopy_comp_dM
    simpa only [AInfinityHom.barMap_id, AInfinityHom.barMap_comp, barMap_transferInclusion,
      barMap_transferProjection, LinearSpecialContraction.perturb_incl,
      LinearSpecialContraction.perturb_proj, LinearSpecialContraction.perturb_homotopy,
      barTensorTrick_incl, barTensorTrick_proj, barTensorTrick_homotopy,
      ← unaryBarDifferential_eq_gradedCoderiv, ← barDifferential_eq_unary_add_higher] using hc.symm

/-- The bar homotopy of transfer is the perturbed tensor-trick homotopy `K - K X K`. -/
@[simp]
theorem barHomotopy_transferHomotopy :
    (𝒜.transferHomotopy c hh hincl hproj).barHomotopy =
      c.reducedTensorWordsHomotopy (𝒜.grading.shift 1) -
        c.reducedTensorWordsHomotopy (𝒜.grading.shift 1) ∘ₗ
          (𝒜.barTensorTrick c hh hincl hproj).perturbationSeries 𝒜.higherBarDifferential ∘ₗ
            c.reducedTensorWordsHomotopy (𝒜.grading.shift 1) := by
  simp only [transferHomotopy, barTensorTrick_homotopy]

/-- The Taylor components of the transfer homotopy are the letter projection of the perturbed
tensor-trick homotopy `K - K X K`. -/
@[simp]
theorem taylor_transferHomotopy :
    (𝒜.transferHomotopy c hh hincl hproj).taylor =
      letter R A ∘ₗ (c.reducedTensorWordsHomotopy (𝒜.grading.shift 1) -
        c.reducedTensorWordsHomotopy (𝒜.grading.shift 1) ∘ₗ
          (𝒜.barTensorTrick c hh hincl hproj).perturbationSeries 𝒜.higherBarDifferential ∘ₗ
            c.reducedTensorWordsHomotopy (𝒜.grading.shift 1)) := by
  simp only [AInfinityHom.Homotopy.taylor_def, barHomotopy_transferHomotopy]

/-- The linear component of the transfer homotopy is the original contraction homotopy. -/
@[simp]
theorem linearHomotopy_transferHomotopy :
    (𝒜.transferHomotopy c hh hincl hproj).linearHomotopy = c.homotopy := by
  ext a
  rw [AInfinityHom.Homotopy.linearHomotopy_apply, AInfinityHom.Homotopy.taylor_def,
    LinearMap.comp_apply, barHomotopy_transferHomotopy, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.comp_apply, c.reducedTensorWordsHomotopy_ofLetter]
  simp only [LinearSpecialContraction.perturbationSeries_def, Module.End.mul_apply,
    higherBarDifferential_ofLetter, map_zero, sub_zero, letter_ofLetter]

end TauCeti.AInfinityAlgebra
