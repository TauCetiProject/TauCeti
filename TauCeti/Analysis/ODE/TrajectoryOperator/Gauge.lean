/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import TauCeti.Analysis.ODE.TrajectoryOperator
import TauCeti.Analysis.Sobolev.Leibniz

/-!
# Changes of trivialization of the trajectory operator

The operator `D_A u = u' + A(s) u` arises by linearizing a flow along a trajectory after a
trivialization of the vector bundle along it has been chosen. Changing that trivialization by a
path `Φ : ℝ → End(F)` of operators replaces the unknown `u` by `Φ u`, and the product rule
`(Φ u)' = Φ u' + Φ' u` gives

`D_A (Φ u) = Φ (u' + B u) = Φ D_B u` whenever `Φ B = A Φ + Φ'`,

that is `B = Φ⁻¹ A Φ + Φ⁻¹ Φ'` when `Φ` is invertible. This is the gauge transformation of the
coefficient. This file proves this identity for the trajectory operator on the weak-derivative
graph over `Lᵖ`, on an open subset of the line with an additive Haar measure, for a
finite-dimensional real space `F`.

When `Φ` is `C¹` on `Omega` and `Φ` and `Φ'` are essentially bounded, multiplication by `Φ` is a
continuous linear endomorphism `TauCeti.WeakDerivStep.gaugeL` of the weak-derivative graph: the
weak derivative of `Φ u` is `Φ u' + Φ' u` by the Leibniz rule for weak derivatives with a `C¹`
operator-valued factor (`TauCeti.HasWeakLineDerivOn.contDiffOn_clm_apply_of_ne_zero`). When `Φ`
has a pointwise inverse `Ψ` with the same properties, multiplication by `Φ` is an isomorphism
(`TauCeti.WeakDerivStep.gaugeEquiv`) of the weak-derivative graph, and also of `Lᵖ`. So the change
of trivialization identifies the two operators: `D_A` and `D_B` have kernels corresponding under
multiplication by `Φ`, one is Fredholm exactly when the other is, and then their indices agree.
In particular the Fredholm property and the index of the linearized operator along a trajectory
do not depend on the trivialization in which it is written.

The identity `Φ B = A Φ + Φ'` is required only almost everywhere, and `Φ` need not be invertible
for the conjugation identity itself. The scalar gauge `Φ = exp w • id` used for exponential weights
in `TauCeti.Analysis.ODE.EnergyEstimate.Weighted` is the case of an unbounded factor, which is not
covered here.

## Main declarations

* `TauCeti.WeakDerivStep.gaugeL`: multiplication `u ↦ Φ u` by a `C¹` path of operators with
  essentially bounded values and derivative, on the weak-derivative graph over `Lᵖ`.
* `TauCeti.WeakDerivStep.prev_gaugeL`: its value is the product of `Φ` with the value of `u`.
* `TauCeti.WeakDerivStep.trajectoryOperator_gaugeL`: `D_A (Φ u) = Φ D_B u` when `Φ B = A Φ + Φ'`.
* `TauCeti.WeakDerivStep.gaugeEquiv`: for a pointwise invertible `Φ`, multiplication by `Φ` as a
  continuous linear automorphism of the weak-derivative graph.
* `TauCeti.WeakDerivStep.ker_trajectoryOperator_eq_map_gaugeL`: the kernel of `D_A` is the image
  of the kernel of `D_B` under multiplication by `Φ`.
* `TauCeti.WeakDerivStep.isFredholm_trajectoryOperator_iff_of_gauge` and
  `TauCeti.WeakDerivStep.index_trajectoryOperator_eq_of_gauge`: `D_A` is Fredholm exactly when
  `D_B` is, and then both have the same index.

## References

* M. Schwarz, *Morse Homology*, Birkhäuser, 1993, Chapter 2 (the linearized trajectory operator
  and its dependence on the trivialization along the trajectory).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, §3.1 (the linearized operator in a trivialization and its
  change under a change of trivialization).
-/

public section

noncomputable section

namespace TauCeti.WeakDerivStep

open MeasureTheory TopologicalSpace
open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {mu : Measure ℝ} [mu.IsAddHaarMeasure] {Omega : Opens ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {Φ Ψ : ℝ → F →L[ℝ] F} {ΦL Φ'L ΨL Ψ'L : Lp (F →L[ℝ] F) ∞ (mu.restrict Omega)}

/-- The two components `(Φ u, Φ' u + Φ u')` of the product of an `L∞` path of operators `Φ`, with
`L∞` derivative `Φ'`, and a path `u` of the weak-derivative graph over `Lᵖ`. -/
private def gaugeJetL (ΦL Φ'L : Lp (F →L[ℝ] F) ∞ (mu.restrict Omega)) :
    WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) →L[ℝ]
      WeakDerivStepJetLp mu Omega p (Lp F p (mu.restrict Omega)) F :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.toContinuousLinearMap.comp
    ((((ContinuousLinearMap.id ℝ (F →L[ℝ] F)).holderL (mu.restrict Omega) ∞ p p ΦL).comp
        (prevL _)).prod
      (((ContinuousLinearMap.toSpanSingletonLIE ℝ F).toLinearIsometry.toContinuousLinearMap.compLpL
          p (mu.restrict Omega)).comp
        (((ContinuousLinearMap.id ℝ (F →L[ℝ] F)).holderL (mu.restrict Omega) ∞ p p Φ'L).comp
            (prevL _) +
          ((ContinuousLinearMap.id ℝ (F →L[ℝ] F)).holderL (mu.restrict Omega) ∞ p p ΦL).comp
            (((ContinuousLinearMap.apply ℝ F (1 : ℝ)).compLpL p (mu.restrict Omega)).comp
              (weakFDerivL _)))))

/-- The value component of `gaugeJetL` is the product `Φ u`. -/
private theorem fst_gaugeJetL
    (u : WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))) :
    WithLp.fst (gaugeJetL ΦL Φ'L u) = (ContinuousLinearMap.id ℝ (F →L[ℝ] F)).holder p ΦL
      (prev (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) u) := by
  simp [gaugeJetL, WithLp.prodContinuousLinearEquiv_symm_apply]

/-- The derivative component of `gaugeJetL` is `Φ' u + Φ u'`. -/
private theorem snd_gaugeJetL
    (u : WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))) :
    WithLp.snd (gaugeJetL ΦL Φ'L u) =
      (ContinuousLinearMap.toSpanSingletonLIE ℝ F).toLinearIsometry.toContinuousLinearMap.compLp
        ((ContinuousLinearMap.id ℝ (F →L[ℝ] F)).holder p Φ'L
            (prev (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) u) +
          (ContinuousLinearMap.id ℝ (F →L[ℝ] F)).holder p ΦL
            ((ContinuousLinearMap.apply ℝ F (1 : ℝ)).compLp
              (weakFDeriv (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) u))) := by
  simp only [gaugeJetL, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearEquiv.coe_coe, WithLp.prodContinuousLinearEquiv_symm_apply,
    add_apply, prevL_apply, weakFDerivL_apply, ContinuousLinearMap.holderL_apply_apply,
    WithLp.toLp_snd]
  -- `L.compLpL p μ f` is `L.compLp f` by definition of `ContinuousLinearMap.compLpL`.
  rfl

/-- **The product rule for a path of the weak-derivative graph.** For `Φ` that is `C¹` on `Omega`
with `L∞` class `ΦL`, the product `Φ u` has weak derivative `Φ u' + Φ' u`. -/
private theorem hasWeakLineDerivOn_holder_prev (hΦ : ContDiffOn ℝ 1 Φ Omega)
    (hΦL : ΦL =ᵐ[mu.restrict Omega] Φ)
    (u : WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))) :
    HasWeakLineDerivOn mu Omega
      (⇑((ContinuousLinearMap.id ℝ (F →L[ℝ] F)).holder p ΦL
        (prev (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) u)))
      (fun s ↦ Φ s (weakFDeriv (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) u s 1) +
        deriv Φ s (prev (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) u s)) 1 := by
  let base := ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))
  have hx : HasWeakLineDerivOn mu Omega (⇑(prev base u))
      (fun s ↦ weakFDeriv base u s 1) 1 := by
    simpa only [base, ContinuousLinearMap.id_apply] using
      (hasWeakFDerivOn_base_prev base u).hasWeakLineDerivOn 1
  refine (hx.contDiffOn_clm_apply_of_ne_zero hΦ one_ne_zero).congr_ae ?_
  filter_upwards [(ContinuousLinearMap.id ℝ (F →L[ℝ] F)).coeFn_holder (r := p) ΦL (prev base u),
    hΦL] with s hs hΦs
  rw [hs, hΦs, ContinuousLinearMap.id_apply]

private theorem gaugeJetL_mem (hΦ : ContDiffOn ℝ 1 Φ Omega) (hΦL : ΦL =ᵐ[mu.restrict Omega] Φ)
    (hΦ'L : Φ'L =ᵐ[mu.restrict Omega] deriv Φ)
    (u : WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))) :
    gaugeJetL ΦL Φ'L u ∈
      (weakDerivStepSubmodule mu Omega p
        (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))).toSubmodule := by
  let base := ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))
  let H := ContinuousLinearMap.id ℝ (F →L[ℝ] F)
  let lift := (ContinuousLinearMap.toSpanSingletonLIE ℝ F).toLinearIsometry.toContinuousLinearMap
  let g : Lp F p (mu.restrict Omega) := H.holder p Φ'L (prev base u) +
    H.holder p ΦL ((ContinuousLinearMap.apply ℝ F (1 : ℝ)).compLp (weakFDeriv base u))
  -- The product rule, with the derivative written as the `Lᵖ` path `g`.
  have h : HasWeakLineDerivOn mu Omega (⇑(H.holder p ΦL (prev base u))) g 1 := by
    refine (hasWeakLineDerivOn_holder_prev hΦ hΦL u).congr_ae_deriv ?_
    filter_upwards [Lp.coeFn_add (H.holder p Φ'L (prev base u))
        (H.holder p ΦL ((ContinuousLinearMap.apply ℝ F (1 : ℝ)).compLp (weakFDeriv base u))),
      H.coeFn_holder (r := p) Φ'L (prev base u),
      H.coeFn_holder (r := p) ΦL
        ((ContinuousLinearMap.apply ℝ F (1 : ℝ)).compLp (weakFDeriv base u)),
      (ContinuousLinearMap.apply ℝ F (1 : ℝ)).coeFn_compLp (weakFDeriv base u), hΦL, hΦ'L]
      with s hsum h₁ h₂ h₃ hΦs hΦ's
    rw [hsum, Pi.add_apply, h₁, h₂, h₃, hΦs, hΦ's]
    simp only [H, ContinuousLinearMap.id_apply, ContinuousLinearMap.apply_apply]
    exact add_comm _ _
  have hD : HasWeakFDerivOn mu Omega (⇑(H.holder p ΦL (prev base u))) (lift.compLp g) := by
    rw [hasWeakFDerivOn_iff]
    intro r
    refine (by simpa using h.smul_direction r : HasWeakLineDerivOn _ _ _ _ r).congr_ae_deriv ?_
    filter_upwards [lift.coeFn_compLp g] with s hs
    simp [lift, hs]
  refine (mem_weakDerivStepSubmodule_iff_hasWeakFDerivOn _ _).mpr ?_
  rw [fst_gaugeJetL, snd_gaugeJetL, ContinuousLinearMap.id_apply]
  exact hD

/-- **Multiplication by a `C¹` path of operators** on the weak-derivative graph over `Lᵖ`: the
path `u` goes to `Φ u`, whose weak derivative is `Φ u' + Φ' u`. The factor `Φ` is `C¹` on
`Omega`, and `ΦL` and `Φ'L` are `L∞` classes of `Φ` and of its derivative, so that both are
essentially bounded. -/
def gaugeL (hΦ : ContDiffOn ℝ 1 Φ Omega) (hΦL : ΦL =ᵐ[mu.restrict Omega] Φ)
    (hΦ'L : Φ'L =ᵐ[mu.restrict Omega] deriv Φ) :
    WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) →L[ℝ]
      WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) :=
  (gaugeJetL ΦL Φ'L).codRestrict _ (gaugeJetL_mem hΦ hΦL hΦ'L)

/-- The value of `Φ u` is the product of `Φ` with the value of `u`. -/
@[simp]
theorem prev_gaugeL (hΦ : ContDiffOn ℝ 1 Φ Omega) (hΦL : ΦL =ᵐ[mu.restrict Omega] Φ)
    (hΦ'L : Φ'L =ᵐ[mu.restrict Omega] deriv Φ)
    (u : WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))) :
    prev (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) (gaugeL hΦ hΦL hΦ'L u) =
      (ContinuousLinearMap.id ℝ (F →L[ℝ] F)).holder p ΦL
        (prev (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) u) := by
  rw [prev_coe]
  exact fst_gaugeJetL u

/-- The weak derivative of `Φ u` is `Φ' u + Φ u'`. -/
theorem weakFDeriv_gaugeL (hΦ : ContDiffOn ℝ 1 Φ Omega) (hΦL : ΦL =ᵐ[mu.restrict Omega] Φ)
    (hΦ'L : Φ'L =ᵐ[mu.restrict Omega] deriv Φ)
    (u : WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))) :
    weakFDeriv (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) (gaugeL hΦ hΦL hΦ'L u) =
      (ContinuousLinearMap.toSpanSingletonLIE ℝ F).toLinearIsometry.toContinuousLinearMap.compLp
        ((ContinuousLinearMap.id ℝ (F →L[ℝ] F)).holder p Φ'L
            (prev (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) u) +
          (ContinuousLinearMap.id ℝ (F →L[ℝ] F)).holder p ΦL
            ((ContinuousLinearMap.apply ℝ F (1 : ℝ)).compLp
              (weakFDeriv (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) u))) := by
  rw [weakFDeriv_coe]
  exact snd_gaugeJetL u

/-- **Change of trivialization of the trajectory operator.** If `Φ B = A Φ + Φ'` almost
everywhere on `Omega`, then `D_A (Φ u) = Φ D_B u`. For invertible `Φ` this is the coefficient
`B = Φ⁻¹ A Φ + Φ⁻¹ Φ'`. -/
theorem trajectoryOperator_gaugeL (hΦ : ContDiffOn ℝ 1 Φ Omega)
    (hΦL : ΦL =ᵐ[mu.restrict Omega] Φ) (hΦ'L : Φ'L =ᵐ[mu.restrict Omega] deriv Φ)
    {A B : Lp (F →L[ℝ] F) ∞ (mu.restrict Omega)}
    (hAB : ∀ᵐ s ∂mu.restrict Omega, Φ s ∘L B s = A s ∘L Φ s + deriv Φ s)
    (u : WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))) :
    trajectoryOperator A (gaugeL hΦ hΦL hΦ'L u) =
      (ContinuousLinearMap.id ℝ (F →L[ℝ] F)).holder p ΦL (trajectoryOperator B u) := by
  rw [trajectoryOperator_eq_iff_hasWeakLineDerivOn, prev_gaugeL]
  refine (hasWeakLineDerivOn_holder_prev hΦ hΦL u).congr_ae_deriv ?_
  filter_upwards [(ContinuousLinearMap.id ℝ (F →L[ℝ] F)).coeFn_holder (r := p) ΦL
      (trajectoryOperator B u),
    (ContinuousLinearMap.id ℝ (F →L[ℝ] F)).coeFn_holder (r := p) ΦL
      (prev (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) u),
    trajectoryOperator_apply_ae B u, hΦL, hAB] with s h₁ h₂ hB hΦs hABs
  have hcomp := congrArg
    (fun T : F →L[ℝ] F ↦ T (prev (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) u s)) hABs
  simp only [ContinuousLinearMap.comp_apply, add_apply] at hcomp
  rw [h₁, h₂, hB, hΦs]
  simp only [ContinuousLinearMap.id_apply, map_add, hcomp]
  abel

omit [FiniteDimensional ℝ F] [mu.IsAddHaarMeasure] [Fact (1 ≤ p)] in
/-- Multiplication of `Lᵖ` paths by `Ψ` undoes multiplication by `Φ` where `Ψ Φ = 1`. -/
private theorem holder_holder_of_comp_eq_id (hΦL : ΦL =ᵐ[mu.restrict Omega] Φ)
    (hΨL : ΨL =ᵐ[mu.restrict Omega] Ψ)
    (hΨΦ : ∀ s ∈ (Omega : Set ℝ), Ψ s ∘L Φ s = ContinuousLinearMap.id ℝ F)
    (x : Lp F p (mu.restrict Omega)) :
    (ContinuousLinearMap.id ℝ (F →L[ℝ] F)).holder p ΨL
      ((ContinuousLinearMap.id ℝ (F →L[ℝ] F)).holder p ΦL x) = x := by
  let H := ContinuousLinearMap.id ℝ (F →L[ℝ] F)
  apply Lp.ext
  filter_upwards [H.coeFn_holder (r := p) ΨL (H.holder p ΦL x), H.coeFn_holder (r := p) ΦL x,
    hΦL, hΨL, ae_restrict_mem Omega.isOpen.measurableSet] with s h₁ h₂ hΦs hΨs hs
  rw [h₁, h₂, hΦs, hΨs]
  simpa [H] using congrArg (fun T : F →L[ℝ] F ↦ T (x s)) (hΨΦ s hs)

/-- Multiplication by `Ψ` undoes multiplication by `Φ` on the weak-derivative graph where
`Ψ Φ = 1`. -/
theorem gaugeL_gaugeL (hΦ : ContDiffOn ℝ 1 Φ Omega) (hΦL : ΦL =ᵐ[mu.restrict Omega] Φ)
    (hΦ'L : Φ'L =ᵐ[mu.restrict Omega] deriv Φ) (hΨ : ContDiffOn ℝ 1 Ψ Omega)
    (hΨL : ΨL =ᵐ[mu.restrict Omega] Ψ) (hΨ'L : Ψ'L =ᵐ[mu.restrict Omega] deriv Ψ)
    (hΨΦ : ∀ s ∈ (Omega : Set ℝ), Ψ s ∘L Φ s = ContinuousLinearMap.id ℝ F)
    (u : WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))) :
    gaugeL hΨ hΨL hΨ'L (gaugeL hΦ hΦL hΦ'L u) = u := by
  apply WeakDerivStep.ext
  rw [prev_gaugeL, prev_gaugeL]
  exact holder_holder_of_comp_eq_id hΦL hΨL hΨΦ _

/-- **Multiplication by an invertible `C¹` path of operators** as a continuous linear
automorphism of the weak-derivative graph over `Lᵖ`, with inverse the multiplication by the
pointwise inverse `Ψ`. -/
def gaugeEquiv (hΦ : ContDiffOn ℝ 1 Φ Omega) (hΦL : ΦL =ᵐ[mu.restrict Omega] Φ)
    (hΦ'L : Φ'L =ᵐ[mu.restrict Omega] deriv Φ) (hΨ : ContDiffOn ℝ 1 Ψ Omega)
    (hΨL : ΨL =ᵐ[mu.restrict Omega] Ψ) (hΨ'L : Ψ'L =ᵐ[mu.restrict Omega] deriv Ψ)
    (hΨΦ : ∀ s ∈ (Omega : Set ℝ), Ψ s ∘L Φ s = ContinuousLinearMap.id ℝ F)
    (hΦΨ : ∀ s ∈ (Omega : Set ℝ), Φ s ∘L Ψ s = ContinuousLinearMap.id ℝ F) :
    WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) ≃L[ℝ]
      WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) :=
  ContinuousLinearEquiv.equivOfInverse (gaugeL hΦ hΦL hΦ'L) (gaugeL hΨ hΨL hΨ'L)
    (gaugeL_gaugeL hΦ hΦL hΦ'L hΨ hΨL hΨ'L hΨΦ) (gaugeL_gaugeL hΨ hΨL hΨ'L hΦ hΦL hΦ'L hΦΨ)

/-- The automorphism `gaugeEquiv` is multiplication by `Φ`. -/
@[simp]
theorem gaugeEquiv_apply (hΦ : ContDiffOn ℝ 1 Φ Omega) (hΦL : ΦL =ᵐ[mu.restrict Omega] Φ)
    (hΦ'L : Φ'L =ᵐ[mu.restrict Omega] deriv Φ) (hΨ : ContDiffOn ℝ 1 Ψ Omega)
    (hΨL : ΨL =ᵐ[mu.restrict Omega] Ψ) (hΨ'L : Ψ'L =ᵐ[mu.restrict Omega] deriv Ψ)
    (hΨΦ : ∀ s ∈ (Omega : Set ℝ), Ψ s ∘L Φ s = ContinuousLinearMap.id ℝ F)
    (hΦΨ : ∀ s ∈ (Omega : Set ℝ), Φ s ∘L Ψ s = ContinuousLinearMap.id ℝ F)
    (u : WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))) :
    gaugeEquiv hΦ hΦL hΦ'L hΨ hΨL hΨ'L hΨΦ hΦΨ u = gaugeL hΦ hΦL hΦ'L u :=
  (rfl)

/-- The inverse of `gaugeEquiv` is multiplication by `Ψ`. -/
@[simp]
theorem gaugeEquiv_symm_apply (hΦ : ContDiffOn ℝ 1 Φ Omega) (hΦL : ΦL =ᵐ[mu.restrict Omega] Φ)
    (hΦ'L : Φ'L =ᵐ[mu.restrict Omega] deriv Φ) (hΨ : ContDiffOn ℝ 1 Ψ Omega)
    (hΨL : ΨL =ᵐ[mu.restrict Omega] Ψ) (hΨ'L : Ψ'L =ᵐ[mu.restrict Omega] deriv Ψ)
    (hΨΦ : ∀ s ∈ (Omega : Set ℝ), Ψ s ∘L Φ s = ContinuousLinearMap.id ℝ F)
    (hΦΨ : ∀ s ∈ (Omega : Set ℝ), Φ s ∘L Ψ s = ContinuousLinearMap.id ℝ F)
    (u : WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))) :
    (gaugeEquiv hΦ hΦL hΦ'L hΨ hΨL hΨ'L hΨΦ hΦΨ).symm u = gaugeL hΨ hΨL hΨ'L u :=
  (rfl)

section Invertible

variable (hΦ : ContDiffOn ℝ 1 Φ Omega) (hΦL : ΦL =ᵐ[mu.restrict Omega] Φ)
  (hΦ'L : Φ'L =ᵐ[mu.restrict Omega] deriv Φ) (hΨ : ContDiffOn ℝ 1 Ψ Omega)
  (hΨL : ΨL =ᵐ[mu.restrict Omega] Ψ) (hΨ'L : Ψ'L =ᵐ[mu.restrict Omega] deriv Ψ)
  (hΨΦ : ∀ s ∈ (Omega : Set ℝ), Ψ s ∘L Φ s = ContinuousLinearMap.id ℝ F)
  (hΦΨ : ∀ s ∈ (Omega : Set ℝ), Φ s ∘L Ψ s = ContinuousLinearMap.id ℝ F)
  {A B : Lp (F →L[ℝ] F) ∞ (mu.restrict Omega)}
  (hAB : ∀ᵐ s ∂mu.restrict Omega, Φ s ∘L B s = A s ∘L Φ s + deriv Φ s)
include hΦ hΦL hΦ'L hΨ hΨL hΨ'L hΨΦ hΦΨ hAB

/-- Multiplication of `Lᵖ` paths by `Φ`, an isomorphism with inverse the multiplication by `Ψ`. -/
private def mulEquiv : Lp F p (mu.restrict Omega) ≃L[ℝ] Lp F p (mu.restrict Omega) :=
  ContinuousLinearEquiv.equivOfInverse
    ((ContinuousLinearMap.id ℝ (F →L[ℝ] F)).holderL (mu.restrict Omega) ∞ p p ΦL)
    ((ContinuousLinearMap.id ℝ (F →L[ℝ] F)).holderL (mu.restrict Omega) ∞ p p ΨL)
    (holder_holder_of_comp_eq_id hΦL hΨL hΨΦ) (holder_holder_of_comp_eq_id hΨL hΦL hΦΨ)

/-- `D_A = Φ ∘ D_B ∘ Φ⁻¹` as maps from the weak-derivative graph to `Lᵖ`. -/
private theorem trajectoryOperator_eq_comp :
    trajectoryOperator (p := p) A =
      ((mulEquiv (p := p) hΦL hΨL hΨΦ hΦΨ : Lp F p (mu.restrict Omega) ≃L[ℝ] _) :
          Lp F p (mu.restrict Omega) →L[ℝ] Lp F p (mu.restrict Omega)) ∘L
        trajectoryOperator B ∘L
          ((gaugeEquiv (p := p) hΦ hΦL hΦ'L hΨ hΨL hΨ'L hΨΦ hΦΨ).symm :
            WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) →L[ℝ]
              WeakDerivStep mu Omega p
                (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))) := by
  ext1 u
  conv_lhs => rw [← (gaugeEquiv (p := p) hΦ hΦL hΦ'L hΨ hΨL hΨ'L hΨΦ hΦΨ).apply_symm_apply u]
  rw [gaugeEquiv_apply, trajectoryOperator_gaugeL hΦ hΦL hΦ'L hAB]
  -- The right side is the composite applied to `u`, and `mulEquiv` acts as multiplication by
  -- `ΦL`, both by definition.
  rfl

/-- **The kernel under a change of trivialization**: the kernel of `D_A` is the image of the
kernel of `D_B` under multiplication by `Φ`. -/
theorem ker_trajectoryOperator_eq_map_gaugeL :
    LinearMap.ker (trajectoryOperator (p := p) A).toLinearMap =
      (LinearMap.ker (trajectoryOperator (p := p) B).toLinearMap).map
        (gaugeL (p := p) hΦ hΦL hΦ'L).toLinearMap := by
  ext u
  rw [trajectoryOperator_eq_comp hΦ hΦL hΦ'L hΨ hΨL hΨ'L hΨΦ hΦΨ hAB]
  constructor
  · intro hu
    refine ⟨gaugeL hΨ hΨL hΨ'L u, ?_, gaugeL_gaugeL hΨ hΨL hΨ'L hΦ hΦL hΦ'L hΦΨ u⟩
    simpa [LinearMap.mem_ker] using hu
  · rintro ⟨w, hw, rfl⟩
    simpa [LinearMap.mem_ker, gaugeL_gaugeL hΦ hΦL hΦ'L hΨ hΨL hΨ'L hΨΦ] using hw

/-- **The Fredholm property does not depend on the trivialization**: `D_A` is Fredholm exactly
when `D_B` is. -/
theorem isFredholm_trajectoryOperator_iff_of_gauge :
    (trajectoryOperator (p := p) A).IsFredholm ↔ (trajectoryOperator (p := p) B).IsFredholm := by
  rw [trajectoryOperator_eq_comp hΦ hΦL hΦ'L hΨ hΨL hΨ'L hΨΦ hΦΨ hAB,
    ContinuousLinearMap.isFredholm_equiv_comp, ContinuousLinearMap.isFredholm_comp_equiv]

/-- **The index does not depend on the trivialization**: if `D_B` is Fredholm, then `D_A` has the
same index. -/
theorem index_trajectoryOperator_eq_of_gauge (hB : (trajectoryOperator (p := p) B).IsFredholm) :
    (trajectoryOperator (p := p) A).index = (trajectoryOperator (p := p) B).index := by
  have hG := (gaugeEquiv (p := p) hΦ hΦL hΦ'L hΨ hΨL hΨ'L hΨΦ hΦΨ).symm.isFredholm
  have hM := (mulEquiv (p := p) hΦL hΨL hΨΦ hΦΨ).isFredholm
  have hG0 : ((gaugeEquiv (p := p) hΦ hΦL hΦ'L hΨ hΨL hΨ'L hΨΦ hΦΨ).symm :
      WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) →L[ℝ]
        WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))).index =
      0 :=
    LinearMap.index_of_bijective
      (gaugeEquiv (p := p) hΦ hΦL hΦ'L hΨ hΨL hΨ'L hΨΦ hΦΨ).symm.bijective
  have hM0 : ((mulEquiv (p := p) hΦL hΨL hΨΦ hΦΨ : Lp F p (mu.restrict Omega) ≃L[ℝ] _) :
      Lp F p (mu.restrict Omega) →L[ℝ] Lp F p (mu.restrict Omega)).index = 0 :=
    LinearMap.index_of_bijective (mulEquiv (p := p) hΦL hΨL hΨΦ hΦΨ).bijective
  rw [trajectoryOperator_eq_comp hΦ hΦL hΦ'L hΨ hΨL hΨ'L hΨΦ hΦΨ hAB,
    hM.index_comp (hB.comp hG), hB.index_comp hG, hM0, hG0, zero_add, add_zero]

end Invertible

end TauCeti.WeakDerivStep
