/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import TauCeti.Analysis.ODE.TrajectoryOperator
public import TauCeti.MeasureTheory.Function.Lp.Holder
import TauCeti.Algebra.Module.LinearMap.Index
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
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
operator-valued factor (`TauCeti.HasWeakFDerivOn.contDiffOn_clm_apply_of_ne_zero`). When `Φ`
has an essentially bounded pointwise left inverse `Ψ`, then `Ψ` is a two-sided inverse, as `F` is
finite-dimensional, and is `C¹` with the essentially bounded derivative `-Ψ Φ' Ψ`. So
multiplication by `Φ` is an isomorphism (`TauCeti.WeakDerivStep.gaugeEquiv`) of the
weak-derivative graph, and also of `Lᵖ` (`MeasureTheory.Lp.pointwiseApplyEquiv`). The change of
trivialization therefore identifies the two operators, `D_A = Φ ∘ D_B ∘ Φ⁻¹`: `D_A` and `D_B`
have kernels corresponding under multiplication by `Φ`, one is Fredholm exactly when the other is,
and their indices agree.
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
* `TauCeti.WeakDerivStep.trajectoryOperator_eq_holderL_comp_gaugeEquiv_symm`:
  `D_A = Φ ∘ D_B ∘ Φ⁻¹`.
* `TauCeti.WeakDerivStep.ker_trajectoryOperator_eq_map_gaugeL`: the kernel of `D_A` is the image
  of the kernel of `D_B` under multiplication by `Φ`.
* `TauCeti.WeakDerivStep.isFredholm_trajectoryOperator_iff_of_gauge` and
  `TauCeti.WeakDerivStep.index_trajectoryOperator_eq_of_gauge`: `D_A` is Fredholm exactly when
  `D_B` is, and both have the same index.

## References

* M. Schwarz, *Morse Homology*, Birkhäuser, 1993, Chapter 2 (the linearized trajectory operator
  and its dependence on the trivialization along the trajectory).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, §3.1 (the linearized operator in a trivialization and its
  change under a change of trivialization).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal

namespace TauCeti.WeakDerivStep

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
  -- The product rule, with the derivative written through the `Lᵖ` path `g`.
  have hD : HasWeakFDerivOn mu Omega (⇑(H.holder p ΦL (prev base u))) (lift.compLp g) := by
    have hu : HasWeakFDerivOn mu Omega (⇑(prev base u)) (weakFDeriv base u) := by
      simpa only [base, ContinuousLinearMap.id_apply] using hasWeakFDerivOn_base_prev base u
    refine ((hu.contDiffOn_clm_apply_of_ne_zero hΦ one_ne_zero).congr_ae ?_).congr_ae_deriv ?_
    · filter_upwards [H.coeFn_holder (r := p) ΦL (prev base u), hΦL] with s hs hΦs
      rw [hs, hΦs, ContinuousLinearMap.id_apply]
    · filter_upwards [lift.coeFn_compLp g, Lp.coeFn_add (H.holder p Φ'L (prev base u))
          (H.holder p ΦL ((ContinuousLinearMap.apply ℝ F (1 : ℝ)).compLp (weakFDeriv base u))),
        H.coeFn_holder (r := p) Φ'L (prev base u),
        H.coeFn_holder (r := p) ΦL
          ((ContinuousLinearMap.apply ℝ F (1 : ℝ)).compLp (weakFDeriv base u)),
        (ContinuousLinearMap.apply ℝ F (1 : ℝ)).coeFn_compLp (weakFDeriv base u), hΦL, hΦ'L]
        with s hs hsum h₁ h₂ h₃ hΦs hΦ's
      ext1
      rw [hs, hsum, Pi.add_apply, h₁, h₂, h₃, hΦs, hΦ's]
      simp [H, lift, add_comm]
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
@[simp]
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
  let base := ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))
  let H := ContinuousLinearMap.id ℝ (F →L[ℝ] F)
  let ev := ContinuousLinearMap.apply ℝ F (1 : ℝ)
  let lift := (ContinuousLinearMap.toSpanSingletonLIE ℝ F).toLinearIsometry.toContinuousLinearMap
  -- The weak derivative of `Φ u` is the one recorded by `weakFDeriv_gaugeL`.
  have hA := trajectoryOperator_apply_ae A (gaugeL hΦ hΦL hΦ'L u)
  rw [weakFDeriv_gaugeL, prev_gaugeL] at hA
  apply Lp.ext
  filter_upwards [hA, H.coeFn_holder (r := p) ΦL (trajectoryOperator B u),
    trajectoryOperator_apply_ae B u,
    lift.coeFn_compLp (H.holder p Φ'L (prev base u) +
      H.holder p ΦL (ev.compLp (weakFDeriv base u))),
    Lp.coeFn_add (H.holder p Φ'L (prev base u)) (H.holder p ΦL (ev.compLp (weakFDeriv base u))),
    H.coeFn_holder (r := p) Φ'L (prev base u),
    H.coeFn_holder (r := p) ΦL (ev.compLp (weakFDeriv base u)),
    ev.coeFn_compLp (weakFDeriv base u), H.coeFn_holder (r := p) ΦL (prev base u), hΦL, hΦ'L,
    hAB] with s hAs h₁ hBs hl hsum h₂ h₃ h₄ h₅ hΦs hΦ's hABs
  have hcomp := congrArg (fun T : F →L[ℝ] F ↦ T (prev base u s)) hABs
  simp only [ContinuousLinearMap.comp_apply, add_apply] at hcomp
  rw [hAs, h₁, hBs, hl, hsum, Pi.add_apply, h₂, h₃, h₄, h₅, hΦs, hΦ's]
  simp [H, lift, ev, base, hcomp]
  abel

omit [FiniteDimensional ℝ F] [mu.IsAddHaarMeasure] in
/-- The pointwise identity `Ψ Φ = 1` on `Omega` for the `L∞` classes of `Φ` and `Ψ`. -/
private theorem ae_comp_eq_id (hΦL : ΦL =ᵐ[mu.restrict Omega] Φ)
    (hΨL : ΨL =ᵐ[mu.restrict Omega] Ψ)
    (hΨΦ : ∀ s ∈ (Omega : Set ℝ), Ψ s ∘L Φ s = ContinuousLinearMap.id ℝ F) :
    ∀ᵐ s ∂mu.restrict Omega, ΨL s ∘L ΦL s = ContinuousLinearMap.id ℝ F := by
  filter_upwards [hΦL, hΨL, ae_restrict_mem Omega.isOpen.measurableSet] with s hΦs hΨs hs
  rw [hΦs, hΨs]
  exact hΨΦ s hs

/-- Multiplication by `Ψ` undoes multiplication by `Φ` on the weak-derivative graph where
`Ψ Φ = 1`. -/
theorem gaugeL_gaugeL_of_comp_eq_id (hΦ : ContDiffOn ℝ 1 Φ Omega) (hΦL : ΦL =ᵐ[mu.restrict Omega] Φ)
    (hΦ'L : Φ'L =ᵐ[mu.restrict Omega] deriv Φ) (hΨ : ContDiffOn ℝ 1 Ψ Omega)
    (hΨL : ΨL =ᵐ[mu.restrict Omega] Ψ) (hΨ'L : Ψ'L =ᵐ[mu.restrict Omega] deriv Ψ)
    (hΨΦ : ∀ s ∈ (Omega : Set ℝ), Ψ s ∘L Φ s = ContinuousLinearMap.id ℝ F)
    (u : WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))) :
    gaugeL hΨ hΨL hΨ'L (gaugeL hΦ hΦL hΦ'L u) = u := by
  apply WeakDerivStep.ext
  rw [prev_gaugeL, prev_gaugeL]
  exact ContinuousLinearMap.holder_holder_of_comp_eq_id (ae_comp_eq_id hΦL hΨL hΨΦ) _

omit [mu.IsAddHaarMeasure] in
/-- A left inverse `Ψ s` of `Φ s` is also a right inverse, as `F` is finite-dimensional. -/
private theorem comp_eq_id_of_comp_eq_id
    (hΨΦ : ∀ s ∈ (Omega : Set ℝ), Ψ s ∘L Φ s = ContinuousLinearMap.id ℝ F) :
    ∀ s ∈ (Omega : Set ℝ), Φ s ∘L Ψ s = ContinuousLinearMap.id ℝ F := by
  intro s hs
  have h : (Ψ s : F →ₗ[ℝ] F) ∘ₗ (Φ s : F →ₗ[ℝ] F) = LinearMap.id := by
    simpa using congrArg (fun T : F →L[ℝ] F ↦ (T : F →ₗ[ℝ] F)) (hΨΦ s hs)
  ext x
  simpa using LinearMap.congr_fun ((LinearMap.comp_eq_id_comm ℝ F).mp h) x

omit [mu.IsAddHaarMeasure] in
/-- On `Omega`, `Φ s` is invertible with inverse `Ψ s`. -/
private theorem isInvertible_and_inverse_eq
    (hΨΦ : ∀ s ∈ (Omega : Set ℝ), Ψ s ∘L Φ s = ContinuousLinearMap.id ℝ F) {s : ℝ}
    (hs : s ∈ (Omega : Set ℝ)) : (Φ s).IsInvertible ∧ (Φ s).inverse = Ψ s :=
  ⟨.of_inverse (comp_eq_id_of_comp_eq_id hΨΦ s hs) (hΨΦ s hs),
    ContinuousLinearMap.inverse_eq (comp_eq_id_of_comp_eq_id hΨΦ s hs) (hΨΦ s hs)⟩

/-- The `L∞` class `-Ψ Φ' Ψ` of the derivative of the pointwise inverse `Ψ` of `Φ`. -/
private def invDerivL (Φ'L ΨL : Lp (F →L[ℝ] F) ∞ (mu.restrict Omega)) :
    Lp (F →L[ℝ] F) ∞ (mu.restrict Omega) :=
  -(ContinuousLinearMap.compL ℝ F F F).holder ∞ ΨL
    ((ContinuousLinearMap.compL ℝ F F F).holder ∞ Φ'L ΨL)

omit [mu.IsAddHaarMeasure] in
/-- `invDerivL Φ'L ΨL` is an `L∞` class of the derivative of the pointwise inverse `Ψ` of `Φ`. -/
private theorem invDerivL_ae_eq (hΦ : ContDiffOn ℝ 1 Φ Omega)
    (hΦ'L : Φ'L =ᵐ[mu.restrict Omega] deriv Φ) (hΨL : ΨL =ᵐ[mu.restrict Omega] Ψ)
    (hΨΦ : ∀ s ∈ (Omega : Set ℝ), Ψ s ∘L Φ s = ContinuousLinearMap.id ℝ F) :
    invDerivL Φ'L ΨL =ᵐ[mu.restrict Omega] deriv Ψ := by
  filter_upwards [Lp.coeFn_neg ((ContinuousLinearMap.compL ℝ F F F).holder ∞ ΨL
      ((ContinuousLinearMap.compL ℝ F F F).holder ∞ Φ'L ΨL)),
    (ContinuousLinearMap.compL ℝ F F F).coeFn_holder (r := ∞) ΨL
      ((ContinuousLinearMap.compL ℝ F F F).holder ∞ Φ'L ΨL),
    (ContinuousLinearMap.compL ℝ F F F).coeFn_holder (r := ∞) Φ'L ΨL, hΨL, hΦ'L,
    ae_restrict_mem Omega.isOpen.measurableSet] with s h₀ h₁ h₂ hΨs hΦ's hs
  -- Near `s`, `Ψ` is the inverse of `Φ`, whose derivative is `-Ψ Φ' Ψ`.
  have hd : HasDerivAt Φ (deriv Φ s) s :=
    ((hΦ.differentiableOn one_ne_zero s hs).differentiableAt
      (Omega.isOpen.mem_nhds hs)).hasDerivAt
  have hΨ : Ψ =ᶠ[nhds s] fun t ↦ (Φ t).inverse := by
    filter_upwards [Omega.isOpen.mem_nhds hs] with t ht
    exact (isInvertible_and_inverse_eq hΨΦ ht).2.symm
  obtain ⟨hinv, hΨs'⟩ := isInvertible_and_inverse_eq hΨΦ hs
  rw [invDerivL, h₀, Pi.neg_apply, h₁, h₂, hΨs, hΦ's,
    ((hd.clm_inverse_of_completeSpace hinv).congr_of_eventuallyEq hΨ).deriv, hΨs',
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.compL_apply]

/-- The pointwise inverse `Ψ` of a `C¹` path `Φ` is `C¹` on `Omega`. -/
private theorem contDiffOn_of_comp_eq_id (hΦ : ContDiffOn ℝ 1 Φ Omega)
    (hΨΦ : ∀ s ∈ (Omega : Set ℝ), Ψ s ∘L Φ s = ContinuousLinearMap.id ℝ F) :
    ContDiffOn ℝ 1 Ψ Omega :=
  (hΦ.clm_inverse fun _ hs ↦ (isInvertible_and_inverse_eq hΨΦ hs).1).congr
    fun _ hs ↦ (isInvertible_and_inverse_eq hΨΦ hs).2.symm

/-- **Multiplication by an invertible `C¹` path of operators** as a continuous linear
automorphism of the weak-derivative graph over `Lᵖ`, with inverse the multiplication by the
pointwise inverse `Ψ`. Only the `L∞` class `ΨL` of `Ψ` is needed: `Ψ` is then `C¹` with the
essentially bounded derivative `-Ψ Φ' Ψ`. -/
def gaugeEquiv (hΦ : ContDiffOn ℝ 1 Φ Omega) (hΦL : ΦL =ᵐ[mu.restrict Omega] Φ)
    (hΦ'L : Φ'L =ᵐ[mu.restrict Omega] deriv Φ) (hΨL : ΨL =ᵐ[mu.restrict Omega] Ψ)
    (hΨΦ : ∀ s ∈ (Omega : Set ℝ), Ψ s ∘L Φ s = ContinuousLinearMap.id ℝ F) :
    WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) ≃L[ℝ]
      WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) :=
  ContinuousLinearEquiv.ofContinuousLinearMap (gaugeL hΦ hΦL hΦ'L)
    (gaugeL (contDiffOn_of_comp_eq_id hΦ hΨΦ) hΨL (invDerivL_ae_eq hΦ hΦ'L hΨL hΨΦ))
    (ContinuousLinearMap.ext (gaugeL_gaugeL_of_comp_eq_id (contDiffOn_of_comp_eq_id hΦ hΨΦ) hΨL
      (invDerivL_ae_eq hΦ hΦ'L hΨL hΨΦ) hΦ hΦL hΦ'L (comp_eq_id_of_comp_eq_id hΨΦ)))
    (ContinuousLinearMap.ext (gaugeL_gaugeL_of_comp_eq_id hΦ hΦL hΦ'L
      (contDiffOn_of_comp_eq_id hΦ hΨΦ) hΨL (invDerivL_ae_eq hΦ hΦ'L hΨL hΨΦ) hΨΦ))

/-- The automorphism `gaugeEquiv` is multiplication by `Φ`. -/
@[simp]
theorem gaugeEquiv_apply (hΦ : ContDiffOn ℝ 1 Φ Omega) (hΦL : ΦL =ᵐ[mu.restrict Omega] Φ)
    (hΦ'L : Φ'L =ᵐ[mu.restrict Omega] deriv Φ) (hΨL : ΨL =ᵐ[mu.restrict Omega] Ψ)
    (hΨΦ : ∀ s ∈ (Omega : Set ℝ), Ψ s ∘L Φ s = ContinuousLinearMap.id ℝ F)
    (u : WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))) :
    gaugeEquiv hΦ hΦL hΦ'L hΨL hΨΦ u = gaugeL hΦ hΦL hΦ'L u :=
  congrFun (ContinuousLinearEquiv.coe_ofContinuousLinearMap _ _ _ _) u

/-- The inverse of `gaugeEquiv` is multiplication by `Ψ`: its value is the product of `Ψ` with
the value of `u`. -/
@[simp]
theorem prev_gaugeEquiv_symm_apply (hΦ : ContDiffOn ℝ 1 Φ Omega)
    (hΦL : ΦL =ᵐ[mu.restrict Omega] Φ) (hΦ'L : Φ'L =ᵐ[mu.restrict Omega] deriv Φ)
    (hΨL : ΨL =ᵐ[mu.restrict Omega] Ψ)
    (hΨΦ : ∀ s ∈ (Omega : Set ℝ), Ψ s ∘L Φ s = ContinuousLinearMap.id ℝ F)
    (u : WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))) :
    prev (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))
        ((gaugeEquiv hΦ hΦL hΦ'L hΨL hΨΦ).symm u) =
      (ContinuousLinearMap.id ℝ (F →L[ℝ] F)).holder p ΨL
        (prev (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) u) := by
  rw [gaugeEquiv, ContinuousLinearEquiv.symm_ofContinuousLinearMap,
    ContinuousLinearEquiv.coe_ofContinuousLinearMap]
  exact prev_gaugeL (contDiffOn_of_comp_eq_id hΦ hΨΦ) hΨL (invDerivL_ae_eq hΦ hΦ'L hΨL hΨΦ) u

section Invertible

variable (hΦ : ContDiffOn ℝ 1 Φ Omega) (hΦL : ΦL =ᵐ[mu.restrict Omega] Φ)
  (hΦ'L : Φ'L =ᵐ[mu.restrict Omega] deriv Φ) (hΨL : ΨL =ᵐ[mu.restrict Omega] Ψ)
  (hΨΦ : ∀ s ∈ (Omega : Set ℝ), Ψ s ∘L Φ s = ContinuousLinearMap.id ℝ F)
  {A B : Lp (F →L[ℝ] F) ∞ (mu.restrict Omega)}
  (hAB : ∀ᵐ s ∂mu.restrict Omega, Φ s ∘L B s = A s ∘L Φ s + deriv Φ s)
include hΦ hΦL hΦ'L hΨL hΨΦ hAB

/-- **`D_A = Φ ∘ D_B ∘ Φ⁻¹`** as maps from the weak-derivative graph to `Lᵖ`: the trajectory
operator `D_A` is conjugate to `D_B` by multiplication by `Φ` on the weak-derivative graph and
on `Lᵖ`. The latter is the automorphism `MeasureTheory.Lp.pointwiseApplyEquiv` of `Lᵖ`. -/
theorem trajectoryOperator_eq_holderL_comp_gaugeEquiv_symm :
    trajectoryOperator (p := p) A =
      (ContinuousLinearMap.id ℝ (F →L[ℝ] F)).holderL (mu.restrict Omega) ∞ p p ΦL ∘L
        trajectoryOperator B ∘L
          ((gaugeEquiv (p := p) hΦ hΦL hΦ'L hΨL hΨΦ).symm :
            WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) →L[ℝ]
              WeakDerivStep mu Omega p
                (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))) := by
  ext1 u
  conv_lhs => rw [← (gaugeEquiv (p := p) hΦ hΦL hΦ'L hΨL hΨΦ).apply_symm_apply u]
  rw [gaugeEquiv_apply, trajectoryOperator_gaugeL hΦ hΦL hΦ'L hAB]
  -- The right side is the composite applied to `u`, by definition.
  rfl

/-- `D_A = Φ ∘ D_B ∘ Φ⁻¹`, with multiplication by `Φ` on `Lᵖ` written as the equivalence
`MeasureTheory.Lp.pointwiseApplyEquiv`. -/
private theorem trajectoryOperator_eq_pointwiseApplyEquiv_comp :
    trajectoryOperator (p := p) A =
      (Lp.pointwiseApplyEquiv p (ae_comp_eq_id hΦL hΨL hΨΦ)
          (ae_comp_eq_id hΨL hΦL (comp_eq_id_of_comp_eq_id hΨΦ)) :
          Lp F p (mu.restrict Omega) →L[ℝ] Lp F p (mu.restrict Omega)) ∘L
        trajectoryOperator B ∘L
          ((gaugeEquiv (p := p) hΦ hΦL hΦ'L hΨL hΨΦ).symm :
            WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) →L[ℝ]
              WeakDerivStep mu Omega p
                (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))) := by
  rw [Lp.coe_pointwiseApplyEquiv]
  exact trajectoryOperator_eq_holderL_comp_gaugeEquiv_symm hΦ hΦL hΦ'L hΨL hΨΦ hAB

/-- **The kernel under a change of trivialization**: the kernel of `D_A` is the image of the
kernel of `D_B` under multiplication by `Φ`. -/
theorem ker_trajectoryOperator_eq_map_gaugeL :
    LinearMap.ker (trajectoryOperator (p := p) A).toLinearMap =
      (LinearMap.ker (trajectoryOperator (p := p) B).toLinearMap).map
        (gaugeL (p := p) hΦ hΦL hΦ'L).toLinearMap := by
  rw [trajectoryOperator_eq_pointwiseApplyEquiv_comp hΦ hΦL hΦ'L hΨL hΨΦ hAB,
    ContinuousLinearMap.toLinearMap_comp,
    ContinuousLinearMap.toLinearMap_comp, ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap,
    ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap, LinearEquiv.ker_comp,
    LinearMap.ker_comp, Submodule.comap_equiv_eq_map_symm,
    ContinuousLinearEquiv.toLinearEquiv_symm, LinearEquiv.symm_symm]
  exact congrArg (Submodule.map · _) (LinearMap.ext (gaugeEquiv_apply hΦ hΦL hΦ'L hΨL hΨΦ))

/-- **The Fredholm property does not depend on the trivialization**: `D_A` is Fredholm exactly
when `D_B` is. -/
theorem isFredholm_trajectoryOperator_iff_of_gauge :
    (trajectoryOperator (p := p) A).IsFredholm ↔ (trajectoryOperator (p := p) B).IsFredholm := by
  rw [trajectoryOperator_eq_pointwiseApplyEquiv_comp hΦ hΦL hΦ'L hΨL hΨΦ hAB,
    ContinuousLinearMap.isFredholm_equiv_comp,
    ContinuousLinearMap.isFredholm_comp_equiv]

/-- **The index does not depend on the trivialization**: `D_A` and `D_B` have the same index. -/
theorem index_trajectoryOperator_eq_of_gauge :
    (trajectoryOperator (p := p) A).index = (trajectoryOperator (p := p) B).index := by
  rw [trajectoryOperator_eq_pointwiseApplyEquiv_comp hΦ hΦL hΦ'L hΨL hΨΦ hAB,
    ContinuousLinearMap.toLinearMap_comp,
    ContinuousLinearMap.toLinearMap_comp, ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap,
    ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap, LinearMap.index_equiv_comp,
    LinearMap.index_comp_equiv]

end Invertible

end TauCeti.WeakDerivStep
