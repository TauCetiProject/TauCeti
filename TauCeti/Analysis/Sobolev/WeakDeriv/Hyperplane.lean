/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Distribution.TestFunction.Prod
import TauCeti.Analysis.Sobolev.WeakDeriv.MeasurePreserving

/-!
# Obstruction to weak differentiation across a hyperplane

A jump discontinuity across a hyperplane produces a surface measure in the distributional first
derivative, so it cannot be represented by a locally integrable function. Concretely, for any
nonzero continuous linear functional `ℓ` on a finite-dimensional real normed space `E` carrying a
Borel additive Haar measure `μ`, the open half-space indicator `{x | 0 < ℓ x}.indicator 1` admits
no weak Fréchet derivative (`TauCeti.HasWeakFDerivOn`) on any open set `Ω` meeting the hyperplane
`{x | ℓ x = 0}`.

The proof pulls the domain back along a continuous linear splitting
`ℝ × EuclideanSpace ℝ (Fin d) ≃L[ℝ] E`
(`TauCeti.HasWeakFDerivOn.comp_continuousLinearEquiv_of_isAddHaarMeasure`), observes that any
normal weak derivative must vanish almost everywhere on both open half-spaces
(`TauCeti.HasWeakLineDerivOn.ae_eq_zero_of_isOpen`), and tests against a tensor-product bump
function (`TestFunction.prodSMulCLM`), evaluating the half-line integral with Mathlib's
`HasCompactSupport.integral_Ioi_deriv_eq`.

## Main declarations

* `TauCeti.not_hasWeakFDerivOn_indicator_pos`: the indicator of `{x | 0 < ℓ x}` (`ℓ ≠ 0`) has no
  weak Fréchet derivative on any open set meeting `{x | ℓ x = 0}`.

## References

* W. P. Ziemer, *Weakly Differentiable Functions*, Graduate Texts in Mathematics 120, Springer,
  1989, §2.1.
-/

public section

open Filter LineDeriv MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Distributions Topology

namespace TauCeti

/-- Model case on `ℝ × EuclideanSpace ℝ (Fin d)`: the indicator of `{q | 0 < q.1}` has no weak
Fréchet derivative on any open set containing a point `(0, y₀)`. -/
private theorem not_hasWeakFDerivOn_indicator_fst_pos {d : ℕ}
    {Ω : Opens (ℝ × EuclideanSpace ℝ (Fin d))} {y₀ : EuclideanSpace ℝ (Fin d)}
    (h0 : ((0 : ℝ), y₀) ∈ Ω)
    (Du : ℝ × EuclideanSpace ℝ (Fin d) → (ℝ × EuclideanSpace ℝ (Fin d)) →L[ℝ] ℝ) :
    ¬ HasWeakFDerivOn volume Ω
        ({q : ℝ × EuclideanSpace ℝ (Fin d) | 0 < q.1}.indicator fun _ => (1 : ℝ)) Du := by
  intro hDu
  let Y := EuclideanSpace ℝ (Fin d)
  have : (volume : Measure (ℝ × Y)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure volume volume
  set u : ℝ × Y → ℝ := {q : ℝ × Y | 0 < q.1}.indicator fun _ => (1 : ℝ) with hu
  -- On `{q | q.1 < 0}` and `{q | 0 < q.1}` the indicator is locally constant, while `{q | q.1 = 0}`
  -- is null, so the normal weak derivative `q ↦ Du q (1, 0)` vanishes almost everywhere on `Ω`.
  have hline0 : HasWeakLineDerivOn volume Ω u (fun q => Du q (1, 0)) (1, 0) :=
    hDu.hasWeakLineDerivOn ((1 : ℝ), (0 : Y))
  have hn : ∀ᵐ q ∂volume.restrict Ω, q.1 < 0 → Du q (1, 0) = 0 :=
    hline0.ae_eq_zero_of_isOpen (isOpen_lt continuous_fst continuous_const) <|
      Eventually.of_forall fun q (hq : q.1 < 0) => indicator_of_notMem hq.not_gt _
  have hp : ∀ᵐ q ∂volume.restrict Ω, 0 < q.1 → Du q (1, 0) = 0 := by
    have hsub :=
      hline0.sub (hasWeakLineDerivOn_const (μ := volume) (Ω := Ω) (v := ((1 : ℝ), (0 : Y))) (1 : ℝ))
    filter_upwards [hsub.ae_eq_zero_of_isOpen (isOpen_lt continuous_const continuous_fst) <|
      Eventually.of_forall fun q (hq : 0 < q.1) => by simp [hu, hq]] with q hq hq0
    simpa using hq hq0
  have hnull : (volume : Measure (ℝ × Y)) {q : ℝ × Y | q.1 = 0} = 0 := by
    have heq : {q : ℝ × Y | q.1 = 0} = ({0} : Set ℝ) ×ˢ (univ : Set Y) := by
      ext ⟨t, y⟩
      simp
    rw [heq, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]
  have hDu0 : (fun q => Du q (1, 0)) =ᵐ[volume.restrict Ω] 0 := by
    filter_upwards [hp, hn, ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hnull)]
      with q hqp hqn hq0
    exact (lt_or_gt_of_ne hq0).elim hqn hqp
  have hline : HasWeakLineDerivOn volume Ω u 0 (1, 0) := hline0.congr_ae_deriv hDu0
  -- Test against a tensor-product bump `q ↦ b q.2 * a q.1` supported in `ball (0, y₀) ε ⊆ Ω`.
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 Ω.isOpen (0, y₀) h0
  let Ω₁ : Opens ℝ := ⟨ball 0 ε, isOpen_ball⟩
  let Ω₂ : Opens Y := ⟨ball y₀ ε, isOpen_ball⟩
  have hV : (Ω₁ : Set ℝ) ×ˢ (Ω₂ : Set Y) ⊆ Ω := ball_prod_same (0 : ℝ) y₀ ε ▸ hball
  let a : ContDiffBump (0 : ℝ) := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  let b : ContDiffBump y₀ := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  let φ₁ : 𝓓(Ω₁, ℝ) :=
    ⟨a, a.contDiff, a.hasCompactSupport,
      a.tsupport_eq.trans_subset (closedBall_subset_ball (half_lt_self hε))⟩
  let φ₂ : 𝓓(Ω₂, ℝ) :=
    ⟨b, b.contDiff, b.hasCompactSupport,
      b.tsupport_eq.trans_subset (closedBall_subset_ball (half_lt_self hε))⟩
  let φ : 𝓓(Ω, ℝ) := TestFunction.prodSMulCLM φ₂ hV φ₁
  have hkey := hline.integral_lineDeriv_smul_eq_neg_integral_smul φ
  simp only [Pi.zero_apply, smul_zero, integral_zero, neg_zero] at hkey
  -- Evaluate the pairing by Fubini and `HasCompactSupport.integral_Ioi_deriv_eq`.
  have hint : ∫ q : ℝ × Y, lineDeriv ℝ (φ : ℝ × Y → ℝ) q (1, 0) • u q =
      (∫ x : ℝ, (Ioi (0 : ℝ)).indicator (deriv a) x) * ∫ y : Y, b y := by
    rw [Measure.volume_eq_prod, ← integral_prod_mul]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    have hld : lineDeriv ℝ (φ : ℝ × Y → ℝ) q (1, 0) = b q.2 * deriv a q.1 := by
      rw [← TestFunction.lineDerivOp_apply, TestFunction.lineDerivOp_prodSMulCLM]
      simp [φ₁, φ₂]
    dsimp only
    rw [hld, smul_eq_mul, hu]
    by_cases hq : 0 < q.1 <;> simp [Set.indicator, hq, mul_comm]
  rw [hint, integral_indicator measurableSet_Ioi,
    a.hasCompactSupport.integral_Ioi_deriv_eq (a.contDiff (n := 1)) 0,
    a.one_of_mem_closedBall (mem_closedBall_self a.rIn_pos.le)] at hkey
  linarith [b.integral_pos (μ := (volume : Measure Y))]

/-- **Jump discontinuities across hyperplanes have no weak derivative.** For any nonzero continuous
linear functional `ℓ` on a finite-dimensional real normed space `E` carrying a Borel additive Haar
measure `μ`, the indicator of `{x | 0 < ℓ x}` admits no weak Fréchet derivative on any open set `Ω`
containing a point `x₀` with `ℓ x₀ = 0`. -/
theorem not_hasWeakFDerivOn_indicator_pos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure]
    {ℓ : StrongDual ℝ E} (hℓ : ℓ ≠ 0) {Ω : Opens E} {x₀ : E} (hx₀ : x₀ ∈ Ω) (hx₀0 : ℓ x₀ = 0)
    (Du : E → E →L[ℝ] ℝ) :
    ¬ HasWeakFDerivOn μ Ω ({x : E | 0 < ℓ x}.indicator fun _ => (1 : ℝ)) Du := by
  intro hDu
  have hex : ∃ v : E, ℓ v ≠ 0 := by
    by_contra! hall
    exact hℓ (ContinuousLinearMap.ext hall)
  obtain ⟨v₀, hv₀⟩ := hex
  let w : E := (ℓ v₀)⁻¹ • v₀
  have hℓw : ℓ w = 1 := by simp [w, inv_mul_cancel₀ hv₀]
  let K := LinearMap.ker (ℓ : E →ₗ[ℝ] ℝ)
  let d := Module.finrank ℝ K
  let eK : K ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
    (Module.finBasis ℝ K).equivFun.trans (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).symm
  let splitL : (ℝ × EuclideanSpace ℝ (Fin d)) ≃ₗ[ℝ] E :=
    { toFun := fun q => q.1 • w + (eK.symm q.2 : E)
      invFun := fun x => (ℓ x, eK ⟨x - ℓ x • w, by simp [K, hℓw]⟩)
      map_add' := fun p q => by
        simp only [Prod.fst_add, Prod.snd_add, add_smul, map_add, Submodule.coe_add]
        abel
      map_smul' := fun r q => by
        simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_smul, map_smul,
          Submodule.coe_smul_of_tower, RingHom.id_apply, smul_add]
      left_inv := fun ⟨t, y⟩ => by
        have hy0 : ℓ (eK.symm y : E) = 0 := (eK.symm y).2
        ext1
        · simp [hℓw, hy0]
        · refine (eK.apply_symm_apply y).symm ▸ congrArg eK (Subtype.ext ?_)
          simp [hℓw, hy0]
      right_inv := fun x => by simp }
  let e : (ℝ × EuclideanSpace ℝ (Fin d)) ≃L[ℝ] E := splitL.toContinuousLinearEquiv
  have : (volume : Measure (ℝ × EuclideanSpace ℝ (Fin d))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure volume volume
  have hℓe : ∀ q, ℓ (e q) = q.1 := fun q => by
    have hy0 : ℓ (eK.symm q.2 : E) = 0 := (eK.symm q.2).2
    simp [e, splitL, hℓw, hy0]
  let y₀ : EuclideanSpace ℝ (Fin d) := eK ⟨x₀, hx₀0⟩
  have he0 : e (0, y₀) = x₀ := by simp [e, splitL, y₀]
  let Ω' : Opens (ℝ × EuclideanSpace ℝ (Fin d)) :=
    Ω.comap (e.toHomeomorph : C(ℝ × EuclideanSpace ℝ (Fin d), E))
  have h0Ω' : ((0 : ℝ), y₀) ∈ Ω' := by simpa [Ω', he0] using hx₀
  have hpull := hDu.comp_continuousLinearEquiv_of_isAddHaarMeasure (μ := volume) (U := Ω') e
    (mapsTo_preimage e (Ω : Set E))
  have hcomp : (({x : E | 0 < ℓ x}.indicator fun _ => (1 : ℝ)) ∘ e) =
      ({q : ℝ × EuclideanSpace ℝ (Fin d) | 0 < q.1}.indicator fun _ => (1 : ℝ)) := by
    funext q
    simp [Set.indicator, hℓe q]
  rw [hcomp] at hpull
  exact not_hasWeakFDerivOn_indicator_fst_pos h0Ω' _ hpull

end TauCeti
