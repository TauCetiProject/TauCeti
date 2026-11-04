/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.Calculus.LineDeriv.Basic
import TauCeti.Analysis.Calculus.Rademacher
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Sobolev.Mollification.Lipschitz

/-!
# The product rule for weak derivatives

A weak derivative is additive and commutes with scalars
(`TauCeti.HasWeakLineDerivOn.add`, `TauCeti.HasWeakLineDerivOn.const_smul`), but Lane A of the PDE
roadmap needs one more algebraic rule before it can localize: multiplication by a *variable*
smooth factor.  This file proves it.  For a smooth `ψ : E → ℝ` and a weakly differentiable `u`,

`∂_v (ψ u) = ψ ∂_v u + (∂_v ψ) u`

on `Ω`, in the weak sense of `TauCeti.HasWeakLineDerivOn`.

The proof is the one-line distributional computation.  Testing `ψ u` against `∂_v φ` is the same
as testing `u` against `ψ ∂_v φ = ∂_v (ψ φ) − (∂_v ψ) φ`, and `ψ φ` is again a test function on
`Ω`, because multiplying by a smooth function neither enlarges a support nor destroys smoothness.
So the defining identity for `u` applies to it, and the leftover term `(∂_v ψ) φ` is the second
summand of the Leibniz formula.  No smoothness of `u` is used, and no boundary hypothesis on `Ω`:
`ψ φ` is compactly supported *inside* `Ω`, so no boundary term appears.

Smoothness of `ψ` is what makes `ψ φ` a member of Mathlib's `TestFunction` type, whose smoothness
order is `∞`, and it is what cutoffs built from `ContDiffBump` supply. Only smoothness on `Ω` is
used (`TauCeti.HasWeakLineDerivOn.contDiffOn_smul`), since `ψ φ` only sees `ψ` on `tsupport φ`; a
coefficient field of an elliptic operator, smooth in the domain but not beyond it, is a factor of
this kind.

## Lipschitz factors

The rule also holds for a factor `ψ` that is only Lipschitz on `Ω`, with `∂_v ψ` its directional
derivative, which exists almost everywhere by Rademacher's theorem
(`TauCeti.HasWeakLineDerivOn.lipschitzOnWith_smul`). This is the form needed for coefficient
fields that are merely Lipschitz, such as those produced by flattening a `C²` boundary. The proof
mollifies a Lipschitz extension of `ψ` by normalized bumps `ρₙ` of radius `1 / (n + 1)` and
applies the smooth rule to `ψₙ = ρₙ ⋆ ψ`. The factors `ψₙ` converge to `ψ` uniformly, while
`∂_v ψₙ = ρₙ ⋆ ∂_v ψ` stays bounded by the Lipschitz constant and converges to `∂_v ψ` almost
everywhere by the Lebesgue differentiation theorem. Dominated convergence then passes the
identity tested against a fixed `φ` to the limit
(`LipschitzWith.tendsto_integral_normed_convolution_smul` and
`LipschitzWith.tendsto_integral_fderiv_normed_convolution_apply_smul`). For a factor that is also
bounded, an `Lᵖ` weak derivative of `u` gives one of `ψ u`
(`TauCeti.HasWeakLineDerivOn.exists_lp_lipschitzOnWith_smul`).

## Why this is the localization tool

`ψ` will be a cutoff.  Multiplying by one is how a global statement about `W^{k,p}(Ω)` is reduced
to a local one: it is the first step of the Meyers–Serrin `H = W` density theorem and of the
extension operator (Lane A.2 and A.6 of `TauCetiRoadmap/PDE/README.md`), and it is what turns an
interior estimate into an estimate on a compactly contained subdomain (Lane E.20).  The second
summand `(∂_v ψ) u` is exactly the error such an argument has to absorb, so having it with an
explicit, non-asymptotic formula is the point.

## Main declarations

* `TauCeti.HasWeakLineDerivOn.contDiffOn_smul`: the Leibniz rule in a direction `v`, for a factor
  smooth on `Ω`.
* `TauCeti.HasWeakLineDerivOn.contDiff_smul`: its case of a factor smooth on all of `E`.
* `TauCeti.HasWeakFDerivOn.contDiffOn_smul`, `TauCeti.HasWeakFDerivOn.contDiff_smul`: its
  Fréchet form, with the rank-one correction `(fderiv ℝ ψ x).smulRight (u x)`.
* `TauCeti.HasWeakLineDerivOn.smul_contDiff` and `TauCeti.HasWeakFDerivOn.smul_contDiff`: the
  rule with the roles exchanged, for a weakly differentiable scalar `a` and a smooth
  vector-valued `g`: `D(a g) = a Dg + Da ⊗ g`.
* `TauCeti.HasWeakLineDerivOn.lipschitzWith_smul` and
  `TauCeti.HasWeakLineDerivOn.lipschitzOnWith_smul`: the rule in a direction `v` for a Lipschitz
  factor, with its almost-everywhere directional derivative.
* `TauCeti.HasWeakLineDerivOn.exists_lp_lipschitzOnWith_smul`: a bounded Lipschitz factor keeps
  an `Lᵖ` weak derivative in `Lᵖ`.
* `TauCeti.HasWeakFDerivOn.contDiffOn_smul_gradient`,
  `TauCeti.HasWeakFDerivOn.contDiff_smul_gradient`: the form consumed by `TauCeti.W1p`, where a
  weak derivative of a scalar function is recorded by its Riesz representative and the rule reads
  `∇(ψ u) = ψ ∇u + u ∇ψ`.

## References

* L. C. Evans, *Partial Differential Equations*, §5.2.3, Theorem 1(iv).
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised ed.,
  §4.2.2 (products of Sobolev functions with Lipschitz functions).
-/

public section

namespace TauCeti

open MeasureTheory TopologicalSpace
open scoped ContDiff Distributions

section General

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace E] [OpensMeasurableSpace E]
  [LocallyCompactSpace E] {Ω : Opens E} {v : E} {μ : Measure E} {u u' : E → F} {ψ : E → ℝ}

/-- **The Leibniz rule for weak directional derivatives, local form.** If `u'` is a weak derivative
of `u` in the direction `v` on `Ω` and `ψ` is smooth on `Ω`, then `ψ u` is weakly differentiable in
the direction `v` on `Ω`, with derivative `ψ u' + (∂_v ψ) u`.

Nothing is assumed about `ψ` off `Ω`, and nothing about `Ω` beyond openness: the test function
`ψ φ` used in the proof is still compactly supported inside `Ω`, so the boundary term of the
classical integration by parts is absent here just as it is in the definition. -/
theorem HasWeakLineDerivOn.contDiffOn_smul (h : HasWeakLineDerivOn μ Ω u u' v)
    (hψ : ContDiffOn ℝ ∞ ψ Ω) :
    HasWeakLineDerivOn μ Ω (fun x => ψ x • u x)
      (fun x => ψ x • u' x + fderiv ℝ ψ x v • u x) v := by
  have hΩ : IsLocallyClosed (Ω : Set E) := Ω.isOpen.isLocallyClosed
  have hdψ : ContDiffOn ℝ ∞ (fun x => fderiv ℝ ψ x v) Ω :=
    (hψ.fderiv_of_isOpen Ω.isOpen (by simp)).clm_apply contDiffOn_const
  have hu : LocallyIntegrableOn (fun x => ψ x • u x) Ω μ :=
    h.locallyIntegrableOn.continuousOn_smul hΩ hψ.continuousOn
  have hu' : LocallyIntegrableOn (fun x => ψ x • u' x + fderiv ℝ ψ x v • u x) Ω μ :=
    (h.locallyIntegrableOn_deriv.continuousOn_smul hΩ hψ.continuousOn).add
      (h.locallyIntegrableOn.continuousOn_smul hΩ hdψ.continuousOn)
  rw [hasWeakLineDerivOn_iff_testFunction]
  refine ⟨h.completeSpace, hu, hu', fun φ => ?_⟩
  -- `ψ φ` and `(∂_v ψ) φ` are test functions on `Ω`.
  obtain ⟨Φ, hΦ⟩ := TestFunction.exists_coe_eq_smul_of_contDiffOn hψ φ
  obtain ⟨Ψ, hΨ⟩ := TestFunction.exists_coe_eq_smul_of_contDiffOn hdψ φ
  have hint1 : Integrable (fun x => lineDeriv ℝ (Φ : E → ℝ) x v • u x) μ :=
    integrable_lineDeriv_smul_of_locallyIntegrableOn h.locallyIntegrableOn Φ v
  have hint2 : Integrable (fun x => (Ψ : E → ℝ) x • u x) μ :=
    integrable_smul_of_locallyIntegrableOn h.locallyIntegrableOn Ψ
  have hint3 : Integrable (fun x => (Φ : E → ℝ) x • u' x) μ :=
    integrable_smul_of_locallyIntegrableOn h.locallyIntegrableOn_deriv Φ
  -- The classical product rule for the smooth factors.
  have hlineΦ : ∀ x, lineDeriv ℝ (Φ : E → ℝ) x v
      = ψ x * lineDeriv ℝ (φ : E → ℝ) x v + (Ψ : E → ℝ) x := fun x => by
    rw [hΦ, hΨ, TestFunction.lineDeriv_fun_smul_of_differentiableOn
      (hψ.differentiableOn (by simp)) φ x v]
    simp only [smul_eq_mul]
  have hsplit : ∫ x, (φ : E → ℝ) x • (ψ x • u' x + fderiv ℝ ψ x v • u x) ∂μ
      = ∫ x, (Φ : E → ℝ) x • u' x ∂μ + ∫ x, (Ψ : E → ℝ) x • u x ∂μ := by
    rw [← integral_add hint3 hint2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hΦ, hΨ, smul_add, smul_smul, smul_eq_mul, mul_comm]
  calc ∫ x, lineDeriv ℝ (φ : E → ℝ) x v • (ψ x • u x) ∂μ
      = ∫ x, (lineDeriv ℝ (Φ : E → ℝ) x v • u x - (Ψ : E → ℝ) x • u x) ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [hlineΦ x, add_smul, add_sub_cancel_right, smul_smul, mul_comm]
    _ = ∫ x, lineDeriv ℝ (Φ : E → ℝ) x v • u x ∂μ - ∫ x, (Ψ : E → ℝ) x • u x ∂μ :=
        integral_sub hint1 hint2
    _ = -∫ x, (Φ : E → ℝ) x • u' x ∂μ - ∫ x, (Ψ : E → ℝ) x • u x ∂μ := by
        rw [h.integral_lineDeriv_smul_eq_neg_integral_smul Φ]
    _ = -∫ x, (φ : E → ℝ) x • (ψ x • u' x + fderiv ℝ ψ x v • u x) ∂μ := by
        rw [hsplit]; abel

/-- **The Leibniz rule for weak directional derivatives.** If `u'` is a weak derivative of `u` in
the direction `v` on `Ω` and `ψ` is smooth, then `ψ u` is weakly differentiable in the direction
`v` on `Ω`, with derivative `ψ u' + (∂_v ψ) u`. -/
theorem HasWeakLineDerivOn.contDiff_smul (h : HasWeakLineDerivOn μ Ω u u' v)
    (hψ : ContDiff ℝ ∞ ψ) :
    HasWeakLineDerivOn μ Ω (fun x => ψ x • u x)
      (fun x => ψ x • u' x + fderiv ℝ ψ x v • u x) v :=
  h.contDiffOn_smul hψ.contDiffOn

/-- **The Leibniz rule for weak Fréchet derivatives, local form**: `D(ψ u) = ψ Du + u ⊗ Dψ` on
`Ω` for `ψ` smooth on `Ω`, the correction being the rank-one map `v ↦ (Dψ v) u`. -/
theorem HasWeakFDerivOn.contDiffOn_smul {U : E → E →L[ℝ] F} (h : HasWeakFDerivOn μ Ω u U)
    (hψ : ContDiffOn ℝ ∞ ψ Ω) :
    HasWeakFDerivOn μ Ω (fun x => ψ x • u x)
      (fun x => ψ x • U x + (fderiv ℝ ψ x).smulRight (u x)) := by
  rw [hasWeakFDerivOn_iff]
  intro v
  have hv := (h.hasWeakLineDerivOn v).contDiffOn_smul hψ
  convert hv using 2 with x
  simp

/-- **The Leibniz rule for weak Fréchet derivatives**: `D(ψ u) = ψ Du + u ⊗ Dψ`, the correction
being the rank-one map `v ↦ (Dψ v) u`. -/
theorem HasWeakFDerivOn.contDiff_smul {U : E → E →L[ℝ] F} (h : HasWeakFDerivOn μ Ω u U)
    (hψ : ContDiff ℝ ∞ ψ) :
    HasWeakFDerivOn μ Ω (fun x => ψ x • u x)
      (fun x => ψ x • U x + (fderiv ℝ ψ x).smulRight (u x)) :=
  h.contDiffOn_smul hψ.contDiffOn

/-- **The Leibniz rule with a smooth vector-valued factor.** If `a'` is a weak derivative of a
scalar function `a` in the direction `v` on `Ω` and `g` is smooth with values in a
finite-dimensional space, then `a g` is weakly differentiable in the direction `v` on `Ω`, with
derivative `a ∂_v g + a' g`. -/
theorem HasWeakLineDerivOn.smul_contDiff [FiniteDimensional ℝ F] {a a' : E → ℝ} {g : E → F}
    (h : HasWeakLineDerivOn μ Ω a a' v) (hg : ContDiff ℝ ∞ g) :
    HasWeakLineDerivOn μ Ω (fun x => a x • g x) (fun x => a x • fderiv ℝ g x v + a' x • g x) v := by
  -- Expand `g` in a basis `(bᵢ)` of `F`: `a g = ∑ᵢ (gᵢ a) bᵢ` with smooth scalar coordinates `gᵢ`,
  -- to each of which the scalar Leibniz rule applies.
  set b := Module.finBasis ℝ F
  let c : Fin (Module.finrank ℝ F) → F →L[ℝ] ℝ := fun i => LinearMap.toContinuousLinearMap
    (b.coord i)
  have hc : ∀ i, ContDiff ℝ ∞ fun x => c i (g x) := fun i => (c i).contDiff.comp hg
  have hfd : ∀ i x, fderiv ℝ (fun y => c i (g y)) x v = c i (fderiv ℝ g x v) := fun i x => by
    rw [fderiv_fun_comp x (c i).differentiableAt ((hg.differentiable (by simp)) x),
      ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply]
  have hsum := HasWeakLineDerivOn.sum (F := F) Finset.univ fun i _ =>
    ((h.contDiff_smul (hc i)).clm_comp (ContinuousLinearMap.toSpanSingleton ℝ (b i)))
  have hrepr : ∀ y : F, ∑ i, c i y • b i = y := fun y => by
    simp [c, Module.Basis.coord_apply]
  refine (hsum.congr_ae (Filter.Eventually.of_forall fun x => ?_)).congr_ae_deriv
    (Filter.Eventually.of_forall fun x => ?_)
  · simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm, mul_smul,
      ← Finset.smul_sum, hrepr]
  · simp only [ContinuousLinearMap.toSpanSingleton_apply, hfd, add_smul, Finset.sum_add_distrib,
      smul_eq_mul, mul_comm (c _ _), mul_smul, ← Finset.smul_sum, hrepr, add_comm]

/-- **The Leibniz rule with a smooth vector-valued factor, Fréchet form**:
`D(a g) = a Dg + Da ⊗ g`, the correction being the rank-one map `v ↦ (Da v) g`. -/
theorem HasWeakFDerivOn.smul_contDiff [FiniteDimensional ℝ F] {a : E → ℝ} {A : E → E →L[ℝ] ℝ}
    {g : E → F} (h : HasWeakFDerivOn μ Ω a A) (hg : ContDiff ℝ ∞ g) :
    HasWeakFDerivOn μ Ω (fun x => a x • g x)
      (fun x => a x • fderiv ℝ g x + (A x).smulRight (g x)) := by
  rw [hasWeakFDerivOn_iff] at h ⊢
  intro v
  convert (h v).smul_contDiff hg using 2 with x
  simp

end General

section Lipschitz

open Filter Topology Metric ContinuousLinearMap
open scoped ENNReal NNReal Convolution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens E} {v : E} {μ : Measure E} [μ.IsAddHaarMeasure] {u u' : E → F} {ψ : E → ℝ}
  {K : ℝ≥0}

/-- **The Leibniz rule for weak directional derivatives with a Lipschitz factor.** If `u'` is a
weak derivative of `u` in the direction `v` on `Ω` and `ψ` is Lipschitz, then `ψ u` is weakly
differentiable in the direction `v` on `Ω`, with derivative `ψ u' + (∂_v ψ) u`, where
`∂_v ψ = lineDeriv ℝ ψ · v` exists almost everywhere by Rademacher's theorem. -/
theorem HasWeakLineDerivOn.lipschitzWith_smul (h : HasWeakLineDerivOn μ Ω u u' v)
    (hψ : LipschitzWith K ψ) :
    HasWeakLineDerivOn μ Ω (fun x => ψ x • u x)
      (fun x => ψ x • u' x + lineDeriv ℝ ψ x v • u x) v := by
  have hΩ : IsLocallyClosed (Ω : Set E) := Ω.isOpen.isLocallyClosed
  set ψ' : E → ℝ := fun x => lineDeriv ℝ ψ x v with hψ'_def
  have hψ'm : Measurable ψ' := measurable_lineDeriv hψ.continuous
  have hψ'b : ∀ x, ‖ψ' x‖ ≤ K * ‖v‖ := fun x => norm_lineDeriv_le_of_lipschitz ℝ hψ
  have hu1 : LocallyIntegrableOn (fun x => ψ x • u x) Ω μ :=
    h.locallyIntegrableOn.continuousOn_smul hΩ hψ.continuous.continuousOn
  have hu2 : LocallyIntegrableOn (fun x => ψ' x • u x) Ω μ := by
    rw [locallyIntegrableOn_iff hΩ]
    intro k hk hkc
    exact (h.locallyIntegrableOn.integrableOn_compact_subset hk hkc).bdd_smul (K * ‖v‖)
      hψ'm.aestronglyMeasurable (Eventually.of_forall hψ'b)
  -- Mollify `ψ` by normalized bumps of radius `1 / (n + 1)`.
  set ρ : ℕ → ContDiffBump (0 : E) := ContDiffBump.shrinking one_pos
  set ψn : ℕ → E → ℝ := fun n => (ρ n).normed μ ⋆[lsmul ℝ ℝ, μ] ψ
  have hρ : Tendsto (fun n => (ρ n).rOut) atTop (𝓝 0) :=
    ContDiffBump.tendsto_rOut_shrinking one_pos
  have h'ρ : ∀ᶠ n in atTop, (ρ n).rOut ≤ 2 * (ρ n).rIn :=
    Eventually.of_forall fun n => (ContDiffBump.rOut_shrinking_eq_two_mul_rIn one_pos n).le
  have hsmooth : ∀ n, ContDiff ℝ ∞ (ψn n) := fun n =>
    (ρ n).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
      (ρ n).contDiff_normed hψ.continuous.locallyIntegrable
  rw [hasWeakLineDerivOn_iff_testFunction]
  refine ⟨h.completeSpace, hu1,
    (h.locallyIntegrableOn_deriv.continuousOn_smul hΩ hψ.continuous.continuousOn).add hu2,
    fun φ => ?_⟩
  -- The three integrands of the Leibniz identity, before multiplication by the factor.
  set w₁ : E → F := fun x => lineDeriv ℝ (φ : E → ℝ) x v • u x
  set w₂ : E → F := fun x => (φ : E → ℝ) x • u' x
  set w₃ : E → F := fun x => (φ : E → ℝ) x • u x
  have hw₁ : Integrable w₁ μ := integrable_lineDeriv_smul_of_locallyIntegrableOn
    h.locallyIntegrableOn φ v
  have hw₂ : Integrable w₂ μ := integrable_smul_of_locallyIntegrableOn h.locallyIntegrableOn_deriv φ
  have hw₃ : Integrable w₃ μ := integrable_smul_of_locallyIntegrableOn h.locallyIntegrableOn φ
  have hK : IsCompact (tsupport (φ : E → ℝ)) := φ.hasCompactSupport.isCompact
  -- `w₁` and `w₂` vanish off the support of `φ`, so they stay integrable against continuous
  -- factors.
  have hwc : ∀ w : E → F, Integrable w μ → (∀ x ∉ tsupport (φ : E → ℝ), w x = 0) →
      ∀ f : E → ℝ, Continuous f → Integrable (fun x => f x • w x) μ := fun w hw hw0 f hf =>
    (hw.integrableOn.continuousOn_smul hf.continuousOn hK).integrable_of_forall_notMem_eq_zero
      fun x hx => by simp [hw0 x hx]
  have hw₁c := hwc w₁ hw₁ fun x hx => by simp [w₁, lineDeriv_of_notMem_tsupport hx]
  have hw₂c := hwc w₂ hw₂ fun x hx => by simp [w₂, image_eq_zero_of_notMem_tsupport hx]
  -- The Leibniz identity for each smooth factor `ψn n`.
  have heq : ∀ n, ∫ x, ψn n x • w₁ x ∂μ =
      -(∫ x, ψn n x • w₂ x ∂μ + ∫ x, fderiv ℝ (ψn n) x v • w₃ x ∂μ) := fun n => by
    have hn := (h.contDiff_smul (hsmooth n)).integral_lineDeriv_smul_eq_neg_integral_smul φ
    have h₃ : Integrable (fun x => fderiv ℝ (ψn n) x v • w₃ x) μ :=
      hw₃.bdd_smul (K * ‖v‖) (((hsmooth n).continuous_fderiv (by simp)).clm_apply
        continuous_const).aestronglyMeasurable
        (Eventually.of_forall fun x => hψ.norm_fderiv_normed_convolution_apply_le (ρ n) x v)
    rw [← integral_add (hw₂c _ (hsmooth n).continuous) h₃]
    convert hn using 2
    · ext x; simp only [w₁, smul_comm (ψn n x)]
    · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [w₂, w₃, smul_add, smul_comm ((φ : E → ℝ) x)]
  -- Pass to the limit on both sides by dominated convergence.
  have hlimit := tendsto_nhds_unique
    (hψ.tendsto_integral_normed_convolution_smul hρ hw₁ (hw₁c ψ hψ.continuous))
    (((hψ.tendsto_integral_normed_convolution_smul hρ hw₂ (hw₂c ψ hψ.continuous)).add
      (hψ.tendsto_integral_fderiv_normed_convolution_apply_smul hρ h'ρ v hw₃)).neg.congr
        fun n => (heq n).symm)
  have h₃ : Integrable (fun x => ψ' x • w₃ x) μ :=
    hw₃.bdd_smul (K * ‖v‖) hψ'm.aestronglyMeasurable (Eventually.of_forall hψ'b)
  rw [← integral_add (hw₂c ψ hψ.continuous) h₃] at hlimit
  convert hlimit using 2
  · ext x; simp only [w₁, smul_comm (ψ x)]
  · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [w₂, w₃, ψ', smul_add, smul_comm ((φ : E → ℝ) x)]

/-- **The Leibniz rule for weak directional derivatives with a factor Lipschitz on the domain.**
If `u'` is a weak derivative of `u` in the direction `v` on `Ω` and `ψ` is Lipschitz on `Ω`, then
`ψ u` is weakly differentiable in the direction `v` on `Ω`, with derivative `ψ u' + (∂_v ψ) u`.
Nothing is assumed about `ψ` off `Ω`. -/
theorem HasWeakLineDerivOn.lipschitzOnWith_smul (h : HasWeakLineDerivOn μ Ω u u' v)
    (hψ : LipschitzOnWith K ψ Ω) :
    HasWeakLineDerivOn μ Ω (fun x => ψ x • u x)
      (fun x => ψ x • u' x + lineDeriv ℝ ψ x v • u x) v := by
  -- Replace `ψ` by a Lipschitz extension, which agrees with it near every point of `Ω`.
  obtain ⟨g, hg, hgψ⟩ := hψ.extend_real
  have hnear : ∀ x ∈ (Ω : Set E), g =ᶠ[𝓝 x] ψ := fun x hx =>
    Filter.eventually_of_mem (Ω.isOpen.mem_nhds hx) fun y hy => (hgψ hy).symm
  refine ((h.lipschitzWith_smul hg).congr_ae ?_).congr_ae_deriv ?_
  · exact (ae_restrict_mem Ω.isOpen.measurableSet).mono fun x hx => by
      simp only [← hgψ hx]
  · exact (ae_restrict_mem Ω.isOpen.measurableSet).mono fun x hx => by
      simp only [← hgψ hx, (hnear x hx).lineDeriv_eq]

/-- **A bounded Lipschitz factor keeps an `Lᵖ` weak derivative.** If `u ∈ Lᵖ(Ω)` has a weak
derivative `u' ∈ Lᵖ(Ω)` in the direction `v` and `ψ` is bounded and Lipschitz on `Ω`, then `ψ u`
has a weak derivative in the direction `v` that lies in `Lᵖ(Ω)`, namely `ψ u' + (∂_v ψ) u` from
`TauCeti.HasWeakLineDerivOn.lipschitzOnWith_smul`. -/
theorem HasWeakLineDerivOn.exists_lp_lipschitzOnWith_smul {p : ℝ≥0∞} {M : ℝ}
    (h : HasWeakLineDerivOn μ Ω u u' v) (hψ : LipschitzOnWith K ψ Ω)
    (hψb : ∀ x ∈ (Ω : Set E), ‖ψ x‖ ≤ M) (hu : MemLp u p (μ.restrict Ω))
    (hu' : MemLp u' p (μ.restrict Ω)) :
    ∃ G : Lp F p (μ.restrict Ω), HasWeakLineDerivOn μ Ω (fun x => ψ x • u x) G v := by
  have hΩm : MeasurableSet (Ω : Set E) := Ω.isOpen.measurableSet
  have hm := ((memLp_top_of_bound (hψ.continuousOn.aestronglyMeasurable hΩm) M
    ((ae_restrict_mem hΩm).mono hψb)).smul (r := p) hu').add
    ((hψ.memLp_lineDeriv Ω.isOpen v).smul (r := p) hu)
  exact ⟨hm.toLp _, (h.lipschitzOnWith_smul hψ).congr_ae_deriv hm.coeFn_toLp.symm⟩

end Lipschitz

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [FiniteDimensional ℝ E] {Ω : Opens E} {μ : Measure E}
  {a ψ : E → ℝ} {g : E → E}

open scoped Gradient

/-- **The Leibniz rule in gradient form, local form**: `∇(ψ a) = ψ ∇a + a ∇ψ` on `Ω` for `ψ`
smooth on `Ω`. -/
theorem HasWeakFDerivOn.contDiffOn_smul_gradient
    (h : HasWeakFDerivOn μ Ω a fun x => innerSL ℝ (g x)) (hψ : ContDiffOn ℝ ∞ ψ Ω) :
    HasWeakFDerivOn μ Ω (fun x => ψ x • a x)
      (fun x => innerSL ℝ (ψ x • g x + a x • ∇ ψ x)) := by
  have hv := h.contDiffOn_smul hψ
  convert hv using 2 with x
  ext w
  simp [inner_gradient_left (𝕜 := ℝ) (f := ψ) (x := x), mul_comm]

/-- **The Leibniz rule in gradient form**: `∇(ψ a) = ψ ∇a + a ∇ψ`.

This is the shape `TauCeti.W1p` stores a weak derivative in — a scalar function together with the
Riesz representative of its weak Fréchet derivative — so it is the form a multiplication operator
on the Sobolev space consumes. -/
theorem HasWeakFDerivOn.contDiff_smul_gradient
    (h : HasWeakFDerivOn μ Ω a fun x => innerSL ℝ (g x)) (hψ : ContDiff ℝ ∞ ψ) :
    HasWeakFDerivOn μ Ω (fun x => ψ x • a x)
      (fun x => innerSL ℝ (ψ x • g x + a x • ∇ ψ x)) :=
  h.contDiffOn_smul_gradient hψ.contDiffOn

end InnerProduct

end TauCeti
