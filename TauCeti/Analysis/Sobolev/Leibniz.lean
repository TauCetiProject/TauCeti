/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.Calculus.LineDeriv.Basic
import TauCeti.Analysis.Calculus.LineDeriv.Measurable
import TauCeti.Analysis.Calculus.Rademacher
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Sobolev.Mollification.Lipschitz
import TauCeti.Analysis.Sobolev.WeakDeriv.Local
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# The product rule for weak derivatives

A weak derivative is additive and commutes with scalars
(`TauCeti.HasWeakLineDerivOn.add`, `TauCeti.HasWeakLineDerivOn.const_smul`), but localization
needs one more algebraic rule: multiplication by a *variable* smooth factor.  This file proves it.
For a smooth `ψ : E → ℝ` and a weakly differentiable `u`,

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
this kind. For an additive Haar measure, a factor that is only `C¹` on `Ω` also suffices
(`TauCeti.HasWeakLineDerivOn.contDiffOn_smul_of_ne_zero`), as a consequence of the Lipschitz rule
below. Expanding in a basis gives the rule `D(T u) = T Du + (DT) u` for a `C¹` field `T` of linear
maps between finite-dimensional spaces (`TauCeti.HasWeakFDerivOn.contDiffOn_clm_apply_of_ne_zero`).

## Lipschitz factors

The rule also holds for a factor `ψ` that is only Lipschitz on `Ω`, with `∂_v ψ` its directional
derivative, which exists almost everywhere by Rademacher's theorem
(`TauCeti.HasWeakLineDerivOn.lipschitzOnWith_smul`). This is the form needed for coefficient
fields that are merely Lipschitz, such as those produced by flattening a `C²` boundary. The proof
mollifies a Lipschitz extension of `ψ` by normalized bumps `ρₙ` of radius `1 / (n + 1)` and
applies the smooth rule to `ψₙ = ρₙ ⋆ ψ`. The factors `ψₙ` converge to `ψ` uniformly, while
`∂_v ψₙ = ρₙ ⋆ ∂_v ψ` stays bounded by the Lipschitz constant and converges to `∂_v ψ` almost
everywhere by the Lebesgue differentiation theorem. The identity tested against a fixed `φ` then
passes to the limit: uniform convergence handles the `ψₙ` terms
(`ContDiffBump.tendsto_integral_normed_convolution_smul`) and dominated convergence the
`∂_v ψₙ` term (`LipschitzWith.tendsto_integral_fderiv_normed_convolution_apply_smul`). For a
factor that is also bounded, an `Lᵖ` weak derivative of `u` gives one of `ψ u`, with the `Lᵖ`
bound `‖∂_v (ψ u)‖ ≤ M ‖∂_v u‖ + K ‖v‖ ‖u‖` for `|ψ| ≤ M`
(`TauCeti.HasWeakLineDerivOn.exists_norm_le_lipschitzOnWith_smul`).

## Why this is the localization tool

Typically `ψ` is a cutoff.  Multiplying by one is how a global statement about `W^{k,p}(Ω)` is
reduced to a local one: it is the first step of the Meyers–Serrin `H = W` density theorem and of
the extension operator, and it is what turns an interior estimate into an estimate on a compactly
contained subdomain.  The second
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
* `TauCeti.HasWeakLineDerivOn.contDiffOn_bilin`, `TauCeti.HasWeakLineDerivOn.contDiff_bilin`,
  `TauCeti.HasWeakLineDerivOn.integral_lineDeriv_smul_bilin_of_contDiff`,
  `TauCeti.HasWeakFDerivOn.contDiffOn_bilin`, and `TauCeti.HasWeakFDerivOn.contDiff_bilin`: the
  bilinear rule for a smooth finite-dimensional factor `f` and a weakly differentiable `g`:
  `D(B(f, g)) = B(Df, g) + B(f, Dg)`, together with its scalar-test integration-by-parts form.
* `TauCeti.HasWeakLineDerivOn.lipschitzWith_smul` and
  `TauCeti.HasWeakLineDerivOn.lipschitzOnWith_smul`: the rule in a direction `v` for a Lipschitz
  factor, with its almost-everywhere directional derivative.
* `TauCeti.HasWeakLineDerivOn.locallyLipschitzOn_smul`: the same for a factor that is only
  locally Lipschitz on `Ω`, such as the continuous representative of a `W^{1,∞}` function.
* `TauCeti.HasWeakLineDerivOn.contDiffOn_smul_of_ne_zero`,
  `TauCeti.HasWeakFDerivOn.contDiffOn_smul_of_ne_zero`: the rule in both forms for a factor that
  is `C^n` on `Ω` with `n ≠ 0` (at least `C¹`), for an additive Haar measure.
* `TauCeti.HasWeakLineDerivOn.contDiffOn_clm_apply_of_ne_zero`,
  `TauCeti.HasWeakFDerivOn.contDiffOn_clm_apply_of_ne_zero`: the same rule in both forms for a
  `C¹` factor with values in linear maps between finite-dimensional spaces,
  `∂_v (Φ u) = Φ ∂_v u + (∂_v Φ) u`.
* `TauCeti.HasWeakLineDerivOn.exists_norm_le_lipschitzOnWith_smul`: a bounded Lipschitz factor
  keeps an `Lᵖ` weak derivative in `Lᵖ`, with an explicit bound.
* `TauCeti.eLpNorm_smul_add_fderiv_smulRight_le`: for `1 ≤ p`, the `Lᵖ` bound
  `‖ψ Du + Dψ ⊗ u‖_{Lᵖ} ≤ A ‖Du‖_{Lᵖ} + B ‖u‖_{Lᵖ}` when `|ψ| ≤ A` and `‖Dψ‖ ≤ B` almost
  everywhere.
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
  {Ω : Opens E} {v : E} {μ : Measure E} {u u' : E → F} {ψ : E → ℝ}

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
  have hdψ : ContDiffOn ℝ ∞ (fun x => fderiv ℝ ψ x v) Ω :=
    (hψ.fderiv_of_isOpen Ω.isOpen (by simp)).clm_apply contDiffOn_const
  have hu : LocallyIntegrableOn (fun x => ψ x • u x) Ω μ :=
    h.locallyIntegrableOn.continuousOn_smul_of_isOpen Ω.isOpen hψ.continuousOn
  have hu' : LocallyIntegrableOn (fun x => ψ x • u' x + fderiv ℝ ψ x v • u x) Ω μ :=
    (h.locallyIntegrableOn_deriv.continuousOn_smul_of_isOpen Ω.isOpen hψ.continuousOn).add
      (h.locallyIntegrableOn.continuousOn_smul_of_isOpen Ω.isOpen hdψ.continuousOn)
  rw [hasWeakLineDerivOn_iff_testFunction]
  refine ⟨h.completeSpace, hu, hu', fun φ => ?_⟩
  -- `ψ φ` and `(∂_v ψ) φ` are test functions on `Ω`.
  obtain ⟨Φ, hΦ⟩ := TestFunction.exists_coe_eq_smul_of_contDiffOn hψ φ
  obtain ⟨Ψ, hΨ⟩ := TestFunction.exists_coe_eq_smul_of_contDiffOn hdψ φ
  have hint1 : Integrable (fun x => lineDeriv ℝ (Φ : E → ℝ) x v • u x) μ :=
    integrable_lineDeriv_smul_of_locallyIntegrableOn h.locallyIntegrableOn Φ v
  have hint2 : Integrable (fun x => (Ψ : E → ℝ) x • u x) μ :=
    Ψ.integrable_smul h.locallyIntegrableOn
  have hint3 : Integrable (fun x => (Φ : E → ℝ) x • u' x) μ :=
    Φ.integrable_smul h.locallyIntegrableOn_deriv
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

/-- **The bilinear Leibniz rule with a smooth factor, local form.** If `g'` is a weak derivative
of `g` in the direction `v` on `Ω`, `f` is smooth on `Ω` with values in a finite-dimensional
space `F`, and `B : F →L[ℝ] G →L[ℝ] H` is continuous bilinear into a complete space `H`, then
`B(f, g)` is weakly differentiable in the direction `v` on `Ω` with derivative
`B(f, g') + B(∂_v f, g)`. -/
theorem HasWeakLineDerivOn.contDiffOn_bilin {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H] [FiniteDimensional ℝ F]
    (B : F →L[ℝ] G →L[ℝ] H) {f : E → F} {g g' : E → G}
    (hg : HasWeakLineDerivOn μ Ω g g' v) (hf : ContDiffOn ℝ ∞ f Ω) :
    HasWeakLineDerivOn μ Ω (fun x => B (f x) (g x))
      (fun x => B (f x) (g' x) + B (fderiv ℝ f x v) (g x)) v := by
  let b := Module.finBasis ℝ F
  let ℓ : Fin (Module.finrank ℝ F) → F →L[ℝ] ℝ := fun i => (b.coord i).toContinuousLinearMap
  have hBrep (x : F) (y : G) : ∑ i, ℓ i x • B (b i) y = B x y := by
    have hx : ∑ i, ℓ i x • b i = x := by simp [ℓ]
    conv_rhs => rw [← hx, map_sum, sum_apply]
    simp [map_smul]
  have hc (i : Fin (Module.finrank ℝ F)) : ContDiffOn ℝ ∞ (fun w => ℓ i (f w)) Ω :=
    (ℓ i).contDiff.comp_contDiffOn hf
  have hsum := HasWeakLineDerivOn.sum (F := H) Finset.univ fun i _ =>
    (hg.clm_comp (B (b i))).contDiffOn_smul (hc i)
  refine (hsum.congr_ae (Filter.Eventually.of_forall fun x => ?_)).congr_ae_deriv
    (ae_restrict_of_forall_mem Ω.isOpen.measurableSet fun x hx => ?_)
  · simp only [hBrep]
  · have hfd (i : Fin (Module.finrank ℝ F)) :
        fderiv ℝ (fun w => ℓ i (f w)) x v = ℓ i (fderiv ℝ f x v) := by
      rw [fderiv_fun_comp x (ℓ i).differentiableAt
        ((hf.differentiableOn (by simp) x hx).differentiableAt (Ω.isOpen.mem_nhds hx)),
        ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply]
    simp only [Finset.sum_add_distrib, hfd, hBrep]

/-- **The bilinear Leibniz rule with a smooth factor.** If `g'` is a weak derivative of `g` in the
direction `v` on `Ω` and `f` is smooth with values in a finite-dimensional space `F`, then
`B(f, g)` has weak directional derivative `B(f, g') + B(∂_v f, g)` on `Ω`. -/
theorem HasWeakLineDerivOn.contDiff_bilin {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H] [FiniteDimensional ℝ F]
    (B : F →L[ℝ] G →L[ℝ] H) {f : E → F} {g g' : E → G}
    (hg : HasWeakLineDerivOn μ Ω g g' v) (hf : ContDiff ℝ ∞ f) :
    HasWeakLineDerivOn μ Ω (fun x => B (f x) (g x))
      (fun x => B (f x) (g' x) + B (fderiv ℝ f x v) (g x)) v :=
  hg.contDiffOn_bilin B hf.contDiffOn

section

open LineDeriv

/-- Smooth-factor weak Leibniz identity for a continuous bilinear map against a scalar test
function, derived from `TauCeti.HasWeakLineDerivOn.contDiff_bilin`. -/
theorem HasWeakLineDerivOn.integral_lineDeriv_smul_bilin_of_contDiff {G H : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    [CompleteSpace H] [FiniteDimensional ℝ F]
    (B : F →L[ℝ] G →L[ℝ] H) {f : E → F} {g g' : E → G}
    (hg : HasWeakLineDerivOn μ Ω g g' v) (hf : ContDiff ℝ ∞ f) (ψ : 𝓓(Ω, ℝ)) :
    (∫ x, (∂_{v} ψ : 𝓓(Ω, ℝ)) x • B (f x) (g x) ∂μ) +
        (∫ x, (ψ : E → ℝ) x • B (fderiv ℝ f x v) (g x) ∂μ) =
      -∫ x, (ψ : E → ℝ) x • B (f x) (g' x) ∂μ := by
  let b := Module.finBasis ℝ F
  let ℓ : Fin (Module.finrank ℝ F) → F →L[ℝ] ℝ := fun i => (b.coord i).toContinuousLinearMap
  have hB_loc {ϕ : E → F} (hϕ : Continuous ϕ) {G' : E → G}
      (hG' : ∀ i, LocallyIntegrableOn (fun x => B (b i) (G' x)) Ω μ) :
      LocallyIntegrableOn (fun x => B (ϕ x) (G' x)) Ω μ := by
    have hrep : (fun x => B (ϕ x) (G' x)) =
        fun x => ∑ i, ℓ i (ϕ x) • B (b i) (G' x) := by
      ext x
      have hx : ∑ i, ℓ i (ϕ x) • b i = ϕ x := by simp [ℓ]
      conv_lhs => rw [← hx, map_sum, sum_apply]
      simp [map_smul]
    rw [hrep]
    exact locallyIntegrableOn_finsetSum Finset.univ fun i _ =>
      (hG' i).continuousOn_smul_of_isOpen Ω.isOpen ((ℓ i).continuous.comp hϕ).continuousOn
  have hDfv_c : Continuous fun x => fderiv ℝ f x v :=
    (ContinuousLinearMap.apply ℝ F v).continuous.comp
      ((hf.of_le (WithTop.coe_le_coe.2 (le_top : (1 : ℕ∞) ≤ ⊤))).continuous_fderiv one_ne_zero)
  have h1 : Integrable (fun x => (ψ : E → ℝ) x • B (f x) (g' x)) μ :=
    ψ.integrable_smul <| hB_loc hf.continuous fun i =>
      (hg.clm_comp (B (b i))).locallyIntegrableOn_deriv
  have h2 : Integrable (fun x => (ψ : E → ℝ) x • B (fderiv ℝ f x v) (g x)) μ :=
    ψ.integrable_smul <| hB_loc hDfv_c fun i => (hg.clm_comp (B (b i))).locallyIntegrableOn
  have hibp := (hg.contDiff_bilin B hf).integral_lineDeriv_smul_eq_neg_integral_smul ψ
  have hsplit : ∫ x, (ψ : E → ℝ) x • (B (f x) (g' x) + B (fderiv ℝ f x v) (g x)) ∂μ =
      (∫ x, (ψ : E → ℝ) x • B (f x) (g' x) ∂μ) +
        ∫ x, (ψ : E → ℝ) x • B (fderiv ℝ f x v) (g x) ∂μ := by
    rw [← integral_add h1 h2]
    exact integral_congr_ae (.of_forall fun x => smul_add _ _ _)
  simp only [← TestFunction.lineDerivOp_apply] at hibp
  rw [hsplit] at hibp
  exact eq_neg_of_add_eq_zero_left (by rw [hibp]; abel)

end

/-- **The bilinear Leibniz rule with a smooth factor, local Fréchet form**:
`D(B(f, g)) = B(Df, g) + B(f, Dg)` on `Ω` for `f` smooth on `Ω` with finite-dimensional codomain
`F` and `g` weakly differentiable with derivative `Dg`. -/
theorem HasWeakFDerivOn.contDiffOn_bilin {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H] [FiniteDimensional ℝ F]
    (B : F →L[ℝ] G →L[ℝ] H) {f : E → F} {g : E → G} {Dg : E → E →L[ℝ] G}
    (hg : HasWeakFDerivOn μ Ω g Dg) (hf : ContDiffOn ℝ ∞ f Ω) :
    HasWeakFDerivOn μ Ω (fun x => B (f x) (g x))
      (fun x => B.precompL E (fderiv ℝ f x) (g x) + B.precompR E (f x) (Dg x)) := by
  rw [hasWeakFDerivOn_iff] at hg ⊢
  intro v
  convert (hg v).contDiffOn_bilin B hf using 2 with x
  simp [add_comm]

/-- **The bilinear Leibniz rule with a smooth factor, Fréchet form**:
`D(B(f, g)) = B(Df, g) + B(f, Dg)` on `Ω` for smooth `f` with finite-dimensional codomain `F` and
weakly differentiable `g`. -/
theorem HasWeakFDerivOn.contDiff_bilin {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H] [FiniteDimensional ℝ F]
    (B : F →L[ℝ] G →L[ℝ] H) {f : E → F} {g : E → G} {Dg : E → E →L[ℝ] G}
    (hg : HasWeakFDerivOn μ Ω g Dg) (hf : ContDiff ℝ ∞ f) :
    HasWeakFDerivOn μ Ω (fun x => B (f x) (g x))
      (fun x => B.precompL E (fderiv ℝ f x) (g x) + B.precompR E (f x) (Dg x)) :=
  hg.contDiffOn_bilin B hf.contDiffOn

end General

section Lipschitz

open Filter Topology Metric ContinuousLinearMap
open scoped ENNReal NNReal Convolution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens E} {v : E} {μ : Measure E} [μ.IsAddHaarMeasure] {u u' : E → F} {ψ : E → ℝ}
  {K : ℝ≥0}

/-- The Leibniz identity against a test function, for the mollification of the Lipschitz factor
by a bump `ρ`, which is smooth. -/
private theorem integral_lineDeriv_smul_normed_convolution_eq
    (h : HasWeakLineDerivOn μ Ω u u' v) (hψ : LipschitzWith K ψ) (ρ : ContDiffBump (0 : E))
    (φ : 𝓓(Ω, ℝ)) :
    ∫ x, (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] ψ) x • (lineDeriv ℝ (φ : E → ℝ) x v • u x) ∂μ =
      -(∫ x, (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] ψ) x • ((φ : E → ℝ) x • u' x) ∂μ +
        ∫ x, fderiv ℝ (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] ψ) x v • ((φ : E → ℝ) x • u x) ∂μ) := by
  have hsmooth : ContDiff ℝ ∞ (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] ψ) :=
    ρ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
      ρ.contDiff_normed hψ.continuous.locallyIntegrable
  have hw₃ : Integrable (fun x => (φ : E → ℝ) x • u x) μ :=
    φ.integrable_smul h.locallyIntegrableOn
  have hw₂c : Integrable (fun x => (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] ψ) x •
      ((φ : E → ℝ) x • u' x)) μ :=
    integrable_continuousOn_smul_of_forall_notMem_eq_zero φ.hasCompactSupport.isCompact
      (φ.integrable_smul h.locallyIntegrableOn_deriv)
      (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx]) hsmooth.continuous.continuousOn
  have h₃ : Integrable (fun x => fderiv ℝ (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] ψ) x v •
      ((φ : E → ℝ) x • u x)) μ :=
    hw₃.bdd_smul (K * ‖v‖) ((hsmooth.continuous_fderiv (by simp)).clm_apply
      continuous_const).aestronglyMeasurable
      (Eventually.of_forall fun x => hψ.norm_fderiv_normed_convolution_apply_le ρ x v)
  have hn := (h.contDiff_smul hsmooth).integral_lineDeriv_smul_eq_neg_integral_smul φ
  rw [← integral_add hw₂c h₃]
  convert hn using 2
  · ext x; simp only [smul_comm ((ρ.normed μ ⋆[lsmul ℝ ℝ, μ] ψ) x)]
  · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [smul_add, smul_comm ((φ : E → ℝ) x)]

/-- The Leibniz identity against a test function, by passing to the limit along mollifications of
the Lipschitz factor. -/
private theorem integral_lineDeriv_smul_lipschitzWith_smul_eq
    (h : HasWeakLineDerivOn μ Ω u u' v) (hψ : LipschitzWith K ψ) (φ : 𝓓(Ω, ℝ)) :
    ∫ x, lineDeriv ℝ (φ : E → ℝ) x v • ψ x • u x ∂μ =
      -∫ x, (φ : E → ℝ) x • (ψ x • u' x + lineDeriv ℝ ψ x v • u x) ∂μ := by
  -- Mollify `ψ` by normalized bumps of radius `1 / (n + 1)`.
  set ρ : ℕ → ContDiffBump (0 : E) := ContDiffBump.shrinking one_pos
  have hρ : Tendsto (fun n => (ρ n).rOut) atTop (𝓝 0) :=
    ContDiffBump.tendsto_rOut_shrinking one_pos
  have h'ρ : ∀ᶠ n in atTop, (ρ n).rOut ≤ 2 * (ρ n).rIn :=
    Eventually.of_forall fun n => (ContDiffBump.rOut_shrinking_eq_two_mul_rIn one_pos n).le
  -- The three integrands of the Leibniz identity, before multiplication by the factor.
  set w₁ : E → F := fun x => lineDeriv ℝ (φ : E → ℝ) x v • u x
  set w₂ : E → F := fun x => (φ : E → ℝ) x • u' x
  set w₃ : E → F := fun x => (φ : E → ℝ) x • u x
  have hw₁ : Integrable w₁ μ := integrable_lineDeriv_smul_of_locallyIntegrableOn
    h.locallyIntegrableOn φ v
  have hw₂ : Integrable w₂ μ := φ.integrable_smul h.locallyIntegrableOn_deriv
  have hw₃ : Integrable w₃ μ := φ.integrable_smul h.locallyIntegrableOn
  -- `w₁` and `w₂` vanish off the support of `φ`, so they stay integrable against continuous
  -- factors.
  have hw₁c : ∀ f : E → ℝ, Continuous f → Integrable (fun x => f x • w₁ x) μ := fun f hf =>
    integrable_continuousOn_smul_of_forall_notMem_eq_zero φ.hasCompactSupport.isCompact hw₁
      (fun x hx => by simp [w₁, lineDeriv_of_notMem_tsupport hx]) hf.continuousOn
  have hw₂c : ∀ f : E → ℝ, Continuous f → Integrable (fun x => f x • w₂ x) μ := fun f hf =>
    integrable_continuousOn_smul_of_forall_notMem_eq_zero φ.hasCompactSupport.isCompact hw₂
      (fun x hx => by simp [w₂, image_eq_zero_of_notMem_tsupport hx]) hf.continuousOn
  -- Pass to the limit on both sides: uniform convergence for `ψₙ`, dominated convergence for
  -- `∂_v ψₙ`.
  have hlimit := tendsto_nhds_unique
    (ContDiffBump.tendsto_integral_normed_convolution_smul hψ.uniformContinuous hρ hw₁
      (hw₁c ψ hψ.continuous))
    (((ContDiffBump.tendsto_integral_normed_convolution_smul hψ.uniformContinuous hρ hw₂
      (hw₂c ψ hψ.continuous)).add
      (hψ.tendsto_integral_fderiv_normed_convolution_apply_smul hρ h'ρ v hw₃)).neg.congr
        fun n => (integral_lineDeriv_smul_normed_convolution_eq h hψ (ρ n) φ).symm)
  rw [← integral_add (hw₂c ψ hψ.continuous) (hψ.integrable_lineDeriv_smul hw₃)]
    at hlimit
  convert hlimit using 2
  · ext x; simp only [w₁, smul_comm (ψ x)]
  · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [w₂, w₃, smul_add, smul_comm ((φ : E → ℝ) x)]

/-- **The Leibniz rule for weak directional derivatives with a Lipschitz factor.** If `u'` is a
weak derivative of `u` in the direction `v` on `Ω` and `ψ` is Lipschitz, then `ψ u` is weakly
differentiable in the direction `v` on `Ω`, with derivative `ψ u' + (∂_v ψ) u`, where
`∂_v ψ = lineDeriv ℝ ψ · v` exists almost everywhere by Rademacher's theorem. -/
theorem HasWeakLineDerivOn.lipschitzWith_smul (h : HasWeakLineDerivOn μ Ω u u' v)
    (hψ : LipschitzWith K ψ) :
    HasWeakLineDerivOn μ Ω (fun x => ψ x • u x)
      (fun x => ψ x • u' x + lineDeriv ℝ ψ x v • u x) v := by
  have hΩ : IsLocallyClosed (Ω : Set E) := Ω.isOpen.isLocallyClosed
  have hu1 : LocallyIntegrableOn (fun x => ψ x • u x) Ω μ :=
    h.locallyIntegrableOn.continuousOn_smul hΩ hψ.continuous.continuousOn
  have hu2 : LocallyIntegrableOn (fun x => lineDeriv ℝ ψ x v • u x) Ω μ := by
    rw [locallyIntegrableOn_iff hΩ]
    intro k hk hkc
    exact hψ.integrable_lineDeriv_smul
      (h.locallyIntegrableOn.integrableOn_compact_subset hk hkc)
  rw [hasWeakLineDerivOn_iff_testFunction]
  exact ⟨h.completeSpace, hu1,
    (h.locallyIntegrableOn_deriv.continuousOn_smul hΩ hψ.continuous.continuousOn).add hu2,
    integral_lineDeriv_smul_lipschitzWith_smul_eq h hψ⟩

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

/-- **The Leibniz rule for weak directional derivatives with a locally Lipschitz factor.** If `u'`
is a weak derivative of `u` in the direction `v` on `Ω` and `ψ` is locally Lipschitz on `Ω`, then
`ψ u` is weakly differentiable in the direction `v` on `Ω`, with derivative `ψ u' + (∂_v ψ) u`.
Neither `ψ` nor its directional derivative need be bounded on `Ω`. -/
theorem HasWeakLineDerivOn.locallyLipschitzOn_smul (h : HasWeakLineDerivOn μ Ω u u' v)
    (hψ : LocallyLipschitzOn (Ω : Set E) ψ) :
    HasWeakLineDerivOn μ Ω (fun x => ψ x • u x)
      (fun x => ψ x • u' x + lineDeriv ℝ ψ x v • u x) v := by
  -- On each relatively compact open `V` with closure in `Ω` the factor is Lipschitz, so the
  -- Lipschitz rule applies there.
  refine hasWeakLineDerivOn_iff_forall_isCompact_closure.2 fun V hVc hVΩ => ?_
  obtain ⟨K, hK⟩ := (hψ.mono hVΩ).exists_lipschitzOnWith_of_compact hVc
  exact (h.mono (subset_closure.trans hVΩ)).lipschitzOnWith_smul (hK.mono subset_closure)

/-- **The Leibniz rule for weak directional derivatives with a `C¹` factor.** If `u'` is a weak
derivative of `u` in the direction `v` on `Ω` and `ψ` is `C^n` on `Ω` for some `n ≠ 0`, then `ψ u`
is weakly differentiable in the direction `v` on `Ω`, with derivative `ψ u' + (∂_v ψ) u`.

This is `TauCeti.HasWeakLineDerivOn.contDiffOn_smul` at finite regularity, for an additive Haar
measure. -/
theorem HasWeakLineDerivOn.contDiffOn_smul_of_ne_zero {n : WithTop ℕ∞}
    (h : HasWeakLineDerivOn μ Ω u u' v) (hψ : ContDiffOn ℝ n ψ Ω) (hn : n ≠ 0) :
    HasWeakLineDerivOn μ Ω (fun x => ψ x • u x)
      (fun x => ψ x • u' x + fderiv ℝ ψ x v • u x) v := by
  -- The factor is locally Lipschitz on `Ω`, and its directional derivative is the classical one.
  have hψ1 : ContDiffOn ℝ 1 ψ Ω := hψ.of_le (ENat.one_le_iff_ne_zero_withTop.2 hn)
  have hll : LocallyLipschitzOn (Ω : Set E) ψ := fun x hx => by
    obtain ⟨K, t, ht, hK⟩ :=
      ((hψ1 x hx).contDiffAt (Ω.isOpen.mem_nhds hx)).exists_lipschitzOnWith
    exact ⟨K, t, nhdsWithin_le_nhds ht, hK⟩
  refine (h.locallyLipschitzOn_smul hll).congr_ae_deriv ?_
  filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hxΩ
  rw [((hψ1.differentiableOn one_ne_zero x hxΩ).differentiableAt
    (Ω.isOpen.mem_nhds hxΩ)).lineDeriv_eq_fderiv]

/-- **The Leibniz rule for weak Fréchet derivatives with a `C¹` factor**: `D(ψ u) = ψ Du + u ⊗ Dψ`
on `Ω` for `ψ` that is `C^n` on `Ω` with `n ≠ 0`, for an additive Haar measure. -/
theorem HasWeakFDerivOn.contDiffOn_smul_of_ne_zero {n : WithTop ℕ∞} {U : E → E →L[ℝ] F}
    (h : HasWeakFDerivOn μ Ω u U) (hψ : ContDiffOn ℝ n ψ Ω) (hn : n ≠ 0) :
    HasWeakFDerivOn μ Ω (fun x => ψ x • u x)
      (fun x => ψ x • U x + (fderiv ℝ ψ x).smulRight (u x)) := by
  rw [hasWeakFDerivOn_iff]
  intro v
  have hv := (h.hasWeakLineDerivOn v).contDiffOn_smul_of_ne_zero hψ hn
  convert hv using 2 with x
  simp

/-- **The Leibniz rule with a `C¹` operator-valued factor.** If `u'` is a weak derivative of `u`
in the direction `v` on `Ω` and `Φ : E → (F →L[ℝ] G)` is `C^n` on `Ω` for some `n ≠ 0`, between
finite-dimensional spaces, then `x ↦ Φ x (u x)` is weakly differentiable in the direction `v` on
`Ω`, with derivative `Φ u' + (∂_v Φ) u`, for an additive Haar measure. -/
theorem HasWeakLineDerivOn.contDiffOn_clm_apply_of_ne_zero [FiniteDimensional ℝ F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {n : WithTop ℕ∞} {Φ : E → F →L[ℝ] G} (h : HasWeakLineDerivOn μ Ω u u' v)
    (hΦ : ContDiffOn ℝ n Φ Ω) (hn : n ≠ 0) :
    HasWeakLineDerivOn μ Ω (fun x => Φ x (u x)) (fun x => Φ x (u' x) + fderiv ℝ Φ x v (u x))
      v := by
  -- Expand `Φ x = ∑ₘ cₘ (Φ x) • bₘ` in a basis `(bₘ)` of `F →L[ℝ] G`; the scalar `C¹` Leibniz
  -- rule applies to each `cₘ (Φ x) • bₘ (u x)`.
  set b := Module.finBasis ℝ (F →L[ℝ] G)
  let c : Fin (Module.finrank ℝ (F →L[ℝ] G)) → (F →L[ℝ] G) →L[ℝ] ℝ := fun m =>
    LinearMap.toContinuousLinearMap (b.coord m)
  have hexp (T : F →L[ℝ] G) (y : F) : ∑ m, c m T • b m y = T y := by
    calc ∑ m, c m T • b m y = (∑ m, b.repr T m • b m) y := by
          simp [-Module.Basis.sum_repr, c]
      _ = T y := by rw [b.sum_repr]
  have hsum := HasWeakLineDerivOn.sum (F := G) Finset.univ fun m _ =>
    (h.clm_comp (b m)).contDiffOn_smul_of_ne_zero ((c m).contDiff.comp_contDiffOn hΦ) hn
  refine (hsum.congr_ae (Filter.Eventually.of_forall fun x => hexp (Φ x) (u x))).congr_ae_deriv ?_
  filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
  have hd : DifferentiableAt ℝ Φ x :=
    ((hΦ.of_le (ENat.one_le_iff_ne_zero_withTop.2 hn)).differentiableOn one_ne_zero x
      hx).differentiableAt (Ω.isOpen.mem_nhds hx)
  simp only [Finset.sum_add_distrib, fderiv_comp x (c _).differentiableAt hd,
    ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply, Function.comp_apply, hexp]

/-- **The Leibniz rule for weak Fréchet derivatives with a `C¹` operator-valued factor**:
`D(Φ u) = Φ Du + (DΦ) u` on `Ω` for `Φ : E → (F →L[ℝ] G)` that is `C^n` on `Ω` with `n ≠ 0`,
between finite-dimensional spaces, for an additive Haar measure. -/
theorem HasWeakFDerivOn.contDiffOn_clm_apply_of_ne_zero [FiniteDimensional ℝ F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {n : WithTop ℕ∞} {Φ : E → F →L[ℝ] G} {U : E → E →L[ℝ] F} (h : HasWeakFDerivOn μ Ω u U)
    (hΦ : ContDiffOn ℝ n Φ Ω) (hn : n ≠ 0) :
    HasWeakFDerivOn μ Ω (fun x => Φ x (u x))
      (fun x => (Φ x).comp (U x) + (fderiv ℝ Φ x).flip (u x)) := by
  rw [hasWeakFDerivOn_iff]
  intro v
  have hv := (h.hasWeakLineDerivOn v).contDiffOn_clm_apply_of_ne_zero hΦ hn
  convert hv using 2 with x
  simp

/-- **A bounded Lipschitz factor keeps an `Lᵖ` weak derivative.** Let `1 ≤ p`. If `u ∈ Lᵖ(Ω)` has
a weak derivative `u' ∈ Lᵖ(Ω)` in the direction `v` and `ψ` is `K`-Lipschitz on `Ω` with
`‖ψ‖ ≤ M` there, then `ψ u` has a weak derivative `G` in the direction `v` that lies in `Lᵖ(Ω)`,
namely `ψ u' + (∂_v ψ) u` from `TauCeti.HasWeakLineDerivOn.lipschitzOnWith_smul`, with

`‖G‖_{Lᵖ(Ω)} ≤ M ‖u'‖_{Lᵖ(Ω)} + K ‖v‖ ‖u‖_{Lᵖ(Ω)}`. -/
theorem HasWeakLineDerivOn.exists_norm_le_lipschitzOnWith_smul {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {M : ℝ} (h : HasWeakLineDerivOn μ Ω u u' v) (hψ : LipschitzOnWith K ψ Ω)
    (hψb : ∀ x ∈ (Ω : Set E), ‖ψ x‖ ≤ M) (hu : MemLp u p (μ.restrict Ω))
    (hu' : MemLp u' p (μ.restrict Ω)) :
    ∃ G : Lp F p (μ.restrict Ω),
      ‖G‖ ≤ M * (eLpNorm u' p (μ.restrict Ω)).toReal +
          K * ‖v‖ * (eLpNorm u p (μ.restrict Ω)).toReal ∧
        HasWeakLineDerivOn μ Ω (fun x => ψ x • u x) G v := by
  have hΩm : MeasurableSet (Ω : Set E) := Ω.isOpen.measurableSet
  have hm := ((memLp_top_of_bound (hψ.continuousOn.aestronglyMeasurable hΩm) M
    ((ae_restrict_mem hΩm).mono hψb)).smul (r := p) hu').add
    ((hψ.memLp_lineDeriv Ω.isOpen v).smul (r := p) hu)
  refine ⟨hm.toLp _, ?_, (h.lipschitzOnWith_smul hψ).congr_ae_deriv hm.coeFn_toLp.symm⟩
  rcases (Ω : Set E).eq_empty_or_nonempty with hΩ | ⟨x₀, hx₀⟩
  · simp [Lp.norm_toLp, hΩ]
  lift M to ℝ≥0 using (norm_nonneg _).trans (hψb x₀ hx₀)
  -- Pointwise, `|ψ| ≤ M` and `|∂_v ψ| ≤ K ‖v‖` on `Ω`.
  have hle := eLpNorm_le_mul_add_mul_of_ae_norm_le (A := M) (B := K * ‖v‖₊) (p := p)
    (f := fun x => ψ x • u' x + lineDeriv ℝ ψ x v • u x) Fact.out
    hm.aestronglyMeasurable hu'.aestronglyMeasurable hu.aestronglyMeasurable <| by
      filter_upwards [ae_restrict_mem hΩm] with x hx
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (hψb x hx) (norm_nonneg _)
      · rw [norm_smul, NNReal.coe_mul, coe_nnNorm]
        exact mul_le_mul_of_nonneg_right
          (norm_lineDeriv_le_of_lipschitzOn ℝ (Ω.isOpen.mem_nhds hx) hψ) (norm_nonneg _)
  have hu_ne := hu.eLpNorm_ne_top
  have hu'_ne := hu'.eLpNorm_ne_top
  rw [Lp.norm_toLp]
  refine (ENNReal.toReal_mono (by finiteness) hle).trans_eq ?_
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp

end Lipschitz

section LpBound

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E} {p : ENNReal}

/-- **`Lᵖ` bound for the Leibniz derivative.** Let `μ` be a measure on a finite-dimensional real
normed space `E` and let `ψ : E → ℝ` satisfy `|ψ| ≤ A` and `‖Dψ‖ ≤ B` almost everywhere. Then the
derivative `ψ Du + Dψ ⊗ u` of `ψ u` in `TauCeti.HasWeakFDerivOn.contDiffOn_smul` satisfies
`‖D(ψ u)‖_{Lᵖ(μ)} ≤ A ‖Du‖_{Lᵖ(μ)} + B ‖u‖_{Lᵖ(μ)}` for `1 ≤ p`. The local bound on a measurable
set `K` is the case `μ = volume.restrict K`. -/
theorem eLpNorm_smul_add_fderiv_smulRight_le (hp : 1 ≤ p) {ψ : E → ℝ}
    (hψ : AEStronglyMeasurable ψ μ) {A B : NNReal} (hA : ∀ᵐ z ∂μ, ‖ψ z‖ ≤ A)
    (hB : ∀ᵐ z ∂μ, ‖fderiv ℝ ψ z‖ ≤ B) {u : E → F} {D : E → E →L[ℝ] F}
    (hD : AEStronglyMeasurable D μ) (hu : AEStronglyMeasurable u μ) :
    eLpNorm (fun z => ψ z • D z + (fderiv ℝ ψ z).smulRight (u z)) p μ ≤
      A * eLpNorm D p μ + B * eLpNorm u p μ := by
  have hm : AEStronglyMeasurable (fun z => ψ z • D z + (fderiv ℝ ψ z).smulRight (u z)) μ :=
    (hψ.smul hD).add ((ContinuousLinearMap.smulRightL ℝ ℝ ℝ E F).aestronglyMeasurable_comp₂
      (measurable_fderiv ℝ ψ).aestronglyMeasurable hu)
  refine eLpNorm_le_mul_add_mul_of_ae_norm_le hp hm hD hu ?_
  filter_upwards [hA, hB] with z hAz hBz
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul]
    exact mul_le_mul_of_nonneg_right hAz (norm_nonneg _)
  · rw [ContinuousLinearMap.norm_smulRight_apply]
    exact mul_le_mul_of_nonneg_right hBz (norm_nonneg _)

end LpBound

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
