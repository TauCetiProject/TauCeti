/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Sobolev
public import TauCeti.Analysis.Sobolev.W1p.Basic
import Mathlib.MeasureTheory.Function.Holder
import TauCeti.Analysis.Distribution.SchwartzSpace.Deriv
import TauCeti.Analysis.Distribution.TemperedDistribution.LaplacianResolvent
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Distribution.TemperedDistribution.TestFunction
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.InnerProductSpace.LaxMilgram
import TauCeti.Analysis.Sobolev.BesselPotential.Basic
import TauCeti.Analysis.Sobolev.Poincare.Schrodinger
import TauCeti.Analysis.Sobolev.W1p.Density
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian

/-!
# The stationary Schrödinger equation with a potential positive at infinity

Let `E` be a finite-dimensional real inner product space and `V` an essentially bounded,
almost everywhere nonnegative potential on `E` that is bounded below by a constant `a > 0`
outside a ball. This file proves that for every `g ∈ L²(E)` the stationary Schrödinger equation
`-Δf + V f = g` has exactly one weak solution `f ∈ L²(E)` up to null sets, and that it lies in
`H²(E)`. Here `f ∈ L²(E)` is a *weak solution* if

`∫ f (-Δφ + V φ) = ∫ g φ`

for every compactly supported smooth `φ`.

The potential may vanish on a large set inside the ball, so `-Δ + V` is not a perturbation of
`-Δ + c` for a constant `c > 0`, and the Laplacian alone has no spectral gap on the whole space.
The Poincaré inequality for Schrödinger forms
(`TauCeti.exists_pos_mul_integral_norm_sq_le_integral_norm_fderiv_sq_add_integral_mul_norm_sq`)
restores the gap: after passing from compactly supported smooth functions to all of
`H¹(E) = W^{1,2}(E)` by density (`TauCeti.W1p.denseRange_ofTestFunctionₗ_top`), the form
`∫ ⟪∇u, ∇v⟫ + ∫ V u v` is coercive on `H¹(E)`. The Lax–Milgram theorem then gives existence
and uniqueness of a weak solution in `H¹(E)` for every `g ∈ L²(E)`.

Regularity is a Fourier argument on tempered distributions: a weak solution satisfies
`-Δf + f = g + f - V f`, so if `f`, `V f` and `g` lie in `H^s` then the resolvent of the
Laplacian (`TemperedDistribution.memSobolev_add_two_iff_neg_laplacian_add_smul`) puts `f` in
`H^(s+2)`. This step uses no sign or bound on `V`, and iterating it gives higher regularity
whenever multiplication by `V` preserves the Sobolev scale. At `s = 0`, boundedness of `V`
suffices, so every weak solution in `L²(E)` lies in `H²(E) ⊆ H¹(E)`, where coercivity makes it
unique.

On the plane, the potential `V = |α|² / 4` of the gauge Laplacian `d₀* d₀ = -Δ + |α|² / 4` of a
framed vortex field vanishes at the zeros of the section `α` and tends to `1 / 4` at infinity;
that is the application in `TauCeti.Analysis.PDE.Vortex.GaugeLaplacian`.

## Main results

* `exists_pos_mul_norm_sq_le_norm_gradient_sq_add_integral_mul_value_sq`: coercivity of the
  Schrödinger form, `c ‖u‖²_{H¹} ≤ ‖∇u‖₂² + ∫ V u²`.
* `existsUnique_forall_integral_inner_gradient_add_integral_mul_eq`: existence and uniqueness of
  the weak solution in `H¹(E)`.
* `IsWeakSolutionSchrodinger`: weak solutions of `-Δf + V f = g`.
* `IsWeakSolutionSchrodinger.mem_realSobolevFunctions_add_two`: a weak solution gains two
  derivatives over `f`, `V f` and `g`.
* `IsWeakSolutionSchrodinger.mem_realSobolevFunctions_two`: for bounded `V`, a weak solution in
  `L²(E)` lies in `H²(E)`.
* `exists_mem_realSobolevFunctions_isWeakSolutionSchrodinger`: for every `g ∈ L²(E)` there is a
  weak solution in `H²(E)`.
* `IsWeakSolutionSchrodinger.ae_eq`: two weak solutions in `L²(E)` agree almost everywhere.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Springer (2001), §8.2 (the energy method and the Lax–Milgram theorem).
* M. Reed and B. Simon, *Methods of Modern Mathematical Physics IV: Analysis of Operators*,
  Academic Press (1978), §XIII.1 (quadratic forms of Schrödinger operators).
-/

public section

noncomputable section

namespace TauCeti.PDE

open MeasureTheory TemperedDistribution TopologicalSpace Filter
open scoped ENNReal SchwartzMap RealInnerProductSpace Gradient Laplacian Distributions ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### Weak solutions -/

/-- **The weak formulation of the stationary Schrödinger equation.** A real function `f` is a weak
solution of `-Δf + V f = g` when

`∫ f (-Δφ + V φ) = ∫ g φ` for every compactly supported smooth `φ`.

Nothing is assumed about `V`, `f` and `g`; each theorem below names the hypotheses it uses. -/
def IsWeakSolutionSchrodinger (V f g : E → ℝ) : Prop :=
  ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    ∫ x, f x * (-Δ φ x + V x * φ x) = ∫ x, g x * φ x

/-- Being a weak solution, written out as the integral identity `∫ f (-Δφ + V φ) = ∫ g φ`. -/
theorem isWeakSolutionSchrodinger_iff {V f g : E → ℝ} :
    IsWeakSolutionSchrodinger V f g ↔ ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ x, f x * (-Δ φ x + V x * φ x) = ∫ x, g x * φ x :=
  Iff.rfl

/-- Being a weak solution only depends on the solution up to null sets. -/
theorem IsWeakSolutionSchrodinger.congr_ae {V f f' g : E → ℝ}
    (h : IsWeakSolutionSchrodinger V f g) (hff' : f =ᵐ[volume] f') :
    IsWeakSolutionSchrodinger V f' g := fun φ hφ hc ↦ by
  rw [← h φ hφ hc]
  exact integral_congr_ae (hff'.mono fun x hx ↦ by simp only [hx])

/-! ### The Schrödinger form on `H¹(E)` -/

section Form

variable {V : E → ℝ}

/-- Multiplication by an essentially bounded potential, as a bounded operator on `L²(E)`. -/
private def potentialMul (hV : MemLp V ∞ (volume : Measure E)) :
    Lp ℝ 2 ((volume : Measure E).restrict (⊤ : Opens E)) →L[ℝ]
      Lp ℝ 2 ((volume : Measure E).restrict (⊤ : Opens E)) :=
  (ContinuousLinearMap.lsmul ℝ ℝ).holderL _ ∞ 2 2 ((hV.restrict _).toLp V)

private theorem potentialMul_ae (hV : MemLp V ∞ (volume : Measure E))
    (f : Lp ℝ 2 ((volume : Measure E).restrict (⊤ : Opens E))) :
    potentialMul hV f =ᵐ[volume] fun x ↦ V x * f x := by
  have h := (ContinuousLinearMap.lsmul ℝ ℝ).coeFn_holder (r := 2) ((hV.restrict _).toLp V) f
  have h' := (hV.restrict ((⊤ : Opens E) : Set E)).coeFn_toLp
  simp only [Opens.coe_top, Measure.restrict_univ] at h h'
  filter_upwards [h, h'] with x hx hx'
  simp only [potentialMul, ContinuousLinearMap.holderL_apply_apply, hx, hx',
    ContinuousLinearMap.lsmul_apply, smul_eq_mul]

/-- The Schrödinger form `(u, v) ↦ ⟪∇u, ∇v⟫ + ⟪u, V v⟫` on `H¹(E)`. -/
private def schrodingerForm (hV : MemLp V ∞ (volume : Measure E)) :
    W1p (volume : Measure E) ⊤ 2 →L[ℝ] W1p (volume : Measure E) ⊤ 2 →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun u v ↦ ⟪W1p.gradient u, W1p.gradient v⟫ +
        ⟪W1p.value u, potentialMul hV (W1p.value v)⟫)
      (fun u u' v ↦ by
        simp only [← W1p.gradientL_apply, ← W1p.valueL_apply, map_add, inner_add_left]; ring)
      (fun c u v ↦ by
        simp only [← W1p.gradientL_apply, ← W1p.valueL_apply, map_smul, real_inner_smul_left,
          smul_eq_mul]; ring)
      (fun u v v' ↦ by
        simp only [← W1p.gradientL_apply, ← W1p.valueL_apply, map_add, inner_add_right]; ring)
      (fun c u v ↦ by
        simp only [← W1p.gradientL_apply, ← W1p.valueL_apply, map_smul, real_inner_smul_right,
          smul_eq_mul]; ring))
    (1 + ‖potentialMul hV‖) fun u v ↦ by
      simp only [LinearMap.mk₂_apply]
      have h1 := abs_real_inner_le_norm (W1p.gradient u) (W1p.gradient v)
      have h2 := abs_real_inner_le_norm (W1p.value u) (potentialMul hV (W1p.value v))
      have h3 := (potentialMul hV).le_opNorm (W1p.value v)
      have hgu := W1p.norm_gradient_le u
      have hgv := W1p.norm_gradient_le v
      have hvu := W1p.norm_value_le u
      have hvv := W1p.norm_value_le v
      rw [Real.norm_eq_abs]
      refine (abs_add_le _ _).trans ?_
      have hM := norm_nonneg (potentialMul hV)
      calc _ ≤ ‖W1p.gradient u‖ * ‖W1p.gradient v‖ +
            ‖W1p.value u‖ * (‖potentialMul hV‖ * ‖W1p.value v‖) := by
            gcongr
            exact h2.trans (mul_le_mul_of_nonneg_left h3 (norm_nonneg _))
        _ ≤ ‖u‖ * ‖v‖ + ‖u‖ * (‖potentialMul hV‖ * ‖v‖) := by gcongr
        _ = (1 + ‖potentialMul hV‖) * ‖u‖ * ‖v‖ := by ring

private theorem schrodingerForm_apply (hV : MemLp V ∞ (volume : Measure E))
    (u v : W1p (volume : Measure E) ⊤ 2) :
    schrodingerForm hV u v = (∫ x, ⟪W1p.gradient u x, W1p.gradient v x⟫) +
      ∫ x, V x * (W1p.value u x * W1p.value v x) := by
  simp only [schrodingerForm, LinearMap.mkContinuous₂_apply, LinearMap.mk₂_apply, L2.inner_def,
    Opens.coe_top, Measure.restrict_univ]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [potentialMul_ae hV (W1p.value v)] with x hx
  rw [hx, real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial, RCLike.re_to_real]
  ring

private theorem schrodingerForm_self (hV : MemLp V ∞ (volume : Measure E))
    (u : W1p (volume : Measure E) ⊤ 2) :
    schrodingerForm hV u u = ‖W1p.gradient u‖ ^ 2 + ∫ x, V x * W1p.value u x ^ 2 := by
  rw [schrodingerForm_apply, ← W1p.integral_norm_gradient_sq_eq_norm_gradient_sq]
  simp only [Opens.coe_top, Measure.restrict_univ, real_inner_self_eq_norm_sq, sq]

/-- The forcing `v ↦ ∫ g v` of an `L²` function, as a continuous linear functional on `H¹(E)`. -/
private def forcing {g : E → ℝ} (hg : MemLp g 2 (volume : Measure E)) :
    StrongDual ℝ (W1p (volume : Measure E) ⊤ 2) :=
  (innerSL ℝ ((hg.restrict ((⊤ : Opens E) : Set E)).toLp g)).comp W1p.valueL

private theorem forcing_apply {g : E → ℝ} (hg : MemLp g 2 (volume : Measure E))
    (v : W1p (volume : Measure E) ⊤ 2) : forcing hg v = ∫ x, g x * W1p.value v x := by
  have h := (hg.restrict ((⊤ : Opens E) : Set E)).coeFn_toLp
  simp only [Opens.coe_top, Measure.restrict_univ] at h
  simp only [forcing, ContinuousLinearMap.comp_apply, innerSL_apply_apply, L2.inner_def,
    Opens.coe_top, Measure.restrict_univ]
  refine integral_congr_ae (h.mono fun x hx ↦ ?_)
  beta_reduce
  rw [hx, real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial, RCLike.re_to_real, mul_comm,
    W1p.valueL_apply]

end Form

/-! ### Coercivity and the weak solution in `H¹(E)` -/

section Coercive

variable [Nontrivial E] {V : E → ℝ} {a R : ℝ}

/-- The Poincaré inequality for the Schrödinger form, extended from test functions to all of
`H¹(E)` by density. -/
private theorem mul_norm_value_sq_le_schrodingerForm (hV : MemLp V ∞ (volume : Measure E))
    (hV₀ : ∀ᵐ x, 0 ≤ V x) (ha : 0 < a) (haV : ∀ᵐ x, R < ‖x‖ → a ≤ V x) :
    ∃ c > 0, ∀ u : W1p (volume : Measure E) ⊤ 2,
      c * ‖W1p.value u‖ ^ 2 ≤ schrodingerForm hV u u := by
  obtain ⟨c, hc, hP⟩ :=
    exists_pos_mul_integral_norm_sq_le_integral_norm_fderiv_sq_add_integral_mul_norm_sq
      (μ := volume) (F := ℝ) (hV.locallyIntegrable le_top) hV₀ ha haV
  refine ⟨c, hc, fun u ↦ ?_⟩
  refine (W1p.denseRange_ofTestFunctionₗ_top (mu := volume) (p := 2) (by norm_num)).induction_on
    u (isClosed_le (continuous_const.mul
      (((W1p.valueL (mu := volume) (Omega := ⊤) (p := 2)).continuous.congr
        W1p.valueL_apply).norm.pow 2))
      ((schrodingerForm hV).continuous₂.comp
      (continuous_id.prodMk continuous_id))) fun φ ↦ ?_
  have hv := W1p.value_ofTestFunctionₗ_top_ae (mu := volume) (p := 2) φ
  rw [schrodingerForm_self, W1p.norm_value_ofTestFunctionₗ_top_sq,
    W1p.norm_gradient_ofTestFunctionₗ_top_sq]
  have h := hP φ (φ.contDiff.of_le (by simp)) φ.hasCompactSupport
  simp only [Real.norm_eq_abs, sq_abs] at h
  convert h using 2
  exact integral_congr_ae (hv.mono fun x hx ↦ by simp only [hx])

/-- **Coercivity of the Schrödinger form on `H¹(E)`.** Let `V` be essentially bounded, almost
everywhere nonnegative, and almost everywhere at least `a > 0` outside the closed ball of radius
`R`. Then there is `c > 0` with `c ‖u‖²_{H¹} ≤ ‖∇u‖₂² + ∫ V u²` for every `u ∈ H¹(E)`. -/
theorem exists_pos_mul_norm_sq_le_norm_gradient_sq_add_integral_mul_value_sq
    (hV : MemLp V ∞ (volume : Measure E)) (hV₀ : ∀ᵐ x, 0 ≤ V x) (ha : 0 < a)
    (haV : ∀ᵐ x, R < ‖x‖ → a ≤ V x) :
    ∃ c > 0, ∀ u : W1p (volume : Measure E) ⊤ 2,
      c * ‖u‖ ^ 2 ≤ ‖W1p.gradient u‖ ^ 2 + ∫ x, V x * W1p.value u x ^ 2 := by
  obtain ⟨c, hc, hP⟩ := mul_norm_value_sq_le_schrodingerForm hV hV₀ ha haV
  refine ⟨min 1 c / 2, by positivity, fun u ↦ ?_⟩
  have hP := hP u
  rw [schrodingerForm_self] at hP
  have hpot : 0 ≤ ∫ x, V x * W1p.value u x ^ 2 :=
    integral_nonneg_of_ae (hV₀.mono fun x hx ↦ by positivity)
  have h1 : min 1 c ≤ 1 := min_le_left _ _
  have h2 : min 1 c ≤ c := min_le_right _ _
  have h0 : 0 ≤ min 1 c := le_min zero_le_one hc.le
  rw [W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq]
  nlinarith [sq_nonneg ‖W1p.value u‖, sq_nonneg ‖W1p.gradient u‖,
    mul_le_mul_of_nonneg_right h2 (sq_nonneg ‖W1p.value u‖),
    mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖W1p.gradient u‖)]

private theorem isCoercive_schrodingerForm (hV : MemLp V ∞ (volume : Measure E))
    (hV₀ : ∀ᵐ x, 0 ≤ V x) (ha : 0 < a) (haV : ∀ᵐ x, R < ‖x‖ → a ≤ V x) :
    IsCoercive (schrodingerForm hV) := by
  obtain ⟨c, hc, h⟩ := exists_pos_mul_norm_sq_le_norm_gradient_sq_add_integral_mul_value_sq
    hV hV₀ ha haV
  exact ⟨c, hc, fun u ↦ by rw [schrodingerForm_self, mul_assoc, ← sq]; exact h u⟩

/-- **Existence and uniqueness of the weak solution in `H¹(E)`.** Let `V` be essentially
bounded, almost everywhere nonnegative, and almost everywhere at least `a > 0` outside a ball.
For every `g ∈ L²(E)` there is exactly one `u ∈ H¹(E)` with

`∫ ⟪∇u, ∇v⟫ + ∫ V u v = ∫ g v`

for every `v ∈ H¹(E)`. -/
theorem existsUnique_forall_integral_inner_gradient_add_integral_mul_eq
    (hV : MemLp V ∞ (volume : Measure E)) (hV₀ : ∀ᵐ x, 0 ≤ V x) (ha : 0 < a)
    (haV : ∀ᵐ x, R < ‖x‖ → a ≤ V x) {g : E → ℝ} (hg : MemLp g 2 (volume : Measure E)) :
    ∃! u : W1p (volume : Measure E) ⊤ 2, ∀ v : W1p (volume : Measure E) ⊤ 2,
      (∫ x, ⟪W1p.gradient u x, W1p.gradient v x⟫) +
        ∫ x, V x * (W1p.value u x * W1p.value v x) = ∫ x, g x * W1p.value v x := by
  simpa only [schrodingerForm_apply, forcing_apply] using
    (isCoercive_schrodingerForm hV hV₀ ha haV).existsUnique_forall_eq (forcing hg)

end Coercive

/-! ### Regularity -/

/-- The distributional form of a weak solution: if `f` is a weak solution of `-Δf + V f = g`,
with `f`, `V f` and `g` square integrable, then `-Δf + f = g + f - V f` as tempered
distributions. -/
private theorem neg_laplacian_add_eq {V f g : E → ℝ} (heq : IsWeakSolutionSchrodinger V f g)
    (hfL : MemLp f 2 volume) (hVfL : MemLp (fun x ↦ V x * f x) 2 volume) (hgL : MemLp g 2 volume)
    {uf uR : Lp ℝ 2 (volume : Measure E)} (huf : uf =ᵐ[volume] f)
    (huR : uR =ᵐ[volume] g + f - fun x ↦ V x * f x) :
    -Δ (Lp.toTemperedDistribution (Complex.ofRealCLM.compLp uf) : 𝓢'(E, ℂ)) +
        (1 : ℝ) • (Lp.toTemperedDistribution (Complex.ofRealCLM.compLp uf) : 𝓢'(E, ℂ)) =
      Lp.toTemperedDistribution (Complex.ofRealCLM.compLp uR) := by
  refine ext_real fun φ hφ ↦ ?_
  have hφ2 := φ.memLp 2 (μ := volume)
  have hΔ2 : MemLp (Δ (φ : E → ℝ)) 2 volume := by
    convert (Δ φ).memLp 2 (μ := volume) using 1
    exact funext fun x ↦ (SchwartzMap.laplacian_apply φ x).symm
  -- Both sides as real integrals against `f`, `g` and `V f`.
  rw [add_apply, neg_apply, smul_apply, laplacian_apply_apply, TauCeti.laplacian_postcompCLM,
    Lp.toTemperedDistribution_ofRealCLM_compLp_apply_postcompCLM,
    Lp.toTemperedDistribution_ofRealCLM_compLp_apply_postcompCLM,
    Lp.toTemperedDistribution_ofRealCLM_compLp_apply_postcompCLM, one_smul]
  have hA : ∫ x, (Δ φ) x * uf x = ∫ x, f x * Δ (φ : E → ℝ) x :=
    integral_congr_ae (huf.mono fun x hx ↦ by simp only [hx, SchwartzMap.laplacian_apply, mul_comm])
  have hB : ∫ x, φ x * uf x = ∫ x, φ x * f x :=
    integral_congr_ae (huf.mono fun x hx ↦ by simp only [hx])
  have hC : ∫ x, φ x * uR x = ∫ x, φ x * (g + f - fun x ↦ V x * f x) x :=
    integral_congr_ae (huR.mono fun x hx ↦ by simp only [hx])
  rw [hA, hB, hC]
  -- Split the integrals of the weak equation and of the right-hand side.
  have h := heq φ (φ.smooth ⊤) hφ
  have i1 : Integrable (fun x ↦ f x * Δ (φ : E → ℝ) x) := hfL.integrable_mul hΔ2
  have i2 : Integrable (fun x ↦ φ x * (V x * f x)) := hφ2.integrable_mul hVfL
  have i3 : Integrable (fun x ↦ φ x * g x) := hφ2.integrable_mul hgL
  have i4 : Integrable (fun x ↦ φ x * f x) := hφ2.integrable_mul hfL
  have e1 : ∫ x, f x * (-Δ (φ : E → ℝ) x + V x * φ x) =
      -(∫ x, f x * Δ (φ : E → ℝ) x) + ∫ x, φ x * (V x * f x) := by
    rw [← integral_neg, ← integral_add (f := fun x ↦ -(f x * Δ (φ : E → ℝ) x)) i1.neg i2]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
  have e2 : ∫ x, φ x * (g + f - fun x ↦ V x * f x) x =
      (∫ x, φ x * g x) + (∫ x, φ x * f x) - ∫ x, φ x * (V x * f x) := by
    rw [← integral_add (f := fun x ↦ φ x * g x) (g := fun x ↦ φ x * f x) i3 i4,
      ← integral_sub (f := fun x ↦ φ x * g x + φ x * f x) (i3.add i4) i2]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by
      simp only [Pi.add_apply, Pi.sub_apply]; ring)
  have e3 : ∫ x, g x * φ x = ∫ x, φ x * g x :=
    integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)
  rw [e2]
  rw [e1, e3] at h
  push_cast
  rw [← Complex.ofReal_neg, ← Complex.ofReal_add, ← Complex.ofReal_add, ← Complex.ofReal_sub]
  congr 1
  linarith

/-- **Weak solutions of `-Δf + V f = g` gain two derivatives.** If `f`, `V f` and `g` lie in
`H^s(E)` and `f` is a weak solution of `-Δf + V f = g`, then `f ∈ H^(s+2)(E)`. No sign or bound on
`V` is assumed. -/
theorem IsWeakSolutionSchrodinger.mem_realSobolevFunctions_add_two {s : ℝ} {V f g : E → ℝ}
    (heq : IsWeakSolutionSchrodinger V f g) (hf : f ∈ realSobolevFunctions E s 2)
    (hVf : (fun x ↦ V x * f x) ∈ realSobolevFunctions E s 2)
    (hg : g ∈ realSobolevFunctions E s 2) :
    f ∈ realSobolevFunctions E (s + 2) 2 := by
  obtain ⟨uf, huf, -⟩ := mem_realSobolevFunctions.1 hf
  obtain ⟨uR, huR, hRs⟩ := mem_realSobolevFunctions.1 (sub_mem (add_mem hg hf) hVf)
  have hT := neg_laplacian_add_eq heq (memLp_of_mem_realSobolevFunctions hf)
    (memLp_of_mem_realSobolevFunctions hVf) (memLp_of_mem_realSobolevFunctions hg) huf huR
  exact mem_realSobolevFunctions.2 ⟨uf, huf,
    (memSobolev_add_two_iff_neg_laplacian_add_smul one_pos).2 (by rw [hT]; exact hRs)⟩

/-! ### Weak solutions in `L²(E)` -/

section Weak

variable {V : E → ℝ}

/-- For `u ∈ H¹(E)`, testing `u` against `-Δφ + V φ` is the Schrödinger form of `u` and `φ`. -/
private theorem integral_value_mul_eq_schrodingerForm (hV : MemLp V ∞ (volume : Measure E))
    (u : W1p (volume : Measure E) ⊤ 2) (φ : 𝓓((⊤ : Opens E), ℝ)) :
    ∫ x, W1p.value u x * (-Δ (φ : E → ℝ) x + V x * φ x) =
      schrodingerForm hV u (W1p.ofTestFunctionₗ volume ⊤ 2 φ) := by
  have hu : MemLp (W1p.value u : E → ℝ) 2 volume := W1p.memLp_value u
  have hφ2 : MemLp (φ : E → ℝ) 2 volume :=
    φ.contDiff.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport
  have hΔ2 : MemLp (Δ (φ : E → ℝ)) 2 volume :=
    (φ.contDiff.of_le (by simp)).continuous_laplacian.memLp_of_hasCompactSupport
      φ.hasCompactSupport.laplacian
  have hibp := (W1p.hasWeakFDerivOn u).integral_laplacian_smul_eq_neg_integral_inner φ
  simp only [smul_eq_mul] at hibp
  have hv := W1p.value_ofTestFunctionₗ_top_ae (mu := volume) (p := 2) φ
  have hg := W1p.gradient_ofTestFunctionₗ_top_ae (mu := volume) (p := 2) φ
  rw [schrodingerForm_apply]
  have e1 : ∫ x, W1p.value u x * (-Δ (φ : E → ℝ) x + V x * φ x) =
      -(∫ x, Δ (φ : E → ℝ) x * W1p.value u x) + ∫ x, V x * (W1p.value u x * φ x) := by
    rw [← integral_neg, ← integral_add (f := fun x ↦ -(Δ (φ : E → ℝ) x * W1p.value u x))
      (hΔ2.integrable_mul hu).neg
        (memLp_one_iff_integrable.1 (hV.fun_mul (hu.fun_mul hφ2 : MemLp _ 1 volume)))]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
  rw [e1, hibp, neg_neg]
  congr 1
  · refine integral_congr_ae (hg.mono fun x hx ↦ ?_)
    simp only [hx, real_inner_comm]
  · exact integral_congr_ae (hv.mono fun x hx ↦ by simp only [hx])

/-- An `H¹` function which is a weak solution of `-Δf + V f = g` satisfies the variational
equation of the Schrödinger form against all of `H¹(E)`. -/
private theorem schrodingerForm_eq_forcing (hV : MemLp V ∞ (volume : Measure E))
    {g : E → ℝ} (hg : MemLp g 2 (volume : Measure E)) {u : W1p (volume : Measure E) ⊤ 2}
    (hu : IsWeakSolutionSchrodinger V (W1p.value u) g) (v : W1p (volume : Measure E) ⊤ 2) :
    schrodingerForm hV u v = forcing hg v := by
  refine (W1p.denseRange_ofTestFunctionₗ_top (mu := volume) (p := 2) (by norm_num)).induction_on
    v (isClosed_eq (schrodingerForm hV u).continuous (forcing hg).continuous) fun φ ↦ ?_
  have h := hu φ (φ.contDiff) φ.hasCompactSupport
  rw [integral_value_mul_eq_schrodingerForm hV] at h
  rw [h, forcing_apply]
  exact integral_congr_ae ((W1p.value_ofTestFunctionₗ_top_ae (mu := volume) (p := 2) φ).mono
    fun x hx ↦ by simp only [hx])

/-- A real `H¹` function is the value of an element of `W^{1,2}(E)`. -/
private theorem exists_w1p_value_ae_eq {f : E → ℝ} (hf : f ∈ realSobolevFunctions E 1 2) :
    ∃ w : W1p (volume : Measure E) ⊤ 2, (W1p.value w : E → ℝ) =ᵐ[volume] f := by
  obtain ⟨u, hu, hs⟩ := mem_realSobolevFunctions.1 hf
  obtain ⟨w, hw⟩ := (Lp.memSobolev_natCast_iff_exists_wkp_value_eq (by norm_num) (by norm_num) 1
    u).1 (by exact_mod_cast hs)
  exact ⟨Wkp.firstOrder 0 w, by rw [Wkp.value_firstOrder]; exact hw.trans hu⟩

/-- **Weak solutions in `L²(E)` lie in `H²(E)`.** For an essentially bounded `V` and
`g ∈ L²(E)`, every weak solution `f ∈ L²(E)` of `-Δf + V f = g` lies in `H²(E)`. -/
theorem IsWeakSolutionSchrodinger.mem_realSobolevFunctions_two {V f g : E → ℝ}
    (heq : IsWeakSolutionSchrodinger V f g) (hV : MemLp V ∞ (volume : Measure E))
    (hf : MemLp f 2 (volume : Measure E)) (hg : MemLp g 2 (volume : Measure E)) :
    f ∈ realSobolevFunctions E 2 2 := by
  simpa only [zero_add] using heq.mem_realSobolevFunctions_add_two (s := 0)
    (mem_realSobolevFunctions_zero_iff.2 hf) (mem_realSobolevFunctions_zero_iff.2 (hV.fun_mul hf))
    (mem_realSobolevFunctions_zero_iff.2 hg)

variable [Nontrivial E] {a R : ℝ}

/-- **Existence of the weak solution in `H²(E)`.** Let `V` be essentially bounded, almost
everywhere nonnegative, and almost everywhere at least `a > 0` outside a ball. For every
`g ∈ L²(E)` the equation `-Δf + V f = g` has a weak solution `f ∈ H²(E)`. -/
theorem exists_mem_realSobolevFunctions_isWeakSolutionSchrodinger
    (hV : MemLp V ∞ (volume : Measure E)) (hV₀ : ∀ᵐ x, 0 ≤ V x) (ha : 0 < a)
    (haV : ∀ᵐ x, R < ‖x‖ → a ≤ V x) {g : E → ℝ} (hg : MemLp g 2 (volume : Measure E)) :
    ∃ f ∈ realSobolevFunctions E 2 2, IsWeakSolutionSchrodinger V f g := by
  set u := (isCoercive_schrodingerForm hV hV₀ ha haV).solutionOfFunctional (forcing hg)
  have hu : IsWeakSolutionSchrodinger V (W1p.value u) g := by
    intro φ hφ hc
    let φ' : 𝓓((⊤ : Opens E), ℝ) := ⟨φ, hφ, hc, by simp only [Opens.coe_top, Set.subset_univ]⟩
    have hcoe : (φ' : E → ℝ) = φ := TestFunction.coe_mk
    have h := integral_value_mul_eq_schrodingerForm hV u φ'
    rw [hcoe, (isCoercive_schrodingerForm hV hV₀ ha haV).apply_solutionOfFunctional_eq,
      forcing_apply] at h
    rw [h]
    refine integral_congr_ae ((W1p.value_ofTestFunctionₗ_top_ae (mu := volume) (p := 2)
      φ').mono fun x hx ↦ ?_)
    simp only [hx, hcoe]
  exact ⟨_, hu.mem_realSobolevFunctions_two hV (W1p.memLp_value u) hg, hu⟩

/-- **Uniqueness of the weak solution in `L²(E)`.** Let `V` be essentially bounded, almost
everywhere nonnegative, and almost everywhere at least `a > 0` outside a ball. Two weak solutions
`f₁, f₂ ∈ L²(E)` of `-Δf + V f = g`, for the same `g`, agree almost everywhere. -/
theorem IsWeakSolutionSchrodinger.ae_eq {f₁ f₂ g : E → ℝ} (heq₁ : IsWeakSolutionSchrodinger V f₁ g)
    (heq₂ : IsWeakSolutionSchrodinger V f₂ g) (hV : MemLp V ∞ (volume : Measure E))
    (hV₀ : ∀ᵐ x, 0 ≤ V x) (ha : 0 < a) (haV : ∀ᵐ x, R < ‖x‖ → a ≤ V x)
    (hf₁ : MemLp f₁ 2 (volume : Measure E)) (hf₂ : MemLp f₂ 2 (volume : Measure E)) :
    f₁ =ᵐ[volume] f₂ := by
  -- The difference is a weak solution with zero right-hand side.
  have hd : IsWeakSolutionSchrodinger V (f₁ - f₂) 0 := by
    intro φ hφ hc
    have hφ2 : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport hc
    have hT : MemLp (fun x ↦ -Δ φ x + V x * φ x) 2 volume :=
      ((hφ.of_le (by simp)).continuous_laplacian.memLp_of_hasCompactSupport hc.laplacian).neg.add
        (hV.fun_mul hφ2)
    simp only [Pi.sub_apply, Pi.zero_apply, zero_mul, integral_zero, sub_mul]
    rw [integral_sub (f := fun x ↦ f₁ x * (-Δ φ x + V x * φ x))
      (g := fun x ↦ f₂ x * (-Δ φ x + V x * φ x)) (hf₁.integrable_mul hT) (hf₂.integrable_mul hT),
      heq₁ φ hφ hc,
      heq₂ φ hφ hc, sub_self]
  -- It lies in `H²(E) ⊆ H¹(E)`, so it is the value of some `w ∈ W^{1,2}(E)`.
  have h2 := hd.mem_realSobolevFunctions_two hV (hf₁.sub hf₂)
    (MemLp.zero : MemLp (0 : E → ℝ) 2 volume)
  obtain ⟨w, hw⟩ := exists_w1p_value_ae_eq
    (realSobolevFunctions_mono (by norm_num) (by norm_num) (by norm_num) h2)
  -- Coercivity forces `w = 0`.
  have hw0 : schrodingerForm hV w w = 0 := by
    have h := schrodingerForm_eq_forcing hV (MemLp.zero : MemLp (0 : E → ℝ) 2 volume)
      (hd.congr_ae hw.symm) w
    rw [h, forcing_apply]
    simp only [Pi.zero_apply, zero_mul, integral_zero]
  obtain ⟨c, hc, hcoer⟩ := isCoercive_schrodingerForm hV hV₀ ha haV
  have hn : ‖w‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg w) (Ne.symm hne)
    have := hcoer w
    rw [hw0] at this
    linarith [mul_pos (mul_pos hc hpos) hpos]
  rw [norm_eq_zero] at hn
  subst hn
  have h0 : (W1p.value (0 : W1p (volume : Measure E) ⊤ 2) : E → ℝ) =ᵐ[volume] 0 := by
    rw [← W1p.valueL_apply, map_zero]
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      Lp.coeFn_zero ℝ 2 ((volume : Measure E).restrict (⊤ : Opens E))
  filter_upwards [hw.symm.trans h0] with x hx
  simpa [sub_eq_zero] using hx

end Weak

end TauCeti.PDE
