/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.LogVariation
public import TauCeti.Analysis.Complex.ZeroMultiplicity
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Complex.Pompeiu.Basic
import TauCeti.Analysis.Complex.Wirtinger.Holomorphic
import TauCeti.Analysis.PDE.Vortex.Divisor

/-!
# The kernel of the gauge-fixed operator at a vortex has dimension at most `2m`

Let `x` be a field whose holomorphicity rows `∂bar_a α = 0` vanish, with `|α| → 1` at infinity,
and let the zeros of its section `α`, counted with multiplicity, form the effective divisor `D`.
This file proves that every real vector space of `C²` square-integrable solutions `y` of
`L_x y = 0`, for the gauge-fixed operator `L_x = d₀* ⊕ d₁` (`gaugeFixedOperator`), has dimension
at most `2 |D|` (`TauCeti.Vortex.finrank_le_two_mul_card_of_gaugeFixedOperator_eq_zero`). For a
vortex with the degree-`m` end framing `α(z) (z / |z|)⁻ᵐ → 1` the bound is `2m`
(`TauCeti.Vortex.finrank_le_two_mul_of_tendsto_sectionValue_mul_inv_pow`). Only the
holomorphicity rows of the vortex equation are used.

This is the upper bound in Taubes's identification of the kernel of `L_x` with the real tangent
space `ℂᵐ` of the divisor space `Sym^m ℂ`, following Samols. Write `δα` for the section variation
of `y` and `η = δα / α`, defined off the zeros of `α`. There the two `∂bar` rows of `L_x y = 0`
make `y` the logarithmic variation of `η` (`apply_eq_logVariation_div_apply`), so
`∂bar η = (y₀ + i y₁) / (2 i)` extends smoothly across the zeros. Subtracting the Cauchy
transform `ψ` of a cut-off copy of this datum leaves `η - ψ` holomorphic on a punctured disc
around each zero `a`. If `α = (w - a)ⁿ v` near `a` with `v a ≠ 0`, the function
`δα / v - (w - a)ⁿ ψ` is continuous at `a` and equals `(w - a)ⁿ (η - ψ)` off `a`, so it is
analytic at `a` by Riemann's removable singularity theorem. Its first `n` Taylor coefficients at
`a` are the coefficients of the principal part of the meromorphic function `η - ψ` at `a`. These
give a real-linear map from the kernel to `ℂ^|D|`. It is injective: if all principal parts vanish,
`η` extends to a `C²` function on the plane with `δα = α η`, and then `y = 0`
(`eq_zero_of_gaugeFixedOperator_eq_zero_of_sectionValue_eq_mul_of_tendsto`).

The covariant translations (`TauCeti.Analysis.PDE.Vortex.TranslationKernel`) show that the
kernel is nonzero once `α` has a zero. Equality with `2m`, which needs kernel elements with
prescribed principal parts, is not proved here.

## Main results

* `TauCeti.Vortex.finiteDimensional_of_gaugeFixedOperator_eq_zero` and
  `TauCeti.Vortex.finrank_le_two_mul_card_of_gaugeFixedOperator_eq_zero`: a space of `C²`
  square-integrable kernel elements is finite dimensional, of dimension at most `2 |D|`.
* `TauCeti.Vortex.finiteDimensional_of_tendsto_sectionValue_mul_inv_pow` and
  `TauCeti.Vortex.finrank_le_two_mul_of_tendsto_sectionValue_mul_inv_pow`: the same for a vortex
  framed in degree `m`, with bound `2m`.

## References

* T. M. Samols, *Vortex scattering*, Comm. Math. Phys. 145 (1992), 149–179.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

namespace TauCeti.Vortex

open Complex Filter MeasureTheory Set
open scoped Topology

/-- The datum `(y₀ + i y₁) / (2 i)` of a variation `y`. Off the zeros of a vortex section it is
`∂bar (δα / α)` for a kernel element `y` (`conjWirtingerDeriv_div_sectionValue`). -/
private noncomputable def dbarDatum (y : ℂ → EuclideanSpace ℝ (Fin 4)) (w : ℂ) : ℂ :=
  ((y w 0 : ℂ) + y w 1 * I) / (2 * I)

private theorem dbarDatum_add (y y' : ℂ → EuclideanSpace ℝ (Fin 4)) (w : ℂ) :
    dbarDatum (y + y') w = dbarDatum y w + dbarDatum y' w := by
  simp only [dbarDatum, Pi.add_apply, PiLp.add_apply, ofReal_add]
  ring

private theorem dbarDatum_smul (c : ℝ) (y : ℂ → EuclideanSpace ℝ (Fin 4)) (w : ℂ) :
    dbarDatum (c • y) w = c * dbarDatum y w := by
  simp only [dbarDatum, Pi.smul_apply, PiLp.smul_apply, smul_eq_mul, ofReal_mul]
  ring

private theorem contDiff_dbarDatum {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : ContDiff ℝ 2 y) :
    ContDiff ℝ 2 (dbarDatum y) := by
  have hi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ ((y w i : ℝ) : ℂ) :=
    ofRealCLM.contDiff.comp ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hy)
  exact ((hi 0).add ((hi 1).mul contDiff_const)).div_const _

/-- **`∂bar (δα / α)` off the zeros.** At a point where the holomorphicity rows of the vortex
equation hold and `α ≠ 0`, a variation `y` satisfying the two `∂bar` rows of `L_x y = 0` has
`∂bar (δα / α) = (y₀ + i y₁) / (2 i)`. -/
private theorem conjWirtingerDeriv_div_sectionValue {x y : ℂ → EuclideanSpace ℝ (Fin 4)} {z : ℂ}
    (hx : DifferentiableAt ℝ x z) (hy : DifferentiableAt ℝ y z) (hα : sectionValue x z ≠ 0)
    (h₁ : equation x z 1 = 0) (h₂ : equation x z 2 = 0)
    (hy₂ : gaugeFixedOperator x y z 2 = 0) (hy₃ : gaugeFixedOperator x y z 3 = 0) :
    conjWirtingerDeriv (fun w ↦ sectionValue y w / sectionValue x w) z 1 = dbarDatum y z := by
  have hη : DifferentiableAt ℝ (fun w ↦ sectionValue y w / sectionValue x w) z := by
    simp_rw [div_eq_mul_inv]
    exact (differentiableAt_sectionValue_of_differentiableAt hy).mul
      ((differentiableAt_sectionValue_of_differentiableAt hx).inv hα)
  have h := logVariation_zero_add_one_mul_I x hη
  rw [← apply_eq_logVariation_div_apply hx hy hα h₁ h₂ hy₂ hy₃] at h
  rw [dbarDatum, h, mul_div_cancel_left₀ _ (mul_ne_zero two_ne_zero I_ne_zero)]

/-- The cutoff around `a`, equal to one on the closed unit disc. -/
private noncomputable def cutoff (a : ℂ) : ContDiffBump a := ⟨1, 2, one_pos, one_lt_two⟩

/-- The Cauchy transform of the cut-off datum, `ψ = T (χ_a (y₀ + i y₁) / (2 i))`. It solves
`∂bar ψ = (y₀ + i y₁) / (2 i)` on the unit disc around `a`. -/
private noncomputable def localPotential (a : ℂ) (y : ℂ → EuclideanSpace ℝ (Fin 4)) : ℂ → ℂ :=
  cauchyTransform fun w ↦ (cutoff a w : ℂ) * dbarDatum y w

private theorem hasCompactSupport_cutoff_mul (a : ℂ) (f : ℂ → ℂ) :
    HasCompactSupport fun w ↦ (cutoff a w : ℂ) * f w :=
  ((cutoff a).hasCompactSupport.comp_left ofReal_zero).mul_right

private theorem contDiff_cutoff_mul (a : ℂ) {f : ℂ → ℂ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 2 fun w ↦ (cutoff a w : ℂ) * f w :=
  (ofRealCLM.contDiff.comp (cutoff a).contDiff).mul hf

private theorem contDiff_localPotential (a : ℂ) {y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hy : ContDiff ℝ 2 y) : ContDiff ℝ 2 (localPotential a y) :=
  (hasCompactSupport_cutoff_mul a _).contDiff_cauchyTransform
    (contDiff_cutoff_mul a (contDiff_dbarDatum hy))

private theorem eventually_conjWirtingerDeriv_localPotential (a : ℂ)
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : ContDiff ℝ 2 y) :
    ∀ᶠ w in 𝓝 a, conjWirtingerDeriv (localPotential a y) w 1 = dbarDatum y w := by
  filter_upwards [Metric.closedBall_mem_nhds a one_pos] with w hw
  rw [localPotential, (hasCompactSupport_cutoff_mul a _).conjWirtingerDeriv_cauchyTransform
    ((contDiff_cutoff_mul a (contDiff_dbarDatum hy)).of_le (by norm_num)) w,
    (cutoff a).one_of_mem_closedBall hw, ofReal_one, one_mul]

private theorem localPotential_add (a : ℂ) {y y' : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hy : Continuous y) (hy' : Continuous y') :
    localPotential a (y + y') = localPotential a y + localPotential a y' := by
  have hc {z : ℂ → EuclideanSpace ℝ (Fin 4)} (hz : Continuous z) :
      Continuous fun w ↦ (cutoff a w : ℂ) * dbarDatum z w := by
    have hi (i : Fin 4) : Continuous fun w ↦ ((z w i : ℝ) : ℂ) :=
      continuous_ofReal.comp ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp hz)
    exact (continuous_ofReal.comp (cutoff a).continuous).mul
      (((hi 0).add ((hi 1).mul continuous_const)).div_const _)
  rw [localPotential, localPotential, localPotential, ← cauchyTransform_add (hc hy)
    (hasCompactSupport_cutoff_mul a _) (hc hy') (hasCompactSupport_cutoff_mul a _)]
  congr 1
  funext w
  simp only [Pi.add_apply, dbarDatum_add]
  ring

private theorem localPotential_smul (a : ℂ) (c : ℝ) (y : ℂ → EuclideanSpace ℝ (Fin 4)) :
    localPotential a (c • y) = c • localPotential a y := by
  rw [localPotential, localPotential, ← cauchyTransform_smul]
  congr 1
  funext w
  simp only [Pi.smul_apply, dbarDatum_smul, real_smul]
  ring

/-- The regularized quotient `δα / v - (w - a)ⁿ ψ` at a zero `a` of `α = (w - a)ⁿ v`. -/
private noncomputable def regularizedQuotient (v ψ : ℂ → ℂ) (n : ℕ) (a : ℂ)
    (y : ℂ → EuclideanSpace ℝ (Fin 4)) (w : ℂ) : ℂ :=
  sectionValue y w / v w - (w - a) ^ n * ψ w

/-- **The regularized quotient is analytic at the zero.** Let `x` have vanishing holomorphicity
rows and section `α = (w - a)ⁿ v` near `a`, with `v` continuous at `a` and `v a ≠ 0`. Let `y`
solve `L_x y = 0`, and let `ψ` satisfy `∂bar ψ = (y₀ + i y₁) / (2 i)` near `a`. Then
`δα / v - (w - a)ⁿ ψ` is analytic at `a`: off `a` it is `(w - a)ⁿ (δα / α - ψ)`, which is
holomorphic, and it is continuous at `a`. -/
private theorem analyticAt_regularizedQuotient {x y : ℂ → EuclideanSpace ℝ (Fin 4)}
    {v ψ : ℂ → ℂ} {a : ℂ} {n : ℕ} (hx : Differentiable ℝ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0) (hy : Differentiable ℝ y)
    (hker : ∀ w, gaugeFixedOperator x y w = 0) (hv : ContinuousAt v a) (hv₀ : v a ≠ 0)
    (hαv : ∀ᶠ w in 𝓝 a, sectionValue x w = (w - a) ^ n * v w) (hψ : Differentiable ℝ ψ)
    (hψy : ∀ᶠ w in 𝓝 a, conjWirtingerDeriv ψ w 1 = dbarDatum y w) :
    AnalyticAt ℂ (regularizedQuotient v ψ n a y) a := by
  have hdy (w : ℂ) := differentiableAt_sectionValue_of_differentiableAt (hy w)
  have hdx (w : ℂ) := differentiableAt_sectionValue_of_differentiableAt (hx w)
  refine analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_
    (((hdy a).continuousAt.div hv hv₀).sub
      (((continuousAt_id.sub continuousAt_const).pow n).mul (hψ a).continuousAt))
  have hP := ((hαv.and (hv.eventually_ne hv₀)).and hψy).eventually_nhds
  filter_upwards [nhdsWithin_le_nhds hP, self_mem_nhdsWithin] with w hw hwa
  obtain ⟨⟨hαw, hvw⟩, hψw⟩ := hw.self_of_nhds
  have hpow (u : ℂ) (hu : u ≠ a) : (u - a) ^ n ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hu)
  have hαw₀ : sectionValue x w ≠ 0 := by
    rw [hαw]
    exact mul_ne_zero (hpow w hwa) hvw
  -- Near `w ≠ a` the regularized quotient is `(u - a)ⁿ (δα / α - ψ)`.
  have heq : regularizedQuotient v ψ n a y =ᶠ[𝓝 w]
      fun u ↦ (u - a) ^ n * (sectionValue y u / sectionValue x u - ψ u) := by
    filter_upwards [hw, eventually_ne_nhds hwa] with u hu hua
    obtain ⟨⟨hαu, hvu⟩, -⟩ := hu
    have := hpow u hua
    rw [regularizedQuotient, hαu]
    field_simp
  -- and `δα / α - ψ` is holomorphic at `w`, since its `∂bar` vanishes.
  have hη : DifferentiableAt ℝ (fun u ↦ sectionValue y u / sectionValue x u) w := by
    simp_rw [div_eq_mul_inv]
    exact (hdy w).mul ((hdx w).inv hαw₀)
  have hd : DifferentiableAt ℂ (fun u ↦ sectionValue y u / sectionValue x u - ψ u) w := by
    refine (differentiableAt_iff_conjWirtingerDeriv_apply_one_eq_zero (hη.sub (hψ w))).mpr ?_
    rw [conjWirtingerDeriv_sub hη (hψ w), sub_apply,
      conjWirtingerDeriv_div_sectionValue (hx w) (hy w) hαw₀ (hhol w).1 (hhol w).2
        (by simp [hker w]) (by simp [hker w]), hψw, sub_self]
  exact ((((differentiableAt_id.sub_const a).pow n).mul hd)).congr_of_eventuallyEq heq

/-- **Vanishing principal part.** If the first `n` derivatives at `a` of the analytic regularized
quotient vanish, then `δα = α (ψ + G)` near `a` for a function `G` analytic at `a`. -/
private theorem exists_analyticAt_sectionValue_eq_mul {x y : ℂ → EuclideanSpace ℝ (Fin 4)}
    {v ψ : ℂ → ℂ} {a : ℂ} {n : ℕ} (hv : ∀ᶠ w in 𝓝 a, v w ≠ 0)
    (hαv : ∀ᶠ w in 𝓝 a, sectionValue x w = (w - a) ^ n * v w)
    (hA : AnalyticAt ℂ (regularizedQuotient v ψ n a y) a)
    (hj : ∀ j < n, iteratedDeriv j (regularizedQuotient v ψ n a y) a = 0) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G a ∧
      ∀ᶠ w in 𝓝 a, sectionValue y w = sectionValue x w * (ψ w + G w) := by
  obtain ⟨G, hG, hfG⟩ := (natCast_le_analyticOrderAt hA).mp
    ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hA).mpr hj)
  refine ⟨G, hG, ?_⟩
  filter_upwards [hfG, hv, hαv] with w hw hvw hαw
  rw [regularizedQuotient, smul_eq_mul] at hw
  have h : sectionValue y w / v w = (w - a) ^ n * (ψ w + G w) := by linear_combination hw
  rw [div_eq_iff hvw] at h
  rw [hαw, h]
  ring

variable {μ : Measure ℂ} [μ.IsAddHaarMeasure] {x : ℂ → EuclideanSpace ℝ (Fin 4)}
  {D : Multiset ℂ} {V : Submodule ℝ (ℂ → EuclideanSpace ℝ (Fin 4))}

/-- **A kernel element with locally regular `δα / α` vanishes.** Let `x` be a `C²` field with
vanishing holomorphicity rows, `|α|² → 1` at infinity and zero divisor `D`, and let `y` be a `C²`
square-integrable solution of `L_x y = 0`. If near each zero `a` of `α`, `δα = α η_a` for a
function `η_a` that is `C²` at `a`, then `y = 0`: the quotient `δα / α` then extends to a `C²`
function `η` on the plane with `δα = α η`. -/
private theorem eq_zero_of_forall_mem_eventually_sectionValue_eq_mul
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ 2 x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) (hy : ContDiff ℝ 2 y)
    (hy₂ : MemLp y 2 μ) (hker : ∀ w, gaugeFixedOperator x y w = 0)
    (hloc : ∀ a ∈ D, ∃ ηa : ℂ → ℂ, ContDiffAt ℝ 2 ηa a ∧
      ∀ᶠ w in 𝓝 a, sectionValue y w = sectionValue x w * ηa w) : y = 0 := by
  classical
  choose ηa hηa hηaeq using hloc
  have hαne (u : ℂ) : sectionValue x u ≠ 0 ↔ u ∉ D :=
    hD.eq_zero_iff.symm.trans Multiset.count_eq_zero
  let η : ℂ → ℂ := fun w ↦
    if hw : w ∈ D then ηa w hw w else sectionValue y w / sectionValue x w
  have hyη (w : ℂ) : sectionValue y w = sectionValue x w * η w := by
    by_cases hw : w ∈ D
    · simpa [η, hw] using (hηaeq w hw).self_of_nhds
    · simp only [η, hw, dite_false]
      rw [mul_div_cancel₀ _ ((hαne w).mpr hw)]
  have hη : ContDiff ℝ 2 η := by
    refine contDiff_iff_contDiffAt.mpr fun z ↦ ?_
    by_cases hz : z ∈ D
    · -- Near a zero `z`, `η = η_z`, since the other zeros are at positive distance.
      have hiso : ∀ᶠ u in 𝓝 z, u ∈ D → u = z := by
        filter_upwards [(D.toFinset.erase z).isClosed.isOpen_compl.mem_nhds (by simp)]
          with u hu huD
        by_contra hne
        exact hu (by simp [hne, huD])
      have heq : η =ᶠ[𝓝 z] ηa z hz := by
        filter_upwards [hiso, hηaeq z hz] with u hu hηu
        by_cases huD : u ∈ D
        · obtain rfl := hu huD
          simp [η, huD]
        · simp only [η, huD, dite_false]
          rw [hηu, mul_div_cancel_left₀ _ ((hαne u).mpr huD)]
      exact (hηa z hz).congr_of_eventuallyEq heq
    · -- Off the zeros, `η = δα / α`.
      have hdx := contDiff_sectionValue (n := 2)
        ((EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 4)).contDiff.comp hx :)
        ((EuclideanSpace.proj (𝕜 := ℝ) (3 : Fin 4)).contDiff.comp hx :)
      have hdy := contDiff_sectionValue (n := 2)
        ((EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 4)).contDiff.comp hy :)
        ((EuclideanSpace.proj (𝕜 := ℝ) (3 : Fin 4)).contDiff.comp hy :)
      have heq : η =ᶠ[𝓝 z] fun u ↦ sectionValue y u * (sectionValue x u)⁻¹ := by
        filter_upwards [D.toFinset.isClosed.isOpen_compl.mem_nhds (by simpa using hz)]
          with u hu
        have huD : u ∉ D := by simpa using hu
        simp [η, huD, div_eq_mul_inv]
      exact (hdy.contDiffAt.mul (hdx.contDiffAt.inv ((hαne z).mpr hz))).congr_of_eventuallyEq heq
  exact eq_zero_of_gaugeFixedOperator_eq_zero_of_sectionValue_eq_mul_of_tendsto
    (hx.of_le (by norm_num)) hhol hlim hy.continuous hy₂ hker hη hyη

/-- **The principal-part map.** For a space `V` of `C²` square-integrable kernel elements, the
principal parts of `δα / α - ψ_a` at the zeros `a` of `α` give an injective real-linear map from
`V` to `ℂ^|D|`, indexed by the zeros `a` and orders `j < D(a)`. -/
private theorem exists_injective_linearMap (hx : ContDiff ℝ 2 x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z)
    (hV : ∀ y ∈ V, ContDiff ℝ 2 y ∧ MemLp y 2 μ ∧ ∀ w, gaugeFixedOperator x y w = 0) :
    ∃ Φ : V →ₗ[ℝ] (Σ a : D.toFinset, Fin (D.count (a : ℂ))) → ℂ, Function.Injective Φ := by
  classical
  choose v hvc hv₀ hαv using isZeroMultiplicity_iff.mp hD
  have hxd : Differentiable ℝ x := hx.differentiable (by simp)
  have hA (y : ℂ → EuclideanSpace ℝ (Fin 4)) (hy : y ∈ V) (a : ℂ) :
      AnalyticAt ℂ (regularizedQuotient (v a) (localPotential a y) (D.count a) a y) a :=
    analyticAt_regularizedQuotient hxd hhol ((hV y hy).1.differentiable (by simp))
      (hV y hy).2.2 (hvc a) (hv₀ a) (hαv a)
      ((contDiff_localPotential a (hV y hy).1).differentiable (by simp))
      (eventually_conjWirtingerDeriv_localPotential a (hV y hy).1)
  have hadd (a : ℂ) {y y' : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : Continuous y)
      (hy' : Continuous y') :
      regularizedQuotient (v a) (localPotential a (y + y')) (D.count a) a (y + y') =
        regularizedQuotient (v a) (localPotential a y) (D.count a) a y +
          regularizedQuotient (v a) (localPotential a y') (D.count a) a y' := by
    funext w
    simp only [regularizedQuotient, localPotential_add a hy hy', Pi.add_apply, sectionValue_add]
    ring
  have hsmul (a : ℂ) (c : ℝ) (y : ℂ → EuclideanSpace ℝ (Fin 4)) :
      regularizedQuotient (v a) (localPotential a (c • y)) (D.count a) a (c • y) =
        (c : ℂ) • regularizedQuotient (v a) (localPotential a y) (D.count a) a y := by
    funext w
    simp only [regularizedQuotient, localPotential_smul, Pi.smul_apply, sectionValue_smul,
      real_smul, smul_eq_mul]
    ring
  let Φ : V →ₗ[ℝ] (Σ a : D.toFinset, Fin (D.count (a : ℂ))) → ℂ :=
    { toFun := fun y p ↦ iteratedDeriv p.2
        (regularizedQuotient (v p.1) (localPotential p.1 y) (D.count (p.1 : ℂ)) p.1 y) p.1
      map_add' := fun y y' ↦ by
        funext p
        simp only [Submodule.coe_add, Pi.add_apply]
        rw [hadd p.1 (hV y y.2).1.continuous (hV y' y'.2).1.continuous,
          iteratedDeriv_add (hA y y.2 p.1).contDiffAt (hA y' y'.2 p.1).contDiffAt]
      map_smul' := fun c y ↦ by
        funext p
        simp only [Submodule.coe_smul, RingHom.id_apply, Pi.smul_apply]
        rw [hsmul p.1 c y, iteratedDeriv_const_smul (hA y y.2 p.1).contDiffAt, real_smul,
          smul_eq_mul] }
  refine ⟨Φ, (injective_iff_map_eq_zero Φ).mpr fun y hΦ ↦ ?_⟩
  obtain ⟨hy, hy₂, hker⟩ := hV y y.2
  -- At each zero `a`, the vanishing principal part gives `δα = α (ψ_a + G_a)` near `a`.
  refine Subtype.ext (eq_zero_of_forall_mem_eventually_sectionValue_eq_mul hx hhol hlim hD hy hy₂
    hker fun a ha ↦ ?_)
  obtain ⟨G, hG, hGeq⟩ := exists_analyticAt_sectionValue_eq_mul
    ((hvc a).eventually_ne (hv₀ a)) (hαv a) (hA y y.2 a) fun j hj ↦ by
      simpa only [Φ, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] using
        congrFun hΦ ⟨⟨a, Multiset.mem_toFinset.mpr ha⟩, ⟨j, hj⟩⟩
  exact ⟨fun w ↦ localPotential a y w + G w,
    (contDiff_localPotential a hy).contDiffAt.add (hG.contDiffAt.restrict_scalars ℝ), hGeq⟩

/-- **Kernel elements of the gauge-fixed operator form a finite-dimensional space.** Let `x` be a
`C²` field with vanishing holomorphicity rows and `|α|² → 1` at infinity, whose section has zero
divisor `D`. Then every real vector space of `C²` square-integrable solutions of `L_x y = 0` is
finite dimensional. -/
theorem finiteDimensional_of_gaugeFixedOperator_eq_zero (hx : ContDiff ℝ 2 x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z)
    (hV : ∀ y ∈ V, ContDiff ℝ 2 y ∧ MemLp y 2 μ ∧ ∀ w, gaugeFixedOperator x y w = 0) :
    FiniteDimensional ℝ V :=
  let ⟨Φ, hΦ⟩ := exists_injective_linearMap hx hhol hlim hD hV
  FiniteDimensional.of_injective Φ hΦ

/-- **The kernel of the gauge-fixed operator at a vortex has dimension at most `2 |D|`.** Let `x`
be a `C²` field with vanishing holomorphicity rows and `|α|² → 1` at infinity, whose section has
zero divisor `D`. Then every real vector space of `C²` square-integrable solutions of `L_x y = 0`
has dimension at most twice the degree of `D`. -/
theorem finrank_le_two_mul_card_of_gaugeFixedOperator_eq_zero (hx : ContDiff ℝ 2 x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z)
    (hV : ∀ y ∈ V, ContDiff ℝ 2 y ∧ MemLp y 2 μ ∧ ∀ w, gaugeFixedOperator x y w = 0) :
    Module.finrank ℝ V ≤ 2 * Multiset.card D := by
  obtain ⟨Φ, hΦ⟩ := exists_injective_linearMap hx hhol hlim hD hV
  refine (LinearMap.finrank_le_finrank_of_injective hΦ).trans_eq ?_
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_sigma,
    Complex.finrank_real_complex, smul_eq_mul, mul_comm]
  simp only [Fintype.card_fin, Finset.univ_eq_attach]
  rw [Finset.sum_attach D.toFinset fun a ↦ D.count a, Multiset.toFinset_sum_count_eq]

/-- The divisor of a framed degree-`m` field: a `C²` field with vanishing holomorphicity rows and
end framing `α(z) (z / |z|)⁻ᵐ → 1` has a zero divisor of degree `m`. -/
private theorem exists_isZeroMultiplicity_of_tendsto_sectionValue_mul_inv_pow {m : ℕ}
    (hx : ContDiff ℝ 2 x) (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    ∃ D : Multiset ℂ, Multiset.card D = m ∧
      IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z := by
  have hi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ x w i :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hx
  obtain ⟨D, hD⟩ := exists_sym_sectionValue_eq_pow_count_mul (k := 2) (by norm_num) (hi 0) (hi 1)
    ((hi 2).differentiable (by norm_num)) ((hi 3).differentiable (by norm_num)) hhol hframe
  exact ⟨D, D.2, isZeroMultiplicity_iff.2 fun z ↦ (hD z).imp fun _ hv ↦ ⟨hv.1.continuousAt, hv.2⟩⟩

/-- **Kernel elements at a framed vortex form a finite-dimensional space.** At a `C²` field with
vanishing holomorphicity rows and the degree-`m` end framing `α(z) (z / |z|)⁻ᵐ → 1`, every real
vector space of `C²` square-integrable solutions of `L_x y = 0` is finite dimensional. -/
theorem finiteDimensional_of_tendsto_sectionValue_mul_inv_pow {m : ℕ} (hx : ContDiff ℝ 2 x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    (hV : ∀ y ∈ V, ContDiff ℝ 2 y ∧ MemLp y 2 μ ∧ ∀ w, gaugeFixedOperator x y w = 0) :
    FiniteDimensional ℝ V :=
  let ⟨_, _, hD⟩ := exists_isZeroMultiplicity_of_tendsto_sectionValue_mul_inv_pow hx hhol hframe
  finiteDimensional_of_gaugeFixedOperator_eq_zero hx hhol
    (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe) hD hV

/-- **The kernel of the gauge-fixed operator at a framed vortex has dimension at most `2m`.** At a
`C²` field with vanishing holomorphicity rows and the degree-`m` end framing
`α(z) (z / |z|)⁻ᵐ → 1`, every real vector space of `C²` square-integrable solutions of
`L_x y = 0` has dimension at most `2m`, the real dimension of the divisor space `Sym^m ℂ`. -/
theorem finrank_le_two_mul_of_tendsto_sectionValue_mul_inv_pow {m : ℕ} (hx : ContDiff ℝ 2 x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    (hV : ∀ y ∈ V, ContDiff ℝ 2 y ∧ MemLp y 2 μ ∧ ∀ w, gaugeFixedOperator x y w = 0) :
    Module.finrank ℝ V ≤ 2 * m := by
  obtain ⟨D, rfl, hD⟩ :=
    exists_isZeroMultiplicity_of_tendsto_sectionValue_mul_inv_pow hx hhol hframe
  exact finrank_le_two_mul_card_of_gaugeFixedOperator_eq_zero hx hhol
    (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe) hD hV

end TauCeti.Vortex
