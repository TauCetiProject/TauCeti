/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.LogVariation
public import TauCeti.Analysis.PDE.Vortex.PrincipalPart
public import TauCeti.Analysis.PDE.Vortex.TranslationKernel
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Complex.Wirtinger.DolbeaultLemma
import TauCeti.Analysis.PDE.Vortex.KernelExistence

/-!
# The dimension of the kernel of the gauge-fixed operator at a plane vortex

Let `x` be a field whose holomorphicity rows `∂bar_a α = 0` vanish, with `|α| → 1` at infinity,
and let the zeros of its section `α`, counted with multiplicity, form the effective divisor `D`.
This file identifies `gaugeFixedKernel x` linearly with the space of principal parts at `D`, of real
dimension `2 |D|` as for the tangent space of `Sym^m ℂ`, following Samols. At a smooth field it
proves that every kernel element in `gaugeFixedKernel x` is smooth and computes the exact real
dimension `2 |D|` (`TauCeti.Vortex.finrank_gaugeFixedKernel_eq_two_mul_card`), hence `2 m` under the
degree-`m` end framing `α(z) (z / |z|)⁻ᵐ → 1`
(`TauCeti.Vortex.finrank_gaugeFixedKernel_eq_two_mul`).

* **Upper bound and degree zero (`C²` fields).** The last two rows of `L_x y = 0` are the
  holomorphicity rows of the linearized equation, so the section variation decomposes as
  `δα = α G + e^ν H` with `H` entire, and the derivatives of `H` at the zeros of `α` record the
  principal parts of `δα / α` (`TauCeti.Vortex.principalPartMap`). This real-linear map to `ℂ^|D|`
  is injective (`TauCeti.Vortex.principalPartMap_injective`) by the vanishing theorem
  `TauCeti.Vortex.eq_zero_of_gaugeFixedOperator_eq_zero_of_sectionValue_eq_mul_of_tendsto`, giving
  the upper bounds `2 |D|` and `2 m`. In particular, when `α` has no zeros (for instance in degree
  zero), `gaugeFixedKernel x = ⊥`
  (`TauCeti.Vortex.gaugeFixedKernel_eq_bot_of_forall_sectionValue_ne_zero`,
  `TauCeti.Vortex.gaugeFixedKernel_eq_bot`).
* **Covariant translations and degree one (`C³` vortices).** When the section of a `C³` vortex has a
  zero, the covariant translations `y_v = (ι_v F_a, ∇_v α)` span a two-dimensional subspace of
  `gaugeFixedKernel x` (`TauCeti.Vortex.two_le_finrank_gaugeFixedKernel_of_sectionValue_eq_zero`,
  `TauCeti.Vortex.two_le_finrank_gaugeFixedKernel`). When `|D| = 1` (in particular in degree one),
  every kernel element is a covariant translation and the kernel has real dimension two
  (`TauCeti.Vortex.range_covariantTranslationLinearMap_of_card_eq_one`,
  `TauCeti.Vortex.range_covariantTranslationLinearMap`).
* **Surjectivity and exact dimension (`C^∞` fields).** At each zero `z` of multiplicity `n` of
  `α = e^ν f`, writing `f(w) = (w - z)ⁿ g(w)` with `g` analytic and `g(z) ≠ 0`, the smooth pole
  kernel element of
  `TauCeti.Vortex.exists_gaugeFixedOperator_eq_zero_sectionValue_eq_mul_div_pow_add`
  with pole `c / (w - z)^(n - m')` has local holomorphic numerator `c (w - z)^m' g(w)` at `z` (of
  analytic order `m'`) and vanishing principal parts at all other zeros. Triangular elimination in
  decreasing jet order shows that `principalPartMap` is already surjective on smooth `L²` kernel
  elements (`TauCeti.Vortex.principalPartMap_surjective`). Together with injectivity on
  `gaugeFixedKernel x`, this forces every `y ∈ gaugeFixedKernel x` to be smooth
  (`TauCeti.Vortex.contDiff_of_mem_gaugeFixedKernel`) and yields the linear isomorphism
  `TauCeti.Vortex.gaugeFixedKernelPrincipalPartEquiv` onto `Multiset.ToType D → ℂ`.

The comparison with the weak `L²` kernel, and membership of kernel elements in every `H^s`, are
proved in `TauCeti.Analysis.PDE.Vortex.EllipticRegularity`.

## Main results

* `TauCeti.Vortex.finiteDimensional_of_gaugeFixedOperator_eq_zero` and
  `TauCeti.Vortex.finrank_le_two_mul_card_of_gaugeFixedOperator_eq_zero`: a space of `C²`
  square-integrable kernel elements is finite dimensional, of dimension at most `2 |D|`.
* `TauCeti.Vortex.finiteDimensional_of_tendsto_sectionValue_mul_inv_pow` and
  `TauCeti.Vortex.finrank_le_two_mul_of_tendsto_sectionValue_mul_inv_pow`: the same for a vortex
  framed in degree `m`, with bound `2m`.
* `TauCeti.Vortex.gaugeFixedKernel_eq_bot_of_forall_sectionValue_ne_zero` and
  `TauCeti.Vortex.gaugeFixedKernel_eq_bot`: the kernel vanishes when the section has no zeros,
  in particular in degree zero.
* `TauCeti.Vortex.two_le_finrank_gaugeFixedKernel_of_sectionValue_eq_zero` and
  `TauCeti.Vortex.two_le_finrank_gaugeFixedKernel`: `2 ≤ dim_ℝ ker L_x` when the section has a
  zero, in particular at a framed vortex of positive degree.
* `TauCeti.Vortex.range_covariantTranslationLinearMap_of_card_eq_one`,
  `TauCeti.Vortex.finrank_gaugeFixedKernel_eq_two_of_card_eq_one`,
  `TauCeti.Vortex.range_covariantTranslationLinearMap` and
  `TauCeti.Vortex.finrank_gaugeFixedKernel_eq_two`: for a single zero, in particular in degree
  one, the kernel consists exactly of the covariant translations and has real dimension two.
* `TauCeti.Vortex.principalPartMap_surjective`, `TauCeti.Vortex.principalPartMap_bijective`, and
  `TauCeti.Vortex.gaugeFixedKernelPrincipalPartEquiv`: surjectivity and bijectivity of the
  principal-part map, identifying `gaugeFixedKernel x` linearly over `ℝ` with
  `Multiset.ToType D → ℂ`.
* `TauCeti.Vortex.contDiff_of_mem_gaugeFixedKernel`: every `C²` square-integrable kernel element at
  a smooth field with `∂bar_a α = 0` and `|α|² → 1` is `C^∞`.
* `TauCeti.Vortex.finrank_gaugeFixedKernel_eq_two_mul_card` and
  `TauCeti.Vortex.finrank_gaugeFixedKernel_eq_two_mul`: exact real dimension `2 |D|` and `2 m`.

## References

* T. M. Samols, *Vortex scattering*, Comm. Math. Phys. 145 (1992), 149–179.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

namespace TauCeti.Vortex

open Complex Filter MeasureTheory Module
open scoped ContDiff Topology

variable {μ : Measure ℂ} [μ.IsAddHaarMeasure] {x : ℂ → EuclideanSpace ℝ (Fin 4)}
  {D : Multiset ℂ} {V : Submodule ℝ (ℂ → EuclideanSpace ℝ (Fin 4))}

omit [μ.IsAddHaarMeasure] in
/-- A `C²` kernel element of `L_x` has `C²` connection components and differentiable section
components, and satisfies the holomorphicity rows of the linearized equation, which are the last
two rows of `L_x y = 0`. -/
private theorem forall_mem_linearizedEquation_eq_zero
    (hV : ∀ y ∈ V, ContDiff ℝ 2 y ∧ MemLp y 2 μ ∧ ∀ w, gaugeFixedOperator x y w = 0) :
    ∀ y ∈ V, ContDiff ℝ 2 (fun w ↦ y w 0) ∧ ContDiff ℝ 2 (fun w ↦ y w 1) ∧
      Differentiable ℝ (fun w ↦ y w 2) ∧ Differentiable ℝ (fun w ↦ y w 3) ∧
      ∀ w, linearizedEquation x y w 1 = 0 ∧ linearizedEquation x y w 2 = 0 := by
  intro y hy
  obtain ⟨hy, -, hker⟩ := hV y hy
  have hi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ y w i :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hy
  refine ⟨hi 0, hi 1, (hi 2).differentiable (by norm_num), (hi 3).differentiable (by norm_num),
    fun w ↦ ⟨?_, ?_⟩⟩
  · rw [← gaugeFixedOperator_apply_two, hker w, PiLp.zero_apply]
  · rw [← gaugeFixedOperator_apply_three, hker w, PiLp.zero_apply]

/-- **The principal-part map on the kernel.** For a space `V` of `C²` square-integrable kernel
elements, the principal-part map `TauCeti.Vortex.principalPartMap` gives an injective real-linear
map from `V` to `ℂ^|D|`. -/
private theorem exists_injective_linearMap (hx : ContDiff ℝ 2 x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z)
    (hV : ∀ y ∈ V, ContDiff ℝ 2 y ∧ MemLp y 2 μ ∧ ∀ w, gaugeFixedOperator x y w = 0) :
    ∃ Φ : V →ₗ[ℝ] Multiset.ToType D → ℂ, Function.Injective Φ := by
  have hi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ x w i :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hx
  have hp := (hi 2).differentiable (by norm_num)
  have hq := (hi 3).differentiable (by norm_num)
  have hlin := forall_mem_linearizedEquation_eq_zero hV
  -- An integrating factor `ν` with `∂bar ν = (b₂ - i b₁) / 2`.
  obtain ⟨ν, hν, hνeq⟩ :=
    exists_contDiff_conjWirtingerDeriv_apply_one_eq (by norm_num) (contDiff_connectionCoeff
      (hi 0) (hi 1))
  have hdec (y) (hy : y ∈ V) : ∃ G : ℂ → ℂ, Continuous G ∧ ∃ H : ℂ → ℂ, Differentiable ℂ H ∧
      ∀ w, sectionValue y w = sectionValue x w * G w + exp (ν w) * H w := by
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hlin y hy
    obtain ⟨G, hG, H, hH, hGH⟩ := exists_sectionValue_eq_mul_add_exp_mul (k := 2) (by norm_num)
      hp hq hhol (hν.differentiable (by norm_num)) hνeq h₁ h₂ h₃ h₄ h₅
    exact ⟨G, hG.continuous, H, hH, hGH⟩
  exact ⟨principalPartMap hD hν.continuous hdec,
    principalPartMap_injective (k := 2) (by norm_num) (hi 0) (hi 1) hp hq hhol hD hν hνeq hlin hdec
      fun y hy η hη hyη ↦ eq_zero_of_gaugeFixedOperator_eq_zero_of_sectionValue_eq_mul_of_tendsto
        (hx.of_le (by norm_num)) hhol hlim (hV y hy).1.continuous (hV y hy).2.1 (hV y hy).2.2 hη
        hyη⟩

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
  rw [Module.finrank_pi_fintype, Finset.sum_const, Complex.finrank_real_complex, smul_eq_mul,
    Finset.card_univ, Multiset.card_coe, mul_comm]

/-- **Kernel elements at a framed vortex form a finite-dimensional space.** At a `C²` field with
vanishing holomorphicity rows and the degree-`m` end framing `α(z) (z / |z|)⁻ᵐ → 1`, every real
vector space of `C²` square-integrable solutions of `L_x y = 0` is finite dimensional. -/
theorem finiteDimensional_of_tendsto_sectionValue_mul_inv_pow {m : ℕ} (hx : ContDiff ℝ 2 x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    (hV : ∀ y ∈ V, ContDiff ℝ 2 y ∧ MemLp y 2 μ ∧ ∀ w, gaugeFixedOperator x y w = 0) :
    FiniteDimensional ℝ V := by
  have hi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ x w i :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hx
  exact finiteDimensional_of_forall_sectionValue_eq_mul_eq_zero (k := 2) (by norm_num) (hi 0)
    (hi 1) ((hi 2).differentiable (by norm_num)) ((hi 3).differentiable (by norm_num)) hhol hframe
    (forall_mem_linearizedEquation_eq_zero hV) fun y hy η hη hyη ↦
      eq_zero_of_gaugeFixedOperator_eq_zero_of_sectionValue_eq_mul_of_tendsto
        (hx.of_le (by norm_num)) hhol (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe)
        (hV y hy).1.continuous (hV y hy).2.1 (hV y hy).2.2 hη hyη

/-- **The kernel of the gauge-fixed operator at a framed vortex has dimension at most `2m`.** At a
`C²` field with vanishing holomorphicity rows and the degree-`m` end framing
`α(z) (z / |z|)⁻ᵐ → 1`, every real vector space of `C²` square-integrable solutions of
`L_x y = 0` has dimension at most `2m`, the real dimension of the divisor space `Sym^m ℂ`. -/
theorem finrank_le_two_mul_of_tendsto_sectionValue_mul_inv_pow {m : ℕ} (hx : ContDiff ℝ 2 x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    (hV : ∀ y ∈ V, ContDiff ℝ 2 y ∧ MemLp y 2 μ ∧ ∀ w, gaugeFixedOperator x y w = 0) :
    Module.finrank ℝ V ≤ 2 * m := by
  have hi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ x w i :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hx
  exact finrank_le_two_mul_of_forall_sectionValue_eq_mul_eq_zero (k := 2) (by norm_num) (hi 0)
    (hi 1) ((hi 2).differentiable (by norm_num)) ((hi 3).differentiable (by norm_num)) hhol hframe
    (forall_mem_linearizedEquation_eq_zero hV) fun y hy η hη hyη ↦
      eq_zero_of_gaugeFixedOperator_eq_zero_of_sectionValue_eq_mul_of_tendsto
        (hx.of_le (by norm_num)) hhol (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe)
        (hV y hy).1.continuous (hV y hy).2.1 (hV y hy).2.2 hη hyη

/-! ### The kernel in degree zero -/

/-- **The kernel of `L_x` vanishes when the section has no zeros.** At a `C²` field satisfying
the holomorphicity rows of the vortex equation whose section has no zeros and modulus tending to
one at infinity, the only square-integrable `C²` solution of `L_x y = 0` is zero. -/
theorem gaugeFixedKernel_eq_bot_of_forall_sectionValue_ne_zero (hx : ContDiff ℝ 2 x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hne : ∀ z, sectionValue x z ≠ 0) :
    gaugeFixedKernel x = ⊥ := by
  have hD : IsZeroMultiplicity (sectionValue x) fun z ↦ (0 : Multiset ℂ).count z := by
    simpa [Pi.zero_def] using isZeroMultiplicity_zero_iff.2 ⟨(contDiff_sectionValue
      (contDiff_euclidean.mp hx 2) (contDiff_euclidean.mp hx 3)).continuous, hne⟩
  have hV (y : ℂ → EuclideanSpace ℝ (Fin 4)) (hy : y ∈ gaugeFixedKernel x) :=
    mem_gaugeFixedKernel.1 hy
  have := finiteDimensional_of_gaugeFixedOperator_eq_zero hx hhol hlim hD hV
  exact Submodule.finrank_eq_zero.1 (Nat.le_zero.1 (by
    simpa using finrank_le_two_mul_card_of_gaugeFixedOperator_eq_zero hx hhol hlim hD hV))

/-- **The kernel of `L_x` vanishes in degree zero.** At a `C²` field satisfying the holomorphicity
rows of the vortex equation whose section tends to one at infinity, the only square-integrable
`C²` solution of `L_x y = 0` is zero. -/
theorem gaugeFixedKernel_eq_bot (hx : ContDiff ℝ 2 x)
    (hhol : ∀ z, equation x z 1 = 0 ∧ equation x z 2 = 0)
    (hframe : Tendsto (sectionValue x) (cocompact ℂ) (𝓝 1)) :
    gaugeFixedKernel x = ⊥ := by
  have hframe₀ : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ 0)⁻¹) (cocompact ℂ)
      (𝓝 1) := by
    simpa using hframe
  have := finiteDimensional_gaugeFixedKernel hx hhol hframe₀
  exact Submodule.finrank_eq_zero.1
    (Nat.le_zero.1 (finrank_gaugeFixedKernel_le hx hhol hframe₀))

/-! ### The lower bound from covariant translations -/

section Translations

variable (hx : ContDiff ℝ 3 x) (hsol : ∀ z, equation x z = 0)

include hx hsol

/-- **The kernel of `L_x` has real dimension at least two once the section has a zero.** At a
`C³` vortex whose section has modulus tending to one at infinity, zero divisor `D` and a zero
`z₀`, the covariant translations span a two-dimensional subspace of `gaugeFixedKernel x`. -/
theorem two_le_finrank_gaugeFixedKernel_of_sectionValue_eq_zero
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) {z₀ : ℂ}
    (hz₀ : sectionValue x z₀ = 0) :
    2 ≤ finrank ℝ (gaugeFixedKernel x) := by
  have hdx (i : Fin 4) : Differentiable ℝ fun w ↦ x w i :=
    (contDiff_euclidean.mp hx i).differentiable (by norm_num)
  have := finiteDimensional_of_gaugeFixedOperator_eq_zero (μ := volume) (hx.of_le (by norm_num))
    (fun w ↦ by simp [hsol w]) hlim hD fun _ ↦ mem_gaugeFixedKernel.1
  rw [← finrank_range_covariantTranslationLinearMap (hdx 2) (hdx 3) hlim hz₀]
  exact Submodule.finrank_mono (range_covariantTranslationLinearMap_le hx hsol hlim)

/-- **The kernel of `L_x` for a single zero consists of the covariant translations.** At a `C³`
vortex whose section has modulus tending to one at infinity and a zero divisor `D` of degree one,
the square-integrable `C²` solutions of `L_x y = 0` are exactly the covariant translations
`y_v`, `v ∈ ℂ`. -/
theorem range_covariantTranslationLinearMap_of_card_eq_one
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) (hcard : Multiset.card D = 1) :
    LinearMap.range (covariantTranslationLinearMap x) = gaugeFixedKernel x := by
  have hdx (i : Fin 4) : Differentiable ℝ fun w ↦ x w i :=
    (contDiff_euclidean.mp hx i).differentiable (by norm_num)
  have hhol (w : ℂ) : equation x w 1 = 0 ∧ equation x w 2 = 0 := by simp [hsol w]
  obtain ⟨z₀, hz₀⟩ := Multiset.card_pos_iff_exists_mem.1 (hcard ▸ one_pos)
  have hV (y : ℂ → EuclideanSpace ℝ (Fin 4)) (hy : y ∈ gaugeFixedKernel x) :=
    mem_gaugeFixedKernel.1 hy
  have := finiteDimensional_of_gaugeFixedOperator_eq_zero (hx.of_le (by norm_num)) hhol hlim hD hV
  refine Submodule.eq_of_le_of_finrank_le (range_covariantTranslationLinearMap_le hx hsol hlim) ?_
  rw [finrank_range_covariantTranslationLinearMap (hdx 2) (hdx 3) hlim
    (hD.pos_iff.1 (Multiset.count_pos.2 hz₀))]
  simpa [hcard] using
    finrank_le_two_mul_card_of_gaugeFixedOperator_eq_zero (hx.of_le (by norm_num)) hhol hlim hD hV

/-- **The kernel of `L_x` for a single zero has real dimension two**, under the hypotheses of
`TauCeti.Vortex.range_covariantTranslationLinearMap_of_card_eq_one`. -/
theorem finrank_gaugeFixedKernel_eq_two_of_card_eq_one
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) (hcard : Multiset.card D = 1) :
    finrank ℝ (gaugeFixedKernel x) = 2 := by
  obtain ⟨z₀, hz₀⟩ := Multiset.card_pos_iff_exists_mem.1 (hcard ▸ one_pos)
  have hdx (i : Fin 4) : Differentiable ℝ fun w ↦ x w i :=
    (contDiff_euclidean.mp hx i).differentiable (by norm_num)
  rw [← range_covariantTranslationLinearMap_of_card_eq_one hx hsol hlim hD hcard,
    finrank_range_covariantTranslationLinearMap (hdx 2) (hdx 3) hlim
      (hD.pos_iff.1 (Multiset.count_pos.2 hz₀))]

/-- The zero divisor of a `C³` vortex with the degree-`m` end framing, as a point of `Sym ℂ m`. -/
private theorem exists_sym_isZeroMultiplicity {m : ℕ}
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    ∃ D : Sym ℂ m, IsZeroMultiplicity (sectionValue x) fun z ↦ (D : Multiset ℂ).count z := by
  have hxi (i : Fin 4) : ContDiff ℝ 3 fun w ↦ x w i := contDiff_euclidean.mp hx i
  exact exists_sym_isZeroMultiplicity_sectionValue (k := 3) (by norm_num) (hxi 0) (hxi 1)
    ((hxi 2).differentiable (by norm_num)) ((hxi 3).differentiable (by norm_num))
    (fun w ↦ by simp [hsol w]) hframe

/-- **The kernel of `L_x` has real dimension at least two** at a `C³` framed vortex of positive
degree. -/
theorem two_le_finrank_gaugeFixedKernel {m : ℕ}
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    (hm : m ≠ 0) : 2 ≤ finrank ℝ (gaugeFixedKernel x) := by
  obtain ⟨D, hD⟩ := exists_sym_isZeroMultiplicity hx hsol hframe
  obtain ⟨z₀, hz₀⟩ := exists_eq_zero_of_tendsto_mul_inv_pow (contDiff_sectionValue
    (contDiff_euclidean.mp hx 2) (contDiff_euclidean.mp hx 3)).continuous hm hframe
  exact two_le_finrank_gaugeFixedKernel_of_sectionValue_eq_zero hx hsol
    (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe) hD hz₀

/-! ### Degree one -/

variable (hframe : Tendsto (fun z ↦ sectionValue x z * (z / (‖z‖ : ℂ))⁻¹) (cocompact ℂ) (𝓝 1))

include hframe

/-- **The kernel of `L_x` in degree one consists of the covariant translations.** At a `C³`
vortex with the degree-one end framing `α (z / |z|)⁻¹ → 1`, the square-integrable `C²` solutions
of `L_x y = 0` are exactly the covariant translations `y_v`, `v ∈ ℂ`. -/
theorem range_covariantTranslationLinearMap :
    LinearMap.range (covariantTranslationLinearMap x) = gaugeFixedKernel x := by
  have hframe₁ : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ 1)⁻¹) (cocompact ℂ)
      (𝓝 1) := by
    simpa using hframe
  obtain ⟨D, hD⟩ := exists_sym_isZeroMultiplicity hx hsol hframe₁
  exact range_covariantTranslationLinearMap_of_card_eq_one hx hsol
    (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe₁) hD D.2

/-- **The kernel of `L_x` in degree one has real dimension two**, the dimension of
`Sym¹ ℂ = ℂ`. -/
theorem finrank_gaugeFixedKernel_eq_two : finrank ℝ (gaugeFixedKernel x) = 2 := by
  have hframe₁ : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ 1)⁻¹) (cocompact ℂ)
      (𝓝 1) := by
    simpa using hframe
  obtain ⟨D, hD⟩ := exists_sym_isZeroMultiplicity hx hsol hframe₁
  exact finrank_gaugeFixedKernel_eq_two_of_card_eq_one hx hsol
    (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe₁) hD D.2

end Translations

/-! ### Surjectivity of the principal-part map and exact dimension -/

/-- A smooth kernel element with a single pole `c / (w - z)^(D(z) - m')` has leading principal-part
jet `a` of order `m'` at `z`, vanishing lower-order jets at `z`, and vanishing principal parts at
every other point. -/
private theorem exists_contDiff_gaugeFixedOperator_eq_zero_principalPart_triangular
    (hx : ContDiff ℝ ∞ x) (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) {ν : ℂ → ℂ}
    (hν : Differentiable ℝ ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2)
    {z : ℂ} {m' : ℕ} (hm' : m' < D.count z) (a : ℂ) :
    ∃ y : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ y ∧ MemLp y 2 volume ∧
      (∀ w, gaugeFixedOperator x y w = 0) ∧
      principalPart x ν y z m' = a ∧
      (∀ k < m', principalPart x ν y z k = 0) ∧
      (∀ z' ≠ z, ∀ k < D.count z', principalPart x ν y z' k = 0) := by
  have hxi (i : Fin 4) : ContDiff ℝ ∞ fun w ↦ x w i := contDiff_euclidean.1 hx i
  have hp : Differentiable ℝ fun w ↦ x w 2 := (hxi 2).differentiable (by simp)
  have hq : Differentiable ℝ fun w ↦ x w 3 := (hxi 3).differentiable (by simp)
  -- Analytic factorization of the entire factor `f = exp (-ν) α` at `z`.
  set f : ℂ → ℂ := fun w ↦ exp (-ν w) * sectionValue x w
  have hf : Differentiable ℂ f := differentiable_exp_neg_mul_sectionValue hp hq hhol hν hνeq
  have hfD : IsZeroMultiplicity f fun w ↦ D.count w :=
    hD.mul_left_of_continuous hν.continuous.neg.cexp fun _ ↦ exp_ne_zero _
  obtain ⟨g, hg, hg₀, hfg⟩ := hfD.exists_analyticAt_eq_pow_mul (hf.analyticAt z)
  have hαg : ∀ᶠ w in 𝓝 z, sectionValue x w = exp (ν w) * ((w - z) ^ D.count z * g w) := by
    filter_upwards [hfg] with w hw
    calc sectionValue x w = exp (ν w) * (exp (-ν w) * sectionValue x w) := by
          rw [← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul]
      _ = exp (ν w) * ((w - z) ^ D.count z * g w) := congrArg (exp (ν w) * ·) hw
  -- Smooth local factorization of `α` at `z` for constructing the pole kernel element.
  choose n' v hvc hv₀ hvf using
    exists_contDiffAt_sectionValue_eq_pow_mul (k := ⊤) le_top (hxi 0) (hxi 1) hp hq hhol
      hD.exists_ne_zero
  have hn' : n' = fun w ↦ D.count w :=
    (isZeroMultiplicity_iff.2 fun w ↦ ⟨v w, (hvc w).continuousAt, hv₀ w, hvf w⟩).unique hD
  subst hn'
  -- The local analytic numerator `R(w) = (w - z)^m' g(w)` has analytic order `m'` at `z`.
  set j : ℕ := D.count z - 1 - m'
  have hj : j < D.count z := by omega
  have hmj : m' + (j + 1) = D.count z := by omega
  set R : ℂ → ℂ := ((· - z) ^ m') * g
  have hpow_an : AnalyticAt ℂ ((· - z) ^ m') z := (analyticAt_id.sub analyticAt_const).pow m'
  have hR : AnalyticAt ℂ R z := hpow_an.mul hg
  have hRord : analyticOrderAt R z = m' := by
    rw [analyticOrderAt_mul hpow_an hg, analyticOrderAt_centeredMonomial,
      hg.analyticOrderAt_eq_zero.2 hg₀, add_zero]
  obtain ⟨hRk, hRm'⟩ := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hR).1 hRord
  -- Scale the pole coefficient so that the `m'`-th derivative of `c R` at `z` equals `a`.
  set c : ℂ := a / iteratedDeriv m' R z
  obtain ⟨y, hy, hy₂, hker, ξ, hξ, hyξ⟩ :=
    exists_gaugeFixedOperator_eq_zero_sectionValue_eq_mul_div_pow_add hx hhol hlim (hvc z)
      (hvf z) hj c
  obtain ⟨G₀, hG₀, H₀, hH₀, hy₀⟩ :=
    exists_sectionValue_eq_mul_add_exp_mul_of_mem_gaugeFixedKernel hp hq hhol hν hνeq
      (mem_gaugeFixedKernel.2 ⟨hy.of_le (by simp), hy₂, hker⟩)
  -- Near `z`, `δα = α ξ + e^ν (c R)` on `{z}ᶜ`, hence on all of `𝓝 z` by continuity.
  have hpt {w : ℂ} (hw : sectionValue x w = exp (ν w) * ((w - z) ^ D.count z * g w))
      (hwz : w ≠ z) :
      sectionValue y w = sectionValue x w * ξ w + exp (ν w) * (c * R w) := by
    have hne : (w - z) ^ (j + 1) ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hwz)
    have hsplit : (w - z) ^ D.count z = (w - z) ^ m' * (w - z) ^ (j + 1) := by
      rw [← hmj, pow_add]
    rw [hyξ w hwz, mul_add, add_comm (sectionValue x w * _), hw, hsplit]
    simp only [R, Pi.mul_apply, Pi.pow_apply]
    field_simp
  have hlhs : ContinuousAt (sectionValue y) z :=
    (contDiff_sectionValue (contDiff_euclidean.1 hy 2)
      (contDiff_euclidean.1 hy 3)).continuous.continuousAt
  have hrhs : ContinuousAt (fun w ↦ sectionValue x w * ξ w + exp (ν w) * (c * R w)) z :=
    ((contDiff_sectionValue (hxi 2) (hxi 3)).continuous.continuousAt.mul
      hξ.continuous.continuousAt).add
      (hν.continuous.cexp.continuousAt.mul (continuousAt_const.mul hR.continuousAt))
  have hloc_z : ∀ᶠ w in 𝓝 z,
      sectionValue y w = sectionValue x w * ξ w + exp (ν w) * (c * R w) := by
    refine (hlhs.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hrhs).1 ?_
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hαg, self_mem_nhdsWithin]
      with w hw hwz
    exact hpt hw hwz
  have hpz {k : ℕ} (hk : k < D.count z) :
      principalPart x ν y z k = c * iteratedDeriv k R z := by
    rw [principalPart_eq_iteratedDeriv_of_eventuallyEq (H := fun w ↦ c * R w) hD hν.continuous
      ⟨G₀, hG₀.continuous, H₀, hH₀, hy₀⟩ hξ.continuous.continuousAt (analyticAt_const.mul hR)
      hloc_z hk, iteratedDeriv_const_mul_field]
  refine ⟨y, hy, hy₂, hker, ?_, fun k hk ↦ ?_, fun z' hz' k hk ↦ ?_⟩
  · rw [hpz hm', div_mul_cancel₀ a hRm']
  · rw [hpz (hk.trans hm'), hRk k hk, mul_zero]
  · have hGz' : ContinuousAt (fun w ↦ c / (w - z) ^ (j + 1) + ξ w) z' :=
      (continuousAt_const.div ((continuousAt_id.sub continuousAt_const).pow _)
        (pow_ne_zero _ (sub_ne_zero.2 hz'))).add hξ.continuous.continuousAt
    have hloc_z' : ∀ᶠ w in 𝓝 z', sectionValue y w =
        sectionValue x w * (c / (w - z) ^ (j + 1) + ξ w) + exp (ν w) * 0 := by
      filter_upwards [isOpen_ne.mem_nhds hz'] with w hw
      rw [hyξ w hw, mul_zero, add_zero]
    rw [principalPart_eq_iteratedDeriv_of_eventuallyEq (H := fun _ ↦ 0) hD hν.continuous
      ⟨G₀, hG₀.continuous, H₀, hH₀, hy₀⟩ hGz' analyticAt_const hloc_z' hk]
    simp

/-- If `y` has principal-part jet `a` at `i = ⟨z, m'⟩`, vanishing lower-order jets at `z`, and
vanishing principal parts away from `z`, then every nonzero entry of
`(j ↦ principalPart x ν y j.1 j.2) - Pi.single i a` lies over the same point `z` with strictly
larger jet order. -/
private theorem eq_and_lt_of_principalPart_sub_single_ne_zero [DecidableEq (Multiset.ToType D)]
    {ν : ℂ → ℂ} {y : ℂ → EuclideanSpace ℝ (Fin 4)} {i j : Multiset.ToType D} {a : ℂ}
    (hp_eq : principalPart x ν y i.1 i.2 = a)
    (hp_lt : ∀ k < (i.2 : ℕ), principalPart x ν y i.1 k = 0)
    (hp_ne : ∀ z' ≠ i.1, ∀ k < D.count z', principalPart x ν y z' k = 0)
    (h : principalPart x ν y j.1 j.2 - (Pi.single i a : Multiset.ToType D → ℂ) j ≠ 0) :
    j.1 = i.1 ∧ (i.2 : ℕ) < j.2 := by
  have hji : j.1 = i.1 := by
    by_contra hne
    have hji_ne : j ≠ i := fun hij ↦ hne (congrArg Sigma.fst hij)
    exact h (by simp [hp_ne j.1 hne j.2 j.2.2, Pi.single_eq_of_ne hji_ne])
  refine ⟨hji, lt_of_not_ge fun hle ↦ h ?_⟩
  rcases hle.eq_or_lt with heq | hlt
  · obtain rfl : j = i := by
      rcases i with ⟨z, k, hk⟩
      rcases j with ⟨z', k', hk'⟩
      dsimp at hji heq
      subst hji heq
      rfl
    simp [hp_eq]
  · have hji_ne : j ≠ i :=
      fun hij ↦ hlt.ne (congrArg (fun p : Multiset.ToType D ↦ (p.2 : ℕ)) hij)
    generalize (j.2 : ℕ) = k at hlt ⊢
    rw [hji, hp_lt k hlt, Pi.single_eq_of_ne hji_ne, sub_zero]

/-- **Surjectivity of the principal-part map.** Let `x` be a smooth field satisfying the
holomorphicity rows `∂bar_a α = 0` with `|α|² → 1` at infinity and zero divisor `D`, and let `ν`
be a differentiable integrating factor (`∂bar ν = (b₂ - i b₁) / 2`). On any real subspace `V` of
variations admitting principal-part decompositions that contains every smooth square-integrable
solution of `L_x y = 0`, the principal-part map `V →ₗ[ℝ] (D → ℂ)` is surjective. -/
theorem principalPartMap_surjective (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) {ν : ℂ → ℂ}
    (hν : Differentiable ℝ ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2)
    (hdec : ∀ y ∈ V, ∃ G : ℂ → ℂ, Continuous G ∧ ∃ H : ℂ → ℂ, Differentiable ℂ H ∧
      ∀ w, sectionValue y w = sectionValue x w * G w + exp (ν w) * H w)
    (hVsmooth : ∀ y, ContDiff ℝ ∞ y → MemLp y 2 volume →
      (∀ w, gaugeFixedOperator x y w = 0) → y ∈ V) :
    Function.Surjective (principalPartMap hD hν.continuous hdec) := by
  classical
  set Φ := principalPartMap hD hν.continuous hdec
  -- Triangular elimination in decreasing jet order `i.2` at each zero `i.1`.
  have hsingle : ∀ d : ℕ, ∀ i : Multiset.ToType D, D.count i.1 - 1 - i.2 = d →
      ∀ a : ℂ, Pi.single i a ∈ LinearMap.range Φ := by
    intro d
    induction d using Nat.strong_induction_on with
    | ind d ih =>
      intro i hd a
      obtain ⟨y₀, hy₀, hy₀2, hy₀k, hp_eq, hp_lt, hp_ne⟩ :=
        exists_contDiff_gaugeFixedOperator_eq_zero_principalPart_triangular hx hhol hlim hD hν
          hνeq i.2.2 a
      set v₀ : V := ⟨y₀, hVsmooth y₀ hy₀ hy₀2 hy₀k⟩
      set u : Multiset.ToType D → ℂ := Φ v₀ - Pi.single i a
      have hu_mem : u ∈ LinearMap.range Φ := by
        rw [← Finset.univ_sum_single u]
        refine Submodule.sum_mem _ fun j _ ↦ ?_
        by_cases huj : u j = 0
        · simp [huj]
        · obtain ⟨hji, hij_lt⟩ := eq_and_lt_of_principalPart_sub_single_ne_zero hp_eq hp_lt hp_ne
            (by simpa [u, Φ, v₀] using huj)
          have hd_lt : D.count j.1 - 1 - j.2 < d := by
            have := j.2.2
            have := congrArg D.count hji
            omega
          exact ih _ hd_lt j rfl (u j)
      exact sub_sub_cancel (Φ v₀) (Pi.single i a) ▸ sub_mem (LinearMap.mem_range_self Φ v₀) hu_mem
  intro g
  rw [← LinearMap.mem_range, ← Finset.univ_sum_single g]
  exact Submodule.sum_mem _ fun i _ ↦ hsingle _ i rfl (g i)

/-- **Bijectivity of the principal-part map.** Under the hypotheses of
`principalPartMap_surjective`, if `ν` is `C²` and `V` consists of `C²` square-integrable
solutions of `L_x y = 0` (for example `V = gaugeFixedKernel x`), then the principal-part map
`V →ₗ[ℝ] (D → ℂ)` is bijective. -/
theorem principalPartMap_bijective (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) {ν : ℂ → ℂ}
    (hν : ContDiff ℝ 2 ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2)
    (hdec : ∀ y ∈ V, ∃ G : ℂ → ℂ, Continuous G ∧ ∃ H : ℂ → ℂ, Differentiable ℂ H ∧
      ∀ w, sectionValue y w = sectionValue x w * G w + exp (ν w) * H w)
    (hVker : ∀ y ∈ V, ContDiff ℝ 2 y ∧ MemLp y 2 volume ∧ ∀ w, gaugeFixedOperator x y w = 0)
    (hVsmooth : ∀ y, ContDiff ℝ ∞ y → MemLp y 2 volume →
      (∀ w, gaugeFixedOperator x y w = 0) → y ∈ V) :
    Function.Bijective (principalPartMap hD hν.continuous hdec) := by
  have hi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ x w i :=
    (contDiff_euclidean.1 hx i).of_le (by simp)
  have hp := (hi 2).differentiable (by norm_num)
  have hq := (hi 3).differentiable (by norm_num)
  refine ⟨principalPartMap_injective (k := 2) (by norm_num) (hi 0) (hi 1) hp hq hhol hD hν hνeq
    (forall_mem_linearizedEquation_eq_zero hVker) hdec
    (fun y hy η hη hyη ↦ eq_zero_of_gaugeFixedOperator_eq_zero_of_sectionValue_eq_mul_of_tendsto
      (hx.of_le (by simp)) hhol hlim (hVker y hy).1.continuous (hVker y hy).2.1 (hVker y hy).2.2
      hη hyη),
    principalPartMap_surjective hx hhol hlim hD (hν.differentiable (by norm_num)) hνeq hdec
      hVsmooth⟩

/-- **The principal-part isomorphism on the gauge-fixed kernel.** At a smooth field `x` with
`∂bar_a α = 0`, `|α|² → 1` at infinity, zero divisor `D`, and a `C²` integrating factor `ν`, the
principal-part map identifies `gaugeFixedKernel x` linearly over `ℝ` with the space
`Multiset.ToType D → ℂ` of principal parts at `D`, of real dimension `2 |D|`. -/
noncomputable def gaugeFixedKernelPrincipalPartEquiv (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) {ν : ℂ → ℂ}
    (hν : ContDiff ℝ 2 ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2) :
    gaugeFixedKernel x ≃ₗ[ℝ] Multiset.ToType D → ℂ :=
  LinearEquiv.ofBijective
    (principalPartMap hD hν.continuous fun _ hy ↦
      (exists_sectionValue_eq_mul_add_exp_mul_of_mem_gaugeFixedKernel
        ((contDiff_euclidean.1 hx 2).differentiable (by simp))
        ((contDiff_euclidean.1 hx 3).differentiable (by simp))
        hhol (hν.differentiable (by norm_num)) hνeq hy).imp fun _ ↦
          And.imp_left ContDiff.continuous)
    (principalPartMap_bijective hx hhol hlim hD hν hνeq _
      (fun _ hy ↦ mem_gaugeFixedKernel.1 hy)
      fun _ hy hy₂ hker ↦ mem_gaugeFixedKernel.2 ⟨hy.of_le (by simp), hy₂, hker⟩)

/-- Evaluating `gaugeFixedKernelPrincipalPartEquiv` at `i = ⟨z, k⟩` gives
`principalPart x ν y z k`. -/
@[simp]
theorem gaugeFixedKernelPrincipalPartEquiv_apply (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) {ν : ℂ → ℂ}
    (hν : ContDiff ℝ 2 ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2)
    (y : gaugeFixedKernel x) (i : Multiset.ToType D) :
    gaugeFixedKernelPrincipalPartEquiv hx hhol hlim hD hν hνeq y i =
      principalPart x ν y i.1 i.2 := by
  simp [gaugeFixedKernelPrincipalPartEquiv]

/-- **Smoothness of classical kernel elements.** At a smooth field `x` satisfying the
holomorphicity rows `∂bar_a α = 0` and `|α|² → 1` at infinity, every `C²` square-integrable
kernel element `y ∈ gaugeFixedKernel x` is smooth (`C^∞`). -/
theorem contDiff_of_mem_gaugeFixedKernel (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ gaugeFixedKernel x) :
    ContDiff ℝ ∞ y := by
  have hxi (i : Fin 4) : ContDiff ℝ ∞ fun w ↦ x w i := contDiff_euclidean.1 hx i
  have hp := (hxi 2).differentiable (by simp)
  have hq := (hxi 3).differentiable (by simp)
  -- The section is nonzero near infinity, so its zeros form a finite divisor `D`.
  have htail : ∀ᶠ w in cocompact ℂ, sectionValue x w ≠ 0 := by
    filter_upwards [hlim.eventually_ne one_ne_zero] with w hw h0
    exact hw (by rw [(sectionValue_eq_zero_iff x w).1 h0]; norm_num)
  obtain ⟨D, hmult⟩ := exists_isZeroMultiplicity_sectionValue_of_eventually_ne (k := 2)
    (by norm_num) ((hxi 0).of_le (by simp)) ((hxi 1).of_le (by simp)) hp hq hhol htail
  obtain ⟨ν, hν, hνeq⟩ := exists_contDiff_conjWirtingerDeriv_apply_one_eq (n := 2) (by norm_num)
    (contDiff_connectionCoeff ((hxi 0).of_le (by simp)) ((hxi 1).of_le (by simp)))
  -- The subspace `W` of smooth `L²` kernel elements surjects onto `D → ℂ` while `gaugeFixedKernel`
  -- injects into `D → ℂ`, forcing `y ∈ W`.
  let S : Submodule ℝ (ℂ → EuclideanSpace ℝ (Fin 4)) :=
    { carrier := {u | ContDiff ℝ ∞ u}
      add_mem' := fun (hu₁ : ContDiff ℝ ∞ _) hu₂ ↦ hu₁.add hu₂
      zero_mem' := show ContDiff ℝ ∞ 0 from contDiff_zero_fun
      smul_mem' := fun t _ (hu : ContDiff ℝ ∞ _) ↦ hu.const_smul t }
  let W : Submodule ℝ (ℂ → EuclideanSpace ℝ (Fin 4)) := gaugeFixedKernel x ⊓ S
  have hdecW (u) (hu : u ∈ W) :=
    (exists_sectionValue_eq_mul_add_exp_mul_of_mem_gaugeFixedKernel hp hq hhol
      (hν.differentiable (by norm_num)) hνeq hu.1).imp fun _ ↦ And.imp_left ContDiff.continuous
  obtain ⟨u, hu_eq⟩ := principalPartMap_surjective hx hhol hlim hmult
    (hν.differentiable (by norm_num)) hνeq hdecW
    (fun _ hu hu₂ huk ↦ ⟨mem_gaugeFixedKernel.2 ⟨hu.of_le (by simp), hu₂, huk⟩, hu⟩)
    (gaugeFixedKernelPrincipalPartEquiv hx hhol hlim hmult hν hνeq ⟨y, hy⟩)
  have h_inj : (⟨u.1, u.2.1⟩ : gaugeFixedKernel x) = ⟨y, hy⟩ := by
    apply (gaugeFixedKernelPrincipalPartEquiv hx hhol hlim hmult hν hνeq).injective
    ext i
    simpa using congrFun hu_eq i
  have hy_eq : u.1 = y := congrArg Subtype.val h_inj
  exact hy_eq ▸ u.2.2

/-- **The kernel of `L_x` has real dimension `2 |D|`.** Let `x` be a smooth field satisfying the
holomorphicity rows `∂bar_a α = 0` with `|α|² → 1` at infinity, whose section has zero divisor
`D`. Then the `C²` square-integrable kernel `gaugeFixedKernel x` has real dimension `2 |D|`. -/
theorem finrank_gaugeFixedKernel_eq_two_mul_card (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) :
    Module.finrank ℝ (gaugeFixedKernel x) = 2 * Multiset.card D := by
  have hi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ x w i :=
    (contDiff_euclidean.1 hx i).of_le (by simp)
  obtain ⟨ν, hν, hνeq⟩ := exists_contDiff_conjWirtingerDeriv_apply_one_eq (n := 2) (by norm_num)
    (contDiff_connectionCoeff (hi 0) (hi 1))
  rw [(gaugeFixedKernelPrincipalPartEquiv hx hhol hlim hD hν hνeq).finrank_eq,
    Module.finrank_pi_fintype, Finset.sum_const, Complex.finrank_real_complex, smul_eq_mul,
    Finset.card_univ, Multiset.card_coe, mul_comm]

/-- **The kernel of `L_x` at a framed degree-`m` vortex has real dimension `2 m`.** Let `x` be a
smooth field satisfying the holomorphicity rows `∂bar_a α = 0` and the degree-`m` end framing
`α(z) (z / |z|)⁻ᵐ → 1`. Then `gaugeFixedKernel x` has real dimension `2 m`, the real dimension of
the divisor space `Sym^m ℂ`. -/
theorem finrank_gaugeFixedKernel_eq_two_mul {m : ℕ} (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    Module.finrank ℝ (gaugeFixedKernel x) = 2 * m := by
  have hi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ x w i :=
    (contDiff_euclidean.1 hx i).of_le (by simp)
  obtain ⟨D, hD⟩ := exists_sym_isZeroMultiplicity_sectionValue (k := 2) (by norm_num) (hi 0)
    (hi 1) ((hi 2).differentiable (by norm_num)) ((hi 3).differentiable (by norm_num)) hhol hframe
  rw [finrank_gaugeFixedKernel_eq_two_mul_card hx hhol
    (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe) hD, Sym.card_coe]

end TauCeti.Vortex
