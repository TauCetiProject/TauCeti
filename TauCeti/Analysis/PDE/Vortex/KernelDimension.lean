/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.LogVariation
public import TauCeti.Analysis.PDE.Vortex.PrincipalPart
public import TauCeti.Analysis.PDE.Vortex.TranslationKernel
import TauCeti.Analysis.Analytic.Order
import TauCeti.Analysis.Complex.Wirtinger.DolbeaultLemma
import TauCeti.Analysis.Normed.Field.PoleSum
import TauCeti.Analysis.PDE.Vortex.KernelExistence
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The dimension of the kernel of the gauge-fixed operator at a plane vortex

Let `x` be a field whose holomorphicity rows `∂bar_a α = 0` vanish, with `|α| → 1` at infinity,
and let the zeros of its section `α`, counted with multiplicity, form the effective divisor `D`.
This file proves that every real vector space of `C²` square-integrable solutions `y` of
`L_x y = 0`, for the gauge-fixed operator `L_x = d₀* ⊕ d₁` (`gaugeFixedOperator`), has dimension
at most `2 |D|` (`TauCeti.Vortex.finrank_le_two_mul_card_of_gaugeFixedOperator_eq_zero`). For a
vortex with the degree-`m` end framing `α(z) (z / |z|)⁻ᵐ → 1` the bound is `2m`
(`TauCeti.Vortex.finrank_le_two_mul_of_tendsto_sectionValue_mul_inv_pow`). Only the
holomorphicity rows of the vortex equation are used.

This is the upper bound in Taubes's identification of the kernel of `L_x` with the real tangent
space `ℂᵐ` of the divisor space `Sym^m ℂ`, following Samols. The last two rows of `L_x y = 0` are
the holomorphicity rows of the linearized equation, so the section variation decomposes as
`δα = α G + e^ν H` with `H` entire, and the derivatives of `H` at the zeros of `α` record the
principal parts of `δα / α` (`TauCeti.Vortex.principalPartMap`). This real-linear map to `ℂ^|D|`
is injective (`TauCeti.Vortex.principalPartMap_injective`) as soon as every kernel element with
`δα = α η`, `η` of class `C²`, vanishes. That is the vanishing theorem
`TauCeti.Vortex.eq_zero_of_gaugeFixedOperator_eq_zero_of_sectionValue_eq_mul_of_tendsto`.

The second part of the file studies the whole space `gaugeFixedKernel x` of square-integrable
`C²` classical solutions of `L_x y = 0`, of real dimension at most `2 |D|` by the above.

**The lower bound from translations.** When the section has a zero, the covariant translations
`y_v = (ι_v F_a, ∇_v α)` span a two-dimensional subspace of the kernel
(`TauCeti.Vortex.finrank_range_covariantTranslationLinearMap`,
`TauCeti.Vortex.range_covariantTranslationLinearMap_le`); thus `2 ≤ dim_ℝ gaugeFixedKernel x`
(`two_le_finrank_gaugeFixedKernel_of_sectionValue_eq_zero`). They move all zeros of the vortex by
the same vector. A vortex framed in positive degree has a zero
(`TauCeti.exists_eq_zero_of_tendsto_mul_inv_pow`), so the bound holds there
(`two_le_finrank_gaugeFixedKernel`).

**Degrees zero and one.** If the section has no zeros, the kernel vanishes
(`gaugeFixedKernel_eq_bot_of_forall_sectionValue_ne_zero`, and `gaugeFixedKernel_eq_bot` in
degree zero). If its divisor is a single point, the two bounds agree: every kernel element is a
covariant translation (`range_covariantTranslationLinearMap_of_card_eq_one`), and the kernel has
real dimension two (`finrank_gaugeFixedKernel_eq_two_of_card_eq_one`), the dimension of
`Sym¹ ℂ = ℂ`. The degree-one framed forms are `range_covariantTranslationLinearMap` and
`finrank_gaugeFixedKernel_eq_two`.

**The dimension `2 |D|`.** At a smooth field, the zeros can also be moved independently. For
every point `⟨a, j⟩` of `D`, `j` below the multiplicity of the zero `a`, and every `c ∈ ℂ`, the
kernel contains an element whose section variation is `δα = α η` with `η` of principal part
`c / (w - a) ^ (j + 1)` at `a` and continuous elsewhere
(`TauCeti.Vortex.exists_gaugeFixedOperator_eq_zero_sectionValue_eq_mul_div_pow_add`). Real
combinations of these elements have principal parts `∑ c_⟨a, j⟩ / (w - a) ^ (j + 1)`, and a finite
sum of poles that extends continuously vanishes (`TauCeti.eq_zero_of_sum_div_sub_pow_eq`), so they
span a subspace of real dimension `2 |D|`. Hence the kernel has real dimension exactly `2 |D|`
(`finrank_gaugeFixedKernel_eq_two_mul_card`), and `2m` at a smooth field framed in degree `m`
(`finrank_gaugeFixedKernel_eq_two_mul`): the real dimension of the tangent space of `Sym^m ℂ`.
This needs only the holomorphicity rows of the vortex equation. The cokernel of the Sobolev
realization of `L_x`, which together with this gives the Fredholm index `2m`, is not treated here.

## Main results

* `TauCeti.Vortex.finiteDimensional_of_gaugeFixedOperator_eq_zero` and
  `TauCeti.Vortex.finrank_le_two_mul_card_of_gaugeFixedOperator_eq_zero`: a space of `C²`
  square-integrable kernel elements is finite dimensional, of dimension at most `2 |D|`.
* `TauCeti.Vortex.finiteDimensional_of_tendsto_sectionValue_mul_inv_pow` and
  `TauCeti.Vortex.finrank_le_two_mul_of_tendsto_sectionValue_mul_inv_pow`: the same for a vortex
  framed in degree `m`, with bound `2m`.
* `TauCeti.Vortex.two_le_finrank_gaugeFixedKernel_of_sectionValue_eq_zero` and
  `TauCeti.Vortex.two_le_finrank_gaugeFixedKernel`: `2 ≤ dim_ℝ ker L_x` when the section has a
  zero, in particular at a framed vortex of positive degree.
* `TauCeti.Vortex.gaugeFixedKernel_eq_bot_of_forall_sectionValue_ne_zero` and
  `TauCeti.Vortex.gaugeFixedKernel_eq_bot`: the kernel vanishes when the section has no zeros,
  in particular in degree zero.
* `TauCeti.Vortex.range_covariantTranslationLinearMap_of_card_eq_one`,
  `TauCeti.Vortex.finrank_gaugeFixedKernel_eq_two_of_card_eq_one`,
  `TauCeti.Vortex.range_covariantTranslationLinearMap` and
  `TauCeti.Vortex.finrank_gaugeFixedKernel_eq_two`: for a single zero, in particular in degree
  one, the kernel consists exactly of the covariant translations and has real dimension two.
* `TauCeti.Vortex.two_mul_card_le_finrank_gaugeFixedKernel`,
  `TauCeti.Vortex.finrank_gaugeFixedKernel_eq_two_mul_card` and
  `TauCeti.Vortex.finrank_gaugeFixedKernel_eq_two_mul`: at a smooth field the kernel has real
  dimension exactly `2 |D|`, and `2m` in degree `m`.

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
/-- A `C²` kernel element of `L_x` has `C²` components and satisfies the holomorphicity rows of
the linearized equation, which are the last two rows of `L_x y = 0`. -/
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

/-! ### The dimension `2 |D|` -/

section Dimension

variable (hx : ContDiff ℝ ∞ x) (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
  (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
  (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z)

include hx hhol hlim hD

/-- At every point `⟨a, j⟩` of the zero divisor `D` and for every `c ∈ ℂ`, the kernel of `L_x`
contains an element with section variation `δα = α (c / (w - a) ^ (j + 1) + ξ)` off `a`, where
`ξ` is continuous. -/
private theorem exists_mem_gaugeFixedKernel_sectionValue_eq (i : D.ToType) (c : ℂ) :
    ∃ y ∈ gaugeFixedKernel x, ∃ ξ : ℂ → ℂ, Continuous ξ ∧ ∀ w, w ≠ i.1 →
      sectionValue y w = sectionValue x w * (c / (w - i.1) ^ ((i.2 : ℕ) + 1) + ξ w) := by
  have hxi (k : Fin 4) : ContDiff ℝ ∞ fun w ↦ x w k := contDiff_euclidean.mp hx k
  obtain ⟨N, v, hv, hv₀, hfac⟩ := exists_contDiffAt_sectionValue_eq_pow_mul (k := ⊤) le_top
    (hxi 0) (hxi 1) ((hxi 2).differentiable (by simp)) ((hxi 3).differentiable (by simp)) hhol
    hD.exists_ne_zero i.1
  obtain ⟨u, hu, hu₀, hfacu⟩ := isZeroMultiplicity_iff.1 hD i.1
  obtain rfl : N = D.count i.1 := eq_of_eventually_sub_pow_mul_eq hv.continuousAt hv₀ hu hu₀ <| by
    filter_upwards [hfac, hfacu] with w hw hwu
    rw [← hw, ← hwu]
  obtain ⟨y, hy, hy₂, hker, ξ, hξ, hyξ⟩ :=
    exists_gaugeFixedOperator_eq_zero_sectionValue_eq_mul_div_pow_add hx hhol hlim hv hfac i.2.2 c
  exact ⟨y, mem_gaugeFixedKernel.2 ⟨hy.of_le (by simp), hy₂, hker⟩, ξ, hξ.continuous, hyξ⟩

/-- **The kernel of `L_x` has real dimension at least `2 |D|`.** Let `x` be a smooth field with
vanishing holomorphicity rows and `|α|² → 1` at infinity, whose section has zero divisor `D`.
Then the `C²` square-integrable kernel of the gauge-fixed operator `L_x` has real dimension at
least twice the degree of `D`: for every point `⟨a, j⟩` of `D` it contains kernel elements whose
section variations `δα = α η` give `η` the principal parts `c / (w - a) ^ (j + 1)`, `c ∈ ℂ`, and
these are linearly independent over `ℝ`. -/
theorem two_mul_card_le_finrank_gaugeFixedKernel :
    2 * Multiset.card D ≤ finrank ℝ (gaugeFixedKernel x) := by
  classical
  have := finiteDimensional_of_gaugeFixedOperator_eq_zero (μ := volume) (hx.of_le (by simp)) hhol
    hlim hD fun _ ↦ mem_gaugeFixedKernel.1
  choose Y hY ξ hξ hYξ using exists_mem_gaugeFixedKernel_sectionValue_eq hx hhol hlim hD
  -- The kernel element `∑ (Re c_i) Y_i(1) + (Im c_i) Y_i(i)`, whose `η` has principal parts
  -- `c_i / (w - a_i) ^ (j_i + 1)`.
  let Ψ : (D.ToType → ℂ) →ₗ[ℝ] gaugeFixedKernel x := ∑ i,
    ((reLm ∘ₗ LinearMap.proj i).smulRight ⟨Y i 1, hY i 1⟩ +
      (imLm ∘ₗ LinearMap.proj i).smulRight ⟨Y i I, hY i I⟩)
  have hΨ (c : D.ToType → ℂ) :
      (Ψ c : ℂ → EuclideanSpace ℝ (Fin 4)) = ∑ i, ((c i).re • Y i 1 + (c i).im • Y i I) := by
    simp [Ψ]
  have hinj : Function.Injective Ψ := by
    refine (injective_iff_map_eq_zero Ψ).2 fun c hc ↦ eq_zero_of_sum_div_sub_pow_eq
      (p := fun i : D.ToType ↦ i.1) (e := fun i ↦ (i.2 : ℕ))
      (g := fun w ↦ -∑ i, ((c i).re * ξ i 1 w + (c i).im * ξ i I w)) ?_
      (fun _ ↦ (by fun_prop (disch := exact hξ _ _) : Continuous _).continuousAt) fun w hw ↦ ?_
    · rintro ⟨a, j⟩ ⟨b, k⟩ h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, h⟩ := h
      rw [Fin.ext h]
    -- Off the zeros of `α`, the section variation of `Ψ c` is `α` times the sum of the poles
    -- plus a continuous function, and it vanishes.
    have hαw : sectionValue x w ≠ 0 := hD.eq_zero_iff.1 <| by
      by_contra h0
      exact hw ⟨⟨w, ⟨0, Nat.pos_of_ne_zero h0⟩⟩, rfl⟩
    let S : (ℂ → EuclideanSpace ℝ (Fin 4)) →ₗ[ℝ] ℂ :=
      { toFun := fun y ↦ sectionValue y w
        map_add' := fun y y' ↦ sectionValue_add y y' w
        map_smul' := fun t y ↦ by simp [sectionValue_smul, Complex.real_smul] }
    have hS : S (Ψ c : ℂ → EuclideanSpace ℝ (Fin 4)) = sectionValue x w *
        (∑ i, c i / (w - i.1) ^ ((i.2 : ℕ) + 1) +
          ∑ i, ((c i).re * ξ i 1 w + (c i).im * ξ i I w)) := by
      rw [hΨ, map_sum, mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hwi : w ≠ i.1 := fun h ↦ hw ⟨i, h.symm⟩
      simp only [map_add, map_smul, S, LinearMap.coe_mk, AddHom.coe_mk, Complex.real_smul,
        hYξ i 1 w hwi, hYξ i I w hwi]
      linear_combination (sectionValue x w / (w - i.1) ^ ((i.2 : ℕ) + 1)) * Complex.re_add_im (c i)
    rw [hc, Submodule.coe_zero, map_zero, eq_comm] at hS
    exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.1 hS).resolve_left hαw)
  calc 2 * Multiset.card D = finrank ℝ (D.ToType → ℂ) := by
        rw [Module.finrank_pi_fintype, Finset.sum_const, Complex.finrank_real_complex, smul_eq_mul,
          Finset.card_univ, Multiset.card_coe, mul_comm]
    _ ≤ finrank ℝ (gaugeFixedKernel x) := LinearMap.finrank_le_finrank_of_injective hinj

/-- **The kernel of `L_x` has real dimension `2 |D|`.** Let `x` be a smooth field with vanishing
holomorphicity rows and `|α|² → 1` at infinity, whose section has zero divisor `D`. Then the `C²`
square-integrable kernel of the gauge-fixed operator `L_x` has real dimension exactly twice the
degree of `D`, the real dimension of the space `Sym^|D| ℂ` of divisors of that degree. -/
theorem finrank_gaugeFixedKernel_eq_two_mul_card :
    finrank ℝ (gaugeFixedKernel x) = 2 * Multiset.card D :=
  (finrank_le_two_mul_card_of_gaugeFixedOperator_eq_zero (μ := volume) (hx.of_le (by simp)) hhol
    hlim hD fun _ ↦ mem_gaugeFixedKernel.1).antisymm
    (two_mul_card_le_finrank_gaugeFixedKernel hx hhol hlim hD)

end Dimension

/-- **The kernel of `L_x` at a framed vortex of degree `m` has real dimension `2m`.** At a smooth
field with vanishing holomorphicity rows and the degree-`m` end framing `α(z) (z / |z|)⁻ᵐ → 1`,
in particular at a smooth framed vortex of degree `m`, the `C²` square-integrable kernel of the
gauge-fixed operator `L_x` has real dimension `2m`, the real dimension of `Sym^m ℂ`. -/
theorem finrank_gaugeFixedKernel_eq_two_mul {m : ℕ} (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    finrank ℝ (gaugeFixedKernel x) = 2 * m := by
  have hxi (k : Fin 4) : ContDiff ℝ 2 fun w ↦ x w k := contDiff_euclidean.mp (hx.of_le (by simp)) k
  obtain ⟨D, hD⟩ := exists_sym_isZeroMultiplicity_sectionValue (k := 2) (by norm_num) (hxi 0)
    (hxi 1) ((hxi 2).differentiable (by norm_num)) ((hxi 3).differentiable (by norm_num)) hhol
    hframe
  rw [finrank_gaugeFixedKernel_eq_two_mul_card hx hhol
    (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe) hD, Sym.card_coe]

end TauCeti.Vortex
