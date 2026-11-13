/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.LogVariation
public import TauCeti.Analysis.PDE.Vortex.PrincipalPart
public import TauCeti.Analysis.PDE.Vortex.TranslationKernel
import TauCeti.Analysis.Complex.Wirtinger.DolbeaultLemma
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
`C²` classical solutions of `L_x y = 0`, of real dimension at most `2 m`
(`TauCeti.Vortex.finrank_gaugeFixedKernel_le`).

**The lower bound from translations.** At a vortex of positive degree the section has a zero,
so the covariant translations `y_v = (ι_v F_a, ∇_v α)` form a two-dimensional subspace of the
kernel (`TauCeti.Vortex.covariantTranslation_injective`); thus `2 ≤ dim_ℝ gaugeFixedKernel x`
(`two_le_finrank_gaugeFixedKernel`). They move all zeros of the vortex by the same vector.

**Degrees zero and one.** In degree zero the kernel vanishes (`gaugeFixedKernel_eq_bot`). In
degree one the two bounds agree: every kernel element is a covariant translation
(`range_covariantTranslationLinearMap`), and the kernel has real dimension two
(`finrank_gaugeFixedKernel_eq_two`), the dimension of `Sym¹ ℂ = ℂ`.

In higher degree the lower bound `2 m` needs kernel elements that move the zeros independently,
which are not constructed here.

## Main results

* `TauCeti.Vortex.finiteDimensional_of_gaugeFixedOperator_eq_zero` and
  `TauCeti.Vortex.finrank_le_two_mul_card_of_gaugeFixedOperator_eq_zero`: a space of `C²`
  square-integrable kernel elements is finite dimensional, of dimension at most `2 |D|`.
* `TauCeti.Vortex.finiteDimensional_of_tendsto_sectionValue_mul_inv_pow` and
  `TauCeti.Vortex.finrank_le_two_mul_of_tendsto_sectionValue_mul_inv_pow`: the same for a vortex
  framed in degree `m`, with bound `2m`.
* `TauCeti.Vortex.two_le_finrank_gaugeFixedKernel`: `2 ≤ dim_ℝ ker L_x` at a framed vortex of
  positive degree.
* `TauCeti.Vortex.gaugeFixedKernel_eq_bot`: the kernel vanishes in degree zero.
* `TauCeti.Vortex.range_covariantTranslationLinearMap` and
  `TauCeti.Vortex.finrank_gaugeFixedKernel_eq_two`: in degree one the kernel consists exactly of
  the covariant translations, and has real dimension two.

## References

* T. M. Samols, *Vortex scattering*, Comm. Math. Phys. 145 (1992), 149–179.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

namespace TauCeti.Vortex

open Complex Filter MeasureTheory Module
open scoped Topology

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

/-! ### Covariant translations -/

section Translations

variable (hx : ContDiff ℝ 3 x) (hsol : ∀ z, equation x z = 0)

include hx hsol

/-- **Covariant translations lie in the kernel of `L_x`** at a `C³` vortex whose section has
modulus tending to one at infinity. -/
theorem covariantTranslation_mem_gaugeFixedKernel
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) (v : ℂ) :
    covariantTranslation x v ∈ gaugeFixedKernel x := by
  have hxi (i : Fin 4) : ContDiff ℝ 3 fun w ↦ x w i := contDiff_euclidean.mp hx i
  refine mem_gaugeFixedKernel.2 ⟨contDiff_covariantTranslation hx v,
    memLp_covariantTranslation volume ((hxi 0).differentiable (by norm_num))
      ((hxi 1).differentiable (by norm_num)) ((hxi 2).of_le (by norm_num))
      ((hxi 3).of_le (by norm_num)) hsol hlim v, fun z ↦ ?_⟩
  exact gaugeFixedOperator_covariantTranslation_of_equation_eq_zero
    ((hxi 0).differentiable (by norm_num) z) ((hxi 1).differentiable (by norm_num) z)
    ((hxi 2).of_le (by norm_num)).contDiffAt ((hxi 3).of_le (by norm_num)).contDiffAt
    (Eventually.of_forall hsol) v

variable {m : ℕ}
  (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))

include hframe

/-- The covariant translations span a subspace of the kernel of `L_x`. -/
theorem range_covariantTranslationLinearMap_le :
    LinearMap.range (covariantTranslationLinearMap x) ≤ gaugeFixedKernel x := by
  rintro _ ⟨v, rfl⟩
  rw [coe_covariantTranslationLinearMap]
  exact covariantTranslation_mem_gaugeFixedKernel hx hsol
    (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe) v

/-- At a framed vortex of positive degree the covariant translations span a real
two-dimensional subspace of the kernel of `L_x`. -/
theorem finrank_range_covariantTranslationLinearMap (hm : m ≠ 0) :
    finrank ℝ (LinearMap.range (covariantTranslationLinearMap x)) = 2 := by
  have hxi (i : Fin 4) : ContDiff ℝ 3 fun w ↦ x w i := contDiff_euclidean.mp hx i
  have hdx (i : Fin 4) : Differentiable ℝ fun w ↦ x w i := (hxi i).differentiable (by norm_num)
  obtain ⟨z₀, hz₀⟩ := exists_sectionValue_eq_zero (k := 3) (by norm_num) (hxi 0) (hxi 1) (hdx 2)
    (hdx 3) (fun w ↦ by simp [hsol w]) hm hframe
  rw [LinearMap.finrank_range_of_inj (by
      rw [coe_covariantTranslationLinearMap]
      exact covariantTranslation_injective (hdx 2) (hdx 3)
        (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe) hz₀),
    Complex.finrank_real_complex]

/-- **The kernel of `L_x` has real dimension at least two** at a `C³` framed vortex of positive
degree, spanned by the covariant translations. -/
theorem two_le_finrank_gaugeFixedKernel (hm : m ≠ 0) : 2 ≤ finrank ℝ (gaugeFixedKernel x) := by
  have := finiteDimensional_gaugeFixedKernel (hx.of_le (by norm_num))
    (fun w ↦ by simp [hsol w]) hframe
  rw [← finrank_range_covariantTranslationLinearMap hx hsol hframe hm]
  exact Submodule.finrank_mono (range_covariantTranslationLinearMap_le hx hsol hframe)

end Translations

/-! ### Degree one -/

/-- The degree-one end framing in the form `α (z / |z|)⁻ᵐ → 1` with `m = 1`. -/
private theorem tendsto_sectionValue_mul_inv_pow_one
    (hframe : Tendsto (fun z ↦ sectionValue x z * (z / (‖z‖ : ℂ))⁻¹) (cocompact ℂ) (𝓝 1)) :
    Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ 1)⁻¹) (cocompact ℂ) (𝓝 1) := by
  simpa using hframe

section DegreeOne

variable (hx : ContDiff ℝ 3 x) (hsol : ∀ z, equation x z = 0)
  (hframe : Tendsto (fun z ↦ sectionValue x z * (z / (‖z‖ : ℂ))⁻¹) (cocompact ℂ) (𝓝 1))

include hx hsol hframe

/-- **The kernel of `L_x` in degree one consists of the covariant translations.** At a `C³`
vortex with the degree-one end framing `α (z / |z|)⁻¹ → 1`, the square-integrable `C²` solutions
of `L_x y = 0` are exactly the covariant translations `y_v`, `v ∈ ℂ`. -/
theorem range_covariantTranslationLinearMap :
    LinearMap.range (covariantTranslationLinearMap x) = gaugeFixedKernel x := by
  have hframe₁ := tendsto_sectionValue_mul_inv_pow_one hframe
  have := finiteDimensional_gaugeFixedKernel (hx.of_le (by norm_num))
    (fun w ↦ by simp [hsol w]) hframe₁
  refine Submodule.eq_of_le_of_finrank_le (range_covariantTranslationLinearMap_le hx hsol hframe₁)
    ?_
  rw [finrank_range_covariantTranslationLinearMap hx hsol hframe₁ one_ne_zero]
  exact finrank_gaugeFixedKernel_le (hx.of_le (by norm_num)) (fun w ↦ by simp [hsol w]) hframe₁

/-- **The kernel of `L_x` in degree one has real dimension two**, the dimension of
`Sym¹ ℂ = ℂ`. -/
theorem finrank_gaugeFixedKernel_eq_two : finrank ℝ (gaugeFixedKernel x) = 2 := by
  rw [← range_covariantTranslationLinearMap hx hsol hframe,
    finrank_range_covariantTranslationLinearMap hx hsol
      (tendsto_sectionValue_mul_inv_pow_one hframe) one_ne_zero]

end DegreeOne

end TauCeti.Vortex
