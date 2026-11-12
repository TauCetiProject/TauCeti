/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.LogVariation
public import TauCeti.Analysis.PDE.Vortex.PrincipalPart
public import TauCeti.Analysis.PDE.Vortex.TranslationKernel
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The dimension of the kernel of the gauge-fixed operator at a plane vortex

At a plane vortex `x = (a, α)` the gauge-fixed linearization `L_x = d₀* ⊕ d₁`
(`TauCeti.Vortex.gaugeFixedOperator`) is expected to have kernel the tangent space of the moduli
space `Sym^m ℂ` of degree-`m` vortices, of real dimension `2 m`. This file proves the upper bound
`2 m` at every degree, and the identification itself in degrees zero and one, for the space
`gaugeFixedKernel x` of square-integrable `C²` classical solutions of `L_x y = 0`.

**The upper bound.** For a kernel element `y = (δa, δα)`, the quotient `η = δα / α` is a
`C²` function plus a meromorphic function with poles at the zeros of `α`, of order at most their
multiplicities. Its principal parts, `m` complex numbers in total, define a real-linear map on
the kernel (`TauCeti.Vortex.principalPartMap`). This map is injective: a kernel element whose
principal parts vanish has `δα = α η` with `η` of class `C²`, so `η` solves `Δη = |φ|² η` on the
whole plane and is square integrable, hence vanishes, and so does `y`
(`TauCeti.Vortex.eq_zero_of_gaugeFixedOperator_eq_zero_of_sectionValue_eq_mul_of_tendsto`).
Hence `dim_ℝ gaugeFixedKernel x ≤ 2 m` (`finrank_gaugeFixedKernel_le`). Only the holomorphicity
rows of the vortex equation and the degree-`m` end framing `α (z / |z|)⁻ᵐ → 1` enter.

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

## Main definitions

* `TauCeti.Vortex.gaugeFixedKernel x`: the square-integrable `C²` solutions of `L_x y = 0`.

## Main results

* `TauCeti.Vortex.finrank_gaugeFixedKernel_le`: `dim_ℝ ker L_x ≤ 2 m` at a framed degree-`m`
  field satisfying the holomorphicity rows.
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

open Complex Filter MeasureTheory Module Topology

variable {x y : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- **The `L²` kernel of the gauge-fixed operator.** The real vector space of `C²` variations `y`
that are square integrable and solve `L_x y = 0` classically at every point. -/
def gaugeFixedKernel (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    Submodule ℝ (ℂ → EuclideanSpace ℝ (Fin 4)) where
  carrier := {y | ContDiff ℝ 2 y ∧ MemLp y 2 volume ∧ ∀ z, gaugeFixedOperator x y z = 0}
  add_mem' {y v} hy hv := ⟨hy.1.add hv.1, hy.2.1.add hv.2.1, fun z ↦ by
    rw [gaugeFixedOperator_add x (hy.1.differentiable two_ne_zero z)
      (hv.1.differentiable two_ne_zero z), hy.2.2 z, hv.2.2 z, add_zero]⟩
  zero_mem' := ⟨contDiff_const, MemLp.zero, fun z ↦ by rw [gaugeFixedOperator_zero, Pi.zero_apply]⟩
  smul_mem' c y hy := ⟨hy.1.const_smul c, hy.2.1.const_smul c, fun z ↦ by
    rw [gaugeFixedOperator_smul, hy.2.2 z, smul_zero]⟩

/-- Membership in `gaugeFixedKernel x`: a square-integrable `C²` solution of `L_x y = 0`. -/
theorem mem_gaugeFixedKernel :
    y ∈ gaugeFixedKernel x ↔
      ContDiff ℝ 2 y ∧ MemLp y 2 volume ∧ ∀ z, gaugeFixedOperator x y z = 0 :=
  Iff.rfl

/-! ### The upper bound `2 m` -/

section UpperBound

variable {m : ℕ} (hx : ContDiff ℝ 2 x) (hhol : ∀ z, equation x z 1 = 0 ∧ equation x z 2 = 0)
  (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))

include hx hhol hframe

/-- Finite dimensionality and the bound `dim ≤ 2 m` for the kernel, from the injectivity of the
principal-part map on it. -/
private theorem finiteDimensional_and_finrank_gaugeFixedKernel_le :
    FiniteDimensional ℝ (gaugeFixedKernel x) ∧ finrank ℝ (gaugeFixedKernel x) ≤ 2 * m := by
  have hxi (i : Fin 4) : ContDiff ℝ (2 : ℕ∞) fun w ↦ x w i := contDiff_euclidean.mp hx i
  have hdx (i : Fin 4) : Differentiable ℝ fun w ↦ x w i := (hxi i).differentiable two_ne_zero
  -- Kernel elements have `C²` coordinates and satisfy the linearized holomorphicity rows.
  have hV (y : ℂ → EuclideanSpace ℝ (Fin 4)) (hy : y ∈ gaugeFixedKernel x) :
      ContDiff ℝ (2 : ℕ∞) (fun w ↦ y w 0) ∧ ContDiff ℝ (2 : ℕ∞) (fun w ↦ y w 1) ∧
        Differentiable ℝ (fun w ↦ y w 2) ∧ Differentiable ℝ (fun w ↦ y w 3) ∧
        ∀ w, linearizedEquation x y w 1 = 0 ∧ linearizedEquation x y w 2 = 0 := by
    obtain ⟨hyc, -, hker⟩ := hy
    have hyi (i : Fin 4) : ContDiff ℝ (2 : ℕ∞) fun w ↦ y w i := contDiff_euclidean.mp hyc i
    exact ⟨hyi 0, hyi 1, (hyi 2).differentiable two_ne_zero, (hyi 3).differentiable two_ne_zero,
      fun w ↦ ⟨by simpa using congrArg (· 2) (hker w), by simpa using congrArg (· 3) (hker w)⟩⟩
  -- A kernel element whose section variation is divisible by `α` vanishes.
  have hdiv (y : ℂ → EuclideanSpace ℝ (Fin 4)) (hy : y ∈ gaugeFixedKernel x) (η : ℂ → ℂ)
      (hη : ContDiff ℝ (2 : ℕ∞) η) (hyη : ∀ z, sectionValue y z = sectionValue x z * η z) :
      y = 0 :=
    eq_zero_of_gaugeFixedOperator_eq_zero_of_sectionValue_eq_mul_of_tendsto (μ := volume)
      (hx.of_le one_le_two) hhol (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe)
      hy.1.continuous hy.2.1 hy.2.2 hη hyη
  exact ⟨finiteDimensional_of_forall_sectionValue_eq_mul_eq_zero (by norm_num) (hxi 0) (hxi 1)
      (hdx 2) (hdx 3) hhol hframe hV hdiv,
    finrank_le_two_mul_of_forall_sectionValue_eq_mul_eq_zero (by norm_num) (hxi 0) (hxi 1)
      (hdx 2) (hdx 3) hhol hframe hV hdiv⟩

/-- **The kernel of `L_x` is finite dimensional** at a `C²` field satisfying the holomorphicity
rows of the vortex equation with the degree-`m` end framing. -/
theorem finiteDimensional_gaugeFixedKernel : FiniteDimensional ℝ (gaugeFixedKernel x) :=
  (finiteDimensional_and_finrank_gaugeFixedKernel_le hx hhol hframe).1

/-- **The kernel of `L_x` has real dimension at most `2 m`**, the real dimension of the tangent
space of `Sym^m ℂ`, at a `C²` field satisfying the holomorphicity rows of the vortex equation with
the degree-`m` end framing `α (z / |z|)⁻ᵐ → 1`. -/
theorem finrank_gaugeFixedKernel_le : finrank ℝ (gaugeFixedKernel x) ≤ 2 * m :=
  (finiteDimensional_and_finrank_gaugeFixedKernel_le hx hhol hframe).2

end UpperBound

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
  refine ⟨contDiff_covariantTranslation hx v,
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
