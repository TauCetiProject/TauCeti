/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.LogVariation
public import TauCeti.Analysis.PDE.Vortex.PrincipalPart
public import TauCeti.Analysis.PDE.Vortex.TranslationKernel
import TauCeti.Analysis.Meromorphic.PrincipalPart
import TauCeti.Analysis.PDE.Vortex.Kernel.Existence
import TauCeti.Analysis.Complex.Wirtinger.OpenSet
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The dimension of the kernel of the gauge-fixed operator at a plane vortex

Let `x` be a field whose holomorphicity rows `∂bar_a α = 0` vanish, with `|α| → 1` at infinity,
and let the zeros of its section `α`, counted with multiplicity, form the effective divisor `D`
(`TauCeti.Vortex.exists_multiset_isZeroMultiplicity_sectionValue_of_tendsto`).
This file proves that every real vector space of `C²` square-integrable solutions `y` of
`L_x y = 0`, for the gauge-fixed operator `L_x = d₀* ⊕ d₁` (`gaugeFixedOperator`), is finite
dimensional (`TauCeti.Vortex.finiteDimensional_of_gaugeFixedOperator_eq_zero`), of dimension at
most `2 |D|` (`TauCeti.Vortex.finrank_le_two_mul_card_of_gaugeFixedOperator_eq_zero`). For a
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

**The dimension `2 |D|` and the principal-part isomorphism.** For a smooth field, every single
pole of `δα / α` is realized: for each zero `a` of `α`, each order `j` below its multiplicity and
each `c ∈ ℂ` there is a smooth kernel element with `δα / α = c / (w - a)^(j+1) + ξ`, `ξ` smooth
(`TauCeti.Vortex.exists_gaugeFixedOperator_eq_zero_sectionValue_eq_mul_div_pow_add`). Taking
`c ∈ {1, i}` gives `2 |D|` smooth kernel elements, and they are linearly independent: in a
vanishing real combination the polar terms sum to a continuous function off the zeros, so their
coefficients vanish (`TauCeti.eq_zero_of_sum_div_sub_pow_eq`). With the upper bound `2 |D|` on
`gaugeFixedKernel x`, these smooth kernel elements span the whole `C²` kernel, so every element of
`gaugeFixedKernel x` is smooth (`contDiff_of_mem_gaugeFixedKernel`), `gaugeFixedKernel x` has real
dimension `2 |D|` (`finrank_gaugeFixedKernel_eq_two_mul_card`) and `2m` at a smooth framed
degree-`m` vortex (`finrank_gaugeFixedKernel_eq_two_mul`), and the injective map
`principalPartMap` is a real-linear isomorphism `gaugeFixedKernel x ≃ₗ[ℝ] (Multiset.ToType D → ℂ)`
(`principalPartEquiv`) realizing every principal-part datum by a smooth kernel element
(`exists_contDiff_gaugeFixedOperator_eq_zero_principalPart_eq`). This holds in every degree,
collisions of zeros included.

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
* `TauCeti.Vortex.finrank_gaugeFixedKernel_eq_two_mul_card` and
  `TauCeti.Vortex.finrank_gaugeFixedKernel_eq_two_mul`: at a smooth field the kernel has real
  dimension `2 |D|`, and `2m` in the framed degree-`m` case.
* `TauCeti.Vortex.contDiff_of_mem_gaugeFixedKernel`: every `y ∈ gaugeFixedKernel x` at a smooth
  field is smooth.
* `TauCeti.Vortex.principalPartEquiv` and
  `TauCeti.Vortex.exists_contDiff_gaugeFixedOperator_eq_zero_principalPart_eq`: at a smooth field,
  the principal-part map is a real-linear isomorphism
  `gaugeFixedKernel x ≃ₗ[ℝ] (Multiset.ToType D → ℂ)` realized by smooth kernel elements.

## References

* T. M. Samols, *Vortex scattering*, Comm. Math. Phys. 145 (1992), 149–179.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

namespace TauCeti.Vortex

open Complex Filter MeasureTheory Module
open scoped Topology ContDiff

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

omit [μ.IsAddHaarMeasure] in
/-- Decomposition `δα = α G + e^ν H` for every element of a space `V` of `C²` solutions of
`L_x y = 0`. -/
private theorem exists_decomposition_of_gaugeFixedOperator_eq_zero (hx : ContDiff ℝ 2 x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0) {ν : ℂ → ℂ}
    (hν : Differentiable ℝ ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2)
    (hV : ∀ y ∈ V, ContDiff ℝ 2 y ∧ MemLp y 2 μ ∧ ∀ w, gaugeFixedOperator x y w = 0) :
    ∀ y ∈ V, ∃ G : ℂ → ℂ, Continuous G ∧ ∃ H : ℂ → ℂ, Differentiable ℂ H ∧
      ∀ w, sectionValue y w = sectionValue x w * G w + exp (ν w) * H w := by
  have hi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ x w i := contDiff_euclidean.1 hx i
  have hlin := forall_mem_linearizedEquation_eq_zero hV
  intro y hy
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hlin y hy
  obtain ⟨G, hG, H, hH, hGH⟩ := exists_sectionValue_eq_mul_add_exp_mul (k := 2) (by norm_num)
    ((hi 2).differentiable (by simp)) ((hi 3).differentiable (by simp)) hhol hν hνeq h₁ h₂ h₃ h₄ h₅
  exact ⟨G, hG.continuous, H, hH, hGH⟩

/-- Injectivity of `principalPartMap` on any space `V` of `C²` square-integrable kernel elements,
requiring only real differentiability of the integrating factor `ν`. -/
private theorem principalPartMap_injective_of_gaugeFixedOperator_eq_zero (hx : ContDiff ℝ 2 x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) {ν : ℂ → ℂ}
    (hν : Differentiable ℝ ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2)
    (hV : ∀ y ∈ V, ContDiff ℝ 2 y ∧ MemLp y 2 μ ∧ ∀ w, gaugeFixedOperator x y w = 0) :
    Function.Injective (principalPartMap hD hν.continuous
      (exists_decomposition_of_gaugeFixedOperator_eq_zero hx hhol hν hνeq hV)) := by
  have hi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ x w i := contDiff_euclidean.1 hx i
  -- Upgrade `ν` to `C²` by comparing with a `C²` Dolbeault solution: their difference is entire.
  obtain ⟨ν₀, hν₀_on, hν₀eq⟩ := exists_contDiffOn_conjWirtingerDeriv_apply_one_eq (by norm_num)
    isOpen_univ (contDiff_connectionCoeff (hi 0) (hi 1)).contDiffOn
  have hν₀ : ContDiff ℝ 2 ν₀ := contDiffOn_univ.1 hν₀_on
  have hν₀d : Differentiable ℝ ν₀ := hν₀.differentiable (by norm_num)
  have hhol_diff : Differentiable ℂ (ν - ν₀) := fun w ↦
    (differentiableAt_iff_conjWirtingerDeriv_apply_one_eq_zero (hν.sub hν₀d w)).2 <| by
      rw [conjWirtingerDeriv_sub (hν w) (hν₀d w), FunLike.coe_sub, Pi.sub_apply, hνeq w,
        hν₀eq w (Set.mem_univ w), sub_self]
  have hν2 : ContDiff ℝ 2 ν := by
    simpa only [Pi.sub_apply, sub_add_cancel] using
      ((hhol_diff.contDiff (n := 2)).restrict_scalars ℝ).add hν₀
  exact principalPartMap_injective (k := 2) (by norm_num) (hi 0) (hi 1)
    ((hi 2).differentiable (by simp)) ((hi 3).differentiable (by simp)) hhol hD hν2 hνeq
    (forall_mem_linearizedEquation_eq_zero hV)
    (exists_decomposition_of_gaugeFixedOperator_eq_zero hx hhol hν hνeq hV)
    fun y hy η hη hyη ↦ eq_zero_of_gaugeFixedOperator_eq_zero_of_sectionValue_eq_mul_of_tendsto
      (hx.of_le one_le_two) hhol hlim (hV y hy).1.continuous (hV y hy).2.1 (hV y hy).2.2 hη hyη

/-- **The principal-part map on the kernel.** For a space `V` of `C²` square-integrable kernel
elements, the principal-part map `TauCeti.Vortex.principalPartMap` gives an injective real-linear
map from `V` to `ℂ^|D|`. -/
private theorem exists_injective_linearMap (hx : ContDiff ℝ 2 x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z)
    (hV : ∀ y ∈ V, ContDiff ℝ 2 y ∧ MemLp y 2 μ ∧ ∀ w, gaugeFixedOperator x y w = 0) :
    ∃ Φ : V →ₗ[ℝ] Multiset.ToType D → ℂ, Function.Injective Φ := by
  have hi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ x w i := contDiff_euclidean.1 hx i
  obtain ⟨ν, hν_on, hνeq⟩ := exists_contDiffOn_conjWirtingerDeriv_apply_one_eq (by norm_num)
    isOpen_univ (contDiff_connectionCoeff (hi 0) (hi 1)).contDiffOn
  have hν : ContDiff ℝ 2 ν := contDiffOn_univ.1 hν_on
  exact ⟨_, principalPartMap_injective_of_gaugeFixedOperator_eq_zero hx hhol hlim hD
    (hν.differentiable (by norm_num)) (fun w ↦ hνeq w (Set.mem_univ w)) hV⟩

/-- **Kernel elements of the gauge-fixed operator form a finite-dimensional space.** Let `x` be a
`C²` field with vanishing holomorphicity rows and `|α|² → 1` at infinity. Then every real vector
space of `C²` square-integrable solutions of `L_x y = 0` is finite dimensional. -/
theorem finiteDimensional_of_gaugeFixedOperator_eq_zero (hx : ContDiff ℝ 2 x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hV : ∀ y ∈ V, ContDiff ℝ 2 y ∧ MemLp y 2 μ ∧ ∀ w, gaugeFixedOperator x y w = 0) :
    FiniteDimensional ℝ V := by
  have hi (i : Fin 4) : ContDiff ℝ 1 fun w ↦ x w i := (contDiff_euclidean.1 hx i).of_le one_le_two
  obtain ⟨D, hD⟩ := exists_multiset_isZeroMultiplicity_sectionValue_of_tendsto (hi 0) (hi 1)
    ((hi 2).differentiable (by simp)) ((hi 3).differentiable (by simp)) hhol hlim
  obtain ⟨Φ, hΦ⟩ := exists_injective_linearMap hx hhol hlim hD hV
  exact FiniteDimensional.of_injective Φ hΦ

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
  have := finiteDimensional_of_gaugeFixedOperator_eq_zero hx hhol hlim hV
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
`C³` vortex whose section has modulus tending to one at infinity and a zero `z₀`, the covariant
translations span a two-dimensional subspace of `gaugeFixedKernel x`. -/
theorem two_le_finrank_gaugeFixedKernel_of_sectionValue_eq_zero
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {z₀ : ℂ}
    (hz₀ : sectionValue x z₀ = 0) :
    2 ≤ finrank ℝ (gaugeFixedKernel x) := by
  have hdx (i : Fin 4) : Differentiable ℝ fun w ↦ x w i :=
    (contDiff_euclidean.mp hx i).differentiable (by norm_num)
  have := finiteDimensional_of_gaugeFixedOperator_eq_zero (μ := volume) (hx.of_le (by norm_num))
    (fun w ↦ by simp [hsol w]) hlim fun _ ↦ mem_gaugeFixedKernel.1
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
  have := finiteDimensional_of_gaugeFixedOperator_eq_zero (hx.of_le (by norm_num)) hhol hlim hV
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
  obtain ⟨z₀, hz₀⟩ := exists_eq_zero_of_tendsto_mul_inv_pow (contDiff_sectionValue
    (contDiff_euclidean.mp hx 2) (contDiff_euclidean.mp hx 3)).continuous hm hframe
  exact two_le_finrank_gaugeFixedKernel_of_sectionValue_eq_zero hx hsol
    (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe) hz₀

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
    (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe₁) hD D.property

/-- **The kernel of `L_x` in degree one has real dimension two**, the dimension of
`Sym¹ ℂ = ℂ`. -/
theorem finrank_gaugeFixedKernel_eq_two : finrank ℝ (gaugeFixedKernel x) = 2 := by
  have hframe₁ : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ 1)⁻¹) (cocompact ℂ)
      (𝓝 1) := by
    simpa using hframe
  obtain ⟨D, hD⟩ := exists_sym_isZeroMultiplicity hx hsol hframe₁
  exact finrank_gaugeFixedKernel_eq_two_of_card_eq_one hx hsol
    (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe₁) hD D.property

end Translations

/-! ### The real dimension `2 |D|` and the principal-part isomorphism -/

/-- The real subspace of smooth square-integrable solutions of `L_x y = 0`. -/
private def smoothGaugeFixedKernel (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    Submodule ℝ (ℂ → EuclideanSpace ℝ (Fin 4)) where
  carrier := {y | ContDiff ℝ ∞ y ∧ MemLp y 2 volume ∧ ∀ z, gaugeFixedOperator x y z = 0}
  add_mem' {y v} hy hv := ⟨hy.1.add hv.1, hy.2.1.add hv.2.1, fun z ↦ by
    rw [gaugeFixedOperator_add x (hy.1.differentiable (by simp) z)
      (hv.1.differentiable (by simp) z), hy.2.2, hv.2.2, add_zero]⟩
  zero_mem' := ⟨contDiff_zero_fun, MemLp.zero, fun z ↦ by simp⟩
  smul_mem' t y hy := ⟨hy.1.const_smul t, hy.2.1.const_smul t, fun z ↦ by
    rw [gaugeFixedOperator_smul, hy.2.2, smul_zero]⟩

private theorem smoothGaugeFixedKernel_le :
    smoothGaugeFixedKernel x ≤ gaugeFixedKernel x :=
  fun _ hy ↦ mem_gaugeFixedKernel.2 ⟨hy.1.of_le (by simp), hy.2.1, hy.2.2⟩

section ZeroModes

variable (hx : ContDiff ℝ ∞ x) (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
  (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
  (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z)

include hx hhol hlim hD

/-- For a point `⟨a, j⟩` of the divisor `D` and `c ∈ ℂ`, a smooth kernel element of `L_x` whose
section variation is `δα = α (c / (w - a)^(j+1) + ξ)` off `a`, for a continuous function `ξ`. -/
private theorem exists_mem_smoothGaugeFixedKernel_sectionValue_eq (i : D.ToType) (c : ℂ) :
    ∃ y ∈ smoothGaugeFixedKernel x, ∃ ξ : ℂ → ℂ, Continuous ξ ∧ ∀ w, w ≠ i.1 →
      sectionValue y w = sectionValue x w * (c / (w - i.1) ^ ((i.2 : ℕ) + 1) + ξ w) := by
  obtain ⟨y, hy, hys, ξ, hξ, hyξ⟩ := exists_mem_gaugeFixedKernel_sectionValue_eq hx hhol hlim hD i c
  exact ⟨y, ⟨hys, (mem_gaugeFixedKernel.1 hy).2⟩, ξ, hξ, hyξ⟩

/-- **Smooth kernel elements with independent principal parts.** Choose, for each point `⟨a, j⟩` of
`D` and each `c ∈ {1, i}`, a smooth kernel element of `L_x` with
`δα / α = c / (w - a)^(j+1) + ξ`, `ξ` continuous. These `2 |D|` kernel elements are linearly
independent over `ℝ`: in a vanishing real combination, the polar terms at each point `a` of `D`
form a polynomial in `(w - a)⁻¹` without constant term that agrees near `a` with a function
continuous at `a`, so its coefficients vanish (`TauCeti.eq_zero_of_sum_div_sub_pow_eq`). -/
private theorem exists_linearIndependent :
    ∃ f : D.ToType × Fin 2 → smoothGaugeFixedKernel x, LinearIndependent ℝ f := by
  choose y hy ξ hξ hyξ using fun p : D.ToType × Fin 2 ↦
    exists_mem_smoothGaugeFixedKernel_sectionValue_eq hx hhol hlim hD p.1 (![1, I] p.2)
  refine ⟨fun p ↦ ⟨y p, hy p⟩, Fintype.linearIndependent_iff.2 fun g hg ↦ ?_⟩
  -- The complex coefficient of the pole at each point of `D`.
  set c : D.ToType → ℂ := fun i ↦ g (i, 0) + g (i, 1) * I
  suffices hc : ∀ i, c i = 0 by
    rintro ⟨i, b⟩
    have h : g (i, 0) = 0 ∧ g (i, 1) = 0 := by simpa [c, Complex.ext_iff] using hc i
    fin_cases b
    exacts [h.1, h.2]
  -- Off the zeros of `α`, the polar terms of the combination sum to a continuous function.
  refine congrFun (eq_zero_of_sum_div_sub_pow_eq (g := fun w ↦ -∑ p, (g p : ℂ) * ξ p w)
    (fun _ _ ↦ (continuous_finsetSum _ fun p _ ↦ continuous_const.mul (hξ p)).neg.continuousAt)
    fun w hw ↦ ?_)
  have hαw : sectionValue x w ≠ 0 := fun h ↦ hw (Multiset.count_pos.1 (hD.pos_iff.2 h))
  have hne (i : D.ToType) : w ≠ i.1 := fun h ↦ hw (h ▸ Multiset.coe_mem)
  have h0 := congrArg (fun F ↦ sectionValue F w) (congrArg Subtype.val hg)
  simp only [Submodule.coe_sum, Submodule.coe_smul, sectionValue_sum, sectionValue_smul,
    ZeroMemClass.coe_zero, sectionValue_zero] at h0
  rw [Finset.sum_congr rfl fun p _ ↦ by rw [hyξ p w (hne p.1)]] at h0
  have key : ∑ p : D.ToType × Fin 2, (g p : ℂ) * (sectionValue x w *
      (![1, I] p.2 / (w - p.1.1) ^ ((p.1.2 : ℕ) + 1) + ξ p w)) =
      sectionValue x w * (∑ i, c i / (w - i.1) ^ ((i.2 : ℕ) + 1) + ∑ p, (g p : ℂ) * ξ p w) := by
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, mul_add, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [c, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  rw [key] at h0
  exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.1 h0).resolve_left hαw)

/-- **The smooth kernel of `L_x` has real dimension at least `2 |D|`.** At a smooth field with
vanishing holomorphicity rows and `|α|² → 1` at infinity, whose section has zero divisor `D`, the
smooth kernel elements with prescribed single poles of
`TauCeti.Vortex.exists_gaugeFixedOperator_eq_zero_sectionValue_eq_mul_div_pow_add` span a subspace
of `smoothGaugeFixedKernel x` of real dimension `2 |D|`. -/
private theorem two_mul_card_le_finrank_smoothGaugeFixedKernel :
    2 * Multiset.card D ≤ finrank ℝ (smoothGaugeFixedKernel x) := by
  have := finiteDimensional_of_gaugeFixedOperator_eq_zero (μ := volume) (hx.of_le (by simp))
    hhol hlim fun _ hy ↦ mem_gaugeFixedKernel.1 (smoothGaugeFixedKernel_le hy)
  obtain ⟨f, hf⟩ := exists_linearIndependent hx hhol hlim hD
  simpa [Multiset.card_coe, mul_comm] using hf.fintype_card_le_finrank

/-- At a smooth field with `∂bar_a α = 0` and `|α|² → 1`, the `C^∞` and `C²` kernels coincide. -/
private theorem smoothGaugeFixedKernel_eq_gaugeFixedKernel :
    smoothGaugeFixedKernel x = gaugeFixedKernel x := by
  have hV (y : ℂ → EuclideanSpace ℝ (Fin 4)) (hy : y ∈ gaugeFixedKernel x) :=
    mem_gaugeFixedKernel.1 hy
  have := finiteDimensional_of_gaugeFixedOperator_eq_zero (hx.of_le (by simp)) hhol hlim hV
  exact Submodule.eq_of_le_of_finrank_le smoothGaugeFixedKernel_le
    ((finrank_le_two_mul_card_of_gaugeFixedOperator_eq_zero (hx.of_le (by simp)) hhol hlim
      hD hV).trans (two_mul_card_le_finrank_smoothGaugeFixedKernel hx hhol hlim hD))

/-- **The kernel of `L_x` has real dimension `2 |D|`.** Let `x` be a smooth field with vanishing
holomorphicity rows `∂bar_a α = 0` and `|α|² → 1` at infinity, whose section has zero divisor
`D`. Then the `C²` square-integrable kernel of the gauge-fixed operator `L_x` has real dimension
twice the degree of `D`, the real dimension of the space of principal parts of `δα / α` at the
zeros of `α`. -/
theorem finrank_gaugeFixedKernel_eq_two_mul_card :
    finrank ℝ (gaugeFixedKernel x) = 2 * Multiset.card D := by
  refine (finrank_le_two_mul_card_of_gaugeFixedOperator_eq_zero (μ := volume) (hx.of_le (by simp))
    hhol hlim hD fun _ ↦ mem_gaugeFixedKernel.1).antisymm ?_
  have h := two_mul_card_le_finrank_smoothGaugeFixedKernel hx hhol hlim hD
  rwa [smoothGaugeFixedKernel_eq_gaugeFixedKernel hx hhol hlim hD] at h

end ZeroModes

/-- **The kernel of `L_x` at a framed vortex has real dimension `2m`.** At a smooth field with
vanishing holomorphicity rows and the degree-`m` end framing `α(z) (z / |z|)⁻ᵐ → 1`, in
particular at a smooth framed degree-`m` vortex, the `C²` square-integrable kernel of the
gauge-fixed operator `L_x` has real dimension `2m`, the real dimension of the divisor space
`Sym^m ℂ`. -/
theorem finrank_gaugeFixedKernel_eq_two_mul {m : ℕ} (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    finrank ℝ (gaugeFixedKernel x) = 2 * m := by
  have hxi (k : Fin 4) : ContDiff ℝ ∞ fun w ↦ x w k := contDiff_euclidean.1 hx k
  obtain ⟨D, hD⟩ := exists_sym_isZeroMultiplicity_sectionValue (k := ⊤) le_top (hxi 0) (hxi 1)
    ((hxi 2).differentiable (by simp)) ((hxi 3).differentiable (by simp)) hhol hframe
  rw [finrank_gaugeFixedKernel_eq_two_mul_card hx hhol
    (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe) hD, Sym.card_coe]

/-- **Every classical kernel element at a smooth vortex is smooth.** If `x` is smooth with
`∂bar_a α = 0` and `|α|² → 1` at infinity, then every `y ∈ gaugeFixedKernel x` (assumed only `C²`)
is smooth (`C^∞`). -/
theorem contDiff_of_mem_gaugeFixedKernel (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ gaugeFixedKernel x) :
    ContDiff ℝ ∞ y := by
  have hi (i : Fin 4) : ContDiff ℝ 1 fun w ↦ x w i := (contDiff_euclidean.1 hx i).of_le (by simp)
  obtain ⟨D, hD⟩ := exists_multiset_isZeroMultiplicity_sectionValue_of_tendsto (hi 0) (hi 1)
    ((hi 2).differentiable (by simp)) ((hi 3).differentiable (by simp)) hhol hlim
  rw [← smoothGaugeFixedKernel_eq_gaugeFixedKernel hx hhol hlim hD] at hy
  exact hy.1

/-- At a smooth field with `∂bar_a α = 0` and `|α|² → 1`, `principalPartMap` on
`gaugeFixedKernel x` is bijective. -/
private theorem bijective_principalPartMap_gaugeFixedKernel (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) {ν : ℂ → ℂ}
    (hν : Differentiable ℝ ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2) :
    Function.Bijective (principalPartMap hD hν.continuous
      (exists_decomposition_of_gaugeFixedOperator_eq_zero (hx.of_le (by simp)) hhol hν hνeq
        fun _ ↦ mem_gaugeFixedKernel.1)) := by
  have hx2 : ContDiff ℝ 2 x := hx.of_le (by simp)
  have hV (y : ℂ → EuclideanSpace ℝ (Fin 4)) (hy : y ∈ gaugeFixedKernel x) :=
    mem_gaugeFixedKernel.1 hy
  have : FiniteDimensional ℝ (gaugeFixedKernel x) :=
    finiteDimensional_of_gaugeFixedOperator_eq_zero hx2 hhol hlim hV
  have hinj :=
    principalPartMap_injective_of_gaugeFixedOperator_eq_zero hx2 hhol hlim hD hν hνeq hV
  have hdim : finrank ℝ (gaugeFixedKernel x) = finrank ℝ (Multiset.ToType D → ℂ) := by
    rw [finrank_gaugeFixedKernel_eq_two_mul_card hx hhol hlim hD, Module.finrank_pi_fintype,
      Finset.sum_const, Complex.finrank_real_complex, smul_eq_mul, Finset.card_univ,
      Multiset.card_coe, mul_comm]
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj⟩

/-- **The principal-part isomorphism** (Taubes, Samols). At a smooth field `x` satisfying the
holomorphicity rows `∂bar_a α = 0` with `|α|² → 1` at infinity and zero divisor `D`, the
principal-part map identifies `gaugeFixedKernel x` real-linearly with `D → ℂ`. -/
noncomputable def principalPartEquiv (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) {ν : ℂ → ℂ}
    (hν : Differentiable ℝ ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2) :
    gaugeFixedKernel x ≃ₗ[ℝ] (Multiset.ToType D → ℂ) :=
  LinearEquiv.ofBijective
    (principalPartMap hD hν.continuous
      (exists_decomposition_of_gaugeFixedOperator_eq_zero (hx.of_le (by simp)) hhol hν hνeq
        fun _ ↦ mem_gaugeFixedKernel.1))
    (bijective_principalPartMap_gaugeFixedKernel hx hhol hlim hD hν hνeq)

/-- Evaluating `principalPartEquiv` at the point `⟨a, j⟩` of `D` gives
`principalPart x ν y a j`. -/
@[simp]
theorem principalPartEquiv_apply (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) {ν : ℂ → ℂ}
    (hν : Differentiable ℝ ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2)
    (y : gaugeFixedKernel x) (i : Multiset.ToType D) :
    principalPartEquiv hx hhol hlim hD hν hνeq y i = principalPart x ν y i.1 i.2 := by
  rw [principalPartEquiv, LinearEquiv.ofBijective_apply, principalPartMap_apply]

/-- **Every principal-part datum is realized by a smooth kernel element.** Let `x` be a smooth
field satisfying the holomorphicity rows `∂bar_a α = 0` with `|α|² → 1` at infinity and zero
divisor `D`, and let `∂bar ν = (b₂ - i b₁) / 2`. For every `p : D → ℂ` there is a smooth
square-integrable solution `y` of `L_x y = 0` whose principal-part data are `p`. -/
theorem exists_contDiff_gaugeFixedOperator_eq_zero_principalPart_eq (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) {ν : ℂ → ℂ}
    (hν : Differentiable ℝ ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2)
    (p : Multiset.ToType D → ℂ) :
    ∃ y : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ y ∧ MemLp y 2 volume ∧
      (∀ w, gaugeFixedOperator x y w = 0) ∧
      ∀ i : Multiset.ToType D, principalPart x ν y i.1 i.2 = p i := by
  let y := (principalPartEquiv hx hhol hlim hD hν hνeq).symm p
  obtain ⟨-, hyL, hker⟩ := mem_gaugeFixedKernel.1 y.property
  refine ⟨y, contDiff_of_mem_gaugeFixedKernel hx hhol hlim y.property, hyL, hker, fun i ↦ ?_⟩
  rw [← principalPartEquiv_apply hx hhol hlim hD hν hνeq, LinearEquiv.apply_symm_apply]

end TauCeti.Vortex
