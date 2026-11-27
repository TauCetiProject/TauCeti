/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.RCLike.Extend

import TauCeti.Geometry.Symplectic.Complex.Module.Basic

/-!
# Real and complex inner product compatibility and real-span isotropy

Let `E` be a seminormed group carrying both an `RCLike` inner product over `𝕜` (in particular `ℂ`)
and a real inner product for the same norm. Because both inner products satisfy the norm-square
identity on `(E, +, ‖·‖)`, polarization forces `⟪x, y⟫_ℝ = RCLike.re ⟪x, y⟫_𝕜`
(`TauCeti.inner_real_eq_re_inner`) without any separate compatibility hypothesis. This applies
simultaneously to `InnerProductSpace.rclikeToReal` (and `InnerProductSpace.complexToReal`) and to
spaces such as `EuclideanSpace ℂ ι` whose coordinatewise real inner product is only propositionally
equal to `Re ⟪·, ·⟫_ℂ`. For `𝕜 = ℂ` the imaginary part is then `Im ⟪x, y⟫_ℂ = ⟪i x, y⟫_ℝ`
(`TauCeti.im_inner_eq_real_inner_I_smul`). Multiplying both vectors by `ζ : 𝕜` scales their
`𝕜`-inner product by `‖ζ‖ ^ 2` (`TauCeti.inner_smul_smul`), so it preserves it when `‖ζ‖ = 1`
(`TauCeti.inner_smul_smul_of_norm_eq_one`), and on a space with a compatible real inner product it
scales the real inner product by `‖ζ‖ ^ 2` too (`TauCeti.real_inner_smul_smul`).

On any complex inner product space, Hermitian symmetry gives `Im ⟪x, x⟫_ℂ = 0`, so pairwise
vanishing of `Im ⟪·, ·⟫_ℂ` on a generating set `s` extends by `ℝ`-bilinearity to all pairs in
`Submodule.span ℝ s` (`Set.Pairwise.im_inner_eq_zero_of_mem_span`). Geometrically, this expresses
isotropy of the real span for the alternating form `Im ⟪·, ·⟫_ℂ` (the standard Kähler/symplectic
form when `E` is normed), which becomes the Lagrangian condition when the real span has half the
ambient real dimension.

Conversely, let `E` be a real inner product space with a compatible complex structure. The
complex-linear extension `⟪v, w⟫_ℂ = ⟪v, w⟫ - i ⟪v, i w⟫` of `⟪v, ·⟫`
(`Module.Dual.extendRCLike`) is complex-linear in `w` and real-linear in `v`. If multiplication by
`i` preserves the real inner product, as it does for the real part of a Hermitian metric, then it
is conjugate-linear in `v` (`TauCeti.extendRCLike_innerₗ_smul_left`) and Hermitian
(`TauCeti.conj_extendRCLike_innerₗ`): it is the Hermitian form whose real part is the given inner
product. Whether or not `i` preserves it, a real orthonormal basis `(bᵢ)` expands every
complex-linear functional as `l y = ½ ∑ᵢ l (bᵢ) ⟪bᵢ, y⟫_ℂ`
(`OrthonormalBasis.eq_sum_mul_extendRCLike_innerₗ`).

## Main results

* `TauCeti.inner_real_eq_re_inner`: `⟪x, y⟫_ℝ = RCLike.re ⟪x, y⟫_𝕜` whenever a `𝕜`-inner product
  (for `[RCLike 𝕜]`) and a real inner product share the same seminormed group structure.
* `TauCeti.im_inner_eq_real_inner_I_smul`: `Im ⟪x, y⟫_ℂ = ⟪i x, y⟫_ℝ` on such a space for `𝕜 = ℂ`.
* `TauCeti.inner_smul_smul`: `⟪ζ • x, ζ • y⟫_𝕜 = ‖ζ‖ ^ 2 * ⟪x, y⟫_𝕜` for `ζ : 𝕜`.
* `TauCeti.inner_smul_smul_of_norm_eq_one`: `⟪ζ • x, ζ • y⟫_𝕜 = ⟪x, y⟫_𝕜` when `‖ζ‖ = 1`.
* `TauCeti.real_inner_smul_smul`: `⟪ζ • x, ζ • y⟫_ℝ = ‖ζ‖ ^ 2 * ⟪x, y⟫_ℝ` for `ζ : 𝕜` on such a
  space.
* `Set.Pairwise.im_inner_eq_zero_of_mem_span`: if `Im ⟪x, y⟫_ℂ` vanishes for distinct elements of
  `s`, then `Im ⟪x, y⟫_ℂ = 0` for all `x, y ∈ Submodule.span ℝ s`.
* `TauCeti.extendRCLike_innerₗ_smul_left`, `TauCeti.conj_extendRCLike_innerₗ`: for an `i`-invariant
  real inner product, `⟪v, w⟫ - i ⟪v, i w⟫` is a Hermitian form.
* `OrthonormalBasis.eq_sum_mul_extendRCLike_innerₗ`: the expansion of a complex-linear functional
  in a real orthonormal basis.
* `TauCeti.sum_sum_mul_extendRCLike_innerₗ_eq`: the expansion of a complex-linear functional in a
  family of real orthonormal bases weighted by a partition of unity `∑ᵢ rᵢ² = 1`.
-/

public section

open scoped InnerProductSpace

namespace TauCeti

/-- On any seminormed space carrying both a `𝕜`-inner product (for an `RCLike` field `𝕜`) and a
real inner product for the same norm, the real inner product equals the real part of the
`𝕜`-inner product. -/
theorem inner_real_eq_re_inner (𝕜 : Type*) {E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [InnerProductSpace ℝ E] (x y : E) :
    ⟪x, y⟫_ℝ = RCLike.re ⟪x, y⟫_𝕜 := by
  linarith [norm_add_sq (𝕜 := 𝕜) x y, norm_add_sq_real x y]

/-- On any seminormed space carrying both a complex and a real inner product for the same norm,
the imaginary part of the complex inner product `⟪x, y⟫_ℂ` is the real inner product of `i x`
with `y`. -/
theorem im_inner_eq_real_inner_I_smul {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℂ E] [InnerProductSpace ℝ E] (x y : E) :
    (⟪x, y⟫_ℂ).im = ⟪Complex.I • x, y⟫_ℝ := by
  rw [inner_real_eq_re_inner ℂ, inner_smul_left]
  simp

/-- Multiplying both vectors by `ζ : 𝕜` scales their `𝕜`-inner product by `‖ζ‖ ^ 2`. -/
theorem inner_smul_smul {𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (ζ : 𝕜) (x y : E) :
    ⟪ζ • x, ζ • y⟫_𝕜 = (‖ζ‖ : 𝕜) ^ 2 * ⟪x, y⟫_𝕜 := by
  rw [inner_smul_left, inner_smul_right, ← mul_assoc, RCLike.conj_mul]

/-- Multiplying both vectors by a scalar `ζ : 𝕜` of norm one, such as a unit complex number,
does not change their `𝕜`-inner product. -/
theorem inner_smul_smul_of_norm_eq_one {𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {ζ : 𝕜} (hζ : ‖ζ‖ = 1) (x y : E) :
    ⟪ζ • x, ζ • y⟫_𝕜 = ⟪x, y⟫_𝕜 := by
  rw [inner_smul_smul, hζ, RCLike.ofReal_one, one_pow, one_mul]

/-- On any seminormed space carrying both a `𝕜`-inner product (for an `RCLike` field `𝕜`) and a
real inner product for the same norm, scalar multiplication by `ζ : 𝕜` scales the real inner
product by `‖ζ‖ ^ 2`. -/
theorem real_inner_smul_smul {𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [InnerProductSpace ℝ E] (ζ : 𝕜) (x y : E) :
    ⟪ζ • x, ζ • y⟫_ℝ = ‖ζ‖ ^ 2 * ⟪x, y⟫_ℝ := by
  rw [inner_real_eq_re_inner 𝕜, inner_real_eq_re_inner 𝕜, inner_smul_smul, ← RCLike.ofReal_pow,
    RCLike.re_ofReal_mul]

end TauCeti

namespace Set.Pairwise

/-- If `Im ⟪x, y⟫_ℂ = 0` for distinct elements of `s`, then `Im ⟪x, y⟫_ℂ = 0` for all
`x, y ∈ Submodule.span ℝ s`: the real span of `s` is isotropic for `Im ⟪·, ·⟫_ℂ`. -/
theorem im_inner_eq_zero_of_mem_span {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
    {s : Set E} (hs : s.Pairwise fun x y ↦ (⟪x, y⟫_ℂ).im = 0)
    {x y : E} (hx : x ∈ Submodule.span ℝ s) (hy : y ∈ Submodule.span ℝ s) :
    (⟪x, y⟫_ℂ).im = 0 := by
  induction hx using Submodule.span_induction with
  | mem u hu =>
    induction hy using Submodule.span_induction with
    | mem v hv =>
      rcases eq_or_ne u v with rfl | huv
      · exact inner_self_im (𝕜 := ℂ) u
      · exact hs hu hv huv
    | zero => simp
    | add y₁ y₂ _ _ hy₁ hy₂ => rw [inner_add_right, Complex.add_im, hy₁, hy₂, add_zero]
    | smul r y _ hy =>
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_real_right]
      simp [hy]
  | zero => simp
  | add x₁ x₂ _ _ hx₁ hx₂ => rw [inner_add_left, Complex.add_im, hx₁, hx₂, add_zero]
  | smul r x _ hx =>
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_real_left]
    simp [hx]

end Set.Pairwise

/-! ### The Hermitian form of an `i`-invariant real inner product -/

section ExtendRCLike

open ComplexConjugate

namespace TauCeti

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E] [Module ℂ E]
  [IsScalarTower ℝ ℂ E]

/-- The complex-linear extension of `⟪v, ·⟫` is `w ↦ ⟪v, w⟫ - i ⟪v, i w⟫`, with the coercion
`Complex.ofReal`. -/
theorem extendRCLike_innerₗ_apply (v w : E) :
    Module.Dual.extendRCLike (𝕜 := ℂ) (innerₗ E v) w =
      (⟪v, w⟫_ℝ : ℂ) - Complex.I * (⟪v, Complex.I • w⟫_ℝ : ℂ) := by
  rw [Module.Dual.extendRCLike_apply, innerₗ_apply_apply, innerₗ_apply_apply, RCLike.I_to_complex,
    RCLike.ofReal_eq_complex_ofReal]

/-- If multiplication by `i` preserves a real inner product, then `⟪i v, w⟫ = -⟪v, i w⟫`: the case
`J = i` of `TauCeti.AlmostComplexStructure.bilinForm_apply_left_eq_neg_apply_right`. -/
theorem real_inner_I_smul_left (hE : ∀ v w : E, ⟪Complex.I • v, Complex.I • w⟫_ℝ = ⟪v, w⟫_ℝ)
    (v w : E) : ⟪Complex.I • v, w⟫_ℝ = -⟪v, Complex.I • w⟫_ℝ := by
  simpa using (AlmostComplexStructure.ofComplexModule E).bilinForm_apply_left_eq_neg_apply_right
    (g := innerₗ E) (by simpa using hE) v w

/-- If multiplication by `i` preserves a real inner product, then the complex-linear extension
`⟪v, w⟫ - i ⟪v, i w⟫` of `⟪v, ·⟫` is conjugate-linear in `v`. -/
theorem extendRCLike_innerₗ_smul_left
    (hE : ∀ v w : E, ⟪Complex.I • v, Complex.I • w⟫_ℝ = ⟪v, w⟫_ℝ) (c : ℂ) (v w : E) :
    Module.Dual.extendRCLike (𝕜 := ℂ) (innerₗ E (c • v)) w =
      conj c * Module.Dual.extendRCLike (𝕜 := ℂ) (innerₗ E v) w := by
  have hc : c • v = c.re • v + c.im • (Complex.I • v) := by
    conv_lhs => rw [← Complex.re_add_im c]
    rw [add_smul, mul_smul, ← algebraMap_smul ℂ c.re v, ← algebraMap_smul ℂ c.im (Complex.I • v)]
    simp
  have hI : Module.Dual.extendRCLike (𝕜 := ℂ) (innerₗ E (Complex.I • v)) w =
      -Complex.I * Module.Dual.extendRCLike (𝕜 := ℂ) (innerₗ E v) w := by
    rw [extendRCLike_innerₗ_apply, extendRCLike_innerₗ_apply, hE, real_inner_I_smul_left hE]
    push_cast
    linear_combination -(⟪v, Complex.I • w⟫_ℝ : ℂ) * Complex.I_sq
  rw [← Module.Dual.extendRCLikeₗ_apply, hc]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    Module.Dual.extendRCLikeₗ_apply, hI, Complex.real_smul]
  conv_rhs => rw [← Complex.re_add_im c]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- If multiplication by `i` preserves a real inner product, then the complex-linear extension
`⟪v, w⟫ - i ⟪v, i w⟫` of `⟪v, ·⟫` is Hermitian. -/
theorem conj_extendRCLike_innerₗ (hE : ∀ v w : E, ⟪Complex.I • v, Complex.I • w⟫_ℝ = ⟪v, w⟫_ℝ)
    (v w : E) :
    conj (Module.Dual.extendRCLike (𝕜 := ℂ) (innerₗ E v) w) =
      Module.Dual.extendRCLike (𝕜 := ℂ) (innerₗ E w) v := by
  rw [extendRCLike_innerₗ_apply, extendRCLike_innerₗ_apply, real_inner_comm (Complex.I • v) w,
    real_inner_I_smul_left hE, real_inner_comm w v]
  simp only [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

end TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Module ℂ E]
  [IsScalarTower ℝ ℂ E]

/-- **Expansion in a real orthonormal basis.** If `b` is a real orthonormal basis of a complex
vector space `E` with a real inner product, every complex-linear functional `l` on `E` is
`l y = ½ ∑ᵢ l (bᵢ) ⟪bᵢ, y⟫_ℂ`, for the complex-linear extensions
`⟪v, y⟫_ℂ = ⟪v, y⟫ - i ⟪v, i y⟫` of `⟪v, ·⟫`. -/
theorem OrthonormalBasis.eq_sum_mul_extendRCLike_innerₗ {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (l : Module.Dual ℂ E) (y : E) :
    l y = 2⁻¹ * ∑ i, l (b i) * Module.Dual.extendRCLike (𝕜 := ℂ) (innerₗ E (b i)) y := by
  -- `l` is real-linear, so it is determined by its values on the real basis.
  have hl (z : E) : l z = ∑ i, (⟪b i, z⟫_ℝ : ℂ) * l (b i) := by
    conv_lhs => rw [← b.sum_repr' z]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← algebraMap_smul ℂ, map_smul, smul_eq_mul, Complex.coe_algebraMap]
  have hI : l (Complex.I • y) = Complex.I * l y := by rw [map_smul, smul_eq_mul]
  have h2 : ∑ i, l (b i) * Module.Dual.extendRCLike (𝕜 := ℂ) (innerₗ E (b i)) y =
      l y - Complex.I * l (Complex.I • y) := by
    rw [hl y, hl (Complex.I • y), Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [TauCeti.extendRCLike_innerₗ_apply]
    ring
  rw [h2, hI, ← mul_assoc, Complex.I_mul_I]
  ring

/-- **Expansion in a family of real orthonormal bases.** If `∑ᵢ rᵢ² = 1` and `(eᵢ a)ₐ` is a real
orthonormal basis of `E` whenever `rᵢ ≠ 0`, then every complex-linear functional `l` on `E` is
`l y = ∑ᵢ ∑ₐ ½ rᵢ l (eᵢ a) ⟪rᵢ eᵢ a, y⟫_ℂ`, for the complex-linear extensions
`⟪v, y⟫_ℂ = ⟪v, y⟫ - i ⟪v, i y⟫` of `⟪v, ·⟫`. -/
theorem TauCeti.sum_sum_mul_extendRCLike_innerₗ_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    {r : ι → ℝ} (hr : ∑ i, r i ^ 2 = 1) {e : ι → κ → E}
    (he : ∀ i, r i ≠ 0 → Orthonormal ℝ (e i) ∧ ⊤ ≤ Submodule.span ℝ (Set.range (e i)))
    (l : Module.Dual ℂ E) (y : E) :
    ∑ i, ∑ a, 2⁻¹ * (r i * l (e i a)) *
      Module.Dual.extendRCLike (𝕜 := ℂ) (innerₗ E (r i • e i a)) y = l y := by
  have key (i : ι) : ∑ a, 2⁻¹ * (r i * l (e i a)) *
      Module.Dual.extendRCLike (𝕜 := ℂ) (innerₗ E (r i • e i a)) y = ((r i ^ 2 : ℝ) : ℂ) * l y := by
    by_cases hri : r i = 0
    · simp [hri]
    obtain ⟨hon, hsp⟩ := he i hri
    rw [(OrthonormalBasis.mk hon hsp).eq_sum_mul_extendRCLike_innerₗ l y, OrthonormalBasis.coe_mk,
      Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    simp only [TauCeti.extendRCLike_innerₗ_apply, real_inner_smul_left]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun i _ ↦ key i, ← Finset.sum_mul, ← Complex.ofReal_sum, hr,
    Complex.ofReal_one, one_mul]

end ExtendRCLike
