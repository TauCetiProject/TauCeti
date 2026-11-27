/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.Symplectic.Complex.InnerProductSpace

/-!
# The `(0,1)`-covectors of an orthogonal complex structure

Let `J` be an orthogonal complex structure on a real inner product space `V`. A `(0,1)`-covector
of `(V, J)` is a real-linear functional `D : V → ℂ` that is complex antilinear,
`D (J w) = -i D w` (`TauCeti.AlmostComplexStructure.zeroOneCovectors`); these form a complex
vector space, the fibre of `Λ^(0,1)` on an almost complex manifold. The complex-antilinear part
`∂bar L w = (L w + i L (J w)) / 2` of a real-linear `L : V → ℂ` is such a covector.

**The metric isomorphism.** The `(0,1)`-part of the metric dual of a vector `v`, doubled, is

`v♭ w = ⟪v, w⟫ - i ⟪J v, w⟫`

(`TauCeti.AlmostComplexStructure.zeroOneFlat`), the conjugate of the Hermitian inner product
of `(V, J)` (`TauCeti.AlmostComplexStructure.zeroOneFlat_apply_apply_eq_conj_inner`). It is a
`(0,1)`-covector
(`TauCeti.AlmostComplexStructure.zeroOneFlat_mem_zeroOneCovectors`), it turns `J` into `i`,
`(J v)♭ = i v♭` (`TauCeti.AlmostComplexStructure.zeroOneFlat_apply_left`), and its real part is
the metric dual of `v`. So `v ↦ v♭` is a complex linear isomorphism from `V`, with the complex
structure `J`, onto its `(0,1)`-covectors, when `V` is complete
(`TauCeti.AlmostComplexStructure.zeroOneFlatEquiv`).

**`∂bar` in the metric.** If `g₁` and `p` represent the real and imaginary parts of `L`, then
`2 ∂bar L = (g₁ + J p)♭` (`TauCeti.AlmostComplexStructure.zeroOneFlat_add_apply_apply`,
`TauCeti.AlmostComplexStructure.zeroOneFlat_add_eq_two_smul_complexAntilinearPart`): the vector
`g₁ + J p` of `TauCeti.Geometry.Symplectic.Complex.AntilinearPart` is the vector metrically dual to
`2 ∂bar L`.

**The Hermitian metric.** In every orthonormal basis `b`, the Hilbert–Schmidt pairing of two such
covectors is twice the Hermitian form of `(V, J)`,

`∑ᵢ conj (v♭ bᵢ) w♭ bᵢ = 2 (⟪v, w⟫ - i ⟪v, J w⟫)`

(`TauCeti.AlmostComplexStructure.sum_conj_zeroOneFlat_mul_zeroOneFlat`), so taking `w = v`,
`∑ᵢ |v♭ bᵢ|² = 2 ‖v‖²` (`TauCeti.AlmostComplexStructure.sum_norm_sq_zeroOneFlat`).

Through Clifford multiplication on the canonical spinor these identify the negative half-spinors
of the canonical `Spinᶜ` structure of an almost Hermitian four-manifold with `Λ^(0,1)`
(`TauCeti.OrthonormalFrameBundle.canonicalNegativeHalfSpinorZeroOneEquiv`), and the Dirac symbol
on the canonical line with `2 ∂bar`
(`TauCeti.SeibergWitten.sum_smul_ι_apply_eq_ι_apply_of_zeroOneFlat_apply_eq`).

## Main definitions

* `TauCeti.AlmostComplexStructure.zeroOneCovectors`: the complex-antilinear real functionals.
* `TauCeti.AlmostComplexStructure.zeroOneFlat`: `v ↦ ⟪v, ·⟫ - i ⟪J v, ·⟫`.
* `TauCeti.AlmostComplexStructure.zeroOneFlatEquiv`: the complex linear isomorphism of `(V, J)`
  with its `(0,1)`-covectors.

## Main results

* `TauCeti.AlmostComplexStructure.zeroOneFlat_add_apply_apply`: `2 ∂bar L = (g₁ + J p)♭`.
* `TauCeti.AlmostComplexStructure.sum_conj_zeroOneFlat_mul_zeroOneFlat`: the Hilbert–Schmidt
  pairing is twice the Hermitian form.

## References

* D. Huybrechts, *Complex Geometry*, Springer, 2005, Section 1.2.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989,
  Appendix D.
-/

public section

noncomputable section

open Complex
open scoped ComplexConjugate RealInnerProductSpace

namespace TauCeti.AlmostComplexStructure

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (J : AlmostComplexStructure V)

/-! ### The `(0,1)`-covectors -/

/-- **The `(0,1)`-covectors** of a complex structure `J`: the real-linear functionals
`D : V → ℂ` that are complex antilinear, `D (J w) = -i D w`. They form a complex subspace of the
real-linear functionals. -/
def zeroOneCovectors : Submodule ℂ (V →L[ℝ] ℂ) where
  carrier :=
    {D | IsComplexAntilinear J.toLinearMap (DistribSMul.toLinearMap ℝ ℂ I) (D : V →ₗ[ℝ] ℂ)}
  add_mem' hD hD' := hD.add hD'
  zero_mem' := isComplexAntilinear_zero
  smul_mem' z D hD := isComplexAntilinear_of_apply fun w ↦ by
    simp only [ContinuousLinearMap.toLinearMap_smul, LinearMap.smul_apply,
      ContinuousLinearMap.coe_coe, DistribSMul.toLinearMap_apply, smul_eq_mul, hD.apply w]
    ring

variable {J}

/-- A `(0,1)`-covector is complex antilinear, for `J` on `V` and multiplication by `i` on `ℂ`. -/
theorem mem_zeroOneCovectors_iff_isComplexAntilinear {D : V →L[ℝ] ℂ} :
    D ∈ zeroOneCovectors J ↔
      IsComplexAntilinear J.toLinearMap (DistribSMul.toLinearMap ℝ ℂ I) (D : V →ₗ[ℝ] ℂ) :=
  Iff.rfl

/-- The pointwise form of membership: `D (J w) = -i D w` for every `w`. -/
@[simp]
theorem mem_zeroOneCovectors {D : V →L[ℝ] ℂ} :
    D ∈ zeroOneCovectors J ↔ ∀ w, D (J w) = -(I * D w) :=
  ⟨fun hD w ↦ hD.apply w, fun hD ↦ isComplexAntilinear_of_apply hD⟩

/-! ### The metric isomorphism -/

variable (J) in
/-- **The `(0,1)`-part of the metric dual**, doubled: `v♭ w = ⟪v, w⟫ - i ⟪J v, w⟫`. For an
orthogonal `J` on a complete space it is a complex linear isomorphism from `(V, J)` onto the
`(0,1)`-covectors (`TauCeti.AlmostComplexStructure.zeroOneFlatEquiv`). -/
def zeroOneFlat : V →ₗ[ℝ] V →L[ℝ] ℂ where
  toFun v := ofRealCLM.comp (innerSL ℝ v) - I • ofRealCLM.comp (innerSL ℝ (J v))
  map_add' v w := by
    ext u
    simp only [sub_apply, add_apply,
      smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      ofRealCLM_apply, map_add, smul_eq_mul]
    ring
  map_smul' r v := by
    ext u
    simp only [sub_apply, smul_apply,
      ContinuousLinearMap.comp_apply, innerSL_apply_apply, ofRealCLM_apply, map_smul,
      RingHom.id_apply, ofReal_mul, smul_eq_mul, real_smul]
    ring

@[simp]
theorem zeroOneFlat_apply_apply (v w : V) :
    zeroOneFlat J v w = (⟪v, w⟫ : ℂ) - ⟪J v, w⟫ * I := by
  simp [zeroOneFlat, mul_comm I]

theorem re_zeroOneFlat_apply_apply (v w : V) : (zeroOneFlat J v w).re = ⟪v, w⟫ := by
  simp

theorem im_zeroOneFlat_apply_apply (v w : V) : (zeroOneFlat J v w).im = -⟪J v, w⟫ := by
  simp

/-- **`J` becomes `i`**: `(J v)♭ = i v♭`. -/
theorem zeroOneFlat_apply_left (v : V) : zeroOneFlat J (J v) = I • zeroOneFlat J v := by
  ext w
  simp only [zeroOneFlat_apply_apply, apply_apply, inner_neg_left, ofReal_neg,
    smul_apply, smul_eq_mul]
  linear_combination (⟪J v, w⟫ : ℂ) * I_sq

/-- The metric dual of `v` is the real part of `v♭`, so `v ↦ v♭` is injective. -/
theorem zeroOneFlat_injective : Function.Injective (zeroOneFlat J) := by
  intro v w h
  refine ext_inner_left ℝ fun u ↦ ?_
  rw [real_inner_comm v u, real_inner_comm w u, ← re_zeroOneFlat_apply_apply (J := J), h,
    re_zeroOneFlat_apply_apply]

/-- `v♭ w` is the conjugate of the Hermitian inner product `⟪v, w⟫ + i ⟪J v, w⟫` of `(V, J)`
(`TauCeti.AlmostComplexStructure.complexInnerProductSpace`). -/
theorem zeroOneFlat_apply_apply_eq_conj_inner (hJ : ∀ v, ‖J v‖ = ‖v‖) (v w : V) :
    letI := J.complexInnerProductSpace hJ
    zeroOneFlat J v w = conj (inner ℂ v w) := by
  let := J.complexInnerProductSpace hJ
  rw [complexInnerProductSpace_inner, zeroOneFlat_apply_apply]
  simp only [map_add, map_mul, conj_ofReal, conj_I]
  ring

variable (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫)
include hJ

/-- **`v♭` is a `(0,1)`-covector** when `J` is orthogonal: `v♭ (J w) = -i v♭ w`. -/
theorem zeroOneFlat_mem_zeroOneCovectors (v : V) : zeroOneFlat J v ∈ zeroOneCovectors J := by
  refine mem_zeroOneCovectors.2 fun w ↦ ?_
  have h : ⟪v, J w⟫ = -⟪J v, w⟫ := by
    rw [real_inner_comm, inner_apply_left_eq_neg_swap hJ]
  simp only [zeroOneFlat_apply_apply, hJ, h, ofReal_neg]
  linear_combination -(⟪J v, w⟫ : ℂ) * I_sq

/-- **Every `(0,1)`-covector is `v♭`**, on a complete space, for the vector `v` metrically dual to
its real part. -/
theorem exists_zeroOneFlat_eq [CompleteSpace V] {D : V →L[ℝ] ℂ} (hD : D ∈ zeroOneCovectors J) :
    ∃ v, zeroOneFlat J v = D := by
  refine ⟨(InnerProductSpace.toDual ℝ V).symm (reCLM.comp D), ?_⟩
  set v := (InnerProductSpace.toDual ℝ V).symm (reCLM.comp D)
  have hv (w : V) : ⟪v, w⟫ = (D w).re := by
    rw [InnerProductSpace.toDual_symm_apply]
    simp
  ext w
  apply Complex.ext
  · rw [re_zeroOneFlat_apply_apply, hv]
  · -- The imaginary part of `D w` is the real part of `D (J w) = -i D w`.
    rw [im_zeroOneFlat_apply_apply, inner_apply_left_eq_neg_swap hJ, neg_neg, real_inner_comm,
      hv, mem_zeroOneCovectors.1 hD w]
    simp

/-- **`(V, J)` is isomorphic to its `(0,1)`-covectors** through the metric, for an orthogonal `J`
on a complete space: `v ↦ v♭ = ⟪v, ·⟫ - i ⟪J v, ·⟫` is complex linear for the complex structure
`J` of `V`, and bijective. -/
def zeroOneFlatEquiv [CompleteSpace V] :
    letI := J.complexModule
    V ≃ₗ[ℂ] zeroOneCovectors J :=
  letI := J.complexModule
  LinearEquiv.ofBijective
    { toFun v := ⟨zeroOneFlat J v, zeroOneFlat_mem_zeroOneCovectors hJ v⟩
      map_add' v w := Subtype.ext (map_add _ v w)
      map_smul' z v := Subtype.ext <| by
        simp only [Submodule.coe_smul]
        ext w
        rw [complexModule_smul_def, map_add, map_smul, map_smul, zeroOneFlat_apply_left]
        simp only [add_apply, smul_apply, real_smul, smul_eq_mul]
        linear_combination (zeroOneFlat J v w) * re_add_im z }
    ⟨fun v w h ↦ zeroOneFlat_injective (congrArg Subtype.val h), fun D ↦
      (exists_zeroOneFlat_eq hJ D.property).imp fun _ h ↦ Subtype.ext h⟩

@[simp]
theorem coe_zeroOneFlatEquiv_apply [CompleteSpace V] (v : V) :
    (zeroOneFlatEquiv hJ v : V →L[ℝ] ℂ) = zeroOneFlat J v :=
  (rfl)

/-- The inverse of `v ↦ v♭` sends a `(0,1)`-covector `D` to the vector `v` with `v♭ = D`. -/
@[simp]
theorem zeroOneFlat_zeroOneFlatEquiv_symm_apply [CompleteSpace V] (D : zeroOneCovectors J) :
    zeroOneFlat J ((zeroOneFlatEquiv hJ).symm D) = D := by
  rw [← coe_zeroOneFlatEquiv_apply hJ, LinearEquiv.apply_symm_apply]

/-! ### `∂bar` in the metric -/

/-- **`2 ∂bar L = (g₁ + J p)♭`.** If `g₁` and `p` represent the real and imaginary parts of
`L : V → ℂ`, then `(g₁ + J p)♭ w = L w + i L (J w)` for every `w`. -/
theorem zeroOneFlat_add_apply_apply {L : V → ℂ} {g₁ p : V} (h₁ : ∀ v, ⟪g₁, v⟫ = (L v).re)
    (h₂ : ∀ v, ⟪p, v⟫ = (L v).im) (w : V) :
    zeroOneFlat J (g₁ + J p) w = L w + I * L (J w) := by
  apply Complex.ext
  · rw [re_zeroOneFlat_apply_apply, inner_add_left, h₁, inner_apply_left_eq_neg_swap hJ,
      real_inner_comm, h₂]
    simp
  · rw [im_zeroOneFlat_apply_apply, map_add, apply_apply, inner_add_left, inner_neg_left,
      inner_apply_left_eq_neg_swap hJ, real_inner_comm g₁ (J w), h₁, h₂]
    simp

/-- **`2 ∂bar L = (g₁ + J p)♭`** for the complex-antilinear part of a real-linear `L`, for `J` on
`V` and multiplication by `i` on `ℂ`. -/
theorem zeroOneFlat_add_eq_two_smul_complexAntilinearPart {L : V →L[ℝ] ℂ} {g₁ p : V}
    (h₁ : ∀ v, ⟪g₁, v⟫ = (L v).re) (h₂ : ∀ v, ⟪p, v⟫ = (L v).im) :
    (zeroOneFlat J (g₁ + J p) : V →ₗ[ℝ] ℂ) =
      (2 : ℝ) • complexAntilinearPart J.toLinearMap (DistribSMul.toLinearMap ℝ ℂ I)
        (L : V →ₗ[ℝ] ℂ) := by
  ext w
  rw [ContinuousLinearMap.coe_coe, zeroOneFlat_add_apply_apply hJ h₁ h₂, LinearMap.smul_apply,
    complexAntilinearPart_apply]
  simp only [ContinuousLinearMap.coe_coe, DistribSMul.toLinearMap_apply, smul_eq_mul,
    smul_add, real_smul, ofReal_inv, ofReal_ofNat]
  ring

/-! ### The Hermitian metric -/

/-- **The Hilbert–Schmidt pairing of `(0,1)`-covectors is twice the Hermitian form**: in every
orthonormal basis, `∑ᵢ conj (v♭ bᵢ) w♭ bᵢ = 2 (⟪v, w⟫ - i ⟪v, J w⟫)`. -/
theorem sum_conj_zeroOneFlat_mul_zeroOneFlat {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (v w : V) :
    ∑ i, conj (zeroOneFlat J v (b i)) * zeroOneFlat J w (b i) =
      2 * ((⟪v, w⟫ : ℂ) - ⟪v, J w⟫ * I) := by
  have hsum (x y : V) : ∑ i, ⟪x, b i⟫ * ⟪y, b i⟫ = ⟪x, y⟫ := by
    simpa only [real_inner_comm (b _) y] using b.sum_inner_mul_inner x y
  have h : ⟪v, J w⟫ = -⟪J v, w⟫ := by
    rw [real_inner_comm, inner_apply_left_eq_neg_swap hJ]
  apply Complex.ext
  · simp only [re_sum, mul_re, conj_re, conj_im, re_zeroOneFlat_apply_apply,
      im_zeroOneFlat_apply_apply]
    simp only [mul_neg, neg_neg, sub_neg_eq_add]
    rw [Finset.sum_add_distrib, hsum, hsum, hJ]
    simp only [re_ofNat, sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, sub_zero, im_ofNat, sub_im, mul_im, add_zero, zero_sub, mul_neg, zero_mul, neg_zero]
    ring
  · simp only [im_sum, mul_im, conj_re, conj_im, re_zeroOneFlat_apply_apply,
      im_zeroOneFlat_apply_apply]
    simp only [mul_neg, neg_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib, hsum]
    simp only [h, neg_neg, re_ofNat, ofReal_neg, neg_mul, sub_neg_eq_add, add_im, ofReal_im,
      mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero, zero_add, im_ofNat, add_re,
      mul_re, sub_self, zero_mul]
    ring

/-- **The Hilbert–Schmidt norm of `v♭`** is `√2 ‖v‖`: in every orthonormal basis,
`∑ᵢ |v♭ bᵢ|² = 2 ‖v‖²`. -/
theorem sum_norm_sq_zeroOneFlat {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V) (v : V) :
    ∑ i, ‖zeroOneFlat J v (b i)‖ ^ 2 = 2 * ‖v‖ ^ 2 := by
  -- The real part of the Hilbert–Schmidt pairing of `v♭` with itself.
  have h := congrArg re (sum_conj_zeroOneFlat_mul_zeroOneFlat hJ b v v)
  simp only [re_sum, conj_mul', ← ofReal_pow, ofReal_re] at h
  rw [h, inner_self_apply hJ, real_inner_self_eq_norm_sq]
  simp [-ofReal_pow]

end TauCeti.AlmostComplexStructure
