/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.Calculus.Bilinear
public import TauCeti.Analysis.Complex.LeviForm
public import TauCeti.Analysis.SpecialFunctions.Complex.Arg
public import TauCeti.LinearAlgebra.QuadraticForm.Signature

/-!
# Levi forms and inertia of complex quadratic functions

This file computes the Levi form and the Morse index of the basic quadratic functions on a complex
vector space: a positive Hermitian quadratic function, the real part of a holomorphic quadratic
form, and their sums. They are the model cases for the comparison between the Levi form and the
real Morse index.

* The Levi form of a real quadratic function `z ↦ B z z` is the Levi form of its polarization
  `B.flip + B`. For the squared norm of a complex inner product space it is the inner product
  itself. Every positive definite Hermitian form on a finite-dimensional complex space is the
  inner product of some inner product space structure, so this is the general positive Hermitian
  quadratic function.
* The real part of a holomorphic quadratic form has vanishing Levi form, so by
  `TauCeti.morseIndex_eq_finrank_of_leviForm_eq_zero` its Morse index is exactly the complex
  dimension when it is nondegenerate.
* For an orthonormal basis `b` of a finite-dimensional complex inner product space of complex
  dimension `n`, the function `a ‖z‖² + Re (c ∑ⱼ ⟪b j, z⟫²)` has Levi form `a ⟪·, ·⟫` and Morse
  index `n [a < ‖c‖] + n [a < -‖c‖]`. In coordinates it is
  `a ∑ⱼ |zⱼ|² + Re (c ∑ⱼ zⱼ²)`; for `a > 0` it is strictly plurisubharmonic, and its Morse index
  jumps from `0` to the complex dimension when `‖c‖` crosses `a`.

## Main results

* `ContinuousLinearMap.leviForm_apply_self`: the Levi form of `z ↦ B z z`.
* `TauCeti.leviForm_norm_sq`: the Levi form of `‖z‖²` is the inner product.
* `TauCeti.leviForm_mul_norm_sq_add_re_mul_sum_inner_sq`,
  `TauCeti.morseIndex_mul_norm_sq_add_re_mul_sum_inner_sq`: the Levi form and the Morse index of
  `a ‖z‖² + Re (c ∑ⱼ ⟪b j, z⟫²)`.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, Section 7.
* R. Hain, *Notes on the Morse theory of complex manifolds*.
-/

public section

open Complex ComplexConjugate ContinuousLinearMap Module
open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The Levi form of the real quadratic function `z ↦ B z z` is the Levi form of the
polarization `B.flip + B`, at every point. -/
theorem ContinuousLinearMap.leviForm_apply_self (B : V →L[ℝ] V →L[ℝ] ℝ) (x : V) :
    TauCeti.leviForm (fun z ↦ B z z) x = (B.flip + B).toBilinForm.leviForm := by
  rw [TauCeti.leviForm_def, fderiv_fderiv_apply_self]

namespace TauCeti

section InnerProductSpace

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Fintype ι]

/-- **The Levi form of the squared norm** of a complex inner product space is the inner product,
at every point. -/
theorem leviForm_norm_sq (x : E) : leviForm (fun z : E ↦ ‖z‖ ^ 2) x = innerₛₗ ℂ := by
  let _ : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
  have h : (fun z : E ↦ ‖z‖ ^ 2) = fun z ↦ innerSL ℝ z z := by
    funext z
    simp
  rw [h, (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).leviForm_apply_self]
  -- The real inner product of the complex space is the real part of the complex one.
  have hinner (u u' : E) : innerSL ℝ u u' = (⟪u, u'⟫_ℂ).re := by
    simp [real_inner_eq_re_inner ℂ]
  ext v w
  apply Complex.ext <;> simp [hinner, inner_smul_left, inner_smul_right] <;> ring

private theorem re_inner_self (z : E) : (⟪z, z⟫_ℂ).re = ‖z‖ ^ 2 :=
  inner_self_eq_norm_sq (𝕜 := ℂ) z

/-- The function `a ‖z‖² + Re (c ∑ⱼ ⟪b j, z⟫²)` is `z ↦ B z z` for a real bilinear form `B`
whose holomorphic part is a complex bilinear form `Q`. -/
private theorem exists_bilinear_apply_self_eq (b : OrthonormalBasis ι ℂ E) (a : ℝ) (c : ℂ) :
    ∃ (Q : E →L[ℂ] E →L[ℂ] ℂ) (B : E →L[ℝ] E →L[ℝ] ℝ),
      (∀ v, Q v v = c * ∑ j, ⟪b j, v⟫_ℂ ^ 2) ∧
        ∀ v w, B v w = a * (⟪v, w⟫_ℂ).re + (Q v w).re := by
  let _ : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
  let Q : E →L[ℂ] E →L[ℂ] ℂ :=
    c • ∑ j, (ContinuousLinearMap.mul ℂ ℂ).bilinearComp (innerSL ℂ (b j)) (innerSL ℂ (b j))
  let J : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ
  refine ⟨Q, a • J + (compL ℝ E ℂ ℝ reCLM).comp (Q.bilinearRestrictScalars ℝ), fun v ↦ ?_,
    fun v w ↦ ?_⟩
  · simp [Q, sq]
  · simp only [J, add_apply, smul_apply, comp_apply, compL_apply,
      bilinearRestrictScalars_apply_apply, reCLM_apply, smul_eq_mul]
    rw [innerSL_apply_apply, real_inner_eq_re_inner ℂ, RCLike.re_to_complex]

private theorem hessianQuadraticForm_mul_norm_sq_add_re_mul_sum_inner_sq
    (b : OrthonormalBasis ι ℂ E) (a : ℝ) (c : ℂ) (x v : E) :
    hessianQuadraticForm (fun z ↦ a * ‖z‖ ^ 2 + (c * ∑ j, ⟪b j, z⟫_ℂ ^ 2).re) x v =
      2 * (a * ‖v‖ ^ 2 + (c * ∑ j, ⟪b j, v⟫_ℂ ^ 2).re) := by
  obtain ⟨Q, B, hQ, hB⟩ := exists_bilinear_apply_self_eq b a c
  have hf : (fun z ↦ a * ‖z‖ ^ 2 + (c * ∑ j, ⟪b j, z⟫_ℂ ^ 2).re) = fun z ↦ B z z := by
    funext z
    rw [hB, hQ, re_inner_self]
  rw [hf, hessianQuadraticForm_apply, fderiv_fderiv_apply_self]
  simp only [add_apply, flip_apply, hB, hQ, re_inner_self]
  ring

/-- On the real span of the rotated basis `ζ • b j`, for a unit complex number `ζ`, the
holomorphic quadratic form `∑ⱼ ⟪b j, v⟫²` is `ζ² ‖v‖²`. This real span has real dimension the
complex dimension. -/
private theorem exists_submodule_sum_inner_sq_eq (b : OrthonormalBasis ι ℂ E) {ζ : ℂ}
    (hζ : ‖ζ‖ = 1) : ∃ S : Submodule ℝ E, finrank ℝ S = finrank ℂ E ∧
      ∀ v ∈ S, ∑ j, ⟪b j, v⟫_ℂ ^ 2 = ζ ^ 2 * ‖v‖ ^ 2 := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    simp at hζ
  refine ⟨Submodule.span ℝ (Set.range fun j ↦ ζ • b j), ?_, fun v hv ↦ ?_⟩
  · have hli : LinearIndependent ℝ fun j ↦ ζ • b j := by
      have h := b.toBasis.linearIndependent.units_smul fun _ ↦ Units.mk0 ζ hζ0
      convert h.restrict_scalars' ℝ using 1
      ext j
      simp [Units.smul_def]
    rw [finrank_span_eq_card hli, finrank_eq_card_basis b.toBasis]
  obtain ⟨t, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hv
  have hk (k : ι) : ⟪b k, ∑ j, t j • ζ • b j⟫_ℂ = ζ * t k := by
    have h : ∑ j, t j • ζ • b j = ∑ j, (ζ * t j) • b j := by
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [← Complex.coe_smul, smul_smul, mul_comm]
    rw [h, b.orthonormal.inner_right_fintype]
  rw [← ofReal_pow, ← b.sum_sq_norm_inner_right]
  simp only [hk, norm_mul, hζ, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow,
    ← Finset.mul_sum]
  push_cast
  ring

/-- The holomorphic part is bounded by the squared norm: `|Re (c ∑ⱼ ⟪b j, v⟫²)| ≤ ‖c‖ ‖v‖²`. -/
private theorem abs_re_mul_sum_inner_sq_le (b : OrthonormalBasis ι ℂ E) (c : ℂ) (v : E) :
    |(c * ∑ j, ⟪b j, v⟫_ℂ ^ 2).re| ≤ ‖c‖ * ‖v‖ ^ 2 := by
  refine (abs_re_le_norm _).trans ?_
  rw [norm_mul, ← b.sum_sq_norm_inner_right]
  gcongr
  exact (norm_sum_le _ _).trans_eq (by simp)

/-- On the real span of `ζ • b j`, for a unit complex number `ζ`, the Hessian of
`a ‖z‖² + Re (c ∑ⱼ ⟪b j, z⟫²)` is the multiple `2 (a + Re (c ζ²))` of `‖v‖²`. -/
private theorem exists_submodule_hessianQuadraticForm_eq (b : OrthonormalBasis ι ℂ E) (a : ℝ)
    (c : ℂ) (x : E) {ζ : ℂ} (hζ : ‖ζ‖ = 1) : ∃ S : Submodule ℝ E, finrank ℝ S = finrank ℂ E ∧
      ∀ v ∈ S, hessianQuadraticForm (fun z ↦ a * ‖z‖ ^ 2 + (c * ∑ j, ⟪b j, z⟫_ℂ ^ 2).re) x v =
        2 * (a + (c * ζ ^ 2).re) * ‖v‖ ^ 2 := by
  obtain ⟨S, hS, hSv⟩ := exists_submodule_sum_inner_sq_eq b hζ
  refine ⟨S, hS, fun v hv ↦ ?_⟩
  rw [hessianQuadraticForm_mul_norm_sq_add_re_mul_sum_inner_sq, hSv v hv, ← ofReal_pow,
    ← mul_assoc, re_mul_ofReal]
  ring

/-- **The Levi form of a Hermitian plus holomorphic quadratic function.** For an orthonormal
basis `b`, the Levi form of `a ‖z‖² + Re (c ∑ⱼ ⟪b j, z⟫²)` is `a ⟪·, ·⟫` at every point: the
holomorphic part does not contribute. -/
theorem leviForm_mul_norm_sq_add_re_mul_sum_inner_sq (b : OrthonormalBasis ι ℂ E) (a : ℝ)
    (c : ℂ) (x : E) :
    leviForm (fun z ↦ a * ‖z‖ ^ 2 + (c * ∑ j, ⟪b j, z⟫_ℂ ^ 2).re) x = (a : ℂ) • innerₛₗ ℂ := by
  obtain ⟨Q, -, hQ, -⟩ := exists_bilinear_apply_self_eq b a c
  have hf : (fun z ↦ a * ‖z‖ ^ 2 + (c * ∑ j, ⟪b j, z⟫_ℂ ^ 2).re) =
      (a • fun z : E ↦ ‖z‖ ^ 2) + fun z ↦ (Q z z).re := by
    funext z
    simp [hQ]
  have hQd : ContDiff ℂ 2 fun z ↦ Q z z := Q.contDiff_apply_self
  have h₁ : ContDiffAt ℝ 2 (a • fun z : E ↦ ‖z‖ ^ 2) x :=
    ((contDiff_norm_sq ℂ).const_smul a).contDiffAt
  have h₂ : ContDiffAt ℝ 2 (fun z ↦ (Q z z).re) x :=
    (reCLM.contDiff.comp (hQd.restrict_scalars ℝ)).contDiffAt
  rw [hf, leviForm_add h₁ h₂, hQd.contDiffAt.leviForm_re_eq_zero, leviForm_smul,
    leviForm_norm_sq, add_zero]

/-- **The Morse index of a Hermitian plus holomorphic quadratic function.** For an orthonormal
basis `b` of a complex inner product space of complex dimension `n`, the Morse index of
`a ‖z‖² + Re (c ∑ⱼ ⟪b j, z⟫²)` is `n` if `-‖c‖ ≤ a < ‖c‖`, it is `2 n` if `a < -‖c‖`, and it is
`0` if `‖c‖ ≤ a`.

In particular, for `a = 0` and `c ≠ 0`, the real part of the nondegenerate holomorphic quadratic
form `c ∑ⱼ ⟪b j, z⟫²` has Morse index `n`. For `a = 1`, the strictly plurisubharmonic function
`‖z‖² + Re (c ∑ⱼ ⟪b j, z⟫²)` has Morse index `n` if `1 < ‖c‖`, and `0` otherwise. -/
theorem morseIndex_mul_norm_sq_add_re_mul_sum_inner_sq [FiniteDimensional ℂ E]
    (b : OrthonormalBasis ι ℂ E) (a : ℝ) (c : ℂ) (x : E) :
    morseIndex (fun z ↦ a * ‖z‖ ^ 2 + (c * ∑ j, ⟪b j, z⟫_ℂ ^ 2).re) x =
      (if a < ‖c‖ then finrank ℂ E else 0) + (if a < -‖c‖ then finrank ℂ E else 0) := by
  -- Bound `sigNeg H` below by negative-definite subspaces and above by subspaces on which `H` is
  -- nonnegative: the real spans of `ω • b j` and `(I * ω) • b j`, or the whole space.
  rw [morseIndex_def]
  set H := hessianQuadraticForm (fun z ↦ a * ‖z‖ ^ 2 + (c * ∑ j, ⟪b j, z⟫_ℂ ^ 2).re) x
  have hH (v : E) : H v = 2 * (a * ‖v‖ ^ 2 + (c * ∑ j, ⟪b j, v⟫_ℂ ^ 2).re) :=
    hessianQuadraticForm_mul_norm_sq_add_re_mul_sum_inner_sq b a c x v
  obtain ⟨ω, hω, hcω⟩ := Complex.exists_norm_eq_one_mul_sq_eq_neg_norm c
  have hdim := finrank_real_eq_two_mul_finrank_complex (V := E)
  have hc := norm_nonneg c
  have hlow : a < ‖c‖ → finrank ℂ E ≤ sigNeg H := by
    intro ha
    obtain ⟨S, hS, hSv⟩ := exists_submodule_hessianQuadraticForm_eq b a c x hω
    rw [← hS]
    refine le_sigNeg_of_negDef H fun v hv ↦ ?_
    have hv' : 0 < ‖(v : E)‖ := norm_pos_iff.2 (by simpa using hv)
    rw [QuadraticMap.restrict_apply, neg_apply, hSv v v.2, hcω, neg_re, ofReal_re]
    nlinarith [mul_pos hv' hv']
  have hup : -‖c‖ ≤ a → sigNeg H ≤ finrank ℂ E := by
    intro ha
    obtain ⟨S, hS, hSv⟩ :=
      exists_submodule_hessianQuadraticForm_eq b a c x (ζ := I * ω) (by simp [hω])
    have h := QuadraticForm.sigPos_add_finrank_le_of_nonpos (Q := -H) (V := S) fun v hv ↦ by
      rw [neg_apply, hSv v hv, mul_pow, I_sq, neg_one_mul, mul_neg, hcω, neg_neg, ofReal_re,
        neg_nonpos]
      nlinarith [sq_nonneg ‖v‖]
    rw [sigPos_neg, hS, hdim] at h
    omega
  have hzero : ‖c‖ ≤ a → sigNeg H = 0 := by
    intro ha
    refine (QuadraticForm.forall_nonneg_iff_sigNeg_eq_zero H).1 fun v ↦ ?_
    rw [hH]
    nlinarith [abs_re_mul_sum_inner_sq_le b c v, neg_abs_le (c * ∑ j, ⟪b j, v⟫_ℂ ^ 2).re,
      sq_nonneg ‖v‖]
  have hall : a < -‖c‖ → sigNeg H = 2 * finrank ℂ E := by
    intro ha
    have h := le_sigNeg_of_negDef H (V := ⊤) fun v hv ↦ by
      have hv' : 0 < ‖(v : E)‖ := norm_pos_iff.2 (by simpa using hv)
      rw [QuadraticMap.restrict_apply, neg_apply, hH]
      nlinarith [abs_re_mul_sum_inner_sq_le b c v, le_abs_self (c * ∑ j, ⟪b j, (v : E)⟫_ℂ ^ 2).re,
        mul_pos hv' hv']
    have h' := sigPos_le_finrank (-H)
    rw [sigPos_neg] at h'
    rw [finrank_top] at h
    omega
  split_ifs with h₁ h₂ h₂
  · rw [hall h₂]
    ring
  · have := hlow h₁
    have := hup (not_lt.1 h₂)
    omega
  · exact absurd (h₂.trans_le (by linarith)) h₁
  · exact hzero (not_lt.1 h₁)

end InnerProductSpace

end TauCeti
