/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.Calculus.Bilinear
public import TauCeti.Analysis.Calculus.Morse.NormSq
public import TauCeti.Analysis.Complex.LeviForm
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.SumInnerSq
public import TauCeti.Analysis.SpecialFunctions.Complex.Arg
public import TauCeti.LinearAlgebra.QuadraticForm.Signature

/-!
# Levi forms and inertia of the quadratic models

This file computes the Levi form and the Morse index of the model quadratic functions of complex
Morse theory on a complex vector space `V` of dimension `n`.

* The Levi form of a real quadratic function `z ↦ B z z` is the Levi form of its polarization
  `B.flip + B`.
* For a continuous complex bilinear form `q`, the real part `z ↦ Re (q z z)` of the holomorphic
  quadratic form has vanishing Levi form. Multiplication by `I` negates its Hessian, so its
  positive and negative indices of inertia agree, and its radical is the kernel of the
  polarization `q.flip + q`. Hence its Morse index is the complex rank of `q.flip + q`; it is `n`
  when `q.flip + q` is nondegenerate.
* The squared norm `z ↦ ‖z‖ ^ 2` of a complex inner product space is the positive Hermitian
  quadratic function: its Levi form is the inner product `⟪v, w⟫_ℂ`, so it is strictly
  plurisubharmonic, and its Morse index is zero.
  Every positive definite Hermitian form on a finite-dimensional complex space is the inner
  product of some inner product space structure, so this is the general positive Hermitian
  quadratic function.
* The sum `z ↦ ‖z‖ ^ 2 + Re (q z z)` still has the inner product as Levi form. On `ℂⁿ` with the
  diagonal form `q(z, z) = ∑ j, a j * z j ^ 2` (`a j` real), its Morse index is the number of `j`
  with `1 < |a j|`. Choosing `a`, every index between `0` and `n` occurs for a strictly
  plurisubharmonic quadratic function, so the index bound `λ ≤ n` for strictly plurisubharmonic
  functions cannot be improved.
* For an orthonormal basis `b` of a finite-dimensional complex inner product space of complex
  dimension `n`, the function `a ‖z‖² + Re (c ∑ⱼ ⟪b j, z⟫²)` has Levi form `a ⟪·, ·⟫` and Morse
  index `n [a < ‖c‖] + n [a < -‖c‖]`. In coordinates it is
  `a ∑ⱼ |zⱼ|² + Re (c ∑ⱼ zⱼ²)`; for `a > 0` it is strictly plurisubharmonic, and its Morse index
  jumps from `0` to the complex dimension when `‖c‖` crosses `a`.

## Main results

* `ContinuousLinearMap.leviForm_apply_self`: the Levi form of `z ↦ B z z`.
* `ContinuousLinearMap.hessianQuadraticForm_re_apply_self`,
  `ContinuousLinearMap.leviForm_re_apply_self`: the Hessian and the Levi form of `Re (q z z)`.
* `ContinuousLinearMap.morseIndex_re_apply_self_add_finrank_ker`: the Morse index of `Re (q z z)`
  plus the complex dimension of the kernel of `q.flip + q` is `n`.
* `TauCeti.leviForm_norm_sq`, `TauCeti.morseIndex_norm_sq_complex`: the Levi form of `‖z‖ ^ 2`
  is the inner product, and its Morse index is zero.
* `ContinuousLinearMap.leviForm_norm_sq_add_re_apply_self`: the Levi form of
  `‖z‖ ^ 2 + Re (q z z)` is the inner product.
* `TauCeti.leviForm_euclidean_norm_sq_add_sum_re_sq`,
  `TauCeti.morseIndex_euclidean_norm_sq_add_sum_re_sq`: on `ℂⁿ`, the Levi form of
  `‖z‖ ^ 2 + ∑ j, a j * Re (z j ^ 2)` is the standard inner product and its Morse index is the
  number of `j` with `1 < |a j|`.
* `OrthonormalBasis.hessianQuadraticForm_mul_norm_sq_add_re_mul_sum_inner_sq`,
  `OrthonormalBasis.leviForm_mul_norm_sq_add_re_mul_sum_inner_sq`,
  `OrthonormalBasis.morseIndex_mul_norm_sq_add_re_mul_sum_inner_sq`: the Hessian, the Levi form
  and the Morse index of `a ‖z‖² + Re (c ∑ⱼ ⟪b j, z⟫²)` for an orthonormal basis `b`.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, §7.
* R. Hain, *Notes on the Morse theory of complex manifolds*.
-/

public section

open Complex ComplexConjugate Module

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-! ### Real quadratic functions -/

/-- The Levi form of the real quadratic function `z ↦ B z z` is the Levi form of the
polarization `B.flip + B`, at every point. -/
@[simp]
theorem _root_.ContinuousLinearMap.leviForm_apply_self (B : V →L[ℝ] V →L[ℝ] ℝ) (x : V) :
    leviForm (fun z ↦ B z z) x = (B.flip + B).toBilinForm.leviForm := by
  rw [leviForm_def, B.fderiv_fderiv_apply_self]

/-! ### The real part of a holomorphic quadratic form -/

section HolomorphicQuadratic

variable (q : V →L[ℂ] V →L[ℂ] ℂ)

private theorem contDiffAt_re_apply_self (x : V) : ContDiffAt ℝ 2 (fun z ↦ (q z z).re) x :=
  (reCLM.contDiff.comp (q.contDiff_apply_self.restrict_scalars ℝ)).contDiffAt

/-- The Hessian quadratic form of the real part of the holomorphic quadratic form `q z z` is
`v ↦ 2 * Re (q v v)`, at every point. -/
theorem _root_.ContinuousLinearMap.hessianQuadraticForm_re_apply_self (x v : V) :
    hessianQuadraticForm (fun z ↦ (q z z).re) x v = 2 * (q v v).re := by
  rw [hessianQuadraticForm_re q.contDiff_apply_self.contDiffAt, q.fderiv_fderiv_apply_self]
  simp only [add_apply, ContinuousLinearMap.flip_apply, add_re]
  ring

/-- The real part of a holomorphic quadratic form has vanishing Levi form. -/
@[simp]
theorem _root_.ContinuousLinearMap.leviForm_re_apply_self (x : V) :
    leviForm (fun z ↦ (q z z).re) x = 0 :=
  leviForm_re_eq_zero q.contDiff_apply_self.contDiffAt

/-- The real part of a holomorphic quadratic form has equal positive and negative indices of
inertia: multiplication by `I` negates its Hessian. -/
theorem _root_.ContinuousLinearMap.morseIndex_re_apply_self_eq_sigPos (x : V) :
    morseIndex (fun z ↦ (q z z).re) x = sigPos (hessianQuadraticForm (fun z ↦ (q z z).re) x) := by
  rw [← morseIndex_neg_eq_of_leviForm_eq_zero (q.leviForm_re_apply_self x), morseIndex_def,
    hessianQuadraticForm_neg, sigNeg_neg]

/-- The radical of the Hessian of the real part of a holomorphic quadratic form is the kernel of
the polarization `q.flip + q`. -/
theorem _root_.ContinuousLinearMap.radical_hessianQuadraticForm_re_apply_self (x : V) :
    (hessianQuadraticForm (fun z ↦ (q z z).re) x).radical =
      (LinearMap.ker (q.flip + q).toLinearMap).restrictScalars ℝ := by
  have hB (v w : V) : fderiv ℝ (fderiv ℝ fun z ↦ (q z z).re) x v w = ((q.flip + q) v w).re := by
    rw [fderiv_fderiv_re_apply q.contDiff_apply_self.contDiffAt, q.fderiv_fderiv_apply_self]
  ext v
  rw [QuadraticMap.radical_eq_ker_associated,
    associated_hessianQuadraticForm (contDiffAt_re_apply_self q x), LinearMap.mem_ker,
    Submodule.restrictScalars_mem, LinearMap.mem_ker]
  constructor
  · intro h
    ext w
    have h1 := congr($h w)
    have h2 := congr($h (I • w))
    simp only [ContinuousLinearMap.toBilinForm_apply, LinearMap.zero_apply, hB, map_smul,
      smul_eq_mul, mul_re, I_re, I_im, zero_mul, one_mul, zero_sub, neg_eq_zero] at h1 h2
    exact Complex.ext h1 h2
  · intro h
    ext w
    have hw := congr($h w)
    simp only [ContinuousLinearMap.coe_coe, add_apply, ContinuousLinearMap.flip_apply,
      zero_apply] at hw
    simp [hB, hw]

/-- **The inertia of the real part of a holomorphic quadratic form.** The Morse index of
`z ↦ Re (q z z)` is the complex rank of the polarization `q.flip + q`: together with the complex
dimension of its kernel it adds up to the complex dimension of `V`. -/
theorem _root_.ContinuousLinearMap.morseIndex_re_apply_self_add_finrank_ker [FiniteDimensional ℂ V]
    (x : V) :
    morseIndex (fun z ↦ (q z z).re) x + finrank ℂ (LinearMap.ker (q.flip + q).toLinearMap) =
      finrank ℂ V := by
  have h := QuadraticForm.sigPos_add_sigNeg_add_radical
    (Q := hessianQuadraticForm (fun z ↦ (q z z).re) x)
  rw [← morseIndex_def, ← q.morseIndex_re_apply_self_eq_sigPos,
    q.radical_hessianQuadraticForm_re_apply_self,
    ((Submodule.restrictScalarsEquiv ℝ ℂ V _).restrictScalars ℝ).finrank_eq,
    finrank_real_eq_two_mul_finrank_complex,
    finrank_real_eq_two_mul_finrank_complex] at h
  omega

/-- If the polarization `q.flip + q` of a complex bilinear form is injective, the real part of the
holomorphic quadratic form `q z z` has Morse index equal to the complex dimension of `V`. -/
theorem _root_.ContinuousLinearMap.morseIndex_re_apply_self_of_ker_eq_bot [FiniteDimensional ℂ V]
    (hq : LinearMap.ker (q.flip + q).toLinearMap = ⊥) (x : V) :
    morseIndex (fun z ↦ (q z z).re) x = finrank ℂ V := by
  have h := q.morseIndex_re_apply_self_add_finrank_ker x
  rwa [hq, finrank_bot, add_zero] at h

end HolomorphicQuadratic

/-! ### The squared norm and its holomorphic perturbations -/

section NormSq

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **The Levi form of the squared norm** of a complex inner product space is the inner product.
In particular the squared norm is strictly plurisubharmonic. -/
@[simp]
theorem leviForm_norm_sq (x : E) : leviForm (fun z ↦ ‖z‖ ^ 2) x = innerₛₗ ℂ := by
  ext v w
  apply Complex.ext <;>
  simp [fderiv_fderiv_norm_sq_apply_complex, inner_smul_left, inner_smul_right] <;> ring

/-- The Hessian quadratic form of the squared norm of a complex inner product space is
`v ↦ 2 * ‖v‖ ^ 2`. -/
theorem hessianQuadraticForm_norm_sq_complex (x v : E) :
    hessianQuadraticForm (fun z ↦ ‖z‖ ^ 2) x v = 2 * ‖v‖ ^ 2 := by
  simp [fderiv_fderiv_norm_sq_apply_complex, inner_self_eq_norm_sq_to_K, ← ofReal_pow]

/-- The squared norm of a finite-dimensional complex inner product space has Morse index zero at
every point. -/
@[simp]
theorem morseIndex_norm_sq_complex [FiniteDimensional ℂ E] (x : E) :
    morseIndex (fun z ↦ ‖z‖ ^ 2) x = 0 := by
  -- As for `fderiv_fderiv_norm_sq_apply_complex`, use the underlying real inner product space.
  let := InnerProductSpace.complexToReal (G := E)
  exact morseIndex_norm_sq x

variable (q : E →L[ℂ] E →L[ℂ] ℂ)

/-- Adding the real part of a holomorphic quadratic form to the squared norm does not change the
Levi form: it is still the inner product. -/
@[simp]
theorem _root_.ContinuousLinearMap.leviForm_norm_sq_add_re_apply_self (x : E) :
    leviForm (fun z ↦ ‖z‖ ^ 2 + (q z z).re) x = innerₛₗ ℂ := by
  simpa [Pi.add_def] using
    leviForm_add (contDiff_norm_sq ℂ).contDiffAt (contDiffAt_re_apply_self q x)

/-- The Hessian quadratic form of `z ↦ ‖z‖ ^ 2 + Re (q z z)` is `v ↦ 2 * ‖v‖ ^ 2 + 2 * Re (q v v)`,
at every point. -/
theorem _root_.ContinuousLinearMap.hessianQuadraticForm_norm_sq_add_re_apply_self (x v : E) :
    hessianQuadraticForm (fun z ↦ ‖z‖ ^ 2 + (q z z).re) x v = 2 * ‖v‖ ^ 2 + 2 * (q v v).re := by
  simpa only [Pi.add_def, add_apply, hessianQuadraticForm_norm_sq_complex,
    q.hessianQuadraticForm_re_apply_self] using congr($(hessianQuadraticForm_add
      (contDiff_norm_sq ℂ).contDiffAt (contDiffAt_re_apply_self q x)) v)

end NormSq

/-! ### Hermitian plus holomorphic quadratic functions in an orthonormal basis -/

section OrthonormalBasis

open ContinuousLinearMap
open scoped InnerProductSpace

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Fintype ι]

/-- The function `a ‖z‖² + Re (c ∑ⱼ ⟪b j, z⟫²)` is `z ↦ B z z` for a real bilinear form `B`
whose holomorphic part is a complex bilinear form `Q`. -/
private theorem exists_bilinear_apply_self_eq (b : OrthonormalBasis ι ℂ E) (a : ℝ) (c : ℂ) :
    ∃ (Q : E →L[ℂ] E →L[ℂ] ℂ) (B : E →L[ℝ] E →L[ℝ] ℝ),
      (∀ v, Q v v = c * ∑ j, ⟪b j, v⟫_ℂ ^ 2) ∧
        ∀ v w, B v w = a * RCLike.re ⟪v, w⟫_ℂ + (Q v w).re := by
  let _ : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
  let Q : E →L[ℂ] E →L[ℂ] ℂ :=
    c • ∑ j, (ContinuousLinearMap.mul ℂ ℂ).bilinearComp (innerSL ℂ (b j)) (innerSL ℂ (b j))
  let J : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ
  refine ⟨Q, a • J + (compL ℝ E ℂ ℝ reCLM).comp (Q.bilinearRestrictScalars ℝ), fun v ↦ ?_,
    fun v w ↦ ?_⟩
  · simp [Q, sq]
  · simp only [J, add_apply, smul_apply, comp_apply, compL_apply,
      bilinearRestrictScalars_apply_apply, reCLM_apply, smul_eq_mul]
    rw [innerSL_apply_apply, real_inner_eq_re_inner ℂ]

/-- **The Hessian of a Hermitian plus holomorphic quadratic function.** For an orthonormal
basis `b`, the Hessian quadratic form of `a ‖z‖² + Re (c ∑ⱼ ⟪b j, z⟫²)` is
`v ↦ 2 (a ‖v‖² + Re (c ∑ⱼ ⟪b j, v⟫²))` at every point. -/
theorem _root_.OrthonormalBasis.hessianQuadraticForm_mul_norm_sq_add_re_mul_sum_inner_sq
    (b : OrthonormalBasis ι ℂ E) (a : ℝ) (c : ℂ) (x v : E) :
    hessianQuadraticForm (fun z ↦ a * ‖z‖ ^ 2 + (c * ∑ j, ⟪b j, z⟫_ℂ ^ 2).re) x v =
      2 * (a * ‖v‖ ^ 2 + (c * ∑ j, ⟪b j, v⟫_ℂ ^ 2).re) := by
  obtain ⟨Q, B, hQ, hB⟩ := exists_bilinear_apply_self_eq b a c
  have hf : (fun z ↦ a * ‖z‖ ^ 2 + (c * ∑ j, ⟪b j, z⟫_ℂ ^ 2).re) = fun z ↦ B z z := by
    funext z
    rw [hB, hQ, inner_self_eq_norm_sq]
  rw [hf, hessianQuadraticForm_apply, fderiv_fderiv_apply_self]
  simp only [add_apply, flip_apply, hB, hQ, inner_self_eq_norm_sq]
  ring

/-- On the real span of `ζ • b j`, for a unit complex number `ζ`, the Hessian of
`a ‖z‖² + Re (c ∑ⱼ ⟪b j, z⟫²)` is the multiple `2 (a + Re (c ζ²))` of `‖v‖²`. -/
private theorem exists_submodule_hessianQuadraticForm_eq (b : OrthonormalBasis ι ℂ E) (a : ℝ)
    (c : ℂ) (x : E) {ζ : ℂ} (hζ : ‖ζ‖ = 1) : ∃ S : Submodule ℝ E, finrank ℝ S = finrank ℂ E ∧
      ∀ v ∈ S, hessianQuadraticForm (fun z ↦ a * ‖z‖ ^ 2 + (c * ∑ j, ⟪b j, z⟫_ℂ ^ 2).re) x v =
        2 * (a + (c * ζ ^ 2).re) * ‖v‖ ^ 2 := by
  refine ⟨_, b.finrank_span_smul (ne_zero_of_norm_ne_zero (hζ.trans_ne one_ne_zero)),
    fun v hv ↦ ?_⟩
  rw [b.hessianQuadraticForm_mul_norm_sq_add_re_mul_sum_inner_sq,
    b.sum_inner_sq_eq_of_mem_span_smul hζ hv, ← ofReal_pow, ← mul_assoc, re_mul_ofReal]
  ring

/-- **The Levi form of a Hermitian plus holomorphic quadratic function.** For an orthonormal
basis `b`, the Levi form of `a ‖z‖² + Re (c ∑ⱼ ⟪b j, z⟫²)` is `a ⟪·, ·⟫` at every point: the
holomorphic part does not contribute. -/
theorem _root_.OrthonormalBasis.leviForm_mul_norm_sq_add_re_mul_sum_inner_sq
    (b : OrthonormalBasis ι ℂ E) (a : ℝ) (c : ℂ) (x : E) :
    leviForm (fun z ↦ a * ‖z‖ ^ 2 + (c * ∑ j, ⟪b j, z⟫_ℂ ^ 2).re) x = (a : ℂ) • innerₛₗ ℂ := by
  obtain ⟨Q, -, hQ, -⟩ := exists_bilinear_apply_self_eq b a c
  have hf : (fun z ↦ a * ‖z‖ ^ 2 + (c * ∑ j, ⟪b j, z⟫_ℂ ^ 2).re) =
      (a • fun z : E ↦ ‖z‖ ^ 2) + fun z ↦ (Q z z).re := by
    funext z
    simp [hQ]
  have h₁ : ContDiffAt ℝ 2 (a • fun z : E ↦ ‖z‖ ^ 2) x :=
    ((contDiff_norm_sq ℂ).const_smul a).contDiffAt
  rw [hf, leviForm_add h₁ (contDiffAt_re_apply_self Q x), Q.leviForm_re_apply_self, leviForm_smul,
    leviForm_norm_sq, add_zero]

/-- **The Morse index of a Hermitian plus holomorphic quadratic function.** For an orthonormal
basis `b` of a complex inner product space of complex dimension `n`, the Morse index of
`a ‖z‖² + Re (c ∑ⱼ ⟪b j, z⟫²)` is `n` if `-‖c‖ ≤ a < ‖c‖`, it is `2 n` if `a < -‖c‖`, and it is
`0` if `‖c‖ ≤ a`.

In particular, for `a = 0` and `c ≠ 0`, the real part of the nondegenerate holomorphic quadratic
form `c ∑ⱼ ⟪b j, z⟫²` has Morse index `n`. For `a = 1`, the strictly plurisubharmonic function
`‖z‖² + Re (c ∑ⱼ ⟪b j, z⟫²)` has Morse index `n` if `1 < ‖c‖`, and `0` otherwise. -/
theorem _root_.OrthonormalBasis.morseIndex_mul_norm_sq_add_re_mul_sum_inner_sq
    [FiniteDimensional ℂ E] (b : OrthonormalBasis ι ℂ E) (a : ℝ) (c : ℂ) (x : E) :
    morseIndex (fun z ↦ a * ‖z‖ ^ 2 + (c * ∑ j, ⟪b j, z⟫_ℂ ^ 2).re) x =
      (if a < ‖c‖ then finrank ℂ E else 0) + (if a < -‖c‖ then finrank ℂ E else 0) := by
  -- Bound `sigNeg H` below by negative-definite subspaces and above by subspaces on which `H` is
  -- nonnegative: the real spans of `ω • b j` and `(I * ω) • b j`, or the whole space.
  rw [morseIndex_def]
  set H := hessianQuadraticForm (fun z ↦ a * ‖z‖ ^ 2 + (c * ∑ j, ⟪b j, z⟫_ℂ ^ 2).re) x
  have hH (v : E) : H v = 2 * (a * ‖v‖ ^ 2 + (c * ∑ j, ⟪b j, v⟫_ℂ ^ 2).re) :=
    b.hessianQuadraticForm_mul_norm_sq_add_re_mul_sum_inner_sq a c x v
  have habs (v : E) : |(c * ∑ j, ⟪b j, v⟫_ℂ ^ 2).re| ≤ ‖c‖ * ‖v‖ ^ 2 := by
    refine (abs_re_le_norm _).trans ?_
    rw [norm_mul]
    gcongr
    exact b.norm_sum_inner_sq_le v
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
    nlinarith [habs v, neg_abs_le (c * ∑ j, ⟪b j, v⟫_ℂ ^ 2).re,
      sq_nonneg ‖v‖]
  have hall : a < -‖c‖ → sigNeg H = 2 * finrank ℂ E := by
    intro ha
    have h := le_sigNeg_of_negDef H (V := ⊤) fun v hv ↦ by
      have hv' : 0 < ‖(v : E)‖ := norm_pos_iff.2 (by simpa using hv)
      rw [QuadraticMap.restrict_apply, neg_apply, hH]
      nlinarith [habs v, le_abs_self (c * ∑ j, ⟪b j, (v : E)⟫_ℂ ^ 2).re,
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

end OrthonormalBasis

/-! ### A diagonal example on `ℂⁿ` -/

section Diagonal

variable {ι : Type*} [Fintype ι]

/-- The diagonal complex bilinear form `(v, w) ↦ ∑ j, a j * v j * w j` on `ℂⁿ`. -/
private noncomputable def diagonalForm (a : ι → ℝ) :
    EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι →L[ℂ] ℂ :=
  ∑ j, (a j : ℂ) • (EuclideanSpace.proj j).smulRight (EuclideanSpace.proj j)

private theorem norm_sq_add_sum_re_sq_eq (a : ι → ℝ) :
    (fun z : EuclideanSpace ℂ ι ↦ ‖z‖ ^ 2 + ∑ j, a j * (z j ^ 2).re) =
      fun z ↦ ‖z‖ ^ 2 + (diagonalForm a z z).re := by
  funext z
  simp [diagonalForm, sq]

/-- On `ℂⁿ`, the Levi form of `z ↦ ‖z‖ ^ 2 + ∑ j, a j * Re (z j ^ 2)` is the standard Hermitian
inner product, for all real `a j`. -/
@[simp]
theorem leviForm_euclidean_norm_sq_add_sum_re_sq (a : ι → ℝ) (x : EuclideanSpace ℂ ι) :
    leviForm (fun z : EuclideanSpace ℂ ι ↦ ‖z‖ ^ 2 + ∑ j, a j * (z j ^ 2).re) x = innerₛₗ ℂ := by
  rw [norm_sq_add_sum_re_sq_eq, ContinuousLinearMap.leviForm_norm_sq_add_re_apply_self]

/-- On `ℂⁿ`, in the coordinates `z j = x j + I y j`, the Hessian quadratic form of
`z ↦ ‖z‖ ^ 2 + ∑ j, a j * Re (z j ^ 2)` is `∑ j, (2 (1 + a j) x j ^ 2 + 2 (1 - a j) y j ^ 2)`. -/
theorem hessianQuadraticForm_euclidean_norm_sq_add_sum_re_sq (a : ι → ℝ)
    (x v : EuclideanSpace ℂ ι) :
    hessianQuadraticForm (fun z : EuclideanSpace ℂ ι ↦ ‖z‖ ^ 2 + ∑ j, a j * (z j ^ 2).re) x v =
      ∑ j, (2 * (1 + a j) * (v j).re ^ 2 + 2 * (1 - a j) * (v j).im ^ 2) := by
  rw [norm_sq_add_sum_re_sq_eq, ContinuousLinearMap.hessianQuadraticForm_norm_sq_add_re_apply_self]
  simp only [diagonalForm, EuclideanSpace.norm_sq_eq, Finset.mul_sum, ← Finset.sum_add_distrib,
    sum_apply, re_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp [← normSq_eq_norm_sq, normSq_apply]
  ring

omit [Fintype ι] in
/-- Counting the negative weights `2 (1 + a j)` and `2 (1 - a j)`. -/
private theorem ncard_sum_elim_neg [Finite ι] (a : ι → ℝ) :
    {i | Sum.elim (fun j ↦ 2 * (1 + a j)) (fun j ↦ 2 * (1 - a j)) i < 0}.ncard =
      {j | 1 < |a j|}.ncard := by
  classical
  have := Fintype.ofFinite ι
  simp only [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred, Finset.card_filter,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have e1 : 2 * (1 + a j) < 0 ↔ a j < -1 := by constructor <;> intro <;> linarith
  have e2 : 2 * (1 - a j) < 0 ↔ 1 < a j := by constructor <;> intro <;> linarith
  have e3 : 1 < |a j| ↔ a j < -1 ∨ 1 < a j := by
    rw [lt_abs]
    constructor <;> rintro (h | h) <;> first | (left; linarith) | (right; linarith)
  simp only [e1, e2, e3]
  by_cases h1 : a j < -1 <;> by_cases h2 : 1 < a j <;> simp [h1, h2]
  linarith

/-- **Explicit inertia of a strictly plurisubharmonic quadratic function.** On `ℂⁿ`, the function
`z ↦ ‖z‖ ^ 2 + ∑ j, a j * Re (z j ^ 2)`, whose Levi form is the standard Hermitian inner product
(`TauCeti.leviForm_euclidean_norm_sq_add_sum_re_sq`), has Morse index equal to the number of `j`
with `1 < |a j|`, at every point. -/
theorem morseIndex_euclidean_norm_sq_add_sum_re_sq (a : ι → ℝ) (x : EuclideanSpace ℂ ι) :
    morseIndex (fun z : EuclideanSpace ℂ ι ↦ ‖z‖ ^ 2 + ∑ j, a j * (z j ^ 2).re) x =
      {j | 1 < |a j|}.ncard := by
  -- The real coordinates `(Re z j, Im z j)` diagonalize the Hessian.
  let e : EuclideanSpace ℂ ι ≃ₗ[ℝ] (ι ⊕ ι → ℝ) :=
    { toFun := fun z ↦ Sum.elim (fun j ↦ (z j).re) (fun j ↦ (z j).im)
      invFun := fun u ↦ WithLp.toLp 2 fun j ↦ ⟨u (Sum.inl j), u (Sum.inr j)⟩
      map_add' := fun z z' ↦ by ext (j | j) <;> simp
      map_smul' := fun c z ↦ by ext (j | j) <;> simp [← coe_smul]
      left_inv := fun z ↦ by ext j; simp
      right_inv := fun u ↦ by ext (j | j) <;> simp }
  rw [morseIndex_def, QuadraticForm.sigNeg_of_equiv_weightedSumSquares
    (w := Sum.elim (fun j ↦ 2 * (1 + a j)) (fun j ↦ 2 * (1 - a j))) ⟨⟨e, fun v ↦ ?_⟩⟩,
    ncard_sum_elim_neg]
  rw [hessianQuadraticForm_euclidean_norm_sq_add_sum_re_sq]
  simp [QuadraticMap.weightedSumSquares_apply, Fintype.sum_sum_type, e, sq, Finset.sum_add_distrib]

end Diagonal

end TauCeti
