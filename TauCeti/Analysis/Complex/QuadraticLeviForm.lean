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
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Coordinates
public import TauCeti.Analysis.SpecialFunctions.Complex.Arg

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
* For real `t`, the sum `z ↦ t ‖z‖ ^ 2 + Re (q z z)` has Levi form `t ⟪·, ·⟫`; in particular
  `z ↦ ‖z‖ ^ 2 + Re (q z z)` still has the inner product as Levi form. On `ℂⁿ` with the diagonal
  form `q(z, z) = ∑ j, a j * z j ^ 2` (`a j` real), the Morse index of `‖z‖ ^ 2 + Re (q z z)` is
  the number of `j` with `1 < |a j|`. Choosing `a`, every index between `0` and `n` occurs for a
  strictly plurisubharmonic quadratic function, so the index bound `λ ≤ n` for strictly
  plurisubharmonic functions cannot be improved.
* For an orthonormal basis `b` of a finite-dimensional complex inner product space, the function
  `a ‖z‖² + Re (∑ⱼ c j ⟪b j, z⟫²)` has Levi form `a ⟪·, ·⟫` and Morse index
  `∑ⱼ ([a < ‖c j‖] + [a < -‖c j‖])`. In coordinates it is `∑ⱼ (a |zⱼ|² + Re (c j zⱼ²))`, and each
  coordinate contributes the inertia of `a |w|² + Re (c j w²)` on `ℂ`, whose real eigenvalues are
  `a ± ‖c j‖`. With one coefficient `c` for all `j`, the index is `n [a < ‖c‖] + n [a < -‖c‖]`:
  for `a > 0` the function is strictly plurisubharmonic, and its Morse index jumps from `0` to
  the complex dimension when `‖c‖` crosses `a`. The diagonal example on `ℂⁿ` above is the case
  of the standard basis, `a = 1` and real `c j`.

## Main results

* `ContinuousLinearMap.leviForm_apply_self`: the Levi form of `z ↦ B z z`.
* `ContinuousLinearMap.hessianQuadraticForm_re_apply_self`,
  `ContinuousLinearMap.leviForm_re_apply_self`: the Hessian and the Levi form of `Re (q z z)`.
* `ContinuousLinearMap.morseIndex_re_apply_self_add_finrank_ker`: the Morse index of `Re (q z z)`
  plus the complex dimension of the kernel of `q.flip + q` is `n`.
* `TauCeti.leviForm_norm_sq`, `TauCeti.morseIndex_norm_sq_complex`: the Levi form of `‖z‖ ^ 2`
  is the inner product, and its Morse index is zero.
* `ContinuousLinearMap.hessianQuadraticForm_mul_norm_sq_add_re_apply_self`,
  `ContinuousLinearMap.leviForm_mul_norm_sq_add_re_apply_self`: the Hessian and the Levi form of
  `a ‖z‖ ^ 2 + Re (q z z)`; the Levi form is `a ⟪·, ·⟫`.
* `TauCeti.leviForm_euclidean_norm_sq_add_sum_re_sq`,
  `TauCeti.morseIndex_euclidean_norm_sq_add_sum_re_sq`: on `ℂⁿ`, the Levi form of
  `‖z‖ ^ 2 + ∑ j, a j * Re (z j ^ 2)` is the standard inner product and its Morse index is the
  number of `j` with `1 < |a j|`.
* `OrthonormalBasis.hessianQuadraticForm_mul_norm_sq_add_re_sum_mul_inner_sq`,
  `OrthonormalBasis.leviForm_mul_norm_sq_add_re_sum_mul_inner_sq`,
  `OrthonormalBasis.morseIndex_mul_norm_sq_add_re_sum_mul_inner_sq`: the Hessian, the Levi form
  and the Morse index of `a ‖z‖² + Re (∑ⱼ c j ⟪b j, z⟫²)` for an orthonormal basis `b`.
* `OrthonormalBasis.morseIndex_mul_norm_sq_add_re_mul_sum_inner_sq`: the Morse index of
  `a ‖z‖² + Re (c ∑ⱼ ⟪b j, z⟫²)`.

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

/-- Adding the real part of a holomorphic quadratic form to a real multiple `a ‖z‖ ^ 2` of the
squared norm does not change the Levi form: it is still `a` times the inner product. -/
@[simp]
theorem _root_.ContinuousLinearMap.leviForm_mul_norm_sq_add_re_apply_self (a : ℝ) (x : E) :
    leviForm (fun z ↦ a * ‖z‖ ^ 2 + (q z z).re) x = (a : ℂ) • innerₛₗ ℂ := by
  have h : ContDiffAt ℝ 2 (a • fun z : E ↦ ‖z‖ ^ 2) x :=
    ((contDiff_norm_sq ℂ).const_smul a).contDiffAt
  simpa [Pi.add_def] using leviForm_add h (contDiffAt_re_apply_self q x)

/-- Adding the real part of a holomorphic quadratic form to the squared norm does not change the
Levi form: it is still the inner product. In particular `‖z‖ ^ 2 + Re (q z z)` is strictly
plurisubharmonic. -/
@[simp]
theorem _root_.ContinuousLinearMap.leviForm_norm_sq_add_re_apply_self (x : E) :
    leviForm (fun z ↦ ‖z‖ ^ 2 + (q z z).re) x = innerₛₗ ℂ := by
  simpa using q.leviForm_mul_norm_sq_add_re_apply_self 1 x

/-- The Hessian quadratic form of `z ↦ a ‖z‖ ^ 2 + Re (q z z)` is
`v ↦ 2 a ‖v‖ ^ 2 + 2 Re (q v v)`, at every point. -/
theorem _root_.ContinuousLinearMap.hessianQuadraticForm_mul_norm_sq_add_re_apply_self (a : ℝ)
    (x v : E) :
    hessianQuadraticForm (fun z ↦ a * ‖z‖ ^ 2 + (q z z).re) x v =
      2 * a * ‖v‖ ^ 2 + 2 * (q v v).re := by
  have h : ContDiffAt ℝ 2 (a • fun z : E ↦ ‖z‖ ^ 2) x :=
    ((contDiff_norm_sq ℂ).const_smul a).contDiffAt
  -- Keep the Hessians folded so that the named Hessian lemmas of both summands apply.
  simpa [-hessianQuadraticForm_apply, Pi.add_def, hessianQuadraticForm_norm_sq_complex,
    q.hessianQuadraticForm_re_apply_self, ← mul_assoc, mul_comm a 2] using
    congr($(hessianQuadraticForm_add h (contDiffAt_re_apply_self q x)) v)

end NormSq

/-! ### Hermitian plus holomorphic quadratic functions in an orthonormal basis -/

section OrthonormalBasis

open ContinuousLinearMap
open scoped InnerProductSpace

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Fintype ι]

/-- **The Hessian of a Hermitian plus holomorphic quadratic function.** For an orthonormal
basis `b`, the Hessian quadratic form of `a ‖z‖² + Re (∑ⱼ c j ⟪b j, z⟫²)` is
`v ↦ 2 (a ‖v‖² + Re (∑ⱼ c j ⟪b j, v⟫²))` at every point. -/
theorem _root_.OrthonormalBasis.hessianQuadraticForm_mul_norm_sq_add_re_sum_mul_inner_sq
    (b : OrthonormalBasis ι ℂ E) (a : ℝ) (c : ι → ℂ) (x v : E) :
    hessianQuadraticForm (fun z ↦ a * ‖z‖ ^ 2 + (∑ j, c j * ⟪b j, z⟫_ℂ ^ 2).re) x v =
      2 * (a * ‖v‖ ^ 2 + (∑ j, c j * ⟪b j, v⟫_ℂ ^ 2).re) := by
  obtain ⟨Q, hQ⟩ := b.exists_apply_self_eq_sum_mul_inner_sq c
  simp_rw [← hQ]
  rw [Q.hessianQuadraticForm_mul_norm_sq_add_re_apply_self]
  ring

/-- **The Levi form of a Hermitian plus holomorphic quadratic function.** For an orthonormal
basis `b`, the Levi form of `a ‖z‖² + Re (∑ⱼ c j ⟪b j, z⟫²)` is `a ⟪·, ·⟫` at every point: the
holomorphic part does not contribute. -/
theorem _root_.OrthonormalBasis.leviForm_mul_norm_sq_add_re_sum_mul_inner_sq
    (b : OrthonormalBasis ι ℂ E) (a : ℝ) (c : ι → ℂ) (x : E) :
    leviForm (fun z ↦ a * ‖z‖ ^ 2 + (∑ j, c j * ⟪b j, z⟫_ℂ ^ 2).re) x =
      (a : ℂ) • innerₛₗ ℂ := by
  obtain ⟨Q, hQ⟩ := b.exists_apply_self_eq_sum_mul_inner_sq c
  simp_rw [← hQ]
  exact Q.leviForm_mul_norm_sq_add_re_apply_self a x

/-- **The Morse index of a Hermitian plus holomorphic quadratic function.** For an orthonormal
basis `b`, the Morse index of `a ‖z‖² + Re (∑ⱼ c j ⟪b j, z⟫²)` counts, for each `j`, one
negative direction if `a < ‖c j‖` and a second one if `a < -‖c j‖`.

By the Autonne-Takagi factorization, on a finite-dimensional space every holomorphic quadratic
form `q z z` is `∑ⱼ c j ⟪b j, z⟫²` with `c j ≥ 0` for some orthonormal basis `b`, so this computes
the inertia of every function `a ‖z‖² + Re (q z z)`. -/
theorem _root_.OrthonormalBasis.morseIndex_mul_norm_sq_add_re_sum_mul_inner_sq
    (b : OrthonormalBasis ι ℂ E) (a : ℝ) (c : ι → ℂ) (x : E) :
    morseIndex (fun z ↦ a * ‖z‖ ^ 2 + (∑ j, c j * ⟪b j, z⟫_ℂ ^ 2).re) x =
      ∑ j, ((if a < ‖c j‖ then 1 else 0) + (if a < -‖c j‖ then 1 else 0)) := by
  classical
  -- Rotating the coordinate `⟪b j, z⟫` by a unit `ω j` with `c j * ω j ^ 2 = -‖c j‖`, the real
  -- and imaginary parts of the rotated coordinates diagonalize the Hessian.
  choose ω hω hcω using fun j ↦ Complex.exists_norm_eq_one_mul_sq_eq_neg_norm (c j)
  have hωω (j : ι) : ω j * conj (ω j) = 1 := by
    rw [mul_conj, normSq_eq_norm_sq, hω, one_pow, ofReal_one]
  rw [morseIndex_def, QuadraticForm.sigNeg_of_equiv_weightedSumSquares
    (w := Sum.elim (fun j ↦ 2 * (a - ‖c j‖)) (fun j ↦ 2 * (a + ‖c j‖)))
    ⟨⟨b.rotatedRealCoords ω hωω, fun v ↦ ?_⟩⟩]
  · have hneg (j : ι) : 2 * (a - ‖c j‖) < 0 ↔ a < ‖c j‖ := by constructor <;> intro <;> linarith
    have hpos (j : ι) : 2 * (a + ‖c j‖) < 0 ↔ a < -‖c j‖ := by constructor <;> intro <;> linarith
    simp only [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred, Finset.card_filter,
      Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, ← Finset.sum_add_distrib, hneg, hpos]
  · rw [b.hessianQuadraticForm_mul_norm_sq_add_re_sum_mul_inner_sq, ← b.sum_sq_norm_inner_right]
    simp only [QuadraticMap.weightedSumSquares_apply, Fintype.sum_sum_type, re_sum,
      Finset.mul_sum, ← Finset.sum_add_distrib, LinearMap.toFun_eq_coe, LinearEquiv.coe_coe,
      b.rotatedRealCoords_apply_inl, b.rotatedRealCoords_apply_inr]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have h : ⟪b j, v⟫_ℂ = ω j * (conj (ω j) * ⟪b j, v⟫_ℂ) := by rw [← mul_assoc, hωω, one_mul]
    generalize conj (ω j) * ⟪b j, v⟫_ℂ = z at h ⊢
    simp only [h, mul_pow, ← mul_assoc, hcω, norm_mul, hω, one_mul, Complex.sq_norm]
    simp [normSq_apply, sq]
    ring

/-- **The Morse index of a Hermitian plus holomorphic quadratic function with one coefficient.**
For an orthonormal basis `b` of a complex inner product space of complex dimension `n`, the Morse
index of `a ‖z‖² + Re (c ∑ⱼ ⟪b j, z⟫²)` is `n` if `-‖c‖ ≤ a < ‖c‖`, it is `2 n` if `a < -‖c‖`,
and it is `0` if `‖c‖ ≤ a`.

In particular, for `a = 0` and `c ≠ 0`, the real part of the nondegenerate holomorphic quadratic
form `c ∑ⱼ ⟪b j, z⟫²` has Morse index `n`. For `a = 1`, the strictly plurisubharmonic function
`‖z‖² + Re (c ∑ⱼ ⟪b j, z⟫²)` has Morse index `n` if `1 < ‖c‖`, and `0` otherwise. -/
theorem _root_.OrthonormalBasis.morseIndex_mul_norm_sq_add_re_mul_sum_inner_sq
    (b : OrthonormalBasis ι ℂ E) (a : ℝ) (c : ℂ) (x : E) :
    morseIndex (fun z ↦ a * ‖z‖ ^ 2 + (c * ∑ j, ⟪b j, z⟫_ℂ ^ 2).re) x =
      (if a < ‖c‖ then finrank ℂ E else 0) + (if a < -‖c‖ then finrank ℂ E else 0) := by
  simp_rw [Finset.mul_sum]
  rw [b.morseIndex_mul_norm_sq_add_re_sum_mul_inner_sq, Finset.sum_add_distrib,
    finrank_eq_card_basis b.toBasis]
  split_ifs <;> simp

end OrthonormalBasis

/-! ### A diagonal example on `ℂⁿ` -/

section Diagonal

open scoped InnerProductSpace

variable {ι : Type*} [Fintype ι]

/-- On `ℂⁿ`, `‖z‖ ^ 2 + ∑ j, a j * Re (z j ^ 2)` is the orthonormal-basis model
`1 * ‖z‖² + Re (∑ⱼ a j ⟪b j, z⟫²)` for the standard basis `b`. -/
private theorem norm_sq_add_sum_re_sq_eq (a : ι → ℝ) :
    (fun z : EuclideanSpace ℂ ι ↦ ‖z‖ ^ 2 + ∑ j, a j * (z j ^ 2).re) = fun z ↦
      (1 : ℝ) * ‖z‖ ^ 2 + (∑ j, (a j : ℂ) * ⟪EuclideanSpace.basisFun ι ℂ j, z⟫_ℂ ^ 2).re := by
  funext z
  simp only [EuclideanSpace.basisFun_inner, one_mul, re_sum, re_ofReal_mul]

/-- On `ℂⁿ`, the Levi form of `z ↦ ‖z‖ ^ 2 + ∑ j, a j * Re (z j ^ 2)` is the standard Hermitian
inner product, for all real `a j`. -/
@[simp]
theorem leviForm_euclidean_norm_sq_add_sum_re_sq (a : ι → ℝ) (x : EuclideanSpace ℂ ι) :
    leviForm (fun z : EuclideanSpace ℂ ι ↦ ‖z‖ ^ 2 + ∑ j, a j * (z j ^ 2).re) x = innerₛₗ ℂ := by
  rw [norm_sq_add_sum_re_sq_eq,
    (EuclideanSpace.basisFun ι ℂ).leviForm_mul_norm_sq_add_re_sum_mul_inner_sq, ofReal_one,
    one_smul]

/-- On `ℂⁿ`, in the coordinates `z j = x j + I y j`, the Hessian quadratic form of
`z ↦ ‖z‖ ^ 2 + ∑ j, a j * Re (z j ^ 2)` is `∑ j, (2 (1 + a j) x j ^ 2 + 2 (1 - a j) y j ^ 2)`. -/
theorem hessianQuadraticForm_euclidean_norm_sq_add_sum_re_sq (a : ι → ℝ)
    (x v : EuclideanSpace ℂ ι) :
    hessianQuadraticForm (fun z : EuclideanSpace ℂ ι ↦ ‖z‖ ^ 2 + ∑ j, a j * (z j ^ 2).re) x v =
      ∑ j, (2 * (1 + a j) * (v j).re ^ 2 + 2 * (1 - a j) * (v j).im ^ 2) := by
  rw [norm_sq_add_sum_re_sq_eq,
    (EuclideanSpace.basisFun ι ℂ).hessianQuadraticForm_mul_norm_sq_add_re_sum_mul_inner_sq]
  simp only [EuclideanSpace.basisFun_inner, one_mul, EuclideanSpace.norm_sq_eq, re_sum,
    re_ofReal_mul, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Complex.sq_norm, normSq_apply, sq, mul_re]
  ring

/-- **Explicit inertia of a strictly plurisubharmonic quadratic function.** On `ℂⁿ`, the function
`z ↦ ‖z‖ ^ 2 + ∑ j, a j * Re (z j ^ 2)`, whose Levi form is the standard Hermitian inner product
(`TauCeti.leviForm_euclidean_norm_sq_add_sum_re_sq`), has Morse index equal to the number of `j`
with `1 < |a j|`, at every point. -/
theorem morseIndex_euclidean_norm_sq_add_sum_re_sq (a : ι → ℝ) (x : EuclideanSpace ℂ ι) :
    morseIndex (fun z : EuclideanSpace ℂ ι ↦ ‖z‖ ^ 2 + ∑ j, a j * (z j ^ 2).re) x =
      {j | 1 < |a j|}.ncard := by
  classical
  rw [norm_sq_add_sum_re_sq_eq, OrthonormalBasis.morseIndex_mul_norm_sq_add_re_sum_mul_inner_sq,
    Set.ncard_eq_toFinset_card', Set.toFinset_ofPred, Finset.card_filter]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have h : ¬(1 : ℝ) < -|a j| := by linarith [abs_nonneg (a j)]
  simp [h]

end Diagonal

end TauCeti
