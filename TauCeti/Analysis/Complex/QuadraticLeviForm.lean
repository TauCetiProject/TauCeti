/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.Calculus.Morse.NormSq
public import TauCeti.Analysis.Complex.LeviForm
public import TauCeti.LinearAlgebra.Complex.Finrank

/-!
# Levi forms and inertia of the quadratic models

This file computes the Levi form and the Morse index of the three model functions of complex Morse
theory on a complex vector space `V` of dimension `n`.

* For a continuous complex bilinear form `q`, the real part `z ↦ Re (q z z)` of the holomorphic
  quadratic form has vanishing Levi form. Multiplication by `I` negates its Hessian, so its
  positive and negative indices of inertia agree, and its radical is the kernel of the
  polarization `q.flip + q`. Hence its Morse index is the complex rank of `q.flip + q`; it is `n`
  when `q.flip + q` is nondegenerate.
* The squared norm `z ↦ ‖z‖ ^ 2` of a complex inner product space is the positive Hermitian
  quadratic function: its Levi form is the inner product `⟪v, w⟫_ℂ`, so it is strictly
  plurisubharmonic, and its Morse index is zero.
* The sum `z ↦ ‖z‖ ^ 2 + Re (q z z)` still has the inner product as Levi form. On `ℂⁿ` with the
  diagonal form `q(z, z) = ∑ j, a j * z j ^ 2` (`a j` real), its Morse index is the number of `j`
  with `1 < |a j|`. Choosing `a`, every index between `0` and `n` occurs for a strictly
  plurisubharmonic quadratic function, so the index bound `λ ≤ n` for strictly plurisubharmonic
  functions cannot be improved.

## Main results

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

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, §7.
* R. Hain, *Notes on the Morse theory of complex manifolds*.
-/

public section

open Complex ComplexConjugate Module

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

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
  rw [morseIndex_def]
  refine QuadraticForm.sigNeg_eq_sigPos_of_comp_eq_neg _
    ((LinearEquiv.smulOfNeZero ℂ V I I_ne_zero).restrictScalars ℝ) fun v ↦ ?_
  simp [q.hessianQuadraticForm_re_apply_self]

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
