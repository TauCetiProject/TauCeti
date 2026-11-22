/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.Alternating.Basic
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import TauCeti.Topology.Algebra.Module.Alternating.Basic

/-!
# The Hermitian form of a real two-form on a complex vector space

Let `E` be a complex vector space and `α` a real alternating two-form on the underlying real
space. Its **Hermitian form** is `H_α(u, v) = α(u, i v) + i·α(u, v)`. It is the form through which
a real (1,1)-form on a complex manifold enters a complex Hessian equation: for a Hermitian metric
`ω` it is the Hermitian inner product `h`, and the eigenvalues of `H_α` relative to `h` are the
relative eigenvalues of `α`.

For every `α`, `H_α` is additive in both slots and complex linear in the second slot, and its
diagonal value `H_α(v, v) = α(v, i v)` is real. It is conjugate linear in the first slot, and
Hermitian, exactly when `α` is invariant under multiplication by `i`, that is, when `α` has type
(1,1). It is then positive definite exactly when `α` tames multiplication by `i`.

## Main definitions

* `ContinuousAlternatingMap.hermitianForm`: the Hermitian form `H_α` of a real two-form `α`.
* `ContinuousAlternatingMap.hermitianSesqForm`: for `α` of type (1,1), `H_α` as a sesquilinear
  form, conjugate linear in the first slot.

## Main results

* `ContinuousAlternatingMap.hermitianForm_smul_right`: `H_α` is complex linear in the second slot.
* `ContinuousAlternatingMap.hermitianForm_apply_self`: `H_α(v, v) = α(v, i v)`.
* `ContinuousAlternatingMap.hermitianForm_smul_left`: for `α` of type (1,1), `H_α` is conjugate
  linear in the first slot.
* `ContinuousAlternatingMap.isSymm_hermitianSesqForm`: for `α` of type (1,1), `H_α` is Hermitian.
* `ContinuousAlternatingMap.apply_I_smul_I_smul_of_conj_hermitianForm` and
  `ContinuousAlternatingMap.apply_I_smul_I_smul_of_hermitianForm_I_smul_left`: conversely, if
  `H_α` is Hermitian, or conjugate linear in the first slot, then `α` has type (1,1).

## References

* G. Székelyhidi, *Fully non-linear elliptic equations on compact Hermitian manifolds*,
  J. Differential Geom. 109 (2018), Section 2.
-/

public section

open Complex
open scoped ComplexConjugate

namespace ContinuousAlternatingMap

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  (α : E [⋀^Fin 2]→L[ℝ] ℝ)

/-- The **Hermitian form** `H_α(u, v) = α(u, i v) + i·α(u, v)` of a real two-form `α` on a complex
vector space. It is complex linear in the second slot; it is conjugate linear in the first slot,
and Hermitian, exactly when `α` is invariant under multiplication by `i`. -/
def hermitianForm (u v : E) : ℂ :=
  ⟨α ![u, I • v], α ![u, v]⟩

/-- Unfolding lemma for `hermitianForm`. -/
theorem hermitianForm_def (u v : E) : α.hermitianForm u v = ⟨α ![u, I • v], α ![u, v]⟩ :=
  (rfl)

/-- The real part of `H_α(u, v)` is `α(u, i v)`. -/
@[simp]
theorem re_hermitianForm (u v : E) : (α.hermitianForm u v).re = α ![u, I • v] :=
  (rfl)

/-- The imaginary part of `H_α(u, v)` is `α(u, v)`. -/
@[simp]
theorem im_hermitianForm (u v : E) : (α.hermitianForm u v).im = α ![u, v] :=
  (rfl)

variable {α}

/-- A real two-form is additive in its second argument. -/
private theorem apply_add_right (u v v' : E) : α ![u, v + v'] = α ![u, v] + α ![u, v'] := by
  simpa using α.toContinuousMultilinearMap.toMultilinearMap.snoc_add ![u] v v'

/-- A real two-form is real homogeneous in its second argument. -/
private theorem apply_smul_right (r : ℝ) (u v : E) : α ![u, r • v] = r * α ![u, v] := by
  simpa using α.toContinuousMultilinearMap.toMultilinearMap.snoc_smul ![u] r v

/-- A real two-form is odd in its second argument. -/
private theorem apply_neg_right (u v : E) : α ![u, -v] = -α ![u, v] := by
  simpa using apply_smul_right (α := α) (-1) u v

omit [TopologicalSpace E] in
/-- Decomposition of a complex multiple into real multiples of `v` and `i v`. -/
private theorem smul_eq_re_smul_add_im_smul (c : ℂ) (v : E) :
    c • v = c.re • v + c.im • (I • v) := by
  conv_lhs => rw [← re_add_im c]
  rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]

/-- `H_α` is additive in the first slot. -/
theorem hermitianForm_add_left (u u' v : E) :
    α.hermitianForm (u + u') v = α.hermitianForm u v + α.hermitianForm u' v := by
  apply Complex.ext <;> simp [vecCons_add]

/-- `H_α` is additive in the second slot. -/
theorem hermitianForm_add_right (u v v' : E) :
    α.hermitianForm u (v + v') = α.hermitianForm u v + α.hermitianForm u v' := by
  apply Complex.ext <;> simp [smul_add, apply_add_right]

/-- `H_α(u, i v) = i·H_α(u, v)`. -/
theorem hermitianForm_I_smul_right (u v : E) :
    α.hermitianForm u (I • v) = I * α.hermitianForm u v := by
  apply Complex.ext <;> simp [smul_smul, apply_neg_right]

/-- **`H_α` is complex linear in the second slot**, for every real two-form `α`. -/
theorem hermitianForm_smul_right (c : ℂ) (u v : E) :
    α.hermitianForm u (c • v) = c * α.hermitianForm u v := by
  have hr (r : ℝ) (w : E) : α.hermitianForm u (r • w) = r * α.hermitianForm u w := by
    apply Complex.ext <;> simp [smul_comm (I : ℂ) r w, apply_smul_right]
  rw [smul_eq_re_smul_add_im_smul, hermitianForm_add_right, hr, hr,
    hermitianForm_I_smul_right]
  conv_rhs => rw [← re_add_im c]
  ring

/-- **The diagonal of `H_α` is real**: `H_α(v, v) = α(v, i v)`. -/
theorem hermitianForm_apply_self (v : E) : α.hermitianForm v v = (α ![v, I • v] : ℂ) := by
  apply Complex.ext
  · simp
  · simpa using α.map_eq_zero_of_eq ![v, v] (i := 0) (j := 1) rfl (by decide)

/-- `H_α(v, v)` has positive real part exactly when `α(v, i v) > 0`. -/
theorem re_hermitianForm_apply_self_pos_iff (v : E) :
    0 < (α.hermitianForm v v).re ↔ 0 < α ![v, I • v] := by
  rw [hermitianForm_apply_self, ofReal_re]

section Invariant

variable (hα : ∀ u v : E, α ![I • u, I • v] = α ![u, v])
include hα

/-- For `α` of type (1,1), `H_α(i u, v) = -i·H_α(u, v)`. -/
theorem hermitianForm_I_smul_left (u v : E) :
    α.hermitianForm (I • u) v = -I * α.hermitianForm u v := by
  have h₁ : α ![I • u, v] = -α ![u, I • v] := by
    linarith [show -α ![I • u, v] = α ![u, I • v] by
      simpa [smul_smul, apply_neg_right] using hα u (I • v)]
  apply Complex.ext <;> simp [hα, h₁]

/-- **For `α` of type (1,1), `H_α` is conjugate linear in the first slot.** -/
theorem hermitianForm_smul_left (c : ℂ) (u v : E) :
    α.hermitianForm (c • u) v = conj c * α.hermitianForm u v := by
  have hr (r : ℝ) (w : E) : α.hermitianForm (r • w) v = r * α.hermitianForm w v := by
    apply Complex.ext <;> simp [vecCons_smul]
  rw [smul_eq_re_smul_add_im_smul, hermitianForm_add_left, hr, hr,
    hermitianForm_I_smul_left hα]
  conv_rhs => rw [← re_add_im c]
  simp only [map_add, map_mul, conj_ofReal, conj_I]
  ring

/-- **For `α` of type (1,1), `H_α` is Hermitian**: `conj H_α(u, v) = H_α(v, u)`. -/
theorem conj_hermitianForm (u v : E) : conj (α.hermitianForm u v) = α.hermitianForm v u := by
  have h₁ : α ![v, I • u] = α ![u, I • v] := by
    have h₂ := hα v (I • u)
    simp only [smul_smul, I_mul_I, neg_one_smul, apply_neg_right] at h₂
    rw [α.apply_vecCons_swap u, α.apply_vecCons_swap (I • u), neg_neg] at *
    linarith
  apply Complex.ext
  · simp [h₁]
  · simp [α.apply_vecCons_swap u v]

/-- For `α` of type (1,1), the Hermitian form `H_α` as a sesquilinear form, conjugate linear in
the first slot. -/
def hermitianSesqForm : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) α.hermitianForm hermitianForm_add_left
    (hermitianForm_smul_left hα) hermitianForm_add_right hermitianForm_smul_right

/-- The sesquilinear form `hermitianSesqForm` evaluates as `H_α`. -/
@[simp]
theorem hermitianSesqForm_apply (u v : E) :
    α.hermitianSesqForm hα u v = α.hermitianForm u v :=
  (rfl)

/-- For `α` of type (1,1), the sesquilinear form `H_α` is Hermitian. -/
theorem isSymm_hermitianSesqForm : (α.hermitianSesqForm hα).IsSymm :=
  ⟨conj_hermitianForm hα⟩

end Invariant

/-- **A real two-form with Hermitian `H_α` has type (1,1).** -/
theorem apply_I_smul_I_smul_of_conj_hermitianForm
    (h : ∀ u v : E, conj (α.hermitianForm u v) = α.hermitianForm v u) (u v : E) :
    α ![I • u, I • v] = α ![u, v] := by
  have h₁ := congrArg Complex.re (h v (I • u))
  simp only [conj_re, re_hermitianForm, smul_smul, I_mul_I, neg_one_smul] at h₁
  rw [apply_neg_right, α.apply_vecCons_swap] at h₁
  linarith

/-- **A real two-form whose `H_α` is conjugate linear in the first slot has type (1,1).** -/
theorem apply_I_smul_I_smul_of_hermitianForm_I_smul_left
    (h : ∀ u v : E, α.hermitianForm (I • u) v = -I * α.hermitianForm u v) (u v : E) :
    α ![I • u, I • v] = α ![u, v] := by
  simpa using congrArg Complex.re (h u v)

end ContinuousAlternatingMap
