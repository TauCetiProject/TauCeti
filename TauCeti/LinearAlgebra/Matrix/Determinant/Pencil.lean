/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Polynomial
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.SetTheory.Cardinal.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Invertible members of a determinant pencil

For square matrices `A` and `B` of size `n` over an integral domain, `t ↦ det (A + t • B)` is a
polynomial in `t` of degree at most `n`, with constant coefficient `det A` and `n`-th coefficient
`det B`. When `det A ≠ 0` it therefore vanishes at no more than `n` values of `t`, and at no more
than `n - 1` values when moreover `det B = 0`.

Over a field with more than `n` elements this shows that invertible matrices are spread through
every subspace of matrices containing one: if a subspace `V` contains an invertible `X`, and
every invertible element of `V` is a scalar multiple of `X`, then `V` is the line through `X`.
Projectively, the line through `X` and any other point `Y` of `V` contains at most `n` singular
points, while it has at least `n + 2` points when the field has more than `n` elements, so it
contains an invertible point other than `X`. When the equations defining `V` are reductions of
integral equations modulo a prime, this one-dimensionality is what makes the solution liftable to
a small integral matrix (`TauCeti.LinearAlgebra.Matrix.ReductionKernel`).

## Main results

* `Polynomial.eval_det_X_add_C`: `det (X • A + B)`, evaluated at `t`, is `det (t • A + B)`.
* `Submodule.eq_span_singleton_of_forall_det_ne_zero`: a subspace of matrices whose invertible
  elements are the nonzero multiples of one invertible matrix is spanned by it.
-/

public section

open Polynomial

namespace Polynomial

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- Evaluating the determinant of the polynomial pencil `X • A + B` at `t` gives
`det (t • A + B)`. -/
theorem eval_det_X_add_C (A B : Matrix n n R) (t : R) :
    (Matrix.det ((X : R[X]) • A.map C + B.map C)).eval t = (t • A + B).det := by
  rw [← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp [mul_comm (A i j)]

end Polynomial

namespace Submodule

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K]

/-- **A subspace with a unique invertible line is that line.** Let `V` be a subspace of `n × n`
matrices over a field with more than `n` elements. If `V` contains an invertible matrix `X`, and
every invertible element of `V` is a scalar multiple of `X`, then `V` is spanned by `X`. -/
theorem eq_span_singleton_of_forall_det_ne_zero (V : Submodule K (Matrix n n K))
    (hK : Fintype.card n < Cardinal.mk K) {X : Matrix n n K} (hXV : X ∈ V) (hX : X.det ≠ 0)
    (h : ∀ Y ∈ V, Y.det ≠ 0 → ∃ c : K, Y = c • X) : V = K ∙ X := by
  refine le_antisymm (fun Y hYV ↦ ?_) ((span_singleton_le_iff_mem X V).2 hXV)
  rw [mem_span_singleton]
  by_cases hY : Y.det = 0
  · -- `P t = det (X + t • Y)` has degree less than `n`, so `t * P t` does not vanish everywhere;
    -- at such a `t`, `X + t • Y` is an invertible element of `V`, hence a multiple of `X`.
    set P := Matrix.det ((Polynomial.X : K[X]) • Y.map C + X.map C) with hPdef
    have hP0 : P ≠ 0 := fun hP ↦ hX (by rw [← coeff_det_X_add_C_zero Y X, ← hPdef, hP, coeff_zero])
    have hPdeg : P.natDegree < Fintype.card n := by
      refine (natDegree_det_X_add_C_le Y X).lt_of_ne fun hdeg ↦ hP0 ?_
      rw [← leadingCoeff_eq_zero, leadingCoeff, hdeg, coeff_det_X_add_C_card, hY]
    obtain ⟨t, ht⟩ : ∃ t, (Polynomial.X * P).eval t ≠ 0 := by
      by_contra! hzero
      refine mul_ne_zero X_ne_zero hP0
        (eq_zero_of_forall_eval_zero_of_natDegree_lt_card _ hzero ?_)
      refine lt_of_le_of_lt ?_ hK
      exact_mod_cast (natDegree_mul_le.trans (by simp; omega))
    rw [eval_mul, eval_X, hPdef, eval_det_X_add_C, add_comm] at ht
    obtain ⟨c, hc⟩ := h _ (V.add_mem hXV (V.smul_mem t hYV)) (right_ne_zero_of_mul ht)
    refine ⟨t⁻¹ * (c - 1), ?_⟩
    rw [mul_smul, sub_smul, one_smul, ← hc, add_sub_cancel_left, inv_smul_smul₀
      (left_ne_zero_of_mul ht)]
  · obtain ⟨c, rfl⟩ := h Y hYV hY
    exact ⟨c, rfl⟩

end Submodule
