/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.InformationTheory.Hamming
import TauCeti.InformationTheory.Hamming

/-!
# The restricted isometry property

A matrix `A` acting on `EuclideanSpace ℝ ι` has the restricted isometry property of order `s`
with constant `δ` when `(1 - δ)‖x‖² ≤ ‖A x‖² ≤ (1 + δ)‖x‖²` for every `s`-sparse `x`, that is,
every `x` with `hammingNorm (WithLp.ofLp x) ≤ s` (Foucart–Rauhut, Def 6.1).

## Main definitions

* `Matrix.HasRIP A s δ`: `(1 - δ)‖x‖² ≤ ‖A x‖² ≤ (1 + δ)‖x‖²` for every `s`-sparse `x`.

## Main results

* `Matrix.HasRIP.mono`: the restricted isometry property passes to smaller orders and larger
  constants.
* `Matrix.injOn_of_forall_mul_norm_sq_le`: a positive lower bound `c ‖x‖² ≤ ‖A x‖²` on
  `2s`-sparse vectors makes `A` injective on `s`-sparse vectors.
* `Matrix.HasRIP.injOn`: with a constant `δ < 1` at order `2s`, the matrix is injective on
  `s`-sparse vectors (Foucart–Rauhut, Thm 2.13).

## References

* S. Foucart and H. Rauhut, *A Mathematical Introduction to Compressive Sensing*, Birkhäuser,
  2013, Thm 2.13 (p. 49) and Def 6.1 (p. 133).

The definition is adapted from the lean-CKSD project (<https://github.com/bjbraams/lean-CKSD>),
file `CKSD/Nonparametric/Basic.lean`; the proofs are new.
-/

public section

noncomputable section

namespace Matrix

variable {m ι : Type*} [Fintype m] [Fintype ι] [DecidableEq ι]

/-- The matrix `A` has the restricted isometry property of order `s` with constant `δ`:
`(1 - δ)‖x‖² ≤ ‖A x‖² ≤ (1 + δ)‖x‖²` for every `s`-sparse `x`. The constant is a parameter, not
the least admissible constant. -/
def HasRIP (A : Matrix m ι ℝ) (s : ℕ) (δ : ℝ) : Prop :=
  ∀ x : EuclideanSpace ℝ ι, hammingNorm (WithLp.ofLp x) ≤ s →
    (1 - δ) * ‖x‖ ^ 2 ≤ ‖toEuclideanLin A x‖ ^ 2 ∧ ‖toEuclideanLin A x‖ ^ 2 ≤ (1 + δ) * ‖x‖ ^ 2

/-- The restricted isometry property is the two-sided bound on every `s`-sparse vector. -/
theorem hasRIP_def (A : Matrix m ι ℝ) (s : ℕ) (δ : ℝ) :
    A.HasRIP s δ ↔ ∀ x : EuclideanSpace ℝ ι, hammingNorm (WithLp.ofLp x) ≤ s →
      (1 - δ) * ‖x‖ ^ 2 ≤ ‖toEuclideanLin A x‖ ^ 2 ∧
        ‖toEuclideanLin A x‖ ^ 2 ≤ (1 + δ) * ‖x‖ ^ 2 :=
  Iff.rfl

/-- A matrix with a lower bound `c ‖x‖² ≤ ‖A x‖²`, `c > 0`, on every `2s`-sparse vector is
injective on `s`-sparse vectors. -/
theorem injOn_of_forall_mul_norm_sq_le {A : Matrix m ι ℝ} {s : ℕ} {c : ℝ} (hc : 0 < c)
    (hA : ∀ x : EuclideanSpace ℝ ι, hammingNorm (WithLp.ofLp x) ≤ 2 * s →
      c * ‖x‖ ^ 2 ≤ ‖toEuclideanLin A x‖ ^ 2) :
    Set.InjOn (toEuclideanLin A) {x | hammingNorm (WithLp.ofLp x) ≤ s} := by
  intro x hx y hy hxy
  have hsparse : hammingNorm (WithLp.ofLp (x - y)) ≤ 2 * s := by
    rw [WithLp.ofLp_sub, sub_eq_add_neg, two_mul]
    refine (TauCeti.hammingNorm_add_le _ _).trans ?_
    rw [TauCeti.hammingNorm_neg]
    exact add_le_add hx hy
  have h := hA _ hsparse
  rw [map_sub, hxy, sub_self, norm_zero] at h
  have hsq : ‖x - y‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖x - y‖]
  exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hsq))

namespace HasRIP

variable {A : Matrix m ι ℝ} {s : ℕ} {δ : ℝ}

/-- The lower restricted isometry bound `(1 - δ)‖x‖² ≤ ‖A x‖²` on an `s`-sparse vector. -/
theorem le_norm_sq (hA : A.HasRIP s δ) {x : EuclideanSpace ℝ ι}
    (hx : hammingNorm (WithLp.ofLp x) ≤ s) : (1 - δ) * ‖x‖ ^ 2 ≤ ‖toEuclideanLin A x‖ ^ 2 :=
  (hA x hx).1

/-- The upper restricted isometry bound `‖A x‖² ≤ (1 + δ)‖x‖²` on an `s`-sparse vector. -/
theorem norm_sq_le (hA : A.HasRIP s δ) {x : EuclideanSpace ℝ ι}
    (hx : hammingNorm (WithLp.ofLp x) ≤ s) : ‖toEuclideanLin A x‖ ^ 2 ≤ (1 + δ) * ‖x‖ ^ 2 :=
  (hA x hx).2

/-- The restricted isometry property passes to smaller orders and larger constants. -/
theorem mono (hA : A.HasRIP s δ) {s' : ℕ} {δ' : ℝ} (hs : s' ≤ s) (hδ : δ ≤ δ') :
    A.HasRIP s' δ' := by
  intro x hx
  have h := hA x (hx.trans hs)
  constructor <;> nlinarith [h.1, h.2, sq_nonneg ‖x‖]

/-- A matrix with the restricted isometry property of order `2s` and constant `δ < 1` is
injective on `s`-sparse vectors. -/
theorem injOn (hA : A.HasRIP (2 * s) δ) (hδ : δ < 1) :
    Set.InjOn (toEuclideanLin A) {x | hammingNorm (WithLp.ofLp x) ≤ s} :=
  injOn_of_forall_mul_norm_sq_le (sub_pos.2 hδ) fun _ hx ↦ hA.le_norm_sq hx

end HasRIP

end Matrix
