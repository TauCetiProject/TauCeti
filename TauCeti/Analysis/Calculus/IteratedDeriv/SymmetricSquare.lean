/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import TauCeti.Analysis.Calculus.IteratedDeriv.Basic

/-!
# The Wronskian of a symmetric square

For functions `f`, `g` of one variable that are `C²` at `x`, the Wronskian of `f²`, `f g` and
`g²`, the determinant of the matrix of their values and first two derivatives at `x`, is twice
the cube of the Wronskian `f g' - f' g` of `f` and `g`. This is a polynomial identity in the
values of `f`, `g` and their first two derivatives; no differential equation is involved.
Consequently, if the scalar field has `2 ≠ 0` and `f g' - f' g` does not vanish at a point, then
`f²`, `f g` and `g²` are linearly independent.

For two solutions `f`, `g` of a second-order equation `w'' = q w`, the products `f²`, `f g`, `g²`
solve the symmetric-square equation, and the identity computes the Wronskian of this fundamental
system; for Airy's equation this is DLMF 9.11.2.

## Main results

* `TauCeti.det_iteratedDeriv_sq_mul_sq`: `𝒲{f², f g, g²} = 2 (f g' - f' g)³`.
* `TauCeti.linearIndependent_sq_mul_sq`: if `2 ≠ 0` in the scalar field and `f g' - f' g ≠ 0` at
  a point, then `f²`, `f g` and `g²` are linearly independent.

## References

* NIST Digital Library of Mathematical Functions, 9.11.2, <https://dlmf.nist.gov/9.11.E2>.

The determinant identity generalizes `airy_product_wronskian` in the lean-DLMF project
(<https://github.com/bjbraams/lean-DLMF>), file `DLMF/Airy/Products.lean`, which proves the case
of Airy functions; the linear independence is new.
-/

public section

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {f g : 𝕜 → 𝕜} {x : 𝕜}

/-- For `f`, `g` that are `C²` at `x`, the Wronskian of `f²`, `f g` and `g²` at `x`, the
determinant of the matrix of their values and first two derivatives, is
`2 (f g' - f' g)³`. -/
theorem det_iteratedDeriv_sq_mul_sq (hf : ContDiffAt 𝕜 2 f x) (hg : ContDiffAt 𝕜 2 g x) :
    (Matrix.of fun i j : Fin 3 => iteratedDeriv i
      (![fun t => f t ^ 2, fun t => f t * g t, fun t => g t ^ 2] j) x).det =
      2 * (f x * deriv g x - deriv f x * g x) ^ 3 := by
  have hf1 := hf.of_le one_le_two
  have hg1 := hg.of_le one_le_two
  simp only [Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Fin.val_zero, Fin.val_one,
    Fin.val_two, iteratedDeriv_zero, sq, iteratedDeriv_fun_mul hf hf, iteratedDeriv_fun_mul hf hg,
    iteratedDeriv_fun_mul hg hg, iteratedDeriv_fun_mul hf1 hf1, iteratedDeriv_fun_mul hf1 hg1,
    iteratedDeriv_fun_mul hg1 hg1, Finset.sum_range_succ, Finset.sum_range_zero, iteratedDeriv_one,
    Nat.choose_zero_right, Nat.choose_self, Nat.choose_succ_self_right, Nat.cast_one,
    Nat.cast_ofNat, zero_add, Nat.reduceAdd, tsub_zero, tsub_self, Nat.add_one_sub_one]
  ring

/-- Over a scalar field in which `2 ≠ 0`, if `f`, `g` are `C²` at `x` and their Wronskian
`f g' - f' g` does not vanish at `x`, then `f²`, `f g` and `g²` are linearly independent. -/
theorem linearIndependent_sq_mul_sq [NeZero (2 : 𝕜)] (hf : ContDiffAt 𝕜 2 f x)
    (hg : ContDiffAt 𝕜 2 g x) (hW : f x * deriv g x - deriv f x * g x ≠ 0) :
    LinearIndependent 𝕜 ![fun t => f t ^ 2, fun t => f t * g t, fun t => g t ^ 2] := by
  set u : Fin 3 → 𝕜 → 𝕜 := ![fun t => f t ^ 2, fun t => f t * g t, fun t => g t ^ 2] with hu_def
  have hu (n : Fin 3) (j : Fin 3) (_ : j ∈ Finset.univ) : ContDiffAt 𝕜 n (u j) x := by
    refine ContDiffAt.of_le (n := 2) ?_ (by exact_mod_cast Nat.le_of_lt_succ n.isLt)
    fin_cases j <;>
      simp only [hu_def, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val] <;> fun_prop
  refine Fintype.linearIndependent_iff.mpr fun c hc => congrFun (Matrix.eq_zero_of_mulVec_eq_zero
    (M := Matrix.of fun i j : Fin 3 => iteratedDeriv i (u j) x) ?_ (funext fun i => ?_))
  · rw [det_iteratedDeriv_sq_mul_sq hf hg]
    exact mul_ne_zero two_ne_zero (pow_ne_zero 3 hW)
  · have h := congrArg (fun F => iteratedDeriv i F x) hc
    rw [iteratedDeriv_sum_smul (hu i)] at h
    simpa [Matrix.mulVec, dotProduct, mul_comm] using h

end TauCeti
