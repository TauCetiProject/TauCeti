/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Pow

/-!
# Wedge products of two real two-forms

For real two-forms `ω` and `β`, the four-form `ω ∧ β` (the real wedge
`ContinuousAlternatingMap.pairedWedge` along multiplication) takes on `(a, b, c, d)` the value

`ω(a, b) β(c, d) - ω(a, c) β(b, d) + ω(a, d) β(b, c)`
`  + ω(b, c) β(a, d) - ω(b, d) β(a, c) + ω(c, d) β(a, b)`,

one term for each way of splitting `(a, b, c, d)` into an ordered pair for `ω` and an ordered
pair for `β` (`ContinuousAlternatingMap.pairedWedge_mul_apply_two_two`). The determinant
normalization of the wedge divides the sum over the `24` permutations by `2! 2! = 4`, which is
the number of permutations producing each such splitting.

Taking `β = ω` shows that the square `ω²` is twice the Pfaffian expression
`ω(a, b) ω(c, d) - ω(a, c) ω(b, d) + ω(a, d) ω(b, c)`
(`ContinuousAlternatingMap.wedgePow_two_apply`). Since two-forms commute under the wedge, the
square of a sum of two-forms expands by the binomial formula `(ω + β)² = ω² + 2 ω ∧ β + β²`
(`ContinuousAlternatingMap.wedgePow_two_add`). With `ContinuousAlternatingMap.wedgePow_smul` these
identities decide whether a linear combination of two-forms on a four-dimensional space is
nondegenerate, through the volume criterion `ContinuousAlternatingMap.wedgePow_ne_zero_iff`.

## Main results

* `ContinuousAlternatingMap.pairedWedge_mul_apply_two_two`: the six-term formula for `ω ∧ β`.
* `ContinuousAlternatingMap.wedgePow_two_eq`: the square of a two-form is its wedge with itself.
* `ContinuousAlternatingMap.wedgePow_two_apply`: the Pfaffian formula for `ω²`.
* `ContinuousAlternatingMap.wedgePow_two_add`: `(ω + β)² = ω² + 2 ω ∧ β + β²`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 14 (the wedge product in the determinant normalization).
-/

public section

namespace ContinuousAlternatingMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- Evaluating a two-form on the first two entries of a permuted four-tuple. -/
private theorem apply_comp_castAdd (ω : E [⋀^Fin 2]→L[ℝ] ℝ) (g : Fin 4 → E)
    (σ : Equiv.Perm (Fin 4)) :
    ω (fun i ↦ g (σ (Fin.castAdd 2 i))) = ω ![g (σ 0), g (σ 1)] := by
  congr 1
  ext i
  fin_cases i <;> rfl

/-- Evaluating a two-form on the last two entries of a permuted four-tuple. -/
private theorem apply_comp_natAdd (ω : E [⋀^Fin 2]→L[ℝ] ℝ) (g : Fin 4 → E)
    (σ : Equiv.Perm (Fin 4)) :
    ω (fun i ↦ g (σ (Fin.natAdd 2 i))) = ω ![g (σ 2), g (σ 3)] := by
  congr 1
  ext i
  fin_cases i <;> rfl

/-- **The wedge of two two-forms on four vectors**: `ω ∧ β` takes on `(a, b, c, d)` the sum,
over the six splittings of `(a, b, c, d)` into an ordered pair for `ω` followed by an ordered pair
for `β`, of the signed products of the two values. -/
theorem pairedWedge_mul_apply_two_two (ω β : E [⋀^Fin 2]→L[ℝ] ℝ) (a b c d : E) :
    pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂ ω β
        ![a, b, c, d] =
      ω ![a, b] * β ![c, d] - ω ![a, c] * β ![b, d] + ω ![a, d] * β ![b, c] +
        ω ![b, c] * β ![a, d] - ω ![b, d] * β ![a, c] + ω ![c, d] * β ![a, b] := by
  -- Values of the permutations of `Fin 4` produced by `Finset.univ_perm_fin_succ` at `2` and `3`.
  have h₂ {n : ℕ} (e : Equiv.Perm (Fin (n + 2))) (p : Fin (n + 3)) :
      Equiv.Perm.decomposeFin.symm (p, e) 2 = Equiv.swap 0 p (e 1).succ := by
    rw [← Fin.succ_one_eq_two, Equiv.Perm.decomposeFin_symm_apply_succ]
  have h₃ {n : ℕ} (e : Equiv.Perm (Fin (n + 3))) (p : Fin (n + 4)) :
      Equiv.Perm.decomposeFin.symm (p, e) 3 = Equiv.swap 0 p (e 2).succ :=
    Equiv.Perm.decomposeFin_symm_apply_succ e p 2
  have hswap (γ : E [⋀^Fin 2]→L[ℝ] ℝ) (v w : E) : γ ![w, v] = -γ ![v, w] := by
    simpa using γ.map_swap ![v, w] (i := 0) (j := 1) Fin.zero_ne_one
  -- Expand the sum over the `24` permutations of `Fin 4` and evaluate each of them.
  rw [pairedWedge_apply]
  simp only [apply_comp_castAdd, apply_comp_natAdd]
  simp only [Finset.univ_perm_fin_succ, Finset.sum_map, ← Finset.univ_product_univ,
    Finset.sum_product, Fin.sum_univ_succ, Equiv.toEmbedding_apply,
    Equiv.Perm.decomposeFin.symm_sign, Fintype.sum_unique]
  simp only [Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_one, h₂,
    h₃, Equiv.swap_apply_def, Fin.isValue]
  simp only [Nat.factorial_two, Nat.cast_ofNat, mul_inv_rev, ↓reduceIte, Nat.reduceAdd,
    Nat.succ_eq_add_one, Fin.default_eq_zero, Fin.isValue, Equiv.Perm.default_eq,
    Equiv.Perm.sign_one, mul_one, Matrix.cons_val_zero, Fin.succ_zero_eq_one, one_ne_zero,
    Matrix.cons_val_one, Fin.succ_one_eq_two, Fin.reduceEq, Matrix.cons_val, Fin.reduceSucc,
    ContinuousLinearMap.mul_apply', one_smul, mul_neg, Units.neg_smul, neg_neg, smul_eq_mul]
  -- Each of the six terms appears four times, with the two arguments of `ω` or `β` reversed.
  simp only [hswap ω b a, hswap ω c a, hswap ω d a, hswap ω c b, hswap ω d b, hswap ω d c,
    hswap β b a, hswap β c a, hswap β d a, hswap β c b, hswap β d b, hswap β d c]
  ring

/-- The square of a two-form is its wedge with itself. -/
theorem wedgePow_two_eq (ω : E [⋀^Fin 2]→L[ℝ] ℝ) :
    wedgePow ω 2 =
      pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂ ω ω := by
  rw [wedgePow_succ]
  congr 1
  ext v
  rw [wedgePow_succ, pairedWedge_apply_zero_left, wedgePow_zero_apply]
  simp only [Fin.cast_refl, CompTriple.comp_eq, ContinuousLinearMap.mul_apply', one_mul]

/-- **The Pfaffian formula**: the square of a two-form `ω` takes on `(a, b, c, d)` twice the
value `ω(a, b) ω(c, d) - ω(a, c) ω(b, d) + ω(a, d) ω(b, c)`. -/
theorem wedgePow_two_apply (ω : E [⋀^Fin 2]→L[ℝ] ℝ) (a b c d : E) :
    wedgePow ω 2 ![a, b, c, d] =
      2 * (ω ![a, b] * ω ![c, d] - ω ![a, c] * ω ![b, d] + ω ![a, d] * ω ![b, c]) := by
  rw [wedgePow_two_eq, pairedWedge_mul_apply_two_two]
  ring

/-- **The binomial formula for two-forms**: `(ω + β)² = ω² + 2 ω ∧ β + β²`. The cross terms
`ω ∧ β` and `β ∧ ω` agree because two-forms have even degree. -/
theorem wedgePow_two_add (ω β : E [⋀^Fin 2]→L[ℝ] ℝ) :
    wedgePow (ω + β) 2 = wedgePow ω 2 +
      (2 : ℝ) • pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂
        ω β + wedgePow β 2 := by
  ext v
  rw [show v = ![v 0, v 1, v 2, v 3] from (FinVec.etaExpand_eq v).symm]
  simp only [add_apply, smul_apply, smul_eq_mul, wedgePow_two_apply,
    pairedWedge_mul_apply_two_two]
  ring

end ContinuousAlternatingMap
