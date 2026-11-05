/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# Matrix inverse identities and entrywise bounds

Applying a ring homomorphism `f : R →+* S` entrywise commutes with taking the inverse of a square
matrix, provided `f` is a local homomorphism (`Matrix.map_nonsing_inv`). The inverse
`A⁻¹ = Ring.inverse (det A) • adjugate A` is built from the determinant and the adjugate, which
commute with every ring homomorphism (`RingHom.map_det`, `RingHom.map_adjugate`), and a local
homomorphism commutes with `Ring.inverse` (`map_ringInverse`).

Locality is needed: `ℤ →+* ℚ` is not local, and the `1 × 1` matrix `2` over `ℤ` has inverse `0`,
while its image in `ℚ` has inverse `1 / 2`. Every ring homomorphism from a field to a nontrivial
ring is local, so the statement applies, for instance, to the casts `ℚ → ℝ` and `ℝ → ℂ`: an
inverse computed over `ℚ` is the inverse over `ℝ`.

For invertible real matrices `A`, `B`, inverse entries bounded by `L ≥ 0` and entrywise
difference bounded by `d ≥ 0` give `|A⁻¹ i j - B⁻¹ i j| ≤ (card ι)² L² d`
(`Matrix.abs_inv_sub_inv_apply_le`). This estimate supplies the inverse-entry Hölder modulus.
It is adapted from the
[KLS formalization](https://github.com/human-ai-mathematics/kls-lean/tree/e60bc39b18ef691263c66e2dba8d64726f18060d/formalization/FunctionalInequalities/Analysis/Matrix).
-/

public section

namespace Matrix

variable {n R S F : Type*} [Fintype n] [DecidableEq n] [CommRing R] [CommRing S]
  [FunLike F R S] [RingHomClass F R S]

/-- A local ring homomorphism applied entrywise commutes with the inverse of a square matrix. -/
@[simp]
theorem map_nonsing_inv (f : F) [IsLocalHom f] (A : Matrix n n R) :
    A⁻¹.map f = (A.map f)⁻¹ := by
  have hdet : f A.det = (A.map f).det := RingHom.map_det (f : R →+* S) A
  have hadj : A.adjugate.map f = (A.map f).adjugate := RingHom.map_adjugate (f : R →+* S) A
  rw [inv_def, inv_def, ← hdet, ← hadj, ← map_ringInverse f]
  ext i j
  simp

end Matrix

section InverseBound

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/--
**Entrywise modulus of the inverse.** For invertible `A`, `B` whose inverse entries are bounded
by `L ≥ 0` and whose entrywise difference is bounded by `d ≥ 0`,
`|A⁻¹ᵢⱼ − B⁻¹ᵢⱼ| ≤ n² L² d` with `n = card ι`. -/
theorem Matrix.abs_inv_sub_inv_apply_le {A B : Matrix ι ι ℝ} {L d : ℝ}
    (hA : IsUnit A) (hB : IsUnit B)
    (hL : 0 ≤ L) (hd : 0 ≤ d) (ha : ∀ i j, |A⁻¹ i j| ≤ L) (hb : ∀ i j, |B⁻¹ i j| ≤ L)
    (hab : ∀ i j, |A i j - B i j| ≤ d) (i j : ι) :
    |A⁻¹ i j - B⁻¹ i j| ≤ (Fintype.card ι : ℝ) ^ 2 * L ^ 2 * d := by
  classical
  have hi : A⁻¹ - B⁻¹ = A⁻¹ * (B - A) * B⁻¹ := Matrix.inv_sub_inv ⟨fun _ => hB, fun _ => hA⟩
  calc
    |A⁻¹ i j - B⁻¹ i j| = |∑ k : ι, ∑ l : ι, A⁻¹ i l * (B l k - A l k) * B⁻¹ k j| := by
      rw [← Matrix.sub_apply, hi]
      simp only [Matrix.mul_apply, Matrix.sub_apply, Finset.sum_mul]
    _ ≤ ∑ k : ι, ∑ l : ι, |A⁻¹ i l * (B l k - A l k) * B⁻¹ k j| := by
      exact
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _k : ι, ∑ _l : ι, L * d * L := by
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro l _
      rw [abs_mul, abs_mul, abs_sub_comm (B l k) (A l k)]
      exact
        mul_le_mul (mul_le_mul (ha i l) (hab l k) (abs_nonneg _) hL) (hb k j) (abs_nonneg _)
          (mul_nonneg hL hd)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

end InverseBound
