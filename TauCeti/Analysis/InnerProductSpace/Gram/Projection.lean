/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Gram.ChangeOfFamily
public import TauCeti.Analysis.InnerProductSpace.Gram.Fischer

/-!
# The Gram determinant after projecting away from one vector

Let `u` be a vector and `v` a finite family in an inner product space over `𝕜` (`ℝ` or `ℂ`).
Replacing each `v j` by `v j - (⟪u, v j⟫ / ⟪u, u⟫) • u`, its component orthogonal to `u`, is a
unitriangular change of the family `(u, v)`, and the new family has block-diagonal Gram matrix.
Hence the Gram determinant of `(u, v)` is `⟪u, u⟫` times the Gram determinant of the projected
family (`Matrix.det_gram_sumElim_unit`). This is the Schur complement of the corner entry
`⟪u, u⟫` of the Gram matrix of `(u, v)`.

For the lattice `ℤ ⊕ L` spanned by `u` and `v`, the projected family spans the orthogonal
projection of the lattice away from `u`, so this identity computes the determinant of a projected
lattice; Hunter's theorem on number fields applies it with `u` the image of `1`.

No hypothesis on `u` is needed: if `⟪u, u⟫ = 0` both sides vanish.

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, §0.8.5 (Schur complements).
-/

public section

open scoped InnerProductSpace

namespace Matrix

variable {𝕜 E ι : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The component `v - (⟪u, v⟫ / ⟪u, u⟫) • u` of `v` orthogonal to `u` is orthogonal to `u`; this
holds also when `⟪u, u⟫ = 0`, since then `⟪u, v⟫ = 0` as well. -/
theorem inner_sub_inner_div_inner_self_smul_eq_zero (u v : E) :
    ⟪u, v - (⟪u, v⟫_𝕜 / ⟪u, u⟫_𝕜) • u⟫_𝕜 = 0 := by
  by_cases hu : ⟪u, u⟫_𝕜 = 0
  · have hnorm : ‖u‖ = 0 := by
      rw [inner_self_eq_norm_sq_to_K] at hu
      exact_mod_cast pow_eq_zero_iff (two_ne_zero) |>.mp hu
    have huv : ⟪u, v⟫_𝕜 = 0 :=
      norm_le_zero_iff.mp ((norm_inner_le_norm u v).trans (by simp [hnorm]))
    simp [huv]
  · rw [inner_sub_right, inner_smul_right, div_mul_cancel₀ _ hu, sub_self]

variable [Fintype ι] [DecidableEq ι]

/-- **The Gram determinant after projecting away from a vector.** The Gram determinant of the
family `(u, v)` is `⟪u, u⟫` times the Gram determinant of the components
`v j - (⟪u, v j⟫ / ⟪u, u⟫) • u` of the `v j` orthogonal to `u`. -/
theorem det_gram_sumElim_unit (u : E) (v : ι → E) :
    (gram 𝕜 (Sum.elim (fun _ : Unit ↦ u) v)).det =
      ⟪u, u⟫_𝕜 * (gram 𝕜 fun j ↦ v j - (⟪u, v j⟫_𝕜 / ⟪u, u⟫_𝕜) • u).det := by
  set w : ι → E := fun j ↦ v j - (⟪u, v j⟫_𝕜 / ⟪u, u⟫_𝕜) • u with hw
  -- The family `(u, w)` is a unitriangular change of the family `(u, v)`.
  let U : Matrix (Unit ⊕ ι) (Unit ⊕ ι) 𝕜 :=
    fromBlocks 1 0 (of fun j _ ↦ -(⟪u, v j⟫_𝕜 / ⟪u, u⟫_𝕜)) 1
  have hU : U.det = 1 := by simp [U]
  have hfam : (fun k ↦ ∑ l, U k l • Sum.elim (fun _ : Unit ↦ u) v l) =
      Sum.elim (fun _ : Unit ↦ u) w := by
    funext k
    rcases k with _ | j
    · simp [U, Fintype.sum_sum_type]
    · have h1 : ∑ i, (1 : Matrix ι ι 𝕜) j i • v i = v j := by
        rw [Finset.sum_eq_single j (fun i _ hij ↦ by rw [one_apply_ne' hij, zero_smul])
          (by simp), one_apply_eq, one_smul]
      simp [U, Fintype.sum_sum_type, h1, hw, sub_eq_add_neg, add_comm]
  -- The Gram matrix of `(u, w)` is block diagonal.
  have hB : (of fun (_ : Unit) j ↦ ⟪u, w j⟫_𝕜) = 0 := by
    ext _ j
    exact inner_sub_inner_div_inner_self_smul_eq_zero u (v j)
  rw [← det_gram_sum_smul_of_det_eq_one hU, hfam, gram_sumElim, hB, conjTranspose_zero,
    det_fromBlocks_zero₂₁, det_unique, gram_apply]

end Matrix
