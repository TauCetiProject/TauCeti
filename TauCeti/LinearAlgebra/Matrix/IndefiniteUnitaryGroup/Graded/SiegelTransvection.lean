/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup.Graded.BesselGroup
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.SiegelTransvection
import Mathlib.Algebra.Ring.Invertible
import Mathlib.Tactic.LinearCombination

/-!
# Siegel (Eichler) transformations in the unipotent group of the grades

Let `R` be a commutative ring with an involution and `J = TauCeti.gradedGram X s N` the graded
Gram matrix on `X ⊕ Fin s`, with its grades `TauCeti.gradedGrade X s` (`0` on `X` and
`s - 1 - 2a` on the string vector `e_a`). Since `J` pairs only basis vectors of opposite grades,
the form `h(v, w) = star v ⬝ᵥ J *ᵥ w` vanishes on vectors whose grades never add up to zero
(`TauCeti.dotProduct_gradedGram_mulVec_eq_zero`). In particular, a vector `x` supported in
grades `> d` is orthogonal to every vector `w` supported in grades `≥ -d`
(`TauCeti.star_dotProduct_gradedGram_mulVec_eq_zero`); for `d ≥ 0` this makes `x` isotropic.

For such `x` and `w` with `d ≥ 0`, and `c` with `c + star c + h(w, w) = 0`, the Siegel
transformation `S(x, w, c) : v ↦ v + h(x, v) (w + c x) - h(w, v) x` of
`Matrix.unitaryGroupOf.siegelTransvection` lies in the unipotent group of the grades
`TauCeti.gradedUnipotent X s N` (`TauCeti.siegelTransvection_mem_gradedUnipotent`): the matrix
`S(x, w, c) - 1` raises the grade by at least one, whatever `c`
(`TauCeti.raisesDegree_siegelTransvection_sub_one`). With `w = -y` and `c = -ς`, `S(x, w, c)` is
the Eichler map `v ↦ v + h(y, v) x - h(x, v) (y + ς x)`, and when `2` is invertible and `N` is
self-adjoint the choice `ς = h(y, y) / 2` is admissible
(`TauCeti.exists_mem_gradedUnipotent_val_eq_siegelTransvection`). For `k ∈ ℤ`, vectors `x`
supported in grades `> max 0 k` and `y` supported in grade `-k` are the case `d = max 0 k`.

These elements of the unipotent group realise prescribed entries of `u - 1`, which is what
averaging a function on the Bessel group over its unipotent part requires.

## Main results

* `TauCeti.vecMul_gradedGram_apply_eq_zero`: the entry of `v ᵥ* J` at `l` only involves the
  entries of `v` of grade `-grade l`.
* `TauCeti.dotProduct_gradedGram_mulVec_eq_zero`: `v ⬝ᵥ J *ᵥ w = 0` when no grade of the support
  of `v` is opposite to a grade of the support of `w`.
* `TauCeti.star_dotProduct_gradedGram_mulVec_eq_zero`: vectors supported in grades `> d` are
  orthogonal to vectors supported in grades `≥ -d`.
* `TauCeti.raisesDegree_siegelTransvection_sub_one`: for such vectors `x`, `w` and `d ≥ 0`, the
  matrix `S(x, w, c) - 1` raises the grade by at least one.
* `TauCeti.siegelTransvection_mem_gradedUnipotent`: the Siegel transformation lies in the
  unipotent group of the grades.
* `TauCeti.exists_mem_gradedUnipotent_val_eq_siegelTransvection`: the Eichler map with
  `ς = h(y, y) / 2` is the matrix of an element of the unipotent group of the grades.

## References

* `grh-lean`, https://github.com/lsernau/grh-lean, file `src/Lib/Weil/Periods/BesselIntegral.lean`
  (declaration `New.Grading.exists_ratCoordMatrix_eq_eichlerMap`); Apache 2.0, Copyright 2026
  Anthropic, PBC. The main statement follows this declaration, with its support conditions
  replaced by the more general ones above.
* M. Eichler, *Quadratische Formen und orthogonale Gruppen*, Grundlehren der mathematischen
  Wissenschaften 63, Springer (1952), for Eichler transformations.
-/

public section

open Matrix

namespace TauCeti

variable {R : Type*} {X : Type*} [Fintype X] [DecidableEq X] {s : ℕ} {N : R}

/-! ### Pairings of vectors supported in prescribed grades -/

section NonAssocRing

variable [NonAssocRing R]

/-- The entry of `v ᵥ* gradedGram X s N` at `l` vanishes when `v` vanishes at every basis vector
of grade `-grade l`, since the graded Gram matrix pairs only opposite grades. -/
theorem vecMul_gradedGram_apply_eq_zero {v : X ⊕ Fin s → R} {l : X ⊕ Fin s}
    (hv : ∀ m, gradedGrade X s m + gradedGrade X s l = 0 → v m = 0) :
    (v ᵥ* gradedGram X s N) l = 0 := by
  rw [vecMul_apply_eq_sum]
  refine Finset.sum_eq_zero fun m _ ↦ ?_
  by_cases hm : gradedGrade X s m + gradedGrade X s l = 0
  · rw [hv m hm, zero_mul]
  · rw [gradedGram_apply_eq_zero_of_add_ne_zero N hm, mul_zero]

end NonAssocRing

section Ring

variable [Ring R]

/-- The graded Gram matrix pairs `v` and `w` to zero when, for any two basis vectors of opposite
grades, `v` vanishes at the first or `w` at the second. -/
theorem dotProduct_gradedGram_mulVec_eq_zero {v w : X ⊕ Fin s → R}
    (h : ∀ k l, gradedGrade X s k + gradedGrade X s l = 0 → v k = 0 ∨ w l = 0) :
    v ⬝ᵥ gradedGram X s N *ᵥ w = 0 := by
  rw [dotProduct_mulVec, dotProduct]
  refine Finset.sum_eq_zero fun l _ ↦ ?_
  by_cases hl : w l = 0
  · rw [hl, mul_zero]
  · rw [vecMul_gradedGram_apply_eq_zero fun m hm ↦ (h m l hm).resolve_right hl, zero_mul]

variable [StarAddMonoid R] {d : ℤ} {x w : X ⊕ Fin s → R}

/-- A vector `x` supported in grades `> d` is orthogonal to every vector `w` supported in grades
`≥ -d`, for the form of the graded Gram matrix. -/
theorem star_dotProduct_gradedGram_mulVec_eq_zero (hx : ∀ p, gradedGrade X s p ≤ d → x p = 0)
    (hw : ∀ q, gradedGrade X s q < -d → w q = 0) :
    star x ⬝ᵥ gradedGram X s N *ᵥ w = 0 :=
  dotProduct_gradedGram_mulVec_eq_zero fun k l hkl ↦ by
    by_cases hk : gradedGrade X s k ≤ d
    · exact .inl (by rw [Pi.star_apply, hx k hk, star_zero])
    · exact .inr (hw l (by omega))

end Ring

/-! ### Siegel transformations in the unipotent group of the grades -/

section CommRing

variable [CommRing R] {d : ℤ} {x w : X ⊕ Fin s → R}

/-- For `0 ≤ d`, a vector `x` supported in grades `> d` and a vector `w` supported in grades
`≥ -d`, the Siegel transformation `S(x, w, c) = 1 + (w + c x) (σ(x)ᵀ J) - ε x (σ(w)ᵀ J)` of the
graded Gram matrix `J`, for any ring endomorphism `σ` and any scalars `ε` and `c`, differs from
the identity by a matrix raising the grade by at least one. -/
theorem raisesDegree_siegelTransvection_sub_one (σ : R →+* R) (ε c : R) (hd : 0 ≤ d)
    (hx : ∀ p, gradedGrade X s p ≤ d → x p = 0) (hw : ∀ q, gradedGrade X s q < -d → w q = 0) :
    RaisesDegree (gradedGrade X s) 1
      ((gradedGram X s N).siegelTransvection σ ε x w c - 1) := by
  -- An entry `j` of `σ(v)ᵀ J` is zero unless `v` has a nonzero entry of grade `-grade j`.
  have hvecMul (v : X ⊕ Fin s → R) (j : X ⊕ Fin s) (hj : ((σ ∘ v) ᵥ* gradedGram X s N) j ≠ 0) :
      ∃ m, v m ≠ 0 ∧ gradedGrade X s m + gradedGrade X s j = 0 := by
    by_contra! hv
    exact hj (vecMul_gradedGram_apply_eq_zero fun m hm ↦ by
      rw [Function.comp_apply, not_ne_iff.1 fun h ↦ hv m h hm, map_zero])
  rw [siegelTransvection_def, add_sub_assoc, add_sub_cancel_left]
  refine RaisesDegree.sub ?_ (RaisesDegree.smul ?_ ε) <;>
    refine raisesDegree_iff.2 fun i j hij ↦ ?_ <;> rw [vecMulVec_apply] at hij
  · -- `(w + c x)_i` and `(σ(x)ᵀ J)_j` are nonzero: `grade j < -d`, and `grade i ≥ -d`.
    obtain ⟨m, hm, hmj⟩ := hvecMul x j (right_ne_zero_of_mul hij)
    have hdm := not_le.1 (mt (hx m) hm)
    have hi : w i ≠ 0 ∨ x i ≠ 0 := by
      by_contra! h
      exact left_ne_zero_of_mul hij (by rw [Pi.add_apply, Pi.smul_apply, h.1, h.2, smul_zero,
        add_zero])
    rcases hi with hi | hi
    · have := not_lt.1 (mt (hw i) hi)
      omega
    · have := not_le.1 (mt (hx i) hi)
      omega
  · -- `x_i` and `(σ(w)ᵀ J)_j` are nonzero: `grade i > d ≥ grade j`.
    obtain ⟨m, hm, hmj⟩ := hvecMul w j (right_ne_zero_of_mul hij)
    have := not_lt.1 (mt (hw m) hm)
    have := not_le.1 (mt (hx i) (left_ne_zero_of_mul hij))
    omega

variable [StarRing R]

/-- **Siegel transformations in the unipotent group of the grades.** For `0 ≤ d`, a vector `x`
supported in grades `> d` (hence isotropic), a vector `w` supported in grades `≥ -d` (hence
orthogonal to `x`) and `c` with `c + star c + h(w, w) = 0`, the Siegel transformation
`S(x, w, c) : v ↦ v + h(x, v) (w + c x) - h(w, v) x`, an isometry of the graded Gram matrix, lies
in the unipotent group of the grades. The isotropy and orthogonality hypotheses needed to form
it follow from the support conditions by `star_dotProduct_gradedGram_mulVec_eq_zero`. -/
theorem siegelTransvection_mem_gradedUnipotent {c : R} (hJ : (gradedGram X s N).IsHermitian)
    (hxx : star x ⬝ᵥ gradedGram X s N *ᵥ x = 0) (hxw : star x ⬝ᵥ gradedGram X s N *ᵥ w = 0)
    (hc : c + star c + star w ⬝ᵥ gradedGram X s N *ᵥ w = 0) (hd : 0 ≤ d)
    (hx : ∀ p, gradedGrade X s p ≤ d → x p = 0) (hw : ∀ q, gradedGrade X s q < -d → w q = 0) :
    unitaryGroupOf.siegelTransvection hJ hxx hxw hc ∈ gradedUnipotent X s N := by
  rw [mem_gradedUnipotent_iff_raisesDegree, unitaryGroupOf.val_siegelTransvection]
  exact raisesDegree_siegelTransvection_sub_one _ _ _ hd hx hw

/-- **Eichler maps in the unipotent group of the grades.** Let `2` be invertible and `N`
self-adjoint. For `0 ≤ d`, a vector `x` supported in grades `> d` and a vector `y` supported in
grades `≥ -d`, the Eichler map `v ↦ v + h(y, v) x - h(x, v) (y + ς x)` with `ς = h(y, y) / 2`,
which is the Siegel transformation `S(x, -y, -ς)`, is the matrix of an element of the unipotent
group of the grades. For `k ∈ ℤ`, `x` supported in grades `> max 0 k` and `y` supported in grade
`-k` satisfy these conditions with `d = max 0 k`. -/
theorem exists_mem_gradedUnipotent_val_eq_siegelTransvection [Invertible (2 : R)]
    {y : X ⊕ Fin s → R} (hN : star N = N) (hd : 0 ≤ d)
    (hx : ∀ p, gradedGrade X s p ≤ d → x p = 0) (hy : ∀ q, gradedGrade X s q < -d → y q = 0) :
    ∃ u ∈ gradedUnipotent X s N, ((u : GL (X ⊕ Fin s) R) : Matrix (X ⊕ Fin s) (X ⊕ Fin s) R) =
      (gradedGram X s N).siegelTransvection (starRingEnd R) 1 x (-y)
        (-(⅟2 * (star y ⬝ᵥ gradedGram X s N *ᵥ y))) := by
  have hJ : (gradedGram X s N).IsHermitian := isHermitian_gradedGram hN
  have hy' : ∀ q, gradedGrade X s q < -d → (-y) q = 0 := fun q hq ↦ by
    rw [Pi.neg_apply, hy q hq, neg_zero]
  have hxx := star_dotProduct_gradedGram_mulVec_eq_zero (N := N) hx fun q hq ↦ hx q (by omega)
  have hxw := star_dotProduct_gradedGram_mulVec_eq_zero (N := N) hx hy'
  have hc : -(⅟2 * (star y ⬝ᵥ gradedGram X s N *ᵥ y)) +
      star (-(⅟2 * (star y ⬝ᵥ gradedGram X s N *ᵥ y))) +
      star (-y) ⬝ᵥ gradedGram X s N *ᵥ (-y) = 0 := by
    have h2 : star (⅟2 : R) = ⅟2 := ((IsSelfAdjoint.invOf_iff (2 : R)).2 (.ofNat 2)).star_eq
    rw [star_neg, star_mul', hJ.star_dotProduct_mulVec_comm, h2, star_neg, neg_dotProduct,
      mulVec_neg, dotProduct_neg, neg_neg]
    linear_combination (-(star y ⬝ᵥ gradedGram X s N *ᵥ y)) * invOf_two_add_invOf_two (R := R)
  exact ⟨_, siegelTransvection_mem_gradedUnipotent hJ hxx hxw hc hd hx hy',
    unitaryGroupOf.val_siegelTransvection hJ hxx hxw hc⟩

end CommRing

end TauCeti
