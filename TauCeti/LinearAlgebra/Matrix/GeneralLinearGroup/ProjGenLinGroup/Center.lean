/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

/-!
# The center of the projective general linear group

Over an integral domain `R`, the projective general linear group `PGL(n, R)` has trivial center
for every finite index type `n`, including in sizes zero and one
(`Matrix.ProjGenLinGroup.center_eq_bot`). Equivalently, an invertible matrix `g : GL n R` whose
commutator with every invertible matrix is a scalar matrix is itself a scalar matrix
(`Matrix.GeneralLinearGroup.mem_center_of_forall_commutator_mem_center`).

The proof tests `g` against the elementary transvections `1 + Eᵢⱼ` (`i ≠ j`). If
`g (1 + Eᵢⱼ) = u • (1 + Eᵢⱼ) g` with `u ≠ 1`, comparing row `j` forces `g j q = 0` first for every
`q ≠ j` (in particular `g j i = 0`) and then for `q = j`, contradicting invertibility of `g`. Thus
`u = 1`, so `g` commutes with every off-diagonal matrix unit `Eᵢⱼ`, which makes `g` scalar. No
field inversions or characteristic hypotheses are used; cancellation of `u - 1` uses only
`[IsDomain R]`.

## Main results

* `Matrix.GeneralLinearGroup.mem_center_of_forall_commutator_mem_center`: an element of `GL n R`
  commuting with `GL n R` modulo its center lies in `Subgroup.center (GL n R)`.
* `Matrix.ProjGenLinGroup.center_eq_bot`: `Subgroup.center PGL(n, R) = ⊥` over an integral domain.

## References

* J. Dieudonné, *La géométrie des groupes classiques*, 3rd edition, Springer, 1971, Chapter I, §4.
-/

public section

open scoped MatrixGroups commutatorElement

namespace Matrix

section Commutator

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R] [IsDomain R]

/-- If `g * (1 + Eᵢⱼ) * scalar u = (1 + Eᵢⱼ) * g` in `GL n R` for `i ≠ j`, then `u = 1`: otherwise
comparing row `j` annihilates the entire `j`-th row of `g`. -/
private theorem scalar_eq_one_of_mul_transvection_mul_scalar_eq {g : GL n R} {i j : n}
    (hij : i ≠ j) {u : Rˣ}
    (h : g * SpecialLinearGroup.toGL (SpecialLinearGroup.transvection hij (1 : R)) *
      GeneralLinearGroup.scalar n u =
        SpecialLinearGroup.toGL (SpecialLinearGroup.transvection hij (1 : R)) * g) :
    u = 1 := by
  by_contra hu
  have hu' : (u : R) - 1 ≠ 0 :=
    sub_ne_zero.mpr fun h1 => hu (Units.ext (by simpa using h1))
  have hmat : (u : R) • ((g : Matrix n n R) + (g : Matrix n n R) * single i j 1) =
      (g : Matrix n n R) + single i j 1 * (g : Matrix n n R) := by
    have hval := congrArg Units.val h
    simpa [SpecialLinearGroup.coe_GL_coe_matrix, SpecialLinearGroup.transvection_coe,
      GeneralLinearGroup.coe_scalar, ← Matrix.smul_one_eq_diagonal, mul_smul_comm,
      add_mul, mul_add] using hval
  have hrow_ne : ∀ q : n, q ≠ j → (g : Matrix n n R) j q = 0 := by
    intro q hqj
    have hjq : (u : R) * (g : Matrix n n R) j q = (g : Matrix n n R) j q := by
      simpa [Matrix.mul_apply, hij, hqj.symm] using congrArg (fun M : Matrix n n R => M j q) hmat
    have hsub : ((u : R) - 1) * (g : Matrix n n R) j q = 0 := by linear_combination hjq
    exact (mul_eq_zero.mp hsub).resolve_left hu'
  have hgji : (g : Matrix n n R) j i = 0 := hrow_ne i hij
  have hgjj : (g : Matrix n n R) j j = 0 := by
    have hjj : (u : R) * (g : Matrix n n R) j j = (g : Matrix n n R) j j := by
      simpa [Matrix.mul_apply, single_apply, hij, hgji] using
        congrArg (fun M : Matrix n n R => M j j) hmat
    have hsub : ((u : R) - 1) * (g : Matrix n n R) j j = 0 := by linear_combination hjj
    exact (mul_eq_zero.mp hsub).resolve_left hu'
  have hall : ∀ q : n, (g : Matrix n n R) j q = 0 := fun q =>
    if hqj : q = j then hqj ▸ hgjj else hrow_ne q hqj
  have hone : (1 : R) = 0 := by
    have hinv := congrArg (fun M : Matrix n n R => M j j) (Units.mul_inv g)
    simpa [Matrix.mul_apply, hall] using hinv.symm
  exact one_ne_zero hone

/-- **An invertible matrix over an integral domain whose commutators with `GL n R` are central is
itself central.** -/
theorem GeneralLinearGroup.mem_center_of_forall_commutator_mem_center {g : GL n R}
    (hg : ∀ x : GL n R, ⁅g, x⁆ ∈ Subgroup.center (GL n R)) :
    g ∈ Subgroup.center (GL n R) := by
  have hcomm_single : ∀ {i j : n}, i ≠ j →
      (g : Matrix n n R) * single i j (1 : R) = single i j (1 : R) * (g : Matrix n n R) := by
    intro i j hij
    let t : GL n R := SpecialLinearGroup.toGL (SpecialLinearGroup.transvection hij (1 : R))
    have ht : ProjGenLinGroup.mk (g * t) = ProjGenLinGroup.mk (t * g) := by
      rw [ProjGenLinGroup.mk_eq_mk_iff']
      refine ⟨⁅g, t⁆⁻¹, (Subgroup.center (GL n R)).inv_mem (hg t), ?_⟩
      have hc := Subgroup.mem_center_iff.mp (hg t) (t * g)
      have hgt : ⁅g, t⁆ * (t * g) = g * t := by
        simp only [commutatorElement_def]
        group
      rw [← hgt, ← hc, mul_inv_cancel_right]
    obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp ht
    have hu1 := scalar_eq_one_of_mul_transvection_mul_scalar_eq hij hu
    rw [hu1, map_one, mul_one] at hu
    have hval := congrArg Units.val hu
    simp only [t, Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix,
      SpecialLinearGroup.transvection_coe, add_mul, mul_add, mul_one, one_mul] at hval
    exact add_left_cancel hval
  have hmat_center : (g : Matrix n n R) ∈ Set.center (Matrix n n R) := by
    rw [Matrix.center_eq_range]
    rcases subsingleton_or_nontrivial n with hn | hn
    · rcases isEmpty_or_nonempty n with hempty | ⟨⟨i₀⟩⟩
      · have := hempty
        exact ⟨0, Subsingleton.elim _ _⟩
      · refine ⟨(g : Matrix n n R) i₀ i₀, ?_⟩
        ext i j
        rw [Subsingleton.elim i i₀, Subsingleton.elim j i₀]
        simp
    · obtain ⟨i₀, _⟩ := exists_pair_ne n
      refine ⟨(g : Matrix n n R) i₀ i₀, ?_⟩
      ext i j
      by_cases hij : i = j
      · subst hij
        simp only [scalar_apply, diagonal_apply_eq]
        by_cases hii₀ : i = i₀
        · rw [hii₀]
        · have hc := congrArg (fun M : Matrix n n R => M i i₀) (hcomm_single hii₀)
          simpa [Matrix.mul_apply, single_apply] using hc.symm
      · simp only [scalar_apply, diagonal_apply_ne _ hij]
        have hc := congrArg (fun M : Matrix n n R => M j j) (hcomm_single (Ne.symm hij))
        simpa [Matrix.mul_apply, single_apply, hij] using hc
  rw [Subgroup.mem_center_iff]
  intro x
  exact Units.ext (Semigroup.mem_center_iff.mp hmat_center (x : Matrix n n R))

end Commutator

namespace ProjGenLinGroup

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R] [IsDomain R]

/-- **The center of `PGL(n, R)` over an integral domain is trivial**, including for `|n| ≤ 1`. -/
@[simp]
theorem center_eq_bot : Subgroup.center PGL(n, R) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  induction x using induction_on with
  | mk g =>
    rw [Subgroup.mem_bot, mk_eq_one]
    refine GeneralLinearGroup.mem_center_of_forall_commutator_mem_center fun h => ?_
    rw [← mk_eq_one, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp hx (mk h)).symm

end ProjGenLinGroup

end Matrix
