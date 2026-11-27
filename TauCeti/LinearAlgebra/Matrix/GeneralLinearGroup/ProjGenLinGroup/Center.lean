/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

/-!
# The center of the projective general linear group

Over an integral domain `R`, `PGL(n, R)` has trivial center for every finite index type `n`
(`Matrix.ProjGenLinGroup.center_eq_bot`), equivalently any `g : GL n R` whose commutators with
`GL n R` are central lies in `Subgroup.center (GL n R)`
(`Matrix.GeneralLinearGroup.mem_center_of_forall_commutator_mem_center`). Testing `g` against
elementary transvections `1 + Eᵢⱼ` (`i ≠ j`) forces the scalar commutator factor to be `1` via
cancellation in `[IsDomain R]`, so `g` commutes with all off-diagonal matrix units and is scalar.

## References

* J. Dieudonné, *La géométrie des groupes classiques*, 3rd ed., Springer, 1971, Chapter I, §4.
-/

public section

open scoped MatrixGroups commutatorElement

namespace Matrix

section Commutator

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R] [IsDomain R]

private theorem scalar_eq_one_of_mul_transvection_mul_scalar_eq {g : GL n R} {i j : n}
    (hij : i ≠ j) {u : Rˣ}
    (h : g * SpecialLinearGroup.toGL (SpecialLinearGroup.transvection hij (1 : R)) *
      GeneralLinearGroup.scalar n u =
        SpecialLinearGroup.toGL (SpecialLinearGroup.transvection hij (1 : R)) * g) :
    u = 1 := by
  by_contra hu
  have hu' : (u : R) - 1 ≠ 0 := sub_ne_zero.mpr fun h1 => hu (Units.ext (by simpa using h1))
  have cancel : ∀ {x : R}, (u : R) * x = x → x = 0 := fun hx =>
    (mul_eq_zero.mp (show ((u : R) - 1) * _ = 0 by linear_combination hx)).resolve_left hu'
  have hmat : (u : R) • ((g : Matrix n n R) + (g : Matrix n n R) * single i j 1) =
      (g : Matrix n n R) + single i j 1 * (g : Matrix n n R) := by
    simpa [SpecialLinearGroup.coe_GL_coe_matrix, SpecialLinearGroup.transvection_coe,
      GeneralLinearGroup.coe_scalar, ← Matrix.smul_one_eq_diagonal, mul_smul_comm,
      add_mul, mul_add] using congrArg Units.val h
  have hrow_ne : ∀ q : n, q ≠ j → (g : Matrix n n R) j q = 0 := fun q hqj => by
    refine cancel ?_
    simpa [Matrix.mul_apply, hij, hqj.symm] using congrArg (fun M : Matrix n n R => M j q) hmat
  have hgjj : (g : Matrix n n R) j j = 0 := by
    refine cancel ?_
    simpa [Matrix.mul_apply, single_apply, hij, hrow_ne i hij] using
      congrArg (fun M : Matrix n n R => M j j) hmat
  have hall : ∀ q : n, (g : Matrix n n R) j q = 0 := fun q =>
    if hqj : q = j then hqj ▸ hgjj else hrow_ne q hqj
  refine (one_ne_zero (α := R)) ?_
  simpa [Matrix.mul_apply, hall] using
    (congrArg (fun M : Matrix n n R => M j j) (Units.mul_inv g)).symm

/-- **An invertible matrix over an integral domain whose commutators with `GL n R` are central is
itself central.** -/
theorem GeneralLinearGroup.mem_center_of_forall_commutator_mem_center {g : GL n R}
    (hg : ∀ x : GL n R, ⁅g, x⁆ ∈ Subgroup.center (GL n R)) :
    g ∈ Subgroup.center (GL n R) := by
  have hcomm_single : ∀ {i j : n}, i ≠ j →
      (g : Matrix n n R) * single i j (1 : R) = single i j (1 : R) * (g : Matrix n n R) := by
    intro i j hij
    let t : GL n R := SpecialLinearGroup.toGL (SpecialLinearGroup.transvection hij (1 : R))
    have hgt : ⁅g, t⁆ * (t * g) = g * t := by simp only [commutatorElement_def]; group
    have ht : ProjGenLinGroup.mk (g * t) = ProjGenLinGroup.mk (t * g) :=
      ProjGenLinGroup.mk_eq_mk_iff'.mpr ⟨⁅g, t⁆⁻¹, (Subgroup.center (GL n R)).inv_mem (hg t), by
        rw [← hgt, ← Subgroup.mem_center_iff.mp (hg t) (t * g), mul_inv_cancel_right]⟩
    obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp ht
    rw [scalar_eq_one_of_mul_transvection_mul_scalar_eq hij hu, map_one, mul_one] at hu
    simpa [t, Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix,
      SpecialLinearGroup.transvection_coe, add_mul, mul_add] using congrArg Units.val hu
  obtain ⟨r, hr⟩ := Matrix.mem_range_scalar_of_commute_single fun i j hij =>
    (hcomm_single hij).symm
  exact Subgroup.mem_center_iff.mpr fun x => Units.ext <| by
    rw [Units.val_mul, Units.val_mul, ← hr]
    exact (Matrix.scalar_commute r (Commute.all r) (x : Matrix n n R)).symm

end Commutator

namespace ProjGenLinGroup

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R] [IsDomain R]

/-- **The center of `PGL(n, R)` over an integral domain is trivial**, including for `|n| ≤ 1`. -/
@[simp] theorem center_eq_bot : Subgroup.center PGL(n, R) = ⊥ := by
  refine eq_bot_iff.mpr fun x hx => ?_
  induction x using induction_on with
  | mk g =>
    rw [Subgroup.mem_bot, mk_eq_one]
    refine GeneralLinearGroup.mem_center_of_forall_commutator_mem_center fun h => ?_
    rw [← mk_eq_one, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp hx (mk h)).symm

end ProjGenLinGroup

end Matrix
