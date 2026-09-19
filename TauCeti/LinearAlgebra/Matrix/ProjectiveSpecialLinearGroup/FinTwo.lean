/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# Parabolic elements of `PSL(2, R)`

Mathlib classifies `2 × 2` matrices as parabolic, elliptic or hyperbolic
(`Matrix.IsParabolic`, with the dot-notation synonym `Matrix.GeneralLinearGroup.IsParabolic`).
Being parabolic is invariant under negation (`Matrix.isParabolic_neg_iff`), so over a ring without
zero divisors, where the center of `SL(2, R)` is `{±1}`, it descends to the projective special
linear group `PSL(2, R) = SL(2, R) ⧸ {±1}`. This is the notion of a parabolic Möbius
transformation which does not depend on a choice of matrix representative.

The model parabolic elements are the translations `upperRightHom x`, the classes of the
transvections `!![1, x; 0, 1]`, which act on the projective line by `z ↦ z + x`. Over a field
of characteristic other than two every parabolic element of `PSL(2, K)` is conjugate to one of
them; that classification, which runs through the action on the projective line, is in
`TauCeti.Topology.Compactification.OnePoint.ProjectiveLine`.

## Main declarations

* `Matrix.ProjectiveSpecialLinearGroup.IsParabolic`: an element of `PSL(2, R)` is parabolic when
  it has a parabolic representative, and `isParabolic_mk_iff`: then every representative is.
* `Matrix.ProjectiveSpecialLinearGroup.isParabolic_conj_iff`: parabolicity is invariant under
  conjugation, `isParabolic_inv_iff`: under inversion, and `IsParabolic.pow`, `IsParabolic.zpow`:
  under nonzero powers in characteristic zero.
* `Matrix.ProjectiveSpecialLinearGroup.upperRightHom`: the translations `x ↦ !![1, x; 0, 1]`, as
  an injective additive character `R → PSL(2, R)`, parabolic exactly away from `x = 0`
  (`isParabolic_upperRightHom_iff`); `mul_zpow_mul_inv_eq_upperRightHom`: a conjugate of a
  translation by `w` has its `n`-th power conjugate to the translation by `n * w`.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91,
  Springer, 1983, §4.3.
* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, §2.1.
-/

public section

open scoped MatrixGroups

namespace Matrix.ProjectiveSpecialLinearGroup

variable {R : Type*} [CommRing R]

/-- An element of `PSL(2, R)` is *parabolic* when it is the class of a parabolic matrix of
`SL(2, R)`. When `R` has no zero divisors every representative is then parabolic
(`Matrix.ProjectiveSpecialLinearGroup.isParabolic_mk_iff`). -/
def IsParabolic (g : PSL(2, R)) : Prop :=
  ∃ a : SL(2, R), (a : PSL(2, R)) = g ∧ (a : GL (Fin 2) R).IsParabolic

variable [NoZeroDivisors R]

/-- The class of a matrix of `SL(2, R)` is parabolic exactly when the matrix is: the only other
representative is its negative, which is parabolic along with it. -/
@[simp]
theorem isParabolic_mk_iff (a : SL(2, R)) :
    IsParabolic (a : PSL(2, R)) ↔ (a : GL (Fin 2) R).IsParabolic := by
  refine ⟨fun ⟨b, hb, hpar⟩ ↦ ?_, fun h ↦ ⟨a, rfl, h⟩⟩
  rw [QuotientGroup.eq, SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one] at hb
  rcases hb with hb | hb
  · rwa [inv_mul_eq_one.mp hb] at hpar
  · rw [inv_mul_eq_iff_eq_mul, mul_neg_one] at hb
    subst hb
    simpa [GeneralLinearGroup.IsParabolic] using hpar

/-- Parabolicity is invariant under conjugation in `PSL(2, R)`. -/
@[simp]
theorem isParabolic_conj_iff (g h : PSL(2, R)) :
    IsParabolic (g * h * g⁻¹) ↔ IsParabolic h := by
  induction g using QuotientGroup.induction_on with | H a => ?_
  induction h using QuotientGroup.induction_on with | H b => ?_
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    isParabolic_mk_iff, isParabolic_mk_iff, map_mul, map_mul, map_inv,
    GeneralLinearGroup.isParabolic_conj_iff]

/-- Parabolicity is invariant under conjugation in `PSL(2, R)`, with the inverse on the left. -/
@[simp]
theorem isParabolic_conj_iff' (g h : PSL(2, R)) :
    IsParabolic (g⁻¹ * h * g) ↔ IsParabolic h := by
  simpa using isParabolic_conj_iff g⁻¹ h

/-- The identity of `PSL(2, R)` is not parabolic: a parabolic matrix is not scalar. -/
@[simp]
theorem not_isParabolic_one : ¬ IsParabolic (1 : PSL(2, R)) := by
  rw [← QuotientGroup.mk_one, isParabolic_mk_iff, map_one]
  exact fun h ↦ h.1 ⟨1, by simp⟩

theorem IsParabolic.ne_one {g : PSL(2, R)} (hg : IsParabolic g) : g ≠ 1 := by
  rintro rfl
  exact not_isParabolic_one hg

/-- Parabolicity is invariant under inversion in `PSL(2, R)`: the inverse of a matrix of
`SL(2, R)` is its adjugate, which has the same trace and is scalar exactly when the matrix is. -/
@[simp]
theorem isParabolic_inv_iff {g : PSL(2, R)} : IsParabolic g⁻¹ ↔ IsParabolic g := by
  induction g using QuotientGroup.induction_on with | H a => ?_
  rw [← QuotientGroup.mk_inv, isParabolic_mk_iff, isParabolic_mk_iff]
  have hscalar (m : Matrix (Fin 2) (Fin 2) R) :
      m ∈ Set.range (scalar (Fin 2)) ↔ m 0 1 = 0 ∧ m 1 0 = 0 ∧ m 0 0 = m 1 1 := by
    refine ⟨by rintro ⟨r, rfl⟩; simp, fun ⟨h01, h10, h00⟩ ↦ ⟨m 0 0, ?_⟩⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h10, h00]
  simp only [GeneralLinearGroup.IsParabolic, SpecialLinearGroup.coe_GL_coe_matrix,
    SpecialLinearGroup.coe_inv, Matrix.IsParabolic, hscalar, Matrix.discr_fin_two,
    Matrix.adjugate_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
  simp [eq_comm, and_comm, add_comm, mul_comm]

alias ⟨_, IsParabolic.inv⟩ := isParabolic_inv_iff

/-- A nonzero power of a parabolic element of `PSL(2, K)` is parabolic. -/
theorem IsParabolic.pow {K : Type*} [Field K] [CharZero K] {g : PSL(2, K)} (hg : IsParabolic g)
    {n : ℕ} (hn : n ≠ 0) : IsParabolic (g ^ n) := by
  induction g using QuotientGroup.induction_on with | H a => ?_
  rw [← QuotientGroup.mk_pow, isParabolic_mk_iff, map_pow]
  exact ((isParabolic_mk_iff a).mp hg).pow hn

/-- A nonzero integer power of a parabolic element of `PSL(2, K)` is parabolic. -/
theorem IsParabolic.zpow {K : Type*} [Field K] [CharZero K] {g : PSL(2, K)} (hg : IsParabolic g)
    {n : ℤ} (hn : n ≠ 0) : IsParabolic (g ^ n) := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg <;>
    simpa only [zpow_neg, zpow_natCast, isParabolic_inv_iff] using hg.pow (by simpa using hn)

omit [NoZeroDivisors R] in
/-- The translation `upperRightHom x ∈ PSL(2, R)`, the class of the transvection
`!![1, x; 0, 1]`; it acts on the projective line by `z ↦ z + x`. -/
def upperRightHom : AddChar R PSL(2, R) where
  toFun x := (SpecialLinearGroup.transvection (zero_ne_one' (Fin 2)) x : PSL(2, R))
  map_zero_eq_one' := by simp [SpecialLinearGroup.transvection_coeff_zero]
  map_add_eq_mul' x y := by
    rw [SpecialLinearGroup.transvection_add, QuotientGroup.mk_mul]

omit [NoZeroDivisors R] in
theorem upperRightHom_apply (x : R) :
    upperRightHom x = (SpecialLinearGroup.transvection (zero_ne_one' (Fin 2)) x : PSL(2, R)) :=
  (rfl)

omit [NoZeroDivisors R] in
/-- Distinct translations are distinct in `PSL(2, R)`: if the classes of two transvections are
equal, then the transvections differ by a central factor, which is the transvection of the
difference of their parameters, and a transvection is central only when its parameter is zero. -/
theorem upperRightHom_injective : Function.Injective (upperRightHom : AddChar R PSL(2, R)) := by
  intro x y h
  rwa [upperRightHom_apply, upperRightHom_apply, QuotientGroup.eq,
    SpecialLinearGroup.transvection_inv, ← SpecialLinearGroup.transvection_add,
    SpecialLinearGroup.transvection_mem_center_iff, neg_add_eq_zero] at h

omit [NoZeroDivisors R] in
/-- If `σ` conjugates `γ` to the translation by `w`, it conjugates `γ ^ n` to the translation by
`n * w`. -/
theorem mul_zpow_mul_inv_eq_upperRightHom {σ γ : PSL(2, R)} {w : R}
    (h : σ * γ * σ⁻¹ = upperRightHom w) (n : ℤ) :
    σ * γ ^ n * σ⁻¹ = upperRightHom (n * w) := by
  rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, h, ← zsmul_eq_mul,
    AddChar.map_zsmul_eq_zpow]

/-- A translation is parabolic exactly when it is nontrivial. -/
@[simp]
theorem isParabolic_upperRightHom_iff {x : R} : IsParabolic (upperRightHom x) ↔ x ≠ 0 := by
  rw [upperRightHom_apply, isParabolic_mk_iff, GeneralLinearGroup.IsParabolic,
    SpecialLinearGroup.coe_GL_coe_matrix, Matrix.isParabolic_iff_of_upperTriangular] <;>
    simp [SpecialLinearGroup.transvection_coe]

end Matrix.ProjectiveSpecialLinearGroup
