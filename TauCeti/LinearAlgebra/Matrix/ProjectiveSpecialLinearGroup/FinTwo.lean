/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.LinearAlgebra.Matrix.Trace.FinTwo

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

* `Matrix.ProjectiveSpecialLinearGroup.mk_inv_mul_mul`: projection to `PSL(2, R)` preserves
  conjugation, with the inverse on the left.
* `Matrix.ProjectiveSpecialLinearGroup.mk_eq_mk_iff`: over a ring without zero divisors, two
  matrices of `SL(2, R)` have the same class exactly when they agree up to sign.
* `Matrix.ProjectiveSpecialLinearGroup.IsParabolic`: an element of `PSL(2, R)` is parabolic when
  it has a parabolic representative, and `isParabolic_mk_iff`: then every representative is.
* `Matrix.ProjectiveSpecialLinearGroup.eq_one_or_isParabolic_of_trace_sq_eq_four`: a matrix of
  `SL(2, R)` with `tr² = 4` has trivial or parabolic class.
* `Matrix.ProjectiveSpecialLinearGroup.isParabolic_conj_iff`: parabolicity is invariant under
  conjugation, `isParabolic_inv_iff`: under inversion, and `IsParabolic.pow`, `IsParabolic.zpow`:
  under nonzero powers in characteristic zero.
* `Matrix.ProjectiveSpecialLinearGroup.upperRightHom`: the translations `x ↦ !![1, x; 0, 1]`, as
  an injective additive character `R → PSL(2, R)`, parabolic exactly away from `x = 0`
  (`isParabolic_upperRightHom_iff`); `mk_mul_upperRightHom_mul_inv`: conjugation by an
  upper-triangular matrix rescales translations by the square of its top-left entry;
  `mul_zpow_mul_inv_eq_upperRightHom`: a conjugate of a translation by `w` has its `n`-th power
  conjugate to the translation by `n * w`.

* `Matrix.ProjectiveSpecialLinearGroup.mk_eq_upperRightHom`: an upper-triangular matrix with
  equal diagonal entries represents the translation by the product of its top-row entries.
* `Matrix.ProjectiveSpecialLinearGroup.exists_eq_upperRightHom_of_commute`: an element commuting
  with a nonzero translation is a translation, in any characteristic.
* `Matrix.ProjectiveSpecialLinearGroup.trace_commutatorElement_sub_two_of_mk_eq_upperRightHom`:
  the commutator trace of a translation lift and another special linear matrix.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91,
  Springer, 1983, §4.3.
* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, §2.1.
-/

public section

open scoped MatrixGroups Pointwise commutatorElement

namespace Matrix.ProjectiveSpecialLinearGroup

variable {R : Type*} [CommRing R]

/-- Projection to `PSL(2, R)` preserves conjugation, with the inverse on the left. -/
theorem mk_inv_mul_mul (S Y : SL(2, R)) :
    ((S⁻¹ * Y * S : SL(2, R)) : PSL(2, R)) = (S : PSL(2, R))⁻¹ * Y * S := by
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]

/-- An element of `PSL(2, R)` is *parabolic* when it is the class of a parabolic matrix of
`SL(2, R)`. When `R` has no zero divisors every representative is then parabolic
(`Matrix.ProjectiveSpecialLinearGroup.isParabolic_mk_iff`). -/
def IsParabolic (g : PSL(2, R)) : Prop :=
  ∃ a : SL(2, R), (a : PSL(2, R)) = g ∧ (a : GL (Fin 2) R).IsParabolic

variable [NoZeroDivisors R]

/-- Two matrices of `SL(2, R)` have the same class in `PSL(2, R)` exactly when they are equal up
to sign. -/
theorem mk_eq_mk_iff {a b : SL(2, R)} : (a : PSL(2, R)) = b ↔ b = a ∨ b = -a := by
  rw [QuotientGroup.eq, SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one, inv_mul_eq_one,
    inv_mul_eq_iff_eq_mul, mul_neg_one, eq_comm (a := a)]

/-- The class of a matrix of `SL(2, R)` is parabolic exactly when the matrix is: the only other
representative is its negative, which is parabolic along with it. -/
@[simp]
theorem isParabolic_mk_iff (a : SL(2, R)) :
    IsParabolic (a : PSL(2, R)) ↔ (a : GL (Fin 2) R).IsParabolic := by
  refine ⟨fun ⟨b, hb, hpar⟩ ↦ ?_, fun h ↦ ⟨a, rfl, h⟩⟩
  rcases mk_eq_mk_iff.1 hb with rfl | rfl
  · exact hpar
  · simpa [GeneralLinearGroup.IsParabolic] using hpar

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

/-- The class of a matrix of `SL(2, R)` with `tr² = 4` is the identity or parabolic: the
discriminant `tr² - 4` vanishes, so the matrix is parabolic unless it is scalar, and a scalar
matrix of determinant one is `±1`. -/
theorem eq_one_or_isParabolic_of_trace_sq_eq_four {a : SL(2, R)}
    (h : (a : Matrix (Fin 2) (Fin 2) R).trace ^ 2 = 4) :
    (a : PSL(2, R)) = 1 ∨ IsParabolic (a : PSL(2, R)) := by
  rw [isParabolic_mk_iff, GeneralLinearGroup.IsParabolic, SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.IsParabolic, Matrix.discr_fin_two, a.det_coe, h]
  by_cases hs : (a : Matrix (Fin 2) (Fin 2) R) ∈ Set.range (scalar (Fin 2))
  · left
    obtain ⟨r, hr⟩ := hs
    have hdet := a.det_coe
    rw [← hr, scalar_apply, det_diagonal, Fin.prod_univ_two] at hdet
    rw [← QuotientGroup.mk_one, mk_eq_mk_iff]
    rcases mul_self_eq_one_iff.1 hdet with rfl | rfl
    · exact Or.inl (Subtype.ext (by rw [← hr]; simp))
    · exact Or.inr (Subtype.ext (by rw [SpecialLinearGroup.coe_neg, ← hr]; simp))
  · exact Or.inr ⟨hs, by ring⟩

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

/-- A parabolic element of `PSL(2, K)` has infinite order: its nonzero powers are parabolic, so
none of them is the identity. -/
theorem IsParabolic.orderOf_eq_zero {K : Type*} [Field K] [CharZero K] {g : PSL(2, K)}
    (hg : IsParabolic g) : orderOf g = 0 :=
  orderOf_eq_zero_iff'.2 fun _ hn ↦ (hg.pow hn.ne').ne_one

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

omit [NoZeroDivisors R] in
/-- Conjugating a translation by an upper-triangular determinant-one matrix rescales its
parameter by the square of the top-left entry. This holds over any commutative ring. -/
theorem mk_mul_upperRightHom_mul_inv (a : SL(2, R)) (ha : a 1 0 = 0) (x : R) :
    (a : PSL(2, R)) * upperRightHom x * (a : PSL(2, R))⁻¹ = upperRightHom (a 0 0 ^ 2 * x) := by
  have hdet : a 0 0 * a 1 1 = 1 := by
    have := a.det_coe
    rw [det_fin_two, ha] at this
    simpa using this
  rw [mul_inv_eq_iff_eq_mul, upperRightHom_apply, upperRightHom_apply, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  congr 1
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe]
  rw [← Matrix.transvection, ← Matrix.transvection]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ha]
  linear_combination -(a 0 0 * x) * hdet

omit [NoZeroDivisors R] in
/-- An upper-triangular determinant-one matrix with equal diagonal entries represents the
translation by the product of its top-row entries. -/
theorem mk_eq_upperRightHom (a : SL(2, R)) (h10 : a 1 0 = 0)
    (hd : a 0 0 = a 1 1) :
    (a : PSL(2, R)) = upperRightHom (a 0 0 * a 0 1) := by
  have hsq : a 0 0 * a 0 0 = 1 := by
    simpa [h10, ← hd] using a.fin_two_mul_sub_mul_eq_one
  rw [upperRightHom_apply, QuotientGroup.eq_iff_div_mem, div_eq_mul_inv,
    SpecialLinearGroup.transvection_inv, SpecialLinearGroup.mem_center_iff]
  refine ⟨a 0 0, by simpa [sq] using hsq, ?_⟩
  rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe, ← Matrix.transvection]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h10, ← hd]
  linear_combination a 0 1 * hsq

/-- An element commuting with a nonzero translation is itself a translation. This holds over
commutative rings without zero divisors, including in characteristic two. -/
theorem exists_eq_upperRightHom_of_commute {g : PSL(2, R)} {x : R}
    (hx : x ≠ 0) (hcomm : Commute g (upperRightHom x)) : ∃ y, g = upperRightHom y := by
  induction g using QuotientGroup.induction_on with | H a => ?_
  have h := hcomm.eq
  rw [upperRightHom_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mk_eq_mk_iff] at h
  -- Work with the underlying matrices to use Mathlib's transvection entry formulas.
  have h := h.imp (congrArg (fun m : SL(2, R) ↦ (m : Matrix (Fin 2) (Fin 2) R)))
    (congrArg (fun m : SL(2, R) ↦ (m : Matrix (Fin 2) (Fin 2) R)))
  simp only [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_neg,
    SpecialLinearGroup.transvection_coe] at h
  rw [← Matrix.transvection] at h
  have hmul : Matrix.transvection 0 1 x * (a : Matrix (Fin 2) (Fin 2) R) =
      (a : Matrix (Fin 2) (Fin 2) R) * Matrix.transvection 0 1 x := by
    rcases h with h | h
    · exact h
    · -- The negative alternative forces 4 = 0 by the determinant-one identity.
      -- Without zero divisors this gives 2 = 0, so the minus sign disappears.
      have h00 : a 0 0 + x * a 1 0 = -a 0 0 := by
        simpa using congrArg (fun m : Matrix (Fin 2) (Fin 2) R ↦ m 0 0) h
      have h10 : a 1 0 = -a 1 0 := by
        simpa using congrArg (fun m : Matrix (Fin 2) (Fin 2) R ↦ m 1 0) h
      have hfour : (2 : R) * 2 = 0 := by
        linear_combination 2 * a 1 1 * h00 - (x * a 1 1 + 2 * a 0 1) * h10 -
          4 * a.fin_two_mul_sub_mul_eq_one
      have htwo : (2 : R) = 0 := mul_self_eq_zero.mp hfour
      have hneg (z : R) : -z = z := by linear_combination -z * htwo
      ext i j
      have hij := congrArg (fun m : Matrix (Fin 2) (Fin 2) R ↦ m i j) h
      simpa only [Matrix.neg_apply, hneg] using hij
  have h00 : x * a 1 0 = 0 := by
    simpa using congrArg (fun m : Matrix (Fin 2) (Fin 2) R ↦ m 0 0) hmul
  have h01 : a 0 1 + x * a 1 1 = a 0 1 + x * a 0 0 := by
    simpa using congrArg (fun m : Matrix (Fin 2) (Fin 2) R ↦ m 0 1) hmul
  have h10 : a 1 0 = 0 := (mul_eq_zero.mp h00).resolve_left hx
  have hd : a 0 0 = a 1 1 := mul_left_cancel₀ hx (by linear_combination -h01)
  exact ⟨a 0 0 * a 0 1, mk_eq_upperRightHom a h10 hd⟩

/-- A translation is parabolic exactly when it is nontrivial. -/
@[simp]
theorem isParabolic_upperRightHom_iff {x : R} : IsParabolic (upperRightHom x) ↔ x ≠ 0 := by
  rw [upperRightHom_apply, isParabolic_mk_iff, GeneralLinearGroup.IsParabolic,
    SpecialLinearGroup.coe_GL_coe_matrix, Matrix.isParabolic_iff_of_upperTriangular] <;>
    simp [SpecialLinearGroup.transvection_coe]

/-- If `T` represents `upperRightHom x`, that is `T = ±!![1, x; 0, 1]`, then
`tr ⁅T, X⁆ - 2 = x² c²`, where `c` is the lower-left entry of `X`. -/
theorem trace_commutatorElement_sub_two_of_mk_eq_upperRightHom {T : SL(2, R)} {x : R}
    (hT : (T : PSL(2, R)) = upperRightHom x) (X : SL(2, R)) :
    ((⁅T, X⁆ : SL(2, R)) : Matrix (Fin 2) (Fin 2) R).trace - 2 = x ^ 2 * X 1 0 ^ 2 := by
  have hTe : T 1 0 = 0 ∧ T 1 1 = T 0 0 ∧ T 0 1 ^ 2 = x ^ 2 := by
    rw [upperRightHom_apply, mk_eq_mk_iff] at hT
    rcases hT with h | h
    · simp [← h, SpecialLinearGroup.transvection_coe]
    · simp [neg_eq_iff_eq_neg.1 h.symm, SpecialLinearGroup.transvection_coe]
  rw [SpecialLinearGroup.trace_commutatorElement_sub_two_fin_two, Matrix.det_fin_two, ← hTe.2.2]
  simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, hTe.1, hTe.2.1]
  ring

end Matrix.ProjectiveSpecialLinearGroup
