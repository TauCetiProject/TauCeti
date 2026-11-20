/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Transvection
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperUnitriangular.Nilpotent

/-!
# The centre of the upper-unitriangular group

Index the rows and columns of `Uₙ₊₁(R)` by `0, …, n`. For every ring `R`, an element of
`Uₙ₊₁(R)` is central exactly when all its entries strictly above the diagonal vanish, except
possibly the corner entry `(0, n)`. So the centre is the corner subgroup `{e₀ₙ(t)}`, the term
`superdiagonalSubgroup n` of the superdiagonal filtration, the last one before the trivial term
`superdiagonalSubgroup (n + 1)`. Consequently two
elements of `Uₙ₊₁(R)` have the same image in the quotient by the centre exactly when their
entries agree off the diagonal and the corner.

This last statement says that the entries away from the corner are well-defined functions on
`Uₙ₊₁(R) / Z`. It is what identifies homomorphisms into `Uₙ₊₁(R) / Z` with defining systems of
Massey products (Dwyer's correspondence).

## Main declarations

* `TauCeti.UpperUnitriangularGroup.mem_center_iff`: an element is central exactly when its
  entries strictly above the diagonal vanish away from the corner.
* `TauCeti.UpperUnitriangularGroup.center_eq_superdiagonalSubgroup`: the centre is the term
  `superdiagonalSubgroup n` of the superdiagonal filtration.
* `TauCeti.UpperUnitriangularGroup.mk_eq_mk_iff`: two elements are congruent modulo the centre
  exactly when their entries above the diagonal agree away from the corner.

## References

* Y. Harpaz and O. Wittenberg, *The Massey vanishing conjecture for number fields*, Duke Math. J.
  172 (2023), §2.
-/

public section

open Matrix

namespace TauCeti

variable {R : Type*} [Ring R]

namespace UpperUnitriangularGroup

variable {n : ℕ}

/-- The entry strictly above the diagonal at position `(i, j)` of a central element of
`Uₙ₊₁(R)` vanishes unless `(i, j)` is the corner `(0, n)`. -/
private theorem apply_eq_zero_of_mem_center {z : upperUnitriangularGroup (Fin (n + 1)) R}
    (hz : z ∈ Subgroup.center (upperUnitriangularGroup (Fin (n + 1)) R)) {i j : Fin (n + 1)}
    (hij : i < j) (hc : ¬ (i = 0 ∧ j = Fin.last n)) :
    ((z : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i j = 0 := by
  set Z := ((z : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
  -- Commute `z` with an upper transvection `e_kl(1)` and compare one entry of `z e = e z`.
  have key : ∀ {k l : Fin (n + 1)} (hkl : k < l),
      (1 + single k l (1 : R)) * Z = Z * (1 + single k l 1) := by
    intro k l hkl
    have h := (Subgroup.mem_center_iff.1 hz)
      ⟨_, transvectionUnit_mem_upperUnitriangularGroup hkl (1 : R)⟩
    simpa [Z, coe_transvectionUnit_eq_one_add_single] using
      congrArg (fun g : upperUnitriangularGroup (Fin (n + 1)) R ↦
        ((g : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R)) h
  by_cases hj : j = Fin.last n
  · -- In the last column, `i ≠ 0`: compare the `(0, j)` entries of `z e₀ᵢ(1) = e₀ᵢ(1) z`.
    have hi : 0 < i := by
      rcases Fin.eq_zero_or_eq_succ i with h | ⟨k, rfl⟩
      · exact absurd ⟨h, hj⟩ hc
      · exact Fin.succ_pos k
    have h := congrFun (congrFun (key hi) 0) j
    simpa [Matrix.add_mul, Matrix.mul_add, single_mul_apply_same,
      mul_single_apply_of_ne (hbj := hij.ne')] using h
  · -- Otherwise `j < n`: compare the `(i, n)` entries of `z eⱼₙ(1) = eⱼₙ(1) z`.
    have hjl : j < Fin.last n := lt_of_le_of_ne (Fin.le_last j) hj
    have h := congrFun (congrFun (key hjl) i) (Fin.last n)
    simpa [Matrix.add_mul, Matrix.mul_add, single_mul_apply_of_ne (h := hij.ne),
      mul_single_apply_same] using h.symm

/-- The corner matrix unit `c E₀ₙ` is absorbed by multiplication on the right with an
upper-unitriangular matrix: its first column is that of the identity. -/
private theorem mul_single_zero_last {G : Matrix (Fin (n + 1)) (Fin (n + 1)) R}
    (hG : G.IsUpperUnitriangular) (c : R) :
    G * single 0 (Fin.last n) c = single 0 (Fin.last n) c := by
  have hlt : ∀ {a b : Fin (n + 1)}, b < a → G a b = 0 := fun h ↦ hG.isUpperTriangular h
  ext a b
  by_cases hb : b = Fin.last n
  · subst hb
    rw [mul_single_apply_same]
    rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨k, rfl⟩
    · rw [hG.apply_diag, one_mul, Matrix.single_apply_same]
    · rw [hlt (Fin.succ_pos k), zero_mul,
        Matrix.single_apply_of_row_ne (Fin.succ_ne_zero k).symm]
  · rw [mul_single_apply_of_ne (hbj := hb), Matrix.single_apply_of_col_ne _ _ (Ne.symm hb)]

/-- The corner matrix unit `c E₀ₙ` is absorbed by multiplication on the left with an
upper-unitriangular matrix: its last row is that of the identity. -/
private theorem single_zero_last_mul {G : Matrix (Fin (n + 1)) (Fin (n + 1)) R}
    (hG : G.IsUpperUnitriangular) (c : R) :
    single (0 : Fin (n + 1)) (Fin.last n) c * G = single 0 (Fin.last n) c := by
  have hlt : ∀ {a b : Fin (n + 1)}, b < a → G a b = 0 := fun h ↦ hG.isUpperTriangular h
  ext a b
  by_cases ha : a = 0
  · subst ha
    rw [single_mul_apply_same]
    rcases eq_or_lt_of_le (Fin.le_last b) with rfl | h
    · rw [hG.apply_diag, mul_one, Matrix.single_apply_same]
    · rw [hlt h, mul_zero, Matrix.single_apply_of_col_ne _ _ h.ne']
  · rw [single_mul_apply_of_ne (h := ha), Matrix.single_apply_of_row_ne (Ne.symm ha)]

/-- An upper-unitriangular matrix whose entries above the diagonal vanish away from the corner
is `1 + t E₀ₙ`, with `t` its corner entry. -/
private theorem eq_one_add_single_zero_last {Z : Matrix (Fin (n + 1)) (Fin (n + 1)) R}
    (hZ : Z.IsUpperUnitriangular) (hn : 0 < n)
    (hz : ∀ i j : Fin (n + 1), i < j → ¬ (i = 0 ∧ j = Fin.last n) → Z i j = 0) :
    Z = 1 + single 0 (Fin.last n) (Z 0 (Fin.last n)) := by
  have h0l : (0 : Fin (n + 1)) ≠ Fin.last n := by
    rw [ne_eq, Fin.ext_iff, Fin.val_last, Fin.val_zero]
    omega
  ext a b
  by_cases hab : a = 0 ∧ b = Fin.last n
  · obtain ⟨rfl, rfl⟩ := hab
    rw [Matrix.add_apply, Matrix.single_apply_same, Matrix.one_apply_ne h0l, zero_add]
  · rw [Matrix.add_apply, Matrix.single_apply_of_ne
      (h := fun h : 0 = a ∧ Fin.last n = b ↦ hab ⟨h.1.symm, h.2.symm⟩), add_zero]
    rcases lt_trichotomy a b with h | rfl | h
    · rw [hz a b h hab, Matrix.one_apply_ne h.ne]
    · rw [hZ.apply_diag, Matrix.one_apply_eq]
    · rw [hZ.isUpperTriangular h, Matrix.one_apply_ne h.ne']

/-- An element of `Uₙ₊₁(R)` is central exactly when its entries strictly above the diagonal
vanish away from the corner `(0, n)`. -/
theorem mem_center_iff {z : upperUnitriangularGroup (Fin (n + 1)) R} :
    z ∈ Subgroup.center (upperUnitriangularGroup (Fin (n + 1)) R) ↔
      ∀ i j : Fin (n + 1), i < j → ¬ (i = 0 ∧ j = Fin.last n) →
        ((z : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i j = 0 := by
  refine ⟨fun hz i j hij hc ↦ apply_eq_zero_of_mem_center hz hij hc, fun hz ↦ ?_⟩
  rw [Subgroup.mem_center_iff]
  intro g
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `U₁(R)` is trivial.
    exact ext fun i j hij ↦ absurd hij (by rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]; simp)
  obtain ⟨t, hZ⟩ : ∃ t : R, ((z : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) =
      1 + single 0 (Fin.last n) t :=
    ⟨_, eq_one_add_single_zero_last (isUpperUnitriangular z) hn hz⟩
  apply Subtype.ext
  apply Units.ext
  -- Reduce to the matrix identity `g (1 + t E₀ₙ) = (1 + t E₀ₙ) g`.
  change ((g : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *
      ((z : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) =
    ((z : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *
      ((g : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
  rw [hZ, Matrix.mul_add, Matrix.add_mul, mul_single_zero_last (isUpperUnitriangular g),
    single_zero_last_mul (isUpperUnitriangular g), Matrix.mul_one, Matrix.one_mul]

/-- The centre of `Uₙ₊₁(R)` is the corner subgroup, the term `superdiagonalSubgroup n` of the
superdiagonal filtration: the matrices whose entries vanish strictly between the diagonal and the
`n`-th superdiagonal. -/
theorem center_eq_superdiagonalSubgroup :
    Subgroup.center (upperUnitriangularGroup (Fin (n + 1)) R) = superdiagonalSubgroup n := by
  ext z
  rw [mem_center_iff, mem_superdiagonalSubgroup_iff]
  constructor
  · intro hz i j hji
    rcases lt_trichotomy i j with h | rfl | h
    · refine (hz i j h fun hc ↦ ?_).trans (Matrix.one_apply_ne h.ne).symm
      rw [hc.1, hc.2, Fin.val_last, Fin.val_zero] at hji
      omega
    · rw [apply_diag, Matrix.one_apply_eq]
    · rw [isUpperTriangular z h, Matrix.one_apply_ne h.ne']
  · intro hz i j hij hc
    rw [hz i j ?_, Matrix.one_apply_ne hij.ne]
    have : (j : ℕ) < n + 1 := j.isLt
    have hc' : ¬ ((i : ℕ) = 0 ∧ (j : ℕ) = n) := fun h ↦
      hc ⟨Fin.ext h.1, Fin.ext (by rw [h.2, Fin.val_last])⟩
    have : (i : ℕ) < j := hij
    omega

/-- Two elements of `Uₙ₊₁(R)` are congruent modulo the centre exactly when their entries strictly
above the diagonal agree away from the corner `(0, n)`. Thus these entries are well-defined
functions on `Uₙ₊₁(R) / Z`. -/
theorem mk_eq_mk_iff {u v : upperUnitriangularGroup (Fin (n + 1)) R} :
    (QuotientGroup.mk u : upperUnitriangularGroup (Fin (n + 1)) R ⧸
        Subgroup.center (upperUnitriangularGroup (Fin (n + 1)) R)) = QuotientGroup.mk v ↔
      ∀ i j : Fin (n + 1), i < j → ¬ (i = 0 ∧ j = Fin.last n) →
        ((u : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i j =
          ((v : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i j := by
  rw [QuotientGroup.eq]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `U₁(R)` is trivial.
    have hlt : ∀ i j : Fin 1, ¬ i < j := fun i j ↦ by
      rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
      exact lt_irrefl 0
    exact ⟨fun _ i j hij ↦ absurd hij (hlt i j),
      fun _ ↦ mem_center_iff.2 fun i j hij ↦ absurd hij (hlt i j)⟩
  constructor
  · -- `v = u (u⁻¹ v)` and the central factor `u⁻¹ v` is `1 + t E₀ₙ`.
    intro hz i j _ hc
    obtain ⟨t, hZ⟩ : ∃ t : R, (((u⁻¹ * v : upperUnitriangularGroup (Fin (n + 1)) R) :
        GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) =
          1 + single 0 (Fin.last n) t :=
      ⟨_, eq_one_add_single_zero_last (isUpperUnitriangular _) hn (mem_center_iff.1 hz)⟩
    have hv : v = u * (u⁻¹ * v) := (mul_inv_cancel_left u v).symm
    rw [hv, Subgroup.coe_mul, Units.val_mul, hZ, Matrix.mul_add, Matrix.mul_one,
      mul_single_zero_last (isUpperUnitriangular u), Matrix.add_apply,
      Matrix.single_apply_of_ne (h := fun h : 0 = i ∧ Fin.last n = j ↦ hc ⟨h.1.symm, h.2.symm⟩),
      add_zero]
  · -- `v = u e₀ₙ(t)` with `t` the difference of the corner entries, and `e₀ₙ(t)` is central.
    intro h
    have h0l : (0 : Fin (n + 1)) < Fin.last n := by
      rw [Fin.lt_def, Fin.val_last, Fin.val_zero]
      exact hn
    set t := ((v : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) 0 (Fin.last n) -
      ((u : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) 0 (Fin.last n)
    let w : upperUnitriangularGroup (Fin (n + 1)) R :=
      ⟨transvectionUnit h0l.ne t, transvectionUnit_mem_upperUnitriangularGroup h0l t⟩
    have hw : ((w : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) =
        1 + single 0 (Fin.last n) t :=
      coe_transvectionUnit_eq_one_add_single h0l.ne t
    have hvw : v = u * w := by
      refine ext fun i j hij ↦ ?_
      rw [Subgroup.coe_mul, Units.val_mul, hw, Matrix.mul_add, Matrix.mul_one,
        mul_single_zero_last (isUpperUnitriangular u), Matrix.add_apply]
      by_cases hc : i = 0 ∧ j = Fin.last n
      · obtain ⟨rfl, rfl⟩ := hc
        rw [Matrix.single_apply_same, add_sub_cancel]
      · rw [Matrix.single_apply_of_ne
          (h := fun h : 0 = i ∧ Fin.last n = j ↦ hc ⟨h.1.symm, h.2.symm⟩), add_zero, h i j hij hc]
    rw [hvw, inv_mul_cancel_left, mem_center_iff]
    intro i j hij hc
    rw [hw, Matrix.add_apply, Matrix.one_apply_ne hij.ne, Matrix.single_apply_of_ne
      (h := fun h : 0 = i ∧ Fin.last n = j ↦ hc ⟨h.1.symm, h.2.symm⟩), add_zero]


end UpperUnitriangularGroup

end TauCeti
