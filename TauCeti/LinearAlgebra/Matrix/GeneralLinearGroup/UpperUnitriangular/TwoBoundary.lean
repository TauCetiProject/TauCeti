/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperUnitriangular.Nilpotent
import Mathlib.Tactic.NoncommRing

/-!
# The two-boundary subgroups of upper-unitriangular groups

Fix a ring `R` and natural numbers `n`, `r`, `s`, and index `(n + 1) × (n + 1)` matrices by
`0, …, n`. The **two-boundary subgroup** `P_(r,s)` of `Uₙ₊₁(R)` consists of the matrices that
agree with the identity except in row `0` at columns `j ≥ n - s` and in column `n` at rows
`i ≤ r`, strictly above the diagonal. For `n = 4`, `r = 2`, `s = 1` the free entries are

```text
1 0 0 * *
  1 0 0 *
    1 0 *
      1 0
        1
```

The corner `(0, n)` lies in both ranges and is one coordinate. Writing `g = 1 + X`, the product
of two such strictly upper triangular `X` is supported at the corner, and more precisely the
support condition is stable under multiplication on either side by upper triangular matrices.
Hence `P_(r,s)` is a normal subgroup of `Uₙ₊₁(R)` for all `n`, `r`, `s`, it contains the
corner subgroup `Z = U^n = P_(0,0)` (`twoBoundarySubgroup_zero_zero`), and every entry other
than the corner is additive on it. For `r, s < n` its noncorner entries, the `s` first-row entries
`(0, j)` with `n - s ≤ j < n` and the `r` last-column entries `(i, n)` with `1 ≤ i ≤ r`, give an
isomorphism `P_(r,s)/Z ≅ R^(r+s)`. When `r + s < n` the corner entry is additive too, so
`P_(r,s)` is abelian and isomorphic to `R^(r+s+1)` by all its coordinates; in particular the
extension `0 → Z → P_(r,s) → P_(r,s)/Z → 0` splits. If `r + s ≥ n` and `R` is nontrivial,
`P_(r,s)` is not abelian in general: for `n = 4`, `r = s = 2` the transvections `e₀₂(1)` and
`e₂₄(1)` have commutator `e₀₄(1)`.

For `r, s ≤ n - 2` the subgroup lies in `U²`, the derived subgroup of `Uₙ₊₁(R)`
(`twoBoundarySubgroup_le_superdiagonalSubgroup`). These subgroups govern the refined lifting
problem for homomorphisms of Galois groups into `Uₙ₊₁(𝔽_p)/Z` studied by Harpaz and Wittenberg.

## Main declarations

* `TauCeti.IsTwoBoundary`: the support condition of `P_(r,s)` on a matrix.
* `TauCeti.UpperUnitriangularGroup.twoBoundarySubgroup`: the subgroup `P_(r,s)` of
  `Uₙ₊₁(R)`, normal by `TauCeti.UpperUnitriangularGroup.twoBoundarySubgroup_normal`.
* `TauCeti.UpperUnitriangularGroup.twoBoundarySubgroup_zero_zero`: `P_(0,0)` is the corner
  subgroup `U^n`, which lies in every `P_(r,s)`.
* `TauCeti.UpperUnitriangularGroup.twoBoundaryHom`: the noncorner coordinates, a surjective
  homomorphism `P_(r,s) →* R^s × R^r` with kernel the corner subgroup
  (`TauCeti.UpperUnitriangularGroup.ker_twoBoundaryHom`).
* `TauCeti.UpperUnitriangularGroup.twoBoundaryQuotientEquiv`:
  `P_(r,s)/Z ≃* R^s × R^r`.
* `TauCeti.UpperUnitriangularGroup.twoBoundaryMk`: the element of `P_(r,s)` with prescribed
  coordinates.
* `TauCeti.UpperUnitriangularGroup.twoBoundaryEquiv`: for `r + s < n`, all coordinates give
  `P_(r,s) ≃* R × R^s × R^r`, so `P_(r,s)` is abelian
  (`TauCeti.UpperUnitriangularGroup.isMulCommutative_twoBoundarySubgroup`).

## References

* Y. Harpaz and O. Wittenberg, *The Massey vanishing conjecture for number fields*, Duke Math. J.
  172 (2023), Definition 5.2 and the observations following it.
-/

public section

open Matrix

namespace TauCeti

variable {R : Type*} {n r s : ℕ}

/-- The support condition of the **two-boundary subgroup** `P_(r,s)` (Harpaz–Wittenberg,
Definition 5.2): an `(n + 1) × (n + 1)` matrix satisfies it when it agrees with the identity
except in row `0` at columns `j ≥ n - s` and in column `n` at rows `i ≤ r`, all strictly above
the diagonal. The corner `(0, n)` lies in both ranges. -/
def IsTwoBoundary [Zero R] [One R] (n r s : ℕ) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    Prop :=
  ∀ i j : Fin (n + 1), M i j ≠ (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i j →
    i < j ∧ ((i = 0 ∧ n ≤ (j : ℕ) + s) ∨ (j = Fin.last n ∧ (i : ℕ) ≤ r))

/-- Enlarging `r` and `s` weakens the two-boundary support condition. -/
theorem IsTwoBoundary.mono [Zero R] [One R] {r' s' : ℕ}
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) R} (hM : IsTwoBoundary n r s M) (hr : r ≤ r')
    (hs : s ≤ s') : IsTwoBoundary n r' s' M := by
  intro i j hij
  obtain ⟨hlt, h | h⟩ := hM i j hij
  · exact ⟨hlt, Or.inl ⟨h.1, by omega⟩⟩
  · exact ⟨hlt, Or.inr ⟨h.1, by omega⟩⟩

/-! ### The support condition on `M - 1` -/

/-- The positions allowed by the two-boundary support condition, on the underlying indices. -/
private def Allowed (n r s : ℕ) (i j : Fin (n + 1)) : Prop :=
  (i : ℕ) < j ∧
    (((i : ℕ) = 0 ∧ n ≤ (j : ℕ) + s) ∨ ((j : ℕ) = n ∧ (i : ℕ) ≤ r))

/-- A matrix vanishes outside the two-boundary positions. -/
private def Supported [Zero R] (n r s : ℕ) (X : Matrix (Fin (n + 1)) (Fin (n + 1)) R) : Prop :=
  ∀ i j, ¬ Allowed n r s i j → X i j = 0

private theorem allowed_iff {i j : Fin (n + 1)} :
    Allowed n r s i j ↔
      i < j ∧ ((i = 0 ∧ n ≤ (j : ℕ) + s) ∨ (j = Fin.last n ∧ (i : ℕ) ≤ r)) := by
  simp only [Allowed, Fin.lt_def, Fin.ext_iff, Fin.val_zero, Fin.val_last]

private theorem isTwoBoundary_iff_supported [AddGroupWithOne R]
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) R} :
    IsTwoBoundary n r s M ↔ Supported n r s (M - 1) := by
  refine forall₂_congr fun i j ↦ ?_
  rw [← allowed_iff, Matrix.sub_apply, sub_eq_zero, not_imp_comm]

section Ring

variable [Ring R]

private theorem Supported.add {X Y : Matrix (Fin (n + 1)) (Fin (n + 1)) R}
    (hX : Supported n r s X) (hY : Supported n r s Y) : Supported n r s (X + Y) := by
  intro i j hij
  simp [hX i j hij, hY i j hij]

private theorem Supported.neg {X : Matrix (Fin (n + 1)) (Fin (n + 1)) R}
    (hX : Supported n r s X) : Supported n r s (-X) := by
  intro i j hij
  simp [hX i j hij]

/-- Left multiplication by an upper triangular matrix preserves the two-boundary support. -/
private theorem Supported.isUpperTriangular_mul {T X : Matrix (Fin (n + 1)) (Fin (n + 1)) R}
    (hT : T.IsUpperTriangular) (hX : Supported n r s X) : Supported n r s (T * X) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  by_cases hki : k < i
  · rw [hT hki, zero_mul]
  · refine (congrArg _ (hX k j fun hk ↦ hij ?_)).trans (mul_zero _)
    rw [Fin.lt_def] at hki
    simp only [Allowed] at hk ⊢
    omega

/-- Right multiplication by an upper triangular matrix preserves the two-boundary support. -/
private theorem Supported.mul_isUpperTriangular {T X : Matrix (Fin (n + 1)) (Fin (n + 1)) R}
    (hT : T.IsUpperTriangular) (hX : Supported n r s X) : Supported n r s (X * T) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  by_cases hjk : j < k
  · rw [hT hjk, mul_zero]
  · refine (congrArg (· * _) (hX i k fun hk ↦ hij ?_)).trans (zero_mul _)
    rw [Fin.lt_def] at hjk
    have := j.isLt
    simp only [Allowed] at hk ⊢
    omega

/-- A product of two two-boundary supported matrices vanishes away from the corner, and
vanishes at the corner too when `r + s < n`. -/
private theorem Supported.mul_apply_eq_zero {X Y : Matrix (Fin (n + 1)) (Fin (n + 1)) R}
    (hX : Supported n r s X) (hY : Supported n r s Y) {i j : Fin (n + 1)}
    (hij : ¬((i : ℕ) = 0 ∧ (j : ℕ) = n ∧ n ≤ r + s)) : (X * Y) i j = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  by_cases hik : Allowed n r s i k
  · refine (congrArg _ (hY k j fun hkj ↦ hij ?_)).trans (mul_zero _)
    have := j.isLt
    simp only [Allowed] at hik hkj
    omega
  · rw [hX i k hik, zero_mul]

end Ring

namespace UpperUnitriangularGroup

section Ring

variable [Ring R]

private theorem supported_sub_one_mul {g h : upperUnitriangularGroup (Fin (n + 1)) R}
    (hg : Supported n r s (((g : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) - 1))
    (hh : Supported n r s (((h : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) - 1)) :
    Supported n r s
      ((((g * h : upperUnitriangularGroup (Fin (n + 1)) R) : GL (Fin (n + 1)) R) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) R) - 1) := by
  set G := ((g : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
  set H := ((h : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
  have heq : G * H - 1 = (G - 1) + G * (H - 1) := by noncomm_ring
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [heq]
  exact hg.add (hh.isUpperTriangular_mul (isUpperTriangular g))

private theorem coe_mul_coe_inv (g : upperUnitriangularGroup (Fin (n + 1)) R) :
    ((g : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *
        (((g⁻¹ : upperUnitriangularGroup (Fin (n + 1)) R) : GL (Fin (n + 1)) R) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) R) = 1 := by
  rw [Subgroup.coe_inv, Units.mul_inv]

private theorem supported_sub_one_inv {g : upperUnitriangularGroup (Fin (n + 1)) R}
    (hg : Supported n r s (((g : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) - 1)) :
    Supported n r s
      ((((g⁻¹ : upperUnitriangularGroup (Fin (n + 1)) R) : GL (Fin (n + 1)) R) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) R) - 1) := by
  set G := ((g : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
  set Ginv := (((g⁻¹ : upperUnitriangularGroup (Fin (n + 1)) R) : GL (Fin (n + 1)) R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R)
  have heq : Ginv - 1 = -((G - 1) * Ginv) := by
    rw [sub_mul, coe_mul_coe_inv, one_mul, neg_sub]
  rw [heq]
  exact (hg.mul_isUpperTriangular (isUpperTriangular g⁻¹)).neg

/-- The **two-boundary subgroup** `P_(r,s)` of `Uₙ₊₁(R)` (Harpaz–Wittenberg, Definition 5.2):
the upper-unitriangular matrices that agree with the identity except in row `0` at columns
`j ≥ n - s` and in column `n` at rows `i ≤ r`. -/
def twoBoundarySubgroup (n r s : ℕ) : Subgroup (upperUnitriangularGroup (Fin (n + 1)) R) where
  carrier := {g | IsTwoBoundary n r s
    ((g : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R)}
  one_mem' := fun _ _ hij ↦ absurd rfl hij
  mul_mem' hg hh := isTwoBoundary_iff_supported.2 <|
    supported_sub_one_mul (isTwoBoundary_iff_supported.1 hg) (isTwoBoundary_iff_supported.1 hh)
  inv_mem' hg := isTwoBoundary_iff_supported.2 <|
    supported_sub_one_inv (isTwoBoundary_iff_supported.1 hg)

/-- Membership in `P_(r,s)` is the two-boundary support condition on the underlying matrix. -/
@[simp]
theorem mem_twoBoundarySubgroup_iff {g : upperUnitriangularGroup (Fin (n + 1)) R} :
    g ∈ twoBoundarySubgroup (R := R) n r s ↔
      IsTwoBoundary n r s ((g : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :=
  Iff.rfl

private theorem supported_of_mem {g : upperUnitriangularGroup (Fin (n + 1)) R}
    (hg : g ∈ twoBoundarySubgroup (R := R) n r s) :
    Supported n r s (((g : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) - 1) :=
  isTwoBoundary_iff_supported.1 hg

/-- The two-boundary subgroup `P_(r,s)` is normal in `Uₙ₊₁(R)`. -/
instance twoBoundarySubgroup_normal : (twoBoundarySubgroup (R := R) n r s).Normal where
  conj_mem g hg u := by
    rw [mem_twoBoundarySubgroup_iff, isTwoBoundary_iff_supported]
    set U := ((u : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    set Uinv := (((u⁻¹ : upperUnitriangularGroup (Fin (n + 1)) R) : GL (Fin (n + 1)) R) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    set G := ((g : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    have hUU : U * Uinv = 1 := coe_mul_coe_inv u
    have heq : U * G * Uinv - 1 = U * (G - 1) * Uinv := by
      rw [mul_sub, sub_mul, mul_one, hUU]
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [heq]
    exact ((supported_of_mem hg).isUpperTriangular_mul
      (isUpperTriangular u)).mul_isUpperTriangular (isUpperTriangular u⁻¹)

/-- The two-boundary subgroups increase with `r` and `s`. -/
theorem twoBoundarySubgroup_mono {r' s' : ℕ} (hr : r ≤ r') (hs : s ≤ s') :
    twoBoundarySubgroup (R := R) n r s ≤ twoBoundarySubgroup n r' s' :=
  fun _ hg ↦ IsTwoBoundary.mono hg hr hs

/-- `P_(0,0)` is the corner subgroup `U^n`: the matrices that differ from the identity only in
the corner `(0, n)`. -/
theorem twoBoundarySubgroup_zero_zero :
    twoBoundarySubgroup (R := R) n 0 0 = superdiagonalSubgroup (n := n + 1) n := by
  ext g
  rw [mem_twoBoundarySubgroup_iff, isTwoBoundary_iff_supported, mem_superdiagonalSubgroup_iff]
  refine ⟨fun hg i j hij ↦ sub_eq_zero.1 (hg i j ?_), fun hg i j hij ↦ ?_⟩
  · simp only [Allowed]
    omega
  · by_cases hji : (j : ℕ) < i + n
    · exact sub_eq_zero.2 (hg i j hji)
    · obtain rfl : i = j := by
        simp only [Allowed] at hij
        have := j.isLt
        ext
        omega
      simp

/-- The corner subgroup `U^n` lies in every two-boundary subgroup. -/
theorem superdiagonalSubgroup_le_twoBoundarySubgroup :
    superdiagonalSubgroup (n := n + 1) n ≤ twoBoundarySubgroup (R := R) n r s :=
  twoBoundarySubgroup_zero_zero (R := R) (n := n) ▸
    twoBoundarySubgroup_mono (Nat.zero_le r) (Nat.zero_le s)

/-- If `r + m ≤ n` and `s + m ≤ n`, then `P_(r,s)` lies in `U^m`. For `m = 2` this places
`P_(r,s)` in the derived subgroup of `Uₙ₊₁(R)` whenever `r, s ≤ n - 2`. -/
theorem twoBoundarySubgroup_le_superdiagonalSubgroup {m : ℕ} (hr : r + m ≤ n)
    (hs : s + m ≤ n) :
    twoBoundarySubgroup (R := R) n r s ≤ superdiagonalSubgroup (n := n + 1) m := by
  intro g hg
  rw [mem_superdiagonalSubgroup_iff]
  intro i j hij
  refine sub_eq_zero.1 (supported_of_mem hg i j ?_)
  simp only [Allowed]
  omega

/-- The corner subgroup `U^n` is normal in `P_(r,s)`, being `P_(0,0)`; this makes
`P_(r,s)/U^n` a group. -/
instance superdiagonalSubgroup_subgroupOf_twoBoundarySubgroup_normal :
    ((superdiagonalSubgroup (R := R) (n := n + 1) n).subgroupOf
      (twoBoundarySubgroup n r s)).Normal := by
  rw [← twoBoundarySubgroup_zero_zero]
  infer_instance

/-- Every entry of a product in `P_(r,s)` other than the corner is the sum of the entries of the
factors, minus the identity entry; the corner is additive too when `r + s < n`. -/
private theorem coe_mul_apply {g h : upperUnitriangularGroup (Fin (n + 1)) R}
    (hg : g ∈ twoBoundarySubgroup (R := R) n r s) (hh : h ∈ twoBoundarySubgroup (R := R) n r s)
    {i j : Fin (n + 1)} (hij : i = 0 → j = Fin.last n → r + s < n) :
    (((g * h : upperUnitriangularGroup (Fin (n + 1)) R) : GL (Fin (n + 1)) R) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) R) i j =
      ((g : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i j +
        ((h : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i j -
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i j := by
  have hzero := (supported_of_mem hg).mul_apply_eq_zero (supported_of_mem hh)
    fun hn ↦ by have := hij (Fin.ext (by simpa using hn.1)) (Fin.ext hn.2.1); omega
  set G := ((g : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
  set H := ((h : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
  have heq : G * H = (G - 1) * (H - 1) + G + H - 1 := by noncomm_ring
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [heq]
  simp only [Matrix.sub_apply, Matrix.add_apply, hzero, zero_add]

private theorem zero_ne_last (hn : 0 < n) : (0 : Fin (n + 1)) ≠ Fin.last n := by
  simp only [Ne, Fin.ext_iff, Fin.val_zero, Fin.val_last]
  omega

private theorem zero_ne_row (hs : s < n) (k : Fin s) :
    (0 : Fin (n + 1)) ≠ ⟨n - s + k, by omega⟩ := by
  simp only [Ne, Fin.ext_iff, Fin.val_zero]
  omega

private theorem row_ne_last (hs : s < n) (k : Fin s) :
    (⟨n - s + k, by omega⟩ : Fin (n + 1)) ≠ Fin.last n := by
  simp only [Ne, Fin.ext_iff, Fin.val_last]
  omega

private theorem col_ne_zero (hr : r < n) (k : Fin r) :
    (⟨k + 1, by omega⟩ : Fin (n + 1)) ≠ 0 := by
  simp only [Ne, Fin.ext_iff, Fin.val_zero]
  omega

private theorem col_ne_last (hr : r < n) (k : Fin r) :
    (⟨k + 1, by omega⟩ : Fin (n + 1)) ≠ Fin.last n := by
  simp only [Ne, Fin.ext_iff, Fin.val_last]
  omega

/-- A two-boundary position is the corner, a first-row position `(0, n - s + k)` with `k < s`, or
a last-column position `(k + 1, n)` with `k < r`. -/
private theorem allowed_cases (hr : r < n) (hs : s < n) {i j : Fin (n + 1)}
    (hij : Allowed n r s i j) :
    (i = 0 ∧ j = Fin.last n) ∨ (∃ k : Fin s, i = 0 ∧ j = ⟨n - s + k, by omega⟩) ∨
      ∃ k : Fin r, i = ⟨k + 1, by omega⟩ ∧ j = Fin.last n := by
  simp only [Allowed] at hij
  have := j.isLt
  by_cases hc : (i : ℕ) = 0 ∧ (j : ℕ) = n
  · exact Or.inl ⟨Fin.ext hc.1, Fin.ext hc.2⟩
  by_cases hi : (i : ℕ) = 0
  · exact Or.inr <| Or.inl ⟨⟨j - (n - s), by omega⟩, Fin.ext hi, Fin.ext (by dsimp only; omega)⟩
  · exact Or.inr <| Or.inr ⟨⟨i - 1, by omega⟩, Fin.ext (by dsimp only; omega),
      Fin.ext (by simp only [Fin.val_last]; omega)⟩

/-- The **noncorner coordinates** of `P_(r,s)` for `r, s < n`: the first-row entries
`(0, n - s + k)`, `k < s`, and the last-column entries `(k + 1, n)`, `k < r`. They form a
homomorphism to `R^s × R^r`, surjective with kernel the corner subgroup. -/
def twoBoundaryHom (hr : r < n) (hs : s < n) :
    twoBoundarySubgroup (R := R) n r s →* Multiplicative ((Fin s → R) × (Fin r → R)) where
  toFun g := Multiplicative.ofAdd
    (fun k ↦ (g : GL (Fin (n + 1)) R) 0 ⟨n - s + k, by omega⟩,
      fun k ↦ (g : GL (Fin (n + 1)) R) ⟨k + 1, by omega⟩ (Fin.last n))
  map_one' := by
    refine congrArg Multiplicative.ofAdd (Prod.ext (funext fun k ↦ ?_) (funext fun k ↦ ?_)) <;>
      simp only [OneMemClass.coe_one, Units.val_one]
    · exact Matrix.one_apply_ne (zero_ne_row hs k)
    · exact Matrix.one_apply_ne (col_ne_last hr k)
  map_mul' g h := by
    refine congrArg Multiplicative.ofAdd (Prod.ext (funext fun k ↦ ?_) (funext fun k ↦ ?_)) <;>
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, toAdd_ofAdd] <;>
      rw [Subgroup.coe_mul _ g h]
    · rw [coe_mul_apply g.property h.property fun _ h ↦ absurd h (row_ne_last hs k),
        Matrix.one_apply_ne (zero_ne_row hs k), sub_zero]
    · rw [coe_mul_apply g.property h.property fun h _ ↦ absurd h (col_ne_zero hr k),
        Matrix.one_apply_ne (col_ne_last hr k), sub_zero]

variable (hr : r < n) (hs : s < n)

/-- The noncorner coordinates of an element of `P_(r,s)`: its first-row entries
`(0, n - s + k)` and its last-column entries `(k + 1, n)`. -/
@[simp]
theorem toAdd_twoBoundaryHom_apply (g : twoBoundarySubgroup (R := R) n r s) :
    (twoBoundaryHom hr hs g).toAdd =
      (fun k : Fin s ↦ (g : GL (Fin (n + 1)) R) 0 ⟨n - s + k, by omega⟩,
        fun k : Fin r ↦ (g : GL (Fin (n + 1)) R) ⟨k + 1, by omega⟩ (Fin.last n)) :=
  (rfl)

/-- The kernel of the noncorner coordinates is the corner subgroup `U^n`, viewed in `P_(r,s)`. -/
theorem ker_twoBoundaryHom :
    (twoBoundaryHom (R := R) hr hs).ker =
      (superdiagonalSubgroup (n := n + 1) n).subgroupOf (twoBoundarySubgroup n r s) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_superdiagonalSubgroup_iff,
    ← toAdd_eq_zero, toAdd_twoBoundaryHom_apply, Prod.ext_iff, funext_iff, funext_iff]
  simp only [Prod.fst_zero, Prod.snd_zero, Pi.zero_apply]
  constructor
  · rintro ⟨hrow, hcol⟩ i j hij
    by_contra hne
    have hA : Allowed n r s i j := by
      by_contra hA
      exact hne (sub_eq_zero.1 (supported_of_mem g.property i j hA))
    rcases allowed_cases hr hs hA with ⟨rfl, rfl⟩ | ⟨k, rfl, rfl⟩ | ⟨k, rfl, rfl⟩
    · simp at hij
    · exact hne ((hrow k).trans (Matrix.one_apply_ne (zero_ne_row hs k)).symm)
    · exact hne ((hcol k).trans (Matrix.one_apply_ne (col_ne_last hr k)).symm)
  · intro hg
    refine ⟨fun k ↦ ?_, fun k ↦ ?_⟩
    · exact (hg _ _ (by simp only [Fin.val_zero]; omega)).trans
        (Matrix.one_apply_ne (zero_ne_row hs k))
    · exact (hg _ _ (by simp only [Fin.val_last]; omega)).trans
        (Matrix.one_apply_ne (col_ne_last hr k))

/-- An element of `P_(r,s)`, for `r, s < n`, is determined by its corner entry and its noncorner
coordinates. -/
theorem twoBoundarySubgroup_ext {g h : twoBoundarySubgroup (R := R) n r s}
    (hc : (g : GL (Fin (n + 1)) R) 0 (Fin.last n) = (h : GL (Fin (n + 1)) R) 0 (Fin.last n))
    (hco : twoBoundaryHom hr hs g = twoBoundaryHom hr hs h) : g = h := by
  have hco' := congrArg Multiplicative.toAdd hco
  simp only [toAdd_twoBoundaryHom_apply, Prod.ext_iff, funext_iff] at hco'
  refine Subtype.ext <| Subtype.ext <| Units.ext <| Matrix.ext fun i j ↦ ?_
  by_cases hij : Allowed n r s i j
  · rcases allowed_cases hr hs hij with ⟨rfl, rfl⟩ | ⟨k, rfl, rfl⟩ | ⟨k, rfl, rfl⟩
    · exact hc
    · exact hco'.1 k
    · exact hco'.2 k
  · rw [← sub_left_inj (a := (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i j),
      ← Matrix.sub_apply, ← Matrix.sub_apply, supported_of_mem g.property i j hij,
      supported_of_mem h.property i j hij]

end Ring

/-! ### Elements with prescribed coordinates -/

section Construction

variable [Ring R]

/-- The strictly upper triangular matrix with `c` in the corner `(0, n)`, `a k` at the
first-row position `(0, n - s + k)` and `b k` at the last-column position `(k + 1, n)`, and zero
elsewhere.
Positions on or below the diagonal are excluded, so that the matrix stays strictly upper
triangular for every `n`, `r`, `s`. -/
private def boundaryMatrix (c : R) (a : Fin s → R) (b : Fin r → R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of fun i j ↦
    if (i : ℕ) = 0 ∧ (j : ℕ) = n ∧ 0 < n then c
    else if h : (i : ℕ) = 0 ∧ 0 < (j : ℕ) ∧ n ≤ (j : ℕ) + s ∧ (j : ℕ) < n then
      a ⟨j - (n - s), by omega⟩
    else if h' : 0 < (i : ℕ) ∧ (i : ℕ) ≤ r ∧ (i : ℕ) < n ∧ (j : ℕ) = n then b ⟨i - 1, by omega⟩
    else 0

private theorem supported_boundaryMatrix (c : R) (a : Fin s → R) (b : Fin r → R) :
    Supported n r s (boundaryMatrix c a b) := by
  intro i j hij
  simp only [Allowed] at hij
  simp only [boundaryMatrix, Matrix.of_apply]
  rw [ite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega)]

private theorem isUpperUnitriangular_one_add_boundaryMatrix (c : R) (a : Fin s → R)
    (b : Fin r → R) : (1 + boundaryMatrix (n := n) c a b).IsUpperUnitriangular := by
  have hlow : ∀ i j : Fin (n + 1), (j : ℕ) ≤ i → boundaryMatrix (n := n) c a b i j = 0 :=
    fun i j hji ↦ supported_boundaryMatrix c a b i j (by simp only [Allowed]; omega)
  refine (isUpperUnitriangular_def _).2 ⟨fun i j (hji : j < i) ↦ ?_, fun i ↦ ?_⟩
  · rw [Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hji), hlow i j (Fin.lt_def.1 hji).le,
      add_zero]
  · rw [Matrix.add_apply, Matrix.one_apply_eq, hlow i i le_rfl, add_zero]

/-- The element of `P_(r,s)` with corner entry `c`, first-row entries `a k` at `(0, n - s + k)`
and last-column entries `b k` at `(k + 1, n)`, all other entries above the diagonal being zero.
For `r, s < n` its coordinates are `c`, `a` and `b` (`twoBoundaryMk_apply_zero_last`,
`twoBoundaryHom_twoBoundaryMk`). -/
noncomputable def twoBoundaryMk (c : R) (a : Fin s → R) (b : Fin r → R) :
    twoBoundarySubgroup (R := R) n r s :=
  ⟨⟨(isUpperUnitriangular_one_add_boundaryMatrix c a b).toGL,
      toGL_mem_upperUnitriangularGroup _⟩, by
    rw [mem_twoBoundarySubgroup_iff, isTwoBoundary_iff_supported]
    simpa only [IsUpperUnitriangular.coe_toGL, add_sub_cancel_left] using
      supported_boundaryMatrix c a b⟩

private theorem coe_twoBoundaryMk (c : R) (a : Fin s → R) (b : Fin r → R) :
    ((twoBoundaryMk (n := n) c a b : GL (Fin (n + 1)) R) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) R) =
      1 + boundaryMatrix c a b :=
  IsUpperUnitriangular.coe_toGL _

/-- The corner entry of `twoBoundaryMk c a b` is `c`, for `n ≥ 1`. -/
@[simp]
theorem twoBoundaryMk_apply_zero_last (hn : 0 < n) (c : R) (a : Fin s → R) (b : Fin r → R) :
    (twoBoundaryMk (n := n) c a b : GL (Fin (n + 1)) R) 0 (Fin.last n) = c := by
  rw [coe_twoBoundaryMk, Matrix.add_apply, Matrix.one_apply_ne (zero_ne_last hn), zero_add]
  simp [boundaryMatrix, hn]

variable (hr : r < n) (hs : s < n)

/-- For `r, s < n` the noncorner coordinates of `twoBoundaryMk c a b` are `a` and `b`. -/
@[simp]
theorem twoBoundaryHom_twoBoundaryMk (c : R) (a : Fin s → R) (b : Fin r → R) :
    twoBoundaryHom hr hs (twoBoundaryMk c a b) = Multiplicative.ofAdd (a, b) := by
  refine congrArg Multiplicative.ofAdd (Prod.ext (funext fun k ↦ ?_) (funext fun k ↦ ?_)) <;>
    simp only [coe_twoBoundaryMk, Matrix.add_apply, boundaryMatrix, Matrix.of_apply]
  · rw [Matrix.one_apply_ne (zero_ne_row hs k), zero_add,
      ite_eq_right (by simp only [Fin.val_zero]; omega),
      dite_eq_left (by simp only [Fin.val_zero, true_and]; omega)]
    exact congrArg a (Fin.ext (Nat.add_sub_cancel_left _ _))
  · rw [Matrix.one_apply_ne (col_ne_last hr k), zero_add, ite_eq_right (by omega),
      dite_eq_right (by omega), dite_eq_left (by simp only [Fin.val_last, and_true]; omega)]
    exact congrArg b (Fin.ext (Nat.add_sub_cancel _ _))

/-- The noncorner coordinates of `P_(r,s)` are surjective, for `r, s < n`. -/
theorem twoBoundaryHom_surjective : Function.Surjective (twoBoundaryHom (R := R) hr hs) :=
  fun x ↦ ⟨twoBoundaryMk 0 x.toAdd.1 x.toAdd.2, by simp⟩

/-- **`P_(r,s)/Z ≅ R^s × R^r`**: for `r, s < n`, the noncorner coordinates identify the quotient
of the two-boundary subgroup by the corner subgroup `Z = U^n` with `R^s × R^r`. -/
noncomputable def twoBoundaryQuotientEquiv :
    twoBoundarySubgroup (R := R) n r s ⧸
        (superdiagonalSubgroup (n := n + 1) n).subgroupOf (twoBoundarySubgroup n r s) ≃*
      Multiplicative ((Fin s → R) × (Fin r → R)) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_twoBoundaryHom hr hs).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (twoBoundaryHom_surjective hr hs))

/-- The isomorphism `P_(r,s)/Z ≅ R^s × R^r` sends a class to the noncorner coordinates of any
representative. -/
@[simp]
theorem twoBoundaryQuotientEquiv_mk (g : twoBoundarySubgroup (R := R) n r s) :
    twoBoundaryQuotientEquiv hr hs (QuotientGroup.mk g) = twoBoundaryHom hr hs g :=
  (rfl)

end Construction

/-! ### The abelian case `r + s < n` -/

section Abelian

variable [Ring R] (h : r + s < n)

/-- **For `r + s < n`, `P_(r,s) ≅ R × R^s × R^r`** by its corner entry and its noncorner
coordinates. In this range the corner entry is additive as well, since no first-row position
`(0, j)` with `j ≥ n - s` has `j ≤ r`. -/
noncomputable def twoBoundaryEquiv :
    twoBoundarySubgroup (R := R) n r s ≃*
      Multiplicative (R × (Fin s → R) × (Fin r → R)) where
  toFun g := Multiplicative.ofAdd
    ((g : GL (Fin (n + 1)) R) 0 (Fin.last n), (twoBoundaryHom (by omega) (by omega) g).toAdd)
  invFun x := twoBoundaryMk x.toAdd.1 x.toAdd.2.1 x.toAdd.2.2
  left_inv g := by
    refine twoBoundarySubgroup_ext (by omega) (by omega) ?_ ?_
    · exact twoBoundaryMk_apply_zero_last (by omega) _ _ _
    · simp only [toAdd_ofAdd, twoBoundaryHom_twoBoundaryMk, Prod.mk.eta, ofAdd_toAdd]
  right_inv x := by
    simp [twoBoundaryMk_apply_zero_last (by omega : 0 < n)]
  map_mul' g g' := by
    refine congrArg Multiplicative.ofAdd (Prod.ext ?_ ?_)
    · simp only [toAdd_ofAdd, Prod.fst_add]
      rw [Subgroup.coe_mul _ g g', coe_mul_apply g.property g'.property fun _ _ ↦ h,
        Matrix.one_apply_ne (zero_ne_last (by omega)), sub_zero]
    · simp only [toAdd_ofAdd, map_mul, toAdd_mul, Prod.snd_add]

/-- The coordinates of an element of `P_(r,s)` for `r + s < n`: its corner entry, its first-row
entries `(0, n - s + k)` and its last-column entries `(k + 1, n)`. -/
@[simp]
theorem toAdd_twoBoundaryEquiv_apply (g : twoBoundarySubgroup (R := R) n r s) :
    (twoBoundaryEquiv h g).toAdd =
      ((g : GL (Fin (n + 1)) R) 0 (Fin.last n),
        fun k : Fin s ↦ (g : GL (Fin (n + 1)) R) 0 ⟨n - s + k, by omega⟩,
        fun k : Fin r ↦ (g : GL (Fin (n + 1)) R) ⟨k + 1, by omega⟩ (Fin.last n)) :=
  (rfl)

/-- The inverse of `twoBoundaryEquiv` builds the element with the given coordinates. -/
@[simp]
theorem twoBoundaryEquiv_symm_apply (x : Multiplicative (R × (Fin s → R) × (Fin r → R))) :
    (twoBoundaryEquiv h).symm x = twoBoundaryMk x.toAdd.1 x.toAdd.2.1 x.toAdd.2.2 :=
  (rfl)

/-- For `r + s < n` the two-boundary subgroup `P_(r,s)` is abelian. -/
theorem isMulCommutative_twoBoundarySubgroup (h : r + s < n) :
    IsMulCommutative (twoBoundarySubgroup (R := R) n r s) :=
  .of_comm fun g g' ↦ (twoBoundaryEquiv h).injective <| by rw [map_mul, map_mul, mul_comm]

end Abelian

end UpperUnitriangularGroup

end TauCeti
