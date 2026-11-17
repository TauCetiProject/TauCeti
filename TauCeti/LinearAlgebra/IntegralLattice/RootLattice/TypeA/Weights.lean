/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeA.ZeroSum

/-!
# Fundamental weights and shortest coset representatives of `Aₙ`

For `0 ≤ k ≤ n + 1`, the discriminant class `[k] = k ω₁` of `typeARootLattice n` has minimum
squared norm `k (n + 1 - k) / (n + 1)`, attained in the zero-sum hyperplane by the vector with
`1 - k / (n + 1)` in the first `k` positions and `-k / (n + 1)` in the remaining positions. Reading
its partial sums expands that vector in the Bourbaki simple roots `αⱼ = eⱼ - eⱼ₊₁` with `j`-th
coordinate `min (j + 1) k - k (j + 1) / (n + 1)`.

This file defines the computable vector `TauCeti.IntegralLattice.typeACosetRepresentative` on
`Fin n → ℚ`. For arbitrary `k : ℕ` it lies in the dual carrier and represents `k ω₁`; for
`k ≤ n + 1` it is the shortest representative of `[k]` (the Bourbaki fundamental weight `ϖₖ` for
`1 ≤ k ≤ n`, and `0` for `k = 0` and `k = n + 1`), with inner products `min j k - j k / (n + 1)`.

## Main declarations

* `TauCeti.IntegralLattice.typeACosetRepresentative` and `typeACosetRepresentativeDual`: computable
  simple-root coordinates and bundled dual-carrier representative of `[k] = k ω₁`, with
  `mk_typeACosetRepresentativeDual` and classical zero-sum coordinate formula
  `typeAIsometryZeroSumLattice_typeACosetRepresentative_apply`.
* `TauCeti.IntegralLattice.form_typeACosetRepresentative_typeASimpleRoot`,
  `form_typeACosetRepresentative`, and `form_typeACosetRepresentative_self`: simple-root pairings,
  inner products, and squared norms for `k ≤ n + 1`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate I.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Chapter 4
  §6.1 and Chapter 16 §1.
-/

public section

namespace TauCeti.IntegralLattice

open Finset Matrix

variable {n : ℕ}

/-- **The canonical coset representative of `[k] = k ω₁` in `Aₙ`** in Bourbaki simple-root
coordinates.  For arbitrary `k : ℕ` it lies in the dual carrier and represents `k ω₁`; for
`k ≤ n + 1` it is the shortest representative of `[k]` (the `k`-th Bourbaki fundamental weight `ϖₖ`
for `1 ≤ k ≤ n`, and `0` for `k = 0` and `k = n + 1`). -/
def typeACosetRepresentative (n k : ℕ) : Fin n → ℚ :=
  fun j ↦ ((min (j.val + 1) k : ℕ) : ℚ) - (k : ℚ) * (j.val + 1) / (n + 1)

/-- Each simple-root coordinate of `typeACosetRepresentative n k` is
`min (j + 1) k - k (j + 1) / (n + 1)`. -/
@[simp] theorem typeACosetRepresentative_apply (n k : ℕ) (j : Fin n) :
    typeACosetRepresentative n k j =
      ((min (j.val + 1) k : ℕ) : ℚ) - (k : ℚ) * (j.val + 1) / (n + 1) := (rfl)

/-- At `k = 0` the coset representative is the zero vector. -/
@[simp] theorem typeACosetRepresentative_zero (n : ℕ) : typeACosetRepresentative n 0 = 0 := by
  ext j; simp [typeACosetRepresentative_apply]

/-- At `k = 1` the coset representative is the first fundamental weight `ω₁`. -/
theorem typeACosetRepresentative_one (n : ℕ) :
    typeACosetRepresentative n 1 = typeAFundamentalWeight n := by
  have hn : (n : ℚ) + 1 ≠ 0 := by positivity
  ext j
  rw [typeACosetRepresentative_apply, typeAFundamentalWeight_apply,
    Nat.min_eq_right (Nat.succ_le_succ (Nat.zero_le _))]
  push_cast; field_simp; ring

/-- At `k = n + 1` the coset representative returns to the zero vector. -/
@[simp] theorem typeACosetRepresentative_add_one (n : ℕ) :
    typeACosetRepresentative n (n + 1) = 0 := by
  have hn : (n : ℚ) + 1 ≠ 0 := by positivity
  ext j
  rw [typeACosetRepresentative_apply, Pi.zero_apply, Nat.min_eq_left (Nat.le_succ_of_le j.isLt)]
  push_cast; field_simp; ring

/-- **Every `typeACosetRepresentative n k` differs from `k ω₁` by a root-lattice vector.** -/
theorem typeACosetRepresentative_sub_nsmul_mem_carrier (n k : ℕ) :
    typeACosetRepresentative n k - k • typeAFundamentalWeight n ∈ (typeARootLattice n).carrier := by
  have hn : (n : ℚ) + 1 ≠ 0 := by positivity
  rw [mem_typeARootLattice_carrier_iff]; intro j
  refine ⟨((min (j.val + 1) k : ℕ) : ℤ) - (k : ℤ), ?_⟩
  rw [Pi.sub_apply, Pi.smul_apply, nsmul_eq_mul, typeACosetRepresentative_apply,
    typeAFundamentalWeight_apply]
  push_cast; field_simp; ring

/-- Every `typeACosetRepresentative n k` belongs to the dual carrier of `typeARootLattice n`. -/
theorem typeACosetRepresentative_mem_dualCarrier (n k : ℕ) :
    typeACosetRepresentative n k ∈ (typeARootLattice n).dualCarrier := by
  simpa only [sub_add_cancel] using (typeARootLattice n).dualCarrier.add_mem
    ((typeARootLattice n).le_dualCarrier (typeACosetRepresentative_sub_nsmul_mem_carrier n k))
    ((typeARootLattice n).dualCarrier.nsmul_mem (typeAFundamentalWeight_mem_dualCarrier n) k)

/-- `typeACosetRepresentative n k` bundled as an element of `(typeARootLattice n).dualCarrier`. -/
noncomputable def typeACosetRepresentativeDual (n k : ℕ) : (typeARootLattice n).dualCarrier :=
  ⟨typeACosetRepresentative n k, typeACosetRepresentative_mem_dualCarrier n k⟩

@[simp] theorem coe_typeACosetRepresentativeDual (n k : ℕ) :
    (typeACosetRepresentativeDual n k : Fin n → ℚ) = typeACosetRepresentative n k := (rfl)

/-- **`typeACosetRepresentativeDual n k` represents the discriminant class `k ω₁`.** -/
@[simp] theorem mk_typeACosetRepresentativeDual (n k : ℕ) :
    (Submodule.Quotient.mk (typeACosetRepresentativeDual n k) :
        (typeARootLattice n).DiscriminantGroup) = k • typeAFundamentalWeightClass n := by
  rw [← natCast_zsmul, mk_eq_zsmul_typeAFundamentalWeightClass_iff,
    coe_typeACosetRepresentativeDual, natCast_zsmul]
  exact typeACosetRepresentative_sub_nsmul_mem_carrier n k

/-- For `a : ZMod (n + 1)`, `typeACosetRepresentativeDual n a.val` represents
`typeADiscriminantGroupEquiv n a`. -/
theorem mk_typeACosetRepresentativeDual_val (a : ZMod (n + 1)) :
    (Submodule.Quotient.mk (typeACosetRepresentativeDual n a.val) :
        (typeARootLattice n).DiscriminantGroup) = typeADiscriminantGroupEquiv n a := by
  rw [typeADiscriminantGroupEquiv_apply, mk_typeACosetRepresentativeDual]

/-- **Classical zero-sum coordinates of `typeACosetRepresentative`.**  For `k ≤ n + 1`,
`typeAIsometryZeroSumLattice` carries `typeACosetRepresentative n k` to `[r < k] - k / (n + 1)`. -/
@[simp] theorem typeAIsometryZeroSumLattice_typeACosetRepresentative_apply {k : ℕ} (hk : k ≤ n + 1)
    (r : Fin (n + 1)) :
    (typeAIsometryZeroSumLattice n (typeACosetRepresentative n k) : Fin (n + 1) → ℚ) r =
      (if (r : ℕ) < k then 1 else 0) - (k : ℚ) / (n + 1) := by
  set w : Fin (n + 1) → ℚ := fun r ↦ (if (r : ℕ) < k then 1 else 0) - (k : ℚ) / (n + 1)
  have hn : (n : ℚ) + 1 ≠ 0 := by positivity
  have hw : w ∈ singleParityCheckCode ℚ (Fin (n + 1)) := by
    rw [mem_singleParityCheckCode]
    simp only [w, sum_sub_distrib, sum_boole, Fin.card_filter_val_lt, min_eq_right hk,
      sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    field_simp; ring
  have key :
      (typeAIsometryZeroSumLattice n (typeACosetRepresentative n k) : Fin (n + 1) → ℚ) = w := by
    rw [← sum_smul_zeroSumSimpleRoot n hw]
    conv_lhs => rw [← sum_smul_typeASimpleRoot (typeACosetRepresentative n k), map_sum]
    simp only [map_smul, Submodule.coe_sum, Submodule.coe_smul,
      typeAIsometryZeroSumLattice_typeASimpleRoot]
    refine sum_congr rfl fun j _ ↦ congrArg (· • zeroSumSimpleRoot n j) ?_
    have hfilt : (Iic j.castSucc).filter (fun s : Fin (n + 1) ↦ (s : ℕ) < k) =
        univ.filter (fun s : Fin (n + 1) ↦ (s : ℕ) < min (j.val + 1) k) := by
      ext s; simp only [mem_filter, mem_Iic, mem_univ, true_and, Fin.le_iff_val_le_val,
        Fin.val_castSucc]; omega
    have hmin_le : min (j.val + 1) k ≤ n + 1 :=
      (Nat.min_le_left _ _).trans (Nat.le_succ_of_le j.isLt)
    simp only [w, sum_sub_distrib, sum_boole, hfilt, Fin.card_filter_val_lt,
      Nat.min_eq_right hmin_le, sum_const, Fin.card_Iic, Fin.val_castSucc, nsmul_eq_mul,
      typeACosetRepresentative_apply, Nat.cast_add, Nat.cast_one]
    ring
  exact congrFun key r

/-- **Pairings with the Bourbaki simple roots.**  For `k ≤ n + 1`, `typeACosetRepresentative n k`
pairs to `1` with `α_{k-1}` (when `1 ≤ k ≤ n`) and to `0` with every other simple root. -/
@[simp] theorem form_typeACosetRepresentative_typeASimpleRoot {k : ℕ} (hk : k ≤ n + 1) (i : Fin n) :
    (typeARootLattice n).form (typeACosetRepresentative n k) (typeASimpleRoot n i) =
      if i.val + 1 = k then 1 else 0 := by
  have hroot : zeroSumSimpleRoot n i = Pi.single i.castSucc 1 - Pi.single i.succ 1 := by
    ext r; simp [zeroSumSimpleRoot_apply, Pi.single_apply]
  rw [← (typeAIsometryZeroSumLattice n).map_app, zeroSumLattice_form, zeroSumForm_apply,
    typeAIsometryZeroSumLattice_typeASimpleRoot, hroot, dotProduct_sub, dotProduct_single,
    dotProduct_single, mul_one, mul_one,
    typeAIsometryZeroSumLattice_typeACosetRepresentative_apply hk,
    typeAIsometryZeroSumLattice_typeACosetRepresentative_apply hk, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> first | (exfalso; omega) | ring

/-- **Inner products of the `Aₙ` coset representatives**: `min j k - j k / (n + 1)` for
`j, k ≤ n + 1`. -/
theorem form_typeACosetRepresentative {j k : ℕ} (hj : j ≤ n + 1) (hk : k ≤ n + 1) :
    (typeARootLattice n).form (typeACosetRepresentative n j) (typeACosetRepresentative n k) =
      ((min j k : ℕ) : ℚ) - (j : ℚ) * k / (n + 1) := by
  have hn : (n : ℚ) + 1 ≠ 0 := by positivity
  rw [← (typeAIsometryZeroSumLattice n).map_app, zeroSumLattice_form, zeroSumForm_apply, dotProduct]
  have hterm (r : Fin (n + 1)) :
      (typeAIsometryZeroSumLattice n (typeACosetRepresentative n j) : Fin (n + 1) → ℚ) r *
        (typeAIsometryZeroSumLattice n (typeACosetRepresentative n k) : Fin (n + 1) → ℚ) r =
        (if (r : ℕ) < min j k then 1 else 0) -
          (if (r : ℕ) < j then 1 else 0) * ((k : ℚ) / (n + 1)) -
          (if (r : ℕ) < k then 1 else 0) * ((j : ℚ) / (n + 1)) +
          ((j : ℚ) / (n + 1)) * ((k : ℚ) / (n + 1)) := by
    rw [typeAIsometryZeroSumLattice_typeACosetRepresentative_apply hj,
      typeAIsometryZeroSumLattice_typeACosetRepresentative_apply hk]
    simp only [lt_min_iff]
    by_cases hrj : (r : ℕ) < j <;> by_cases hrk : (r : ℕ) < k <;> simp [hrj, hrk] <;> ring
  have hmin : min (n + 1) (min j k) = min j k := Nat.min_eq_right ((Nat.min_le_left j k).trans hj)
  simp only [hterm, sum_add_distrib, sum_sub_distrib, ← sum_mul, sum_boole, Fin.card_filter_val_lt,
    hmin, min_eq_right hj, min_eq_right hk, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one]
  field_simp; ring

/-- **Squared norm of `typeACosetRepresentative`**: `k (n + 1 - k) / (n + 1)` for `k ≤ n + 1`. -/
@[simp] theorem form_typeACosetRepresentative_self {k : ℕ} (hk : k ≤ n + 1) :
    (typeARootLattice n).form (typeACosetRepresentative n k) (typeACosetRepresentative n k) =
      (k : ℚ) * (n + 1 - k) / (n + 1) := by
  have hn : (n : ℚ) + 1 ≠ 0 := by positivity
  rw [form_typeACosetRepresentative hk hk, min_self]; field_simp

end TauCeti.IntegralLattice
