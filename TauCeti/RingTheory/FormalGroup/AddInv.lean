/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou, The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FormalGroup.Basic

/-!
# Inverses for native formal group laws

For a one-dimensional formal group law `F` over a commutative ring, `addInvX F` is the
unique series `i(X)` with zero constant term and `F(i(X), X) = 0`. Its linear coefficient
is `-1`. Substitution gives inverses on Mathlib's native `F.Point σ` carrier, including
points whose constant coefficients are nilpotent. Thus these points form an additive
group, and an additive commutative group when `F` is commutative.

The two inverse identities, uniqueness and involution are stated on the native series
carriers; they provide the inverse coordinate used in formal-group calculations.

## References

* M. Hazewinkel, *Formal Groups and Applications*, Chapter I, §1.

## Attribution

The coefficient recursion and its finite-stage cancellation proof are adapted from
Wenrong Zou's Mathlib PR [#36167](https://github.com/leanprover-community/mathlib4/pull/36167),
`Mathlib/RingTheory/FormalGroup/AddInv.lean`. The point construction here uses the native
power-series points of the pinned Mathlib rather than the proposed topological carrier.
-/

public section

namespace TauCeti

open PowerSeries Finset Finsupp

variable {R : Type*} [CommRing R] (F : FormalGroup R)

private noncomputable def addInvAux : ℕ → R
  | 0 => 0
  | 1 => -1
  | n + 2 => -coeff (n + 2) (F.toPowerSeries.subst
      ![∑ i : Fin (n + 2), C (addInvAux i.1) * X ^ i.1, X])

private theorem addInvAux_succ (k : ℕ) : addInvAux F (k + 1) = -coeff (k + 1)
    (F.toPowerSeries.subst ![∑ i ∈ range (k + 1), C (addInvAux F i) * X ^ i, X]) := by
  obtain _ | k := k
  · simp [addInvAux, FormalGroup.zeroX_eq_X]
  · rw [addInvAux, Fin.sum_univ_eq_sum_range (fun i ↦ C (addInvAux F i) * X ^ i)]

/-- The inverse coordinate of the formal group `F`, characterized by
`F(addInvX F, X) = 0` and zero constant term. -/
noncomputable def addInvX : PowerSeries R := .mk (addInvAux F)

/-- The inverse coordinate has zero constant term. -/
@[simp]
theorem constantCoeff_addInvX : constantCoeff (addInvX F) = 0 := by
  rw [← coeff_zero_eq_constantCoeff]
  simp [addInvX, addInvAux]

/-- The inverse coordinate has linear coefficient `-1`. -/
@[simp]
theorem coeff_one_addInvX : coeff 1 (addInvX F) = -1 := by
  simp [addInvX, addInvAux]

/-- Each coefficient of the inverse coordinate cancels the error left by the preceding
coefficients, so its construction requires no division in the coefficient ring. -/
theorem coeff_succ_addInvX (n : ℕ) :
    coeff (n + 1) (addInvX F) = -coeff (n + 1) (F.toPowerSeries.subst
      ![∑ i ∈ range (n + 1), C (coeff i (addInvX F)) * X ^ i, X]) := by
  simpa only [addInvX, coeff_mk] using addInvAux_succ F n

private theorem hasSubst_addInv_pair :
    MvPowerSeries.HasSubst ![addInvX F, X] :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun i ↦ by
    fin_cases i <;> simp [← constantCoeff_eq]

private theorem hasSubst_addInv_sum (n : ℕ) :
    MvPowerSeries.HasSubst ![∑ i ∈ range (n + 1), C (addInvAux F i) * X ^ i, X] :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun i ↦ by
    fin_cases i <;> simp [← constantCoeff_eq, zero_pow_eq, addInvAux]

private theorem coeff_subst_addInv_sum (n : ℕ) :
    coeff n (F.toPowerSeries.subst
      ![∑ i ∈ range (n + 1), C (addInvAux F i) * X ^ i, X]) = 0 := by
  obtain _ | k := n
  · simp [addInvAux, FormalGroup.zeroX_eq_X]
  · rw [sum_range_succ]
    generalize hB : (∑ i ∈ range (k + 1), C (addInvAux F i) * X ^ i) = B
    have coeff_B : constantCoeff B = 0 := by simp [← hB, zero_pow_eq, addInvAux]
    have ha := hasSubst_addInv_sum F (k + 1)
    rw [sum_range_succ, hB] at ha
    rw [coeff, MvPowerSeries.coeff_subst ha]
    simp only [Finsupp.prod_pow, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, smul_eq_mul]
    -- Adding the coefficient in degree k + 1 affects only the linear X term of F.
    have eq_aux (d : Fin 2 →₀ ℕ) : coeff (k + 1)
        ((B + C (addInvAux F (k + 1)) * X ^ (k + 1)) ^ d 0 * X ^ d 1) =
          coeff (k + 1) (B ^ d 0 * X ^ d 1) +
            if d = single 0 1 then addInvAux F (k + 1) else 0 := by
      rw [coeff_mul_X_pow', coeff_mul_X_pow']
      by_cases hd : d = single 0 1
      · simp [hd]
      rw [ite_eq_right hd, add_zero]
      by_cases hd_le : d 1 ≤ k + 1
      · simp_rw [ite_eq_left hd_le, add_pow, map_sum]
        rw [Finset.sum_eq_single (d 0) _ (by simp)]
        · simp
        · intro i hi_mem hi
          rw [mul_pow, mul_assoc, mul_assoc, mul_comm ((X ^ (k + 1)) ^ (d 0 - i)),
            ← mul_assoc, ← mul_assoc, ← pow_mul, coeff_mul_X_pow']
          by_cases hd₀ : d 1 = 0 ∧ d 0 - i = 1
          · have i_ne_zero : i ≠ 0 := by
              intro hi
              subst i
              apply hd
              ext j
              fin_cases j <;> simp_all
            simp [hd₀, coeff_B, zero_pow i_ne_zero]
          have : k + 1 ≤ (k + 1) * (d 0 - i) :=
            Nat.le_mul_of_pos_right _ (by grind)
          rw [ite_eq_right _]
          by_cases hd₀' : d 1 = 0
          · have : (k + 1) * 2 ≤ (k + 1) * (d 0 - i) :=
              Nat.mul_le_mul_left _ (by grind)
            omega
          omega
      · simp_rw [ite_eq_right hd_le]
    -- The remaining contribution is the linear coefficient 1 times the new coefficient.
    -- The recursion cancels it against the error of the preceding partial sum.
    simp only [coeff_coeToMvPowerSeries]
    simp_rw [eq_aux, mul_add]
    rw [finsum_add_distrib]
    · nth_rw 2 [finsum_eq_single _ (single 0 1) fun d hd ↦ by rw [ite_eq_right hd, mul_zero]]
      rw [ite_eq_left rfl, F.lin_coeff_X, one_mul, addInvAux_succ]
      rw [← hB]
      rw [coeff, MvPowerSeries.coeff_subst (hasSubst_addInv_sum F k)]
      simp [Finsupp.prod_pow, Fin.prod_univ_two]
    · simpa only [Finsupp.prod_pow, Fin.prod_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, smul_eq_mul, hB,
        coeff_coeToMvPowerSeries] using
        MvPowerSeries.coeff_subst_finite (hasSubst_addInv_sum F k) F.toPowerSeries
          (single () (k + 1))
    · exact (Set.finite_singleton (single 0 1)).subset
        (Function.support_subset_iff'.mpr fun d hd ↦ by
          simp only [Set.mem_singleton_iff] at hd
          simp [hd])

/-- The inverse coordinate is a left inverse: `F(i(X), X) = 0`. -/
theorem subst_addInvX_X : F.toPowerSeries.subst ![addInvX F, X] = 0 := by
  ext n
  rw [map_zero, ← coeff_subst_addInv_sum F n, coeff,
    MvPowerSeries.coeff_subst (hasSubst_addInv_pair F),
    MvPowerSeries.coeff_subst (hasSubst_addInv_sum F n)]
  refine finsum_congr fun d ↦ ?_
  congr 1
  simp only [Finsupp.prod_pow, Fin.prod_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  generalize hB : (∑ i ∈ range (n + 1), C (addInvAux F i) * X ^ i) = B
  -- Agreement through degree n is preserved by powers and multiplication; the higher
  -- coefficients therefore do not change the finite-stage cancellation.
  have hdiv : X ^ (n + 1) ∣ addInvX F - B := by
    rw [X_pow_dvd_iff]
    intro m hm
    simp [← hB, addInvX, coeff_X_pow, hm]
  obtain ⟨Q, hQ⟩ := (hdiv.trans (sub_dvd_pow_sub_pow _ _ (d 0))).mul_right (X ^ d 1)
  have heq : addInvX F ^ d 0 * X ^ d 1 = B ^ d 0 * X ^ d 1 + X ^ (n + 1) * Q := by
    rw [sub_mul] at hQ
    exact (sub_eq_iff_eq_add.mp hQ).trans (add_comm _ _)
  rw [heq]
  simp only [coeff_coeToMvPowerSeries, map_add, coeff_X_pow_mul',
    show ¬n + 1 ≤ n by omega, ite_false, add_zero]

variable {σ : Type*}

/-- Substituting any native point into the inverse coordinate gives its left inverse. -/
@[simp]
theorem subst_addInvX_self {f : MvPowerSeries σ R} (hf : PowerSeries.HasSubst f) :
    F.toPowerSeries.subst ![PowerSeries.subst f (addInvX F), f] = 0 := by
  calc
    _ = PowerSeries.subst f (F.toPowerSeries.subst ![addInvX F, X]) := by
      rw [PowerSeries.subst_def _ (F.toPowerSeries.subst _),
        MvPowerSeries.subst_comp_subst_apply
        (hasSubst_addInv_pair F) hf.const]
      congr 1
      funext i
      fin_cases i <;> simp [← PowerSeries.subst_def, PowerSeries.subst_X hf]
    _ = 0 := by rw [subst_addInvX_X, ← PowerSeries.coe_substAlgHom hf, map_zero]

/-- Negation on native formal-group points is substitution into the inverse coordinate. -/
noncomputable instance instNegPoint : Neg (F.Point σ) where
  neg x := ⟨PowerSeries.subst x.val (addInvX F),
    MvPowerSeries.IsNilpotent_subst x.property.const
      (by simpa only [← constantCoeff_eq, constantCoeff_addInvX] using
        (IsNilpotent.zero : IsNilpotent (0 : R)))⟩

/-- The underlying series of the negative of a point. -/
@[simp]
theorem neg_point_val (x : F.Point σ) :
    (-x).val = PowerSeries.subst x.val (addInvX F) := (rfl)

/-- Native points of a formal group form an additive group. -/
noncomputable instance instAddGroupPoint : AddGroup (F.Point σ) where
  zsmul := zsmulRec
  neg_add_cancel x := Subtype.ext <| by
    rw [FormalGroup.add_apply, neg_point_val, FormalGroup.zero_apply]
    exact subst_addInvX_self F x.property

/-- Native points of a commutative formal group form an additive commutative group. -/
noncomputable instance instAddCommGroupPoint [F.IsComm] : AddCommGroup (F.Point σ) where
  add_comm := add_comm

/-- A left inverse of a native point is obtained by substituting it into `addInvX`. -/
theorem eq_subst_addInvX_iff {f g : MvPowerSeries σ R}
    (hf : PowerSeries.HasSubst f) (hg : PowerSeries.HasSubst g) :
    g = PowerSeries.subst f (addInvX F) ↔ F.toPowerSeries.subst ![g, f] = 0 := by
  let x : F.Point σ := ⟨f, hf⟩
  let y : F.Point σ := ⟨g, hg⟩
  constructor
  · rintro rfl
    exact subst_addInvX_self F hf
  · intro h
    have h' : y + x = 0 := Subtype.ext h
    have heq : y = -x := eq_neg_of_add_eq_zero_left h'
    exact congrArg (fun z : F.Point σ ↦ z.val) heq

/-- The inverse coordinate gives right inverses too, without assuming commutativity of `F`. -/
@[simp]
theorem subst_self_addInvX {f : MvPowerSeries σ R} (hf : PowerSeries.HasSubst f) :
    F.toPowerSeries.subst ![f, PowerSeries.subst f (addInvX F)] = 0 := by
  let x : F.Point σ := ⟨f, hf⟩
  have h := congrArg (fun z : F.Point σ ↦ z.val) (add_neg_cancel x)
  rw [FormalGroup.add_apply, neg_point_val, FormalGroup.zero_apply] at h
  exact h

/-- Inverting twice returns the original coordinate. -/
@[simp]
theorem subst_addInvX_addInvX : PowerSeries.subst (addInvX F) (addInvX F) = X := by
  let x : F.Point Unit := ⟨X, PowerSeries.HasSubst.X'⟩
  have h := congrArg (fun z : F.Point Unit ↦ z.val) (neg_neg x)
  rw [neg_point_val, neg_point_val] at h
  simpa only [x, PowerSeries.X_subst] using h

/-- The zero-constant inverse coordinate is uniquely characterized by its left inverse law. -/
theorem eq_addInvX_iff {g : PowerSeries R} (hg : constantCoeff g = 0) :
    g = addInvX F ↔ F.toPowerSeries.subst ![g, X] = 0 := by
  simpa only [PowerSeries.X_subst] using eq_subst_addInvX_iff F
    PowerSeries.HasSubst.X' (PowerSeries.HasSubst.of_constantCoeff_zero' hg)

end TauCeti
