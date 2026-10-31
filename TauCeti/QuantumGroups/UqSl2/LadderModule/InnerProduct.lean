/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.UqSl2.LadderModule.Basic
public import TauCeti.QuantumGroups.UqSl2.Star
public import TauCeti.QuantumGroups.QuantumInteger.Order
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.Analysis.InnerProductSpace.Defs

/-!
# The invariant metric on positive ladder modules

For real `0 < q` with `q - q⁻¹ ≠ 0` (in particular, for `0 < q < 1`), the positive
ladder module has an orthogonal basis with squared lengths
`h₀ = 1` and `hⱼ / hⱼ₋₁ = [m-j+1]_q / ([j]_q q^(m-2j))`. The resulting positive definite
Hermitian form makes the action of the compact real form a star representation. The metric is
packaged as named `InnerProductSpace.Core` data, without installing a global norm on the
underlying algebraic module.

The diagonal form uses Mathlib's `Matrix.toLinearMapₛₗ₂` in the ladder basis. The compact
real-form convention is `E* = KF`, not `E* = F`.
-/

public noncomputable section

open Module ComplexConjugate

namespace TauCeti.UqSl2.LadderModule

/-- Squared length of the `j`th positive ladder vector, normalized at the highest vector. -/
def innerWeight (q : ℝ) (m j : ℕ) : ℝ :=
  ∏ t ∈ Finset.range j,
    quantumInteger q ((m : ℤ) - t) /
      (quantumInteger q ((t : ℤ) + 1) * q ^ ((m : ℤ) - 2 * (t + 1)))

/-- The highest ladder vector has squared length one. -/
@[simp]
theorem innerWeight_zero (q : ℝ) (m : ℕ) : innerWeight q m 0 = 1 := by
  simp [innerWeight]

/-- The successive-length recurrence dictated by `E* = KF`. -/
theorem innerWeight_succ (q : ℝ) (m j : ℕ) :
    innerWeight q m (j + 1) = innerWeight q m j *
      (quantumInteger q ((m : ℤ) - j) /
        (quantumInteger q ((j : ℤ) + 1) * q ^ ((m : ℤ) - 2 * (j + 1)))) := by
  unfold innerWeight
  rw [Finset.prod_range_succ]

/-- All squared lengths in the finite ladder are strictly positive. -/
theorem innerWeight_pos {q : ℝ} (hq : 0 < q) (hd : q - q⁻¹ ≠ 0) {m j : ℕ} (hj : j ≤ m) :
    0 < innerWeight q m j := by
  apply Finset.prod_pos
  intro t ht
  have ht : t < j := Finset.mem_range.mp ht
  have hnum : 0 < quantumInteger q ((m : ℤ) - t) := by
    convert quantumInteger_pos hq hd (n := m - t) (by omega) using 1
    congr 1
    omega
  have hden : 0 < quantumInteger q ((t : ℤ) + 1) := by
    exact_mod_cast quantumInteger_pos hq hd (Nat.succ_pos t)
  exact div_pos hnum (mul_pos hden (zpow_pos hq _))

/-- The Hermitian form with diagonal squared lengths `innerWeight`, conjugate-linear in its
first argument. It is positive definite for `0 < q` with `q - q⁻¹ ≠ 0`. -/
def invariantForm (q : ℝ) (m : ℕ) :
    LadderModule (q : ℂ) m 1 →ₗ⋆[ℂ] LadderModule (q : ℂ) m 1 →ₗ[ℂ] ℂ :=
  Matrix.toLinearMapₛₗ₂ (starRingEnd ℂ) (basis (q : ℂ) m 1) (basis (q : ℂ) m 1)
    (Matrix.diagonal fun i => (innerWeight q m i : ℂ))

/-- The original ladder basis is orthogonal with the specified squared lengths. -/
@[simp]
theorem invariantForm_basis (q : ℝ) (m : ℕ) (i j : Fin (m + 1)) :
    invariantForm q m (basis (q : ℂ) m 1 i) (basis (q : ℂ) m 1 j) =
      if i = j then (innerWeight q m i : ℂ) else 0 := by
  rw [invariantForm, Matrix.toLinearMapₛₗ₂_apply_basis, Matrix.diagonal_apply]

/-- The diagonal-coordinate formula for the invariant metric. -/
theorem invariantForm_apply (q : ℝ) (m : ℕ) (v w : LadderModule (q : ℂ) m 1) :
    invariantForm q m v w = ∑ i, conj ((basis (q : ℂ) m 1).repr v i) *
      (basis (q : ℂ) m 1).repr w i * (innerWeight q m i : ℂ) := by
  simp [invariantForm, Matrix.toLinearMapₛₗ₂_apply, Matrix.diagonal_apply, smul_eq_mul,
    mul_assoc]

/-- Hermitian symmetry of the invariant metric. -/
@[simp]
theorem invariantForm_symm (q : ℝ) (m : ℕ) (v w : LadderModule (q : ℂ) m 1) :
    star (invariantForm q m v w) = invariantForm q m w v := by
  simp only [invariantForm_apply, map_sum, Complex.star_def, map_mul,
    RingHomCompTriple.comp_apply, RingHom.id_apply, Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The real part of the squared length is a weighted sum of squared moduli.
The weights are positive when `0 < q` and `q - q⁻¹ ≠ 0`. -/
theorem re_invariantForm_self (q : ℝ) (m : ℕ) (v : LadderModule (q : ℂ) m 1) :
    (invariantForm q m v v).re =
      ∑ i, Complex.normSq ((basis (q : ℂ) m 1).repr v i) * innerWeight q m i := by
  simp [invariantForm_apply, Complex.mul_re, Complex.normSq_apply]

/-- The metric is strictly positive on every nonzero vector. -/
theorem invariantForm_pos {q : ℝ} (hq : 0 < q) (hd : q - q⁻¹ ≠ 0) {m : ℕ}
    {v : LadderModule (q : ℂ) m 1} (hv : v ≠ 0) : 0 < (invariantForm q m v v).re := by
  rw [re_invariantForm_self]
  have hex : ∃ i, (basis (q : ℂ) m 1).repr v i ≠ 0 := by
    by_contra! h
    apply hv
    exact (basis (q : ℂ) m 1).repr.injective (by ext i; simp [h])
  obtain ⟨i, hi⟩ := hex
  exact Finset.sum_pos' (fun j _ => mul_nonneg (Complex.normSq_nonneg _)
    (innerWeight_pos hq hd (by omega)).le)
    ⟨i, Finset.mem_univ _, mul_pos (Complex.normSq_pos.mpr hi)
      (innerWeight_pos hq hd (by omega))⟩

/-- The normalized invariant inner product as named core data. No global norm is installed. -/
@[instance_reducible]
def innerProductCore {q : ℝ} (hq : 0 < q) (hd : q - q⁻¹ ≠ 0) (m : ℕ) :
    InnerProductSpace.Core ℂ (LadderModule (q : ℂ) m 1) where
  inner v w := invariantForm q m v w
  conj_inner_symm x y := invariantForm_symm q m y x
  re_inner_nonneg x := by
    by_cases hx : x = 0
    · simp [hx]
    · exact (invariantForm_pos hq hd hx).le
  add_left x y z := by simp
  smul_left x y r := by simp
  definite x hx := by
    by_contra h
    have := invariantForm_pos hq hd h
    simp [hx] at this

/-- The named inner product is the explicit diagonal form. -/
@[simp]
theorem innerProductCore_inner {q : ℝ} (hq : 0 < q) (hd : q - q⁻¹ ≠ 0) (m : ℕ)
    (v w : LadderModule (q : ℂ) m 1) :
    @inner ℂ _ (innerProductCore hq hd m).toInner v w = invariantForm q m v w := (rfl)

/-- Pairing an integer-indexed ladder vector with a basis vector, including out-of-range
indices. -/
@[simp]
theorem invariantForm_vec_basis (q : ℝ) (m : ℕ) (j : ℤ) (i : Fin (m + 1)) :
    invariantForm q m (vec (q : ℂ) m 1 j) (basis (q : ℂ) m 1 i) =
      if (i : ℤ) = j then (innerWeight q m i : ℂ) else 0 := by
  simp [invariantForm_apply, basis_repr_vec, Finsupp.single_apply, mul_ite]

/-- The parallel pairing with the integer-indexed vector in the second argument. -/
@[simp]
theorem invariantForm_basis_vec (q : ℝ) (m : ℕ) (i : Fin (m + 1)) (j : ℤ) :
    invariantForm q m (basis (q : ℂ) m 1 i) (vec (q : ℂ) m 1 j) =
      if (i : ℤ) = j then (innerWeight q m i : ℂ) else 0 := by
  rw [← invariantForm_symm, invariantForm_vec_basis]
  split_ifs <;> simp

section Invariance

variable {q : ℝ} [Fact ((q : ℂ) ≠ 0)] {m : ℕ}

private theorem invariant_of_basis {a b : UqSl2 (q : ℂ)}
    (h : ∀ i j : Fin (m + 1),
      invariantForm q m (a • basis (q : ℂ) m 1 i) (basis (q : ℂ) m 1 j) =
        invariantForm q m (basis (q : ℂ) m 1 i) (b • basis (q : ℂ) m 1 j))
    (v w : LadderModule (q : ℂ) m 1) :
    invariantForm q m (a • v) w = invariantForm q m v (b • w) := by
  have hh : (invariantForm q m).comp (rep (q : ℂ) m 1 a) =
      (invariantForm q m).compl₂ (rep (q : ℂ) m 1 b) :=
    LinearMap.ext_basis (basis (q : ℂ) m 1) (basis (q : ℂ) m 1) h
  exact LinearMap.congr_fun₂ hh v w

private theorem invariant_k (v w : LadderModule (q : ℂ) m 1) :
    invariantForm q m (k (q : ℂ) • v) w =
      invariantForm q m v (k (q : ℂ) • w) := by
  apply invariant_of_basis
  intro i j
  simp only [k_smul_basis, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    invariantForm_basis]
  split_ifs with h
  · subst j
    simp
  · simp

private theorem invariant_kInv (v w : LadderModule (q : ℂ) m 1) :
    invariantForm q m (kInv (q : ℂ) • v) w =
      invariantForm q m v (kInv (q : ℂ) • w) := by
  apply invariant_of_basis
  intro i j
  simp only [kInv_smul_basis, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    invariantForm_basis]
  split_ifs with h
  · subst j
    simp
  · simp

private theorem invariant_e {q : ℝ} (hq : 0 < q) (hd : q - q⁻¹ ≠ 0)
    [Fact ((q : ℂ) ≠ 0)] (v w : LadderModule (q : ℂ) m 1) :
    invariantForm q m (e (q : ℂ) • v) w =
      invariantForm q m v ((k (q : ℂ) * f (q : ℂ)) • w) := by
  apply invariant_of_basis
  intro i j
  rw [e_smul_basis, mul_smul (k (q : ℂ)) (f (q : ℂ)), f_smul_basis,
    smul_comm (k (q : ℂ)), k_smul_vec]
  simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    invariantForm_vec_basis, invariantForm_basis_vec]
  by_cases hij : (i : ℤ) = (j : ℤ) + 1
  · have hi : (i : ℕ) = (j : ℕ) + 1 := by omega
    have hjden := (quantumInteger_pos hq hd (Nat.succ_pos (j : ℕ))).ne'
    have hpow := (zpow_pos hq ((m : ℤ) - 2 * (j + 1))).ne'
    have hden : quantumInteger q ((j : ℤ) + 1) ≠ 0 := by exact_mod_cast hjden
    have hb : quantumInteger q ((m : ℤ) - j) * innerWeight q m j =
        quantumInteger q ((j : ℤ) + 1) * q ^ ((m : ℤ) - 2 * (j + 1)) *
          innerWeight q m (j + 1) := by
      rw [innerWeight_succ]
      field_simp
    simp only [ite_eq_left (by omega : (j : ℤ) = (i : ℤ) - 1), ite_eq_left hij]
    have hc (r : ℤ) : quantumInteger (q : ℂ) r = ((quantumInteger q r : ℝ) : ℂ) := by
      simp [quantumInteger_def]
    simp only [Units.val_one, Int.cast_one, one_mul]
    rw [hc, hc]
    simp only [Complex.conj_ofReal, RingHom.id_apply]
    rw [hi]
    have hexp : (m : ℤ) - ((j : ℕ) + 1) + 1 = (m : ℤ) - j := by omega
    simp only [Nat.cast_add, Nat.cast_one, hexp]
    exact_mod_cast (hb.trans (mul_assoc _ _ _))
  · have hji : (j : ℤ) ≠ (i : ℤ) - 1 := by omega
    simp [hij, hji]

/-- The whole algebra acts by adjoints for the compact real form, not just its generators. -/
theorem invariantForm_smul {q : ℝ} (hq : 0 < q) (hd : q - q⁻¹ ≠ 0)
    (a : UqSl2 (q : ℂ)) (v w : LadderModule (q : ℂ) m 1) :
    letI : Fact ((q : ℂ) ≠ 0) := ⟨by exact_mod_cast hq.ne'⟩
    letI : Fact (IsSelfAdjoint (q : ℂ)) := ⟨by simp [IsSelfAdjoint]⟩
    invariantForm q m (a • v) w = invariantForm q m v (star a • w) := by
  let : Fact ((q : ℂ) ≠ 0) := ⟨by exact_mod_cast hq.ne'⟩
  let : Fact (IsSelfAdjoint (q : ℂ)) := ⟨by simp [IsSelfAdjoint]⟩
  induction a using UqSl2.induction generalizing v w with
  | algebraMap c =>
    rw [← algebraMap_star_comm]
    simp
  | add a b ha hb => simp [add_smul, ha, hb]
  | mul a b ha hb => simp [mul_smul, ha, hb]
  | generator g =>
    cases g with
    | k => simpa using invariant_k v w
    | kInv => simpa using invariant_kInv v w
    | e => simpa using invariant_e hq hd v w
    | f =>
      have he := invariant_e hq hd ((kInv (q : ℂ)) • w) v
      have he' := congrArg star he
      simp only [invariantForm_symm] at he'
      simpa [← invariant_kInv, ← mul_smul] using he'.symm

/-- The weight generator is strictly positive in the invariant metric on the positive family. -/
theorem invariantForm_k_pos {q : ℝ} (hq : 0 < q) (hd : q - q⁻¹ ≠ 0)
    {v : LadderModule (q : ℂ) m 1} (hv : v ≠ 0) :
    letI : Fact ((q : ℂ) ≠ 0) := ⟨by exact_mod_cast hq.ne'⟩
    0 < (invariantForm q m v (k (q : ℂ) • v)).re := by
  let : Fact ((q : ℂ) ≠ 0) := ⟨by exact_mod_cast hq.ne'⟩
  have hc (i : Fin (m + 1)) :
      (basis (q : ℂ) m 1).repr (k (q : ℂ) • v) i =
        (q : ℂ) ^ ((m : ℤ) - 2 * i) * (basis (q : ℂ) m 1).repr v i := by
    rw [smul_def, ← LinearMap.toMatrix_mulVec_repr (basis (q : ℂ) m 1)
      (basis (q : ℂ) m 1)]
    simp [Matrix.mulVec, dotProduct, LinearMap.toMatrix_apply, ← smul_def,
      k_smul_basis, Finsupp.single_apply]
  have hex : ∃ i, (basis (q : ℂ) m 1).repr v i ≠ 0 := by
    by_contra! h
    exact hv ((basis (q : ℂ) m 1).repr.injective (by ext i; simp [h]))
  have hsum : (invariantForm q m v (k (q : ℂ) • v)).re =
      ∑ i, Complex.normSq ((basis (q : ℂ) m 1).repr v i) *
        (q ^ ((m : ℤ) - 2 * i) * innerWeight q m i) := by
    simp only [invariantForm_apply, hc]
    simp only [← Complex.ofReal_zpow, Complex.re_sum, Complex.mul_re, Complex.conj_re,
      Complex.conj_im, Complex.mul_im, neg_mul, sub_neg_eq_add, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero, Complex.normSq_apply]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum]
  obtain ⟨i, hi⟩ := hex
  exact Finset.sum_pos' (fun j _ => mul_nonneg (Complex.normSq_nonneg _)
    (mul_pos (zpow_pos hq _) (innerWeight_pos hq hd (by omega))).le)
    ⟨i, Finset.mem_univ _, mul_pos (Complex.normSq_pos.mpr hi)
      (mul_pos (zpow_pos hq _) (innerWeight_pos hq hd (by omega)))⟩

end Invariance

end TauCeti.UqSl2.LadderModule
