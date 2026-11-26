/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Unbundled.RingSeminorm
public import TauCeti.Analysis.Normed.Field.Factorial
public import TauCeti.RingTheory.DividedPowers.Associative
public import TauCeti.Topology.Order.SequenceMinimum

/-!
# Ultrametric bounds for nearly primitive elements

Divided powers of an element with bounded powers tend to zero after scaling strictly
inside the factorial radius. A dominant diagonal term then bounds a nearly primitive
element in a pair of algebras. The norms are supplied as ring seminorms, so
no topology or normed algebra instance on the algebras is required.

## References

The argument is due to L. Alpöge, from his formal Lean proof of the Riemann hypothesis
for Dirichlet L-functions (2026), https://github.com/leanprover-community/riemann-hypothesis;
the formalization here is independent of that source.
-/

public section

open Filter Topology Finset

namespace TauCeti

open Associative

section Estimates

variable {C A : Type*} [NormedField C] [CharZero C] [Ring A] [Algebra C A]
  [Algebra ℚ A] [IsScalarTower ℚ C A]

private theorem seminorm_dividedPower_smul_le [IsUltrametricDist C]
    (N : RingSeminorm A) (hN : ∀ (c : C) x, N (c • x) = ‖c‖ * N x)
    {p : ℕ} (hp : p.Prime) (hpC : ‖(p : C)‖ < 1) (c : C) (y : A)
    {K : ℝ} (hK : ∀ n : ℕ, N (y ^ n) ≤ K) (n : ℕ) :
    N (dividedPower n (c • y)) ≤
      K * (‖c‖ * ‖(p : C)‖ ^ (-((p : ℝ) - 1)⁻¹)) ^ n := by
  rw [dividedPower_def, ← IsScalarTower.algebraMap_smul C, map_inv₀, map_natCast,
    smul_pow, hN, hN, norm_pow]
  calc
    _ ≤ (‖(p : C)‖ ^ (-((p : ℝ) - 1)⁻¹)) ^ n * (‖c‖ ^ n * K) :=
      mul_le_mul (norm_inv_factorial_le_norm_natCast_rpow_pow hp hpC n)
        (mul_le_mul_of_nonneg_left (hK n) (by positivity)) (by positivity) (by positivity)
    _ = _ := by rw [mul_pow]; ring

private theorem tendsto_seminorm_dividedPower_smul [IsUltrametricDist C]
    (N : RingSeminorm A) (hN : ∀ (c : C) x, N (c • x) = ‖c‖ * N x)
    {p : ℕ} (hp : p.Prime) (hpC : ‖(p : C)‖ < 1) (c : C) (y : A)
    (hc : ‖c‖ * ‖(p : C)‖ ^ (-((p : ℝ) - 1)⁻¹) < 1)
    (hy : ∃ K : ℝ, ∀ n : ℕ, N (y ^ n) ≤ K) :
    Tendsto (fun n ↦ N (dividedPower n (c • y))) atTop (𝓝 0) := by
  obtain ⟨K, hK⟩ := hy
  apply squeeze_zero (fun n ↦ apply_nonneg N _) (seminorm_dividedPower_smul_le N hN hp hpC c y hK)
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hc).const_mul K

end Estimates

section Diagonal

variable {C A B : Type*} [NormedField C] [CharZero C]
  [Ring A] [CommRing B] [Algebra C A] [Algebra C B]
  [Algebra ℚ A] [IsScalarTower ℚ C A]
  [Algebra ℚ B] [IsScalarTower ℚ C B]

omit [CharZero C] [IsScalarTower ℚ C A] [Algebra ℚ B] [IsScalarTower ℚ C B] in
private theorem diagonal_sum_le (N : RingSeminorm A) (M : RingSeminorm B)
    (hM : IsNonarchimedean M) (L R : A →ₐ[C] B)
    (hLR : ∀ x y, M (L x * R y) = N x * N y) (z : A) {v : ℝ}
    (hv : 0 ≤ v) (hmax : ∀ n, N (dividedPower n z) ≤ v) (j : ℕ) :
    M (∑ ab ∈ antidiagonal j,
      L (dividedPower ab.1 z) * R (dividedPower ab.2 z)) ≤ v * v := by
  have hne : (antidiagonal j).Nonempty := ⟨(0, j), by simp⟩
  obtain ⟨ab, _, hbound⟩ := hM.finset_image_add_of_nonempty
    (fun ab ↦ L (dividedPower ab.1 z) * R (dividedPower ab.2 z)) hne
  refine hbound.trans ?_
  rw [hLR]
  exact mul_le_mul (hmax _) (hmax _) (apply_nonneg N _) hv

omit [CharZero C] [IsScalarTower ℚ C A] [Algebra ℚ B] [IsScalarTower ℚ C B] in
private theorem diagonal_sum_eq (N : RingSeminorm A) (M : RingSeminorm B)
    (hM : IsNonarchimedean M) (L R : A →ₐ[C] B)
    (hLR : ∀ x y, M (L x * R y) = N x * N y) (z : A) {k : ℕ}
    (hk : 0 < N (dividedPower k z)) (hmax : ∀ n, N (dividedPower n z) ≤ N (dividedPower k z))
    (hlast : ∀ n, k < n → N (dividedPower n z) < N (dividedPower k z)) :
    M (∑ ab ∈ antidiagonal (2 * k),
      L (dividedPower ab.1 z) * R (dividedPower ab.2 z)) =
      N (dividedPower k z) * N (dividedPower k z) := by
  rw [hM.apply_sum_eq_of_lt (g := fun ab : ℕ × ℕ ↦
    L (dividedPower ab.1 z) * R (dividedPower ab.2 z)) (fun x ↦ map_neg_eq_map M x)
    (k := (k, k)) (by simp [two_mul]) ?_, hLR]
  intro ab hab hne
  rw [hLR, hLR]
  have hab' := mem_antidiagonal.mp hab
  have hlt : k < ab.1 ∨ k < ab.2 := by
    by_contra! h
    have : ab = (k, k) := Prod.ext (by omega) (by omega)
    exact hne this
  rcases hlt with h | h
  · exact mul_lt_mul_of_lt_of_le_of_nonneg_of_pos
      (hlast _ h) (hmax _) (apply_nonneg N _) hk
  · exact mul_lt_mul_of_le_of_lt_of_nonneg_of_pos
      (hmax _) (hlast _ h) (apply_nonneg N _) hk

private theorem perturbed_sum_eq (M : RingSeminorm B) (hM : IsNonarchimedean M)
    (w : ℕ → B) (e : B) (he : ∀ l : ℕ, l ≠ 0 → M (dividedPower l e) < 1)
    {v : ℝ} (hv : 0 < v) (hw : ∀ j, M (w j) ≤ v) {n : ℕ} (hwn : M (w n) = v) :
    M (∑ jl ∈ antidiagonal n, w jl.1 * dividedPower jl.2 e) = v := by
  have hn : (n, 0) ∈ antidiagonal n := by simp
  have hsum := hM.apply_sum_eq_of_lt (g := fun jl : ℕ × ℕ ↦ w jl.1 * dividedPower jl.2 e)
    (fun x ↦ map_neg_eq_map M x) hn (fun jl hjl hne ↦ ?_)
  · simpa only [dividedPower_zero, mul_one, hwn] using hsum
  · have hl : jl.2 ≠ 0 := by
      intro h
      have hj := mem_antidiagonal.mp hjl
      exact hne (Prod.ext (by omega) h)
    simp only [dividedPower_zero, mul_one, hwn]
    calc
      M (w jl.1 * dividedPower jl.2 e) ≤ M (w jl.1) * M (dividedPower jl.2 e) :=
        map_mul_le_mul M _ _
      _ ≤ v * M (dividedPower jl.2 e) :=
        mul_le_mul_of_nonneg_right (hw _) (apply_nonneg M _)
      _ < v := by simpa using mul_lt_mul_of_pos_left (he _ hl) hv

private theorem seminorm_le_one_of_dividedPower (N : RingSeminorm A) (M : RingSeminorm B)
    (hN1 : N 1 ≤ 1) (hM : IsNonarchimedean M) (D L R : A →ₐ[C] B)
    (hD : ∀ x, M (D x) ≤ N x) (hLR : ∀ x y, M (L x * R y) = N x * N y)
    (z : A) (e : B) (hz : D z = L z + R z + e)
    (he : ∀ l : ℕ, l ≠ 0 → M (dividedPower l e) < 1)
    (ht : Tendsto (fun n ↦ N (dividedPower n z)) atTop (𝓝 0)) : N z ≤ 1 := by
  by_contra! h
  obtain ⟨k, hk, hk1, hmax, hlast⟩ := ht.exists_last_max_of_tendsto_zero
    (by simpa using hN1) (by simpa using h)
  let w : ℕ → B := fun j ↦ ∑ ab ∈ antidiagonal j,
    L (dividedPower ab.1 z) * R (dividedPower ab.2 z)
  have hv : 0 < N (dividedPower k z) := zero_lt_one.trans hk1
  have hw (j : ℕ) : M (w j) ≤ N (dividedPower k z) * N (dividedPower k z) :=
    diagonal_sum_le N M hM L R hLR z hv.le hmax j
  have hwn := diagonal_sum_eq N M hM L R hLR z hv hmax hlast
  have heq := perturbed_sum_eq M hM w e he (mul_pos hv hv) hw hwn
  have hexp := AlgHom.dividedPower_eq_sum (D.restrictScalars ℚ)
    (L.restrictScalars ℚ) (R.restrictScalars ℚ) z e hz (2 * k)
  simp only [AlgHom.restrictScalars_apply] at hexp
  rw [← hexp] at heq
  have hlt := hlast (2 * k) (by omega)
  have hbig : N (dividedPower k z) < N (dividedPower k z) * N (dividedPower k z) := by
    simpa using mul_lt_mul_of_pos_left hk1 hv
  have := hD (dividedPower (2 * k) z)
  linarith

end Diagonal

section Main

variable {C A B : Type*} [NormedField C] [CharZero C] [IsUltrametricDist C]
  [Ring A] [CommRing B] [Algebra C A] [Algebra C B]

/-- A nearly primitive element with bounded powers has seminorm at most one after scaling
strictly inside the factorial radius. The two algebra maps have multiplicative cross norm and the
diagonal map is contractive. Only the target seminorm must be ultrametric. -/
theorem _root_.RingSeminorm.smul_le_one_of_bounded_powers_of_lt
    (N : RingSeminorm A) (M : RingSeminorm B) (hM : IsNonarchimedean M)
    (hNsmul : ∀ (c : C) x, N (c • x) = ‖c‖ * N x)
    (D L R : A →ₐ[C] B) (hD : ∀ x, M (D x) ≤ N x)
    (hLR : ∀ x y, M (L x * R y) = N x * N y)
    (p : ℕ) (hp : p.Prime) (hpC : ‖(p : C)‖ < 1)
    (y : A) (hy : ∃ K : ℝ, ∀ n : ℕ, N (y ^ n) ≤ K)
    (he : M (D y - L y - R y) ≤ 1) (c : C)
    (hc : ‖c‖ < ‖(p : C)‖ ^ (((p : ℝ) - 1)⁻¹)) : N (c • y) ≤ 1 := by
  let : Algebra ℚ A := Algebra.compHom A (algebraMap ℚ C)
  let : Algebra ℚ B := Algebra.compHom B (algebraMap ℚ C)
  have : IsScalarTower ℚ C A := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower ℚ C B := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hp0 : 0 < ‖(p : C)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hq : ‖c‖ * ‖(p : C)‖ ^ (-((p : ℝ) - 1)⁻¹) < 1 := by
    rw [Real.rpow_neg (norm_nonneg _),
      mul_inv_lt_iff₀ (Real.rpow_pos_of_pos hp0 _), one_mul]
    exact hc
  obtain ⟨hN1, hM1⟩ := N.apply_one_le_one_of_pair M D L R hD hLR
  have hMsmul := N.smul_eq_of_pair M hNsmul L R hLR hN1
  let e₀ := D y - L y - R y
  have hepow (n : ℕ) : M (e₀ ^ n) ≤ 1 :=
    (map_pow_le_pow' hM1 e₀ n).trans (pow_le_one₀ (apply_nonneg M _) he)
  apply seminorm_le_one_of_dividedPower N M hN1 hM D L R hD hLR (c • y) (c • e₀)
  · simp only [map_smul, smul_sub, e₀]
    abel
  · intro l hl
    have h := seminorm_dividedPower_smul_le M hMsmul hp hpC c e₀ hepow l
    rw [one_mul] at h
    exact h.trans_lt (pow_lt_one₀ (by positivity) hq hl)
  · exact tendsto_seminorm_dividedPower_smul N hNsmul hp hpC c y hq hy

end Main

section Closed

variable {C A B : Type*} [DenselyNormedField C] [CharZero C] [IsUltrametricDist C]
  [Ring A] [CommRing B] [Algebra C A] [Algebra C B]

/-- Over a densely normed field the divided-power estimate includes the boundary, in the
power form `‖κ‖ ^ (p - 1) ≤ ‖p‖`. In particular this includes the prime `2`. -/
theorem _root_.RingSeminorm.smul_le_one_of_bounded_powers
    (N : RingSeminorm A) (M : RingSeminorm B) (hM : IsNonarchimedean M)
    (hNsmul : ∀ (c : C) x, N (c • x) = ‖c‖ * N x)
    (D L R : A →ₐ[C] B) (hD : ∀ x, M (D x) ≤ N x)
    (hLR : ∀ x y, M (L x * R y) = N x * N y)
    (p : ℕ) (hp : p.Prime) (hpC : ‖(p : C)‖ < 1)
    (y : A) (hy : ∃ K : ℝ, ∀ n : ℕ, N (y ^ n) ≤ K)
    (he : M (D y - L y - R y) ≤ 1) (κ : C)
    (hκ : ‖κ‖ ^ (p - 1) ≤ ‖(p : C)‖) : N (κ • y) ≤ 1 := by
  have hp1 : 0 < (p : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast hp.one_lt)
  have hκ' : ‖κ‖ ≤ ‖(p : C)‖ ^ (((p : ℝ) - 1)⁻¹) := by
    apply (Real.le_rpow_inv_iff_of_pos (norm_nonneg _) (norm_nonneg _) hp1).mpr
    have hcast : (p : ℝ) - 1 = ((p - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hp.one_le, Nat.cast_one]
    rwa [hcast, Real.rpow_natCast]
  rw [hNsmul]
  by_contra! h
  have hy0 : 0 < N y := by nlinarith [norm_nonneg κ, apply_nonneg N y]
  have hr : (N y)⁻¹ < ‖(p : C)‖ ^ (((p : ℝ) - 1)⁻¹) :=
    ((inv_lt_iff_one_lt_mul₀ hy0).mpr h).trans_le hκ'
  obtain ⟨c, hc0, hc⟩ := NormedField.exists_lt_norm_lt C (by positivity) hr
  have hbound := RingSeminorm.smul_le_one_of_bounded_powers_of_lt
    N M hM hNsmul D L R hD hLR p hp hpC y hy he c hc
  rw [hNsmul] at hbound
  have := (inv_lt_iff_one_lt_mul₀ hy0).mp hc0
  nlinarith

end Closed

end TauCeti
