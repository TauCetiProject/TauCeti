/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic
import TauCeti.Analysis.Complex.UpperHalfPlane.Displacement
import TauCeti.Analysis.Complex.UpperHalfPlane.MoebiusAction
import TauCeti.Analysis.SpecialFunctions.Hyperbolic

/-!
# The systole of the principal congruence subgroup `Γ(N)`

A hyperbolic element `γ` of `Γ(N)`, one with `|tr γ| > 2`, gives a closed geodesic on `Γ(N) \ ℍ`
whose length is the translation length `2 arcosh (|tr γ| / 2)` of `γ`, the least distance it moves
a point of `ℍ`. Since `tr γ ≡ 2 (mod N²)` (`CongruenceSubgroup.sq_dvd_two_sub_trace_of_mem_Gamma`),
such a trace has absolute value at least `N² - 2`, and every hyperbolic element of `Γ(N)` moves
every point of `ℍ` at least `4 log (N / 2)`. Conversely, for `N ≥ 3` the hyperbolic matrix
`!![1 - N², N; -N, 1] = !![1, N; 0, 1] * !![1, 0; -N, 1]` of `Γ(N)` moves `I` at most
`4 log N + log 2`. So the shortest closed geodesic of `Γ(N) \ ℍ` has length `4 log N + O(1)`,
with explicit constants.

Both bounds are read off the hyperbolic cosine of a displacement: the trace bound
`tr² g - 4 ≤ 2 (cosh (dist (g • z) z) - 1)` of `Matrix.SpecialLinearGroup.trace_sq_sub_four_le`
gives `cosh ≥ N⁴ / 16` below, and `Matrix.SpecialLinearGroup.dist_smul_I_le_log` bounds the
distance moved by `I` by the logarithm of the sum of the squared entries above.

The lower bound concerns every hyperbolic element, so it also bounds below the closed geodesics
of `Γ(N) \ ℍ` that stay nontrivial after the cusps are filled in. The witness above, the one of
Bakker and Tsimerman's Lemma 5, is the product of two parabolic elements of `Γ(N)`, so it becomes
trivial after filling. For `N` prime to `3`, write `N = 3 r + x` with `x ∈ {1, 2}`; a witness of
length `4 log N + O(1)` meant to survive the filling is

`M = !![1 + x N, 3 N; N (2 - x² + 2 N x) / 3, 1 + 2 N² - x N]`,

which has the exact factorizations

* `M = -L(2r) U(3) L(-r-1) U(3)` for `x = 1` (`CongruenceSubgroup.fillingWitnessOne`);
* `M = L(2r+1) U(-3) L(-r-1) U(1) L(1) U(1)` for `x = 2` (`CongruenceSubgroup.fillingWitnessTwo`).

Here `U(t) = T ^ t = !![1, t; 0, 1]` and `L(t) = S T ^ (-t) S⁻¹ = !![1, 0; t, 1]`. The matrix `M`
lies in `Γ(N)`, has trace `2 N² + 2`, and for `N ≥ 2` moves `I` at most `4 log N + 3 log 2`.
That its geodesic survives the filling, because its image in the compact triangle group
`Δ(2, 3, N)` stays hyperbolic, is a statement about that image and is not proved here. The
factorizations are what transport `M` to that group, where `S` and `T` go to its order-`2` and
order-`N` rotations.

## Main results

* `CongruenceSubgroup.four_mul_log_div_two_le_dist_smul_of_mem_Gamma`: a hyperbolic element of
  `Γ(N)` moves every point of `ℍ` at least `4 log (N / 2)`.
* `CongruenceSubgroup.exists_mem_Gamma_dist_smul_I_le`: for `N ≥ 3` some hyperbolic element of
  `Γ(N)` moves `I` at most `4 log N + log 2`.
* `CongruenceSubgroup.fillingWitnessOne`, `CongruenceSubgroup.fillingWitnessTwo`: the witnesses
  at the levels `3 r + 1` and `3 r + 2`, with their entries, their membership in `Γ(N)`, their
  trace `2 N² + 2` and their displacement of `I`.

## References

* Benjamin Bakker and Jacob Tsimerman, *p-torsion monodromy representations of elliptic curves
  over geometric function fields*, Annals of Mathematics 184 (2016), 709–744, §3.1 and Lemma 5
  (the systole of `X(p)`, of length `4 log p + O(1)`).
* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91, Springer,
  1983, Chapter 7 (translation lengths and traces).
-/

public section

open UpperHalfPlane ModularGroup
open scoped MatrixGroups

namespace CongruenceSubgroup

variable {N : ℕ}

/-! ### The lower bound -/

/-- The square of a hyperbolic trace in `Γ(N)` is at least `N⁴ / 8 + 2`: it is at least `9`, and
at least `(N² - 2)²` by `sq_sub_two_le_abs_trace_of_mem_Gamma`. -/
private theorem pow_four_add_sixteen_le_eight_mul_trace_sq {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma N)
    (htr : 2 < |(γ : Matrix (Fin 2) (Fin 2) ℤ).trace|) :
    (N : ℤ) ^ 4 + 16 ≤ 8 * (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 := by
  set t := (γ : Matrix (Fin 2) (Fin 2) ℤ).trace
  have hle := sq_sub_two_le_abs_trace_of_mem_Gamma hγ fun h ↦ by simp [t, h] at htr
  rw [← sq_abs t]
  rcases le_or_gt N 1 with hN | hN
  · have : (N : ℤ) ≤ 1 := by exact_mod_cast hN
    nlinarith
  · -- with `m = N² ≥ 4`: `8 (m - 2)² - m² - 16 = (m - 4) (7 m - 4) ≥ 0`
    have hm : (4 : ℤ) ≤ (N : ℤ) ^ 2 := by
      have : (2 : ℤ) ≤ N := by exact_mod_cast hN
      nlinarith
    have hsq : ((N : ℤ) ^ 2 - 2) ^ 2 ≤ |t| ^ 2 := pow_le_pow_left₀ (by linarith) hle 2
    nlinarith

/-- **The systole of `Γ(N)` is at least `4 log (N / 2)`.** A hyperbolic element `γ` of `Γ(N)`,
one with `|tr γ| > 2`, moves every point of `ℍ` a hyperbolic distance at least `4 log (N / 2)`.
Hence every closed geodesic of `Γ(N) \ ℍ` has length at least `4 log N - 4 log 2`. -/
theorem four_mul_log_div_two_le_dist_smul_of_mem_Gamma {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma N)
    (htr : 2 < |(γ : Matrix (Fin 2) (Fin 2) ℤ).trace|) (z : ℍ) :
    4 * Real.log (N / 2) ≤ dist (γ • z) z := by
  set δ := dist (γ • z) z
  -- `cosh δ ≥ tr² / 2 - 1 ≥ N⁴ / 16`
  have hcosh : ((N : ℝ) / 2) ^ 4 ≤ Real.cosh δ := by
    have h := Matrix.SpecialLinearGroup.trace_sq_sub_four_le
      (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ) z
    rw [Matrix.SpecialLinearGroup.map_intCastRingHom_smul] at h
    have htr' : ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ : SL(2, ℝ)) :
        Matrix (Fin 2) (Fin 2) ℝ).trace = ((γ : Matrix (Fin 2) (Fin 2) ℤ).trace : ℝ) := by
      simp [Matrix.trace_fin_two]
    have h' : ((N : ℤ) ^ 4 + 16 : ℝ) ≤ 8 * ((γ : Matrix (Fin 2) (Fin 2) ℤ).trace : ℝ) ^ 2 := by
      exact_mod_cast pow_four_add_sixteen_le_eight_mul_trace_sq hγ htr
    push_cast at h'
    rw [htr'] at h
    nlinarith
  rcases N.eq_zero_or_pos with rfl | hN
  · simp [δ, dist_nonneg]
  calc 4 * Real.log (N / 2) = Real.log (((N : ℝ) / 2) ^ 4) := by
        rw [Real.log_pow]; push_cast; ring
    _ ≤ Real.log (Real.cosh δ) := Real.log_le_log (by positivity) hcosh
    _ ≤ |δ| := Real.log_cosh_le_abs δ
    _ = δ := abs_of_nonneg dist_nonneg

/-! ### Upper bounds -/

/-- An integral matrix whose squared entries sum to at most `c N⁴` moves `I` at most
`4 log N + log c`. -/
private theorem dist_smul_I_le_of_sum_sq_le (γ : SL(2, ℤ)) {c : ℝ} (hN : 0 < N)
    (h : ((γ 0 0 ^ 2 + γ 0 1 ^ 2 + γ 1 0 ^ 2 + γ 1 1 ^ 2 : ℤ) : ℝ) ≤ c * (N : ℝ) ^ 4) :
    dist (γ • I) I ≤ 4 * Real.log N + Real.log c := by
  have hd := Matrix.SpecialLinearGroup.dist_smul_I_le_log
    (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ)
  rw [Matrix.SpecialLinearGroup.map_intCastRingHom_smul] at hd
  have hentry (i j : Fin 2) :
      (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ : SL(2, ℝ)) i j = (γ i j : ℝ) := by
    simp
  simp only [hentry] at hd
  push_cast at h
  have hpos : 0 < (γ 0 0 : ℝ) ^ 2 + (γ 0 1 : ℝ) ^ 2 + (γ 1 0 : ℝ) ^ 2 + (γ 1 1 : ℝ) ^ 2 := by
    have hdet := γ.det_coe
    rw [Matrix.det_fin_two] at hdet
    have hdet' : (γ 0 0 : ℝ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by exact_mod_cast hdet
    nlinarith [sq_nonneg ((γ 0 0 : ℝ) - γ 1 1), sq_nonneg ((γ 0 1 : ℝ) + γ 1 0)]
  have hc : 0 < c := pos_of_mul_pos_left (hpos.trans_le h) (by positivity)
  calc dist (γ • I) I ≤ _ := hd
    _ ≤ Real.log (c * (N : ℝ) ^ 4) := Real.log_le_log hpos h
    _ = 4 * Real.log N + Real.log c := by
        rw [Real.log_mul hc.ne' (by positivity), Real.log_pow]; push_cast; ring

/-- An integral matrix whose squared entries sum to at most `8 N⁴` moves `I` at most
`4 log N + 3 log 2`. -/
private theorem dist_smul_I_le_of_sum_sq_le_eight (γ : SL(2, ℤ)) (hN : 0 < N)
    (h : γ 0 0 ^ 2 + γ 0 1 ^ 2 + γ 1 0 ^ 2 + γ 1 1 ^ 2 ≤ 8 * (N : ℤ) ^ 4) :
    dist (γ • I) I ≤ 4 * Real.log N + 3 * Real.log 2 := by
  have h8 : 3 * Real.log 2 = Real.log 8 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  rw [h8]
  exact dist_smul_I_le_of_sum_sq_le γ hN (by exact_mod_cast h)

/-- **The systole of `Γ(N)` is at most `4 log N + log 2`.** For `N ≥ 3` the matrix
`!![1 - N², N; -N, 1] = !![1, N; 0, 1] * !![1, 0; -N, 1]` lies in `Γ(N)`, is hyperbolic with
trace `2 - N²`, and moves `I` a distance at most `4 log N + log 2`; its closed geodesic on
`Γ(N) \ ℍ` therefore has length at most `4 log N + log 2`. -/
theorem exists_mem_Gamma_dist_smul_I_le (hN : 3 ≤ N) :
    ∃ γ ∈ Gamma N, 2 < |(γ : Matrix (Fin 2) (Fin 2) ℤ).trace| ∧
      dist (γ • I) I ≤ 4 * Real.log N + Real.log 2 := by
  let γ : SL(2, ℤ) := ⟨!![1 - (N : ℤ) ^ 2, N; -N, 1], by simp [Matrix.det_fin_two]; ring⟩
  refine ⟨γ, mem_Gamma_iff_dvd.2 ⟨⟨-N, by simp [γ, sq]⟩, ⟨1, by simp [γ]⟩, ⟨-1, by simp [γ]⟩,
    ⟨0, by simp [γ]⟩⟩, ?_, dist_smul_I_le_of_sum_sq_le γ (by omega) ?_⟩
  · rw [show (γ : Matrix (Fin 2) (Fin 2) ℤ).trace = 2 - (N : ℤ) ^ 2 by
      simp [γ, Matrix.trace_fin_two]; ring]
    rw [abs_of_neg (by nlinarith)]
    nlinarith
  · -- the squared entries sum to `N⁴ + 2 ≤ 2 N⁴`
    have h : (γ 0 0 ^ 2 + γ 0 1 ^ 2 + γ 1 0 ^ 2 + γ 1 1 ^ 2 : ℤ) ≤ 2 * (N : ℤ) ^ 4 := by
      simp only [γ]
      simp
      nlinarith
    exact_mod_cast h

/-! ### The witnesses surviving cusp filling -/

/-- The witness at the level `N = 3 r + 1`: the word `-L(2r) U(3) L(-r-1) U(3)` in
`U(t) = T ^ t` and `L(t) = S T ^ (-t) S⁻¹`, equal to
`!![1 + N, 3 N; N (2 r + 1), 1 + 2 N² - N]` (`CongruenceSubgroup.coe_fillingWitnessOne`). -/
def fillingWitnessOne (r : ℕ) : SL(2, ℤ) :=
  -(S * T ^ (-(2 * r : ℤ)) * S⁻¹ * T ^ (3 : ℤ) * (S * T ^ ((r : ℤ) + 1) * S⁻¹) * T ^ (3 : ℤ))

/-- The witness at the level `N = 3 r + 2`: the word `L(2r+1) U(-3) L(-r-1) U(1) L(1) U(1)` in
`U(t) = T ^ t` and `L(t) = S T ^ (-t) S⁻¹`, equal to
`!![1 + 2 N, 3 N; 2 N (2 r + 1), 1 + 2 N² - 2 N]` (`CongruenceSubgroup.coe_fillingWitnessTwo`). -/
def fillingWitnessTwo (r : ℕ) : SL(2, ℤ) :=
  S * T ^ (-(2 * r + 1 : ℤ)) * S⁻¹ * T ^ (-3 : ℤ) * (S * T ^ ((r : ℤ) + 1) * S⁻¹) * T *
    (S * T ^ (-1 : ℤ) * S⁻¹) * T

/-- The witness at the level `3 r + 1` as the word `-L(2r) U(3) L(-r-1) U(3)` in `S` and `T`. -/
theorem fillingWitnessOne_eq (r : ℕ) :
    fillingWitnessOne r =
      -(S * T ^ (-(2 * r : ℤ)) * S⁻¹ * T ^ (3 : ℤ) * (S * T ^ ((r : ℤ) + 1) * S⁻¹) * T ^ (3 : ℤ)) :=
  (rfl)

/-- The witness at the level `3 r + 2` as the word `L(2r+1) U(-3) L(-r-1) U(1) L(1) U(1)` in `S`
and `T`. -/
theorem fillingWitnessTwo_eq (r : ℕ) :
    fillingWitnessTwo r =
      S * T ^ (-(2 * r + 1 : ℤ)) * S⁻¹ * T ^ (-3 : ℤ) * (S * T ^ ((r : ℤ) + 1) * S⁻¹) * T *
        (S * T ^ (-1 : ℤ) * S⁻¹) * T :=
  (rfl)

/-- The entries of the witness at the level `N = 3 r + 1`. -/
@[simp]
theorem coe_fillingWitnessOne (r : ℕ) :
    (fillingWitnessOne r : Matrix (Fin 2) (Fin 2) ℤ) =
      (!![1 + (3 * r + 1), 3 * (3 * r + 1); (3 * r + 1) * (2 * r + 1),
        1 + 2 * (3 * r + 1) ^ 2 - (3 * r + 1)] : Matrix (Fin 2) (Fin 2) ℤ) := by
  simp only [fillingWitnessOne_eq, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_mul, coe_T_zpow, coe_S, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- The entries of the witness at the level `N = 3 r + 2`. -/
@[simp]
theorem coe_fillingWitnessTwo (r : ℕ) :
    (fillingWitnessTwo r : Matrix (Fin 2) (Fin 2) ℤ) =
      (!![1 + 2 * (3 * r + 2), 3 * (3 * r + 2); 2 * (3 * r + 2) * (2 * r + 1),
        1 + 2 * (3 * r + 2) ^ 2 - 2 * (3 * r + 2)] : Matrix (Fin 2) (Fin 2) ℤ) := by
  simp only [fillingWitnessTwo_eq, Matrix.SpecialLinearGroup.coe_mul, coe_T_zpow, coe_T, coe_S,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- The witness at the level `3 r + 1` lies in `Γ(3 r + 1)`. -/
theorem fillingWitnessOne_mem_Gamma (r : ℕ) : fillingWitnessOne r ∈ Gamma (3 * r + 1) := by
  refine mem_Gamma_iff_dvd.2 ⟨⟨1, ?_⟩, ⟨3, ?_⟩, ⟨2 * r + 1, ?_⟩, ⟨2 * (3 * r + 1) - 1, ?_⟩⟩ <;>
    rw [coe_fillingWitnessOne] <;> simp <;> ring

/-- The witness at the level `3 r + 2` lies in `Γ(3 r + 2)`. -/
theorem fillingWitnessTwo_mem_Gamma (r : ℕ) : fillingWitnessTwo r ∈ Gamma (3 * r + 2) := by
  refine mem_Gamma_iff_dvd.2
    ⟨⟨2, ?_⟩, ⟨3, ?_⟩, ⟨2 * (2 * r + 1), ?_⟩, ⟨2 * (3 * r + 2) - 2, ?_⟩⟩ <;>
    rw [coe_fillingWitnessTwo] <;> simp <;> ring

/-- The witness at the level `N = 3 r + 1` has trace `2 N² + 2`. -/
theorem trace_fillingWitnessOne (r : ℕ) :
    (fillingWitnessOne r : Matrix (Fin 2) (Fin 2) ℤ).trace = 2 * (3 * r + 1) ^ 2 + 2 := by
  rw [coe_fillingWitnessOne, Matrix.trace_fin_two]
  simp
  ring

/-- The witness at the level `N = 3 r + 2` has trace `2 N² + 2`. -/
theorem trace_fillingWitnessTwo (r : ℕ) :
    (fillingWitnessTwo r : Matrix (Fin 2) (Fin 2) ℤ).trace = 2 * (3 * r + 2) ^ 2 + 2 := by
  rw [coe_fillingWitnessTwo, Matrix.trace_fin_two]
  simp
  ring

/-- The witness at the level `N = 3 r + 1`, for `r ≥ 1`, moves `I` at most `4 log N + 3 log 2`. -/
theorem dist_fillingWitnessOne_smul_I_le {r : ℕ} (hr : 1 ≤ r) :
    dist (fillingWitnessOne r • I) I ≤ 4 * Real.log (3 * r + 1 : ℕ) + 3 * Real.log 2 := by
  refine dist_smul_I_le_of_sum_sq_le_eight _ (by omega) ?_
  rw [coe_fillingWitnessOne]
  have : (1 : ℤ) ≤ r := by exact_mod_cast hr
  simp
  nlinarith [pow_pos (show (0 : ℤ) < r by omega) 3, pow_pos (show (0 : ℤ) < r by omega) 4]

/-- The witness at the level `N = 3 r + 2` moves `I` at most `4 log N + 3 log 2`. -/
theorem dist_fillingWitnessTwo_smul_I_le (r : ℕ) :
    dist (fillingWitnessTwo r • I) I ≤ 4 * Real.log (3 * r + 2 : ℕ) + 3 * Real.log 2 := by
  refine dist_smul_I_le_of_sum_sq_le_eight _ (by omega) ?_
  rw [coe_fillingWitnessTwo]
  have : (0 : ℤ) ≤ r := by exact_mod_cast r.zero_le
  simp
  nlinarith [pow_nonneg this 3, pow_nonneg this 4]

end CongruenceSubgroup
