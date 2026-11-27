/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.Dynamics.TopologicalEntropy.NetEntropy
import Mathlib.Analysis.Real.OfDigits
import Mathlib.Analysis.Asymptotics.ExpGrowth
import Mathlib.Dynamics.TopologicalEntropy.Semiconj
import TauCeti.Dynamics.Entropy.FullShift

/-!
# Topological entropy of the doubling map

The doubling map `x ↦ 2 • x` of `UnitAddCircle` has topological entropy `log 2`
(`TauCeti.coverEntropy_two_nsmul_unitAddCircle`).

* Upper bound: binary expansion `x ↦ ∑ xᵢ 2^(-(i+1))` (Mathlib's `Real.ofDigits`) is a uniformly
  continuous surjection from the one-sided full shift on `Fin 2` onto the circle which
  semiconjugates the shift to the doubling map, so the entropy is at most that of the full shift,
  `log 2` (`TauCeti.coverEntropy_shift_nat`).
* Lower bound: the `2^n` points `j / 2^n` form a dynamical net at scale `1/8` and time `n`. For
  `d ≠ 0` with `2^n • d = 0`, some `2^k • d` with `k < n` has norm at least `1/4`, since doubling
  a point of norm less than `1/4` doubles its norm.

## Main results

* `TauCeti.coverEntropy_two_nsmul_unitAddCircle`,
  `TauCeti.coverEntropyInf_two_nsmul_unitAddCircle`: the doubling map has entropy `log 2`.
-/

public section

namespace TauCeti

open Dynamics Set Filter ExpGrowth
open scoped ENNReal

/-- The discrete uniform structure on `Fin n`, whose topology is Mathlib's discrete topology on
`Fin n`. -/
private abbrev finUniformSpace (n : ℕ) : UniformSpace (Fin n) := ⊥

attribute [local instance] finUniformSpace

/-- Binary expansion, as a map from the one-sided full shift on `Fin 2` to the circle. -/
private noncomputable def binaryExpansion (x : ℕ → Fin 2) : UnitAddCircle :=
  (Real.ofDigits x : UnitAddCircle)

private lemma uniformContinuous_binaryExpansion : UniformContinuous binaryExpansion :=
  CompactSpace.uniformContinuous_of_continuous
    ((AddCircle.continuous_mk' 1).comp Real.continuous_ofDigits)

private lemma surjective_binaryExpansion : Function.Surjective binaryExpansion := by
  intro z
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective z
  obtain ⟨x, -, hx⟩ := Real.ofDigits_SurjOn (b := 2) one_lt_two
    ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
  refine ⟨x, ?_⟩
  simp only [binaryExpansion, hx]
  rw [← Int.self_sub_floor, AddCircle.coe_sub, sub_eq_self]
  exact (AddCircle.coe_eq_zero_iff 1).mpr ⟨⌊t⌋, by simp⟩

/-- Binary expansion turns the shift into the doubling map. -/
private lemma semiconj_binaryExpansion :
    Function.Semiconj binaryExpansion (SymbolicDynamics.FullShift.shift (1 : ℕ))
      (fun z : UnitAddCircle ↦ 2 • z) := by
  intro x
  have h := Real.ofDigits_eq_sum_add_ofDigits x 1
  simp only [Finset.range_one, Finset.sum_singleton, Real.ofDigitsTerm, zero_add, pow_one,
    Nat.cast_ofNat] at h
  have hx : 2 * Real.ofDigits x = ((x 0 : ℕ) : ℝ) +
      Real.ofDigits (SymbolicDynamics.FullShift.shift (1 : ℕ) x) := by
    have : SymbolicDynamics.FullShift.shift (1 : ℕ) x = fun i ↦ x (i + 1) := by
      funext i
      simp [SymbolicDynamics.FullShift.shift_apply, add_comm]
    rw [this, h]
    ring
  have hzero : ((((x 0 : ℕ) : ℝ)) : UnitAddCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff 1).mpr ⟨((x 0 : ℕ) : ℤ), by simp⟩
  change (Real.ofDigits (SymbolicDynamics.FullShift.shift (1 : ℕ) x) : UnitAddCircle) =
    2 • (Real.ofDigits x : UnitAddCircle)
  rw [← AddCircle.coe_nsmul, nsmul_eq_mul, Nat.cast_ofNat, hx, AddCircle.coe_add, hzero,
    zero_add]

/-- Doubling a point of the circle of norm at most `1/4` doubles its norm. -/
private lemma norm_two_nsmul_of_norm_le {y : UnitAddCircle} (hy : ‖y‖ ≤ 1 / 4) :
    ‖2 • y‖ = 2 * ‖y‖ := by
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective y
  have ht : ((t - round t : ℝ) : UnitAddCircle) = (t : UnitAddCircle) := by
    rw [AddCircle.coe_sub, sub_eq_self]
    exact (AddCircle.coe_eq_zero_iff 1).mpr ⟨round t, by simp⟩
  have hnorm : ‖((t : ℝ) : UnitAddCircle)‖ = |t - round t| := UnitAddCircle.norm_eq
  change ‖((t : ℝ) : UnitAddCircle)‖ ≤ 1 / 4 at hy
  rw [hnorm] at hy
  change ‖2 • ((t : ℝ) : UnitAddCircle)‖ = 2 * ‖((t : ℝ) : UnitAddCircle)‖
  have h1 := (AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) (x := t - round t) one_ne_zero).mpr
    (by rw [abs_one]; linarith)
  have h2 := (AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) (x := 2 * (t - round t))
    one_ne_zero).mpr (by rw [abs_mul, abs_two, abs_one]; linarith)
  rw [← ht, ← AddCircle.coe_nsmul, nsmul_eq_mul, Nat.cast_ofNat, h1, h2, abs_mul, abs_two]

/-- If `2^n • d = 0` and `d ≠ 0`, some `2^k • d` with `k < n` has norm at least `1/4`. -/
private lemma exists_le_norm_two_pow_nsmul {d : UnitAddCircle} (hd : d ≠ 0) {n : ℕ}
    (hn : 2 ^ n • d = 0) : ∃ k < n, 1 / 4 ≤ ‖2 ^ k • d‖ := by
  by_contra! h
  have key : ∀ k ≤ n, ‖2 ^ k • d‖ = 2 ^ k * ‖d‖ := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, mul_nsmul, norm_two_nsmul_of_norm_le (h k (by omega)).le,
        ih (by omega), pow_succ, mul_comm _ (2 : ℝ), mul_assoc]
  have := key n le_rfl
  rw [hn, norm_zero] at this
  exact hd (norm_eq_zero.mp
    ((mul_eq_zero.mp this.symm).resolve_left (pow_ne_zero n two_ne_zero)))

/-- The dyadic points `j / 2^n`, `j < 2^n`. -/
private noncomputable def dyadicPoint (n : ℕ) (j : ℕ) : UnitAddCircle :=
  ((j : ℝ) / 2 ^ n : ℝ)

/-- Distinct dyadic points of level `n` are `1/4`-separated by some iterate of the doubling map
before time `n`. -/
private lemma exists_le_dist_dyadicPoint {n i j : ℕ} (hi : i < 2 ^ n) (hj : j < 2 ^ n)
    (hij : i ≠ j) : ∃ k < n, 1 / 4 ≤
      dist ((fun z : UnitAddCircle ↦ 2 • z)^[k] (dyadicPoint n i))
        ((fun z : UnitAddCircle ↦ 2 • z)^[k] (dyadicPoint n j)) := by
  set d := dyadicPoint n i - dyadicPoint n j
  have hiter : ∀ k (z : UnitAddCircle), (fun z : UnitAddCircle ↦ 2 • z)^[k] z = 2 ^ k • z :=
    fun k z ↦ by
      induction k generalizing z with
      | zero => simp
      | succ k ih => rw [Function.iterate_succ_apply, ih, ← mul_nsmul, ← pow_succ']
  have hn : 2 ^ n • d = 0 := by
    simp only [d, dyadicPoint, ← AddCircle.coe_sub, ← AddCircle.coe_nsmul, nsmul_eq_mul]
    refine (AddCircle.coe_eq_zero_iff 1).mpr ⟨(i : ℤ) - j, ?_⟩
    rw [zsmul_one]
    push_cast
    field_simp
  have hd : d ≠ 0 := by
    simp only [d, dyadicPoint, ← AddCircle.coe_sub, ne_eq, AddCircle.coe_eq_zero_iff]
    rintro ⟨m, hm⟩
    rw [zsmul_one] at hm
    have hmr : (m : ℝ) * 2 ^ n = (i : ℝ) - j := by
      rw [hm]
      field_simp
    have hmz : m * 2 ^ n = (i : ℤ) - j := by exact_mod_cast hmr
    have : (i : ℤ) < 2 ^ n := by exact_mod_cast hi
    have : (j : ℤ) < 2 ^ n := by exact_mod_cast hj
    have : (0 : ℤ) < 2 ^ n := by positivity
    rcases lt_trichotomy m 0 with hm0 | rfl | hm0
    · have : m * (2 : ℤ) ^ n ≤ -2 ^ n := by nlinarith
      linarith
    · exact hij (by omega)
    · have : (2 : ℤ) ^ n ≤ m * 2 ^ n := by nlinarith
      linarith
  obtain ⟨k, hk, hle⟩ := exists_le_norm_two_pow_nsmul hd hn
  refine ⟨k, hk, ?_⟩
  rwa [hiter, hiter, dist_eq_norm, ← smul_sub]

/-- The `2^n` dyadic points of level `n` form a dynamical net at scale `1/8` and time `n`. -/
private lemma pow_le_netMaxcard (n : ℕ) :
    (2 : ℕ∞) ^ n ≤ netMaxcard (fun z : UnitAddCircle ↦ 2 • z) univ
      {p | dist p.1 p.2 < 1 / 8} n := by
  classical
  let s : Finset UnitAddCircle := (Finset.range (2 ^ n)).image (dyadicPoint n)
  have hinj : Set.InjOn (dyadicPoint n) (Finset.range (2 ^ n) : Set ℕ) := by
    intro i hi j hj hij
    by_contra hne
    obtain ⟨k, -, hk⟩ := exists_le_dist_dyadicPoint (Finset.mem_range.mp hi)
      (Finset.mem_range.mp hj) hne
    rw [hij, dist_self] at hk
    norm_num at hk
  have hcard : s.card = 2 ^ n := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hnet : IsDynNetIn (fun z : UnitAddCircle ↦ 2 • z) univ {p | dist p.1 p.2 < 1 / 8} n
      (s : Set UnitAddCircle) := by
    refine ⟨subset_univ _, ?_⟩
    rintro _ hx _ hy hxy
    simp only [s, Finset.coe_image, Finset.coe_range, mem_image, mem_Iio] at hx hy
    obtain ⟨i, hi, rfl⟩ := hx
    obtain ⟨j, hj, rfl⟩ := hy
    have hij : i ≠ j := fun h ↦ hxy (h ▸ rfl)
    obtain ⟨k, hk, hle⟩ := exists_le_dist_dyadicPoint hi hj hij
    refine Set.disjoint_left.mpr fun z hzi hzj ↦ ?_
    simp only [SetRel.mem_ball, SetRel.mem_inv, mem_dynEntourage, mem_ofPred_eq] at hzi hzj
    have h1 := hzi k hk
    have h2 := hzj k hk
    have := dist_triangle_left ((fun z : UnitAddCircle ↦ 2 • z)^[k] (dyadicPoint n i))
      ((fun z : UnitAddCircle ↦ 2 • z)^[k] (dyadicPoint n j))
      ((fun z : UnitAddCircle ↦ 2 • z)^[k] z)
    rw [dist_comm] at h1 h2
    linarith
  have := hnet.card_le_netMaxcard
  rwa [hcard, Nat.cast_pow, Nat.cast_ofNat] at this

/-- The doubling map of the circle has topological entropy at least `log 2`. -/
private lemma log_two_le_netEntropyInfEntourage :
    ENNReal.log 2 ≤ netEntropyInfEntourage (fun z : UnitAddCircle ↦ 2 • z) univ
      {p | dist p.1 p.2 < 1 / 8} := by
  rw [← expGrowthInf_pow]
  exact expGrowthInf_monotone fun n ↦ by
    simpa using ENat.toENNReal_le.2 (pow_le_netMaxcard n)

private lemma mem_uniformity_dist_lt_eighth :
    {p : UnitAddCircle × UnitAddCircle | dist p.1 p.2 < 1 / 8} ∈ uniformity UnitAddCircle :=
  Metric.dist_mem_uniformity (by norm_num)

/-- **Check.** The doubling map `x ↦ 2 • x` of the circle has topological entropy `log 2`. -/
theorem coverEntropy_two_nsmul_unitAddCircle :
    coverEntropy (fun z : UnitAddCircle ↦ 2 • z) univ = ENNReal.log 2 := by
  refine le_antisymm ?_ ?_
  · calc coverEntropy (fun z : UnitAddCircle ↦ 2 • z) univ =
          coverEntropy (fun z : UnitAddCircle ↦ 2 • z) (binaryExpansion '' univ) := by
          rw [image_univ, surjective_binaryExpansion.range_eq]
      _ ≤ coverEntropy (SymbolicDynamics.FullShift.shift (1 : ℕ)) (univ : Set (ℕ → Fin 2)) :=
          coverEntropy_image_le_of_uniformContinuous semiconj_binaryExpansion
            uniformContinuous_binaryExpansion univ
      _ = ENNReal.log 2 := by rw [coverEntropy_shift_nat, Fintype.card_fin, Nat.cast_ofNat]
  · exact log_two_le_netEntropyInfEntourage.trans <|
      (netEntropyInfEntourage_le_coverEntropyInf _ _ mem_uniformity_dist_lt_eighth).trans
        (coverEntropyInf_le_coverEntropy _ _)

/-- **Check.** The `liminf` topological entropy of the doubling map of the circle is `log 2`. -/
theorem coverEntropyInf_two_nsmul_unitAddCircle :
    coverEntropyInf (fun z : UnitAddCircle ↦ 2 • z) univ = ENNReal.log 2 :=
  le_antisymm (coverEntropyInf_le_coverEntropy _ _ |>.trans_eq
    coverEntropy_two_nsmul_unitAddCircle)
    (log_two_le_netEntropyInfEntourage.trans
      (netEntropyInfEntourage_le_coverEntropyInf _ _ mem_uniformity_dist_lt_eighth))

end TauCeti
