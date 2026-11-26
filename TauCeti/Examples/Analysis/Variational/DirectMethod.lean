/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
public import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Dimension
public import TauCeti.Analysis.Normed.Lp.Diagonal.Basic

/-!
# Checks: compact maps and the direct method on `ℓ²`

Checks of compact diagonal maps and of minimization problems with and without minimizers, on
`ℓ² = ℓ²(ℕ, ℝ)` with the unit vectors `eₙ = lp.single 2 n 1`.

Compact maps, for the compact injective diagonal map `j = diag(1/(n + 1))` (`j`,
`isCompactOperator_j`, `injective_j`):

* `‖j eₙ‖ = 1/(n + 1) → 0` (`norm_j_single`, `tendsto_norm_j_single`);
* the unbounded sequence `uₙ = (n + 1) eₙ` has `‖j uₙ‖ = 1` (`norm_smul_single`,
  `norm_j_smul_single`);
* the identity of `ℓ²` is not compact (`not_isCompactOperator_id`).

Minimization:

* `‖u‖²` attains its infimum `0` on `ℓ²` at `0` (`isMinOn_norm_sq`);
* the energy `E(u) = ‖k u‖² = Σ |uₙ|²/(n + 1)`, `k = diag(1/√(n + 1))`, is positive on the unit
  sphere `S` (`energy_pos`) with `E(eₙ) = 1/(n + 1)` (`energy_single`), so it has no minimizer on
  `S` (`not_exists_isMinOn_energy_sphere`), although `S` is bounded;
* `E(u) = −⟪e₀, u⟫` is unbounded below on `ℓ²` (`not_bddBelow_neg_inner`), `sInf (E '' ℓ²)` is
  the junk value `0` (`sInf_neg_inner`), and `E` has no minimizer (`not_exists_isMinOn_neg_inner`).
-/

public section

open Filter Set
open scoped lp ENNReal NNReal Topology RealInnerProductSpace

namespace TauCeti.DirectMethodChecks

/-- The space `ℓ²(ℕ, ℝ)`. -/
abbrev L2 : Type := ℓ^2(ℕ, ℝ)

/-- The unit vector `eₙ` of `ℓ²`. -/
noncomputable abbrev e (n : ℕ) : L2 := lp.single 2 n 1

/-- The unit vectors have norm `1`. -/
theorem norm_e (n : ℕ) : ‖e n‖ = 1 := by simp [e, lp.norm_single]

/-! ### Compact maps -/

/-- The coefficients `1/(n + 1)` decrease. -/
theorem antitone_inv_succ : Antitone fun n : ℕ ↦ (1 / (n + 1) : ℝ≥0) := fun m n h ↦ by
  dsimp only
  gcongr

/-- The compact diagonal map `j = diag(1/(n + 1))` of `ℓ²`. -/
noncomputable def j : L2 →L[ℝ] L2 := lp.diagonalCLM (lp.ofAntitone ℝ antitone_inv_succ)

/-- `j` multiplies the `n`-th coordinate by `1/(n + 1)`. -/
theorem j_single (n : ℕ) (a : ℝ) : j (lp.single 2 n a) = lp.single 2 n (a / (n + 1)) := by
  simp [j, lp.ofAntitone_apply, div_eq_inv_mul]

/-- `j` is compact, since its coefficients tend to `0`. -/
theorem isCompactOperator_j : IsCompactOperator j := by
  refine lp.isCompactOperator_diagonalCLM _ ?_
  simp only [lp.norm_ofAntitone_apply, Nat.cofinite_eq_atTop]
  simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)

/-- `j` is injective, since no coefficient vanishes. -/
theorem injective_j : Function.Injective j :=
  (lp.injective_diagonalCLM_ofAntitone_iff ℝ _).2 fun n ↦ by positivity

/-- `‖j eₙ‖ = 1/(n + 1)`. -/
theorem norm_j_single (n : ℕ) : ‖j (e n)‖ = 1 / (n + 1) := by
  simp [e, j_single, lp.norm_single, abs_of_pos (by positivity : (0 : ℝ) < n + 1)]

/-- `‖j eₙ‖ → 0`. -/
theorem tendsto_norm_j_single : Tendsto (fun n ↦ ‖j (e n)‖) atTop (𝓝 0) := by
  simpa only [norm_j_single] using tendsto_one_div_add_atTop_nhds_zero_nat

/-- `uₙ = (n + 1) eₙ` is unbounded: `‖uₙ‖ = n + 1`. -/
theorem norm_smul_single (n : ℕ) : ‖((n : ℝ) + 1) • e n‖ = n + 1 := by
  rw [norm_smul, norm_e, mul_one, Real.norm_eq_abs, abs_of_pos (by positivity)]

/-- `‖j ((n + 1) eₙ)‖ = 1`. -/
theorem norm_j_smul_single (n : ℕ) : ‖j (((n : ℝ) + 1) • e n)‖ = 1 := by
  rw [map_smul, norm_smul, norm_j_single, Real.norm_eq_abs, abs_of_pos (by positivity)]
  field_simp

/-- The identity of `ℓ²` is not compact. -/
theorem not_isCompactOperator_id : ¬ IsCompactOperator (ContinuousLinearMap.id ℝ L2) :=
  fun h ↦ (HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℝ L2)).infinite_iff_not_finiteDimensional.1
    inferInstance (.of_isCompactOperator_id h)

/-! ### Minimization -/

/-- `‖u‖²` attains its infimum `0` on `ℓ²` at `0`. -/
theorem isMinOn_norm_sq : IsMinOn (fun u : L2 ↦ ‖u‖ ^ 2) univ 0 :=
  isMinOn_iff.2 fun u _ ↦ by simp

/-- The coefficients `1/√(n + 1)` decrease. -/
theorem antitone_sqrt_inv_succ : Antitone fun n : ℕ ↦ NNReal.sqrt (1 / (n + 1)) :=
  fun _ _ h ↦ NNReal.sqrt_le_sqrt.2 (antitone_inv_succ h)

/-- The diagonal map `k = diag(1/√(n + 1))`, with `‖k u‖² = Σ |uₙ|²/(n + 1)`. -/
noncomputable def k : L2 →L[ℝ] L2 := lp.diagonalCLM (lp.ofAntitone ℝ antitone_sqrt_inv_succ)

/-- `k` is injective, since no coefficient vanishes. -/
theorem injective_k : Function.Injective k :=
  (lp.injective_diagonalCLM_ofAntitone_iff ℝ _).2 fun n ↦ by positivity

/-- The energy `E(u) = Σ |uₙ|²/(n + 1)`. -/
noncomputable def energy (u : L2) : ℝ := ‖k u‖ ^ 2

/-- `E(eₙ) = 1/(n + 1)`. -/
theorem energy_single (n : ℕ) : energy (e n) = 1 / (n + 1) := by
  simp [energy, k, lp.norm_single, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n + 1)]

/-- `E > 0` away from `0`. -/
theorem energy_pos {u : L2} (hu : u ≠ 0) : 0 < energy u := by
  have : k u ≠ 0 := (map_ne_zero_iff k injective_k).2 hu
  unfold energy
  positivity

/-- `E` has no minimizer on the unit sphere of `ℓ²`: it is positive there, while
`E(eₙ) = 1/(n + 1) → 0`. -/
theorem not_exists_isMinOn_energy_sphere :
    ¬ ∃ u ∈ Metric.sphere (0 : L2) 1, IsMinOn energy (Metric.sphere 0 1) u := by
  rintro ⟨u, hu, hmin⟩
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (energy_pos hu0)
  have := isMinOn_iff.1 hmin (e n) (by simp)
  rw [energy_single] at this
  exact_mod_cast (this.trans_lt hn).false

/-- `E(u) = −⟪e₀, u⟫` is unbounded below on `ℓ²`. -/
theorem not_bddBelow_neg_inner : ¬ BddBelow (range fun u : L2 ↦ -⟪e 0, u⟫) := by
  rintro ⟨m, hm⟩
  have h := hm ⟨(|m| + 1) • e 0, rfl⟩
  simp only [inner_smul_right, real_inner_self_eq_norm_sq, norm_e] at h
  linarith [le_abs_self m, neg_abs_le m]

/-- The infimum of `E(u) = −⟪e₀, u⟫` over `ℓ²` is the junk value `0`. -/
theorem sInf_neg_inner : sInf (range fun u : L2 ↦ -⟪e 0, u⟫) = 0 :=
  Real.sInf_of_not_bddBelow not_bddBelow_neg_inner

/-- `E(u) = −⟪e₀, u⟫` has no minimizer on `ℓ²`. -/
theorem not_exists_isMinOn_neg_inner : ¬ ∃ u : L2, IsMinOn (fun u : L2 ↦ -⟪e 0, u⟫) univ u := by
  rintro ⟨u, hu⟩
  exact not_bddBelow_neg_inner ⟨_, by rintro _ ⟨v, rfl⟩; exact isMinOn_iff.1 hu v (mem_univ v)⟩

end TauCeti.DirectMethodChecks
