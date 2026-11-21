/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import Mathlib.Topology.Sequences
public import TauCeti.Analysis.Normed.Lp.Diagonal.Basic
public import TauCeti.Analysis.Normed.Module.WeakSpace.Sphere
public import TauCeti.Analysis.Normed.Operator.Compact.WeakSpace
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.Analysis.Normed.Module.WeakSpace.Bounded

/-!
# Diagonal operators on `lp` in the weak topology

This file records weak-topology characterizations for bounded diagonal multipliers
`lp.diagonalCLM d` on `ℓ^p(ι, 𝕜)` (`1 ≤ p ≤ ∞`) and constructs the concrete harmonic diagonal
operator `lp.harmonicDiagonalCLM 𝕜 p` with coefficients `1 / (n + 1)` on `ℓ^p(ℕ, 𝕜)`.

* A diagonal multiplier `lp.diagonalCLM d` is globally weak-to-norm continuous if and only if
  only finitely many of its coefficients are nonzero
  (`lp.continuous_diagonalCLM_comp_toWeakSpace_symm_iff`).
* Over `ℝ` or `ℂ`, when infinitely many coefficients are nonzero, the weak closure of the level
  sphere `{u | ‖diagonalCLM d u‖ = r}` is `{u | ‖diagonalCLM d u‖ ≤ r}`
  (`lp.closure_toWeakSpace_setOf_norm_diagonalCLM_eq`), and for `r > 0` the sphere is weakly closed
  if and only if only finitely many coefficients are nonzero
  (`lp.isClosed_toWeakSpace_setOf_norm_diagonalCLM_eq_iff`, and for injective multipliers on
  infinite index sets `lp.not_isClosed_toWeakSpace_setOf_norm_diagonalCLM_eq`). When the
  coefficients tend to zero along the cofinite filter, every level sphere is sequentially weakly
  closed (`lp.isSeqClosed_toWeakSpace_setOf_norm_diagonalCLM_eq`).
* When infinitely many coefficients are nonzero and `‖d i‖ → 0` along the cofinite filter, the
  positive-radius level spheres `{u | ‖diagonalCLM d u‖ = r}` are norm-unbounded
  (`lp.not_isBounded_setOf_norm_diagonalCLM_eq`), and on `ℓ^p(ℕ, 𝕜)` with everywhere-nonzero null
  coefficients the normalized coordinate vectors `(d n)⁻¹ • lp.single p n 1` have no weakly
  convergent subsequence (`lp.not_tendsto_toWeakSpace_subseq_inv_smul_single`).
* The harmonic diagonal operator `lp.harmonicDiagonalCLM 𝕜 p` (`x n ↦ (n + 1)⁻¹ * x n`) is compact,
  injective, dense-range (for `p ≠ ∞`), and has infinite-dimensional range; it maps
  `(n + 1) • lp.single p n 1` to `lp.single p n 1`, giving an explicit witness on `ℓ^p(ℕ, 𝕜)`
  (in particular on `ℓ²(ℕ, 𝕜)`) of an injective compact operator whose positive-radius level spheres
  (in particular the unit level sphere) are unbounded
  (`lp.not_isBounded_setOf_norm_harmonicDiagonalCLM_eq`), sequentially weakly closed
  (`lp.isSeqClosed_toWeakSpace_setOf_norm_harmonicDiagonalCLM_eq`), and not weakly closed
  (`lp.not_isClosed_toWeakSpace_setOf_norm_harmonicDiagonalCLM_eq`).
-/

public section

open Bornology Filter Set Topology
open scoped lp ENNReal NNReal

namespace lp

section DiagonalWeak

variable {ι 𝕜 : Type*} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Over a nontrivially normed field, a bounded diagonal multiplier on `ℓ^p(ι, 𝕜)` is globally
weak-to-norm continuous if and only if only finitely many of its coefficients are nonzero. -/
theorem continuous_diagonalCLM_comp_toWeakSpace_symm_iff [NontriviallyNormedField 𝕜]
    (d : ℓ^∞(ι, 𝕜)) :
    Continuous (fun w : WeakSpace 𝕜 ℓ^p(ι, 𝕜) ↦
      diagonalCLM (p := p) d ((toWeakSpace 𝕜 ℓ^p(ι, 𝕜)).symm w)) ↔ {i : ι | d i ≠ 0}.Finite := by
  have : SeparatingDual 𝕜 ℓ^p(ι, 𝕜) := ⟨fun x hx ↦ by
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h
      push Not at h
      exact hx (lp.ext (funext h))
    exact ⟨evalCLM 𝕜 (fun _ : ι ↦ 𝕜) p i, hi⟩⟩
  exact (diagonalCLM (p := p) d).continuous_comp_toWeakSpace_symm_iff.trans
    (finiteDimensional_range_diagonalCLM_iff d)

variable [RCLike 𝕜]

/-- For an infinite index type and nonvanishing coefficients, a sphere of positive radius of a
diagonal operator is not weakly closed. -/
theorem not_isClosed_toWeakSpace_setOf_norm_diagonalCLM_eq [Infinite ι] {d : ℓ^∞(ι, 𝕜)}
    (hd : ∀ i, d i ≠ 0) {r : ℝ} (hr : 0 < r) :
    ¬ IsClosed (toWeakSpace 𝕜 ℓ^p(ι, 𝕜) '' {u | ‖diagonalCLM d u‖ = r}) :=
  TauCeti.not_isClosed_toWeakSpace_setOf_norm_eq not_finite
    ((injective_diagonalCLM_iff d).2 hd) hr

/-- If the coefficients tend to zero, every sphere of a diagonal operator is weakly sequentially
closed. -/
theorem isSeqClosed_toWeakSpace_setOf_norm_diagonalCLM_eq {d : ℓ^∞(ι, 𝕜)}
    (hd : Tendsto (fun i ↦ ‖d i‖) cofinite (𝓝 0)) (r : ℝ) :
    IsSeqClosed (toWeakSpace 𝕜 ℓ^p(ι, 𝕜) '' {u | ‖diagonalCLM d u‖ = r}) := by
  have heq : {u : ℓ^p(ι, 𝕜) | ‖diagonalCLM d u‖ = r} =
      diagonalCLM d ⁻¹' Metric.sphere 0 r := by
    ext u
    simp
  rw [heq]
  exact (isCompactOperator_diagonalCLM d hd).isSeqClosed_toWeakSpace_preimage
    Metric.isClosed_sphere

/-- If infinitely many coefficients of `d` are nonzero, the weak closure of the level sphere
`{u | ‖diagonalCLM d u‖ = r}` in `ℓ^p(ι, 𝕜)` is `{u | ‖diagonalCLM d u‖ ≤ r}`. -/
theorem closure_toWeakSpace_setOf_norm_diagonalCLM_eq (d : ℓ^∞(ι, 𝕜))
    (hd : {i : ι | d i ≠ 0}.Infinite) (r : ℝ) :
    closure (toWeakSpace 𝕜 ℓ^p(ι, 𝕜) '' {u : ℓ^p(ι, 𝕜) | ‖diagonalCLM (p := p) d u‖ = r}) =
      toWeakSpace 𝕜 ℓ^p(ι, 𝕜) '' {u : ℓ^p(ι, 𝕜) | ‖diagonalCLM (p := p) d u‖ ≤ r} :=
  (diagonalCLM (p := p) d).closure_toWeakSpace_setOf_norm_apply_eq
    (mt (finiteDimensional_range_diagonalCLM_iff d).1 hd) r

/-- For `r > 0`, the level sphere `{u | ‖diagonalCLM d u‖ = r}` in `ℓ^p(ι, 𝕜)` is weakly closed if
and only if only finitely many coefficients of `d` are nonzero. -/
theorem isClosed_toWeakSpace_setOf_norm_diagonalCLM_eq_iff (d : ℓ^∞(ι, 𝕜)) {r : ℝ} (hr : 0 < r) :
    IsClosed (toWeakSpace 𝕜 ℓ^p(ι, 𝕜) '' {u : ℓ^p(ι, 𝕜) | ‖diagonalCLM (p := p) d u‖ = r}) ↔
      {i : ι | d i ≠ 0}.Finite :=
  ((diagonalCLM (p := p) d).isClosed_toWeakSpace_setOf_norm_apply_eq_iff hr).trans
    (finiteDimensional_range_diagonalCLM_iff d)

/-- If infinitely many coefficients of `d` are nonzero and `‖d i‖ → 0` along the cofinite filter,
then every positive-radius level sphere `{u | ‖diagonalCLM d u‖ = r}` in `ℓ^p(ι, 𝕜)` is
norm-unbounded. -/
theorem not_isBounded_setOf_norm_diagonalCLM_eq (d : ℓ^∞(ι, 𝕜))
    (hinf : {i : ι | d i ≠ 0}.Infinite) (hd : Tendsto (fun i ↦ ‖d i‖) cofinite (𝓝 0))
    {r : ℝ} (hr : 0 < r) :
    ¬ IsBounded {u : ℓ^p(ι, 𝕜) | ‖diagonalCLM (p := p) d u‖ = r} := by
  classical
  intro hbd
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hbd
  set M : ℝ := max C 0 + 1
  have hM : 0 < M := by positivity
  have hfin : {i : ι | ¬ ‖d i‖ < r / M}.Finite :=
    eventually_cofinite.1 (hd.eventually (gt_mem_nhds (div_pos hr hM)))
  obtain ⟨i, hi_ne, hi_lt⟩ := (hinf.sdiff hfin).nonempty
  have hdi_lt : ‖d i‖ < r / M := not_not.1 hi_lt
  have hdi_pos : 0 < ‖d i‖ := norm_pos_iff.2 hi_ne
  have hp : 0 < p := zero_lt_one.trans_le Fact.out
  let u : ℓ^p(ι, 𝕜) := ((r : 𝕜) * (d i)⁻¹) • lp.single p i (1 : 𝕜)
  have hu_mem : ‖diagonalCLM (p := p) d u‖ = r := by
    have hDu : diagonalCLM (p := p) d u = lp.single p i (r : 𝕜) := by
      simp only [u, ← lp.single_smul, diagonalCLM_single, smul_eq_mul, mul_one]
      rw [mul_left_comm, mul_inv_cancel₀ hi_ne, mul_one]
    rw [hDu, lp.norm_single hp, RCLike.norm_ofReal, abs_of_pos hr]
  have hu_norm : ‖u‖ = r / ‖d i‖ := by
    rw [norm_smul, lp.norm_single hp, norm_one, mul_one, norm_mul, RCLike.norm_ofReal,
      abs_of_pos hr, norm_inv, div_eq_mul_inv]
  have hle : ‖u‖ ≤ C := hC u hu_mem
  have hgt : M < r / ‖d i‖ := (lt_div_iff₀ hdi_pos).2 <| by
    rw [mul_comm]
    exact (lt_div_iff₀ hM).1 hdi_lt
  have hCM : C < M := lt_of_le_of_lt (le_max_left C 0) (lt_add_one _)
  linarith

/-- If every coefficient of `d : ℓ^∞(ℕ, 𝕜)` is nonzero and `‖d n‖ → 0`, then the normalized
coordinate vectors `(d n)⁻¹ • lp.single p n 1` have no weakly convergent subsequence. -/
theorem not_tendsto_toWeakSpace_subseq_inv_smul_single (d : ℓ^∞(ℕ, 𝕜))
    (hd0 : ∀ n, d n ≠ 0) (hd : Tendsto (fun n ↦ ‖d n‖) atTop (𝓝 0)) (x : ℓ^p(ℕ, 𝕜))
    {σ : ℕ → ℕ} (hσ : StrictMono σ) :
    ¬ Tendsto (fun n ↦ toWeakSpace 𝕜 ℓ^p(ℕ, 𝕜) ((d (σ n))⁻¹ • lp.single p (σ n) (1 : 𝕜)))
        atTop (𝓝 (toWeakSpace 𝕜 ℓ^p(ℕ, 𝕜) x)) := by
  intro hlim
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hlim.isBounded_range_of_toWeakSpace
  set M : ℝ := max C 0 + 1
  have hM : 0 < M := by positivity
  have hsub : Tendsto (fun n ↦ ‖d (σ n)‖) atTop (𝓝 0) := hd.comp hσ.tendsto_atTop
  obtain ⟨n, hn⟩ := (hsub.eventually (gt_mem_nhds (inv_pos.2 hM))).exists
  have hp : 0 < p := zero_lt_one.trans_le Fact.out
  have hpos : 0 < ‖d (σ n)‖ := norm_pos_iff.2 (hd0 (σ n))
  have hle : ‖d (σ n)‖⁻¹ ≤ C := by
    have h := hC _ (mem_range_self n)
    simpa only [norm_smul, norm_inv, lp.norm_single hp, norm_one, mul_one] using h
  have hgt : M < ‖d (σ n)‖⁻¹ := (lt_inv_comm₀ hM hpos).2 hn
  have hCM : C < M := lt_of_le_of_lt (le_max_left C 0) (lt_add_one _)
  linarith

end DiagonalWeak

section Harmonic

variable (𝕜 : Type*) [RCLike 𝕜]

/-- The bounded harmonic weight sequence `n ↦ (n + 1)⁻¹` in `ℓ^∞(ℕ, 𝕜)`. -/
noncomputable def harmonicWeights : ℓ^∞(ℕ, 𝕜) :=
  ofAntitone 𝕜 (c := fun n : ℕ ↦ ((n : ℝ≥0) + 1)⁻¹) fun _ _ h ↦
    inv_anti₀ (by positivity) (by gcongr)

/-- The `n`-th harmonic weight is `(n + 1)⁻¹`. -/
@[simp]
theorem harmonicWeights_apply (n : ℕ) : harmonicWeights 𝕜 n = ((n : 𝕜) + 1)⁻¹ :=
  (ofAntitone_apply 𝕜 _ n).trans (by push_cast; rfl)

/-- The norm of the `n`-th harmonic weight is `(n + 1)⁻¹`. -/
theorem norm_harmonicWeights_apply (n : ℕ) : ‖harmonicWeights 𝕜 n‖ = ((n : ℝ) + 1)⁻¹ :=
  (norm_ofAntitone_apply 𝕜 _ n).trans (by push_cast; rfl)

/-- Every harmonic weight is nonzero. -/
theorem harmonicWeights_ne_zero (n : ℕ) : harmonicWeights 𝕜 n ≠ 0 := by
  rw [harmonicWeights_apply]
  exact inv_ne_zero (by exact_mod_cast Nat.succ_ne_zero n)

/-- The norms of the harmonic weights tend to zero. -/
theorem tendsto_norm_harmonicWeights :
    Tendsto (fun n ↦ ‖harmonicWeights 𝕜 n‖) atTop (𝓝 0) := by
  simpa only [norm_harmonicWeights_apply, ← one_div] using
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)

/-- The harmonic diagonal operator `x n ↦ (n + 1)⁻¹ * x n` on `ℓ^p(ℕ, 𝕜)`. -/
noncomputable def harmonicDiagonalCLM (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ℓ^p(ℕ, 𝕜) →L[𝕜] ℓ^p(ℕ, 𝕜) :=
  diagonalCLM (p := p) (harmonicWeights 𝕜)

/-- `lp.harmonicDiagonalCLM` is the diagonal multiplier of `lp.harmonicWeights`. -/
theorem harmonicDiagonalCLM_eq_diagonalCLM (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    harmonicDiagonalCLM 𝕜 p = diagonalCLM (p := p) (harmonicWeights 𝕜) := (rfl)

/-- Applying `lp.harmonicDiagonalCLM` multiplies the `n`-th coordinate by `(n + 1)⁻¹`. -/
@[simp]
theorem harmonicDiagonalCLM_apply (p : ℝ≥0∞) [Fact (1 ≤ p)] (x : ℓ^p(ℕ, 𝕜)) (n : ℕ) :
    harmonicDiagonalCLM 𝕜 p x n = ((n : 𝕜) + 1)⁻¹ * x n := by
  simp [harmonicDiagonalCLM]

/-- `lp.harmonicDiagonalCLM` acts on the `n`-th coordinate vector by multiplying by `(n + 1)⁻¹`. -/
@[simp]
theorem harmonicDiagonalCLM_single (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℕ) (a : 𝕜) :
    harmonicDiagonalCLM 𝕜 p (lp.single p n a) = lp.single p n (((n : 𝕜) + 1)⁻¹ * a) := by
  simp [harmonicDiagonalCLM]

/-- The harmonic diagonal operator on `ℓ^p(ℕ, 𝕜)` is compact. -/
theorem isCompactOperator_harmonicDiagonalCLM (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    IsCompactOperator (harmonicDiagonalCLM 𝕜 p) :=
  isCompactOperator_diagonalCLM (harmonicWeights 𝕜)
    (Nat.cofinite_eq_atTop ▸ tendsto_norm_harmonicWeights 𝕜)

/-- The harmonic diagonal operator on `ℓ^p(ℕ, 𝕜)` is injective. -/
theorem harmonicDiagonalCLM_injective (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Function.Injective (harmonicDiagonalCLM 𝕜 p) :=
  (injective_diagonalCLM_iff (harmonicWeights 𝕜)).2 (harmonicWeights_ne_zero 𝕜)

/-- For finite exponent `1 ≤ p < ∞`, the harmonic diagonal operator on `ℓ^p(ℕ, 𝕜)` has dense
range. -/
theorem denseRange_harmonicDiagonalCLM {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    DenseRange (harmonicDiagonalCLM 𝕜 p) :=
  (denseRange_diagonalCLM_iff hp (harmonicWeights 𝕜)).2 (harmonicWeights_ne_zero 𝕜)

/-- The harmonic diagonal operator on `ℓ^p(ℕ, 𝕜)` has infinite-dimensional range. -/
theorem not_finiteDimensional_range_harmonicDiagonalCLM (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ¬ FiniteDimensional 𝕜 (harmonicDiagonalCLM 𝕜 p).range := by
  rw [harmonicDiagonalCLM_eq_diagonalCLM, finiteDimensional_range_diagonalCLM_iff]
  exact infinite_univ.mono fun n _ ↦ harmonicWeights_ne_zero 𝕜 n

/-- Every positive-radius level sphere of `lp.harmonicDiagonalCLM 𝕜 p` is norm-unbounded. -/
theorem not_isBounded_setOf_norm_harmonicDiagonalCLM_eq (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {r : ℝ} (hr : 0 < r) :
    ¬ IsBounded {u : ℓ^p(ℕ, 𝕜) | ‖harmonicDiagonalCLM 𝕜 p u‖ = r} :=
  not_isBounded_setOf_norm_diagonalCLM_eq (harmonicWeights 𝕜)
    (infinite_univ.mono fun n _ ↦ harmonicWeights_ne_zero 𝕜 n)
    (Nat.cofinite_eq_atTop ▸ tendsto_norm_harmonicWeights 𝕜) hr

/-- Every level sphere of `lp.harmonicDiagonalCLM 𝕜 p` is sequentially weakly closed. -/
theorem isSeqClosed_toWeakSpace_setOf_norm_harmonicDiagonalCLM_eq (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (r : ℝ) :
    IsSeqClosed (toWeakSpace 𝕜 ℓ^p(ℕ, 𝕜) '' {u : ℓ^p(ℕ, 𝕜) | ‖harmonicDiagonalCLM 𝕜 p u‖ = r}) :=
  (isCompactOperator_harmonicDiagonalCLM 𝕜 p).isSeqClosed_toWeakSpace_setOf_norm_apply_eq r

/-- No positive-radius level sphere of `lp.harmonicDiagonalCLM 𝕜 p` is weakly closed. -/
theorem not_isClosed_toWeakSpace_setOf_norm_harmonicDiagonalCLM_eq (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {r : ℝ} (hr : 0 < r) :
    ¬ IsClosed (toWeakSpace 𝕜 ℓ^p(ℕ, 𝕜) '' {u : ℓ^p(ℕ, 𝕜) | ‖harmonicDiagonalCLM 𝕜 p u‖ = r}) :=
  mt ((harmonicDiagonalCLM 𝕜 p).isClosed_toWeakSpace_setOf_norm_apply_eq_iff hr).1
    (not_finiteDimensional_range_harmonicDiagonalCLM 𝕜 p)

/-- The harmonic diagonal operator sends `(n + 1) • lp.single p n 1` to the unit coordinate vector
`lp.single p n 1`. -/
theorem harmonicDiagonalCLM_natCast_add_one_smul_single (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℕ) :
    harmonicDiagonalCLM 𝕜 p (((n : 𝕜) + 1) • lp.single p n (1 : 𝕜)) = lp.single p n (1 : 𝕜) := by
  have hne : ((n : 𝕜) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [map_smul, harmonicDiagonalCLM_single, ← lp.single_smul, smul_eq_mul, mul_one,
    mul_inv_cancel₀ hne]

/-- The sequence `n ↦ (n + 1) • lp.single p n 1`, which lies on the unit sphere of
`lp.harmonicDiagonalCLM 𝕜 p`, has no weakly convergent subsequence. -/
theorem not_tendsto_toWeakSpace_subseq_natCast_add_one_smul_single (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (x : ℓ^p(ℕ, 𝕜)) {σ : ℕ → ℕ} (hσ : StrictMono σ) :
    ¬ Tendsto (fun n ↦ toWeakSpace 𝕜 ℓ^p(ℕ, 𝕜) ((((σ n : 𝕜) + 1) • lp.single p (σ n) (1 : 𝕜))))
        atTop (𝓝 (toWeakSpace 𝕜 ℓ^p(ℕ, 𝕜) x)) := by
  simpa only [harmonicWeights_apply, inv_inv] using
    not_tendsto_toWeakSpace_subseq_inv_smul_single (p := p) (harmonicWeights 𝕜)
      (harmonicWeights_ne_zero 𝕜) (tendsto_norm_harmonicWeights 𝕜) x hσ

end Harmonic

end lp
