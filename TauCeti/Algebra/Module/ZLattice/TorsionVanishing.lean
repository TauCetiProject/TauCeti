/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Cocompactness and torsion-point vanishing for full `ℤ`-lattices

Let `L` be a full `ℤ`-lattice (`IsZLattice ℝ L`) in a finite-dimensional real normed space `V`.
Then `L` has a compact fundamental cover (`TauCeti.ZLattice.exists_isCompact_cover`), any
continuous function `f : V → Y` into a `T₁` space with `0` that vanishes on lattices of
arbitrarily small mesh is identically zero (`TauCeti.ZLattice.eq_zero_of_small_mesh`), and in
particular any continuous function vanishing on all torsion points of `V / L` is identically zero
(`TauCeti.ZLattice.eq_zero_of_torsion_eq_zero`). Furthermore, any function on `V` factoring
through `V / L` takes finitely many values on the `n`-torsion points `{x : V | n • x ∈ L}` for
`n ≠ 0` (`TauCeti.ZLattice.finite_range_nsmul_torsion`).

## Main results

* `TauCeti.ZLattice.exists_isCompact_cover`: some compact set meets every coset of a full
  `ℤ`-lattice `L`.
* `TauCeti.ZLattice.eq_zero_of_small_mesh`: a continuous function vanishing on preimages of `L`
  under maps with arbitrarily small right inverses is zero.
* `TauCeti.ZLattice.eq_zero_of_torsion_eq_zero`: a continuous function vanishing on all torsion
  points of `V / L` is zero.
* `TauCeti.ZLattice.finite_range_nsmul_torsion`: a function factoring through `V / L` takes
  finitely many values on the `n`-torsion points for `n ≠ 0`.

## Provenance

Adapted from `New.ThetaTori.isCocompact_of_isFullRankLattice`,
`New.ThetaTori.eq_zero_of_small_mesh`, `New.ThetaTori.eq_zero_of_torsionPoints`, and
`New.ThetaTori.finite_range_nsmul_torsion` (file
`src/Lib/Shimura/GoodReduction/TorsionSizes.lean`) in grh-lean
(https://github.com/lsernau/grh-lean, commit `72fead102f663d5c7a407964a13dc0cf9d977207`,
Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

open Filter Module Set Submodule Topology ZSpan

namespace TauCeti.ZLattice

section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {L : Submodule ℤ V} [DiscreteTopology L] [IsZLattice ℝ L]

/-- A full `ℤ`-lattice `L` in a finite-dimensional real normed space is cocompact: some compact
set meets every coset of `L`. -/
theorem exists_isCompact_cover : ∃ K : Set V, IsCompact K ∧ ∀ x : V, ∃ l ∈ L, l + x ∈ K := by
  let b := (finBasis ℤ L).ofZLatticeBasis ℝ
  refine ⟨_, isCompact_closedBall 0 (∑ i, ‖b i‖), fun x ↦ ⟨-floor b x, ?_, ?_⟩⟩
  · exact ((finBasis ℤ L).ofZLatticeBasis_span ℝ).le (-floor b x).property
  · simpa [neg_add_eq_sub, ZSpan.fract_apply] using norm_fract_le b x

/-- A continuous function into a `T₁` space with `0` that vanishes on lattices of arbitrarily small
mesh is identically zero: if for continuous `ℝ`-linear maps `d` arbitrarily close to `0` there is a
left inverse `c` of `d` such that `f` vanishes on `c ⁻¹' L`, then `f = 0`. -/
theorem eq_zero_of_small_mesh {Y : Type*} [TopologicalSpace Y] [T1Space Y] [Zero Y]
    {f : V → Y} (hf : Continuous f)
    (h_small : ∃ᶠ d : V →L[ℝ] V in 𝓝 0, ∃ c : V →L[ℝ] V,
      (∀ y : V, c (d y) = y) ∧ ∀ y : V, c y ∈ L → f y = 0) :
    f = 0 := by
  obtain ⟨K, hK, h_cover⟩ := exists_isCompact_cover (L := L)
  funext z
  by_contra hz
  have h_ne : ∀ᶠ d : V →L[ℝ] V in 𝓝 0, ∀ u ∈ K, f (z - d u) ≠ 0 := by
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isClosed_singleton.isOpen_compl.preimage hf) z hz
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : V)
    have hR' : 0 < max R 1 := lt_max_of_lt_right one_pos
    filter_upwards [Metric.ball_mem_nhds (0 : V →L[ℝ] V) (div_pos hε hR')] with d hd u hu
    refine hball (Metric.mem_ball.mpr ?_)
    have hu' : ‖u‖ ≤ max R 1 := (mem_closedBall_zero_iff.mp (hR hu)).trans (le_max_left R 1)
    have hd' : ‖d‖ < ε / max R 1 := by simpa [Metric.mem_ball, dist_zero_right] using hd
    calc dist (z - d u) z = ‖d u‖ := by simp
      _ ≤ ‖d‖ * ‖u‖ := d.le_opNorm u
      _ ≤ ‖d‖ * max R 1 := mul_le_mul_of_nonneg_left hu' (norm_nonneg d)
      _ < (ε / max R 1) * max R 1 := mul_lt_mul_of_pos_right hd' hR'
      _ = ε := div_mul_cancel₀ ε hR'.ne'
  refine h_small (h_ne.mono fun d hd ⟨c, hcd, h_zero⟩ ↦ ?_)
  obtain ⟨l, hl, hu⟩ := h_cover (c z)
  exact hd _ hu (h_zero _ (by simpa [hcd] using hl))

/-- A continuous function into a `T₁` space with `0` that vanishes at all torsion points of `V / L`
(vectors `x` with `n • x ∈ L` for some `n ≠ 0`) is identically zero. -/
theorem eq_zero_of_torsion_eq_zero {Y : Type*} [TopologicalSpace Y] [T1Space Y] [Zero Y]
    {f : V → Y} (hf : Continuous f)
    (h_zero : ∀ x : V, (∃ n : ℕ, n ≠ 0 ∧ n • x ∈ L) → f x = 0) :
    f = 0 := by
  have h_mesh : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ • (1 : V →L[ℝ] V)) atTop (𝓝 0) :=
    ((continuous_id.smul continuous_const).tendsto' 0 0 (zero_smul ℝ _)).comp
      tendsto_inv_atTop_nhds_zero_nat
  have h_small : ∃ᶠ d : V →L[ℝ] V in 𝓝 0, ∃ c : V →L[ℝ] V,
      (∀ y : V, c (d y) = y) ∧ ∀ y : V, c y ∈ L → f y = 0 := by
    refine h_mesh.frequently ((eventually_ne_atTop 0).frequently.mono fun n hn ↦ ?_)
    refine ⟨n • (1 : V →L[ℝ] V), fun y ↦ ?_, fun y hy ↦ h_zero y ⟨n, hn, by simpa using hy⟩⟩
    simp [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hn]
  exact eq_zero_of_small_mesh (L := L) hf h_small

end

/-- A function `p : V → α` on a real vector space that factors through the quotient `V / L` by a
finitely generated `ℤ`-submodule `L` takes finitely many values on the `n`-torsion points
`{x : V | n • x ∈ L}` for any `n ≠ 0`. -/
theorem finite_range_nsmul_torsion {V α : Type*} [AddCommGroup V] [Module ℝ V]
    {L : Submodule ℤ V} [Module.Finite ℤ L] {p : V → α} {n : ℕ} (hn : n ≠ 0)
    (hp : p.FactorsThrough L.mkQ) :
    (p '' {x : V | n • x ∈ L}).Finite := by
  let M : Submodule ℤ (V ⧸ L) := L.map (L.mkQ ∘ₗ ((n⁻¹ : ℝ) • (1 : V →ₗ[ℝ] V)).restrictScalars ℤ)
  have hM : (M : Set (V ⧸ L)).Finite := finite_of_fg_torsion M fun ⟨_, l, hl, rfl⟩ ↦
    ⟨⟨n, by simpa using hn⟩, by
      simpa [← Submodule.Quotient.mk_smul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hn] using hl⟩
  refine (hM.image (Function.extend L.mkQ p (fun _ ↦ p 0))).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨L.mkQ x, ⟨n • x, hx, ?_⟩, hp.extend_apply _ _⟩
  simp [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hn]

end TauCeti.ZLattice
