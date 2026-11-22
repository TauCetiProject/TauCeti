/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.MeasureTheory.Group.GeometryOfNumbers

/-!
# Minkowski's convex body theorem for lattices

Mathlib states Minkowski's convex body theorem for an arbitrary discrete subgroup with a
fundamental domain. This file packages it for full `ℤ`-lattices in terms of `ZLattice.covolume`
and records the standard coordinate instance for the integer lattice `ℤ^η` in `η → ℝ` with Lebesgue
measure.

## Main results

* `MeasureTheory.exists_ne_zero_int_vec_mem_of_two_pow_le_volume`: a compact convex symmetric
  set `s ⊆ η → ℝ` of volume at least `2 ^ |η|` contains a nonzero integer vector.
* `ZLattice.measure_fundamentalDomain_chooseBasis`: identifies the `μ`-measure of the chosen
  basis fundamental domain of `L` with `ENNReal.ofReal (ZLattice.covolume L μ)`.
* `ZLattice.exists_ne_zero_mem_of_covolume_mul_two_pow_le`: a compact convex symmetric set `s` in a
  nontrivial finite-dimensional real normed space `E` with `covolume L μ * 2 ^ finrank ℝ E ≤ μ s`
  contains a nonzero vector of the full lattice `L`.
-/

public section

open Module

namespace ZLattice

open MeasureTheory

/-- The `μ`-measure of the fundamental domain of `Free.chooseBasis ℤ L` equals
`ENNReal.ofReal (ZLattice.covolume L μ)`. -/
theorem measure_fundamentalDomain_chooseBasis
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (μ : Measure E := by volume_tac) [μ.IsAddHaarMeasure] :
    μ (ZSpan.fundamentalDomain ((Free.chooseBasis ℤ L).ofZLatticeBasis ℝ)) =
      ENNReal.ofReal (ZLattice.covolume L μ) := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain L μ
      (ZLattice.isAddFundamentalDomain (Free.chooseBasis ℤ L) μ),
    ofReal_measureReal (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne]

/-- **Minkowski's convex body theorem for a full lattice.** Let `L` be a full `ℤ`-lattice in a
nontrivial finite-dimensional real normed space `E` with Haar measure `μ`. Every compact convex
symmetric set `s ⊆ E` with `covolume L μ * 2 ^ finrank ℝ E ≤ μ s` contains a nonzero vector of
`L`. -/
theorem exists_ne_zero_mem_of_covolume_mul_two_pow_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
    [MeasurableSpace E] [BorelSpace E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (μ : Measure E := by volume_tac) [μ.IsAddHaarMeasure]
    {s : Set E} (h_symm : ∀ x ∈ s, -x ∈ s) (h_conv : Convex ℝ s) (h_cpt : IsCompact s)
    (h : ENNReal.ofReal (ZLattice.covolume L μ) * 2 ^ finrank ℝ E ≤ μ s) :
    ∃ x ∈ L, x ≠ 0 ∧ x ∈ s := by
  have hfund := ZLattice.isAddFundamentalDomain (Free.chooseBasis ℤ L) μ
  have : Countable L.toAddSubgroup := (inferInstance : Countable L)
  have : DiscreteTopology L.toAddSubgroup := (inferInstance : DiscreteTopology L)
  have hvol :
      μ (ZSpan.fundamentalDomain ((Free.chooseBasis ℤ L).ofZLatticeBasis ℝ)) *
          2 ^ finrank ℝ E ≤
        μ s := by
    rwa [ZLattice.measure_fundamentalDomain_chooseBasis L μ]
  obtain ⟨⟨x, hxL⟩, hx0, hxs⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure (L := L.toAddSubgroup)
      hfund h_symm h_conv h_cpt hvol
  exact ⟨x, (Submodule.mem_toAddSubgroup L).mp hxL, fun h0 ↦ hx0 (Subtype.ext h0), hxs⟩

end ZLattice

namespace MeasureTheory

/-- **Minkowski's convex body theorem for the integer lattice.** A compact convex set
`s ⊆ η → ℝ`, symmetric about the origin, of volume at least `2 ^ |η|` contains a nonzero integer
vector. -/
theorem exists_ne_zero_int_vec_mem_of_two_pow_le_volume {η : Type*} [Fintype η] [Nonempty η]
    {s : Set (η → ℝ)} (h_symm : ∀ x ∈ s, -x ∈ s) (h_conv : Convex ℝ s) (h_cpt : IsCompact s)
    (h : 2 ^ Fintype.card η ≤ volume s) :
    ∃ z : η → ℤ, z ≠ 0 ∧ (fun k ↦ (z k : ℝ)) ∈ s := by
  set b := Pi.basisFun ℝ η
  set L : Submodule ℤ (η → ℝ) := Submodule.span ℤ (Set.range b)
  have : DiscreteTopology L := inferInstance
  have hcov : ZLattice.covolume L volume = 1 := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain L volume
        (ZSpan.isAddFundamentalDomain' b volume),
      measureReal_def, ZSpan.fundamentalDomain_pi_basisFun, Real.volume_pi_Ico]
    simp
  have hvol : ENNReal.ofReal (ZLattice.covolume L volume) * 2 ^ finrank ℝ (η → ℝ) ≤ volume s := by
    rwa [hcov, ENNReal.ofReal_one, one_mul, finrank_fintype_fun_eq_card]
  obtain ⟨v, hv, hv0, hvs⟩ :=
    ZLattice.exists_ne_zero_mem_of_covolume_mul_two_pow_le L volume h_symm h_conv h_cpt hvol
  choose z hz using fun k ↦ by simpa [b] using (b.mem_span_iff_repr_mem ℤ v).1 hv k
  have hvz : v = fun k ↦ (z k : ℝ) := funext fun k ↦ (hz k).symm
  subst hvz
  exact ⟨z, fun h0 ↦ hv0 (funext fun k ↦ by simp [h0]), hvs⟩

end MeasureTheory
