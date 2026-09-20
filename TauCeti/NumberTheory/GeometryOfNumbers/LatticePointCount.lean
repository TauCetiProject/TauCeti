/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import TauCeti.Algebra.Module.ZLattice.Basic
public import TauCeti.NumberTheory.GeometryOfNumbers.BoundaryCount
public import TauCeti.Topology.MetricSpace.DiscreteAddSubgroup
import TauCeti.Topology.Frontier

/-!
# Counting the lattice points of a dilated body, with a boundary-order error

Let `L` be a `ℤ`-lattice in an `n`-dimensional real normed space `E`, let `μ` be an additive Haar
measure on `E`, and let `D` be a bounded set whose frontier is Lipschitz parametrizable in
dimension `n - 1`.  When `0 < n`, the resulting error is power-saving. Dilating `D` by `c`
multiplies its volume by `c ^ n`, and each point of `L` in `c • D` accounts for one cell of the
lattice, of volume `covolume L μ`.  So

```text
#(c • D ∩ L) = μ D / covolume L μ * c ^ n + O(c ^ (n - 1)) as c → ∞.
```

Mathlib's `ZLattice.covolume.tendsto_card_div_pow'` assumes only that the frontier of the body is
null, which gives the limit but no error term at all.  An error term is what a counting argument
needs when the count is one term of a larger asymptotic, and it is what the stronger frontier
hypothesis buys.

## The argument

Fix a fundamental domain `F` for `L`, and call `w + F` the *cell* at a lattice point `w`.  The
cells tile `E`, so the volume of a set `X` is squeezed between the total volume of the cells
contained in `X` and the total volume of the cells meeting `X`, that is, between `#A * μ F` and
`#B * μ F` where

```text
A = {w ∈ L | w + F ⊆ X},   B = {w ∈ L | (w + F) ∩ X ≠ ∅}.
```

Since `0 ∈ F`, a lattice point lies in its own cell, so `A ⊆ X ∩ L ⊆ B` and the count `#(X ∩ L)`
is squeezed between the same two numbers.  Both quantities therefore differ by at most `#(B \ A)`
cells.  A cell counted by `B` and not by `A` meets `X` and its complement; being convex it is
preconnected, so it meets `frontier X` (`IsPreconnected.inter_frontier_nonempty`).  Hence
`B \ A` embeds in the lattice points of the thickened frontier `frontier X + -F`.  That is
`abs_ncard_inter_mul_sub_measureReal_le`, and it holds for any bounded `X`, with no regularity
hypothesis on the frontier: the boundary term is not yet estimated, only identified.

Taking `X = c • D` and `F` the fundamental domain of a basis of `L`, the thickened frontier is
`c • frontier D + -F`, whose lattice points number `O(c ^ (n - 1))` by the boundary count
`TauCeti.IsLipschitzParametrizable.exists_ncard_smul_add_inter_le`.  This is the only place the
Lipschitz hypothesis is used, and the only source of the error term.

## Main results

* `TauCeti.abs_ncard_inter_mul_sub_measureReal_le`: for any bounded set `X`, the count of lattice
  points of `X` times the volume of a fundamental domain `F` differs from the volume of `X` by at
  most the volume of `F` times the number of lattice points of `frontier X + -F`.
* `TauCeti.exists_abs_ncard_smul_inter_sub_le`: the explicit bound
  `|#(c • D ∩ L) - μ D / covolume L μ * c ^ n| ≤ A * c ^ (n - 1)` for `c ≥ 1`, with `A`
  independent of `c`.
* `TauCeti.isBigO_ncard_smul_inter_sub`: the same bound as an asymptotic statement.
## References

* S. Lang, *Algebraic Number Theory*, Chapter VI, Section 2.
-/

public section

open Asymptotics Bornology Filter MeasureTheory Module Set Submodule
open scoped ENNReal Pointwise Topology

namespace TauCeti

section Cells

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

/-- A translate of a set has the same measure. -/
private theorem measure_sub_mem (μ : Measure E) [μ.IsAddRightInvariant] (w : E) (F : Set E) :
    μ {y : E | y - w ∈ F} = μ F := by
  have : {y : E | y - w ∈ F} = (fun y : E ↦ y + -w) ⁻¹' F := by
    ext y; simp [sub_eq_add_neg]
  rw [this, measure_preimage_add_right]

/-- The translates of `F` by finitely many pairwise distinct lattice points have total measure
the number of them times the measure of `F`. -/
private theorem measure_biUnion_sub_mem (μ : Measure E) [μ.IsAddRightInvariant]
    {G : Set E} {F : Set E} (hFm : MeasurableSet F)
    (hdisj : ∀ w₁ ∈ G, ∀ w₂ ∈ G, w₁ ≠ w₂ →
      Disjoint {y : E | y - w₁ ∈ F} {y : E | y - w₂ ∈ F})
    {T : Finset E} (hT : ↑T ⊆ G) :
    μ (⋃ w ∈ T, {y : E | y - w ∈ F}) = T.card * μ F := by
  rw [measure_biUnion_finset (fun w₁ h₁ w₂ h₂ h ↦ hdisj w₁ (hT h₁) w₂ (hT h₂) h)
    fun w _ ↦ measurableSet_preimage (measurable_id.sub_const w) hFm]
  simp [measure_sub_mem]

end Cells


section Counting

variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
  [MeasurableSpace E] [BorelSpace E] {L : Submodule ℤ E} [DiscreteTopology L]
  {μ : Measure E} [μ.IsAddRightInvariant] [IsLocallyFiniteMeasure μ] {F X : Set E}

/-- **Counting lattice points by cells.**  Let `F` be a bounded measurable preconnected set
containing `0` whose lattice translates `w + F`, for `w` in a discrete `L`, tile `E`.  Then for
every bounded set `X` the number of lattice points of `X`, weighted by the volume of `F`, differs
from the volume of `X` by at most the volume of `F` times the number of lattice points in the
thickened frontier `frontier X + -F`.

The hypotheses on `F` say exactly that it is a fundamental domain of the shape a counting argument
uses: `hFu` and `hFe` are uniqueness and existence of the cell containing a point, `hF₀` puts a
lattice point in its own cell, and preconnectedness is what makes a cell straddling `X` meet its
frontier.  No regularity is asked of `X`, and none of `frontier X`: the boundary term is
identified here and estimated by the caller. -/
theorem abs_ncard_inter_mul_sub_measureReal_le
    (hF₀ : (0 : E) ∈ F) (hFpc : IsPreconnected F) (hFb : IsBounded F) (hFm : MeasurableSet F)
    (hFu : ∀ x : E, ∀ w₁ ∈ (L : Set E), ∀ w₂ ∈ (L : Set E), x - w₁ ∈ F → x - w₂ ∈ F → w₁ = w₂)
    (hFe : ∀ x : E, ∃ w ∈ (L : Set E), x - w ∈ F)
    (hXb : IsBounded X) :
    |((X ∩ (L : Set E)).ncard : ℝ) * μ.real F - μ.real X| ≤
      (((frontier X + -F) ∩ (L : Set E)).ncard : ℝ) * μ.real F := by
  classical
  set A : Set E := {w | w ∈ (L : Set E) ∧ {y : E | y - w ∈ F} ⊆ X}
  set B : Set E := {w | w ∈ (L : Set E) ∧ ({y : E | y - w ∈ F} ∩ X).Nonempty}
  have hself : ∀ w : E, w ∈ {y : E | y - w ∈ F} := fun w ↦ by simpa using hF₀
  have hdisj : ∀ w₁ ∈ (L : Set E), ∀ w₂ ∈ (L : Set E), w₁ ≠ w₂ →
      Disjoint {y : E | y - w₁ ∈ F} {y : E | y - w₂ ∈ F} := fun w₁ h₁ w₂ h₂ hne ↦
    Set.disjoint_left.mpr fun y hy₁ hy₂ ↦ hne (hFu y w₁ h₁ w₂ h₂ hy₁ hy₂)
  have hBsub : B ⊆ (X + -F) ∩ (L : Set E) := by
    rintro w ⟨hwL, y, hyF, hyX⟩
    exact ⟨⟨y, hyX, -(y - w), by simpa using hyF, by simp⟩, hwL⟩
  have hBfin : B.Finite :=
    (L.toAddSubgroup.finite_inter (isBounded_add hXb hFb.neg)).subset hBsub
  have hAB : A ⊆ B := fun w hw ↦ ⟨hw.1, ⟨w, hself w, hw.2 (hself w)⟩⟩
  have hAfin : A.Finite := hBfin.subset hAB
  -- the cells of `A` lie in `X`, and the cells of `B` cover `X`
  have hAmeas : μ (⋃ w ∈ hAfin.toFinset, {y : E | y - w ∈ F}) = A.ncard * μ F := by
    rw [measure_biUnion_sub_mem μ hFm hdisj
        (fun w hw ↦ (hAfin.mem_toFinset.mp hw).1), Set.ncard_eq_toFinset_card _ hAfin]
  have hBmeas : μ (⋃ w ∈ hBfin.toFinset, {y : E | y - w ∈ F}) = B.ncard * μ F := by
    rw [measure_biUnion_sub_mem μ hFm hdisj
        (fun w hw ↦ (hBfin.mem_toFinset.mp hw).1), Set.ncard_eq_toFinset_card _ hBfin]
  have hlow : (A.ncard : ℝ≥0∞) * μ F ≤ μ X := by
    rw [← hAmeas]
    exact measure_mono (Set.iUnion₂_subset fun w hw ↦ (hAfin.mem_toFinset.mp hw).2)
  have hup : μ X ≤ (B.ncard : ℝ≥0∞) * μ F := by
    rw [← hBmeas]
    refine measure_mono fun x hx ↦ ?_
    obtain ⟨w, hwL, hwF⟩ := hFe x
    exact Set.mem_iUnion₂.mpr ⟨w, hBfin.mem_toFinset.mpr ⟨hwL, ⟨x, hwF, hx⟩⟩, hwF⟩
  -- a cell straddling `X` meets its frontier, so it is counted by the boundary term
  have hbadfin : ((frontier X + -F) ∩ (L : Set E)).Finite :=
    L.toAddSubgroup.finite_inter
      (isBounded_add (hXb.closure.subset frontier_subset_closure) hFb.neg)
  have hBA : B \ A ⊆ (frontier X + -F) ∩ (L : Set E) := by
    rintro w ⟨⟨hwL, hmeet⟩, hnA⟩
    obtain ⟨z, hzc, hzX⟩ := Set.not_subset.mp fun h ↦ hnA ⟨hwL, h⟩
    obtain ⟨y, hyc, hyfr⟩ :=
      ((Homeomorph.subRight w).isPreconnected_preimage.mpr hFpc).inter_frontier_nonempty
        hmeet ⟨z, hzc, hzX⟩
    exact ⟨⟨y, hyfr, -(y - w), by simpa using hyc, by simp⟩, hwL⟩
  -- assemble: the count is squeezed between the two cell counts, as is the measure
  have hAX : A ⊆ X ∩ (L : Set E) := fun w hw ↦ ⟨hw.2 (hself w), hw.1⟩
  have hXB : X ∩ (L : Set E) ⊆ B := fun w hw ↦ ⟨hw.2, ⟨w, hself w, hw.1⟩⟩
  have hκ : (0 : ℝ) ≤ μ.real F := ENNReal.toReal_nonneg
  have h1 : (A.ncard : ℝ) * μ.real F ≤ μ.real X := by
    have h := ENNReal.toReal_mono hXb.measure_lt_top.ne hlow
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h
  have h2 : μ.real X ≤ (B.ncard : ℝ) * μ.real F := by
    have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hFb.measure_lt_top.ne) hup
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h
  have h3 : (A.ncard : ℝ) ≤ ((X ∩ (L : Set E)).ncard : ℝ) :=
    Nat.cast_le.mpr (Set.ncard_le_ncard hAX (L.toAddSubgroup.finite_inter hXb))
  have h4 : ((X ∩ (L : Set E)).ncard : ℝ) ≤ (B.ncard : ℝ) :=
    Nat.cast_le.mpr (Set.ncard_le_ncard hXB hBfin)
  have h5 : (B.ncard : ℝ) - A.ncard ≤ (((frontier X + -F) ∩ (L : Set E)).ncard : ℝ) := by
    have hle := Set.ncard_le_ncard hBA hbadfin
    rw [Set.ncard_sdiff hAB hAfin] at hle
    have hAle : A.ncard ≤ B.ncard := Set.ncard_le_ncard hAB hBfin
    rw [← Nat.cast_le (α := ℝ), Nat.cast_sub hAle] at hle
    linarith
  have e1 := mul_le_mul_of_nonneg_right h4 hκ
  have e2 := mul_le_mul_of_nonneg_right h3 hκ
  have e3 := mul_le_mul_of_nonneg_right h5 hκ
  rw [sub_mul] at e3
  rw [abs_le]
  constructor <;> linarith

end Counting

section Lattice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **Lattice points in a dilated body, with a boundary-order error.**  For a bounded set `D` whose
frontier is Lipschitz parametrizable in dimension `n - 1`, with `n = finrank ℝ E`, the number of
lattice points of `c • D` is `μ D / covolume L μ * c ^ n` up to `A * c ^ (n - 1)`, with `A`
independent of `c ≥ 1`.

The main term is the volume of `c • D` divided by the covolume of the lattice.  The error is the
number of lattice cells meeting the frontier of the dilate, so its order is governed by the
parametrization dimension of `frontier D` alone. When `0 < n`, this is power-saving relative to
the order `c ^ n` main term; the theorem itself also covers zero-dimensional spaces. -/
theorem exists_abs_ncard_smul_inter_sub_le {D : Set E} (hDb : IsBounded D)
    (hDfr : IsLipschitzParametrizable (finrank ℝ E - 1) (frontier D)) :
    ∃ A ≥ (0 : ℝ), ∀ c : ℝ, 1 ≤ c →
      |(((c • D) ∩ (L : Set E)).ncard : ℝ) -
          μ.real D / ZLattice.covolume L μ * c ^ finrank ℝ E| ≤ A * c ^ (finrank ℝ E - 1) := by
  classical
  set b := Module.Free.chooseBasis ℤ L
  set β := b.ofZLatticeBasis ℝ L
  set F := ZSpan.fundamentalDomain β with hFdef
  have hmem : ∀ w : E, w ∈ (L : Set E) ↔ w ∈ span ℤ (Set.range β) := fun w ↦ by
    rw [b.ofZLatticeBasis_span ℝ]; exact Iff.rfl
  have hFb : IsBounded F := ZSpan.fundamentalDomain_isBounded β
  have hFm : MeasurableSet F := ZSpan.fundamentalDomain_measurableSet β
  have hF₀ : (0 : E) ∈ F := by rw [hFdef]; simp [ZSpan.mem_fundamentalDomain]
  have hFpc : IsPreconnected F := (ZSpan.convex_fundamentalDomain β).isPreconnected
  have hcov : ZLattice.covolume L μ = μ.real F :=
    ZLattice.covolume_eq_measure_fundamentalDomain L μ (ZLattice.isAddFundamentalDomain b μ)
  have hκ : 0 < μ.real F := hcov ▸ ZLattice.covolume_pos L μ
  have hFu : ∀ x : E, ∀ w₁ ∈ (L : Set E), ∀ w₂ ∈ (L : Set E),
      x - w₁ ∈ F → x - w₂ ∈ F → w₁ = w₂ := fun x w₁ h₁ w₂ h₂ k₁ k₂ ↦ by
    have hw₁ : -w₁ ∈ span ℤ (Set.range β) := neg_mem ((hmem w₁).mp h₁)
    have hw₂ : -w₂ ∈ span ℤ (Set.range β) := neg_mem ((hmem w₂).mp h₂)
    have subtype_vadd (w : E) (hw : w ∈ span ℤ (Set.range β)) :
        (⟨w, hw⟩ : span ℤ (Set.range β)) +ᵥ x = w + x := rfl
    have heq : (⟨-w₁, hw₁⟩ : span ℤ (Set.range β)) = ⟨-w₂, hw₂⟩ :=
      (ZSpan.exist_unique_vadd_mem_fundamentalDomain β x).unique
        (by
          rw [subtype_vadd]
          simpa only [hFdef, sub_eq_add_neg, add_comm] using k₁)
        (by
          rw [subtype_vadd]
          simpa only [hFdef, sub_eq_add_neg, add_comm] using k₂)
    exact neg_injective (congrArg Subtype.val heq)
  have hFe : ∀ x : E, ∃ w ∈ (L : Set E), x - w ∈ F := fun x ↦
    ⟨(ZSpan.floor β x : E), (hmem _).mpr (ZSpan.floor β x).2,
      ZSpan.fract_mem_fundamentalDomain β x⟩
  obtain ⟨A, hA0, hA⟩ := hDfr.exists_ncard_smul_add_inter_le L.toAddSubgroup hFb.neg
  refine ⟨A, hA0, fun c hc ↦ ?_⟩
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le one_pos hc
  have hfr : frontier (c • D) = c • frontier D := by
    have h := (isHomeomorph_smul₀ (α := E) hc0.ne').image_frontier D
    simpa [Set.image_smul] using h.symm
  have hvol : μ.real (c • D) = c ^ finrank ℝ E * μ.real D := by
    rw [measureReal_def, Measure.addHaar_smul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (abs_nonneg _), abs_of_nonneg (by positivity), measureReal_def]
  have hkey := abs_ncard_inter_mul_sub_measureReal_le (μ := μ) (L := L) hF₀ hFpc hFb hFm hFu hFe
    (hDb.smul₀ c)
  rw [hfr, hvol] at hkey
  have hbad : (((c • frontier D + -F) ∩ (L : Set E)).ncard : ℝ) ≤ A * c ^ (finrank ℝ E - 1) :=
    hA c hc
  rw [hcov]
  refine le_trans (le_of_mul_le_mul_right ?_ hκ) hbad
  refine le_trans (le_of_eq ?_) hkey
  have hrw : (((c • D) ∩ (L : Set E)).ncard : ℝ) - μ.real D / μ.real F * c ^ finrank ℝ E =
      ((((c • D) ∩ (L : Set E)).ncard : ℝ) * μ.real F - c ^ finrank ℝ E * μ.real D) /
        μ.real F := by
    field_simp
  rw [hrw, abs_div, abs_of_pos hκ, div_mul_cancel₀ _ hκ.ne']

/-- **Lattice points in a dilated body**, as an asymptotic statement: the count of the lattice
points of `c • D` differs from `μ D / covolume L μ * c ^ n` by `O(c ^ (n - 1))` as `c → ∞`. -/
theorem isBigO_ncard_smul_inter_sub {D : Set E} (hDb : IsBounded D)
    (hDfr : IsLipschitzParametrizable (finrank ℝ E - 1) (frontier D)) :
    (fun c : ℝ ↦ (((c • D) ∩ (L : Set E)).ncard : ℝ) -
        μ.real D / ZLattice.covolume L μ * c ^ finrank ℝ E) =O[atTop]
      fun c : ℝ ↦ c ^ (finrank ℝ E - 1) := by
  obtain ⟨A, -, hA⟩ := exists_abs_ncard_smul_inter_sub_le (μ := μ) (L := L) hDb hDfr
  refine isBigO_iff.2 ⟨A, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with c hc
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ c) _)]
  exact hA c hc

end Lattice

end TauCeti
