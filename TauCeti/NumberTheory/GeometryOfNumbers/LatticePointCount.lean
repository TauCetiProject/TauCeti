/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import TauCeti.Algebra.Module.ZLattice.Basic
public import TauCeti.MeasureTheory.Group.Measure
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
* `TauCeti.exists_abs_ncard_smul_inter_vadd_sub_le`: for `c ≥ 1` and *any* coset `ξ +ᵥ L`,
  `|#(c • D ∩ (ξ +ᵥ L)) - μ D / covolume L μ * c ^ n| ≤ A * c ^ (n - 1)`, with `A` independent of
  `c` **and** of `ξ`.
* `TauCeti.isBigO_ncard_smul_inter_sub`: that bound at `ξ = 0`, as an asymptotic statement.
## References

* S. Lang, *Algebraic Number Theory*, Chapter VI, Section 2.
* The coset-uniform count follows C. Birkbeck and R. Brasca,
  [*AINTLIB*](https://github.com/CBirkbeck/AINTLIB) at commit
  `db14b34cc5e3d79603e67c205dfa86b7b989000c` (Apache-2.0),
  `projects/Chebotarev/CebotarevDensity/ForMathlib/IdealCongruenceCount.lean`, theorem
  `exists_card_coset_inter_smul_sub_volume_mul_rpow_le`: the same statement, and the same
  reduction of the translate into a fundamental domain.
-/

public section

open Asymptotics Bornology Filter MeasureTheory Module Set Submodule
open scoped ENNReal Pointwise Topology

namespace TauCeti

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
    rw [Measure.measure_biUnion_sub_mem μ hFm hdisj
        (fun w hw ↦ (hAfin.mem_toFinset.mp hw).1), Set.ncard_eq_toFinset_card _ hAfin]
  have hBmeas : μ (⋃ w ∈ hBfin.toFinset, {y : E | y - w ∈ F}) = B.ncard * μ F := by
    rw [Measure.measure_biUnion_sub_mem μ hFm hdisj
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

private theorem abs_ncard_smul_inter_vadd_sub_le_aux {D F : Set E} {ξ : E} {c : ℝ}
    (hDb : IsBounded D) (hc : 1 ≤ c) (hF₀ : (0 : E) ∈ F) (hFpc : IsPreconnected F)
    (hFb : IsBounded F) (hFm : MeasurableSet F) (hcov : ZLattice.covolume L μ = μ.real F)
    (hFu : ∀ x : E, ∀ w₁ ∈ (L : Set E), ∀ w₂ ∈ (L : Set E), x - w₁ ∈ F → x - w₂ ∈ F → w₁ = w₂)
    (hFe : ∀ x : E, ∃ w ∈ (L : Set E), x - w ∈ F) :
    |(((c • D) ∩ (ξ +ᵥ (L : Set E))).ncard : ℝ) -
        μ.real D / ZLattice.covolume L μ * c ^ finrank ℝ E| ≤
      (((c • frontier D + (F + -F)) ∩ (L : Set E)).ncard : ℝ) := by
  have hκ : 0 < μ.real F := hcov ▸ ZLattice.covolume_pos L μ
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le one_pos hc
  -- The count only depends on `ξ` modulo `L`, so reduce the representative into `F`: the slack
  -- the boundary estimate must absorb is then `F + -F`, not a set depending on `ξ`.
  obtain ⟨w, hwL, hvF⟩ := hFe (-ξ)
  have hvξ : -ξ - w + ξ = -w := by abel
  set v : E := -ξ - w
  -- translating by `v` carries the coset onto `L`, turning the count into a lattice-point count
  rw [hcov, ← Set.ncard_vadd_set v ((c • D) ∩ (ξ +ᵥ (L : Set E))), vadd_set_inter, vadd_vadd,
    hvξ, vadd_coe_set (L.neg_mem hwL)]
  have hvol : μ.real (v +ᵥ c • D) = c ^ finrank ℝ E * μ.real D := by
    rw [measureReal_def, measure_vadd, Measure.addHaar_smul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (abs_nonneg _), abs_of_nonneg (by positivity), measureReal_def]
  have hkey := abs_ncard_inter_mul_sub_measureReal_le (μ := μ) (L := L) hF₀ hFpc hFb hFm hFu hFe
    ((hDb.smul₀ c).vadd v)
  rw [hvol] at hkey
  have hfr : frontier (c • D) = c • frontier D := by
    have h := (isHomeomorph_smul₀ (α := E) hc0.ne').image_frontier D
    simpa [Set.image_smul] using h.symm
  have hfrv : frontier (v +ᵥ c • D) = v +ᵥ c • frontier D := by
    rw [← hfr]
    exact (IsHomeomorph.image_frontier (Homeomorph.addLeft v).isHomeomorph (c • D)).symm
  -- a cell meeting the frontier of the translate is counted by the fixed thickened frontier
  have hsub : frontier (v +ᵥ c • D) + -F ⊆ c • frontier D + (F + -F) := by
    rw [hfrv]
    rintro _ ⟨_, ⟨y, hy, rfl⟩, z, hz, rfl⟩
    exact ⟨y, hy, v + z, ⟨v, hvF, z, hz, rfl⟩, by simp [vadd_eq_add, add_comm, add_left_comm]⟩
  have hbadfin : ((c • frontier D + (F + -F)) ∩ (L : Set E)).Finite :=
    L.toAddSubgroup.finite_inter
      (isBounded_add ((hDb.closure.subset frontier_subset_closure).smul₀ c)
        (isBounded_add hFb hFb.neg))
  have hrw : (((v +ᵥ c • D) ∩ (L : Set E)).ncard : ℝ) -
      μ.real D / μ.real F * c ^ finrank ℝ E =
      ((((v +ᵥ c • D) ∩ (L : Set E)).ncard : ℝ) * μ.real F - c ^ finrank ℝ E * μ.real D) /
        μ.real F := by
    field_simp
  refine le_of_mul_le_mul_right (le_trans (le_of_eq ?_) (hkey.trans ?_)) hκ
  · rw [hrw, abs_div, abs_of_pos hκ, div_mul_cancel₀ _ hκ.ne']
  · gcongr

/-- **Lattice points of a coset in a dilated body, uniformly in the coset.** For a bounded set `D`
whose frontier is Lipschitz parametrizable in dimension `n - 1`, the number of points of *any*
coset `ξ +ᵥ L` lying in `c • D` is `μ D / covolume L μ * c ^ n` up to `A * c ^ (n - 1)`, with `A`
independent of both `c ≥ 1` **and** the translate `ξ`.

Uniformity in `ξ` is the point, and it is not formal: the error is governed by the lattice cells
meeting the boundary of the translated body, while a translate ranges over all of `E`, which is
unbounded.

This is what lets a count be run over each coset of a sublattice with a single implied constant,
as a count of ideals in a fixed ray class requires. -/
theorem exists_abs_ncard_smul_inter_vadd_sub_le {D : Set E} (hDb : IsBounded D)
    (hDfr : IsLipschitzParametrizable (finrank ℝ E - 1) (frontier D)) :
    ∃ A ≥ (0 : ℝ), ∀ (ξ : E) (c : ℝ), 1 ≤ c →
      |(((c • D) ∩ (ξ +ᵥ (L : Set E))).ncard : ℝ) -
          μ.real D / ZLattice.covolume L μ * c ^ finrank ℝ E| ≤ A * c ^ (finrank ℝ E - 1) := by
  classical
  -- A fundamental domain for `L`, with the properties the estimate below consumes. Tiling is
  -- taken in subtraction form, which is the idiom the count uses.
  set b := Module.Free.chooseBasis ℤ L with hb
  set β := b.ofZLatticeBasis ℝ L with hβ
  set F := ZSpan.fundamentalDomain β with hF
  have hmem : ∀ w : E, w ∈ (L : Set E) ↔ w ∈ Submodule.span ℤ (Set.range β) := fun w ↦ by
    rw [hβ, b.ofZLatticeBasis_span ℝ]
    exact Iff.rfl
  have hF₀ : (0 : E) ∈ F := by simp [hF, ZSpan.mem_fundamentalDomain]
  have hFpc : IsPreconnected F := (ZSpan.convex_fundamentalDomain β).isPreconnected
  have hFb : IsBounded F := ZSpan.fundamentalDomain_isBounded β
  have hFm : MeasurableSet F := ZSpan.fundamentalDomain_measurableSet β
  have hFu : ∀ x : E, ∀ w₁ ∈ (L : Set E), ∀ w₂ ∈ (L : Set E), x - w₁ ∈ F → x - w₂ ∈ F →
      w₁ = w₂ := fun _ w₁ h₁ w₂ h₂ k₁ k₂ ↦
    ZSpan.eq_of_sub_mem_fundamentalDomain β ((hmem w₁).mp h₁) ((hmem w₂).mp h₂) k₁ k₂
  have hFe : ∀ x : E, ∃ w ∈ (L : Set E), x - w ∈ F := fun x ↦
    ⟨(ZSpan.floor β x : E), (hmem _).mpr (ZSpan.floor β x).2,
      ZSpan.fract_mem_fundamentalDomain β x⟩
  have hcov : ZLattice.covolume L μ = μ.real F :=
    ZLattice.covolume_eq_measure_fundamentalDomain L μ (ZLattice.isAddFundamentalDomain b μ)
  -- The slack `F + -F` is one fixed bounded set, and is what makes `A` independent of `ξ`.
  obtain ⟨A, hA0, hA⟩ := hDfr.exists_ncard_smul_add_inter_le L.toAddSubgroup
    (isBounded_add hFb hFb.neg)
  exact ⟨A, hA0, fun ξ c hc ↦
    (abs_ncard_smul_inter_vadd_sub_le_aux hDb hc hF₀ hFpc hFb hFm hcov hFu hFe).trans (hA c hc)⟩


/-- **Lattice points in a dilated body**, as an asymptotic statement: the count of the lattice
points of `c • D` differs from `μ D / covolume L μ * c ^ n` by `O(c ^ (n - 1))` as `c → ∞`. -/
theorem isBigO_ncard_smul_inter_sub {D : Set E} (hDb : IsBounded D)
    (hDfr : IsLipschitzParametrizable (finrank ℝ E - 1) (frontier D)) :
    (fun c : ℝ ↦ (((c • D) ∩ (L : Set E)).ncard : ℝ) -
        μ.real D / ZLattice.covolume L μ * c ^ finrank ℝ E) =O[atTop]
      fun c : ℝ ↦ c ^ (finrank ℝ E - 1) := by
  -- the coset estimate at `ξ = 0`
  obtain ⟨A, -, hA⟩ := exists_abs_ncard_smul_inter_vadd_sub_le (μ := μ) (L := L) hDb hDfr
  refine isBigO_iff.2 ⟨A, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with c hc
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ c) _)]
  simpa using hA 0 c hc

end Lattice

end TauCeti
