/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Support

/-!
# Dirac measures: pushforwards, additive rigidity and finite convex combinations

Mathlib's `MeasureTheory.Measure.map_dirac'` computes `(Measure.dirac x).map T = Measure.dirac
(T x)` for a measurable `T`. A Dirac measure leaves a map no room to be modified on a null set:
its only null sets avoid `x`, so a `Measure.dirac x`-a.e. measurable map already agrees at `x`
with the measurable representative it is a.e. equal to. The pushforward formula therefore holds
under that weaker hypothesis, which is the one a.e.-measurable interfaces such as
`ProbabilityTheory.HasLaw` provide.

A Dirac measure is also rigid under addition: if two measures sum to a Dirac mass, each is a
multiple of that same Dirac mass. This identifies the atomic extreme rays in cones represented
by positive measures.

Finally, the probability measures carried by a finite set are exactly the finite convex
combinations of Dirac measures at its points, with nonnegative real weights summing to `1`.

## Main results

* `Measure.map_dirac_of_aemeasurable` — the Dirac pushforward formula for a map that is
  only a.e. measurable.
* `Measure.dirac_eq_dirac_of_inseparable` — inseparable points have equal Borel Dirac measures.
* `MeasureTheory.Measure.support_dirac` — the topological support of a Dirac measure.
* `TauCeti.MeasureTheory.measurePreserving_const_dirac` — a constant map out of a probability
  space onto a point `b` is measure preserving onto `Measure.dirac b`.
* `MeasureTheory.Measure.eq_smul_dirac_of_forall_notMem` — a measure vanishing on measurable sets
  avoiding a point is a multiple of its Dirac measure.
* `TauCeti.exists_eq_sum_smul_dirac_of_ae_mem_finset` — a probability measure carried by a
  finite set is a convex combination of the Dirac measures at its points.
* `TauCeti.isProbabilityMeasure_sum_smul_dirac` — conversely, a convex combination of Dirac
  measures is a probability measure.
* `TauCeti.eq_smul_dirac_and_eq_smul_dirac_of_add_eq_dirac` — summands of a Dirac measure are
  supported at the same point.
* `TauCeti.isProbabilityMeasure_natWeights`, `Finset.natWeights_compl_eq_zero` — the normalised
  measure `(∑ m)⁻¹ • ∑ m x • δₓ` with natural multiplicities `m` on a finite set `S` is a
  probability measure when `0 < ∑ m`, and it is carried by `S`.
* `TauCeti.exists_finset_prod_natWeights_eq` — such a measure on terms of a sequence `u` is indexed
  by a finite set of pairs `(i, k)`, `k` being the multiplicity of the `i`-th term.
* `Multiset.measureReal_univ_sum_map_dirac`, `Multiset.sum_map_dirac_apply_eq_zero` — the
  counting measure `∑_{x ∈ s} δₓ` of a multiset `s` is finite, has mass `card s` and vanishes on
  measurable sets avoiding `s`.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal Topology

namespace Measure

variable {X : Type*} {Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {T : X → Y}

/-- A Dirac measure leaves a map no room to be modified on a null set: pushing `Measure.dirac x`
forward along a `Measure.dirac x`-a.e. measurable map is evaluating that map at `x`. -/
-- Evaluate the point mass before generic map rules request singleton measurability.
@[simp↓]
theorem map_dirac_of_aemeasurable {x : X} (hT : AEMeasurable T (Measure.dirac x)) :
    (Measure.dirac x).map T = Measure.dirac (T x) := by
  have hx : T x = hT.mk T x := by
    by_contra hne
    have h0 : Measure.dirac x {y | ¬T y = hT.mk T y} = 0 := ae_iff.1 hT.ae_eq_mk
    rw [Measure.dirac_apply_of_mem hne] at h0
    exact one_ne_zero h0
  rw [Measure.map_congr hT.ae_eq_mk, Measure.map_dirac' hT.measurable_mk, ← hx]

/-- Dirac measures at topologically inseparable points agree: Borel measurable sets cannot
separate the points. -/
theorem dirac_eq_dirac_of_inseparable [TopologicalSpace X] [BorelSpace X]
    {x y : X} (hxy : Inseparable x y) : Measure.dirac x = Measure.dirac y := by
  apply MeasureTheory.dirac_eq_dirac_iff_forall_mem_iff_mem.2
  exact fun _ hs ↦ hxy.mem_measurableSet_iff hs

end Measure

namespace MeasureTheory.Measure

open Set

/-- A measure dominates a unit point mass exactly when its mass at that point is at least one. -/
@[simp]
theorem dirac_le_iff_one_le_apply_singleton {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (x : X) :
    dirac x ≤ μ ↔ 1 ≤ μ {x} := by
  classical
  constructor
  · intro h
    simpa only [dirac_apply_of_mem (mem_singleton x)] using h {x}
  · intro hx
    refine le_iff.2 fun A hA ↦ ?_
    by_cases hxA : x ∈ A
    · simpa [dirac_apply' _ hA, hxA] using
        hx.trans (measure_mono (singleton_subset_iff.2 hxA))
    · simp [dirac_apply' _ hA, hxA]

/-- The topological support of a Dirac measure is the closure of its singleton atom. -/
@[simp]
theorem support_dirac {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (a : X) : (dirac a).support = closure {a} := by
  ext x
  rw [support_eq_forall_isOpen, Set.mem_ofPred_eq, mem_closure_iff]
  constructor
  · intro hx U hU hxU
    have haU : a ∈ U := by
      by_contra haU
      simpa [dirac_apply' _ hU.measurableSet, Set.indicator_of_notMem haU] using
        hx U hxU hU
    exact ⟨a, haU, Set.mem_singleton a⟩
  · intro hx U hxU hU
    obtain ⟨_, haU, rfl⟩ := hx U hU hxU
    rw [dirac_apply_of_mem haU]
    exact zero_lt_one

/-- A measure vanishing on every measurable set avoiding `x` is its total mass times the
Dirac measure at `x`. No measurability assumption on `{x}` is needed. -/
theorem eq_smul_dirac_of_forall_notMem {X : Type*} [MeasurableSpace X]
    (κ : Measure X) (x : X)
    (hk : ∀ s, MeasurableSet s → x ∉ s → κ s = 0) :
    κ = κ Set.univ • Measure.dirac x := by
  apply Measure.ext
  intro s hs
  by_cases hx : x ∈ s
  · rw [_root_.smul_apply, Measure.dirac_apply' _ hs,
      Set.indicator_of_mem hx, Pi.one_apply, smul_eq_mul, mul_one]
    exact measure_of_measure_compl_eq_zero (hk sᶜ hs.compl (by simpa))
  · rw [_root_.smul_apply, Measure.dirac_apply' _ hs,
      Set.indicator_of_notMem hx, smul_eq_mul, mul_zero]
    exact hk s hs hx

end MeasureTheory.Measure

/-! ### Counting measures of multisets -/

namespace Multiset

variable {X : Type*} [MeasurableSpace X]

/-- The counting measure `∑_{x ∈ s} δₓ` of a multiset is finite. -/
instance isFiniteMeasure_sum_map_dirac (s : Multiset X) :
    IsFiniteMeasure (s.map Measure.dirac).sum := by
  induction s using Multiset.induction_on with
  | empty => simp only [map_zero, sum_zero]; infer_instance
  | cons a s ih => simp only [map_cons, sum_cons]; infer_instance

/-- The total mass of the counting measure of a multiset is its cardinality. -/
@[simp]
theorem measure_univ_sum_map_dirac (s : Multiset X) :
    (s.map Measure.dirac).sum Set.univ = card s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [ih, add_comm]

/-- The total mass of the counting measure of a multiset is its cardinality. -/
@[simp]
theorem measureReal_univ_sum_map_dirac (s : Multiset X) :
    (s.map Measure.dirac).sum.real Set.univ = card s := by
  simp [measureReal_def]

/-- The counting measure of a multiset vanishes on a measurable set containing none of its
elements. -/
theorem sum_map_dirac_apply_eq_zero {s : Multiset X} {A : Set X} (hA : MeasurableSet A)
    (hs : ∀ x ∈ s, x ∉ A) : (s.map Measure.dirac).sum A = 0 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [map_cons, sum_cons, _root_.add_apply, ih fun x hx => hs x (mem_cons_of_mem hx),
      add_zero, Measure.dirac_apply' _ hA, Set.indicator_of_notMem (hs a (mem_cons_self a s))]

end Multiset

namespace TauCeti

/-- A probability measure carried by a finite set `s` is a convex combination of the Dirac
measures at the points of `s`: indexed by `s` itself, its weights are the masses of the points,
as `ℝ≥0` values summing to `1`. -/
theorem exists_eq_sum_smul_dirac_of_ae_mem_finset {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] {μ : Measure X} [IsProbabilityMeasure μ] {s : Finset X}
    (hμ : ∀ᵐ x ∂μ, x ∈ s) :
    ∃ w : s → ℝ≥0, ∑ x, w x = 1 ∧ μ = ∑ x : s, w x • Measure.dirac (x : X) := by
  have h := Measure.ae_mem_finset_iff.1 hμ
  have hsum : ∑ x ∈ s, μ {x} = 1 := by
    simpa using (congrArg (fun ν : Measure X ↦ ν Set.univ) h).symm
  refine ⟨fun x ↦ (μ {(x : X)}).toNNReal, ENNReal.coe_injective ?_, ?_⟩
  · simp only [ENNReal.ofNNReal_finsetSum, ENNReal.coe_toNNReal (measure_ne_top _ _),
      ENNReal.coe_one]
    rwa [Finset.sum_coe_sort s fun x ↦ μ {x}]
  · conv_lhs => rw [h]
    rw [← Finset.sum_coe_sort s]
    simp only [ENNReal.smul_def, ENNReal.coe_toNNReal (measure_ne_top _ _)]

/-- For weights summing to `1`, the weighted law `∑ j, w j • δ_{y j}` of finitely many points is a
probability measure. -/
theorem isProbabilityMeasure_sum_smul_dirac {J X : Type*} [Fintype J] [MeasurableSpace X]
    {w : J → ℝ≥0} (hw : ∑ j, w j = 1) (y : J → X) :
    IsProbabilityMeasure (∑ j, w j • Measure.dirac (y j)) :=
  Measure.sum_fintype (fun j ↦ w j • Measure.dirac (y j)) ▸
    (hw ▸ hasSum_fintype w).isProbabilityMeasure_sum_dirac_nnreal

/-- If a sum of measures is a Dirac mass, both summands are multiples of that Dirac mass. -/
theorem eq_smul_dirac_and_eq_smul_dirac_of_add_eq_dirac {X : Type*} [MeasurableSpace X]
    {μ ν : Measure X} {x : X}
    (h : μ + ν = Measure.dirac x) :
    μ = μ Set.univ • Measure.dirac x ∧ ν = ν Set.univ • Measure.dirac x := by
  have hzero (s : Set X) (hs : MeasurableSet s) (hx : x ∉ s) :
      μ s = 0 ∧ ν s = 0 := by
    have h' := congrArg (fun η : Measure X => η s) h
    rw [_root_.add_apply, Measure.dirac_apply' _ hs,
      Set.indicator_of_notMem hx] at h'
    exact add_eq_zero.mp h'
  exact ⟨μ.eq_smul_dirac_of_forall_notMem x (fun s hs hx => (hzero s hs hx).1),
    ν.eq_smul_dirac_of_forall_notMem x (fun s hs hx => (hzero s hs hx).2)⟩

section NatWeights

variable {X : Type*} [MeasurableSpace X]

/-- The probability measure with weights given by natural multiplicities `m x` on the points of a
finite set `S` is a probability measure when the total multiplicity is positive. -/
theorem isProbabilityMeasure_natWeights {S : Finset X} {m : X → ℕ} (hm : 0 < ∑ x ∈ S, m x) :
    IsProbabilityMeasure
      ((∑ x ∈ S, (m x : ℝ≥0∞))⁻¹ • ∑ x ∈ S, (m x : ℝ≥0∞) • Measure.dirac x) := by
  refine ⟨?_⟩
  have hmsum : ∑ x ∈ S, ((m x : ℕ) : ℝ≥0∞) = ((∑ x ∈ S, m x : ℕ) : ℝ≥0∞) :=
    (Nat.cast_sum _ _).symm
  have hmass : (∑ x ∈ S, (m x : ℝ≥0∞) • Measure.dirac x) Set.univ
      = ((∑ x ∈ S, m x : ℕ) : ℝ≥0∞) := by
    rw [FunLike.coe_sum, Finset.sum_apply, ← hmsum]
    exact Finset.sum_congr rfl fun x _ ↦ by simp
  rw [_root_.smul_apply, hmass, smul_eq_mul, hmsum,
    ENNReal.inv_mul_cancel (Nat.cast_ne_zero.2 hm.ne') (ENNReal.natCast_ne_top _)]

/-- The measure with natural multiplicities on a finite set of terms of a sequence `u` is of the
form `(∑ m)⁻¹ • ∑ m • δ_(u i)` for a finite set of pairs `(i, k)`, where `k` is the
multiplicity of the `i`-th term. -/
theorem exists_finset_prod_natWeights_eq {u : ℕ → X} {S : Finset X} (m : X → ℕ)
    (hS : ∀ x ∈ S, x ∈ Set.range u) :
    ∃ t : Finset (ℕ × ℕ), (∑ q ∈ t, (q.2 : ℝ≥0∞))⁻¹ •
        ∑ q ∈ t, (q.2 : ℝ≥0∞) • Measure.dirac (u q.1) =
      (∑ x ∈ S, (m x : ℝ≥0∞))⁻¹ • ∑ x ∈ S, (m x : ℝ≥0∞) • Measure.dirac x := by
  classical
  choose! i hi using hS
  have hinj : ∀ x ∈ S, ∀ y ∈ S, (i x, m x) = (i y, m y) → x = y := by
    intro x hx y hy hxy
    have hix : i x = i y := congrArg Prod.fst hxy
    rw [← hi x hx, ← hi y hy, hix]
  refine ⟨S.image fun x ↦ (i x, m x), ?_⟩
  rw [Finset.sum_image hinj, Finset.sum_image hinj]
  exact congrArg₂ _ rfl (Finset.sum_congr rfl fun x hx ↦ by rw [hi x hx])

end NatWeights

end TauCeti

namespace TauCeti

namespace MeasureTheory

variable {X : Type*} {Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- A constant map out of a probability space onto a point `b` is measure preserving onto
`Measure.dirac b`, with no hypothesis on either measurable space. -/
theorem measurePreserving_const_dirac {μ : Measure X} [IsProbabilityMeasure μ] (b : Y) :
    MeasurePreserving (fun _ : X => b) μ (Measure.dirac b) :=
  ⟨measurable_const, by rw [Measure.map_const, measure_univ, one_smul]⟩

end MeasureTheory

end TauCeti

/-- The measure with natural multiplicities `m x` on the points of a finite set `S` is carried
by `S`. -/
theorem Finset.natWeights_compl_eq_zero {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] (S : Finset X) (m : X → ℕ) :
    ((∑ x ∈ S, (m x : ℝ≥0∞))⁻¹ • ∑ x ∈ S, (m x : ℝ≥0∞) • Measure.dirac x)
      ((S : Set X)ᶜ) = 0 := by
  have hzero : (∑ x ∈ S, (m x : ℝ≥0∞) • Measure.dirac x) ((S : Set X)ᶜ) = 0 := by
    rw [FunLike.coe_sum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun x hx ↦ ?_
    rw [_root_.smul_apply, Measure.dirac_apply' _ S.measurableSet.compl,
      Set.indicator_of_notMem (by simpa using hx), smul_zero]
  rw [_root_.smul_apply, hzero, smul_zero]
