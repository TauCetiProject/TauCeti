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
# Dirac measures: cumulative masses, pushforwards, additive rigidity and finite convex combinations

The cumulative mass of a Dirac measure on a preorder is the indicator of the upper set of its atom.

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

* `TauCeti.Probability.dirac_real_Iic` — the cumulative mass of a Dirac measure on a preorder.
* `MeasureTheory.Measure.map_dirac_of_aemeasurable` — the Dirac pushforward formula for a map
  that is only a.e. measurable.
* `MeasureTheory.Measure.dirac_eq_dirac_iff_inseparable` — two points have equal Borel Dirac
  measures exactly when they are topologically inseparable.
* `MeasureTheory.Measure.dirac_le_iff_one_le_apply_singleton` — a measure dominates a unit point
  mass exactly when it gives the point mass at least one.
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
* `TauCeti.exists_finset_prod_natWeights_eq` — such a measure on values of a family `u` is indexed
  by a finite set of pairs `(i, k)`, `k` being the multiplicity of the value `u i`.
* `Multiset.measureReal_univ_sum_map_dirac`, `Multiset.sum_map_dirac_apply_eq_zero` — the
  counting measure `∑_{x ∈ s} δₓ` of a multiset `s` is finite, has mass `card s` and vanishes on
  measurable sets avoiding `s`.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability

open Set

/-- The cumulative mass of a Dirac measure is the indicator of the upper set of its atom. -/
theorem dirac_real_Iic {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Preorder α]
    (a b : α) [Decidable (a ≤ b)] :
    (Measure.dirac a).real (Iic b) = if a ≤ b then 1 else 0 := by
  by_cases h : a ≤ b <;> simp [Measure.dirac_real_apply, Set.indicator, h]

end TauCeti.Probability

namespace MeasureTheory.Measure

open Set

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

/-- Two points have equal Borel Dirac measures exactly when they are topologically inseparable:
Borel measurable sets separate points no better than open sets do. -/
theorem dirac_eq_dirac_iff_inseparable [TopologicalSpace X] [BorelSpace X] {x y : X} :
    dirac x = dirac y ↔ Inseparable x y :=
  dirac_eq_dirac_iff_forall_mem_iff_mem.trans
    ⟨fun h ↦ inseparable_iff_forall_isOpen.2 fun _ hs ↦ h _ hs.measurableSet,
      fun h _ hs ↦ h.mem_measurableSet_iff hs⟩

/-- A measure dominates a unit point mass exactly when its mass at that point is at least one. -/
@[simp]
theorem dirac_le_iff_one_le_apply_singleton (μ : Measure X) (x : X) :
    dirac x ≤ μ ↔ 1 ≤ μ {x} := by
  refine ⟨fun h ↦ by simpa only [dirac_apply_of_mem (mem_singleton x)] using h {x},
    fun hx ↦ le_iff.2 fun A hA ↦ ?_⟩
  rw [dirac_apply' _ hA]
  exact indicator_apply_le' (fun hxA ↦ hx.trans (measure_mono (singleton_subset_iff.2 hxA)))
    fun _ ↦ zero_le

/-- The topological support of a Dirac measure is the closure of its singleton atom. -/
@[simp]
theorem support_dirac [TopologicalSpace X] [OpensMeasurableSpace X] (a : X) :
    (dirac a).support = closure {a} := by
  ext x
  rw [support_eq_forall_isOpen, mem_ofPred_eq, ← specializes_iff_mem_closure,
    specializes_iff_forall_open]
  -- An open set has positive Dirac mass exactly when it contains the atom.
  refine forall_congr' fun U ↦ imp.swap.trans <| forall_congr' fun hU ↦
    imp_congr_right fun _ ↦ ?_
  rw [pos_iff_ne_zero, Ne, dirac_eq_zero_iff_notMem hU.measurableSet, not_not]

/-- A measure vanishing on every measurable set avoiding `x` is its total mass times the
Dirac measure at `x`. No measurability assumption on `{x}` is needed. -/
theorem eq_smul_dirac_of_forall_notMem (κ : Measure X) (x : X)
    (hk : ∀ s, MeasurableSet s → x ∉ s → κ s = 0) :
    κ = κ univ • dirac x := by
  ext s hs
  by_cases hx : x ∈ s
  · -- `κ` gives the complement of `s` no mass, so `κ s` is the total mass.
    simpa [dirac_apply' _ hs, hx] using
      measure_of_measure_compl_eq_zero (hk sᶜ hs.compl (notMem_compl_iff.2 hx))
  · simpa [dirac_apply' _ hs, hx] using hk s hs hx

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
    simp [ih fun x hx ↦ hs x (mem_cons_of_mem hx), Measure.dirac_apply' _ hA,
      hs a (mem_cons_self a s)]

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
  have hzero (s : Set X) (hs : MeasurableSet s) (hx : x ∉ s) : μ s = 0 ∧ ν s = 0 := by
    simpa [Measure.dirac_apply' _ hs, hx] using congr($h s)
  exact ⟨μ.eq_smul_dirac_of_forall_notMem x (fun s hs hx => (hzero s hs hx).1),
    ν.eq_smul_dirac_of_forall_notMem x (fun s hs hx => (hzero s hs hx).2)⟩

section NatWeights

variable {X : Type*} [MeasurableSpace X]

/-- The normalised measure `(∑ m)⁻¹ • ∑ m x • δₓ` with natural multiplicities `m x` on the points
of a finite set `S` is a probability measure when the total multiplicity is positive. -/
theorem isProbabilityMeasure_natWeights {S : Finset X} {m : X → ℕ} (hm : 0 < ∑ x ∈ S, m x) :
    IsProbabilityMeasure
      ((∑ x ∈ S, (m x : ℝ≥0∞))⁻¹ • ∑ x ∈ S, (m x : ℝ≥0∞) • Measure.dirac x) := by
  constructor
  -- The total mass is `(∑ m)⁻¹ * ∑ m`.
  simp only [_root_.smul_apply, FunLike.coe_sum, Finset.sum_apply, measure_univ, smul_eq_mul,
    mul_one]
  exact ENNReal.inv_mul_cancel (by simpa using hm.ne') (by simp)

/-- The measure with natural multiplicities on a finite set of values of a family `u` is of the
form `(∑ m)⁻¹ • ∑ m • δ_(u i)` for a finite set of pairs `(i, k)`, where `k` is the
multiplicity of the value `u i`. -/
theorem exists_finset_prod_natWeights_eq {ι : Type*} {u : ι → X} {S : Finset X} (m : X → ℕ)
    (hS : ∀ x ∈ S, x ∈ Set.range u) :
    ∃ t : Finset (ι × ℕ), (∑ q ∈ t, (q.2 : ℝ≥0∞))⁻¹ •
        ∑ q ∈ t, (q.2 : ℝ≥0∞) • Measure.dirac (u q.1) =
      (∑ x ∈ S, (m x : ℝ≥0∞))⁻¹ • ∑ x ∈ S, (m x : ℝ≥0∞) • Measure.dirac x := by
  classical
  obtain rfl | ⟨x₀, hx₀⟩ := S.eq_empty_or_nonempty
  · exact ⟨∅, by simp⟩
  -- `choose!` needs an index to fill in off `S`.
  have : Nonempty ι := ⟨(hS x₀ hx₀).choose⟩
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
    exact Finset.sum_eq_zero fun x hx ↦ by
      simp [Measure.dirac_apply' _ S.measurableSet.compl, Finset.mem_coe.2 hx]
  rw [_root_.smul_apply, hzero, smul_zero]
