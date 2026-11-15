/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.MeasurableSpace.Souslin
public import TauCeti.Probability.Process.Debut
public import TauCeti.Probability.Process.Filtration.Progressive
public import TauCeti.Probability.Process.Predictable.StoppingTime
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# The predictable section theorem and graph announcement

For a filtration `ℱ` indexed by `ℝ≥0`, `ℱ.predictablePaving` consists of finite unions of closed
stochastic intervals `[[σᵢ, τᵢ]]` with pointwise predictable lower endpoints `σᵢ` and everywhere
finite stopping upper endpoints `τᵢ`. Every set in `ℱ.predictablePaving` has compact time fibers, a
pointwise predictable debut, and an ambient-measurable sample-space projection without completing
the measure space. The paving is closed under finite unions and intersections, generates
`ℱ.predictable`, and has complements in its Souslin closure, so every predictable set belongs to
`souslinClosure ℱ.predictablePaving`.

Combining Theodorakopoulos's Souslin-scheme pruning theorem with compact-fiber debut continuity and
outer-measure projection continuity yields the predictable section theorem
(`TauCeti.exists_isPredictableTime_section_lt` and
`TauCeti.exists_isPredictableTime_section_le_add`) on any finite measure space, without assuming
completeness or right continuity of the filtration.

We then define almost-sure announcing sequences (`TauCeti.IsAEAnnouncingSequence`), prove that on a
right-continuous filtration over a finite measure space every random time with predictable finite
graph (and every stopping time with predictable closed upper ray) admits an almost-sure announcing
sequence, and upgrade almost-sure announcement to pointwise announcement under completeness
(`[ℱ.IsComplete P]`) or ambient-null completeness. On a complete right-continuous finite-measure
basis, a `[0, ∞]`-valued random time is pointwise predictable if and only if its finite graph
(equivalently, its closed upper ray) is predictable.

## References

* S. Theodorakopoulos, *New proofs to measurable, predictable and optional section theorems*,
  arXiv:2310.13086v2, Lemma 4.2, Theorem 4.4, and Corollary 4.5.
* C. Dellacherie and P.-A. Meyer, *Probabilities and Potential*, North-Holland, 1978,
  Chapter IV, Theorems 71 and 84.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory.Filtration

variable {Ω : Type*} {m : MeasurableSpace Ω} (ℱ : Filtration ℝ≥0 m)

/-- The predictable paving `E*` of finite unions of closed stochastic intervals `[[σᵢ, τᵢ]]` with
pointwise predictable lower endpoints and everywhere finite stopping upper endpoints. -/
def predictablePaving : Set (Set (ℝ≥0 × Ω)) :=
  {u | ∃ (n : ℕ) (σ τ : Fin n → Ω → WithTop ℝ≥0),
    (∀ i, TauCeti.IsPredictableTime ℱ (σ i)) ∧
    (∀ i, IsStoppingTime ℱ (τ i)) ∧
    (∀ i ω, τ i ω ≠ ⊤) ∧
    u = ⋃ i, {p : ℝ≥0 × Ω | σ i p.2 ≤ p.1 ∧ (p.1 : WithTop ℝ≥0) ≤ τ i p.2}}

/-- Unfold the definition of `predictablePaving`. -/
theorem predictablePaving_def :
    ℱ.predictablePaving =
      {u | ∃ (n : ℕ) (σ τ : Fin n → Ω → WithTop ℝ≥0),
        (∀ i, TauCeti.IsPredictableTime ℱ (σ i)) ∧
        (∀ i, IsStoppingTime ℱ (τ i)) ∧
        (∀ i ω, τ i ω ≠ ⊤) ∧
        u = ⋃ i, {p : ℝ≥0 × Ω | σ i p.2 ≤ p.1 ∧ (p.1 : WithTop ℝ≥0) ≤ τ i p.2}} :=
  (rfl)

/-- Membership in `predictablePaving` unpacked into finite families of endpoints. -/
theorem mem_predictablePaving_iff {u : Set (ℝ≥0 × Ω)} :
    u ∈ ℱ.predictablePaving ↔
      ∃ (n : ℕ) (σ τ : Fin n → Ω → WithTop ℝ≥0),
        (∀ i, TauCeti.IsPredictableTime ℱ (σ i)) ∧
        (∀ i, IsStoppingTime ℱ (τ i)) ∧
        (∀ i ω, τ i ω ≠ ⊤) ∧
        u = ⋃ i, {p : ℝ≥0 × Ω | σ i p.2 ≤ p.1 ∧ (p.1 : WithTop ℝ≥0) ≤ τ i p.2} :=
  Iff.rfl

section PavingProperties

variable {ℱ}

/-- The empty set belongs to `predictablePaving` as an empty union. -/
theorem empty_mem_predictablePaving : ∅ ∈ ℱ.predictablePaving :=
  ⟨0, Fin.elim0, Fin.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0, by simp⟩

/-- Every single closed stochastic interval `[[σ, τ]]` with predictable `σ` and finite stopping `τ`
belongs to `predictablePaving`. -/
theorem Icc_mem_predictablePaving {σ τ : Ω → WithTop ℝ≥0}
    (hσ : TauCeti.IsPredictableTime ℱ σ) (hτ : IsStoppingTime ℱ τ) (hfin : ∀ ω, τ ω ≠ ⊤) :
    {p : ℝ≥0 × Ω | σ p.2 ≤ p.1 ∧ (p.1 : WithTop ℝ≥0) ≤ τ p.2} ∈ ℱ.predictablePaving :=
  ⟨1, fun _ ↦ σ, fun _ ↦ τ, fun _ ↦ hσ, fun _ ↦ hτ, fun _ ↦ hfin, (iUnion_const _).symm⟩

/-- `predictablePaving` is closed under binary unions. -/
theorem union_mem_predictablePaving {u v : Set (ℝ≥0 × Ω)}
    (hu : u ∈ ℱ.predictablePaving) (hv : v ∈ ℱ.predictablePaving) :
    u ∪ v ∈ ℱ.predictablePaving := by
  rcases hu with ⟨m₁, σ₁, τ₁, hσ₁, hτ₁, hfin₁, rfl⟩
  rcases hv with ⟨m₂, σ₂, τ₂, hσ₂, hτ₂, hfin₂, rfl⟩
  refine ⟨m₁ + m₂, Fin.addCases σ₁ σ₂, Fin.addCases τ₁ τ₂,
    fun i ↦ Fin.addCases (fun j ↦ by simpa only [Fin.addCases_left] using hσ₁ j)
      (fun j ↦ by simpa only [Fin.addCases_right] using hσ₂ j) i,
    fun i ↦ Fin.addCases (fun j ↦ by simpa only [Fin.addCases_left] using hτ₁ j)
      (fun j ↦ by simpa only [Fin.addCases_right] using hτ₂ j) i,
    fun i ↦ Fin.addCases (fun j ↦ by simpa only [Fin.addCases_left] using hfin₁ j)
      (fun j ↦ by simpa only [Fin.addCases_right] using hfin₂ j) i, ?_⟩
  ext p
  simp only [mem_union, mem_iUnion]
  refine ⟨fun h ↦ h.elim (fun ⟨i, hi⟩ ↦ ⟨Fin.castAdd m₂ i, by simpa using hi⟩)
      (fun ⟨j, hj⟩ ↦ ⟨Fin.natAdd m₁ j, by simpa using hj⟩), ?_⟩
  rintro ⟨k, hk⟩
  revert hk
  exact k.addCases (fun i hk ↦ Or.inl ⟨i, by simpa using hk⟩)
    (fun j hk ↦ Or.inr ⟨j, by simpa using hk⟩)

/-- `predictablePaving` is closed under binary intersections. -/
theorem inter_mem_predictablePaving {u v : Set (ℝ≥0 × Ω)}
    (hu : u ∈ ℱ.predictablePaving) (hv : v ∈ ℱ.predictablePaving) :
    u ∩ v ∈ ℱ.predictablePaving := by
  rcases hu with ⟨m₁, σ₁, τ₁, hσ₁, hτ₁, hfin₁, rfl⟩
  rcases hv with ⟨m₂, σ₂, τ₂, hσ₂, hτ₂, _, rfl⟩
  let e : Fin (m₁ * m₂) ≃ Fin m₁ × Fin m₂ := finProdFinEquiv.symm
  refine ⟨m₁ * m₂,
    fun k ω ↦ max (σ₁ (e k).1 ω) (σ₂ (e k).2 ω),
    fun k ω ↦ min (τ₁ (e k).1 ω) (τ₂ (e k).2 ω),
    fun k ↦ (hσ₁ _).max (hσ₂ _),
    fun k ↦ (hτ₁ _).min (hτ₂ _),
    fun k ω ↦ ne_top_of_le_ne_top (hfin₁ (e k).1 ω) (min_le_left _ _), ?_⟩
  ext p
  simp only [mem_inter_iff, mem_iUnion, mem_ofPred_eq, max_le_iff, le_min_iff]
  rw [e.exists_congr_left]
  simp only [e.apply_symm_apply, Prod.exists]
  exact ⟨fun ⟨⟨i, hi1, hi2⟩, ⟨j, hj1, hj2⟩⟩ ↦ ⟨i, j, ⟨hi1, hj1⟩, ⟨hi2, hj2⟩⟩,
    fun ⟨i, j, ⟨hi1, hj1⟩, ⟨hi2, hj2⟩⟩ ↦ ⟨⟨i, hi1, hi2⟩, ⟨j, hj1, hj2⟩⟩⟩

/-- Every set in `predictablePaving` has compact time fibers at every outcome. -/
theorem isCompact_fiber_of_mem_predictablePaving {u : Set (ℝ≥0 × Ω)}
    (hu : u ∈ ℱ.predictablePaving) (ω : Ω) :
    IsCompact {t : ℝ≥0 | (t, ω) ∈ u} := by
  rcases hu with ⟨n, σ, τ, _, _, hfin, rfl⟩
  have heq : {t : ℝ≥0 |
      (t, ω) ∈ ⋃ i, {p : ℝ≥0 × Ω | σ i p.2 ≤ p.1 ∧ (p.1 : WithTop ℝ≥0) ≤ τ i p.2}} =
      ⋃ i, {t : ℝ≥0 | σ i ω ≤ t ∧ (t : WithTop ℝ≥0) ≤ τ i ω} := by
    ext t; simp
  rw [heq]
  refine isCompact_iUnion fun i ↦ ?_
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp (hfin i ω)
  cases ha : σ i ω with
  | top =>
    have hemp : {t : ℝ≥0 | (⊤ : WithTop ℝ≥0) ≤ t ∧ (t : WithTop ℝ≥0) ≤ τ i ω} = ∅ := by
      ext t
      simp only [mem_ofPred_eq, top_le_iff, WithTop.coe_ne_top, false_and, mem_empty_iff_false]
    exact hemp ▸ isCompact_empty
  | coe a =>
    have hIcc : {t : ℝ≥0 | (a : WithTop ℝ≥0) ≤ t ∧ (t : WithTop ℝ≥0) ≤ τ i ω} = Icc a b := by
      ext t
      simp only [mem_ofPred_eq, ← hb, WithTop.coe_le_coe, mem_Icc]
    exact hIcc ▸ isCompact_Icc

/-- The debut of every set in `predictablePaving` is pointwise predictable. -/
theorem isPredictableTime_debut_of_mem_predictablePaving {u : Set (ℝ≥0 × Ω)}
    (hu : u ∈ ℱ.predictablePaving) :
    TauCeti.IsPredictableTime ℱ (TauCeti.debut u) := by
  rcases hu with ⟨n, σ, τ, hσ, hτ, _, rfl⟩
  have heq : TauCeti.debut
      (⋃ i, {p : ℝ≥0 × Ω | σ i p.2 ≤ p.1 ∧ (p.1 : WithTop ℝ≥0) ≤ τ i p.2}) =
      fun ω ↦ Finset.univ.inf fun i ↦ if σ i ω ≤ τ i ω then σ i ω else ⊤ := by
    ext ω
    rw [TauCeti.debut_iUnion, iInf_apply, Finset.inf_univ_eq_iInf]
    refine iInf_congr fun i ↦ ?_
    rw [TauCeti.debut_Icc]
    congr
  rw [heq]
  exact TauCeti.IsPredictableTime.finsetInf fun i _ ↦ (hσ i).ite_le (hτ i)

/-- Every set in `predictablePaving` has ambient-measurable projection onto `Ω`, without completing
the measure space. -/
theorem measurableSet_image_snd_of_mem_predictablePaving {u : Set (ℝ≥0 × Ω)}
    (hu : u ∈ ℱ.predictablePaving) :
    MeasurableSet (Prod.snd '' u) := by
  rw [TauCeti.image_snd_eq_setOf_debut_ne_top]
  have hstop := (ℱ.isPredictableTime_debut_of_mem_predictablePaving hu).isStoppingTime
  exact hstop.measurableSet_eq_top.compl

/-- Every set in `predictablePaving` belongs to `ℱ.predictable`. -/
theorem measurableSet_predictable_of_mem_predictablePaving {u : Set (ℝ≥0 × Ω)}
    (hu : u ∈ ℱ.predictablePaving) :
    MeasurableSet[ℱ.predictable] u := by
  rcases hu with ⟨n, σ, τ, hσ, hτ, _, rfl⟩
  exact MeasurableSet.iUnion fun i ↦ (hσ i).measurableSet_predictable_Icc (hτ i)

end PavingProperties

/-- `predictablePaving` generates the predictable sigma-algebra `ℱ.predictable`. -/
theorem generateFrom_predictablePaving :
    MeasurableSpace.generateFrom ℱ.predictablePaving = ℱ.predictable := by
  refine le_antisymm (MeasurableSpace.generateFrom_le fun _ hu ↦
    ℱ.measurableSet_predictable_of_mem_predictablePaving hu) ?_
  rw [ℱ.predictable_eq_generateFrom_isPredictableTime_le]
  refine MeasurableSpace.generateFrom_le ?_
  rintro _ ⟨σ, hσ, rfl⟩
  have heq : {p : ℝ≥0 × Ω | σ p.2 ≤ p.1} =
      ⋃ m : ℕ, {p : ℝ≥0 × Ω | σ p.2 ≤ p.1 ∧ (p.1 : WithTop ℝ≥0) ≤ (m : ℝ≥0)} := by
    ext ⟨t, ω⟩
    simp only [mem_ofPred_eq, mem_iUnion, WithTop.coe_le_coe]
    exact ⟨fun h ↦ let ⟨m, hm⟩ := exists_nat_ge t; ⟨m, h, hm⟩, fun ⟨_, h, _⟩ ↦ h⟩
  rw [heq]
  exact MeasurableSet.iUnion fun m ↦ MeasurableSpace.measurableSet_generateFrom
    (ℱ.Icc_mem_predictablePaving hσ (isStoppingTime_const ℱ m) fun _ ↦ WithTop.coe_ne_top)

section SouslinClosure

variable {ℱ}

-- The strict lower ray of a pointwise predictable time belongs to the Souslin closure of `E*`.
private theorem lt_predictable_mem_souslinClosure {σ : Ω → WithTop ℝ≥0}
    (hσ : TauCeti.IsPredictableTime ℱ σ) :
    {p : ℝ≥0 × Ω | (p.1 : WithTop ℝ≥0) < σ p.2} ∈ TauCeti.souslinClosure ℱ.predictablePaving := by
  classical
  obtain ⟨s, hs⟩ := TauCeti.isPredictableTime_iff.mp hσ
  let A : Set Ω := {ω | σ ω ≤ (0 : ℝ≥0)}ᶜ
  have hA : MeasurableSet[ℱ 0] A := (hs.isStoppingTime_limit 0).compl
  let σ₀ : Ω → WithTop ℝ≥0 := A.piecewise (fun _ ↦ 0) (fun _ ↦ ⊤)
  have hσ₀ : TauCeti.IsPredictableTime ℱ σ₀ :=
    TauCeti.IsPredictableTime.zero.piecewise TauCeti.IsPredictableTime.top hA
  have heq : {p : ℝ≥0 × Ω | (p.1 : WithTop ℝ≥0) < σ p.2} =
      ⋃ m : ℕ, {p : ℝ≥0 × Ω | σ₀ p.2 ≤ p.1 ∧ (p.1 : WithTop ℝ≥0) ≤ s m p.2} := by
    ext ⟨t, ω⟩
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · intro hlt
      have hpos : 0 < σ ω := bot_le.trans_lt hlt
      have hAω : ω ∈ A := by
        simpa only [A, mem_compl_iff, mem_ofPred_eq, WithTop.coe_zero, not_le] using hpos
      rw [← hs.iSup_eq ω, lt_iSup_iff] at hlt
      obtain ⟨m, hm⟩ := hlt
      refine ⟨m, ?_, hm.le⟩
      simp only [σ₀, hAω, piecewise_eq_of_mem]
      exact bot_le
    · rintro ⟨m, h0, hm⟩
      by_cases hAω : ω ∈ A
      · have hpos : 0 < σ ω := by
          simpa only [A, mem_compl_iff, mem_ofPred_eq, WithTop.coe_zero, not_le] using hAω
        exact hm.trans_lt (hs.lt m ω hpos)
      · simp only [σ₀, hAω, not_false_eq_true, piecewise_eq_of_notMem, top_le_iff,
          WithTop.coe_ne_top] at h0
  rw [heq]
  exact TauCeti.iUnion_mem_souslinClosure fun m ↦ TauCeti.subset_souslinClosure
    (ℱ.Icc_mem_predictablePaving hσ₀ (hs.isStoppingTime m) (hs.ne_top m))

-- The strict upper ray of a finite stopping time belongs to the Souslin closure of `E*`.
private theorem gt_stopping_mem_souslinClosure {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime ℱ τ) (hfin : ∀ ω, τ ω ≠ ⊤) :
    {p : ℝ≥0 × Ω | τ p.2 < p.1} ∈ TauCeti.souslinClosure ℱ.predictablePaving := by
  have heq : {p : ℝ≥0 × Ω | τ p.2 < p.1} =
      ⋃ k : ℕ, ⋃ m : ℕ,
        {p : ℝ≥0 × Ω | τ p.2 + ((1 / (k + 1 : ℝ≥0) : ℝ≥0) : WithTop ℝ≥0) ≤ p.1 ∧
          (p.1 : WithTop ℝ≥0) ≤ (m : ℝ≥0)} := by
    ext ⟨t, ω⟩
    obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.mp (hfin ω)
    simp only [mem_ofPred_eq, mem_iUnion, ← hu, ← WithTop.coe_add, WithTop.coe_lt_coe,
      WithTop.coe_le_coe]
    constructor
    · intro hut
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr (NNReal.coe_lt_coe.mpr hut))
      obtain ⟨m, hm⟩ := exists_nat_ge t
      exact ⟨k, m, by exact_mod_cast (lt_sub_iff_add_lt'.mp hk).le, hm⟩
    · rintro ⟨k, _, hk, _⟩
      exact (lt_add_of_pos_right u (by positivity)).trans_le hk
  rw [heq]
  exact TauCeti.iUnion_mem_souslinClosure fun k ↦ TauCeti.iUnion_mem_souslinClosure fun m ↦
    TauCeti.subset_souslinClosure (ℱ.Icc_mem_predictablePaving
      (hτ.isPredictableTime_add_const (by positivity)) (isStoppingTime_const ℱ m)
      fun _ ↦ WithTop.coe_ne_top)

/-- The complement of every set in `predictablePaving` belongs to
`souslinClosure ℱ.predictablePaving`. -/
theorem compl_mem_souslinClosure_predictablePaving {u : Set (ℝ≥0 × Ω)}
    (hu : u ∈ ℱ.predictablePaving) :
    uᶜ ∈ TauCeti.souslinClosure ℱ.predictablePaving := by
  rcases hu with ⟨n, σ, τ, hσ, hτ, hfin, rfl⟩
  cases n with
  | zero =>
    have hc : (⋃ i : Fin 0,
        {p : ℝ≥0 × Ω | σ i p.2 ≤ p.1 ∧ (p.1 : WithTop ℝ≥0) ≤ τ i p.2})ᶜ = univ := by simp
    have huniv : (univ : Set (ℝ≥0 × Ω)) =
        ⋃ m : ℕ, {p : ℝ≥0 × Ω | (0 : WithTop ℝ≥0) ≤ p.1 ∧ (p.1 : WithTop ℝ≥0) ≤ (m : ℝ≥0)} := by
      ext ⟨t, _⟩
      simp only [mem_univ, mem_iUnion, mem_ofPred_eq, true_iff]
      obtain ⟨m, hm⟩ := exists_nat_ge t
      exact ⟨m, bot_le, WithTop.coe_le_coe.mpr hm⟩
    rw [hc, huniv]
    exact TauCeti.iUnion_mem_souslinClosure fun m ↦ TauCeti.subset_souslinClosure
      (ℱ.Icc_mem_predictablePaving TauCeti.IsPredictableTime.zero (isStoppingTime_const ℱ m)
        fun _ ↦ WithTop.coe_ne_top)
  | succ n =>
    have heq : (⋃ i : Fin (n + 1),
        {p : ℝ≥0 × Ω | σ i p.2 ≤ p.1 ∧ (p.1 : WithTop ℝ≥0) ≤ τ i p.2})ᶜ =
        ⋂ i : Fin (n + 1),
          ({p : ℝ≥0 × Ω | (p.1 : WithTop ℝ≥0) < σ i p.2} ∪ {p : ℝ≥0 × Ω | τ i p.2 < p.1}) := by
      ext p
      simp only [compl_iUnion, mem_iInter, mem_compl_iff, mem_ofPred_eq, not_and_or, not_le,
        mem_union]
    rw [heq]
    exact TauCeti.iInter_mem_souslinClosure fun i ↦ TauCeti.union_mem_souslinClosure
      (lt_predictable_mem_souslinClosure (hσ i))
      (gt_stopping_mem_souslinClosure (hτ i) (hfin i))

/-- Every predictable set belongs to the Souslin closure of `ℱ.predictablePaving` (Theodorakopoulos,
Lemma 4.2). -/
theorem mem_souslinClosure_predictablePaving_of_measurableSet_predictable {E : Set (ℝ≥0 × Ω)}
    (hE : MeasurableSet[ℱ.predictable] E) :
    E ∈ TauCeti.souslinClosure ℱ.predictablePaving :=
  TauCeti.mem_souslinClosure_of_measurableSet_generateFrom
    ⟨∅, ℱ.empty_mem_predictablePaving⟩
    (fun _ hu ↦ ℱ.compl_mem_souslinClosure_predictablePaving hu)
    (ℱ.generateFrom_predictablePaving.symm ▸ hE)

/-- The debut of the intersection of an antitone sequence in `predictablePaving` is pointwise
predictable. -/
theorem isPredictableTime_debut_iInter {e : ℕ → Set (ℝ≥0 × Ω)} (hanti : Antitone e)
    (he : ∀ k, e k ∈ ℱ.predictablePaving) :
    TauCeti.IsPredictableTime ℱ (TauCeti.debut (⋂ k, e k)) := by
  have heq : TauCeti.debut (⋂ k, e k) = fun ω ↦ ⨆ k, TauCeti.debut (e k) ω :=
    funext fun ω ↦ TauCeti.debut_iInter_eq_iSup_of_isCompact hanti
      fun k ↦ ℱ.isCompact_fiber_of_mem_predictablePaving (he k) ω
  rw [heq]
  exact TauCeti.IsPredictableTime.iSup fun k ↦
    ℱ.isPredictableTime_debut_of_mem_predictablePaving (he k)

/-- For an antitone sequence in `predictablePaving`, the debut sublevel of the intersection at time
`t` is the intersection of the time-`t` truncated projections, and belongs to `ℱ t` without
completeness or right continuity. -/
theorem debut_iInter_le_coe_eq {e : ℕ → Set (ℝ≥0 × Ω)} (hanti : Antitone e)
    (he : ∀ k, e k ∈ ℱ.predictablePaving) (t : ℝ≥0) :
    {ω | TauCeti.debut (⋂ k, e k) ω ≤ t} = ⋂ k, Prod.snd '' (e k ∩ (Iic t ×ˢ univ)) := by
  have hfib (k : ℕ) (ω : Ω) :
      {u : ℝ≥0 | (u, ω) ∈ e k ∩ (Iic t ×ˢ univ)} = {u : ℝ≥0 | (u, ω) ∈ e k} ∩ Iic t := by
    ext u; simp
  have hK (k : ℕ) (ω : Ω) : IsCompact {u : ℝ≥0 | (u, ω) ∈ e k ∩ (Iic t ×ˢ univ)} :=
    hfib k ω ▸ (ℱ.isCompact_fiber_of_mem_predictablePaving (he k) ω).inter_right isClosed_Iic
  have hanti' : Antitone (fun k ↦ e k ∩ (Iic t ×ˢ univ)) :=
    fun _ _ h ↦ inter_subset_inter_left _ (hanti h)
  rw [← TauCeti.image_snd_iInter_eq_of_isCompact hanti' hK]
  ext ω
  simp only [mem_ofPred_eq,
    TauCeti.debut_le_coe_iff_of_isCompact
      (TauCeti.isCompact_fiber_iInter fun k ↦ ℱ.isCompact_fiber_of_mem_predictablePaving (he k) ω),
    mem_image, Prod.exists, exists_eq_right, mem_iInter, mem_inter_iff, mem_prod, mem_Iic,
    mem_univ, and_true]
  exact ⟨fun ⟨u, hut, hu⟩ ↦ ⟨u, fun k ↦ ⟨hu k, hut⟩⟩,
    fun ⟨u, hu⟩ ↦ ⟨u, (hu 0).2, fun k ↦ (hu k).1⟩⟩

/-- For an antitone sequence in `predictablePaving`, the debut sublevel of the intersection at time
`t` is `ℱ t`-measurable without completeness or right continuity. -/
theorem measurableSet_debut_iInter_le {e : ℕ → Set (ℝ≥0 × Ω)} (hanti : Antitone e)
    (he : ∀ k, e k ∈ ℱ.predictablePaving) (t : ℝ≥0) :
    MeasurableSet[ℱ t] {ω | TauCeti.debut (⋂ k, e k) ω ≤ t} :=
  (ℱ.isPredictableTime_debut_iInter hanti he).isStoppingTime t

/-- For an antitone sequence in `predictablePaving`, the sample-space projection of the intersection
is ambient-measurable without completing the measure space. -/
theorem measurableSet_image_snd_iInter_of_mem_predictablePaving {e : ℕ → Set (ℝ≥0 × Ω)}
    (hanti : Antitone e) (he : ∀ k, e k ∈ ℱ.predictablePaving) :
    MeasurableSet (Prod.snd '' (⋂ k, e k)) := by
  rw [TauCeti.image_snd_iInter_eq_of_isCompact hanti
    fun k ω ↦ ℱ.isCompact_fiber_of_mem_predictablePaving (he k) ω]
  exact MeasurableSet.iInter fun k ↦ ℱ.measurableSet_image_snd_of_mem_predictablePaving (he k)

end SouslinClosure

end MeasureTheory.Filtration

namespace TauCeti

section PredictableSectionTheorem

variable {Ω : Type*} {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m}
  {P : Measure Ω} [IsFiniteMeasure P]

/-- **The predictable section theorem (strict threshold form).** For any predictable set `E` and
any finite measure `P` (without completeness or right continuity of `ℱ`), every threshold strictly
below the outer measure `P (Prod.snd '' E)` is exceeded by the finite-domain probability of a
pointwise predictable time `T` whose finite graph lies in `E`. -/
theorem exists_isPredictableTime_section_lt {E : Set (ℝ≥0 × Ω)}
    (hE : MeasurableSet[ℱ.predictable] E) {r : ℝ≥0∞} (hr : r < P (Prod.snd '' E)) :
    ∃ T : Ω → WithTop ℝ≥0, IsPredictableTime ℱ T ∧
      (∀ ω (t : ℝ≥0), T ω = t → (t, ω) ∈ E) ∧ r < P {ω | T ω ≠ ⊤} := by
  have hI_mono : Monotone (fun s : Set (ℝ≥0 × Ω) ↦ P (Prod.snd '' s)) :=
    fun _ _ hst ↦ measure_mono (image_mono hst)
  have hI_cont (u : ℕ → Set (ℝ≥0 × Ω)) (hu : Monotone u) :
      P (Prod.snd '' (⋃ n, u n)) = ⨆ n, P (Prod.snd '' u n) := by
    rw [image_iUnion]
    exact Monotone.measure_iUnion (fun _ _ h ↦ image_mono (hu h))
  obtain ⟨e, he_anti, he_mem, he_sub, he_lt⟩ :=
    exists_antitone_mem_of_lt_of_mem_souslinClosure
      (fun _ hu _ hv ↦ ℱ.union_mem_predictablePaving hu hv)
      (fun _ hu _ hv ↦ ℱ.inter_mem_predictablePaving hu hv)
      hI_mono hI_cont
      (ℱ.mem_souslinClosure_predictablePaving_of_measurableSet_predictable hE) hr
  refine ⟨debut (⋂ k, e k), ℱ.isPredictableTime_debut_iInter he_anti he_mem, ?_, ?_⟩
  · intro ω t ht
    exact he_sub (debut_mem_of_isCompact
      (isCompact_fiber_iInter fun k ↦ ℱ.isCompact_fiber_of_mem_predictablePaving (he_mem k) ω) ht)
  · have hproj : {ω | debut (⋂ k, e k) ω ≠ ⊤} = ⋂ k, Prod.snd '' e k := by
      rw [← image_snd_eq_setOf_debut_ne_top]
      exact image_snd_iInter_eq_of_isCompact he_anti
        fun k ω ↦ ℱ.isCompact_fiber_of_mem_predictablePaving (he_mem k) ω
    have hmeas : P (⋂ k, Prod.snd '' e k) = ⨅ k, P (Prod.snd '' e k) :=
      Antitone.measure_iInter (fun _ _ h ↦ image_mono (he_anti h))
        (fun k ↦ (ℱ.measurableSet_image_snd_of_mem_predictablePaving (he_mem k)).nullMeasurableSet)
        ⟨0, measure_ne_top P _⟩
    exact hproj ▸ hmeas ▸ he_lt

/-- **The predictable section theorem** (Dellacherie–Meyer, IV.84; Theodorakopoulos, Theorem 4.4).
For any predictable set `E`, finite measure `P`, and tolerance `ε ≠ 0` (without completeness or
right continuity of `ℱ`), there exists a pointwise predictable time `T` whose finite graph lies in
`E` and whose finite-domain probability misses `P (Prod.snd '' E)` by at most `ε`. -/
theorem exists_isPredictableTime_section_le_add {E : Set (ℝ≥0 × Ω)}
    (hE : MeasurableSet[ℱ.predictable] E) (P : Measure Ω) [IsFiniteMeasure P]
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ T : Ω → WithTop ℝ≥0, IsPredictableTime ℱ T ∧
      (∀ ω (t : ℝ≥0), T ω = t → (t, ω) ∈ E) ∧
      P (Prod.snd '' E) ≤ P {ω | T ω ≠ ⊤} + ε := by
  by_cases hle : P (Prod.snd '' E) ≤ ε
  · refine ⟨fun _ ↦ ⊤, IsPredictableTime.top, fun _ _ h ↦ (WithTop.coe_ne_top h.symm).elim, ?_⟩
    simpa using hle
  · have hlt : ε < P (Prod.snd '' E) := lt_of_not_ge hle
    have hne : P (Prod.snd '' E) ≠ 0 := pos_iff_ne_zero.mp ((pos_iff_ne_zero.mpr hε).trans hlt)
    have hsub : P (Prod.snd '' E) - ε < P (Prod.snd '' E) :=
      ENNReal.sub_lt_self (measure_ne_top P _) hne hε
    obtain ⟨T, hT, hgraph, hrT⟩ := exists_isPredictableTime_section_lt hE hsub
    exact ⟨T, hT, hgraph, tsub_le_iff_right.mp hrT.le⟩

end PredictableSectionTheorem

section AEAnnouncingSequence

variable {Ω : Type*} {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m}
  {P : Measure Ω} {σ : ℕ → Ω → WithTop ℝ≥0} {τ : Ω → WithTop ℝ≥0}

/-- An almost-sure announcing sequence consists of `ℱ`-stopping times that almost surely increase
to `τ` (including at infinity) and are almost surely strictly smaller than `τ` wherever `0 < τ`. -/
structure IsAEAnnouncingSequence (ℱ : Filtration ℝ≥0 m) (P : Measure Ω)
    (σ : ℕ → Ω → WithTop ℝ≥0) (τ : Ω → WithTop ℝ≥0) : Prop where
  /-- Every approximant is a stopping time of the filtration. -/
  isStoppingTime : ∀ n, IsStoppingTime ℱ (σ n)
  /-- The approximants increase almost surely. -/
  monotone : ∀ᵐ ω ∂P, Monotone (fun n ↦ σ n ω)
  /-- The approximants converge to `τ` almost surely, including on `{τ = ⊤}`. -/
  tendsto : ∀ᵐ ω ∂P, Tendsto (fun n ↦ σ n ω) atTop (𝓝 (τ ω))
  /-- Strict announcement holds almost surely wherever `τ` is positive. -/
  lt : ∀ᵐ ω ∂P, ∀ n, 0 < τ ω → σ n ω < τ ω

/-- Every pointwise announcing sequence is an almost-sure announcing sequence for every measure. -/
theorem IsAnnouncingSequence.isAEAnnouncingSequence (h : IsAnnouncingSequence ℱ σ τ)
    (P : Measure Ω) : IsAEAnnouncingSequence ℱ P σ τ where
  isStoppingTime := h.isStoppingTime
  monotone := Eventually.of_forall h.monotone
  tendsto := Eventually.of_forall h.tendsto
  lt := Eventually.of_forall fun ω n hpos ↦ h.lt n ω hpos

namespace IsAEAnnouncingSequence

/-- Almost surely, every approximant of an almost-sure announcing sequence is at most `τ`. -/
theorem ae_le (h : IsAEAnnouncingSequence ℱ P σ τ) : ∀ᵐ ω ∂P, ∀ n, σ n ω ≤ τ ω := by
  filter_upwards [h.monotone, h.tendsto] with ω hmono htend n
  exact hmono.ge_of_tendsto htend n

/-- Almost surely, every approximant of an almost-sure announcing sequence is finite. -/
theorem ae_ne_top (h : IsAEAnnouncingSequence ℱ P σ τ) : ∀ᵐ ω ∂P, ∀ n, σ n ω ≠ ⊤ := by
  filter_upwards [h.ae_le, h.lt] with ω hle hlt n
  by_cases hpos : 0 < τ ω
  · exact ne_top_of_lt (hlt n hpos)
  · exact ne_top_of_le_ne_top WithTop.zero_ne_top ((hle n).trans (not_lt.mp hpos))

/-- Almost surely, `τ` is the supremum of its almost-sure announcing sequence. -/
theorem ae_iSup_eq (h : IsAEAnnouncingSequence ℱ P σ τ) :
    ∀ᵐ ω ∂P, (⨆ n, σ n ω) = τ ω := by
  filter_upwards [h.monotone, h.tendsto] with ω hmono htend
  exact iSup_eq_of_tendsto hmono htend

-- Pointwise fallback approximants used on the exceptional null set when upgrading to a pointwise
-- announcing sequence: `(τ - 1 / (n + 1))^+ ∧ n` on finite values and `n` at infinity.
private def fallbackStep (n : ℕ) : WithTop ℝ≥0 → WithTop ℝ≥0
  | ⊤ => (n : ℝ≥0)
  | (t : ℝ≥0) => min ((n : ℝ≥0) : WithTop ℝ≥0) ((t - 1 / (n + 1 : ℝ≥0) : ℝ≥0) : WithTop ℝ≥0)

private theorem fallbackStep_properties (x : WithTop ℝ≥0) :
    Monotone (fun n ↦ fallbackStep n x) ∧
      Tendsto (fun n ↦ fallbackStep n x) atTop (𝓝 x) ∧
      (∀ n, 0 < x → fallbackStep n x < x) := by
  let trivFiltration : Filtration ℝ≥0 (⊤ : MeasurableSpace PUnit.{1}) :=
    ⟨fun _ ↦ ⊤, fun _ _ _ ↦ le_rfl, fun _ ↦ le_rfl⟩
  cases x with
  | top =>
    have ha := IsAnnouncingSequence.top (ℱ := trivFiltration)
    exact ⟨ha.monotone PUnit.unit, ha.tendsto PUnit.unit, fun n h ↦ ha.lt n PUnit.unit h⟩
  | coe t =>
    have ha := (IsAnnouncingSequence.top (ℱ := trivFiltration)).min t.isAnnouncingSequence_const
    have hmin : min (⊤ : WithTop ℝ≥0) (t : WithTop ℝ≥0) = t := min_top_left _
    refine ⟨ha.monotone PUnit.unit, hmin ▸ ha.tendsto PUnit.unit,
      fun n h ↦ hmin ▸ ha.lt n PUnit.unit (hmin.symm ▸ h)⟩

private theorem measurableSet_fallbackStep_le (hτ : IsStoppingTime ℱ τ) (n : ℕ) (t : ℝ≥0) :
    MeasurableSet {ω | fallbackStep n (τ ω) ≤ t} := by
  by_cases hnt : (n : ℝ≥0) ≤ t
  · have heq : {ω | fallbackStep n (τ ω) ≤ t} = univ := by
      ext ω
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      cases τ ω with
      | top => exact WithTop.coe_le_coe.mpr hnt
      | coe s => exact (min_le_left _ _).trans (WithTop.coe_le_coe.mpr hnt)
    exact heq ▸ MeasurableSet.univ
  · have heq : {ω | fallbackStep n (τ ω) ≤ t} =
        {ω | τ ω ≤ ((t + 1 / (n + 1 : ℝ≥0) : ℝ≥0) : WithTop ℝ≥0)} := by
      ext ω
      simp only [mem_ofPred_eq]
      cases τ ω with
      | top =>
        simp only [fallbackStep, WithTop.coe_le_coe, hnt, top_le_iff, WithTop.coe_ne_top]
      | coe s =>
        simp only [fallbackStep, min_le_iff, WithTop.coe_le_coe, hnt, false_or]
        exact tsub_le_iff_right
    rw [heq]
    exact ℱ.le _ _ (hτ _)

/-- If `τ` is a stopping time and every ambient-measurable `P`-null set belongs to `ℱ 0` (for
instance on `ℱ.ambientNullAugmentation P`), an almost-sure announcing sequence can be modified on an
`ℱ 0`-measurable null envelope to produce a pointwise announcing sequence. -/
theorem exists_isAnnouncingSequence_of_null (h : IsAEAnnouncingSequence ℱ P σ τ)
    (hτ : IsStoppingTime ℱ τ)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) :
    ∃ σ', IsAnnouncingSequence ℱ σ' τ := by
  classical
  let G : Set Ω := {ω | Monotone (fun n ↦ σ n ω) ∧
    Tendsto (fun n ↦ σ n ω) atTop (𝓝 (τ ω)) ∧ (∀ n, 0 < τ ω → σ n ω < τ ω)}
  have hG_ae : G ∈ ae P := by
    filter_upwards [h.monotone, h.tendsto, h.lt] with ω h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hG_null : P Gᶜ = 0 := mem_ae_iff.mp hG_ae
  let N : Set Ω := toMeasurable P Gᶜ
  have hN_meas : MeasurableSet N := measurableSet_toMeasurable P Gᶜ
  have hN_null : P N = 0 := by rw [measure_toMeasurable, hG_null]
  have hN_F0 : MeasurableSet[ℱ 0] N := hnull N hN_meas hN_null
  have hsub : Nᶜ ⊆ G := compl_subset_comm.mp (subset_toMeasurable P Gᶜ)
  refine ⟨fun n ↦ N.piecewise (fun ω ↦ fallbackStep n (τ ω)) (σ n), ?_, ?_, ?_, ?_⟩
  · intro n t
    have heq : {ω | N.piecewise (fun ω ↦ fallbackStep n (τ ω)) (σ n) ω ≤ t} =
        (N ∩ {ω | fallbackStep n (τ ω) ≤ t}) ∪ (Nᶜ ∩ {ω | σ n ω ≤ t}) := by
      ext ω
      simp only [mem_ofPred_eq, mem_union, mem_inter_iff, mem_compl_iff]
      by_cases hω : ω ∈ N <;> simp [hω]
    rw [heq]
    have hleft : MeasurableSet[ℱ t] (N ∩ {ω | fallbackStep n (τ ω) ≤ t}) :=
      ℱ.mono bot_le _ (hnull _ (hN_meas.inter (measurableSet_fallbackStep_le hτ n t))
        (measure_mono_null inter_subset_left hN_null))
    have hright : MeasurableSet[ℱ t] (Nᶜ ∩ {ω | σ n ω ≤ t}) :=
      (ℱ.mono bot_le _ hN_F0.compl).inter (h.isStoppingTime n t)
    exact hleft.union hright
  · intro ω
    by_cases hω : ω ∈ N
    · simpa [hω] using (fallbackStep_properties (τ ω)).1
    · simpa [hω] using (hsub hω).1
  · intro ω
    by_cases hω : ω ∈ N
    · simpa [hω] using (fallbackStep_properties (τ ω)).2.1
    · simpa [hω] using (hsub hω).2.1
  · intro n ω hpos
    by_cases hω : ω ∈ N
    · simpa [hω] using (fallbackStep_properties (τ ω)).2.2 n hpos
    · simpa [hω] using (hsub hω).2.2 n hpos

/-- On a `P`-complete filtration, every almost-sure announcing sequence can be modified on a single
`P`-null set in `ℱ 0` to obtain a pointwise announcing sequence (no measurability assumption on `τ`
is required). -/
theorem exists_isAnnouncingSequence [ℱ.IsComplete P] (h : IsAEAnnouncingSequence ℱ P σ τ) :
    ∃ σ', IsAnnouncingSequence ℱ σ' τ := by
  classical
  let G : Set Ω := {ω | Monotone (fun n ↦ σ n ω) ∧
    Tendsto (fun n ↦ σ n ω) atTop (𝓝 (τ ω)) ∧ (∀ n, 0 < τ ω → σ n ω < τ ω)}
  have hG_ae : G ∈ ae P := by
    filter_upwards [h.monotone, h.tendsto, h.lt] with ω h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hG_null : P Gᶜ = 0 := mem_ae_iff.mp hG_ae
  refine ⟨fun n ↦ G.piecewise (σ n) (fun ω ↦ fallbackStep n (τ ω)), ?_, ?_, ?_, ?_⟩
  · intro n t
    have heq : {ω | G.piecewise (σ n) (fun ω ↦ fallbackStep n (τ ω)) ω ≤ t} =
        (G ∩ {ω | σ n ω ≤ t}) ∪ (Gᶜ ∩ {ω | fallbackStep n (τ ω) ≤ t}) := by
      ext ω
      simp only [mem_ofPred_eq, mem_union, mem_inter_iff, mem_compl_iff]
      by_cases hω : ω ∈ G <;> simp [hω]
    rw [heq]
    have hG_meas : MeasurableSet[ℱ t] G :=
      compl_compl G ▸ (Filtration.IsComplete.measurableSet_of_null hG_null t).compl
    have hright : MeasurableSet[ℱ t] (Gᶜ ∩ {ω | fallbackStep n (τ ω) ≤ t}) :=
      Filtration.IsComplete.measurableSet_of_null
        (measure_mono_null inter_subset_left hG_null) t
    exact (hG_meas.inter (h.isStoppingTime n t)).union hright
  · intro ω
    by_cases hω : ω ∈ G
    · simpa [hω] using hω.1
    · simpa [hω] using (fallbackStep_properties (τ ω)).1
  · intro ω
    by_cases hω : ω ∈ G
    · simpa [hω] using hω.2.1
    · simpa [hω] using (fallbackStep_properties (τ ω)).2.1
  · intro n ω hpos
    by_cases hω : ω ∈ G
    · simpa [hω] using hω.2.2 n hpos
    · simpa [hω] using (fallbackStep_properties (τ ω)).2.2 n hpos

/-- On a `P`-complete filtration, every time admitting an almost-sure announcing sequence is
pointwise predictable. -/
theorem isPredictableTime [ℱ.IsComplete P] (h : IsAEAnnouncingSequence ℱ P σ τ) :
    IsPredictableTime ℱ τ := by
  obtain ⟨σ', hσ'⟩ := h.exists_isAnnouncingSequence
  exact hσ'.isPredictableTime

end IsAEAnnouncingSequence

end AEAnnouncingSequence

end TauCeti

namespace MeasureTheory.IsStoppingTime

section GraphToAnnouncement

variable {Ω : Type*} {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m}
  {P : Measure Ω} [IsFiniteMeasure P] {τ : Ω → WithTop ℝ≥0}

-- Apply the predictable section theorem to the finite graph of `τ` with geometric error `2⁻ᵏ`.
private theorem exists_predictable_graph_section
    (hgraph : MeasurableSet[ℱ.predictable] {p : ℝ≥0 × Ω | τ p.2 = p.1}) (k : ℕ) :
    ∃ D : Ω → WithTop ℝ≥0, TauCeti.IsPredictableTime ℱ D ∧
      (∀ ω, τ ω ≤ D ω) ∧ (∀ ω, D ω ≠ ⊤ → D ω = τ ω) ∧
      P {ω | τ ω ≠ ⊤ ∧ D ω = ⊤} ≤ (2⁻¹ : ℝ≥0∞) ^ k := by
  have hproj : Prod.snd '' {p : ℝ≥0 × Ω | τ p.2 = p.1} = {ω | τ ω ≠ ⊤} := by
    ext ω
    simp only [mem_image, mem_ofPred_eq, Prod.exists, exists_eq_right]
    exact ⟨fun ⟨t, ht⟩ ↦ ht ▸ WithTop.coe_ne_top,
      fun h ↦ let ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp h; ⟨t, ht.symm⟩⟩
  obtain ⟨D, hD, hsec, hmass⟩ := TauCeti.exists_isPredictableTime_section_le_add hgraph P
    (pow_ne_zero k (by simp : (2⁻¹ : ℝ≥0∞) ≠ 0))
  have hD_eq (ω : Ω) (hne : D ω ≠ ⊤) : D ω = τ ω := by
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hne
    exact ht.symm.trans (hsec ω t ht.symm).symm
  have hD_ge (ω : Ω) : τ ω ≤ D ω := by
    by_cases hne : D ω = ⊤
    · exact hne ▸ le_top
    · exact (hD_eq ω hne).ge
  have hsub : {ω | D ω ≠ ⊤} ⊆ {ω | τ ω ≠ ⊤} := by
    intro ω hne
    simp only [mem_ofPred_eq] at hne ⊢
    exact hD_eq ω hne ▸ hne
  have hsdiff : P ({ω | τ ω ≠ ⊤} \ {ω | D ω ≠ ⊤}) ≤ (2⁻¹ : ℝ≥0∞) ^ k :=
    (measure_sdiff_le_iff_le_add hD.isStoppingTime.measurableSet_eq_top.compl.nullMeasurableSet
      hsub (measure_ne_top P _)).mpr (hproj ▸ hmass)
  have heq : {ω | τ ω ≠ ⊤} \ {ω | D ω ≠ ⊤} = {ω | τ ω ≠ ⊤ ∧ D ω = ⊤} := by
    ext ω; simp
  exact ⟨D, hD, hD_ge, hD_eq, heq ▸ hsdiff⟩

private theorem exists_index_measure_le_of_antitone {E : ℕ → Set Ω} (hanti : Antitone E)
    (hmeas : ∀ m, MeasurableSet (E m)) (hempty : (⋂ m, E m) = ∅) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ M : ℕ, P (E M) ≤ ε := by
  have hinf : ⨅ m, P (E m) < ε := by
    rw [← Antitone.measure_iInter hanti (fun m ↦ (hmeas m).nullMeasurableSet)
      ⟨0, measure_ne_top P _⟩, hempty, measure_empty]
    exact hε
  obtain ⟨M, hM⟩ := iInf_lt_iff.mp hinf
  exact ⟨M, hM.le⟩

-- Bound the finite-lag failure event of an announcing sequence at tolerance `1 / (k + 1)`.
private theorem exists_finite_lag_index {D : Ω → WithTop ℝ≥0} {a : ℕ → Ω → WithTop ℝ≥0}
    (ha : TauCeti.IsAnnouncingSequence ℱ a D) (k : ℕ) :
    ∃ M : ℕ,
      P {ω | D ω ≠ ⊤ ∧ a M ω + ((1 / (k + 1 : ℝ≥0) : ℝ≥0) : WithTop ℝ≥0) < D ω} ≤
        (2⁻¹ : ℝ≥0∞) ^ k := by
  let c : ℝ≥0 := 1 / (k + 1 : ℝ≥0)
  have hc : 0 < c := by positivity
  let hD := ha.isStoppingTime_limit
  let E : ℕ → Set Ω := fun m ↦ {ω | D ω ≠ ⊤ ∧ a m ω + (c : WithTop ℝ≥0) < D ω}
  have hmeas (m : ℕ) : MeasurableSet (E m) := by
    have hle : MeasurableSet {ω | D ω ≤ a m ω + (c : WithTop ℝ≥0)} :=
      iSup_le (fun t ↦ ℱ.le t) _
        (hD.measurableSet_le_stopping_time ((ha.isStoppingTime m).add_const_nnreal c)).1
    have hlt : MeasurableSet {ω | a m ω + (c : WithTop ℝ≥0) < D ω} := by
      simpa only [compl_ofPred, not_le] using hle.compl
    simpa only [E, compl_ofPred, ← ofPred_and] using hD.measurableSet_eq_top.compl.inter hlt
  have hanti : Antitone E := fun _ _ hm _ ⟨h1, h2⟩ ↦
    ⟨h1, (add_le_add (ha.monotone _ hm) le_rfl).trans_lt h2⟩
  have hempty : (⋂ m, E m) = ∅ := by
    ext ω
    simp only [E, mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall]
    by_cases htop : D ω = ⊤
    · exact ⟨0, fun h ↦ h.1 htop⟩
    · obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp htop
      by_cases ht0 : t = 0
      · exact ⟨0, fun h ↦ not_lt_of_ge (ht ▸ ht0 ▸ bot_le) h.2⟩
      · have hlt : ((t - c : ℝ≥0) : WithTop ℝ≥0) < D ω :=
          ht ▸ WithTop.coe_lt_coe.mpr (tsub_lt_self (pos_iff_ne_zero.mpr ht0) hc)
        obtain ⟨m, hm⟩ := ((ha.tendsto ω).eventually (isOpen_Ioi.mem_nhds hlt)).exists
        obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.mp (ha.ne_top m ω)
        have hle : D ω ≤ a m ω + (c : WithTop ℝ≥0) := by
          rw [← ht, ← hu, ← WithTop.coe_add, WithTop.coe_le_coe]
          exact tsub_le_iff_right.mp (WithTop.coe_lt_coe.mp (hu ▸ hm)).le
        exact ⟨m, fun h ↦ not_lt_of_ge hle h.2⟩
  exact exists_index_measure_le_of_antitone hanti hmeas hempty (ENNReal.pow_pos (by simp) k)

-- Bound the infinite-escape failure event of an announcing sequence at height `k`.
private theorem exists_infinite_escape_index {D : Ω → WithTop ℝ≥0} {a : ℕ → Ω → WithTop ℝ≥0}
    (ha : TauCeti.IsAnnouncingSequence ℱ a D) (k : ℕ) :
    ∃ M : ℕ, P {ω | D ω = ⊤ ∧ a M ω < ((k : ℝ≥0) : WithTop ℝ≥0)} ≤ (2⁻¹ : ℝ≥0∞) ^ k := by
  let hD := ha.isStoppingTime_limit
  let E : ℕ → Set Ω := fun m ↦ {ω | D ω = ⊤ ∧ a m ω < ((k : ℝ≥0) : WithTop ℝ≥0)}
  have hmeas (m : ℕ) : MeasurableSet (E m) := by
    have hk_lt : MeasurableSet {ω | a m ω < ((k : ℝ≥0) : WithTop ℝ≥0)} :=
      (ha.isStoppingTime m).measurableSpace_le _ ((ha.isStoppingTime m).measurableSet_lt' k)
    simpa only [E, ← ofPred_and] using hD.measurableSet_eq_top.inter hk_lt
  have hanti : Antitone E := fun _ _ hm _ ⟨h1, h2⟩ ↦ ⟨h1, (ha.monotone _ hm).trans_lt h2⟩
  have hempty : (⋂ m, E m) = ∅ := by
    ext ω
    simp only [E, mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall]
    by_cases htop : D ω = ⊤
    · have hlt : ((k : ℝ≥0) : WithTop ℝ≥0) < D ω := htop ▸ WithTop.coe_lt_top (k : ℝ≥0)
      obtain ⟨m, hm⟩ := ((ha.tendsto ω).eventually (isOpen_Ioi.mem_nhds hlt)).exists
      exact ⟨m, fun h ↦ not_lt_of_ge hm.le h.2⟩
    · exact ⟨0, fun h ↦ htop h.1⟩
  exact exists_index_measure_le_of_antitone hanti hmeas hempty (ENNReal.pow_pos (by simp) k)

-- Choose a single index `M` simultaneously bounding both finite-lag and infinite-escape failures.
private theorem exists_announcing_index {D : Ω → WithTop ℝ≥0} {a : ℕ → Ω → WithTop ℝ≥0}
    (ha : TauCeti.IsAnnouncingSequence ℱ a D) (k : ℕ) :
    ∃ M : ℕ,
      P {ω | D ω ≠ ⊤ ∧ a M ω + ((1 / (k + 1 : ℝ≥0) : ℝ≥0) : WithTop ℝ≥0) < D ω} ≤
        (2⁻¹ : ℝ≥0∞) ^ k ∧
      P {ω | D ω = ⊤ ∧ a M ω < ((k : ℝ≥0) : WithTop ℝ≥0)} ≤ (2⁻¹ : ℝ≥0∞) ^ k := by
  obtain ⟨M₁, hM₁⟩ := exists_finite_lag_index (P := P) ha k
  obtain ⟨M₂, hM₂⟩ := exists_infinite_escape_index (P := P) ha k
  refine ⟨max M₁ M₂, le_trans (measure_mono ?_) hM₁, le_trans (measure_mono ?_) hM₂⟩
  · exact fun ω ⟨h1, h2⟩ ↦
      ⟨h1, (add_le_add (ha.monotone ω (le_max_left M₁ M₂)) le_rfl).trans_lt h2⟩
  · exact fun ω ⟨h1, h2⟩ ↦ ⟨h1, (ha.monotone ω (le_max_right M₁ M₂)).trans_lt h2⟩

-- Pathwise convergence and strict announcement for `S n ω = ⨅ k ≥ n, b k ω` on outcomes that
-- eventually avoid all three failure events.
private theorem biInf_tendsto_and_lt {D : ℕ → Ω → WithTop ℝ≥0} {b : ℕ → Ω → WithTop ℝ≥0}
    (hb_le : ∀ k ω, b k ω ≤ D k ω) (hb_ne_top : ∀ k ω, b k ω ≠ ⊤)
    (hb_lt : ∀ k ω, 0 < D k ω → b k ω < D k ω)
    (hD_ge : ∀ k ω, τ ω ≤ D k ω) (hD_eq : ∀ k ω, D k ω ≠ ⊤ → D k ω = τ ω) {ω : Ω}
    (hK_ev : ∀ᶠ k in atTop,
      ω ∉ ({ω | τ ω ≠ ⊤ ∧ D k ω = ⊤} ∪
        ({ω | D k ω ≠ ⊤ ∧ b k ω + ((1 / (k + 1 : ℝ≥0) : ℝ≥0) : WithTop ℝ≥0) < D k ω} ∪
          {ω | D k ω = ⊤ ∧ b k ω < ((k : ℝ≥0) : WithTop ℝ≥0)}))) :
    Tendsto (fun n ↦ ⨅ k ∈ Ici n, b k ω) atTop (𝓝 (τ ω)) ∧
      (∀ n, 0 < τ ω → (⨅ k ∈ Ici n, b k ω) < τ ω) := by
  let trivFiltration : Filtration ℝ≥0 (⊤ : MeasurableSpace PUnit.{1}) :=
    ⟨fun _ ↦ ⊤, fun _ _ _ ↦ le_rfl, fun _ ↦ le_rfl⟩
  obtain ⟨K, hK⟩ := eventually_atTop.mp hK_ev
  cases hτ_val : τ ω with
  | top =>
    refine ⟨tendsto_nhds_top_mono
        (TauCeti.IsAnnouncingSequence.top (ℱ := trivFiltration).tendsto PUnit.unit) ?_,
      fun n _ ↦ (biInf_le (f := fun k ↦ b k ω) (le_rfl : n ≤ n)).trans_lt (hb_ne_top n ω).lt_top⟩
    refine eventually_atTop.mpr ⟨K, fun n hn ↦ le_iInf₂ fun k (hk : n ≤ k) ↦ ?_⟩
    have hD_top : D k ω = ⊤ := top_le_iff.mp (hτ_val ▸ hD_ge k ω)
    have hnot : ¬ b k ω < ((k : ℝ≥0) : WithTop ℝ≥0) := fun hlt ↦
      hK k (hn.trans hk) (Or.inr (Or.inr ⟨hD_top, hlt⟩))
    exact (WithTop.coe_le_coe.mpr (Nat.cast_le.mpr hk)).trans (not_lt.mp hnot)
  | coe t =>
    have hfin (n : ℕ) : D (max n K) ω = t := by
      have hne : D (max n K) ω ≠ ⊤ := fun htop ↦
        hK _ (le_max_right n K) (Or.inl ⟨hτ_val ▸ WithTop.coe_ne_top, htop⟩)
      exact (hD_eq _ ω hne).trans hτ_val
    have hle_all (n : ℕ) : (⨅ k ∈ Ici n, b k ω) ≤ t :=
      (biInf_le (f := fun k ↦ b k ω) (le_max_left n K)).trans
        ((hb_le _ ω).trans (hfin n).le)
    have hge_ev : ∀ᶠ n : ℕ in atTop,
        ((t - 1 / ((n : ℝ≥0) + 1) : ℝ≥0) : WithTop ℝ≥0) ≤ ⨅ k ∈ Ici n, b k ω := by
      refine eventually_atTop.mpr ⟨K, fun n hn ↦ le_iInf₂ fun k (hk : n ≤ k) ↦ ?_⟩
      have hne : D k ω ≠ ⊤ := fun htop ↦
        hK k (hn.trans hk) (Or.inl ⟨hτ_val ▸ WithTop.coe_ne_top, htop⟩)
      have hDk : D k ω = t := (hD_eq k ω hne).trans hτ_val
      have hnot : ¬ b k ω + ((1 / (k + 1 : ℝ≥0) : ℝ≥0) : WithTop ℝ≥0) < D k ω :=
        fun hlt ↦ hK k (hn.trans hk) (Or.inr (Or.inl ⟨hne, hlt⟩))
      obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.mp (hb_ne_top k ω)
      have h1 : t ≤ u + 1 / (k + 1 : ℝ≥0) := by
        have := not_lt.mp hnot
        rwa [hDk, ← hu, ← WithTop.coe_add, WithTop.coe_le_coe] at this
      have htu : t ≤ u + 1 / ((n : ℝ≥0) + 1) := h1.trans (add_le_add le_rfl
        (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hk 1)))
      exact hu ▸ WithTop.coe_le_coe.mpr (tsub_le_iff_right.mpr htu)
    refine ⟨tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (t.isAnnouncingSequence_const (ℱ := trivFiltration).tendsto PUnit.unit) tendsto_const_nhds
      hge_ev (Eventually.of_forall hle_all), fun n hpos ↦ ?_⟩
    exact (biInf_le (f := fun k ↦ b k ω) (le_max_left n K)).trans_lt
      (hfin n ▸ hb_lt _ ω ((hfin n).symm ▸ hτ_val ▸ hpos))

/-- **Graph-to-announcement.** On a right-continuous filtration over a finite measure space, every
random time `τ : Ω → WithTop ℝ≥0` with predictable finite graph `[[τ]]` admits an almost-sure
announcing sequence (including outcomes where `τ = 0` or `τ = ⊤`, and without assuming
completeness or that `τ` is a priori a stopping time). -/
theorem _root_.TauCeti.exists_isAEAnnouncingSequence_of_measurableSet_predictable_eq
    (P : Measure Ω) [IsFiniteMeasure P] [ℱ.IsRightContinuous]
    (hgraph : MeasurableSet[ℱ.predictable] {p : ℝ≥0 × Ω | τ p.2 = p.1}) :
    ∃ σ, TauCeti.IsAEAnnouncingSequence ℱ P σ τ := by
  choose D hD hD_ge hD_eq hD_err using fun k ↦ exists_predictable_graph_section (P := P) hgraph k
  choose a ha using fun k ↦ TauCeti.isPredictableTime_iff.mp (hD k)
  choose M hM₁ hM₂ using fun k ↦ exists_announcing_index (P := P) (ha k) k
  let b : ℕ → Ω → WithTop ℝ≥0 := fun k ↦ a k (M k)
  let S : ℕ → Ω → WithTop ℝ≥0 := fun n ω ↦ ⨅ k ∈ Ici n, b k ω
  have hS_stop (n : ℕ) : IsStoppingTime ℱ (S n) :=
    IsStoppingTime.biInf (Set.to_countable _) fun k _ ↦ (ha k).isStoppingTime (M k)
  have hS_mono (ω : Ω) : Monotone (fun n ↦ S n ω) :=
    fun _ _ h ↦ biInf_mono (Ici_subset_Ici.mpr h)
  let Bad : ℕ → Set Ω := fun k ↦
    {ω | τ ω ≠ ⊤ ∧ D k ω = ⊤} ∪
      ({ω | D k ω ≠ ⊤ ∧ b k ω + ((1 / (k + 1 : ℝ≥0) : ℝ≥0) : WithTop ℝ≥0) < D k ω} ∪
        {ω | D k ω = ⊤ ∧ b k ω < ((k : ℝ≥0) : WithTop ℝ≥0)})
  have hBad_sum : ∑' k, P (Bad k) ≠ ∞ := by
    have hle (k : ℕ) : P (Bad k) ≤ 3 * (2⁻¹ : ℝ≥0∞) ^ k := by
      calc P (Bad k)
        _ ≤ P {ω | τ ω ≠ ⊤ ∧ D k ω = ⊤} +
            (P {ω | D k ω ≠ ⊤ ∧
              b k ω + ((1 / (k + 1 : ℝ≥0) : ℝ≥0) : WithTop ℝ≥0) < D k ω} +
              P {ω | D k ω = ⊤ ∧ b k ω < ((k : ℝ≥0) : WithTop ℝ≥0)}) :=
            (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
        _ ≤ (2⁻¹ : ℝ≥0∞) ^ k + ((2⁻¹ : ℝ≥0∞) ^ k + (2⁻¹ : ℝ≥0∞) ^ k) :=
            add_le_add (hD_err k) (add_le_add (hM₁ k) (hM₂ k))
        _ = 3 * (2⁻¹ : ℝ≥0∞) ^ k := by ring
    refine ne_top_of_le_ne_top ?_
      (CompleteLattice.summable.tsum_le_tsum hle CompleteLattice.summable)
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_two]
    exact by norm_num
  have hBC : ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ω ∉ Bad k := ae_eventually_notMem hBad_sum
  have hpath (ω : Ω) (hω : ∀ᶠ k in atTop, ω ∉ Bad k) :=
    biInf_tendsto_and_lt (fun k ↦ (ha k).le (M k)) (fun k ↦ (ha k).ne_top (M k))
      (fun k ↦ (ha k).lt (M k)) hD_ge hD_eq hω
  refine ⟨S, hS_stop, Eventually.of_forall hS_mono, ?_, ?_⟩
  · filter_upwards [hBC] with ω hω
    exact (hpath ω hω).1
  · filter_upwards [hBC] with ω hω
    exact (hpath ω hω).2

/-- On a right-continuous filtration over a finite measure space, every stopping time with
predictable closed upper ray `[τ, ∞)` admits an almost-sure announcing sequence. -/
theorem exists_isAEAnnouncingSequence_of_measurableSet_predictable_le
    (P : Measure Ω) [IsFiniteMeasure P] [ℱ.IsRightContinuous]
    (hτ : IsStoppingTime ℱ τ)
    (hray : MeasurableSet[ℱ.predictable] {p : ℝ≥0 × Ω | τ p.2 ≤ p.1}) :
    ∃ σ, TauCeti.IsAEAnnouncingSequence ℱ P σ τ :=
  TauCeti.exists_isAEAnnouncingSequence_of_measurableSet_predictable_eq P
    (hτ.measurableSet_predictable_eq_iff_le.mpr hray)

/-- On a right-continuous filtration over a finite measure space containing all ambient-measurable
`P`-null sets at time `0` (for example `ℱ.ambientNullAugmentation P`), a stopping time is pointwise
predictable if and only if its finite graph `[[τ]]` is predictable. -/
theorem isPredictableTime_iff_measurableSet_predictable_eq_of_null
    (P : Measure Ω) [IsFiniteMeasure P] [ℱ.IsRightContinuous]
    (hτ : IsStoppingTime ℱ τ)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) :
    TauCeti.IsPredictableTime ℱ τ ↔
      MeasurableSet[ℱ.predictable] {p : ℝ≥0 × Ω | τ p.2 = p.1} := by
  refine ⟨fun h ↦ h.measurableSet_predictable_eq, fun h ↦ ?_⟩
  obtain ⟨σ, hσ⟩ := TauCeti.exists_isAEAnnouncingSequence_of_measurableSet_predictable_eq P h
  obtain ⟨σ', hσ'⟩ := hσ.exists_isAnnouncingSequence_of_null hτ hnull
  exact hσ'.isPredictableTime

end GraphToAnnouncement

end MeasureTheory.IsStoppingTime

namespace TauCeti

variable {Ω : Type*} {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m}
  {τ : Ω → WithTop ℝ≥0}

/-- On a `P`-complete filtration, a random time is pointwise predictable if and only if it admits an
almost-sure announcing sequence. -/
theorem isPredictableTime_iff_exists_isAEAnnouncingSequence
    (P : Measure Ω) [ℱ.IsComplete P] :
    IsPredictableTime ℱ τ ↔ ∃ σ, IsAEAnnouncingSequence ℱ P σ τ :=
  ⟨fun h ↦ let ⟨σ, hσ⟩ := isPredictableTime_iff.mp h; ⟨σ, hσ.isAEAnnouncingSequence P⟩,
    fun ⟨_, hσ⟩ ↦ hσ.isPredictableTime⟩

/-- **Characterization of predictable times by their graphs** (Dellacherie–Meyer, IV.71;
Theodorakopoulos, Corollary 4.5). On a complete right-continuous finite-measure basis, an arbitrary
random time `τ : Ω → WithTop ℝ≥0` (not assumed a priori to be a stopping time) is pointwise
predictable if and only if its finite graph `[[τ]]` is predictable. -/
theorem isPredictableTime_iff_measurableSet_predictable_eq
    (P : Measure Ω) [IsFiniteMeasure P] [ℱ.IsRightContinuous] [ℱ.IsComplete P] :
    IsPredictableTime ℱ τ ↔ MeasurableSet[ℱ.predictable] {p : ℝ≥0 × Ω | τ p.2 = p.1} := by
  refine ⟨fun h ↦ h.measurableSet_predictable_eq, fun h ↦ ?_⟩
  obtain ⟨_, hσ⟩ := exists_isAEAnnouncingSequence_of_measurableSet_predictable_eq P h
  exact hσ.isPredictableTime

/-- **Characterization of predictable times by their closed upper rays.** On a complete
right-continuous finite-measure basis, an arbitrary random time `τ : Ω → WithTop ℝ≥0` (not assumed a
priori to be a stopping time) is pointwise predictable if and only if its closed upper ray `[τ, ∞)`
is predictable. -/
theorem isPredictableTime_iff_measurableSet_predictable_le
    (P : Measure Ω) [IsFiniteMeasure P] [ℱ.IsRightContinuous] [ℱ.IsComplete P] :
    IsPredictableTime ℱ τ ↔ MeasurableSet[ℱ.predictable] {p : ℝ≥0 × Ω | τ p.2 ≤ p.1} := by
  refine ⟨fun h ↦ h.measurableSet_predictable_le, fun h ↦ ?_⟩
  have hτ : IsStoppingTime ℱ τ := by
    simpa only [debut_le] using (ℱ.predictable_le_progressive _ h).isStoppingTime_debut P
  obtain ⟨_, hσ⟩ := hτ.exists_isAEAnnouncingSequence_of_measurableSet_predictable_le P h
  exact hσ.isPredictableTime

end TauCeti
