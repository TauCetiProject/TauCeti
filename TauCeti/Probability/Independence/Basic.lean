/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic
import Mathlib.Data.Finset.Powerset
import TauCeti.Probability.HasLaw

/-!
# Basic criteria for independence

A dependent family of random variables is independent if all but at most one coordinate are
almost surely constant; no measurability assumption or restriction on the index type is needed
(`TauCeti.Probability.iIndepFun_of_ae_eq_const_outside_subsingleton`).

Under a zero or probability measure `P`, a random variable `Z` is independent of a sub-σ-algebra `m`
whenever restricting `P` to every `m`-measurable event `A` (or `A ∩ F` for an almost-surely holding
event `F`) gives `Z` the scalar-multiple law `P A • ν` (respectively `P (A ∩ F) • ν`): see
`ProbabilityTheory.indep_comap_of_forall_hasLaw_restrict` and
`ProbabilityTheory.indep_comap_of_forall_hasLaw_restrict_inter`.

Two independent functions force a finite measure to be zero or a probability measure
(`ProbabilityTheory.IndepFun.isZeroOrProbabilityMeasure`), and under a measure of infinite total
mass all their measurable cells and preimages have real mass zero
(`ProbabilityTheory.IndepFun.measureReal_inter_preimage_eq_zero_of_measure_univ_eq_top`,
`ProbabilityTheory.IndepFun.measureReal_preimage_eq_zero_of_measure_univ_eq_top`).

An independent, identically distributed family admits a measurable version agreeing almost
everywhere at each index, preserving independence and identical distribution
(`ProbabilityTheory.iIndepFun.exists_measurable_ae_eq_of_identDistrib`). Preimages of measurable
sets under the coordinates of an independent family are independent events, whether or not the
coordinates are measurable (`ProbabilityTheory.iIndepFun.iIndepSet_preimage`).

Under a finite measure, two measurable random variables with countably many values are independent
as soon as every cell `f ⁻¹' {a} ∩ g ⁻¹' {b}` has the product mass of `f ⁻¹' {a}` and `g ⁻¹' {b}`
(`TauCeti.Probability.indepFun_of_measureReal_preimage_singleton_inter_eq_mul`).

Independence within rows also gives a union bound for row counts. For a finite array of events
whose rows consist of independent events of measure at most `p`, the measure that some row
contains at least `q` occurring events is at most `p ^ q` times the sum over rows of the number of
`q`-element subsets of the row indices (`TauCeti.Probability.measure_exists_le_card_filter_mem_le`).
No separate `[IsProbabilityMeasure μ]` argument is needed: whenever some row is nonempty, its
independence hypothesis already makes `μ` a probability measure. For rows of independent random
variables of length at most `N`, the measure that some row has at least `q` entries of norm above
`R` is at most `card ι * N ^ q * τ ^ q`, where `τ` bounds each entry tail
(`TauCeti.Probability.measure_exists_le_card_filter_lt_norm_le`).
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace TauCeti.Probability

variable {Ω ι : Type*} {β : ι → Type*} [MeasurableSpace Ω]
  [∀ i, MeasurableSpace (β i)] {μ : Measure Ω}

open scoped Classical in
/-- For a finite array of events, each row consisting of independent events with measures at
most `p`, the measure that some row contains at least `q` occurring events is bounded by
`p ^ q` times the sum, over rows, of the number of `q`-element subsets of entry indices
in that row. -/
theorem measure_exists_le_card_filter_mem_le {κ : ι → Type*} [Fintype ι]
    [∀ i, Fintype (κ i)] (E : (i : ι) → κ i → Set Ω) (hE : ∀ i, iIndepSet (E i) μ)
    {p : ℝ≥0∞} (hp : ∀ i j, μ (E i j) ≤ p) (q : ℕ) :
    μ {ω | ∃ i, q ≤ (Finset.univ.filter fun j ↦ ω ∈ E i j).card} ≤
      ∑ i, ((Fintype.card (κ i)).choose q : ℝ≥0∞) * p ^ q := by
  let U (i : ι) := ⋃ S ∈ (Finset.univ : Finset (κ i)).powersetCard q, ⋂ j ∈ S, E i j
  have hcover : {ω | ∃ i, q ≤ (Finset.univ.filter fun j ↦ ω ∈ E i j).card} ⊆ ⋃ i, U i := by
    rintro ω ⟨i, hi⟩
    obtain ⟨S, hsub, hcard⟩ := Finset.exists_subset_card_eq hi
    refine mem_iUnion.2 ⟨i, mem_iUnion₂.2 ⟨S, Finset.mem_powersetCard.2 ⟨
      Finset.subset_univ _, hcard⟩, ?_⟩⟩
    exact mem_iInter₂.2 fun j hj ↦ (Finset.mem_filter.1 (hsub hj)).2
  refine ((measure_mono hcover).trans (measure_iUnion_fintype_le μ U)).trans ?_
  refine Finset.sum_le_sum fun i _ ↦ (measure_biUnion_finset_le _ _).trans ?_
  calc
    _ ≤ ∑ _S ∈ (Finset.univ : Finset (κ i)).powersetCard q, p ^ q := by
      refine Finset.sum_le_sum fun S hS ↦ ?_
      rw [(hE i).meas_biInter, ← (Finset.mem_powersetCard.1 hS).2, ← Finset.prod_const]
      exact Finset.prod_le_prod fun j _ ↦ hp i j
    _ = _ := by simp [Finset.card_powersetCard, nsmul_eq_mul]

variable [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- An independent restriction remains independent when the other coordinates are almost
surely constant. The constants and the exceptional null sets may depend on the coordinate. -/
theorem _root_.ProbabilityTheory.iIndepFun.of_subtype_of_ae_eq_const_outside
    {f : ∀ i, Ω → β i} {s : Set ι}
    (h : iIndepFun (fun i : s ↦ f i.val) μ)
    (hf : ∀ i ∉ s, ∃ c, f i =ᵐ[μ] fun _ ↦ c) : iIndepFun f μ := by
  classical
  have := h.isProbabilityMeasure
  let g (i : ι) : Ω → β i :=
    if hi : i ∈ s then f i else fun _ ↦ (hf i hi).choose
  have hfg (i : ι) : f i =ᵐ[μ] g i := by
    dsimp [g]
    split_ifs with hi
    · exact Filter.EventuallyEq.rfl
    · exact (hf i hi).choose_spec
  suffices hg : iIndepFun g μ from hg.congr (fun i ↦ (hfg i).symm)
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hs
  by_cases hbad : ∃ i ∈ S, ∃ c, g i = (fun _ ↦ c) ∧ c ∉ sets i
  · obtain ⟨i, hi, c, hgi, hci⟩ := hbad
    have hempty : g i ⁻¹' sets i = ∅ := by simp [hgi, hci]
    have hInter : (⋂ j ∈ S, g j ⁻¹' sets j) = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun ω hω ↦ by
        have := Set.mem_iInter₂.mp hω i hi
        simp only [hempty, Set.mem_empty_iff_false] at this
    rw [hInter, measure_empty]
    exact (Finset.prod_eq_zero hi (by rw [hempty, measure_empty])).symm
  have hfull (i : ι) (hi : i ∈ S) (hsi : i ∉ s) : g i ⁻¹' sets i = Set.univ := by
    have hg : g i = fun _ ↦ (hf i hsi).choose := by simp [g, hsi]
    have hci : (hf i hsi).choose ∈ sets i := by
      by_contra hn
      exact hbad ⟨i, hi, _, hg, hn⟩
    simp [hg, hci]
  let T := S.subtype (· ∈ s)
  have h' := h.measure_inter_preimage_eq_mul T (sets := fun i ↦ sets i)
    (fun i hi ↦ hs i (Finset.mem_subtype.mp hi))
  have hInter : (⋂ j ∈ S, g j ⁻¹' sets j) = ⋂ j ∈ T, f j.val ⁻¹' sets j := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_preimage]
    refine ⟨fun hw i hi ↦ ?_, fun hw i hi ↦ ?_⟩
    · simpa [g, i.property] using hw i (Finset.mem_subtype.mp hi)
    · by_cases his : i ∈ s
      · simpa [g, his] using hw ⟨i, his⟩ (Finset.mem_subtype.mpr hi)
      · have hmem : ω ∈ g i ⁻¹' sets i := (hfull i hi his).symm ▸ Set.mem_univ ω
        exact hmem
  rw [hInter, h']
  calc
    _ = ∏ j ∈ S.filter (· ∈ s), μ (f j ⁻¹' sets j) := Finset.prod_subtype_eq_prod_filter _
    _ = ∏ j ∈ S.filter (· ∈ s), μ (g j ⁻¹' sets j) :=
      Finset.prod_congr rfl fun j hj ↦ by simp [g, (Finset.mem_filter.mp hj).2]
    _ = _ := Finset.prod_subset (Finset.filter_subset _ _) fun j hj hjs ↦ by
      rw [hfull j hj (fun hjs' ↦ hjs (Finset.mem_filter.mpr ⟨hj, hjs'⟩)), measure_univ]

/-- A family is independent if its coordinates are almost surely constant outside a subsingleton
set of indices. The constants and the exceptional null sets may depend on the coordinate. -/
theorem iIndepFun_of_ae_eq_const_outside_subsingleton {f : ∀ i, Ω → β i} {s : Set ι}
    (hs : s.Subsingleton) (hf : ∀ i ∉ s, ∃ c, f i =ᵐ[μ] fun _ => c) :
    iIndepFun f μ := by
  let : Subsingleton s := ⟨fun i j ↦ Subtype.ext (hs i.property j.property)⟩
  exact (iIndepFun.of_subsingleton (f := fun i : s ↦ f i.val)).of_subtype_of_ae_eq_const_outside hf

end TauCeti.Probability

namespace ProbabilityTheory

open Set

variable {Ω β : Type*} [MeasurableSpace β]

/-- Under a zero or probability measure `P`, if restricting `P` to every event `A` of a
sub-σ-algebra `m` gives `Z` the law `P A • ν`, then `Z` is independent of `m`. Measurability of `Z`
in the ambient σ-algebra is not required beyond the almost-everywhere measurability carried by
`HasLaw`. -/
theorem indep_comap_of_forall_hasLaw_restrict {m mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsZeroOrProbabilityMeasure P] {ν : Measure β} {Z : Ω → β} (hm : m ≤ mΩ)
    (h : ∀ A, MeasurableSet[m] A → HasLaw Z (P A • ν) (P.restrict A)) :
    Indep (.comap Z inferInstance) m P := by
  rcases eq_zero_or_isProbabilityMeasure P with rfl | hP
  · simp [Indep_iff]
  have hZ : HasLaw Z ν P := by simpa using h univ .univ
  rw [Indep_iff]
  rintro _ A ⟨C, hC, rfl⟩ hA
  have hZA := h A hA
  calc
    P (Z ⁻¹' C ∩ A) = P.restrict A (Z ⁻¹' C) := (Measure.restrict_apply' (hm A hA)).symm
    _ = Measure.map Z (P.restrict A) C :=
      (Measure.map_apply_of_aemeasurable hZA.aemeasurable hC).symm
    _ = (P A • ν) C := by rw [hZA.map_eq]
    _ = ν C * P A := by simp [mul_comm]
    _ = Measure.map Z P C * P A := by rw [hZ.map_eq]
    _ = P (Z ⁻¹' C) * P A := by rw [Measure.map_apply_of_aemeasurable hZ.aemeasurable hC]

/-- Under a zero or probability measure, restricted scalar-multiple laws on `A ∩ F` for every
`m`-event `A` and an almost-surely holding event `F` imply that `Z` is independent of `m`. -/
theorem indep_comap_of_forall_hasLaw_restrict_inter {m mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsZeroOrProbabilityMeasure P] {ν : Measure β} {Z : Ω → β} {F : Set Ω} (hm : m ≤ mΩ)
    (hF : ∀ᵐ ω ∂P, ω ∈ F)
    (h : ∀ A, MeasurableSet[m] A → HasLaw Z (P (A ∩ F) • ν) (P.restrict (A ∩ F))) :
    Indep (.comap Z inferInstance) m P :=
  indep_comap_of_forall_hasLaw_restrict hm fun A hA ↦ (h A hA).of_restrict_inter_of_ae_mem hF

/-- Every independent, identically distributed family of random variables admits a measurable
version agreeing almost everywhere at each index, preserving independence, identical distribution
within the family, and identical distribution with each original coordinate. -/
theorem iIndepFun.exists_measurable_ae_eq_of_identDistrib {Ω ι α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] {P : Measure Ω} {X : ι → Ω → α} {i₀ : ι}
    (hindep : iIndepFun X P) (hid : ∀ i, IdentDistrib (X i) (X i₀) P P) :
    ∃ X' : ι → Ω → α, (∀ i, Measurable (X' i)) ∧ (∀ i, X i =ᵐ[P] X' i) ∧
      iIndepFun X' P ∧ (∀ i, IdentDistrib (X' i) (X' i₀) P P) ∧
      ∀ i, IdentDistrib (X' i) (X i) P P := by
  let X' : ι → Ω → α := fun i ↦ (hid i).aemeasurable_fst.mk (X i)
  have hX'_ae (i : ι) : X i =ᵐ[P] X' i := (hid i).aemeasurable_fst.ae_eq_mk
  refine ⟨X', fun i ↦ (hid i).aemeasurable_fst.measurable_mk, hX'_ae, hindep.congr hX'_ae,
    fun i ↦ ((hid i).aemeasurable_fst.identDistrib_mk.symm.trans (hid i)).trans
      (hid i₀).aemeasurable_fst.identDistrib_mk,
    fun i ↦ (hid i).aemeasurable_fst.identDistrib_mk.symm⟩

/-- Preimages of measurable sets under the coordinates of an independent family are independent
events. The coordinates need not be measurable, so these events need not be measurable in the
ambient σ-algebra. -/
theorem iIndepFun.iIndepSet_preimage {Ω ι : Type*} {β : ι → Type*} [MeasurableSpace Ω]
    [∀ i, MeasurableSpace (β i)] {P : Measure Ω} {f : ∀ i, Ω → β i} (h : iIndepFun f P)
    {s : ∀ i, Set (β i)} (hs : ∀ i, MeasurableSet (s i)) :
    iIndepSet (fun i ↦ f i ⁻¹' s i) P := by
  rw [iIndepSet_iff_iIndep]
  exact iIndep_of_iIndep_of_le h.iIndep fun i ↦ MeasurableSpace.generateFrom_singleton_le <|
    MeasurableSpace.measurableSet_comap.2 ⟨s i, hs i, rfl⟩

/-- Two independent functions under a finite measure force the measure to be zero or a
probability measure, since `μ univ = μ univ * μ univ`. -/
theorem IndepFun.isZeroOrProbabilityMeasure {Ω γ : Type*} {mΩ : MeasurableSpace Ω}
    [MeasurableSpace γ] {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → β} {g : Ω → γ}
    (h : IndepFun f g μ) : IsZeroOrProbabilityMeasure μ := by
  have huniv : μ univ = μ univ * μ univ := by
    simpa using h.measure_inter_preimage_eq_mul univ univ .univ .univ
  refine ⟨(eq_or_ne (μ univ) 0).imp_right fun h0 ↦ ?_⟩
  exact (ENNReal.mul_eq_left h0 (measure_ne_top μ univ)).mp huniv.symm

/-- Under a measure of infinite total mass, two independent functions have cells
`f ⁻¹' s ∩ g ⁻¹' t` of real mass zero: every measurable preimage under `f` has mass `0` or `∞`. -/
theorem IndepFun.measureReal_inter_preimage_eq_zero_of_measure_univ_eq_top {Ω γ : Type*}
    {mΩ : MeasurableSpace Ω} [MeasurableSpace γ] {μ : Measure Ω} {f : Ω → β} {g : Ω → γ}
    (h : IndepFun f g μ) (hμ : μ univ = ∞) {s : Set β} {t : Set γ} (hs : MeasurableSet s)
    (ht : MeasurableSet t) : μ.real (f ⁻¹' s ∩ g ⁻¹' t) = 0 := by
  have hf : μ (f ⁻¹' s) = μ (f ⁻¹' s) * ∞ := by
    simpa [hμ] using h.measure_inter_preimage_eq_mul s univ hs .univ
  rw [measureReal_def, h.measure_inter_preimage_eq_mul s t hs ht, ENNReal.toReal_mul, hf,
    ENNReal.toReal_mul_top, zero_mul]

/-- Under a measure of infinite total mass, the measurable preimages under a function independent
of another function have real mass zero. Apply it to `h.symm` for the second function. -/
theorem IndepFun.measureReal_preimage_eq_zero_of_measure_univ_eq_top {Ω γ : Type*}
    {mΩ : MeasurableSpace Ω} [MeasurableSpace γ] {μ : Measure Ω} {f : Ω → β} {g : Ω → γ}
    (h : IndepFun f g μ) (hμ : μ univ = ∞) {s : Set β} (hs : MeasurableSet s) :
    μ.real (f ⁻¹' s) = 0 := by
  simpa using h.measureReal_inter_preimage_eq_zero_of_measure_univ_eq_top hμ hs .univ

end ProbabilityTheory

namespace TauCeti.Probability

variable {Ω ι E : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SeminormedAddGroup E]
  [MeasurableSpace E] [OpensMeasurableSpace E]

/-- For a finite family of rows of random variables, each row independent and with at most `N`
entries, the measure of the set where some row has at least `q` entries of norm strictly above
`R` is at most `card ι * N ^ q * τ ^ q`, where `τ` bounds the measure of each entry exceeding `R`.
The entries need not be measurable, so this bounds an outer measure in general. -/
theorem measure_exists_le_card_filter_lt_norm_le {κ : ι → Type*} [Fintype ι]
    [∀ i, Fintype (κ i)] {Y : (i : ι) → κ i → Ω → E} (hind : ∀ i, iIndepFun (Y i) μ) (R : ℝ)
    {τ : ℝ≥0∞} (htail : ∀ i j, μ {ω | R < ‖Y i j ω‖} ≤ τ) {N : ℕ}
    (hN : ∀ i, Fintype.card (κ i) ≤ N) (q : ℕ) :
    μ {ω | ∃ i, q ≤ (Finset.univ.filter fun j ↦ R < ‖Y i j ω‖).card} ≤
      Fintype.card ι * (N : ℝ≥0∞) ^ q * τ ^ q := by
  have hE (i : ι) : iIndepSet (fun j ↦ {ω | R < ‖Y i j ω‖}) μ :=
    (hind i).iIndepSet_preimage (s := fun _ ↦ {z : E | R < ‖z‖})
      fun _ ↦ measurableSet_lt measurable_const continuous_norm.measurable
  calc
    _ ≤ μ {ω | ∃ i, q ≤ (Finset.univ.filter fun j ↦ ω ∈ {ω | R < ‖Y i j ω‖}).card} :=
      -- The two filters differ only in their decidability instances.
      measure_mono fun ω ↦ by
        rintro ⟨i, hi⟩
        exact ⟨i, by convert hi⟩
    _ ≤ ∑ i, ((Fintype.card (κ i)).choose q : ℝ≥0∞) * τ ^ q :=
      measure_exists_le_card_filter_mem_le _ hE htail q
    _ ≤ ∑ _i : ι, (N : ℝ≥0∞) ^ q * τ ^ q := by
      gcongr with i
      exact_mod_cast (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (hN i) q)
    _ = _ := by simp [mul_assoc]

end TauCeti.Probability

namespace TauCeti.Probability

variable {Ω α β : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Countable β] [MeasurableSpace β] [MeasurableSingletonClass β]

/-- Two measurable random variables with countably many values are independent when the mass of
each cell `f ⁻¹' {a} ∩ g ⁻¹' {b}` is the product of the masses of `f ⁻¹' {a}` and `g ⁻¹' {b}`. -/
theorem indepFun_of_measureReal_preimage_singleton_inter_eq_mul {f : Ω → α} {g : Ω → β}
    (hf : Measurable f) (hg : Measurable g)
    (h : ∀ a b, μ.real (f ⁻¹' {a} ∩ g ⁻¹' {b}) = μ.real (f ⁻¹' {a}) * μ.real (g ⁻¹' {b})) :
    IndepFun f g μ := by
  rw [indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable,
    Measure.ext_iff_singleton]
  rintro ⟨a, b⟩
  rw [Measure.map_apply (hf.prodMk hg) (measurableSet_singleton _), ← singleton_prod_singleton,
    Measure.prod_prod, Measure.map_apply hf (measurableSet_singleton _),
    Measure.map_apply hg (measurableSet_singleton _), mk_preimage_prod]
  -- The cell identity `h a b` holds in `ℝ`; lift it to `ℝ≥0∞` through the finite masses.
  rw [← ofReal_measureReal, h, ENNReal.ofReal_mul measureReal_nonneg, ofReal_measureReal,
    ofReal_measureReal]

end TauCeti.Probability
