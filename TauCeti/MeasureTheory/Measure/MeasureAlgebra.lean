/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.Topology.Order.Lattice

/-!
# The measure algebra of a measure

The *measure algebra* of a measure `μ` on `α` is the Boolean algebra of measurable sets modulo
`μ`-null sets: two measurable sets are identified when their symmetric difference is null. It
carries the Fréchet–Nikodym extended metric `edist [s] [t] = μ (s ∆ t)`, a genuine metric when `μ`
is finite, and the measure descends to it.

We realize it as the separation quotient of Mathlib's pseudo-extended-metric space
`MeasureTheory.MeasuredSets μ`, so that its metric and topology are those of the quotient, and
we descend the Boolean operations of sets to it. Union, intersection, complement and difference
are Lipschitz for this metric, and the measure of a class is additive on disjoint classes.

For a finite measure, the class of `s` determines the class `[𝟙_s c]` in `Lᵖ(μ; E)`, and
`‖[𝟙_s c] - [𝟙_t c]‖_p = ‖c‖ μ(s ∆ t)^(1/p)` for `0 < p < ∞`. Through this map the measure algebra
of a finite measure is separable exactly when `Lᵖ(μ; E)` is, for any `1 ≤ p < ∞` and any nonzero
separable normed space `E` (in particular for scalar `L²`), and exactly when `μ` is separable in
the sense of `MeasureTheory.IsSeparable`.

## Main declarations

* `TauCeti.MeasureAlgebra μ`: the measure algebra of `μ`, with `TauCeti.MeasureAlgebra.mk s hs`
  the class of a measurable set `s`; `TauCeti.MeasureAlgebra.mk_eq_mk` characterizes equality of
  classes by almost-everywhere equality of sets.
* `TauCeti.MeasureAlgebra.instBooleanAlgebra`: the Boolean algebra structure, with
  `TauCeti.MeasureAlgebra.mk_sup`, `mk_inf`, `mk_compl`, `mk_sdiff` and
  `TauCeti.MeasureAlgebra.mk_le_mk`.
* `TauCeti.MeasureAlgebra.measure`: the measure of a class, with
  `TauCeti.MeasureAlgebra.measure_sup_add_measure_inf` and
  `TauCeti.MeasureAlgebra.measure_eq_zero_iff`.
* `TauCeti.MeasureAlgebra.edist_eq_measure_symmDiff`: `edist a b = (a ∆ b).measure`; the lattice
  operations are continuous (`TauCeti.MeasureAlgebra.instTopologicalLattice`) and complement is an
  isometry (`TauCeti.MeasureAlgebra.isometry_compl`).
* `TauCeti.MeasureAlgebra.indicatorConstLp`: the class of `𝟙_s c` in `Lᵖ(μ; E)` for a finite
  measure, with its distance formula `TauCeti.MeasureAlgebra.dist_indicatorConstLp`.
* `TauCeti.MeasureAlgebra.isSeparable_iff_separableSpace` and
  `TauCeti.MeasureAlgebra.separableSpace_iff_separableSpace_Lp`: separability of the measure
  algebra of a finite measure.

## References

* P. R. Halmos, *Measure Theory*, Van Nostrand, 1950, §40 (the metric space of a measure ring).
* D. H. Fremlin, *Measure Theory*, Volume 3, Torres Fremlin, 2002, §§321 and 323 (measure
  algebras and their topology).
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace Function Filter
open scoped ENNReal symmDiff

namespace MeasureTheory.MeasuredSets

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Two measurable sets are inseparable in `MeasuredSets μ` exactly when they agree almost
everywhere. -/
theorem inseparable_iff_ae_eq {s t : MeasuredSets μ} :
    Inseparable s t ↔ (s : Set α) =ᵐ[μ] t := by
  rw [EMetric.inseparable_iff, edist_def, measure_symmDiff_eq_zero_iff]

end MeasureTheory.MeasuredSets

namespace TauCeti

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

variable (μ) in
/-- The measure algebra of `μ`: measurable sets modulo `μ`-null sets, realized as the separation
quotient of the pseudo-extended-metric space `MeasureTheory.MeasuredSets μ`, whose distance is
`edist s t = μ (s ∆ t)`. -/
@[expose] def MeasureAlgebra : Type _ := SeparationQuotient (MeasuredSets μ)

namespace MeasureAlgebra

instance : EMetricSpace (MeasureAlgebra μ) :=
  inferInstanceAs (EMetricSpace (SeparationQuotient (MeasuredSets μ)))

/-- The class of a measurable set in the measure algebra. -/
def mk (s : Set α) (hs : MeasurableSet s) : MeasureAlgebra μ :=
  SeparationQuotient.mk (Subtype.mk s hs : MeasuredSets μ)

variable {s t : Set α} {hs : MeasurableSet s} {ht : MeasurableSet t}

/-- Induction principle for the measure algebra: every element is the class of a measurable
set. -/
@[elab_as_elim]
theorem ind {p : MeasureAlgebra μ → Prop} (h : ∀ s hs, p (mk s hs)) (a : MeasureAlgebra μ) :
    p a :=
  SeparationQuotient.surjective_mk.forall.2 (fun s : MeasuredSets μ ↦ h s.val s.property) a

theorem exists_mk_eq (a : MeasureAlgebra μ) : ∃ s hs, mk s hs = a :=
  ind (fun s hs ↦ ⟨s, hs, rfl⟩) a

/-- Two measurable sets have the same class exactly when they agree almost everywhere. -/
@[simp]
theorem mk_eq_mk : (mk s hs : MeasureAlgebra μ) = mk t ht ↔ s =ᵐ[μ] t :=
  SeparationQuotient.mk_eq_mk.trans MeasuredSets.inseparable_iff_ae_eq

theorem mk_eq_mk_iff_measure_symmDiff : (mk s hs : MeasureAlgebra μ) = mk t ht ↔ μ (s ∆ t) = 0 :=
  mk_eq_mk.trans measure_symmDiff_eq_zero_iff.symm

theorem mk_congr (h : s = t) : (mk s hs : MeasureAlgebra μ) = mk t ht := by
  subst h; rfl

/-! ### Boolean operations -/

/-- The Boolean algebra of the measure algebra. The order is almost-everywhere inclusion of
representatives (`TauCeti.MeasureAlgebra.mk_le_mk`) and the operations are those of
representatives (`TauCeti.MeasureAlgebra.mk_sup` and its companions). -/
instance instBooleanAlgebra : BooleanAlgebra (MeasureAlgebra μ) where
  -- On classes of sets the order and the operations reduce to those of representatives, so each
  -- axiom below is checked on representatives.
  le := SeparationQuotient.lift₂ (fun s t : MeasuredSets μ ↦ (s : Set α) ≤ᵐ[μ] t)
    fun _ _ _ _ hs ht ↦ propext
      ⟨fun h ↦ h.congr (MeasuredSets.inseparable_iff_ae_eq.1 hs)
          (MeasuredSets.inseparable_iff_ae_eq.1 ht),
        fun h ↦ h.congr (MeasuredSets.inseparable_iff_ae_eq.1 hs).symm
          (MeasuredSets.inseparable_iff_ae_eq.1 ht).symm⟩
  le_refl a := by
    induction a using ind with | h s _ => exact EventuallySubset.refl (ae μ) s
  le_trans a b c := by
    induction a using ind with | h s hs => ?_
    induction b using ind with | h t ht => ?_
    induction c using ind with | h u hu => ?_
    exact fun (hst : s ≤ᵐ[μ] t) (htu : t ≤ᵐ[μ] u) ↦ hst.trans htu
  le_antisymm a b := by
    induction a using ind with | h s hs => ?_
    induction b using ind with | h t ht => ?_
    exact fun (hst : s ≤ᵐ[μ] t) (hts : t ≤ᵐ[μ] s) ↦ mk_eq_mk.2 (hst.antisymm hts)
  sup := SeparationQuotient.lift₂
    (fun s t : MeasuredSets μ ↦ mk ((s : Set α) ∪ t) (s.property.union t.property))
    fun _ _ _ _ hs ht ↦ mk_eq_mk.2 <| ae_eq_set_union
      (MeasuredSets.inseparable_iff_ae_eq.1 hs) (MeasuredSets.inseparable_iff_ae_eq.1 ht)
  le_sup_left a b := by
    induction a using ind with | h s hs => ?_
    induction b using ind with | h t ht => ?_
    exact EventuallySubset.of_subset (subset_union_left : s ⊆ s ∪ t)
  le_sup_right a b := by
    induction a using ind with | h s hs => ?_
    induction b using ind with | h t ht => ?_
    exact EventuallySubset.of_subset (subset_union_right : t ⊆ s ∪ t)
  sup_le a b c := by
    induction a using ind with | h s hs => ?_
    induction b using ind with | h t ht => ?_
    induction c using ind with | h u hu => ?_
    exact fun (hsu : s ≤ᵐ[μ] u) (htu : t ≤ᵐ[μ] u) ↦
      (hsu.union htu).trans (EventuallySubset.of_subset (union_self u).le)
  inf := SeparationQuotient.lift₂
    (fun s t : MeasuredSets μ ↦ mk ((s : Set α) ∩ t) (s.property.inter t.property))
    fun _ _ _ _ hs ht ↦ mk_eq_mk.2 <| ae_eq_set_inter
      (MeasuredSets.inseparable_iff_ae_eq.1 hs) (MeasuredSets.inseparable_iff_ae_eq.1 ht)
  inf_le_left a b := by
    induction a using ind with | h s hs => ?_
    induction b using ind with | h t ht => ?_
    exact EventuallySubset.of_subset (inter_subset_left : s ∩ t ⊆ s)
  inf_le_right a b := by
    induction a using ind with | h s hs => ?_
    induction b using ind with | h t ht => ?_
    exact EventuallySubset.of_subset (inter_subset_right : s ∩ t ⊆ t)
  le_inf a b c := by
    induction a using ind with | h s hs => ?_
    induction b using ind with | h t ht => ?_
    induction c using ind with | h u hu => ?_
    exact fun (hst : s ≤ᵐ[μ] t) (hsu : s ≤ᵐ[μ] u) ↦
      (EventuallySubset.of_subset (inter_self s).ge).trans (hst.inter hsu)
  le_sup_inf a b c := by
    induction a using ind with | h s hs => ?_
    induction b using ind with | h t ht => ?_
    induction c using ind with | h u hu => ?_
    exact EventuallySubset.of_subset (union_inter_distrib_left s t u).ge
  compl := SeparationQuotient.lift (fun s : MeasuredSets μ ↦ mk (s : Set α)ᶜ s.property.compl)
    fun _ _ h ↦ mk_eq_mk.2 <| ae_eq_set_compl_compl.2 (MeasuredSets.inseparable_iff_ae_eq.1 h)
  sdiff := SeparationQuotient.lift₂
    (fun s t : MeasuredSets μ ↦ mk ((s : Set α) \ t) (s.property.diff t.property))
    fun _ _ _ _ hs ht ↦ mk_eq_mk.2 <| ae_eq_set_sdiff
      (MeasuredSets.inseparable_iff_ae_eq.1 hs) (MeasuredSets.inseparable_iff_ae_eq.1 ht)
  himp := SeparationQuotient.lift₂
    (fun s t : MeasuredSets μ ↦ mk ((t : Set α) ∪ (s : Set α)ᶜ) (t.property.union s.property.compl))
    fun _ _ _ _ hs ht ↦ mk_eq_mk.2 <| ae_eq_set_union (MeasuredSets.inseparable_iff_ae_eq.1 ht)
      (ae_eq_set_compl_compl.2 (MeasuredSets.inseparable_iff_ae_eq.1 hs))
  top := mk univ .univ
  bot := mk ∅ .empty
  inf_compl_le_bot a := by
    induction a using ind with | h s hs => exact EventuallySubset.of_subset (inter_compl_self s).le
  top_le_sup_compl a := by
    induction a using ind with | h s hs => exact EventuallySubset.of_subset (union_compl_self s).ge
  le_top a := by
    induction a using ind with | h s hs => exact EventuallySubset.of_subset (subset_univ s)
  bot_le a := by
    induction a using ind with | h s hs => exact EventuallySubset.of_subset (empty_subset s)
  sdiff_eq a b := by
    induction a using ind with | h s hs => ?_
    induction b using ind with | h t ht => ?_
    exact mk_congr (Set.sdiff_eq s t)
  himp_eq a b := by
    induction a using ind with | h s hs => ?_
    induction b using ind with | h t ht => ?_
    rfl

/-- The order of the measure algebra is almost-everywhere inclusion of representatives. -/
@[simp]
theorem mk_le_mk : (mk s hs : MeasureAlgebra μ) ≤ mk t ht ↔ s ≤ᵐ[μ] t := (Iff.rfl)

theorem mk_le_mk_iff_measure_sdiff : (mk s hs : MeasureAlgebra μ) ≤ mk t ht ↔ μ (s \ t) = 0 :=
  mk_le_mk.trans ae_subset

theorem mk_le_mk_of_subset (h : s ⊆ t) : (mk s hs : MeasureAlgebra μ) ≤ mk t ht :=
  mk_le_mk.2 (EventuallySubset.of_subset h)

@[simp]
theorem mk_sup : (mk s hs ⊔ mk t ht : MeasureAlgebra μ) = mk (s ∪ t) (hs.union ht) := (rfl)

@[simp]
theorem mk_inf : (mk s hs ⊓ mk t ht : MeasureAlgebra μ) = mk (s ∩ t) (hs.inter ht) := (rfl)

@[simp]
theorem mk_compl : (mk s hs : MeasureAlgebra μ)ᶜ = mk sᶜ hs.compl := (rfl)

@[simp]
theorem mk_sdiff : (mk s hs \ mk t ht : MeasureAlgebra μ) = mk (s \ t) (hs.diff ht) := (rfl)

@[simp]
theorem mk_empty : (mk ∅ .empty : MeasureAlgebra μ) = ⊥ := (rfl)

@[simp]
theorem mk_univ : (mk univ .univ : MeasureAlgebra μ) = ⊤ := (rfl)

theorem mk_eq_bot : (mk s hs : MeasureAlgebra μ) = ⊥ ↔ μ s = 0 := by
  rw [← mk_empty, mk_eq_mk, ae_eq_empty]

theorem mk_eq_top : (mk s hs : MeasureAlgebra μ) = ⊤ ↔ μ sᶜ = 0 := by
  rw [← mk_univ, mk_eq_mk, ae_eq_univ]

@[simp]
theorem mk_symmDiff : (mk s hs ∆ mk t ht : MeasureAlgebra μ) = mk (s ∆ t) (hs.symmDiff ht) := by
  rw [symmDiff_def, mk_sdiff, mk_sdiff, mk_sup]
  exact mk_congr (symmDiff_def _ _).symm

instance : Inhabited (MeasureAlgebra μ) := ⟨⊥⟩

theorem disjoint_mk : Disjoint (mk s hs : MeasureAlgebra μ) (mk t ht) ↔ μ (s ∩ t) = 0 := by
  rw [disjoint_iff, mk_inf, mk_eq_bot]

/-! ### The measure of a class -/

/-- The measure of an element of the measure algebra: the measure of any representative. -/
def measure : MeasureAlgebra μ → ℝ≥0∞ :=
  SeparationQuotient.lift (fun s : MeasuredSets μ ↦ μ s)
    fun _ _ h ↦ measure_congr (MeasuredSets.inseparable_iff_ae_eq.1 h)

@[simp]
theorem measure_mk : (mk s hs : MeasureAlgebra μ).measure = μ s := (rfl)

@[simp]
theorem measure_bot : (⊥ : MeasureAlgebra μ).measure = 0 := by
  rw [← mk_empty, measure_mk, measure_empty]

@[simp]
theorem measure_top : (⊤ : MeasureAlgebra μ).measure = μ univ := by
  rw [← mk_univ, measure_mk]

@[simp]
theorem measure_eq_zero_iff {a : MeasureAlgebra μ} : a.measure = 0 ↔ a = ⊥ := by
  induction a using ind
  rw [measure_mk, mk_eq_bot]

@[gcongr]
theorem measure_mono {a b : MeasureAlgebra μ} (h : a ≤ b) : a.measure ≤ b.measure := by
  induction a using ind; induction b using ind
  exact measure_mono_ae (mk_le_mk.1 h)

theorem measure_sup_add_measure_inf (a b : MeasureAlgebra μ) :
    (a ⊔ b).measure + (a ⊓ b).measure = a.measure + b.measure := by
  induction a using ind with | h s hs => ?_
  induction b using ind with | h t ht => ?_
  simp only [mk_sup, mk_inf, measure_mk]
  exact measure_union_add_inter s ht

theorem measure_sup_of_disjoint {a b : MeasureAlgebra μ} (h : Disjoint a b) :
    (a ⊔ b).measure = a.measure + b.measure := by
  rw [← measure_sup_add_measure_inf, h.eq_bot, measure_bot, add_zero]

theorem measure_sup_le (a b : MeasureAlgebra μ) : (a ⊔ b).measure ≤ a.measure + b.measure :=
  (le_self_add).trans (measure_sup_add_measure_inf a b).le

/-! ### The metric -/

@[simp]
theorem edist_mk_mk : edist (mk s hs : MeasureAlgebra μ) (mk t ht) = μ (s ∆ t) := (rfl)

/-- The distance between two classes is the measure of their symmetric difference. -/
theorem edist_eq_measure_symmDiff (a b : MeasureAlgebra μ) : edist a b = (a ∆ b).measure := by
  induction a using ind; induction b using ind
  rw [edist_mk_mk, mk_symmDiff, measure_mk]

/-- For a finite measure, the measure algebra is a metric space. -/
instance [IsFiniteMeasure μ] : MetricSpace (MeasureAlgebra μ) :=
  EMetricSpace.toMetricSpace fun a b ↦ by
    induction a using ind; induction b using ind
    rw [edist_mk_mk]
    exact measure_ne_top _ _

@[simp]
theorem dist_mk_mk [IsFiniteMeasure μ] :
    dist (mk s hs : MeasureAlgebra μ) (mk t ht) = μ.real (s ∆ t) := by
  rw [dist_edist, edist_mk_mk, measureReal_def]

theorem edist_bot_right (a : MeasureAlgebra μ) : edist a ⊥ = a.measure := by
  rw [edist_eq_measure_symmDiff, symmDiff_bot]

theorem continuous_measure : Continuous (measure : MeasureAlgebra μ → ℝ≥0∞) :=
  SeparationQuotient.continuous_lift MeasuredSets.continuous_measure

theorem edist_compl_compl (a b : MeasureAlgebra μ) : edist aᶜ bᶜ = edist a b := by
  rw [edist_eq_measure_symmDiff, edist_eq_measure_symmDiff, compl_symmDiff_compl]

/-- Complementation is an isometric involution of the measure algebra. -/
theorem isometry_compl : Isometry (compl : MeasureAlgebra μ → MeasureAlgebra μ) :=
  edist_compl_compl

theorem edist_sup_sup_le (a b c d : MeasureAlgebra μ) :
    edist (a ⊔ b) (c ⊔ d) ≤ edist a c + edist b d := by
  induction a using ind; induction b using ind; induction c using ind; induction d using ind
  simp only [mk_sup, edist_mk_mk]
  exact (MeasureTheory.measure_mono union_symmDiff_union_subset).trans (measure_union_le _ _)

theorem edist_inf_inf_le (a b c d : MeasureAlgebra μ) :
    edist (a ⊓ b) (c ⊓ d) ≤ edist a c + edist b d := by
  rw [← edist_compl_compl, compl_inf, compl_inf, ← edist_compl_compl a, ← edist_compl_compl b]
  exact edist_sup_sup_le _ _ _ _

theorem edist_sdiff_sdiff_le (a b c d : MeasureAlgebra μ) :
    edist (a \ b) (c \ d) ≤ edist a c + edist b d := by
  rw [_root_.sdiff_eq, _root_.sdiff_eq, ← edist_compl_compl b]
  exact edist_inf_inf_le _ _ _ _

instance instTopologicalLattice : TopologicalLattice (MeasureAlgebra μ) where
  continuous_sup := (LipschitzWith.uncurry
    (fun b ↦ .of_edist_le fun a c ↦ by simpa using edist_sup_sup_le a b c b)
    (fun a ↦ .of_edist_le fun b d ↦ by simpa using edist_sup_sup_le a b a d)).continuous
  continuous_inf := (LipschitzWith.uncurry
    (fun b ↦ .of_edist_le fun a c ↦ by simpa using edist_inf_inf_le a b c b)
    (fun a ↦ .of_edist_le fun b d ↦ by simpa using edist_inf_inf_le a b a d)).continuous

/-! ### Indicator classes in `Lᵖ` -/

section IndicatorConstLp

variable [IsFiniteMeasure μ] {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞}

/-- For a finite measure, the class in `Lᵖ(μ; E)` of the indicator `𝟙_s c` of a representative
`s`, which only depends on the class of `s` in the measure algebra. -/
def indicatorConstLp (p : ℝ≥0∞) (c : E) : MeasureAlgebra μ → Lp E p μ :=
  SeparationQuotient.lift
    (fun s : MeasuredSets μ ↦
      MeasureTheory.indicatorConstLp p s.property (measure_ne_top μ (s : Set α)) c)
    fun _ _ h ↦ Lp.ext <| indicatorConstLp_coeFn.trans <|
      (indicator_ae_eq_of_ae_eq_set (MeasuredSets.inseparable_iff_ae_eq.1 h)).trans
        indicatorConstLp_coeFn.symm

@[simp]
theorem indicatorConstLp_mk (c : E) :
    indicatorConstLp p c (mk s hs : MeasureAlgebra μ) =
      MeasureTheory.indicatorConstLp p hs (measure_ne_top μ s) c := (rfl)

@[simp]
theorem indicatorConstLp_bot (c : E) : indicatorConstLp p c (⊥ : MeasureAlgebra μ) = 0 := by
  rw [← mk_empty, indicatorConstLp_mk, MeasureTheory.indicatorConstLp_empty]

theorem indicatorConstLp_sup_of_disjoint (c : E) {a b : MeasureAlgebra μ} (h : Disjoint a b) :
    indicatorConstLp p c (a ⊔ b) = indicatorConstLp p c a + indicatorConstLp p c b := by
  induction a using ind with | h s hs => ?_
  induction b using ind with | h t ht => ?_
  -- Replace the representative `t` by `t \ s`, which is disjoint from `s`.
  have ht' : mk t ht = (mk (t \ s) (ht.diff hs) : MeasureAlgebra μ) := by
    rw [← sdiff_eq_left.2 h.symm, mk_sdiff]
  rw [ht', mk_sup]
  simp only [indicatorConstLp_mk]
  exact indicatorConstLp_disjoint_union hs (ht.diff hs) _ _ disjoint_sdiff_right c

/-- For `0 < p < ∞`, the `Lᵖ` distance between the indicator classes of a vector `c` is
`‖c‖ μ(s ∆ t) ^ (1 / p)`. -/
theorem dist_indicatorConstLp (hp₀ : p ≠ 0) (hp : p ≠ ∞) (c : E) (a b : MeasureAlgebra μ) :
    dist (indicatorConstLp p c a) (indicatorConstLp p c b) = ‖c‖ * dist a b ^ (1 / p.toReal) := by
  induction a using ind; induction b using ind
  rw [indicatorConstLp_mk, indicatorConstLp_mk, dist_indicatorConstLp_eq_norm,
    norm_indicatorConstLp hp₀ hp, dist_mk_mk]

/-- Indicator classes of a nonzero vector that are close in `Lᵖ`, `1 ≤ p ≤ ∞`, come from close
elements of the measure algebra. -/
private theorem exists_pos_forall_dist_indicatorConstLp_lt [Fact (1 ≤ p)] {c : E} (hc : c ≠ 0)
    {δ : ℝ} (hδ : 0 < δ) : ∃ ε > 0, ∀ a b : MeasureAlgebra μ,
      dist (indicatorConstLp p c a) (indicatorConstLp p c b) < ε → dist a b < δ := by
  have hc' : 0 < ‖c‖ := norm_pos_iff.2 hc
  rcases eq_or_ne p ∞ with rfl | hp
  · refine ⟨‖c‖, hc', fun a b hab ↦ ?_⟩
    induction a using ind with | h s hs => ?_
    induction b using ind with | h t ht => ?_
    have hst : μ (s ∆ t) = 0 := by
      by_contra h0
      rw [indicatorConstLp_mk, indicatorConstLp_mk, dist_indicatorConstLp_eq_norm,
        norm_indicatorConstLp_top h0] at hab
      exact lt_irrefl _ hab
    rwa [dist_mk_mk, measureReal_def, hst, ENNReal.toReal_zero]
  · refine ⟨‖c‖ * δ ^ (1 / p.toReal), mul_pos hc' (Real.rpow_pos_of_pos hδ _), fun a b hab ↦ ?_⟩
    have hp₀ : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
    have hp0 : 0 < p.toReal := ENNReal.toReal_pos hp₀ hp
    rw [dist_indicatorConstLp hp₀ hp] at hab
    exact (Real.rpow_lt_rpow_iff dist_nonneg hδ.le (by positivity)).1
      (lt_of_mul_lt_mul_left hab hc'.le)

end IndicatorConstLp

/-! ### Separability -/

/-- If the measure algebra of `μ` is separable, then `μ` is separable. -/
theorem isSeparable_of_separableSpace [SeparableSpace (MeasureAlgebra μ)] : IsSeparable μ := by
  obtain ⟨D, hDc, hD⟩ := exists_countable_dense (MeasureAlgebra μ)
  choose! r hr hrD using exists_mk_eq (μ := μ)
  refine ⟨r '' D, hDc.image r, ⟨?_, fun s hs _ ε hε ↦ ?_⟩⟩
  · rintro _ ⟨a, -, rfl⟩
    exact hr a
  · obtain ⟨b, hbD, hb⟩ :=
      EMetric.mem_closure_iff.1 (hD (mk s hs)) (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
    refine ⟨r b, mem_image_of_mem r hbD, ?_⟩
    rwa [← hrD b, edist_mk_mk] at hb

/-- The measure algebra of a separable finite measure is separable. -/
instance [IsFiniteMeasure μ] [IsSeparable μ] : SeparableSpace (MeasureAlgebra μ) := by
  obtain ⟨𝒜, h𝒜c, h𝒜⟩ := exists_countable_measureDense μ
  have := h𝒜c.to_subtype
  refine ⟨⟨range fun t : 𝒜 ↦ (mk t.val (h𝒜.measurable _ t.property) : MeasureAlgebra μ),
    countable_range _, fun a ↦ ?_⟩⟩
  induction a using ind with | h s hs => ?_
  refine Metric.mem_closure_iff.2 fun ε hε ↦ ?_
  obtain ⟨t, ht𝒜, hst⟩ := h𝒜.approx s hs (measure_ne_top μ s) ε hε
  refine ⟨_, ⟨⟨t, ht𝒜⟩, rfl⟩, ?_⟩
  rw [dist_mk_mk, measureReal_def]
  exact ENNReal.toReal_lt_of_lt_ofReal hst

/-- A finite measure is separable exactly when its measure algebra is separable. -/
theorem isSeparable_iff_separableSpace [IsFiniteMeasure μ] :
    IsSeparable μ ↔ SeparableSpace (MeasureAlgebra μ) :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ isSeparable_of_separableSpace⟩

/-- If `Lᵖ(μ; E)` is separable for a finite measure `μ`, a nonzero `E` and some `1 ≤ p ≤ ∞`, then
the measure algebra of `μ` is separable: it embeds into `Lᵖ(μ; E)` through the indicator classes
of a nonzero vector. -/
theorem separableSpace_of_separableSpace_Lp [IsFiniteMeasure μ] (E : Type*)
    [NormedAddCommGroup E] [Nontrivial E] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    [SeparableSpace (Lp E p μ)] : SeparableSpace (MeasureAlgebra μ) := by
  obtain ⟨c, hc⟩ := exists_ne (0 : E)
  set g : MeasureAlgebra μ → Lp E p μ := indicatorConstLp p c
  have : SeparableSpace (range g) := (IsSeparable.of_separableSpace _).separableSpace
  obtain ⟨T, hTc, hTg, hgT⟩ := exists_countable_dense_subset (range g)
  refine ⟨⟨invFun g '' T, hTc.image _, fun a ↦ Metric.mem_closure_iff.2 fun δ hδ ↦ ?_⟩⟩
  obtain ⟨ε, hε, hεδ⟩ := exists_pos_forall_dist_indicatorConstLp_lt (μ := μ) (p := p) hc hδ
  obtain ⟨y, hyT, hy⟩ := Metric.mem_closure_iff.1 (hgT (mem_range_self a)) ε hε
  refine ⟨invFun g y, mem_image_of_mem _ hyT, hεδ _ _ ?_⟩
  rw [← invFun_eq (f := g) (hTg hyT)] at hy
  exact hy

/-- For a finite measure `μ`, `1 ≤ p < ∞` and a nonzero separable normed space `E`, the measure
algebra of `μ` is separable exactly when `Lᵖ(μ; E)` is. -/
theorem separableSpace_iff_separableSpace_Lp [IsFiniteMeasure μ] {E : Type*}
    [NormedAddCommGroup E] [Nontrivial E] [SeparableSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ∞) : SeparableSpace (MeasureAlgebra μ) ↔ SeparableSpace (Lp E p μ) := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ separableSpace_of_separableSpace_Lp E p⟩
  have := isSeparable_of_separableSpace (μ := μ)
  have : Fact (p ≠ ∞) := ⟨hp⟩
  infer_instance

end MeasureAlgebra

end TauCeti
