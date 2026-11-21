/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.Marking.Enumeration
public import TauCeti.MeasureTheory.Measure.IntegerValued.Enumeration.LocallyFinite
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Independent marking kernel on integer-valued measures

On a standard Borel space `X`, composing a total measurable occurrence enumeration for a countable
measurable cover `s : ℕ → Set X` with `Kernel.optionalTupleMarking` yields a Markov kernel
`Kernel.markingOfCover` from `Measure X` to `Measure (X × E)`. By enumeration independence, the
resulting marked law on the domain of integer-valued measures finite on every `s n` depends only
on the measure `μ` and the mark kernel `κ`, not on the chosen enumeration or cover.

When `X` is a sigma-compact Hausdorff standard Borel space, specializing to `compactCovering X`
gives a canonical cover-free marking kernel `Kernel.marking` defined on all integer-valued
measures finite on every `compactCovering X n` (in particular, all integer-valued measures finite
on compact sets).

For every measure `μ` in the domain, the marked law projects to `Measure.dirac μ`, has mean
measure (`Measure.join`) equal to the composition-product `μ ⊗ₘ κ`, and satisfies the
exponential Laplace transform formula for all extended nonnegative measurable tests. Outside
the domain, the kernel assigns the point mass at the zero measure.

## References

* G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press,
  2018, Chapter 5 (independent marking).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace ProbabilityTheory.Kernel

section Cover

variable {X E : Type*} [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace E]
  (κ : Kernel X E) [IsMarkovKernel κ]

/-- The independent marking kernel associated to a countable measurable cover `s` of a standard
Borel space. On every integer-valued measure finite on each `s n`, it attaches independent
`κ`-marks to every occurrence; outside this locus it assigns the point mass at the zero measure. -/
def markingOfCover {s : ℕ → Set X} (hs : ∀ n, MeasurableSet (s n))
    (hcover : ⋃ n, s n = univ) : Kernel (Measure X) (Measure (X × E)) :=
  (κ.optionalTupleMarking ℕ).comap
    (Measure.exists_occurrence_enumeration_of_cover hs hcover).choose
    (Measure.exists_occurrence_enumeration_of_cover hs hcover).choose_spec.1

/-- Independent marking of measures is a Markov kernel. -/
instance {s : ℕ → Set X} (hs : ∀ n, MeasurableSet (s n)) (hcover : ⋃ n, s n = univ) :
    IsMarkovKernel (κ.markingOfCover hs hcover) := by
  unfold markingOfCover
  infer_instance

/-- On any integer-valued measure finite on the cover, `markingOfCover` agrees with marking any
countable optional occurrence enumeration of the measure. -/
theorem markingOfCover_eq_optionalTupleMarking {s : ℕ → Set X}
    (hs : ∀ n, MeasurableSet (s n)) (hcover : ⋃ n, s n = univ)
    {μ : Measure X} (hμ : μ.IsIntegerValued) (hfin : ∀ n, μ (s n) ≠ ∞)
    {ι : Type*} [Countable ι] {x : ι → Option X}
    (hx : μ = Measure.sum fun i => (x i).elim 0 Measure.dirac) :
    κ.markingOfCover hs hcover μ = κ.optionalTupleMarking ι x := by
  have hrec :=
    (Measure.exists_occurrence_enumeration_of_cover hs hcover).choose_spec.2.1 μ hμ hfin
  exact κ.optionalTupleMarking_eq_of_sum_elim_dirac_eq (hrec.symm.trans hx)

/-- On any integer-valued measure finite on the cover, `markingOfCover` agrees with marking any
countable non-optional occurrence enumeration of the measure. -/
theorem markingOfCover_eq_tupleMarking {s : ℕ → Set X}
    (hs : ∀ n, MeasurableSet (s n)) (hcover : ⋃ n, s n = univ)
    {μ : Measure X} (hμ : μ.IsIntegerValued) (hfin : ∀ n, μ (s n) ≠ ∞)
    {ι : Type*} [Countable ι] {x : ι → X}
    (hx : μ = Measure.sum fun i => Measure.dirac (x i)) :
    κ.markingOfCover hs hcover μ = κ.tupleMarking ι x := by
  simpa only [optionalTupleMarking_some] using
    κ.markingOfCover_eq_optionalTupleMarking hs hcover hμ hfin (x := fun i => some (x i)) hx

/-- Independent marking does not depend on the choice of finite-mass cover. -/
theorem markingOfCover_congr_cover {s t : ℕ → Set X}
    (hs : ∀ n, MeasurableSet (s n)) (hcover : ⋃ n, s n = univ)
    (ht : ∀ n, MeasurableSet (t n)) (hcover' : ⋃ n, t n = univ)
    {μ : Measure X} (hμ : μ.IsIntegerValued)
    (hfin : ∀ n, μ (s n) ≠ ∞) (hfin' : ∀ n, μ (t n) ≠ ∞) :
    κ.markingOfCover hs hcover μ = κ.markingOfCover ht hcover' μ := by
  have hrec :=
    (Measure.exists_occurrence_enumeration_of_cover ht hcover').choose_spec.2.1 μ hμ hfin'
  exact κ.markingOfCover_eq_optionalTupleMarking hs hcover hμ hfin hrec

/-- Outside the integer-valued finite-on-cover locus, `markingOfCover` produces the empty
configuration almost surely. -/
theorem markingOfCover_eq_dirac_zero_of_not_isIntegerValued_and_forall_ne_top {s : ℕ → Set X}
    (hs : ∀ n, MeasurableSet (s n)) (hcover : ⋃ n, s n = univ)
    {μ : Measure X} (hnot : ¬ (μ.IsIntegerValued ∧ ∀ n, μ (s n) ≠ ∞)) :
    κ.markingOfCover hs hcover μ = Measure.dirac 0 := by
  have hnone :=
    (Measure.exists_occurrence_enumeration_of_cover hs hcover).choose_spec.2.2 μ hnot
  simpa only [markingOfCover, comap_apply, funext hnone] using κ.optionalTupleMarking_none ℕ

/-- Marking the zero measure gives the point mass at the zero measure. -/
@[simp]
theorem markingOfCover_zero {s : ℕ → Set X}
    (hs : ∀ n, MeasurableSet (s n)) (hcover : ⋃ n, s n = univ) :
    κ.markingOfCover hs hcover 0 = Measure.dirac 0 := by
  rw [κ.markingOfCover_eq_optionalTupleMarking hs hcover Measure.isIntegerValued_zero
    (fun _ => by simp) (ι := Empty) (x := Empty.elim) (by simp),
    optionalTupleMarking_of_isEmpty]

/-- Marking a single Dirac occurrence marks that point with `κ x`. -/
@[simp]
theorem markingOfCover_dirac {s : ℕ → Set X}
    (hs : ∀ n, MeasurableSet (s n)) (hcover : ⋃ n, s n = univ) (x : X) :
    κ.markingOfCover hs hcover (Measure.dirac x) = ((Kernel.id ×ₖ κ) x).map Measure.dirac := by
  rw [κ.markingOfCover_eq_tupleMarking hs hcover (Measure.isIntegerValued_dirac x)
    (fun _ => measure_ne_top _ _) (ι := Unit) (x := fun _ => x) (by simp),
    tupleMarking_apply]
  have hmap : (Measure.infinitePi fun _ : Unit => (Kernel.id ×ₖ κ) x).map
      (fun z : Unit → X × E => z ()) = (Kernel.id ×ₖ κ) x :=
    Measure.infinitePi_map_eval _ ()
  have heval : Measurable (fun z : Unit → X × E => z ()) := measurable_pi_apply ()
  conv_rhs => rw [← hmap, Measure.map_map Measure.measurable_dirac heval]
  congr 1
  funext z
  simp

/-- Deterministic marking pushes every occurrence forward along `x ↦ (x, g x)`. -/
theorem markingOfCover_deterministic {s : ℕ → Set X}
    (hs : ∀ n, MeasurableSet (s n)) (hcover : ⋃ n, s n = univ)
    {g : X → E} (hg : Measurable g) {μ : Measure X}
    (hμ : μ.IsIntegerValued) (hfin : ∀ n, μ (s n) ≠ ∞) :
    (Kernel.deterministic g hg).markingOfCover hs hcover μ =
      Measure.dirac (μ.map fun x => (x, g x)) := by
  have hrec :=
    (Measure.exists_occurrence_enumeration_of_cover hs hcover).choose_spec.2.1 μ hμ hfin
  rw [(Kernel.deterministic g hg).markingOfCover_eq_optionalTupleMarking hs hcover hμ hfin hrec,
    optionalTupleMarking_deterministic hg]
  congr 1
  have hpair : Measurable (fun x : X => (x, g x)) := measurable_id.prodMk hg
  conv_rhs => rw [hrec, Measure.map_sum hpair.aemeasurable]
  congr 1
  funext n
  cases (Measure.exists_occurrence_enumeration_of_cover hs hcover).choose μ n with
  | none => simp
  | some a => simp [Measure.map_dirac' hpair]

/-- Forgetting marks recovers the input measure with probability one. -/
theorem map_map_fst_markingOfCover {s : ℕ → Set X}
    (hs : ∀ n, MeasurableSet (s n)) (hcover : ⋃ n, s n = univ)
    {μ : Measure X} (hμ : μ.IsIntegerValued) (hfin : ∀ n, μ (s n) ≠ ∞) :
    (κ.markingOfCover hs hcover μ).map (fun ν => ν.map Prod.fst) = Measure.dirac μ := by
  have hrec :=
    (Measure.exists_occurrence_enumeration_of_cover hs hcover).choose_spec.2.1 μ hμ hfin
  rw [κ.markingOfCover_eq_optionalTupleMarking hs hcover hμ hfin hrec,
    map_map_fst_optionalTupleMarking, ← hrec]

/-- The mean measure of independently marking `μ` is `μ ⊗ₘ κ`. -/
theorem join_markingOfCover {s : ℕ → Set X}
    (hs : ∀ n, MeasurableSet (s n)) (hcover : ⋃ n, s n = univ)
    {μ : Measure X} (hμ : μ.IsIntegerValued) (hfin : ∀ n, μ (s n) ≠ ∞) :
    (κ.markingOfCover hs hcover μ).join = μ ⊗ₘ κ := by
  have hrec :=
    (Measure.exists_occurrence_enumeration_of_cover hs hcover).choose_spec.2.1 μ hμ hfin
  rw [κ.markingOfCover_eq_optionalTupleMarking hs hcover hμ hfin hrec,
    κ.join_optionalTupleMarking, ← hrec]

/-- Laplace functional of `markingOfCover` for any nonnegative measurable test function. -/
theorem laplaceFunctional_markingOfCover {s : ℕ → Set X}
    (hs : ∀ n, MeasurableSet (s n)) (hcover : ⋃ n, s n = univ)
    {μ : Measure X} (hμ : μ.IsIntegerValued) (hfin : ∀ n, μ (s n) ≠ ∞)
    {f : X × E → ℝ≥0∞} (hf : Measurable f) :
    (κ.markingOfCover hs hcover μ).laplaceFunctional id f =
      (ENNReal.expNeg (∫⁻ a, (-ENNReal.log
        (∫⁻ e, (ENNReal.expNeg (f (a, e)) : ℝ≥0∞) ∂κ a)).toENNReal ∂μ) :
          ℝ≥0∞) := by
  have hrec :=
    (Measure.exists_occurrence_enumeration_of_cover hs hcover).choose_spec.2.1 μ hμ hfin
  rw [κ.markingOfCover_eq_optionalTupleMarking hs hcover hμ hfin hrec,
    Measure.laplaceFunctional_def]
  simp only [id]
  rw [κ.lintegral_expNeg_optionalTupleMarking_eq_expNeg_lintegral _ hf, ← hrec]

end Cover

section CompactCovering

variable {X E : Type*} [TopologicalSpace X] [T2Space X] [SigmaCompactSpace X]
  [MeasurableSpace X] [OpensMeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace E] (κ : Kernel X E) [IsMarkovKernel κ]

/-- The canonical independent marking kernel on a sigma-compact Hausdorff standard Borel space.
On every integer-valued measure finite on every `compactCovering X n` (in particular, every
integer-valued measure finite on compact sets), it attaches independent `κ`-marks to every
occurrence; outside that locus it assigns the point mass at the zero measure. -/
def marking : Kernel (Measure X) (Measure (X × E)) :=
  κ.markingOfCover (fun n => (isCompact_compactCovering X n).measurableSet)
    (iUnion_compactCovering X)

/-- Canonical independent marking is a Markov kernel. -/
instance : IsMarkovKernel κ.marking := by
  unfold marking
  infer_instance

/-- Canonical independent marking equals `Kernel.markingOfCover` for `compactCovering X`. -/
theorem marking_eq_markingOfCover_compactCovering :
    κ.marking = κ.markingOfCover
      (fun n => (isCompact_compactCovering X n).measurableSet) (iUnion_compactCovering X) := by
  unfold marking
  rfl

/-- Outside the integer-valued finite-on-`compactCovering` locus, `Kernel.marking` produces the
empty configuration almost surely. -/
theorem marking_eq_dirac_zero_of_not_isIntegerValued_and_forall_ne_top {μ : Measure X}
    (hnot : ¬ (μ.IsIntegerValued ∧ ∀ n, μ (compactCovering X n) ≠ ∞)) :
    κ.marking μ = Measure.dirac 0 :=
  κ.markingOfCover_eq_dirac_zero_of_not_isIntegerValued_and_forall_ne_top _ _ hnot

/-- On integer-valued measures finite on compact sets, `Kernel.marking` agrees with
`Kernel.markingOfCover` for any finite-mass measurable cover. -/
theorem marking_eq_markingOfCover {s : ℕ → Set X}
    (hs : ∀ n, MeasurableSet (s n)) (hcover : ⋃ n, s n = univ)
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ] (hμ : μ.IsIntegerValued)
    (hfin : ∀ n, μ (s n) ≠ ∞) :
    κ.marking μ = κ.markingOfCover hs hcover μ :=
  κ.markingOfCover_congr_cover _ _ hs hcover hμ
    (fun n => (isCompact_compactCovering X n).measure_ne_top) hfin

/-- On integer-valued measures finite on compact sets, `Kernel.marking` agrees with marking any
countable optional occurrence enumeration of `μ`. -/
theorem marking_eq_optionalTupleMarking {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
    (hμ : μ.IsIntegerValued) {ι : Type*} [Countable ι] {x : ι → Option X}
    (hx : μ = Measure.sum fun i => (x i).elim 0 Measure.dirac) :
    κ.marking μ = κ.optionalTupleMarking ι x :=
  κ.markingOfCover_eq_optionalTupleMarking _ _ hμ
    (fun n => (isCompact_compactCovering X n).measure_ne_top) hx

/-- On integer-valued measures finite on compact sets, `Kernel.marking` agrees with marking any
countable occurrence enumeration of `μ`. -/
theorem marking_eq_tupleMarking {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
    (hμ : μ.IsIntegerValued) {ι : Type*} [Countable ι] {x : ι → X}
    (hx : μ = Measure.sum fun i => Measure.dirac (x i)) :
    κ.marking μ = κ.tupleMarking ι x :=
  κ.markingOfCover_eq_tupleMarking _ _ hμ
    (fun n => (isCompact_compactCovering X n).measure_ne_top) hx

/-- Marking the zero measure gives the point mass at the zero measure. -/
@[simp]
theorem marking_zero : κ.marking 0 = Measure.dirac 0 :=
  κ.markingOfCover_zero _ _

/-- Marking a single Dirac occurrence marks that point with `κ x`. -/
@[simp]
theorem marking_dirac (x : X) :
    κ.marking (Measure.dirac x) = ((Kernel.id ×ₖ κ) x).map Measure.dirac :=
  κ.markingOfCover_dirac _ _ x

/-- Deterministic marking pushes every occurrence forward along `x ↦ (x, g x)`. -/
theorem marking_deterministic {g : X → E} (hg : Measurable g)
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ] (hμ : μ.IsIntegerValued) :
    (Kernel.deterministic g hg).marking μ = Measure.dirac (μ.map fun x => (x, g x)) :=
  markingOfCover_deterministic _ _ hg hμ
    (fun n => (isCompact_compactCovering X n).measure_ne_top)

/-- Forgetting marks recovers any integer-valued measure finite on compact sets almost surely. -/
theorem map_map_fst_marking {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
    (hμ : μ.IsIntegerValued) :
    (κ.marking μ).map (fun ν => ν.map Prod.fst) = Measure.dirac μ :=
  κ.map_map_fst_markingOfCover _ _ hμ
    (fun n => (isCompact_compactCovering X n).measure_ne_top)

/-- The mean measure of independently marking an integer-valued measure finite on compact sets
is `μ ⊗ₘ κ`. -/
theorem join_marking {μ : Measure X} [IsFiniteMeasureOnCompacts μ] (hμ : μ.IsIntegerValued) :
    (κ.marking μ).join = μ ⊗ₘ κ :=
  κ.join_markingOfCover _ _ hμ (fun n => (isCompact_compactCovering X n).measure_ne_top)

/-- Laplace functional of `Kernel.marking` for any nonnegative measurable test function. -/
theorem laplaceFunctional_marking {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
    (hμ : μ.IsIntegerValued) {f : X × E → ℝ≥0∞} (hf : Measurable f) :
    (κ.marking μ).laplaceFunctional id f =
      (ENNReal.expNeg (∫⁻ a, (-ENNReal.log
        (∫⁻ e, (ENNReal.expNeg (f (a, e)) : ℝ≥0∞) ∂κ a)).toENNReal ∂μ) :
          ℝ≥0∞) :=
  κ.laplaceFunctional_markingOfCover _ _ hμ
    (fun n => (isCompact_compactCovering X n).measure_ne_top) hf

end CompactCovering

end ProbabilityTheory.Kernel
