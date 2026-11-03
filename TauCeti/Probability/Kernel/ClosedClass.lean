/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Kernel.Reachability
public import TauCeti.Probability.Kernel.Composition.Power
public import Mathlib.Probability.Kernel.Composition.CompMap

/-!
# Restriction of a kernel to a closed set of states

`Kernel.subtype κ hs` restricts both the starting and destination states to a measurable
set `s`. It is a Markov kernel exactly when `κ x s = 1` for every `x ∈ s`.
For a Markov kernel this is equivalent to `Kernel.IsClosedSet κ s`: no probability
leaves `s` in one step.

Under this closure condition, pushing the restricted kernel back into the ambient space
recovers the original transitions from states in `s`, at every time. Consequently
reachability and communication in the restricted chain agree with their ambient versions.
On a countable space, closure is equivalent to containing every state reachable from one
of its members. In particular, a closed communicating class carries an irreducible
Markov kernel, with the same transition probabilities as the original chain.

The construction uses Mathlib's `Kernel.comapRight` and `Kernel.comap`, rather than
choosing a retraction onto the set of states. Empty sets are allowed.

## References

* J. R. Norris, *Markov Chains* (1997), §1.2, communicating classes and closed classes.
-/

public section

open MeasureTheory Set

namespace ProbabilityTheory.Kernel

variable {S : Type*} [MeasurableSpace S] {κ : Kernel S S} {s : Set S}

/-- A set of states is closed for a kernel if no mass leaves it in one step. -/
def IsClosedSet (κ : Kernel S S) (s : Set S) : Prop :=
  ∀ x ∈ s, κ x sᶜ = 0

/-- Closedness means that each state in the set assigns zero mass to its complement. -/
theorem isClosedSet_def (κ : Kernel S S) (s : Set S) :
    κ.IsClosedSet s ↔ ∀ x ∈ s, κ x sᶜ = 0 := (Iff.rfl)

/-- For a Markov kernel, closedness is equivalent to preserving total mass in the set. -/
theorem isClosedSet_iff_forall_apply_eq_one [IsMarkovKernel κ] (hs : MeasurableSet s) :
    κ.IsClosedSet s ↔ ∀ x ∈ s, κ x s = 1 := by
  simp only [isClosedSet_def, prob_compl_eq_zero_iff hs]

/-- Restrict both arguments of a transition kernel to a measurable set of states.
The resulting kernel may lose mass unless the set is closed under transitions. -/
noncomputable def subtype (κ : Kernel S S) (hs : MeasurableSet s) : Kernel s s :=
  (κ.comap Subtype.val measurable_subtype_coe).comapRight
    (MeasurableEmbedding.subtype_coe hs)

/-- The transition measure of the subtype kernel is the pullback along subtype inclusion. -/
theorem subtype_apply (κ : Kernel S S) (hs : MeasurableSet s) (x : s) :
    κ.subtype hs x = (κ x).comap Subtype.val := (rfl)

/-- Evaluation of the subtype kernel on a set of subtype states. -/
theorem subtype_apply' (κ : Kernel S S) (hs : MeasurableSet s) (x : s) (t : Set s) :
    κ.subtype hs x t = κ x (Subtype.val '' t) := by
  rw [subtype_apply, (MeasurableEmbedding.subtype_coe hs).comap_apply]

/-- Singleton transition probabilities are unchanged by restriction. -/
@[simp]
theorem subtype_apply_singleton (κ : Kernel S S) (hs : MeasurableSet s) (x y : s) :
    κ.subtype hs x {y} = κ x {y.val} := by
  simp [subtype_apply']

instance (κ : Kernel S S) [IsFiniteKernel κ] (hs : MeasurableSet s) :
    IsFiniteKernel (κ.subtype hs) := by
  unfold subtype
  infer_instance

/-- Restriction is a Markov kernel precisely when each starting state in the set sends
total mass one into the set. This characterization also applies to non-Markov kernels. -/
theorem isMarkovKernel_subtype_iff (κ : Kernel S S) (hs : MeasurableSet s) :
    IsMarkovKernel (κ.subtype hs) ↔ ∀ x ∈ s, κ x s = 1 := by
  constructor
  · intro h x hx
    have hmass := measure_univ (μ := κ.subtype hs ⟨x, hx⟩)
    rw [subtype_apply', image_univ, Subtype.range_coe] at hmass
    exact hmass
  · intro h
    exact ⟨fun x => ⟨by simpa [subtype_apply', Subtype.range_coe] using h x x.property⟩⟩

/-- Restriction of a Markov kernel is Markov precisely when the set is closed. -/
theorem isMarkovKernel_subtype_iff_isClosedSet [IsMarkovKernel κ] (hs : MeasurableSet s) :
    IsMarkovKernel (κ.subtype hs) ↔ κ.IsClosedSet s := by
  rw [isMarkovKernel_subtype_iff, isClosedSet_iff_forall_apply_eq_one hs]

/-- If no mass leaves the set, inclusion recovers the original transition measure. -/
theorem map_subtype (κ : Kernel S S) (hs : MeasurableSet s)
    (hclosed : κ.IsClosedSet s) :
    (κ.subtype hs).map Subtype.val = κ.comap Subtype.val measurable_subtype_coe := by
  ext1 x
  rw [map_apply _ measurable_subtype_coe, subtype_apply,
    map_comap_subtype_coe hs, comap_apply]
  exact Measure.restrict_eq_self_of_ae_mem
    (ae_iff.mpr ((isClosedSet_def κ s).mp hclosed x x.property))

/-- Inclusion intertwines every power of a kernel restricted to a closed set with the
corresponding ambient power. -/
theorem map_subtype_pow (κ : Kernel S S) (hs : MeasurableSet s)
    (hclosed : κ.IsClosedSet s) (n : ℕ) :
    ((κ.subtype hs) ^ n).map Subtype.val =
      (κ ^ n).comap Subtype.val measurable_subtype_coe := by
  let e : Kernel s S := deterministic Subtype.val measurable_subtype_coe
  have hstep : e ∘ₖ κ.subtype hs = κ ∘ₖ e := by
    simpa [e, deterministic_comp_eq_map, comp_deterministic_eq_comap] using
      map_subtype κ hs hclosed
  simpa [e, deterministic_comp_eq_map, comp_deterministic_eq_comap] using
    comp_pow_eq_pow_comp_of_comp_eq hstep n

/-- All finite-time transition probabilities within a closed set are preserved by
restriction, including time zero. -/
theorem subtype_pow_apply (κ : Kernel S S) (hs : MeasurableSet s)
    (hclosed : κ.IsClosedSet s) (n : ℕ) (x : s) (t : Set s) :
    ((κ.subtype hs) ^ n) x t = (κ ^ n) x (Subtype.val '' t) := by
  have h := congrArg (fun η : Kernel s S => η x (Subtype.val '' t))
    (map_subtype_pow κ hs hclosed n)
  rw [map_apply _ measurable_subtype_coe,
    (MeasurableEmbedding.subtype_coe hs).map_apply, comap_apply'] at h
  simpa only [Subtype.coe_injective.preimage_image] using h

/-- The probability of leaving a closed set is zero at every finite time. -/
theorem pow_apply_compl_eq_zero (κ : Kernel S S) (hs : MeasurableSet s)
    (hclosed : κ.IsClosedSet s) (n : ℕ) {x : S} (hx : x ∈ s) :
    (κ ^ n) x sᶜ = 0 := by
  have h := congrArg (fun η : Kernel s S => η ⟨x, hx⟩ sᶜ)
    (map_subtype_pow κ hs hclosed n)
  simpa [map_apply' _ measurable_subtype_coe _ hs.compl, comap_apply'] using h.symm

/-- On a countable state space, one-step closure is equivalent to closure under
reachability at arbitrary finite times. -/
theorem isClosedSet_iff_forall_reaches_mem [Countable S]
    [MeasurableSingletonClass S] :
    κ.IsClosedSet s ↔ ∀ x ∈ s, ∀ y, κ.Reaches x y → y ∈ s := by
  constructor
  · intro h x hx y hy
    rw [reaches_def] at hy
    obtain ⟨n, hn⟩ := hy
    by_contra hys
    have hzero := pow_apply_compl_eq_zero κ (to_countable s).measurableSet h n hx
    have hle := measure_mono (μ := (κ ^ n) x)
      (singleton_subset_iff.mpr hys : {y} ⊆ sᶜ)
    exact hn.not_ge (hzero ▸ hle)
  · intro h
    rw [isClosedSet_def]
    intro x hx
    apply (measure_null_iff_singleton (to_countable sᶜ)).mpr
    intro y hy
    by_contra hpos
    exact hy (h x hx y (reaches_of_pos (pos_iff_ne_zero.mpr hpos)))

/-- Restricting to a closed set preserves and reflects reachability between its states. -/
@[simp]
theorem reaches_subtype_iff (hs : MeasurableSet s)
    (hclosed : κ.IsClosedSet s) (x y : s) :
    (κ.subtype hs).Reaches x y ↔ κ.Reaches x.val y.val := by
  simp only [reaches_def, subtype_pow_apply κ hs hclosed, image_singleton]

/-- Restricting to a closed set preserves and reflects communication between its states. -/
@[simp]
theorem communicates_subtype_iff (hs : MeasurableSet s)
    (hclosed : κ.IsClosedSet s) (x y : s) :
    (κ.subtype hs).Communicates x y ↔ κ.Communicates x.val y.val := by
  simp only [communicates_def, reaches_subtype_iff hs hclosed]

/-- A kernel on a closed set is irreducible precisely when its states communicate in
the ambient chain. -/
theorem isIrreducible_subtype_iff [MeasurableSingletonClass S] (hs : MeasurableSet s)
    (hclosed : κ.IsClosedSet s) :
    IsIrreducible Measure.count (κ.subtype hs) ↔
      ∀ x ∈ s, ∀ y ∈ s, κ.Communicates x y := by
  simp only [isIrreducible_count_iff_forall_communicates,
    communicates_subtype_iff hs hclosed]
  exact ⟨fun h x hx y hy => h ⟨x, hx⟩ ⟨y, hy⟩, fun h x y => h x x.property y y.property⟩

/-- The communicating class of `x` supports a Markov restriction exactly when every
state reachable from `x` can reach `x` again. This is the closed-class criterion. -/
theorem isMarkovKernel_subtype_communicatingClass_iff [Countable S]
    [MeasurableSingletonClass S] [IsMarkovKernel κ] (x : S) :
    IsMarkovKernel (κ.subtype (κ.measurableSet_communicatingClass x)) ↔
      ∀ y, κ.Reaches x y → κ.Reaches y x := by
  rw [isMarkovKernel_subtype_iff_isClosedSet, isClosedSet_iff_forall_reaches_mem]
  simp only [mem_communicatingClass_iff]
  constructor
  · intro h y hxy
    exact ((communicates_def x y).mp (h x (Communicates.refl x) y hxy)).2
  · intro h y hxy z hyz
    have hxy' := (communicates_def x y).mp hxy
    exact (communicates_def x z).mpr ⟨hxy'.1.trans hyz, h z (hxy'.1.trans hyz)⟩

/-- Restriction to a closed communicating class is irreducible for counting measure. -/
theorem isIrreducible_subtype_communicatingClass [Countable S]
    [MeasurableSingletonClass S] (x : S) (hclosed : κ.IsClosedSet (κ.communicatingClass x)) :
    IsIrreducible Measure.count (κ.subtype (κ.measurableSet_communicatingClass x)) := by
  rw [isIrreducible_subtype_iff (κ.measurableSet_communicatingClass x) hclosed]
  intro y hy z hz
  exact ((mem_communicatingClass_iff x y).mp hy).symm.trans
    ((mem_communicatingClass_iff x z).mp hz)

end ProbabilityTheory.Kernel
