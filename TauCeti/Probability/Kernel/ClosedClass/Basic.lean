/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Kernel.Reachability
public import TauCeti.Probability.Kernel.Composition.Power
public import Mathlib.Probability.Kernel.Composition.CompMap
import TauCeti.Probability.Kernel.PMF

/-!
# Closed sets of states and communicating classes

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

Every state with only finitely many reachable states reaches a closed communicating class.
In particular, every nonempty finite closed set contains a closed communicating class, and
on a finite nonempty state space such a class always exists. Only the relevant reachable
set, or the closed set trapping the chain, has to be finite; no Markov or finiteness
assumption on the kernel is needed. These structural results do not assert almost-sure
entrance into a class.

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

/-- A measurable closed set contains every state reachable from one of its members. -/
theorem IsClosedSet.mem_of_reaches (hs : MeasurableSet s) (hclosed : κ.IsClosedSet s) {x y : S}
    (hx : x ∈ s) (hxy : κ.Reaches x y) : y ∈ s := by
  obtain ⟨n, hn⟩ := (reaches_def x y).mp hxy
  by_contra hys
  have hle := measure_mono (μ := (κ ^ n) x) (singleton_subset_iff.mpr hys : {y} ⊆ sᶜ)
  exact hn.not_ge (pow_apply_compl_eq_zero κ hs hclosed n hx ▸ hle)

/-- On a countable state space, one-step closure is equivalent to closure under
reachability at arbitrary finite times. -/
theorem isClosedSet_iff_forall_reaches_mem [Countable S]
    [MeasurableSingletonClass S] :
    κ.IsClosedSet s ↔ ∀ x ∈ s, ∀ y, κ.Reaches x y → y ∈ s := by
  constructor
  · intro h x hx y hy
    exact h.mem_of_reaches (to_countable s).measurableSet hx hy
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
theorem isIrreducible_subtype_iff (hs : MeasurableSet s)
    (hclosed : κ.IsClosedSet s) :
    IsIrreducible Measure.count (κ.subtype hs) ↔
      ∀ x ∈ s, ∀ y ∈ s, κ.Communicates x y := by
  simp only [isIrreducible_count_iff_forall_communicates,
    communicates_subtype_iff hs hclosed]
  exact ⟨fun h x hx y hy => h ⟨x, hx⟩ ⟨y, hy⟩, fun h x y => h x x.property y y.property⟩

/-- A communicating class is closed exactly when every state reachable from its
representative can reach the representative again. No Markov assumption is needed. -/
theorem isClosedSet_communicatingClass_iff [Countable S]
    [MeasurableSingletonClass S] (x : S) :
    κ.IsClosedSet (κ.communicatingClass x) ↔ ∀ y, κ.Reaches x y → κ.Reaches y x := by
  rw [isClosedSet_iff_forall_reaches_mem]
  simp only [mem_communicatingClass_iff]
  constructor
  · intro h y hxy
    exact ((communicates_def x y).mp (h x (Communicates.refl x) y hxy)).2
  · intro h y hxy z hyz
    have hxy' := (communicates_def x y).mp hxy
    exact (communicates_def x z).mpr ⟨hxy'.1.trans hyz, h z (hxy'.1.trans hyz)⟩

/-- The communicating class of `x` supports a Markov restriction exactly when every
state reachable from `x` can reach `x` again. This is the closed-class criterion. -/
theorem isMarkovKernel_subtype_communicatingClass_iff [Countable S]
    [MeasurableSingletonClass S] [IsMarkovKernel κ] (x : S) :
    IsMarkovKernel (κ.subtype (κ.measurableSet_communicatingClass x)) ↔
      ∀ y, κ.Reaches x y → κ.Reaches y x := by
  rw [isMarkovKernel_subtype_iff_isClosedSet, isClosedSet_communicatingClass_iff]

/-- Reachability between two states of a communicating class is preserved by restriction to
the class: every state on a positive-probability path between class members is itself in the
class. -/
theorem reaches_subtype_communicatingClass [Countable S] [MeasurableSingletonClass S] (x : S)
    {y z : S} (hy : y ∈ κ.communicatingClass x) (hz : z ∈ κ.communicatingClass x) :
    (κ.subtype (κ.measurableSet_communicatingClass x)).Reaches ⟨y, hy⟩ ⟨z, hz⟩ := by
  obtain ⟨n, hn⟩ := (reaches_def y z).mp
    (((communicates_def y z).mp (((mem_communicatingClass_iff x y).mp hy).symm.trans
      ((mem_communicatingClass_iff x z).mp hz))).1)
  suffices key : ∀ (n : ℕ) (a : κ.communicatingClass x), 0 < (κ ^ n) a.1 {z} →
      0 < ((κ.subtype (κ.measurableSet_communicatingClass x)) ^ n) a {⟨z, hz⟩} from
    (reaches_def _ _).mpr ⟨n, key n ⟨y, hy⟩ hn⟩
  intro n
  induction n with
  | zero =>
    intro a ha
    have haz : a = ⟨z, hz⟩ := Subtype.ext (by
      by_contra hne
      rw [pow_zero, one_def, Kernel.id_apply,
        Measure.dirac_apply' _ (measurableSet_singleton z),
        indicator_of_notMem (by simpa using hne)] at ha
      exact lt_irrefl _ ha)
    subst haz
    rw [pow_zero, one_def, Kernel.id_apply,
      Measure.dirac_apply_of_mem (Set.mem_singleton_iff.2 rfl)]
    simp
  | succ n ih =>
    intro a ha
    rw [add_comm n 1, pow_add_apply_singleton κ 1 n, pos_iff_ne_zero, Ne, tsum_eq_zero_iff] at ha
    push Not at ha
    obtain ⟨w, hw⟩ := ha
    have hw1 : 0 < κ a.1 {w} := by simpa [pos_iff_ne_zero] using left_ne_zero_of_mul hw
    have hw2 : 0 < (κ ^ n) w {z} := by simpa [pos_iff_ne_zero] using right_ne_zero_of_mul hw
    have haw : κ.Reaches a.1 w := reaches_of_pos hw1
    have hwx : κ.Communicates x w := by
      have hz' := (mem_communicatingClass_iff x z).mp hz
      have ha' := (mem_communicatingClass_iff x a.1).mp a.2
      rw [communicates_def] at ha' hz' ⊢
      exact ⟨ha'.1.trans haw, ((reaches_def w z).mpr ⟨n, hw2⟩).trans hz'.2⟩
    have hwC : w ∈ κ.communicatingClass x := (mem_communicatingClass_iff x w).mpr hwx
    have := ih ⟨w, hwC⟩ hw2
    rw [add_comm]
    exact pow_add_apply_pos (by simpa using hw1) this

/-- Restriction to a communicating class is irreducible for counting measure. -/
theorem isIrreducible_subtype_communicatingClass [Countable S]
    [MeasurableSingletonClass S] (x : S) :
    IsIrreducible Measure.count (κ.subtype (κ.measurableSet_communicatingClass x)) := by
  rw [isIrreducible_count_iff_forall_reaches]
  rintro ⟨y, hy⟩ ⟨z, hz⟩
  exact reaches_subtype_communicatingClass x hy hz

section Finite

variable [Countable S] [MeasurableSingletonClass S]

omit [MeasurableSingletonClass S] in
/-- A state with finitely many reachable states reaches a closed communicating class.
The representative of the class is itself reachable from the initial state. -/
theorem exists_reaches_isClosedSet_communicatingClass_of_finite (κ : Kernel S S) (x : S)
    (hfinite : {y | κ.Reaches x y}.Finite) :
    ∃ y, κ.Reaches x y ∧ κ.IsClosedSet (κ.communicatingClass y) := by
  obtain ⟨y, hxy, hret⟩ := exists_reaches_forall_reaches_reaches_of_finite κ hfinite
  refine ⟨y, hxy, fun w hw => ?_⟩
  refine (measure_null_iff_singleton (to_countable _)).mpr fun z hz => ?_
  by_contra hpos
  have hyz : κ.Reaches y z :=
    ((communicates_def y w).mp ((mem_communicatingClass_iff y w).mp hw)).1.trans
      (reaches_of_pos (pos_iff_ne_zero.mpr hpos))
  exact hz ((mem_communicatingClass_iff y z).mpr ((communicates_def y z).mpr ⟨hyz, hret z hyz⟩))

omit [Countable S] [MeasurableSingletonClass S] in
/-- Every state of a finite state space reaches a closed communicating class. This does not
say that the class is entered almost surely, or that the entrance time has finite mean. -/
theorem exists_reaches_isClosedSet_communicatingClass [Finite S] (κ : Kernel S S) (x : S) :
    ∃ y, κ.Reaches x y ∧ κ.IsClosedSet (κ.communicatingClass y) :=
  exists_reaches_isClosedSet_communicatingClass_of_finite κ x (Set.toFinite _)

omit [Countable S] [MeasurableSingletonClass S] in
/-- A finite nonempty state space has a closed communicating class. -/
theorem exists_isClosedSet_communicatingClass [Finite S] [Nonempty S] (κ : Kernel S S) :
    ∃ y, κ.IsClosedSet (κ.communicatingClass y) := by
  obtain ⟨y, _, hy⟩ := exists_reaches_isClosedSet_communicatingClass κ
    (Classical.arbitrary S)
  exact ⟨y, hy⟩

omit [Countable S] in
/-- From each state of a finite closed set one can reach a closed communicating class
contained in that set, even when the ambient state space is infinite. -/
theorem IsClosedSet.exists_reaches_communicatingClass_subset (hclosed : κ.IsClosedSet s)
    (hfinite : s.Finite) {x : S} (hx : x ∈ s) :
    ∃ y ∈ s, κ.Reaches x y ∧ κ.IsClosedSet (κ.communicatingClass y) ∧
      κ.communicatingClass y ⊆ s := by
  have hstay : ∀ x ∈ s, ∀ y, κ.Reaches x y → y ∈ s := fun x hx y hy =>
    hclosed.mem_of_reaches hfinite.measurableSet hx hy
  have hreach : {y | κ.Reaches x y}.Finite := hfinite.subset fun z hz => hstay x hx z hz
  obtain ⟨y, hxy, hret⟩ := exists_reaches_forall_reaches_reaches_of_finite κ hreach
  have hys := hstay x hx y hxy
  have hsub : κ.communicatingClass y ⊆ s := fun z hz =>
    hstay y hys z ((communicates_def y z).mp ((mem_communicatingClass_iff y z).mp hz)).1
  refine ⟨y, hys, hxy, fun w hw => ?_, hsub⟩
  have hws := hsub hw
  have hcompl : (κ.communicatingClass y)ᶜ ⊆ sᶜ ∪ (s \ κ.communicatingClass y) := by
    intro z hz
    by_cases hzs : z ∈ s
    · exact Or.inr ⟨hzs, hz⟩
    · exact Or.inl hzs
  refine measure_mono_null hcompl (measure_union_null (hclosed w hws) ?_)
  refine (measure_null_iff_singleton (hfinite.subset sdiff_subset).countable).mpr fun z hz => ?_
  by_contra hpos
  have hyz : κ.Reaches y z :=
    ((communicates_def y w).mp ((mem_communicatingClass_iff y w).mp hw)).1.trans
      (reaches_of_pos (pos_iff_ne_zero.mpr hpos))
  exact hz.2 ((mem_communicatingClass_iff y z).mpr ((communicates_def y z).mpr ⟨hyz, hret z hyz⟩))

end Finite

end ProbabilityTheory.Kernel
