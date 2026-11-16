/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Kernel.Irreducible
public import TauCeti.Probability.Kernel.Composition.Power
import Mathlib.Order.Preorder.Finite
import TauCeti.MeasureTheory.Measure.GiryMonad

/-!
# Reachability and communication for kernels

For a kernel `κ` on a measurable space, a state `y` is *reachable* from `x` if some power of `κ`
(including the zeroth) assigns positive mass to `y`, and two states *communicate* if they are
mutually reachable. Reachability is reflexive and transitive, communication is an equivalence
relation, and Mathlib's `Kernel.IsIrreducible` with respect to the counting measure is
equivalent to every state reaching every other state, equivalently to every pair of states
communicating. Positive singleton mass of an invariant measure propagates along reachability, so
under counting-measure irreducibility every nonzero invariant measure charges every singleton. A
state with finitely many reachable states reaches a state from which every reachable state can
return.
-/

public section

open MeasureTheory

namespace ProbabilityTheory.Kernel

variable {S : Type*} [MeasurableSpace S] {κ : Kernel S S}

/-- A state `y` is reachable from `x` for the kernel `κ` if some power of `κ`, including the
zeroth, assigns positive mass to `y`. -/
def Reaches (κ : Kernel S S) (x y : S) : Prop :=
    ∃ n : ℕ, 0 < (κ ^ n) x {y}

/-- Two states `x` and `y` communicate for the kernel `κ` if each is reachable from the other. -/
def Communicates (κ : Kernel S S) (x y : S) : Prop :=
    κ.Reaches x y ∧ κ.Reaches y x

/-- The communicating class of a state consists of all states communicating with it. -/
def communicatingClass (κ : Kernel S S) (x : S) : Set S :=
  {y | κ.Communicates x y}

/-- Membership in a communicating class is communication with its representative. -/
@[simp]
theorem mem_communicatingClass_iff (x y : S) :
    y ∈ κ.communicatingClass x ↔ κ.Communicates x y := (Iff.rfl)

/-- Communicating classes are measurable on countable spaces with measurable singletons. -/
@[measurability]
theorem measurableSet_communicatingClass [Countable S] [MeasurableSingletonClass S]
    (κ : Kernel S S) (x : S) : MeasurableSet (κ.communicatingClass x) :=
  (Set.to_countable _).measurableSet

/-- `Communicates` unfolds to mutual reachability of the two states. -/
theorem communicates_def (x y : S) : κ.Communicates x y ↔ κ.Reaches x y ∧ κ.Reaches y x :=
    Iff.rfl

/-- `Reaches` unfolds to the existence of a power of the kernel assigning positive mass to the
target state. -/
theorem reaches_def (x y : S) :
    κ.Reaches x y ↔ ∃ n : ℕ, 0 < (κ ^ n) x {y} := Iff.rfl

/-- Reachability under a deterministic kernel is membership in the forward orbit. -/
@[simp]
theorem reaches_deterministic [MeasurableSingletonClass S] {f : S → S}
    (hf : Measurable f) (x y : S) :
    (deterministic f hf).Reaches x y ↔ ∃ n : ℕ, f^[n] x = y := by
  simp [reaches_def, deterministic_pow, deterministic_apply, pos_iff_ne_zero,
    Set.indicator_apply_eq_zero]

/-- Every state reaches itself. -/
@[simp] theorem Reaches.refl (x : S) : κ.Reaches x x := by
  use 0
  -- the zeroth power of a kernel is the identity kernel, hence the Dirac mass at the state;
  -- `rw [pow_zero]` would leave the numeral `1`, which simp does not unfold to `Kernel.id`
  rw [show (κ ^ 0 : Kernel S S) = Kernel.id from rfl,
    Kernel.id_apply, Measure.dirac_apply_of_mem (Set.mem_singleton_iff.2 rfl)]
  simp

/-- A positive one-step transition mass implies reachability. -/
theorem reaches_of_pos {x y : S} (h : 0 < κ x {y}) : κ.Reaches x y := by
  use 1
  simpa [pow_one] using h

/-- Reachability is transitive. -/
theorem Reaches.trans {x y z : S}
    (hxy : κ.Reaches x y) (hyz : κ.Reaches y z) : κ.Reaches x z := by
  obtain ⟨n, hn⟩ := hxy
  obtain ⟨m, hm⟩ := hyz
  exact ⟨n + m, pow_add_apply_pos hn hm⟩

/-- Every state communicates with itself. -/
@[simp] theorem Communicates.refl (x : S) : κ.Communicates x x :=
    ⟨Reaches.refl x, Reaches.refl x⟩

/-- Communication is symmetric. -/
theorem Communicates.symm {x y : S} (h : κ.Communicates x y) : κ.Communicates y x :=
  ⟨h.2, h.1⟩

/-- Communication is transitive. -/
theorem Communicates.trans {x y z : S}
    (hxy : κ.Communicates x y) (hyz : κ.Communicates y z) : κ.Communicates x z :=
  ⟨hxy.1.trans hyz.1, hyz.2.trans hxy.2⟩

/-- Communication is commutative: two states communicate in one order if and only if they
communicate in the other. -/
theorem communicates_comm (x y : S) : κ.Communicates x y ↔ κ.Communicates y x :=
  ⟨fun h => h.symm, fun h => h.symm⟩

/-- Communication is an equivalence relation on the state space. -/
theorem communicates_equivalence :
    Equivalence κ.Communicates := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact Communicates.refl x
  · intro x y h
    exact h.symm
  · intro x y z hxy hyz
    exact hxy.trans hyz

/-- Under counting-measure irreducibility every state reaches every other state. -/
theorem exists_pos_pow_apply_singleton [IsIrreducible Measure.count κ] (x y : S) :
    ∃ n, 0 < (κ ^ n) x {y} := by
  by_contra! h
  -- Without measurable singletons, use a measurable superset of `{y}` of the same mass for all `n`.
  obtain ⟨A, hyA, hA, hEq⟩ := exists_measurable_superset_forall_eq (fun n : ℕ => (κ ^ n) x) {y}
  obtain ⟨n, hn⟩ := IsIrreducible.irreducible (φ := Measure.count) (κ := κ) hA
    (pos_iff_ne_zero.mpr (Measure.count_ne_zero_iff.mpr ⟨y, hyA rfl⟩)) x
  exact hn.not_ge ((hEq n).trans_le (h n))

/-- A kernel is irreducible with respect to the counting measure if and only if every state
reaches every state. -/
theorem isIrreducible_count_iff_forall_reaches :
    IsIrreducible Measure.count κ ↔ ∀ x y : S, κ.Reaches x y := by
  constructor
  · intro h x y
    exact exists_pos_pow_apply_singleton x y
  · intro h
    refine ⟨?_⟩
    intro s _ hA x
    obtain ⟨y, hy⟩ := Measure.count_ne_zero_iff.mp (Ne.symm (ne_of_lt hA))
    obtain ⟨n, hn⟩ := h x y
    use n
    exact lt_of_lt_of_le hn (measure_mono (Set.singleton_subset_iff.mpr hy))

/-- A kernel is irreducible with respect to the counting measure if and only if every pair of
states communicates. -/
theorem isIrreducible_count_iff_forall_communicates :
    IsIrreducible Measure.count κ ↔ ∀ x y : S, κ.Communicates x y := by
  rw [isIrreducible_count_iff_forall_reaches]
  exact ⟨fun h x y => ⟨h x y, h y x⟩, fun h x y => (h x y).1⟩

/-- A state with finitely many reachable states reaches a state all of whose reachable states
can reach it back. -/
theorem exists_reaches_forall_reaches_reaches_of_finite (κ : Kernel S S) {x : S}
    (hfinite : {y | κ.Reaches x y}.Finite) :
    ∃ y, κ.Reaches x y ∧ ∀ z, κ.Reaches y z → κ.Reaches z y := by
  -- Choose a minimal reachable set using the finite-order minimal-element theorem.
  obtain ⟨y, hxy, hmin⟩ := hfinite.exists_minimalFor
    (fun y => {z | κ.Reaches y z}) _ ⟨x, Reaches.refl x⟩
  exact ⟨y, hxy, fun z hyz => hmin (hxy.trans hyz) (fun w hzw => hyz.trans hzw) (Reaches.refl y)⟩

/-- An irreducible s-finite kernel with respect to the counting measure lives on a countable state
space with measurable singletons: every state is reached from a fixed state, and each s-finite
measure `(κ ^ n) x` has only countably many atoms. -/
theorem countable_of_isIrreducible_count [MeasurableSingletonClass S] [IsSFiniteKernel κ]
    [IsIrreducible Measure.count κ] : Countable S := by
  rcases isEmpty_or_nonempty S with hS | ⟨⟨x⟩⟩
  · infer_instance
  · have hc : (⋃ n : ℕ, {y | 0 < (κ ^ n) x {y}}).Countable :=
      Set.countable_iUnion fun n => Measure.countable_meas_pos_of_disjoint_iUnion
        (fun y => measurableSet_singleton y) fun _ _ h => Set.disjoint_singleton.mpr h
    exact Set.countable_univ_iff.mp (hc.mono fun y _ =>
      Set.mem_iUnion.mpr ((reaches_def x y).mp
        (isIrreducible_count_iff_forall_reaches.mp ‹_› x y)))

/-- Positive singleton mass of an invariant measure propagates along reachable transitions. -/
theorem Invariant.apply_singleton_pos_of_reaches {μ : Measure S} (hμ : κ.Invariant μ) {x y : S}
    (hx : 0 < μ {x}) (hxy : κ.Reaches x y) :
    0 < μ {y} := by
  obtain ⟨n, hn⟩ := (reaches_def x y).mp hxy
  have hle := Measure.singleton_mul_apply_le_bind_apply μ (κ ^ n).aemeasurable x (s := {y})
  rw [(hμ.pow n).def] at hle
  exact (ENNReal.mul_pos hx.ne' hn.ne').trans_le hle

/-- Under counting-measure irreducibility, every nonzero invariant measure charges every
singleton. -/
theorem Invariant.apply_singleton_pos_of_ne_zero
    [IsIrreducible Measure.count κ] {μ : Measure S} (hμ : κ.Invariant μ) (hμ0 : μ ≠ 0) (x : S) :
    0 < μ {x} := by
  by_contra hx0
  set A := toMeasurable μ {x}
  have hA : MeasurableSet A := measurableSet_toMeasurable μ {x}
  have hzero : ∀ n : ℕ, μ {z | (κ ^ n) z A ≠ 0} = 0 := fun n => by
    have hint : ∫⁻ z, (κ ^ n) z A ∂μ = 0 := by
      rw [← Measure.bind_apply hA (κ ^ n).aemeasurable, (hμ.pow n).def, measure_toMeasurable]
      exact nonpos_iff_eq_zero.mp (not_lt.mp hx0)
    exact ae_iff.mp (((lintegral_eq_zero_iff
      ((κ ^ n).measurable_coe hA)).mp hint).mono fun _ hz => hz)
  have huniv : (⋃ n : ℕ, {z : S | (κ ^ n) z A ≠ 0}) = Set.univ := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_pos_pow_apply_singleton (κ := κ) z x
    exact ⟨n, (hn.trans_le (measure_mono (subset_toMeasurable μ {x}))).ne'⟩
  have hμ_univ : μ Set.univ = 0 := by
    rw [← huniv]
    exact measure_iUnion_null hzero
  exact hμ0 (Measure.measure_univ_eq_zero.mp hμ_univ)

/-- Under counting-measure irreducibility, every invariant probability measure charges every
singleton. -/
theorem Invariant.apply_singleton_pos
    [IsIrreducible Measure.count κ] {π : Measure S} [IsProbabilityMeasure π]
    (hπ : κ.Invariant π) (x : S) :
    0 < π {x} :=
  hπ.apply_singleton_pos_of_ne_zero (IsProbabilityMeasure.ne_zero π) x

end ProbabilityTheory.Kernel
