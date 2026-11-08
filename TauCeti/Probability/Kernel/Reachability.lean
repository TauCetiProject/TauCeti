/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Kernel.Irreducible
public import TauCeti.Probability.Kernel.Composition.Power

/-!
# Reachability and communication for kernels

For a kernel `κ` on a measurable space, a state `y` is *reachable* from `x` if some power of `κ`
(including the zeroth) assigns positive mass to `y`, and two states *communicate* if they are
mutually reachable. Reachability is reflexive; when the singletons are measurable it is
transitive, communication is an equivalence relation, and Mathlib's `Kernel.IsIrreducible`
with respect to the counting measure is equivalent to every state reaching every other state,
equivalently to every pair of states communicating.
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
theorem Reaches.trans [MeasurableSingletonClass S] {x y z : S}
    (hxy : κ.Reaches x y) (hyz : κ.Reaches y z) : κ.Reaches x z := by
  obtain ⟨n, hn⟩ := hxy
  obtain ⟨m, hm⟩ := hyz
  exact ⟨n + m, pow_add_apply_pos (measurableSet_singleton z) hn hm⟩

/-- Every state communicates with itself. -/
@[simp] theorem Communicates.refl (x : S) : κ.Communicates x x :=
    ⟨Reaches.refl x, Reaches.refl x⟩

/-- Communication is symmetric. -/
theorem Communicates.symm {x y : S} (h : κ.Communicates x y) : κ.Communicates y x :=
  ⟨h.2, h.1⟩

/-- Communication is transitive. -/
theorem Communicates.trans [MeasurableSingletonClass S] {x y z : S}
    (hxy : κ.Communicates x y) (hyz : κ.Communicates y z) : κ.Communicates x z :=
  ⟨hxy.1.trans hyz.1, hyz.2.trans hxy.2⟩

/-- Communication is commutative: two states communicate in one order if and only if they
communicate in the other. -/
theorem communicates_comm (x y : S) : κ.Communicates x y ↔ κ.Communicates y x :=
  ⟨fun h => h.symm, fun h => h.symm⟩

/-- Communication is an equivalence relation on the state space. -/
theorem communicates_equivalence [MeasurableSingletonClass S] :
    Equivalence κ.Communicates := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact Communicates.refl x
  · intro x y h
    exact h.symm
  · intro x y z hxy hyz
    exact hxy.trans hyz

/-- A kernel is irreducible with respect to the counting measure if and only if every state
reaches every state. -/
theorem isIrreducible_count_iff_forall_reaches [MeasurableSingletonClass S] :
    IsIrreducible Measure.count κ ↔ ∀ x y : S, κ.Reaches x y := by
  constructor
  · intro h x y
    have hpos : Measure.count {y} > 0 := by
      rw [Measure.count_singleton y]
      exact one_pos
    exact h.irreducible (measurableSet_singleton y) hpos x
  · intro h
    refine ⟨?_⟩
    intro s hs hA x
    obtain ⟨y, hy⟩ := Measure.count_ne_zero_iff.mp (Ne.symm (ne_of_lt hA))
    obtain ⟨n, hn⟩ := h x y
    use n
    exact lt_of_lt_of_le hn (measure_mono (Set.singleton_subset_iff.mpr hy))

/-- A kernel is irreducible with respect to the counting measure if and only if every pair of
states communicates. -/
theorem isIrreducible_count_iff_forall_communicates [MeasurableSingletonClass S] :
    IsIrreducible Measure.count κ ↔ ∀ x y : S, κ.Communicates x y := by
  rw [isIrreducible_count_iff_forall_reaches]
  exact ⟨fun h x y => ⟨h x y, h y x⟩, fun h x y => (h x y).1⟩

end ProbabilityTheory.Kernel
