/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Probability.Kernel.Irreducible
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Reachability and communication for kernels

For a kernel `κ` on a measurable space, a state `y` is *reachable* from `x` if some power of `κ`
(including the zeroth) assigns positive mass to `y`, and two states *communicate* if they are
mutually reachable. This file proves that reachability is reflexive and transitive (the latter via
the Chapman-Kolmogorov equation on countable spaces with measurable singletons) and that
communication is an equivalence relation, then bridges both to Mathlib's
`Kernel.IsIrreducible` with respect to the counting measure.
-/

public section

open MeasureTheory

namespace ProbabilityTheory.Kernel

variable {S : Type*} [MeasurableSpace S] (κ : Kernel S S)

/-- A state `y` is reachable from `x` for the kernel `κ` if some power of `κ`, including the
zeroth, assigns positive mass to `y`. -/
def Reaches (x y : S) : Prop :=
    ∃ n : ℕ, 0 < (κ ^ n) x {y}

/-- Two states `x` and `y` communicate for the kernel `κ` if each is reachable from the other. -/
def Communicates (x y : S) : Prop :=
    κ.Reaches x y ∧ κ.Reaches y x

/-- `Reaches` unfolds to the existence of a power of the kernel assigning positive mass to the
target state. -/
theorem reaches_def (x y : S) :
    κ.Reaches x y ↔ ∃ n : ℕ, 0 < (κ ^ n) x {y} := Iff.rfl

/-- Every state reaches itself: the zeroth power of a kernel is the identity kernel, hence the
Dirac mass at the state. -/
theorem Reaches.refl [MeasurableSingletonClass S] (x : S) : κ.Reaches x x := by
  use 0
  rw [pow_zero]
  change 0 < (Kernel.id x) {x}
  rw [Kernel.id_apply, Measure.dirac_apply' _ (measurableSet_singleton x)]
  simp

/-- A positive one-step transition mass implies reachability. -/
theorem reaches_of_pos (x y : S) (h : 0 < κ x {y}) : κ.Reaches x y := by
  use 1
  simpa [pow_one] using h

/-- Reachability is transitive: paths of positive mass can be concatenated using the
Chapman-Kolmogorov equation. -/
theorem Reaches.trans [Countable S] [MeasurableSingletonClass S] (x y z : S)
    (hxy : κ.Reaches x y) (hyz : κ.Reaches y z) : κ.Reaches x z := by
  obtain ⟨n, hn⟩ := hxy
  obtain ⟨m, hm⟩ := hyz
  use n + m
  have hyz_y : 0 < (κ ^ m) y {z} * (κ ^ n) x {y} := by
    rw [ENNReal.mul_pos_iff]
    exact ⟨hm, hn⟩
  have hsum : 0 < ∑' b, (κ ^ m) b {z} * (κ ^ n) x {b} :=
    lt_of_lt_of_le hyz_y (ENNReal.le_tsum (f := fun b => (κ ^ m) b {z} * (κ ^ n) x {b}) (y : S))
  rw [Kernel.pow_add_apply_eq_lintegral _ n m _ (measurableSet_singleton z), lintegral_countable']
  exact hsum

/-- Every state communicates with itself. -/
theorem Communicates.refl [MeasurableSingletonClass S] (x : S) : κ.Communicates x x :=
  ⟨Reaches.refl κ x, Reaches.refl κ x⟩

/-- Communication is symmetric. -/
theorem Communicates.symm (x y : S) (h : κ.Communicates x y) : κ.Communicates y x :=
  ⟨h.2, h.1⟩

/-- Communication is transitive. -/
theorem Communicates.trans [Countable S] [MeasurableSingletonClass S] (x y z : S)
    (hxy : κ.Communicates x y) (hyz : κ.Communicates y z) : κ.Communicates x z :=
  ⟨Reaches.trans κ x y z hxy.1 hyz.1, Reaches.trans κ z y x hyz.2 hxy.2⟩

/-- Communication is commutative: two states communicate in one order if and only if they
communicate in the other. -/
theorem communicates_comm (x y : S) : κ.Communicates x y ↔ κ.Communicates y x :=
  ⟨fun h => h.symm, fun h => h.symm⟩

/-- Communication is an equivalence relation on the state space. -/
theorem communicates_equivalence [Countable S] [MeasurableSingletonClass S] :
    Equivalence κ.Communicates := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact Communicates.refl κ x
  · intro x y h
    exact Communicates.symm κ x y h
  · intro x y z hxy hyz
    exact Communicates.trans κ x y z hxy hyz

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
