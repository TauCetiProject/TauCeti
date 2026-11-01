/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Kernel.ClosedClass
public import Mathlib.Order.Preorder.Finite

/-!
# Closed communicating classes in finite sets of states

Every state with only finitely many reachable states reaches a closed communicating class.
In particular, every nonempty finite closed set contains a closed communicating class, and
on a finite nonempty state space such a class always exists. These are the structural inputs
to the decomposition of a finite Markov chain into transient states and closed classes.

The ambient space may be countably infinite: only the relevant reachable set, or the closed
set trapping the chain, has to be finite. No Markov or finiteness assumption on the kernel
is needed for these structural statements. Closedness uses the countable-space
characterization by reachability, so these results apply to substochastic kernels as well.
They do not assert almost-sure entrance into a class.

The proof chooses a minimal reachable set among those reachable from the initial state.
Every state reachable from its representative must return to that representative, so its
communicating class is closed. This uses the existing reachability and closed-set APIs and
the finite-order minimal-element theorem.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press (1997), §1.2.
-/

public section

open MeasureTheory Set

namespace ProbabilityTheory.Kernel

variable {S : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]
    {κ : Kernel S S} {s : Set S}

/-- A state with finitely many reachable states reaches a closed communicating class.
The representative of the class is itself reachable from the initial state. -/
theorem exists_reaches_isClosedSet_communicatingClass_of_finite (κ : Kernel S S) (x : S)
    (hfinite : {y | κ.Reaches x y}.Finite) :
    ∃ y, κ.Reaches x y ∧ κ.IsClosedSet (κ.communicatingClass y) := by
  obtain ⟨y, hxy, hmin⟩ := hfinite.exists_minimalFor
    (fun y => {z | κ.Reaches y z}) _ ⟨x, Reaches.refl x⟩
  have hreturn : ∀ z, κ.Reaches y z → κ.Reaches z y := by
    intro z hyz
    have hsub : {w | κ.Reaches z w} ⊆ {w | κ.Reaches y w} :=
      fun w hzw => hyz.trans hzw
    exact hmin (hxy.trans hyz) hsub (Reaches.refl y)
  refine ⟨y, hxy, isClosedSet_iff_forall_reaches_mem.mpr ?_⟩
  intro z hz w hzw
  have hyz := (communicates_def y z).mp ((mem_communicatingClass_iff y z).mp hz)
  exact (mem_communicatingClass_iff y w).mpr <| (communicates_def y w).mpr
    ⟨hyz.1.trans hzw, hreturn w (hyz.1.trans hzw)⟩

/-- Every state of a finite state space reaches a closed communicating class. This does not
say that the class is entered almost surely, or that the entrance time has finite mean. -/
theorem exists_reaches_isClosedSet_communicatingClass [Finite S] (κ : Kernel S S) (x : S) :
    ∃ y, κ.Reaches x y ∧ κ.IsClosedSet (κ.communicatingClass y) :=
  exists_reaches_isClosedSet_communicatingClass_of_finite κ x (Set.toFinite _)

/-- A finite nonempty state space has a closed communicating class. -/
theorem exists_isClosedSet_communicatingClass [Finite S] [Nonempty S] (κ : Kernel S S) :
    ∃ y, κ.IsClosedSet (κ.communicatingClass y) := by
  obtain ⟨y, _, hy⟩ := exists_reaches_isClosedSet_communicatingClass κ
    (Classical.arbitrary S)
  exact ⟨y, hy⟩

/-- From each state of a finite closed set one can reach a closed communicating class
contained in that set, even when the ambient state space is infinite. -/
theorem IsClosedSet.exists_reaches_communicatingClass_subset (hclosed : κ.IsClosedSet s)
    (hfinite : s.Finite) {x : S} (hx : x ∈ s) :
    ∃ y ∈ s, κ.Reaches x y ∧ κ.IsClosedSet (κ.communicatingClass y) ∧
      κ.communicatingClass y ⊆ s := by
  have hstay := isClosedSet_iff_forall_reaches_mem.mp hclosed
  obtain ⟨y, hxy, hy⟩ := exists_reaches_isClosedSet_communicatingClass_of_finite κ x
    (hfinite.subset fun z hz => hstay x hx z hz)
  have hys := hstay x hx y hxy
  exact ⟨y, hys, hxy, hy, fun z hz =>
    hstay y hys z ((communicates_def y z).mp ((mem_communicatingClass_iff y z).mp hz)).1⟩

end ProbabilityTheory.Kernel
