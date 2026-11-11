/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Walk
public import TauCeti.Combinatorics.Quiver.Reachable

/-!
# Directed cycles and strong connectivity

This file characterizes the arrows that lie on directed cycles and uses that characterization to
relate weak and strong connectivity of an explicit arrow family. An arrow lies on a directed cycle
exactly when there is a directed walk back from its target to its source. Consequently, a weakly
connected arrow family is strongly connected exactly when every arrow lies on a directed cycle.

Weak connectivity is expressed through Mathlib's `Quiver.Symmetrify`, so parallel arrows and loops
retain their identities. The results require no finiteness assumptions.

## Main results

* `TauCeti.ArrowWalk.liesOnCycle_iff_nonempty`: an arrow lies on a directed cycle exactly when its
  target can reach its source.
* `TauCeti.isStronglyConnected_iff_isWeaklyConnected_and_forall_liesOnCycle`: the directed bridge
  criterion.

## References

* J. Bang-Jensen, G. Gutin, *Digraphs: Theory, Algorithms and Applications*, 2nd ed., Springer,
  2009, Section 5.3.
-/

public section

namespace TauCeti

universe u v

variable {V : Type u} {Q : V → V → Type v}

namespace ArrowWalk

variable {s t : V}

/-- An arrow lies on a directed cycle when some directed cycle traverses that arrow. -/
def LiesOnCycle (e : Q s t) : Prop :=
  ∃ (v : V) (c : ArrowWalk Q v v), c.IsCycle ∧ ⟨s, t, e⟩ ∈ c.arrows

/-- An arrow lies on a directed cycle exactly when some cycle's arrow list contains it. -/
theorem liesOnCycle_def (e : Q s t) :
    LiesOnCycle e ↔ ∃ (v : V) (c : ArrowWalk Q v v), c.IsCycle ∧ ⟨s, t, e⟩ ∈ c.arrows :=
  Iff.rfl

/-- A loop lies on the one-arrow directed cycle. -/
@[simp]
theorem liesOnCycle_loop (e : Q s s) : LiesOnCycle e :=
  ⟨s, (nil s).cons e, isCycle_loop e, by simp⟩

/-- An arrow lies on a directed cycle exactly when a directed walk returns from its target to its
source. -/
theorem liesOnCycle_iff_nonempty (e : Q s t) :
    LiesOnCycle e ↔ Nonempty (ArrowWalk Q t s) := by
  constructor
  · rintro ⟨v, c, -, he⟩
    obtain ⟨p₁, p₂, -⟩ := exists_eq_comp_cons_comp_of_mem_arrows he
    exact ⟨p₂.comp p₁⟩
  · rintro ⟨p⟩
    obtain ⟨q, hq, -⟩ := p.exists_isPath_arrows_subset
    exact ⟨t, q.cons e, hq.isCycle_cons e, by simp⟩

end ArrowWalk

/-- Every arrow of a strongly connected arrow family lies on a directed cycle. -/
theorem _root_.Quiver.IsStronglyConnected.liesOnCycle
    (h : @Quiver.IsStronglyConnected V ⟨Q⟩) {s t : V} (e : Q s t) :
    ArrowWalk.LiesOnCycle e :=
  (ArrowWalk.liesOnCycle_iff_nonempty e).2 (h t s)

/-- If every arrow lies on a directed cycle, every walk in the symmetrification can be replaced by
a directed walk with the same endpoints. -/
theorem nonempty_arrowWalk_of_symmetrify
    (hcycle : ∀ ⦃s t⦄ (e : Q s t), ArrowWalk.LiesOnCycle e) {s t : V}
    (p : Nonempty
      (@Quiver.Path (Quiver.Symmetrify V) (@Quiver.symmetrifyQuiver V ⟨Q⟩) s t)) :
    Nonempty (ArrowWalk Q s t) := by
  obtain ⟨p⟩ := p
  induction p with
  | nil => exact ⟨ArrowWalk.nil _⟩
  | @cons x y p e ih =>
    obtain ⟨q⟩ := ih
    rcases e with e | e
    · exact ⟨q.cons e⟩
    · obtain ⟨r⟩ := (ArrowWalk.liesOnCycle_iff_nonempty e).1 (hcycle e)
      exact ⟨q.comp r⟩

/-- **Directed bridge criterion.** An arrow family is strongly connected exactly when it is
weakly connected and every arrow lies on a directed cycle. -/
theorem isStronglyConnected_iff_isWeaklyConnected_and_forall_liesOnCycle :
    @Quiver.IsStronglyConnected V ⟨Q⟩ ↔
      @Quiver.IsStronglyConnected (Quiver.Symmetrify V) (@Quiver.symmetrifyQuiver V ⟨Q⟩) ∧
      ∀ ⦃s t⦄ (e : Q s t), ArrowWalk.LiesOnCycle e := by
  constructor
  · intro h
    exact ⟨@Quiver.IsStronglyConnected.isStronglyConnected_symmetrify V ⟨Q⟩ h,
      fun ⦃s t⦄ e ↦ h.liesOnCycle e⟩
  · rintro ⟨hweak, hcycle⟩ s t
    exact nonempty_arrowWalk_of_symmetrify hcycle (hweak s t)

end TauCeti
