/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.CyclicallyReduced
public import Mathlib.SetTheory.Cardinal.Finite

import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.GroupTheory.Perm.Cycle.Basic

/-!
# Circuits through the components of 2-regular Serre graphs

A path of a Serre graph traverses each geometric edge at most once when the list of the geometric
edges of its darts has no duplicates. Such a path never backtracks, and a closed one does not
backtrack cyclically either: it is cyclically reduced.

In a finite Serre graph in which exactly two darts start at every vertex, the component of every
vertex `a` is traversed by a circuit: some closed path at `a` traverses every geometric edge of the
component exactly once. After a dart `e`, the path continues along the dart at the target of `e`
other than the reverse of `e`; this successor map is a permutation of the darts, and none of its
cycles contains a dart together with its reverse. This is the graph-theoretic fact behind the
contours of a polygonal surface: its boundary graph is finite and 2-regular, so each of its
components is traversed by a circuit.

## Main results

* `TauCeti.SerreGraph.Path.isCyclicallyReduced_of_nodup_map_toGeomEdge_darts`: a closed path
  traversing each geometric edge at most once is cyclically reduced.
* `TauCeti.SerreGraph.exists_path_nodup_map_toGeomEdge_darts_and_mem`: in a finite 2-regular
  Serre graph, a closed path at any vertex traverses every geometric edge of its component exactly
  once.

## References

* J. Gallier, D. Xu, *A Guide to the Classification Theorem for Compact Surfaces*, Springer, 2013,
  §4.6, p. 51 and Chapter 6, p. 87 (contours, the components of the boundary). The existence of a
  circuit in a finite 2-regular graph is elementary and is not proved there.
-/

public section

namespace TauCeti.SerreGraph

variable (Γ : SerreGraph)

/-- A path traversing each geometric edge at most once is reduced: no dart of it is followed by its
reverse. -/
theorem Path.isReduced_of_nodup_map_toGeomEdge_darts {a b : Γ.V} {p : Γ.Path a b}
    (hp : ((Path.darts Γ p).map Γ.toGeomEdge).Nodup) : Path.IsReduced Γ p := by
  rw [Path.isReduced_iff_isChain]
  refine List.isChain_of_isChain_map Γ.toGeomEdge (S := (· ≠ ·)) (fun e f hef hfe => ?_)
    hp.isChain
  exact hef (by rw [hfe, toGeomEdge_rev])

/-- A closed path traversing each geometric edge at most once is cyclically reduced: it does not
backtrack, also not from its last dart to its first. -/
theorem Path.isCyclicallyReduced_of_nodup_map_toGeomEdge_darts {a : Γ.V} {p : Γ.Path a a}
    (hp : ((Path.darts Γ p).map Γ.toGeomEdge).Nodup) : Path.IsCyclicallyReduced Γ p := by
  have hred := Path.isReduced_of_nodup_map_toGeomEdge_darts Γ hp
  refine (Path.isCyclicallyReduced_iff Γ p).2 <|
    (Path.isReduced_comp_iff Γ p p).2 ⟨hred, hred, fun e he f hf hfe => ?_⟩
  obtain ⟨l, hl⟩ := List.head?_eq_some_iff.1 hf
  rw [hl, List.map_cons, List.nodup_cons] at hp
  rw [hl] at he
  rcases List.mem_cons.1 (List.mem_of_mem_getLast? he) with rfl | he'
  · exact Γ.rev_ne e hfe.symm
  · exact hp.1 (List.mem_map.2 ⟨e, he', by rw [hfe, toGeomEdge_rev]⟩)

variable {Γ}

/-! ### Circuits in 2-regular graphs

When exactly two darts start at every vertex, `other e` is the dart at the source of `e` other than
`e`, and `next e = other (rev e)` is the dart following `e` along the circuit. The cycle of `next`
through `e`, listed up to the period of `e`, is the circuit through `e`. -/

section TwoRegular

variable (hΓ : ∀ x, Nat.card {e : Γ.E // Γ.src e = x} = 2)
include hΓ

private theorem existsUnique_ne (e : Γ.E) :
    ∃! f : {f : Γ.E // Γ.src f = Γ.src e}, f ≠ ⟨e, rfl⟩ :=
  (Nat.card_eq_two_iff' _).1 (hΓ _)

private noncomputable def other (e : Γ.E) : Γ.E := (existsUnique_ne hΓ e).exists.choose.1

private theorem src_other (e : Γ.E) : Γ.src (other hΓ e) = Γ.src e :=
  (existsUnique_ne hΓ e).exists.choose.2

private theorem other_ne (e : Γ.E) : other hΓ e ≠ e := fun h =>
  (existsUnique_ne hΓ e).exists.choose_spec (Subtype.ext h)

private theorem eq_other_of_ne {e f : Γ.E} (hf : Γ.src f = Γ.src e) (hne : f ≠ e) :
    f = other hΓ e :=
  congrArg Subtype.val <| (existsUnique_ne hΓ e).unique (y₁ := ⟨f, hf⟩)
    (fun h => hne (congrArg Subtype.val h)) (existsUnique_ne hΓ e).exists.choose_spec

private theorem other_other (e : Γ.E) : other hΓ (other hΓ e) = e :=
  (eq_other_of_ne hΓ (src_other hΓ e).symm (other_ne hΓ e).symm).symm

private noncomputable def next : Equiv.Perm Γ.E where
  toFun e := other hΓ (Γ.rev e)
  invFun e := Γ.rev (other hΓ e)
  left_inv e := by simp only [other_other, rev_rev]
  right_inv e := by simp only [other_other, rev_rev]

private theorem next_apply (e : Γ.E) : next hΓ e = other hΓ (Γ.rev e) := rfl

private theorem src_next (e : Γ.E) : Γ.src (next hΓ e) = Γ.tgt e := by
  rw [next_apply, src_other, src_rev]

private theorem next_rev_next (e : Γ.E) : next hΓ (Γ.rev (next hΓ e)) = Γ.rev e := by
  rw [next_apply, next_apply, rev_rev, other_other]

private theorem pow_rev_pow (m : ℕ) (e : Γ.E) :
    (next hΓ ^ m) (Γ.rev ((next hΓ ^ m) e)) = Γ.rev e := by
  induction m generalizing e with
  | zero => simp
  | succ m ih =>
    have h₁ (y : Γ.E) : (next hΓ ^ (m + 1)) y = (next hΓ ^ m) (next hΓ y) := by
      rw [pow_succ, Equiv.Perm.mul_apply]
    have h₂ : (next hΓ ^ (m + 1)) e = next hΓ ((next hΓ ^ m) e) := by
      rw [pow_succ', Equiv.Perm.mul_apply]
    rw [h₂, h₁, next_rev_next, ih]

-- A dart and its reverse never lie on the same cycle of `next`: compare `next ^ k e = rev e` with
-- `next ^ m (rev (next ^ m e)) = rev e` for `k = 2 * m` or `k = 2 * m + 1`.
private theorem not_sameCycle_rev [Finite Γ.E] (e : Γ.E) : ¬(next hΓ).SameCycle e (Γ.rev e) := by
  intro h
  obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' k
  · apply Γ.rev_ne ((next hΓ ^ m) e)
    apply (next hΓ ^ m).injective
    rw [pow_rev_pow, ← hk, two_mul, pow_add, Equiv.Perm.mul_apply]
  · apply other_ne hΓ (Γ.rev ((next hΓ ^ m) e))
    apply (next hΓ ^ m).injective
    rw [← next_apply, pow_rev_pow, ← hk, show 2 * m + 1 = m + 1 + m by omega, pow_add, pow_succ,
      Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]

private theorem sameCycle_other {e d : Γ.E}
    (hd : (next hΓ).SameCycle e d ∨ (next hΓ).SameCycle e (Γ.rev d)) :
    (next hΓ).SameCycle e (other hΓ d) ∨ (next hΓ).SameCycle e (Γ.rev (other hΓ d)) := by
  rcases hd with hd | hd
  · refine .inr (Equiv.Perm.sameCycle_apply_right.1 ?_)
    rwa [next_apply, rev_rev, other_other]
  · refine .inl ?_
    rwa [← rev_rev Γ d, ← next_apply, Equiv.Perm.sameCycle_apply_right]

-- Every dart starting at a vertex reachable from the source of `e` lies on the cycle of `e`, or its
-- reverse does.
private theorem sameCycle_of_path {e : Γ.E} {x : Γ.V} (p : Γ.Path (Γ.src e) x) {f : Γ.E}
    (hf : Γ.src f = x) : (next hΓ).SameCycle e f ∨ (next hΓ).SameCycle e (Γ.rev f) := by
  have key : ∀ d, ((next hΓ).SameCycle e d ∨ (next hΓ).SameCycle e (Γ.rev d)) → ∀ f,
      Γ.src f = Γ.src d → (next hΓ).SameCycle e f ∨ (next hΓ).SameCycle e (Γ.rev f) := by
    intro d hd f hf
    by_cases hfd : f = d
    · exact hfd ▸ hd
    · rw [eq_other_of_ne hΓ hf hfd]
      exact sameCycle_other hΓ hd
  let R : Set Γ.V := {x | ∀ f, Γ.src f = x →
    (next hΓ).SameCycle e f ∨ (next hΓ).SameCycle e (Γ.rev f)}
  have hR : ∀ d ∈ (Set.univ : Set Γ.E), Γ.src d ∈ R → Γ.tgt d ∈ R := by
    intro d _ hd f hf
    refine key (Γ.rev d) ?_ f (by rw [hf, src_rev])
    rw [rev_rev]
    exact (hd d rfl).symm
  have h₀ : Γ.src e ∈ R := key e (.inl (Equiv.Perm.SameCycle.refl _ e))
  exact (Path.mem_iff_mem_of_forall_mem_darts Γ (fun _ _ => trivial) hR p
    (fun _ _ => trivial)).1 h₀ f hf

private noncomputable def orbit (e : Γ.E) : List Γ.E :=
  (List.range (Function.minimalPeriod (next hΓ) e)).map fun k => (next hΓ)^[k] e

private theorem mem_orbit_iff [Finite Γ.E] {e d : Γ.E} :
    d ∈ orbit hΓ e ↔ (next hΓ).SameCycle e d := by
  rw [orbit, ← Cycle.mem_coe_iff, ← Function.periodicOrbit_def,
    Function.mem_periodicOrbit_iff ((next hΓ).injective.mem_periodicPts e)]
  refine ⟨fun ⟨k, hk⟩ => ⟨k, ?_⟩, fun h => ?_⟩
  · rw [← hk, zpow_natCast, Equiv.Perm.iterate_eq_pow]
  · obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
    exact ⟨k, by rw [Equiv.Perm.iterate_eq_pow, hk]⟩

private theorem nodup_orbit (e : Γ.E) : (orbit hΓ e).Nodup := by
  rw [orbit, ← Cycle.nodup_coe_iff, ← Function.periodicOrbit_def]
  exact Function.nodup_periodicOrbit

private theorem exists_path_darts_eq_orbit (e : Γ.E) :
    ∃ p : Γ.Path (Γ.src e) (Γ.src e), Path.darts Γ p = orbit hΓ e := by
  refine exists_path_darts_eq Γ _ ?_
  have h₁ : Γ.src e :: (orbit hΓ e).map Γ.tgt = (List.range
      (Function.minimalPeriod (next hΓ) e + 1)).map fun k => Γ.src ((next hΓ)^[k] e) := by
    simp [orbit, List.range_succ_eq_map, Function.iterate_succ_apply', src_next]
  have h₂ : (orbit hΓ e).map Γ.src ++ [Γ.src e] = (List.range
      (Function.minimalPeriod (next hΓ) e + 1)).map fun k => Γ.src ((next hΓ)^[k] e) := by
    simp [orbit, List.range_succ, Function.iterate_minimalPeriod]
  rw [h₁, h₂]

end TwoRegular

/-- In a finite Serre graph in which exactly two darts start at every vertex, the component of every
vertex `a` is traversed by a circuit: some closed path at `a` traverses every geometric edge of the
component exactly once, that is, the geometric edges of its darts are distinct and include every
geometric edge with an end reachable from `a`. -/
theorem exists_path_nodup_map_toGeomEdge_darts_and_mem [Finite Γ.E]
    (hΓ : ∀ x, Nat.card {e : Γ.E // Γ.src e = x} = 2) (a : Γ.V) :
    ∃ p : Γ.Path a a, ((Path.darts Γ p).map Γ.toGeomEdge).Nodup ∧
      ∀ e, Nonempty (Γ.Path a (Γ.src e)) → Γ.toGeomEdge e ∈ (Path.darts Γ p).map Γ.toGeomEdge := by
  obtain ⟨⟨e, rfl⟩⟩ : Nonempty {e : Γ.E // Γ.src e = a} :=
    (Nat.card_pos_iff.1 (by rw [hΓ]; omega)).1
  obtain ⟨p, hp⟩ := exists_path_darts_eq_orbit hΓ e
  refine ⟨p, hp ▸ (nodup_orbit hΓ e).map_on fun x hx y hy hxy => ?_, fun d ⟨q⟩ => hp ▸ ?_⟩
  · rcases Γ.toGeomEdge_eq_toGeomEdge_iff.1 hxy with h | h
    · exact h.symm
    · rw [mem_orbit_iff] at hx hy
      exact absurd (hx.symm.trans (h ▸ hy)) (not_sameCycle_rev hΓ x)
  · rcases sameCycle_of_path hΓ q rfl with h | h
    · exact List.mem_map_of_mem (mem_orbit_iff hΓ |>.2 h)
    · exact List.mem_map.2 ⟨Γ.rev d, mem_orbit_iff hΓ |>.2 h, toGeomEdge_rev Γ d⟩

end TauCeti.SerreGraph
