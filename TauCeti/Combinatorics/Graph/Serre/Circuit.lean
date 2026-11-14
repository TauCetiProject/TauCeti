/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Path.Basic
public import Mathlib.Data.Set.Card

import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.GroupTheory.Perm.Cycle.Basic
import TauCeti.Combinatorics.Enumerative.PerfectMatching

/-!
# Circuits through the components of 2-regular Serre graphs

A path of a Serre graph traverses each geometric edge at most once when the list of the geometric
edges of its darts has no duplicates. When at most two darts start at every vertex, a path of this
kind also leaves each vertex at most once, so a closed one visits each vertex at most once: entering
and leaving a vertex uses both darts starting there. A nonempty closed path at `a` traversing every
geometric edge with an end reachable from `a` visits exactly the vertices reachable from `a`.

In a finite Serre graph in which exactly two darts start at every vertex, the component of every
vertex `a` is traversed by a circuit: some closed path at `a` traverses every geometric edge of the
component exactly once. After a dart `e`, the path continues along the dart at the target of `e`
other than the reverse of `e`; this successor map is the product of two fixed-point-free
involutions of the darts, so none of its cycles contains a dart together with its reverse. This is
the graph-theoretic fact behind the contours of a polygonal surface: its boundary graph is finite
and 2-regular, so each of its components is a circle, traversed by a circuit.

## Main results

* `TauCeti.SerreGraph.Path.nodup_map_src_darts_of_nodup_map_toGeomEdge_darts`: when at most two
  darts start at every vertex, a path traversing each geometric edge at most once leaves each
  vertex at most once.
* `TauCeti.SerreGraph.Path.mem_map_src_darts_iff_nonempty_path`: a nonempty closed path at `a`
  traversing every geometric edge with an end reachable from `a` visits exactly the vertices
  reachable from `a`.
* `TauCeti.SerreGraph.exists_path_nodup_map_toGeomEdge_darts_and_mem`: in a finite 2-regular
  Serre graph, some closed path at any vertex traverses every geometric edge of its component
  exactly once.

## References

* J. Gallier, D. Xu, *A Guide to the Classification Theorem for Compact Surfaces*, Springer, 2013,
  §4.6, p. 51 and Chapter 6, p. 87 (contours, the components of the boundary). The existence of a
  circuit in a finite 2-regular graph is elementary and is not proved there.
-/

public section

namespace TauCeti.SerreGraph

variable {Γ : SerreGraph}

/-! ### Paths traversing each geometric edge at most once -/

/-- In a Serre graph in which at most two darts start at every vertex, a path traversing each
geometric edge at most once leaves each vertex at most once: the sources of its darts are
distinct. -/
theorem Path.nodup_map_src_darts_of_nodup_map_toGeomEdge_darts
    (hΓ : ∀ x, {e : Γ.E | Γ.src e = x}.encard ≤ 2) {a b : Γ.V} {p : Γ.Path a b}
    (hp : ((Path.darts Γ p).map Γ.toGeomEdge).Nodup) : ((Path.darts Γ p).map Γ.src).Nodup := by
  classical
  refine List.nodup_iff_count_le_one.2 fun x => ?_
  -- The darts of `p` starting at `x` and the reverses of the darts of `p` ending at `x` are
  -- distinct darts starting at `x`, and every dart of `p` starting at `x`, except possibly the
  -- first dart of `p`, follows a dart of `p` ending at `x`.
  set L := (Path.darts Γ p).filter (Γ.src · == x) ++
    ((Path.darts Γ p).filter (Γ.tgt · == x)).map Γ.rev
  have hL : L.Nodup := by
    refine List.nodup_append.2 ⟨hp.of_map.filter _, (hp.of_map.filter _).map Γ.rev_injective, ?_⟩
    simp only [List.mem_filter, List.mem_map]
    rintro d ⟨hd, -⟩ _ ⟨d', ⟨hd', -⟩, rfl⟩ rfl
    exact rev_notMem_of_nodup_map_toGeomEdge Γ hp hd' hd
  have hsub : (L.toFinset : Set Γ.E) ⊆ {e | Γ.src e = x} := by
    intro e he
    simp only [L, List.coe_toFinset, Set.mem_ofPred_eq, List.mem_append, List.mem_filter,
      List.mem_map, beq_iff_eq] at he
    rcases he with ⟨-, rfl⟩ | ⟨d, ⟨-, rfl⟩, rfl⟩
    · rfl
    · exact src_rev Γ d
  have hlen : (L.length : ℕ∞) ≤ 2 := by
    rw [← List.toFinset_card_of_nodup hL, ← Set.encard_coe_eq_coe_finsetCard]
    exact (Set.encard_le_encard hsub).trans (hΓ x)
  have hcount : L.length =
      ((Path.darts Γ p).map Γ.src).count x + ((Path.darts Γ p).map Γ.tgt).count x := by
    simp [L, List.count_eq_length_filter, List.filter_map, Function.comp_def]
  have hpath := congrArg (List.count x) (Path.cons_map_tgt_darts Γ p)
  rw [List.count_cons, List.count_append] at hpath
  have : L.length ≤ 2 := by exact_mod_cast hlen
  split_ifs at hpath <;> omega

/-- A nonempty closed path at `a` traversing every geometric edge with an end reachable from `a`
visits exactly the vertices reachable from `a`. -/
theorem Path.mem_map_src_darts_iff_nonempty_path {a : Γ.V} {p : Γ.Path a a}
    (hp₀ : Path.darts Γ p ≠ [])
    (hp : ∀ e, Nonempty (Γ.Path a (Γ.src e)) → Γ.toGeomEdge e ∈ (Path.darts Γ p).map Γ.toGeomEdge)
    {x : Γ.V} : x ∈ (Path.darts Γ p).map Γ.src ↔ Nonempty (Γ.Path a x) := by
  refine ⟨fun h => ?_, fun ⟨q⟩ => ?_⟩
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 h
    obtain ⟨q, -, -⟩ := Path.exists_eq_cons_comp_of_mem_darts Γ p hd
    exact ⟨q⟩
  cases q with
  | nil =>
    obtain ⟨d, l, hdl⟩ := List.exists_cons_of_ne_nil hp₀
    have hd : d ∈ (Path.darts Γ p).head? := by simp [hdl]
    exact List.mem_map.2 ⟨d, List.mem_of_mem_head? hd, Path.src_eq_of_mem_head?_darts Γ p hd⟩
  | cons q e =>
    obtain ⟨e, rfl, rfl⟩ := e
    have h := hp (Γ.rev e) ⟨by rw [src_rev]; exact q.cons (Γ.dart e)⟩
    rcases (toGeomEdge_mem_map_iff Γ).1 h with h | h
    · exact List.mem_map.2 ⟨_, h, src_rev Γ e⟩
    · rw [rev_rev] at h
      exact (Path.map_tgt_darts_perm Γ p).subset (List.mem_map_of_mem h)

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

-- `other` and `rev` are fixed-point-free involutions of the darts, and `next` is their product.
private noncomputable def otherMatching : PerfectMatching Γ.E :=
  PerfectMatching.ofInvolutive (show Function.Involutive (other hΓ) from other_other hΓ)
    (other_ne hΓ)

private noncomputable def next : Equiv.Perm Γ.E :=
  (otherMatching hΓ).val *
    (PerfectMatching.ofInvolutive (show Function.Involutive Γ.rev from Γ.rev_rev) Γ.rev_ne).val

private theorem next_apply (e : Γ.E) : next hΓ e = other hΓ (Γ.rev e) := by
  simp [next, otherMatching]

private theorem src_next (e : Γ.E) : Γ.src (next hΓ e) = Γ.tgt e := by
  rw [next_apply, src_other, src_rev]

-- A dart and its reverse never lie on the same cycle of `next`: no cycle of a product of two
-- perfect matchings is its own reverse.
private theorem not_sameCycle_rev (e : Γ.E) : ¬(next hΓ).SameCycle e (Γ.rev e) := by
  simpa [next] using (otherMatching hΓ).prop.not_sameCycle_self_apply
    (PerfectMatching.ofInvolutive (show Function.Involutive Γ.rev from Γ.rev_rev) Γ.rev_ne).prop e

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
    simp [orbit, List.range_succ_eq_map, Function.iterate_succ_apply', src_next,
      -List.range_map_iterate]
  have h₂ : (orbit hΓ e).map Γ.src ++ [Γ.src e] = (List.range
      (Function.minimalPeriod (next hΓ) e + 1)).map fun k => Γ.src ((next hΓ)^[k] e) := by
    simp [orbit, List.range_succ, Function.iterate_minimalPeriod, -List.range_map_iterate]
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
  · exact (toGeomEdge_mem_map_iff Γ).2 <|
      (sameCycle_of_path hΓ q rfl).imp (mem_orbit_iff hΓ).2 (mem_orbit_iff hΓ).2

end TauCeti.SerreGraph
