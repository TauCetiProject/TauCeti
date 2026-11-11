/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Convex
public import TauCeti.Combinatorics.Graph.Serre.Dist

/-!
# Geodesic lines in Serre graphs

A geodesic line in a Serre graph is a family of vertices `c : ℤ → Γ.V` that is isometric for the
path distance: `d(c m, c n) = |m - n|`. Consecutive vertices of a geodesic line are joined by a
dart, and the resulting paths along the line are shortest paths, hence reduced. In an acyclic
graph they are the only reduced paths between vertices of the line, so the vertices of a geodesic
line form a convex set: a geodesic line is a subtree. A geodesic line contained in another one
has the same vertices, because an isometric self-map of the integers is surjective.

These are the lines that occur as axes of hyperbolic automorphisms of trees.

## References

* J.-P. Serre, *Trees*, Chapter I, §2.2 and §6.4.
-/

public section

namespace TauCeti
namespace SerreGraph

variable {Γ : SerreGraph}

/-- In a preconnected graph, a family of vertices indexed by the integers whose consecutive
members are at distance at most one does not increase distances. -/
theorem Preconnected.dist_le_natAbs (h : Γ.Preconnected) {c : ℤ → Γ.V}
    (hc : ∀ n, Γ.dist (c n) (c (n + 1)) ≤ 1) (m n : ℤ) : Γ.dist (c m) (c n) ≤ (m - n).natAbs := by
  have key : ∀ (m : ℤ) (k : ℕ), Γ.dist (c m) (c (m + k)) ≤ k := by
    intro m k
    induction k with
    | zero => simp
    | succ k ih =>
      have htri := dist_triangle ((preconnected_iff Γ).mp h (c m) (c (m + k)))
        ((preconnected_iff Γ).mp h (c (m + k)) (c (m + k + 1)))
      have := hc (m + k)
      rw [Int.natCast_add, Int.natCast_one, ← Int.add_assoc]
      omega
  rcases le_total m n with hmn | hmn
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = m + k := ⟨(n - m).toNat, by omega⟩
    exact (key m k).trans (by omega)
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = n + k := ⟨(m - n).toNat, by omega⟩
    rw [dist_comm]
    exact (key n k).trans (by omega)

/-- Two vertices of a geodesic line are joined by a path along the line whose length is their
distance. -/
theorem exists_path_length_eq_of_dist_eq_natAbs {c : ℤ → Γ.V}
    (hc : ∀ m n, Γ.dist (c m) (c n) = (m - n).natAbs) (m : ℤ) (k : ℕ) :
    ∃ p : Γ.Path (c m) (c (m + k)), p.length = k ∧
      ∀ e ∈ Path.darts Γ p, Γ.src e ∈ Set.range c ∧ Γ.tgt e ∈ Set.range c := by
  induction k with
  | zero =>
    exact ⟨(Quiver.Path.nil : Γ.Path (c m) (c m)).cast rfl (by simp),
      by rw [← Path.length_darts, Path.darts_cast, Path.darts_nil, List.length_nil],
      by simp⟩
  | succ k ih =>
    obtain ⟨p, hp, hpc⟩ := ih
    obtain ⟨e, hs, ht⟩ := exists_src_eq_and_tgt_eq_of_dist_eq_one
      (a := c (m + k)) (b := c (m + (k + 1 : ℕ))) (by rw [hc]; omega)
    refine ⟨p.cons ⟨e, hs, ht⟩, by rw [Quiver.Path.length_cons, hp], fun f hf => ?_⟩
    rw [Path.darts_cons, List.mem_append, List.mem_singleton] at hf
    rcases hf with hf | rfl
    · exact hpc f hf
    · exact ⟨hs ▸ Set.mem_range_self _, ht ▸ Set.mem_range_self _⟩

/-- In an acyclic graph, the vertices of a geodesic line form a convex set. -/
theorem IsAcyclic.isConvex_range_of_dist_eq_natAbs (h : Γ.IsAcyclic) {c : ℤ → Γ.V}
    (hc : ∀ m n, Γ.dist (c m) (c n) = (m - n).natAbs) : Γ.IsConvex (Set.range c) := by
  -- A reduced path between two vertices of the line is the shortest path along the line.
  have key : ∀ m n : ℤ, m ≤ n → ∀ p : Γ.Path (c m) (c n), Path.IsReduced Γ p →
      ∀ e ∈ Path.darts Γ p, Γ.src e ∈ Set.range c ∧ Γ.tgt e ∈ Set.range c := by
    intro m n hmn p hp
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = m + k := ⟨(n - m).toNat, by omega⟩
    obtain ⟨q, hq, hqc⟩ := exists_path_length_eq_of_dist_eq_natAbs hc m k
    rw [h.eq_of_isReduced hp (Path.isReduced_of_length_le_dist (by rw [hq, hc]; omega))]
    exact hqc
  refine isConvex_iff.mpr ?_
  rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩ p hp e he
  rcases le_total m n with hmn | hmn
  · exact (key m n hmn p hp e he).1
  · have he' : Γ.rev e ∈ Path.darts Γ p.reverse := by
      rw [Path.darts_reverse]
      exact List.mem_map.mpr ⟨e, List.mem_reverse.mpr he, rfl⟩
    simpa only [tgt_rev] using
      (key n m hmn p.reverse ((Path.isReduced_reverse Γ p).mpr hp) (Γ.rev e) he').2

/-- A geodesic line contained in another geodesic line has the same vertices. -/
theorem range_eq_of_range_subset_of_dist_eq_natAbs {c c' : ℤ → Γ.V}
    (hc : ∀ m n, Γ.dist (c m) (c n) = (m - n).natAbs)
    (hc' : ∀ m n, Γ.dist (c' m) (c' n) = (m - n).natAbs)
    (h : Set.range c ⊆ Set.range c') : Set.range c = Set.range c' := by
  choose φ hφ using fun n => h (Set.mem_range_self n)
  -- The reparametrization `φ` is an isometry of the integers, so a translation or a reflection.
  have hiso : ∀ m n, (φ m - φ n).natAbs = (m - n).natAbs := fun m n => by
    rw [← hc', hφ, hφ, hc]
  refine h.antisymm ?_
  rintro _ ⟨k, rfl⟩
  have h₁₀ := hiso 1 0
  obtain h₁ | h₁ : φ 1 - φ 0 = 1 ∨ φ 1 - φ 0 = -1 := by omega
  · have h₀ := hiso (k - φ 0) 0
    have h₂ := hiso (k - φ 0) 1
    exact ⟨k - φ 0, by rw [← hφ]; congr 1; omega⟩
  · have h₀ := hiso (φ 0 - k) 0
    have h₂ := hiso (φ 0 - k) 1
    exact ⟨φ 0 - k, by rw [← hφ]; congr 1; omega⟩

end SerreGraph
end TauCeti
