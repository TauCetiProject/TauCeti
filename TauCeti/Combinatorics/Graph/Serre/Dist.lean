/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Tree
public import TauCeti.Combinatorics.Quiver.Symmetric
public import Mathlib.Order.Lattice.Nat

/-!
# The path distance of a Serre graph

The distance between two vertices of a Serre graph is the least length of a path joining them,
and `0` when there is no such path, following Mathlib's `SimpleGraph.dist`. Between joined
vertices it vanishes exactly on the diagonal, is symmetric, and satisfies the triangle
inequality. Graph morphisms do not increase it.

In an acyclic graph the unique reduced path between two vertices realizes their distance, since
free reduction never lengthens a path.

## References

* J.-P. Serre, *Trees*, Chapter I, §2.2.
-/

public section

namespace TauCeti
namespace SerreGraph

variable (Γ : SerreGraph)

/-- The distance between two vertices of a Serre graph: the least length of a path from the
first to the second, or `0` when there is none. -/
noncomputable def dist (a b : Γ.V) : ℕ :=
  sInf (Set.range (Quiver.Path.length : Γ.Path a b → ℕ))

variable {Γ}

/-- Every path is at least as long as the distance between its endpoints. -/
theorem dist_le_length {a b : Γ.V} (p : Γ.Path a b) : Γ.dist a b ≤ p.length :=
  Nat.sInf_le ⟨p, rfl⟩

/-- Joined vertices are joined by a path whose length is their distance. -/
theorem exists_length_eq_dist {a b : Γ.V} (h : Nonempty (Γ.Path a b)) :
    ∃ p : Γ.Path a b, p.length = Γ.dist a b :=
  Nat.sInf_mem (Set.range_nonempty_iff_nonempty.mpr h)

/-- Vertices joined by no path are at distance zero. -/
theorem dist_of_isEmpty {a b : Γ.V} (h : IsEmpty (Γ.Path a b)) : Γ.dist a b = 0 := by
  rw [dist, Set.range_eq_empty_iff.mpr h, Nat.sInf_empty]

@[simp] theorem dist_self (a : Γ.V) : Γ.dist a a = 0 :=
  Nat.le_zero.mp (dist_le_length (Quiver.Path.nil : Γ.Path a a))

/-- Joined vertices are at distance zero exactly when they are equal. -/
theorem dist_eq_zero_iff {a b : Γ.V} (h : Nonempty (Γ.Path a b)) : Γ.dist a b = 0 ↔ a = b := by
  refine ⟨fun hd => ?_, fun hab => hab ▸ dist_self a⟩
  obtain ⟨p, hp⟩ := exists_length_eq_dist h
  exact p.eq_of_length_zero (hp.trans hd)

theorem dist_comm (a b : Γ.V) : Γ.dist a b = Γ.dist b a := by
  -- Reversal is a length-preserving bijection between the paths in the two directions.
  suffices h : ∀ a b : Γ.V, Γ.dist b a ≤ Γ.dist a b from (h b a).antisymm (h a b)
  intro a b
  rcases isEmpty_or_nonempty (Γ.Path a b) with hab | hab
  · have hba : IsEmpty (Γ.Path b a) := ⟨fun p => hab.false p.reverse⟩
    rw [dist_of_isEmpty hab, dist_of_isEmpty hba]
  · obtain ⟨p, hp⟩ := exists_length_eq_dist hab
    calc Γ.dist b a ≤ p.reverse.length := dist_le_length p.reverse
      _ = Γ.dist a b := by rw [Quiver.Path.length_reverse, hp]

/-- The triangle inequality, for vertices joined in sequence. -/
theorem dist_triangle {a b c : Γ.V} (hab : Nonempty (Γ.Path a b))
    (hbc : Nonempty (Γ.Path b c)) : Γ.dist a c ≤ Γ.dist a b + Γ.dist b c := by
  obtain ⟨p, hp⟩ := exists_length_eq_dist hab
  obtain ⟨q, hq⟩ := exists_length_eq_dist hbc
  rw [← hp, ← hq, ← Quiver.Path.length_comp]
  exact dist_le_length (p.comp q)

/-- A dart joins vertices at distance at most one. -/
theorem dist_src_tgt_le_one (e : Γ.E) : Γ.dist (Γ.src e) (Γ.tgt e) ≤ 1 :=
  dist_le_length (Γ.dart e).toPath

/-- A morphism maps a path to a path of the same length. -/
@[simp] theorem Hom.length_mapPath {Δ : SerreGraph} (f : Γ.Hom Δ) {a b : Γ.V}
    (p : Γ.Path a b) : (f.toPrefunctor.mapPath p).length = p.length := by
  rw [← Path.length_darts, ← Path.length_darts, Hom.darts_mapPath, List.length_map]

/-- A graph morphism does not increase the distance between joined vertices. -/
theorem Hom.dist_le {Δ : SerreGraph} (f : Γ.Hom Δ) {a b : Γ.V} (h : Nonempty (Γ.Path a b)) :
    Δ.dist (f.mapV a) (f.mapV b) ≤ Γ.dist a b := by
  obtain ⟨p, hp⟩ := exists_length_eq_dist h
  calc Δ.dist (f.mapV a) (f.mapV b) ≤ (f.toPrefunctor.mapPath p).length :=
        dist_le_length (f.toPrefunctor.mapPath p)
    _ = Γ.dist a b := by rw [f.length_mapPath, hp]

/-! ### Distances in acyclic graphs -/

/-- Free reduction never lengthens a path. -/
theorem Path.length_reduce_le {a b : Γ.V} (p : Γ.Path a b) :
    (Path.reduce Γ p).length ≤ p.length := by
  induction p with
  | nil => simp
  | @cons b c p e ih =>
    by_cases h : Path.IsReduced Γ ((Path.reduce Γ p).cons e)
    · rw [Path.reduce_cons_of_isReduced Γ p e h, Quiver.Path.length_cons,
        Quiver.Path.length_cons]
      omega
    · -- The appended dart backtracks against the last dart of the reduced prefix.
      generalize hq : Path.reduce Γ p = q at h ih
      cases q with
      | nil => exact absurd (Path.isReduced_toPath Γ e) h
      | @cons d _ q f =>
        have hfe : e.1 = Γ.rev f.1 := by
          by_contra hne
          exact h ((Path.isReduced_cons_cons Γ q f e).mpr
            ⟨hq ▸ Path.isReduced_reduce Γ p, hne⟩)
        obtain rfl : c = d := by rw [← e.2.2, hfe, tgt_rev, f.2.1]
        obtain rfl : e = Quiver.reverse f := Subtype.ext (by simpa using hfe)
        rw [Path.reduce_cons_of_reduce_eq_cons_reverse Γ p q _ (by
          rw [hq, Quiver.reverse_reverse]), Quiver.Path.length_cons]
        rw [Quiver.Path.length_cons] at ih
        omega

/-- In an acyclic graph, a reduced path realizes the distance between its endpoints. -/
theorem IsAcyclic.dist_eq_length (h : Γ.IsAcyclic) {a b : Γ.V} {p : Γ.Path a b}
    (hp : Path.IsReduced Γ p) : Γ.dist a b = p.length := by
  refine (dist_le_length p).antisymm ?_
  obtain ⟨q, hq⟩ := exists_length_eq_dist ⟨p⟩
  rw [← hq, h.eq_of_isReduced hp (Path.isReduced_reduce Γ q)]
  exact Path.length_reduce_le q

end SerreGraph
end TauCeti
