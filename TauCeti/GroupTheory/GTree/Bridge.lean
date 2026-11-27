/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GTree.Axis

/-!
# Products of tree automorphisms with disjoint characteristic sets

Let `G` act on a tree without inversions, and let `A(g)` be the characteristic set of `g ∈ G`: its
set of fixed vertices if `g` is elliptic, its axis if `g` is hyperbolic. If `A(g)` and `A(h)` are
disjoint, then `g * h` is hyperbolic; for two elliptic elements this is Serre's lemma
`TauCeti.GTree.exists_smul_eq_and_smul_eq_of_isElliptic_mul`. For any `g` and `h`, the segment
between a vertex of `A(g)` and a vertex of `A(h)` lies in `A(g) ∪ A(g * h) ∪ A(h)`. This is the
key step in showing that the union of the axes of the hyperbolic elements of a subgroup is convex.

The argument goes through the *bridge* between disjoint sets `A(g)` and `A(h)`: the reduced path
`[a₀, b₀]` meeting `A(g)` only at `a₀` and `A(h)` only at `b₀`. The bridge, reversed, followed by
a reduced path from `a₀` to `g • a₀` and by the translate of the bridge under `g` does not
backtrack, and neither does the bridge followed by a reduced path from `b₀` to `h • b₀` and by
the reversed translate of the bridge under `h`. Gluing these two paths along the translate of the
bridge under `g` gives a reduced path from `b₀` to `(g * h) • b₀` that is followed by its
translate under `g * h` without backtracking. Hence `g * h` is hyperbolic and `b₀` lies on its
axis; the same argument for `h⁻¹` and `g⁻¹` gives `a₀`, so the bridge lies on the axis of `g * h`.

## Main results

* `TauCeti.GTree.isHyperbolic_mul_of_disjoint_axis`: the product of two elements with disjoint
  characteristic sets is hyperbolic.
* `TauCeti.GTree.convexHull_pair_subset_axis_union`: the segment between vertices of the
  characteristic sets of `g` and `h` lies in the union of the characteristic sets of `g`, `g * h`
  and `h`.

## References

* V. Guirardel, G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017), §1.1 and
  Appendix, Lemma A.1, after F. Paulin, *The Gromov topology on R-trees*, Topology Appl. 32
  (1989).
* J.-P. Serre, *Trees*, Chapter I, §6.5, Proposition 26.
-/

public section

universe u v w

namespace TauCeti
namespace GTree

open SerreGraph

variable {G : Type w} [Group G] {T : GTree.{u, v} G}

/-! ### Reduced paths through a characteristic set -/

/-- Translating a sequence of darts creates no backtracking and removes none. -/
private theorem isChain_map_smul (g : G) {l : List T.E} :
    (l.map (g • ·)).IsChain (fun e f => f ≠ T.rev e) ↔ l.IsChain fun e f => f ≠ T.rev e := by
  simp [List.isChain_map]

/-- The reverse of a path whose darts end outside `A` and start outside `B` has darts ending
outside `B` and starting outside `A`. -/
private theorem forall_mem_darts_reverse {A B : Set T.V} {a b : T.V} {p : T.Path a b}
    (hp : ∀ e ∈ Path.darts T.toSerreGraph p, T.tgt e ∉ A ∧ T.src e ∉ B) :
    ∀ e ∈ Path.darts T.toSerreGraph p.reverse, T.tgt e ∉ B ∧ T.src e ∉ A := by
  simp only [Path.darts_reverse, List.mem_map, List.mem_reverse]
  rintro _ ⟨e, he, rfl⟩
  simpa using (hp e he).symm

/-- Let `c` be a vertex of the characteristic set of `g` and `s` a reduced path ending at `c`
whose last dart starts outside that set. Then `s`, followed by a reduced path from `c` to `g • c`
and by the translate under `g` of the reverse of `s`, has no backtracking. -/
private theorem isChain_darts_of_mem_axis {g : G} {x c : T.V} (hc : c ∈ T.axis g) {s : T.Path x c}
    (hs : Path.IsReduced T.toSerreGraph s)
    (hsc : ∀ d ∈ (Path.darts T.toSerreGraph s).getLast?, T.src d ∉ T.axis g) {r : T.Path c (g • c)}
    (hr : Path.IsReduced T.toSerreGraph r) :
    (Path.darts T.toSerreGraph s ++ Path.darts T.toSerreGraph r ++
      (Path.darts T.toSerreGraph s.reverse).map (g • ·)).IsChain fun e f => f ≠ T.rev e := by
  have hgc : g • c ∈ T.axis g := smul_mem_axis_iff.mpr hc
  have hsr := (T.isConvex_axis g).isReduced_comp hc hgc hs hsc hr
  rw [Path.isReduced_iff_isChain, Path.darts_comp] at hsr
  refine hsr.append ((isChain_map_smul g).mpr ((Path.isReduced_iff_isChain _ _).mp
    ((Path.isReduced_reverse _ s).mpr hs))) fun e he f hf hfe => ?_
  -- The translate starts with `g • rev d`, which ends at `g • src d`, for `d` the last dart of `s`.
  simp only [Path.darts_reverse, List.head?_map, List.head?_reverse, Option.map_map,
    Option.mem_def, Option.map_eq_some_iff, Function.comp_apply] at hf
  obtain ⟨d, hd, rfl⟩ := hf
  have htgt : g • T.src d = T.src e := by simpa using congrArg T.tgt hfe
  refine hsc d hd ?_
  rcases eq_or_ne (Path.darts T.toSerreGraph r) [] with hnil | hne
  · -- Then `e = d`, so `g` fixes `src d`, which therefore lies in the characteristic set of `g`.
    rw [hnil, List.append_nil, hd] at he
    obtain rfl : d = e := Option.some.inj he
    exact mem_axis_of_smul_eq htgt
  · -- The last dart `e` of `r` starts in the characteristic set of `g`.
    rw [List.getLast?_append_of_ne_nil _ hne] at he
    rw [← smul_mem_axis_iff (g := g), htgt]
    exact isConvex_iff.mp (T.isConvex_axis g) c hc _ hgc r hr e (List.mem_of_mem_getLast? he)

/-! ### The bridge between two characteristic sets -/

section Bridge

variable {g h : G} {a b : T.V} {p : T.Path a b}

/-- Let `p` be a nonempty reduced path from `a ∈ A(g)` to `b ∈ A(h)`, meeting `A(g)` only at `a`
and `A(h)` only at `b`, and let `α : a → g • a` and `β : b → h • b` be reduced. Then the darts of
`p⁻¹`, `α`, `g • p`, `g • β` and `(g * h) • p⁻¹`, in this order, show no backtracking. -/
private theorem isChain_darts_bridge (ha : a ∈ T.axis g) (hb : b ∈ T.axis h)
    (hne : Path.darts T.toSerreGraph p ≠ []) (hp : Path.IsReduced T.toSerreGraph p)
    (hpab : ∀ e ∈ Path.darts T.toSerreGraph p, T.tgt e ∉ T.axis g ∧ T.src e ∉ T.axis h)
    {α : T.Path a (g • a)} (hα : Path.IsReduced T.toSerreGraph α) {β : T.Path b (h • b)}
    (hβ : Path.IsReduced T.toSerreGraph β) :
    (Path.darts T.toSerreGraph p.reverse ++ Path.darts T.toSerreGraph α ++
      (Path.darts T.toSerreGraph p).map (g • ·) ++ ((Path.darts T.toSerreGraph β).map (g • ·) ++
        (Path.darts T.toSerreGraph p.reverse).map ((g * h) • ·))).IsChain
      fun e f => f ≠ T.rev e := by
  -- No backtracking at `A(g)` in `p⁻¹ α (g • p)`, nor at `A(h)` in `p β (h • p⁻¹)`.
  have h₁ := isChain_darts_of_mem_axis ha ((Path.isReduced_reverse _ p).mpr hp)
    (fun d hd => (forall_mem_darts_reverse hpab d (List.mem_of_mem_getLast? hd)).2) hα
  have h₂ := (isChain_map_smul g).mpr <| isChain_darts_of_mem_axis hb hp
    (fun e he => (hpab e (List.mem_of_mem_getLast? he)).2) hβ
  rw [Quiver.Path.reverse_reverse] at h₁
  simp only [List.map_append, List.map_map, Function.comp_def, ← mul_smul,
    List.append_assoc] at h₂
  -- The two chains overlap in the darts of `g • p`, which is not empty.
  exact h₁.append_overlap h₂ (by simpa using hne)

/-- Let `p` be a reduced path from `a ∈ A(g)` to `b ∈ A(h)`, `a ≠ b`, meeting `A(g)` only at `a`
and `A(h)` only at `b`. Then a reduced path from `b` to `(g * h) • b`, starting with the reverse
of `p`, is followed by its translate under `g * h` without backtracking. -/
private theorem exists_isReduced_path_mul_smul (ha : a ∈ T.axis g) (hb : b ∈ T.axis h) (hab : a ≠ b)
    (hp : Path.IsReduced T.toSerreGraph p)
    (hpab : ∀ e ∈ Path.darts T.toSerreGraph p, T.tgt e ∉ T.axis g ∧ T.src e ∉ T.axis h) :
    ∃ q : T.Path b ((g * h) • b), Path.IsReduced T.toSerreGraph q ∧
      Path.darts T.toSerreGraph q ≠ [] ∧ ∀ e ∈ (Path.darts T.toSerreGraph q).getLast?,
        ∀ f ∈ (Path.darts T.toSerreGraph q).head?, (g * h) • f ≠ T.rev e := by
  obtain ⟨α, hα, -⟩ := T.isTree.existsUnique_isReduced a (g • a)
  obtain ⟨β, hβ, -⟩ := T.isTree.existsUnique_isReduced b (h • b)
  have hne : Path.darts T.toSerreGraph p ≠ [] := fun h0 => hab (Path.eq_of_darts_eq_nil _ p h0)
  have hc := isChain_darts_bridge ha hb hne hp hpab hα hβ
  -- The path `q = p⁻¹ α (g • p) (g • β)`, followed by the first darts of its translate.
  let q := ((p.reverse.comp α).comp (smulPath g p)).comp
    ((smulPath g β).cast rfl (mul_smul g h b).symm)
  have hq : Path.darts T.toSerreGraph q = Path.darts T.toSerreGraph p.reverse ++
      Path.darts T.toSerreGraph α ++ (Path.darts T.toSerreGraph p).map (g • ·) ++
        (Path.darts T.toSerreGraph β).map (g • ·) := by
    simp [q]
  rw [← List.append_assoc, ← hq, List.isChain_append] at hc
  have hrev : Path.darts T.toSerreGraph p.reverse ≠ [] := by simpa using hne
  refine ⟨q, (Path.isReduced_iff_isChain _ _).mpr hc.1, by simp [hq, hne],
    fun e he f hf => hc.2.2 e he _ ?_⟩
  rw [hq, List.append_assoc, List.append_assoc, List.head?_append_of_ne_nil _ hrev] at hf
  rw [List.head?_map]
  exact Option.mem_map_of_mem _ hf

/-- The end of a reduced path from `A(g)` to `A(h)`, meeting `A(g)` only at its start and `A(h)`
only at its end, lies in the characteristic set of `g * h`. -/
private theorem mem_axis_mul_of_isReduced (ha : a ∈ T.axis g) (hb : b ∈ T.axis h) (hab : a ≠ b)
    (hp : Path.IsReduced T.toSerreGraph p)
    (hpab : ∀ e ∈ Path.darts T.toSerreGraph p, T.tgt e ∉ T.axis g ∧ T.src e ∉ T.axis h) :
    b ∈ T.axis (g * h) :=
  let ⟨_, hq, _, hqgh⟩ := exists_isReduced_path_mul_smul ha hb hab hp hpab
  mem_axis_of_isReduced hq hqgh

/-- The bridge between the characteristic sets of `g` and `h` lies in the characteristic set of
`g * h`. -/
private theorem convexHull_pair_subset_axis_mul (ha : a ∈ T.axis g) (hb : b ∈ T.axis h)
    (hab : a ≠ b) (hp : Path.IsReduced T.toSerreGraph p)
    (hpab : ∀ e ∈ Path.darts T.toSerreGraph p, T.tgt e ∉ T.axis g ∧ T.src e ∉ T.axis h) :
    T.convexHull {a, b} ⊆ T.axis (g * h) := by
  refine (T.isConvex_axis _).convexHull_subset
    (Set.pair_subset ?_ (mem_axis_mul_of_isReduced ha hb hab hp hpab))
  -- The start of the bridge is the end of the reversed bridge, from `A(h⁻¹)` to `A(g⁻¹)`.
  rw [← axis_inv, mul_inv_rev]
  refine mem_axis_mul_of_isReduced (by rwa [axis_inv]) (by rwa [axis_inv]) hab.symm
    ((Path.isReduced_reverse _ p).mpr hp) ?_
  simpa only [axis_inv] using forall_mem_darts_reverse hpab

end Bridge

/-! ### Products and segments -/

/-- The product of two elements with disjoint characteristic sets is hyperbolic. For elliptic
elements the characteristic sets are the sets of fixed vertices
(`GTree.IsElliptic.axis_eq_fixedBy`), so this says that the product of two elliptic elements
without a common fixed vertex is hyperbolic (Serre's lemma,
`GTree.exists_smul_eq_and_smul_eq_of_isElliptic_mul`). -/
theorem isHyperbolic_mul_of_disjoint_axis {g h : G} (hd : Disjoint (T.axis g) (T.axis h)) :
    T.IsHyperbolic (g * h) := by
  obtain ⟨a, ha, b, hb, p, hp, hpab⟩ := ((connected_iff _).mp
    T.isTree.connected).2.exists_isReduced_path (T.axis_nonempty g) (T.axis_nonempty h)
  obtain ⟨q, hq, hqne, hqgh⟩ := exists_isReduced_path_mul_smul ha hb
    (fun hab => Set.disjoint_left.mp hd ha (hab ▸ hb)) hp hpab
  -- The reduced path `q` is not closed, so `g * h` moves `b`.
  refine isHyperbolic_of_isReduced (fun hgh => hqne ?_) hq hqgh
  have h0 : T.dist b ((g * h) • b) = 0 := by rw [hgh, dist_self]
  rwa [T.isTree.isAcyclic.dist_eq_length hq, ← Path.length_darts, List.length_eq_zero_iff] at h0

/-- The segment between points of the characteristic sets of two elements `g` and `h` lies in the
union of the characteristic sets of `g`, of `g * h` and of `h`. Since `g * h` lies in every
subgroup containing `g` and `h`, this makes the union of the axes of the hyperbolic elements of a
subgroup convex. -/
theorem convexHull_pair_subset_axis_union {g h : G} {a b : T.V} (ha : a ∈ T.axis g)
    (hb : b ∈ T.axis h) : T.convexHull {a, b} ⊆ T.axis g ∪ T.axis (g * h) ∪ T.axis h := by
  obtain ⟨a₀, ha₀, b₀, hb₀, p, hp, hpab⟩ := ((connected_iff _).mp
    T.isTree.connected).2.exists_isReduced_path (T.axis_nonempty g) (T.axis_nonempty h)
  -- The segment `[a, b]` lies in the convex set `A(g) ∪ [a₀, b₀] ∪ A(h)`.
  have hC := T.isTree.isConvex_union (T.isTree.isConvex_union (T.isConvex_axis g)
    (isConvex_convexHull _) ⟨a₀, ha₀, left_mem_convexHull_pair a₀ b₀⟩) (T.isConvex_axis h)
      ⟨b₀, Or.inr (right_mem_convexHull_pair a₀ b₀), hb₀⟩
  refine (hC.convexHull_subset (Set.pair_subset (Or.inl (Or.inl ha)) (Or.inr hb))).trans
    (Set.union_subset_union_left _ (Set.union_subset Set.subset_union_left ?_))
  -- The bridge `[a₀, b₀]` is a single vertex of `A(g)`, or lies in `A(g * h)`.
  obtain rfl | hab := eq_or_ne a₀ b₀
  · exact ((T.isConvex_axis g).convexHull_subset (Set.pair_subset ha₀ ha₀)).trans
      Set.subset_union_left
  · exact (convexHull_pair_subset_axis_mul ha₀ hb₀ hab hp hpab).trans Set.subset_union_right

end GTree
end TauCeti
