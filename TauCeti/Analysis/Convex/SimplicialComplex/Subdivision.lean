/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Analysis.Convex.SimplicialComplex.Glue
import TauCeti.Analysis.Convex.Intrinsic
import TauCeti.Analysis.Convex.SimplicialComplex.Cone

/-!
# Simplicial subdivision of a family of compact convex cells

Let `(P i)` be a locally finite family of nonempty compact convex sets (*cells*) in a
finite-dimensional real normed space, with pairwise disjoint intrinsic interiors, such that the
intrinsic frontier of each cell is covered by the other cells contained in it. For instance, the
cells may be compact convex polytopes, each proper face of which is a finite union of
lower-dimensional cells of the family. Such a family has a simplicial subdivision: a geometric
simplicial complex `K` with `|K| = ⋃ i, P i` in which every cell is triangulated by finitely many
simplices of `K` and every simplex of `K` lies in a cell
(`Geometry.SimplicialComplex.exists_subdivision`). The complex is locally finite, by the
criterion `Geometry.SimplicialComplex.locallyFinite_convexHull_of_finite_restrict`.

The construction retains a prescribed triangulation `L` of part of the frontiers of the cells
(`Geometry.SimplicialComplex.exists_subdivision_extending`): it suffices that `L` meets every cell
in a finite subcomplex, avoids the intrinsic interiors of the cells, and covers whatever part of
the frontier of a cell the smaller cells do not. The resulting `K` contains `L` and adds no
simplex with all its vertices in `|L|`.

The proof is by induction on the dimension of the cells. A cell contained in the frontier of
another one has strictly smaller dimension
(`TauCeti.finrank_vectorSpan_lt_of_disjoint_intrinsicInterior`).
Once the cells of dimension `< n` are triangulated, the frontier of each `n`-dimensional cell is a
subcomplex, and each such cell is triangulated by coning its frontier to a point of its intrinsic
interior. These cones are glued to the complex built so far
(`Geometry.SimplicialComplex.exists_extension_of_intrinsicFrontier_subset_space`); two distinct
`n`-dimensional cells meet only inside `|L|` and smaller cells, so the cones meet properly.

The hypotheses imply that two cells meet in a union of points of `|L|` and of cells contained in
both of them (`TauCeti.mem_intrinsicInterior_or_of_mem`); for two distinct cells of the same
dimension these common cells are smaller. So this need not be assumed.

## Main results

* `Geometry.SimplicialComplex.exists_extension_of_intrinsicFrontier_subset_space`: a complex `L`
  extends over a family of compact convex cells attached to `L` along subcomplexes covering their
  intrinsic frontiers.
* `Geometry.SimplicialComplex.exists_subdivision_extending`: the relative subdivision of a family
  of compact convex cells, extending a prescribed triangulation `L`.
* `Geometry.SimplicialComplex.exists_subdivision`: a locally finite simplicial subdivision of a
  locally finite family of compact convex cells.

## References

* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Ann. Scuola Norm. Sup. Pisa (3) 18
  (1964), 449–474 (the simplicial subdivision of the rectilinear cells in the proof of the
  triangulation theorem).
* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 2 (cell complexes and their simplicial subdivisions).
-/

public section

open Finset Set

namespace Geometry.SimplicialComplex

variable {E ι J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Attaching compact convex cells to a simplicial complex.** Let `C j` be nonempty compact
convex sets whose intrinsic interiors avoid `|L|`, each meeting `L` in a subcomplex covering its
intrinsic frontier, and any two of which meet only inside `|L|`. Then `L` extends to a complex
`K` with `|K| = |L| ∪ ⋃ j, C j`. Every simplex of `K` is a simplex of `L` or lies in a single
`C j`; each `C j` is
triangulated by the simplices of `K` it contains, finitely many when `L` has finitely many
simplices in `C j`; and `K` has the same simplices as `L` with all their vertices in any set
avoiding the intrinsic interiors of the cells. -/
theorem exists_extension_of_intrinsicFrontier_subset_space (L : SimplicialComplex ℝ E)
    (C : J → Set E) (hCc : ∀ j, IsCompact (C j)) (hCv : ∀ j, Convex ℝ (C j))
    (hCne : ∀ j, (C j).Nonempty)
    (hfr : ∀ j, intrinsicFrontier ℝ (C j) ⊆ (L.restrict (C j)).space)
    (hint : ∀ j, Disjoint (intrinsicInterior ℝ (C j)) L.space)
    (hCC : Pairwise fun j k => C j ∩ C k ⊆ L.space) :
    ∃ K : SimplicialComplex ℝ E, K.space = L.space ∪ ⋃ j, C j ∧
      (∀ B : Set E, (∀ j, Disjoint (intrinsicInterior ℝ (C j)) B) →
        K.restrict B = L.restrict B) ∧
      (∀ j, (K.restrict (C j)).space = C j ∧
        ((L.restrict (C j)).faces.Finite → (K.restrict (C j)).faces.Finite)) ∧
      ∀ s ∈ K.faces, s ∈ L.faces ∨ ∃ j, (s : Set E) ⊆ C j := by
  classical
  choose p hp using fun j => (hCne j).intrinsicInterior (hCv j)
  have hpC : ∀ j, p j ∈ C j := fun j => intrinsicInterior_subset (hp j)
  -- a point of `C j` in `|L|` lies in the intrinsic frontier of `C j`
  have hCL : ∀ j, C j ∩ L.space ⊆ intrinsicFrontier ℝ (C j) := fun j x ⟨hxC, hxL⟩ => by
    rw [← intrinsicClosure_sdiff_intrinsicInterior]
    exact ⟨subset_intrinsicClosure hxC, fun hxi => Set.disjoint_left.1 (hint j) hxi hxL⟩
  have hM : ∀ j, (L.restrict (C j)).space = intrinsicFrontier ℝ (C j) := fun j =>
    ((space_restrict_subset (hCv j)).trans fun _ ⟨hxL, hxC⟩ => hCL j ⟨hxC, hxL⟩).antisymm
      (hfr j)
  have hapex : ∀ j, (L.restrict (C j)).IsConeApex (p j) := fun j =>
    .of_space_eq_intrinsicFrontier (hCv j) (hM j) (hp j)
  -- the triangulation of `C j` by coning its frontier
  set T : J → SimplicialComplex ℝ E := fun j => (L.restrict (C j)).cone (p j) (hapex j)
  have hT : ∀ j, (T j).space = C j := fun j =>
    space_cone_of_space_eq_intrinsicFrontier (hCc j) (hCv j) (hM j) (hp j)
  have hTC : ∀ j ⦃s : Finset E⦄, s ∈ (T j).faces → (s : Set E) ⊆ C j := fun j _ hs =>
    ((T j).subset_space hs).trans (hT j).le
  set F : Option J → SimplicialComplex ℝ E := fun a => a.elim L T
  -- a point of `|L|` carried by a face of a piece is carried by a subface which is a face of `L`
  have hdesc : ∀ a ⦃s : Finset E⦄ ⦃x : E⦄, s ∈ (F a).faces → x ∈ convexHull ℝ (s : Set E) →
      x ∈ L.space → ∃ t ⊆ s, t ∈ L.faces ∧ x ∈ convexHull ℝ (t : Set E) := by
    rintro (_ | j) s x hs hx hxL
    · exact ⟨s, Finset.Subset.rfl, hs, hx⟩
    · have hxC : x ∈ C j := hT j ▸ convexHull_subset_space hs hx
      obtain ⟨hs', hx'⟩ := erase_mem_faces_of_mem_convexHull (hapex j) hs hx
        (hfr j (hCL j ⟨hxC, hxL⟩))
      exact ⟨_, erase_subset _ _, restrict_le hs', hx'⟩
  have hcompat : ∀ a b, ∀ ⦃s t : Finset E⦄, s ∈ (F a).faces → t ∈ (F b).faces →
      convexHull ℝ ↑s ∩ convexHull ℝ ↑t ⊆ convexHull ℝ (s ∩ t : Set E) := by
    rintro a b s t hs ht x ⟨hxs, hxt⟩
    rcases eq_or_ne a b with rfl | hab
    · exact (F a).inter_subset_convexHull hs ht ⟨hxs, hxt⟩
    -- two distinct pieces meet inside `|L|`
    have hxL : x ∈ L.space := by
      rcases a with _ | j
      · exact convexHull_subset_space hs hxs
      rcases b with _ | k
      · exact convexHull_subset_space ht hxt
      exact hCC (fun hjk => hab (congrArg some hjk))
        ⟨hT j ▸ convexHull_subset_space hs hxs, hT k ▸ convexHull_subset_space ht hxt⟩
    obtain ⟨s', hss', hs', hxs'⟩ := hdesc a hs hxs hxL
    obtain ⟨t', htt', ht', hxt'⟩ := hdesc b ht hxt hxL
    exact convexHull_mono (Set.inter_subset_inter (coe_subset.2 hss') (coe_subset.2 htt'))
      (L.inter_subset_convexHull hs' ht' ⟨hxs', hxt'⟩)
  -- a face of the cone on `C j` avoiding its apex is a face of `L`
  have hTL : ∀ j ⦃s : Finset E⦄, s ∈ (T j).faces → p j ∉ s → s ∈ L.faces := fun j _ hs hps =>
    restrict_le ((mem_cone_faces_iff_of_notMem (hapex j) hps).1 hs)
  refine ⟨glue F hcompat, ?_, fun B hB => ?_, fun j => ?_, fun s hs => ?_⟩
  · rw [space_glue, iUnion_option]
    simp only [F, Option.elim, hT]
  · ext s
    simp only [mem_restrict_faces, mem_glue_faces]
    refine ⟨fun ⟨⟨a, hs⟩, hsB⟩ => ⟨?_, hsB⟩, fun ⟨hs, hsB⟩ => ⟨⟨none, hs⟩, hsB⟩⟩
    rcases a with _ | j
    · exact hs
    · exact hTL j hs fun hps => Set.disjoint_left.1 (hB j) (hp j) (hsB hps)
  · have hrestrict : (glue F hcompat).restrict (C j) = T j := by
      ext s
      simp only [mem_restrict_faces, mem_glue_faces]
      refine ⟨fun ⟨⟨a, hs⟩, hsC⟩ => ?_, fun hs => ⟨⟨some j, hs⟩, hTC j hs⟩⟩
      rcases a with _ | k
      · exact le_cone (hapex j) (mem_restrict_faces.2 ⟨hs, hsC⟩)
      rcases eq_or_ne k j with rfl | hkj
      · exact hs
      -- the apex of the cone on `C k` is not in `C j`
      have hps : p k ∉ s := fun hps =>
        Set.disjoint_left.1 (hint k) (hp k) (hCC hkj.symm ⟨hsC hps, hpC k⟩)
      exact le_cone (hapex j) (mem_restrict_faces.2 ⟨hTL k hs hps, hsC⟩)
    rw [hrestrict]
    exact ⟨hT j, (finite_faces_cone_iff (hapex j)).2⟩
  · obtain ⟨a, hs⟩ := (mem_glue_faces hcompat).1 hs
    rcases a with _ | j
    · exact .inl hs
    · exact .inr ⟨j, hTC j hs⟩

section Cells

variable {P : ι → Set E}

/-- The inductive step of `exists_subdivision_extending`: a subdivision of the cells of
dimension `< n` extends to one of the cells of dimension `≤ n`. -/
private theorem exists_subdivision_lt_succ {L K : SimplicialComplex ℝ E}
    (hPc : ∀ i, IsCompact (P i)) (hPv : ∀ i, Convex ℝ (P i)) (hPne : ∀ i, (P i).Nonempty)
    (hPlf : LocallyFinite P)
    (hri : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (P i)) (intrinsicInterior ℝ (P j)))
    (hfr : ∀ i, intrinsicFrontier ℝ (P i) ⊆ L.space ∪ ⋃ (j) (_ : j ≠ i ∧ P j ⊆ P i), P j)
    (hL : ∀ i, P i ∩ L.space ⊆ (L.restrict (P i)).space)
    (hLi : ∀ i, Disjoint (intrinsicInterior ℝ (P i)) L.space)
    (hLfin : ∀ i, (L.restrict (P i)).faces.Finite) {n : ℕ} (hKL : K.restrict L.space = L)
    (hKs : K.space = L.space ∪ ⋃ (k) (_ : Module.finrank ℝ (vectorSpan ℝ (P k)) < n), P k)
    (hKP : ∀ k, Module.finrank ℝ (vectorSpan ℝ (P k)) < n →
      (K.restrict (P k)).space = P k ∧ (K.restrict (P k)).faces.Finite)
    (hKf : ∀ s ∈ K.faces, s ∈ L.faces ∨
      ∃ k, Module.finrank ℝ (vectorSpan ℝ (P k)) < n ∧ (s : Set E) ⊆ P k) :
    ∃ K' : SimplicialComplex ℝ E, K'.restrict L.space = L ∧
      K'.space = L.space ∪ ⋃ (k) (_ : Module.finrank ℝ (vectorSpan ℝ (P k)) < n + 1), P k ∧
      (∀ k, Module.finrank ℝ (vectorSpan ℝ (P k)) < n + 1 →
        (K'.restrict (P k)).space = P k ∧ (K'.restrict (P k)).faces.Finite) ∧
      ∀ s ∈ K'.faces, s ∈ L.faces ∨
        ∃ k, Module.finrank ℝ (vectorSpan ℝ (P k)) < n + 1 ∧ (s : Set E) ⊆ P k := by
  have hmeet {i j : ι} {x : E} (hxi : x ∈ intrinsicInterior ℝ (P i)) (hxj : x ∈ P j) :
      i = j ∨ Module.finrank ℝ (vectorSpan ℝ (P i)) < Module.finrank ℝ (vectorSpan ℝ (P j)) :=
    TauCeti.eq_or_finrank_lt_of_mem_intrinsicInterior hPv hPne hri hfr hLi hxi hxj
  have hLK : ∀ i, L.restrict (P i) ≤ K.restrict (P i) := fun i s hs =>
    mem_restrict_faces.2 ⟨(hKL ▸ restrict_le : L ≤ K) (mem_restrict_faces.1 hs).1,
      (mem_restrict_faces.1 hs).2⟩
  -- the intrinsic interior of a cell of dimension `≥ n` misses every cell of dimension `< n`
  have hB : ∀ i k, n ≤ Module.finrank ℝ (vectorSpan ℝ (P i)) →
      Module.finrank ℝ (vectorSpan ℝ (P k)) < n → Disjoint (intrinsicInterior ℝ (P i)) (P k) :=
    fun i k hi hk => Set.disjoint_left.2 fun x hxi hxk => by
      rcases hmeet hxi hxk with rfl | h <;> omega
  -- attach the `n`-dimensional cells to `K`, after checking the hypotheses of
  -- `exists_extension_of_intrinsicFrontier_subset_space`
  obtain ⟨K', hK's, hK'B, hK'C, hK'f⟩ := exists_extension_of_intrinsicFrontier_subset_space K
    (fun j : {i // Module.finrank ℝ (vectorSpan ℝ (P i)) = n} => P j) (fun j => hPc j)
    (fun j => hPv j) (fun j => hPne j)
    (fun ⟨i, hi⟩ x hx => by
      rcases hfr i hx with hxL | hx'
      · exact space_mono (hLK i) (hL i ⟨intrinsicFrontier_subset (hPc i).isClosed hx, hxL⟩)
      simp only [mem_iUnion, exists_prop] at hx'
      obtain ⟨j, ⟨hji, hjP⟩, hxj⟩ := hx'
      have hj := TauCeti.finrank_vectorSpan_lt_of_disjoint_intrinsicInterior (hPv j) (hPne j)
        hjP (hri hji)
      exact space_mono (restrict_mono hjP) ((hKP j (by omega)).1.symm ▸ hxj))
    (fun ⟨i, hi⟩ => by
      rw [hKs, Set.disjoint_union_right, Set.disjoint_iUnion₂_right]
      exact ⟨hLi i, fun k hk => hB i k hi.ge hk⟩)
    (fun i j hij x ⟨hxi, hxj⟩ => by
      have hij : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
      have hi := i.2
      have hj := j.2
      rw [hKs]
      rcases TauCeti.mem_intrinsicInterior_or_of_mem hPv hPne hri hfr hxi with
        h | h | ⟨k, hk, -, hxk⟩
      · rcases hmeet h hxj with h' | h' <;> [exact (hij h').elim; omega]
      · exact .inl h
      · exact .inr (mem_iUnion₂.2 ⟨k, by omega, intrinsicInterior_subset hxk⟩))
  refine ⟨K', ?_, ?_, fun k hk => ?_, fun s hs => ?_⟩
  · rw [hK'B _ fun ⟨i, _⟩ => hLi i, hKL]
  · rw [hK's, hKs, Set.union_assoc]
    congr 1
    ext x
    simp only [Set.mem_union, Set.mem_iUnion, exists_prop, Subtype.exists]
    constructor
    · rintro (⟨k, hk, hx⟩ | ⟨k, hk, hx⟩) <;> exact ⟨k, by omega, hx⟩
    · rintro ⟨k, hk, hx⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
      · exact .inl ⟨k, hk, hx⟩
      · exact .inr ⟨k, hk, hx⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
    · rw [hK'B _ fun ⟨i, hi⟩ => hB i k hi.ge hk]
      exact hKP k hk
    obtain ⟨hsp, hfin⟩ := hK'C ⟨k, hk⟩
    refine ⟨hsp, hfin (((hLfin k).union (((hPlf.finite_nonempty_inter_compact
      (hPc k)).inter_of_left {m | Module.finrank ℝ (vectorSpan ℝ (P m)) < n}).biUnion
        fun m hm => (hKP m hm.2).2)).subset ?_)⟩
    -- a face of `K` in `P k` is a face of `L` or lies in a smaller cell meeting `P k`
    intro s hs
    obtain ⟨hs, hsP⟩ := mem_restrict_faces.1 hs
    rcases hKf s hs with hsL | ⟨m, hm, hsm⟩
    · exact .inl (mem_restrict_faces.2 ⟨hsL, hsP⟩)
    · obtain ⟨y, hy⟩ := K.nonempty_of_mem_faces hs
      exact .inr (Set.mem_biUnion (x := m) ⟨⟨y, hsm hy, hsP hy⟩, hm⟩
        (mem_restrict_faces.2 ⟨hs, hsm⟩))
  · rcases hK'f s hs with hsK | ⟨⟨i, hi⟩, hsi⟩
    · rcases hKf s hsK with h | ⟨k, hk, hsk⟩
      · exact .inl h
      · exact .inr ⟨k, by omega, hsk⟩
    · exact .inr ⟨i, by omega, hsi⟩

end Cells

/-- **Relative simplicial subdivision of a family of compact convex cells.** Let `P i` be a
locally finite family of nonempty compact convex sets with pairwise disjoint intrinsic interiors,
and let `L` be a simplicial complex meeting every cell in a finite subcomplex and avoiding the
intrinsic interiors of all cells. Suppose the intrinsic frontier of each cell is covered by `|L|`
and the other cells contained in it. Then there is a simplicial complex `K` with
`|K| = |L| ∪ ⋃ i, P i` which contains `L`, has no other simplex with all its vertices in `|L|`,
triangulates every cell by finitely many of its simplices, and all of whose simplices outside `L`
lie in a single cell. -/
theorem exists_subdivision_extending (L : SimplicialComplex ℝ E) (P : ι → Set E)
    (hPc : ∀ i, IsCompact (P i)) (hPv : ∀ i, Convex ℝ (P i)) (hPne : ∀ i, (P i).Nonempty)
    (hPlf : LocallyFinite P)
    (hri : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (P i)) (intrinsicInterior ℝ (P j)))
    (hfr : ∀ i, intrinsicFrontier ℝ (P i) ⊆ L.space ∪ ⋃ (j) (_ : j ≠ i ∧ P j ⊆ P i), P j)
    (hL : ∀ i, P i ∩ L.space ⊆ (L.restrict (P i)).space)
    (hLi : ∀ i, Disjoint (intrinsicInterior ℝ (P i)) L.space)
    (hLfin : ∀ i, (L.restrict (P i)).faces.Finite) :
    ∃ K : SimplicialComplex ℝ E, K.restrict L.space = L ∧ K.space = L.space ∪ ⋃ i, P i ∧
      (∀ i, (K.restrict (P i)).space = P i ∧ (K.restrict (P i)).faces.Finite) ∧
      ∀ s ∈ K.faces, s ∈ L.faces ∨ ∃ i, (s : Set E) ⊆ P i := by
  -- subdivide the cells of dimension `< n`, by induction on `n`
  have key : ∀ n : ℕ, ∃ K : SimplicialComplex ℝ E, K.restrict L.space = L ∧
      K.space = L.space ∪ ⋃ (k) (_ : Module.finrank ℝ (vectorSpan ℝ (P k)) < n), P k ∧
      (∀ k, Module.finrank ℝ (vectorSpan ℝ (P k)) < n →
        (K.restrict (P k)).space = P k ∧ (K.restrict (P k)).faces.Finite) ∧
      ∀ s ∈ K.faces, s ∈ L.faces ∨
        ∃ k, Module.finrank ℝ (vectorSpan ℝ (P k)) < n ∧ (s : Set E) ⊆ P k := by
    intro n
    induction n with
    | zero =>
      exact ⟨L, restrict_eq_self_of_space_subset Subset.rfl, by simp, by simp,
        fun s hs => .inl hs⟩
    | succ n ih =>
      obtain ⟨K, hKL, hKs, hKP, hKf⟩ := ih
      exact exists_subdivision_lt_succ hPc hPv hPne hPlf hri hfr hL hLi hLfin hKL hKs hKP hKf
  -- every cell has dimension at most that of `E`
  have hδE : ∀ k, Module.finrank ℝ (vectorSpan ℝ (P k)) < Module.finrank ℝ E + 1 := fun k =>
    Nat.lt_succ_of_le (Submodule.finrank_le _)
  obtain ⟨K, hKL, hKs, hKP, hKf⟩ := key (Module.finrank ℝ E + 1)
  refine ⟨K, hKL, ?_, fun k => hKP k (hδE k), fun s hs =>
    (hKf s hs).imp_right fun ⟨k, _, h⟩ => ⟨k, h⟩⟩
  rw [hKs]
  simp only [hδE, iUnion_true]

/-- **Simplicial subdivision of a family of compact convex cells.** Let `P i` be a locally finite
family of nonempty compact convex sets with pairwise disjoint intrinsic interiors, such that the
intrinsic frontier of each cell is covered by the other cells contained in it; for instance,
compact convex polytopes each proper face of which is a union of lower-dimensional cells of the
family. Then there is a locally finite simplicial complex `K` with `|K| = ⋃ i, P i` which
triangulates every cell by finitely many of its simplices, and every simplex of which lies in a
single cell. -/
theorem exists_subdivision (P : ι → Set E) (hPc : ∀ i, IsCompact (P i))
    (hPv : ∀ i, Convex ℝ (P i)) (hPne : ∀ i, (P i).Nonempty) (hPlf : LocallyFinite P)
    (hri : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (P i)) (intrinsicInterior ℝ (P j)))
    (hfr : ∀ i, intrinsicFrontier ℝ (P i) ⊆ ⋃ (j) (_ : j ≠ i ∧ P j ⊆ P i), P j) :
    ∃ K : SimplicialComplex ℝ E, K.space = ⋃ i, P i ∧
      (∀ i, (K.restrict (P i)).space = P i ∧ (K.restrict (P i)).faces.Finite) ∧
      (∀ s ∈ K.faces, ∃ i, (s : Set E) ⊆ P i) ∧
      LocallyFinite fun σ : K.faces => convexHull ℝ (σ : Set E) := by
  obtain ⟨K, -, hKs, hKP, hKf⟩ := exists_subdivision_extending ⊥ P hPc hPv hPne hPlf hri
    (by simpa [space_bot] using hfr) (by simp [space_bot]) (by simp [space_bot])
    (fun _ => Set.finite_empty.subset fun _ hs => (mem_restrict_faces.1 hs).1)
  have hKf' : ∀ s ∈ K.faces, ∃ i, (s : Set E) ⊆ P i := fun s hs =>
    (hKf s hs).resolve_left (Set.notMem_empty s)
  refine ⟨K, by simpa [space_bot] using hKs, hKP, hKf',
    locallyFinite_convexHull_of_finite_restrict hPv hPlf (L := ⊥) ?_ (fun i => (hKP i).2)
      fun s hs => .inr (hKf' s hs)⟩
  intro x
  exact ⟨univ, Filter.univ_mem, Set.finite_empty.subset fun σ _ => (Set.notMem_empty σ.1 σ.2).elim⟩

end Geometry.SimplicialComplex
