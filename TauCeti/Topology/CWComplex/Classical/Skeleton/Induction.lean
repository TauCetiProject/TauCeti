/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Subcomplex
public import TauCeti.Topology.CWComplex.Classical.OpenCells
public import TauCeti.Topology.CWComplex.Classical.Quotient
public import TauCeti.Topology.CWComplex.Classical.Skeleton.Basic

/-!
# Skeletal induction for relative CW complexes

Continuous maps out of a relative CW complex `C`, and more generally out of `Z × C` for a locally
compact space `Z`, can be built one skeleton at a time.

* Passing from `skeletonLT C n` to `skeletonLT C (n + 1)` means extending over the closed
  `n`-cells.  A map on `Z × skeletonLT C n`, together with one map on `Z × closedBall 0 1` for each
  `n`-cell that agrees with it on `Z × sphere 0 1` through the characteristic map, glues to a
  continuous map on `Z × skeletonLT C (n + 1)`.
* Maps on `Z × skeletonLT C (k + j)` for all `j : ℕ`, each restricting to the previous one, glue
  to a continuous map on `Z × C`.

In both cases continuity of the glued map is the weak-topology axiom of the complex, in the form
`TauCeti.continuous_prod_complex_iff`.  Taking `Z = I` builds homotopies, as in the proof that
relative CW inclusions have the homotopy extension property; taking `Z` to be a point builds
maps, as in the extension lemma for maps into a space whose spheres are null-homotopic.

## Main results

* `TauCeti.exists_continuousMap_prod_skeletonLT_succ`: extension over the closed `n`-cells, from
  `Z × skeletonLT C n` to `Z × skeletonLT C (n + 1)`.
* `TauCeti.exists_continuousMap_prod_complex_of_skeletonLT`: a compatible family of maps on the
  products of `Z` with the skeleta from the `k`-th one on glues to a map on `Z × C`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, Proposition 0.16, and Section 4.1, Lemma 4.7, where maps and homotopies are extended
  over a CW complex cell by cell and skeleton by skeleton.
* G. W. Whitehead, *Elements of Homotopy Theory*, Chapter II.
-/

public section

noncomputable section

open Metric Set Topology Topology.RelCWComplex

universe u

namespace TauCeti

variable {X : Type u} [TopologicalSpace X] [T2Space X] {C D : Set X} [RelCWComplex C D]
  {Z Y : Type*} [TopologicalSpace Z] [TopologicalSpace Y]

section Step

variable {n : ℕ}

/-- The extension of a map `G` given on `Z × skeletonLT C n` over `Z × skeletonLT C (n + 1)`,
built from maps `K j` on the products of `Z` with the closed `n`-cells: on an open `n`-cell it is
read off `K j` through the inverse of the characteristic map, and elsewhere it is `G`. -/
private def extendOverCells (G : C(Z × (skeletonLT C n : Set X), Y))
    (K : cell C n → C(Z × closedBall (0 : Fin n → ℝ) 1, Y))
    (p : Z × (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X)) : Y :=
  open Classical in
  if h : ∃ j : cell C n, (p.2 : X) ∈ openCell n j then
    K h.choose (p.1, ⟨(map n h.choose).symm p.2,
      ball_subset_closedBall (map_symm_mem_ball _ h.choose_spec)⟩)
  else G (p.1, ⟨p.2, mem_skeletonLT_of_forall_notMem_openCell _ p.2.2 (not_exists.1 h)⟩)

variable {G : C(Z × (skeletonLT C n : Set X), Y)}
  {K : cell C n → C(Z × closedBall (0 : Fin n → ℝ) 1, Y)}

private lemma extendOverCells_of_mem (z : Z) (x : (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X))
    (hx : (x : X) ∈ (skeletonLT C n : Set X)) :
    extendOverCells G K (z, x) = G (z, ⟨x, hx⟩) := by
  rw [extendOverCells, dite_eq_right fun ⟨j, hj⟩ ↦
    (disjoint_skeletonLT_openCell le_rfl).notMem_of_mem_left hx hj]

private lemma extendOverCells_map
    (hK : ∀ j z (y : closedBall (0 : Fin n → ℝ) 1) (hy : (y : Fin n → ℝ) ∈ sphere 0 1),
      K j (z, y) = G (z, ⟨map n j y, cellFrontier_subset_skeletonLT n j ⟨y, hy, rfl⟩⟩))
    (j : cell C n) (z : Z) (y : closedBall (0 : Fin n → ℝ) 1) :
    extendOverCells G K
      (z, ⟨map n j y, map_mem_skeletonLT_succ j (mem_closedBall_zero_iff.1 y.2)⟩) = K j (z, y) := by
  by_cases hy : (y : Fin n → ℝ) ∈ ball 0 1
  · have hmem : map n j y ∈ openCell n j := ⟨y, hy, rfl⟩
    -- The open cell containing `map n j y` is the one of `j`, and `y` is recovered from its
    -- image by the inverse of the characteristic map.
    have key : ∀ (i : cell C n) (hi : map n j y ∈ openCell n i),
        K i (z, ⟨(map n i).symm (map n j y), ball_subset_closedBall (map_symm_mem_ball _ hi)⟩) =
          K j (z, y) := by
      intro i hi
      obtain rfl : i = j := by
        by_contra hne
        exact (disjoint_openCell_of_ne (by simpa using hne)).notMem_of_mem_left hi hmem
      congr
      exact (map n i).left_inv ((source_eq n i).symm ▸ hy)
    have h : ∃ i : cell C n, map n j y ∈ openCell n i := ⟨j, hmem⟩
    rw [extendOverCells, dite_eq_left h]
    exact key _ h.choose_spec
  · have hs : (y : Fin n → ℝ) ∈ sphere 0 1 :=
      mem_sphere.2 (le_antisymm (mem_closedBall.1 y.2) (not_lt.1 fun h ↦ hy (mem_ball.2 h)))
    rw [extendOverCells_of_mem _ _ (cellFrontier_subset_skeletonLT n j ⟨y, hs, rfl⟩), hK j z y hs]

variable [LocallyCompactSpace Z]

variable (G K) in
/-- **Extension over the closed `n`-cells.**  A map `G` on `Z × skeletonLT C n` and maps `K j` on
`Z × closedBall 0 1`, one for each `n`-cell `j`, that agree with `G` on `Z × sphere 0 1` through
the characteristic map of `j`, glue to a continuous map on `Z × skeletonLT C (n + 1)` that
restricts to `G` and, through each characteristic map, to `K j`. -/
theorem exists_continuousMap_prod_skeletonLT_succ
    (hK : ∀ j z (y : closedBall (0 : Fin n → ℝ) 1) (hy : (y : Fin n → ℝ) ∈ sphere 0 1),
      K j (z, y) = G (z, ⟨map n j y, cellFrontier_subset_skeletonLT n j ⟨y, hy, rfl⟩⟩)) :
    ∃ F : C(Z × (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X), Y),
      (∀ z (x : X) (hx : x ∈ (skeletonLT C n : Set X)),
        F (z, ⟨x, skeletonLT_mono (by exact_mod_cast n.le_succ) hx⟩) = G (z, ⟨x, hx⟩)) ∧
      ∀ j z (y : closedBall (0 : Fin n → ℝ) 1),
        F (z, ⟨map n j y, map_mem_skeletonLT_succ j (mem_closedBall_zero_iff.1 y.2)⟩) =
          K j (z, y) := by
  refine ⟨⟨extendOverCells G K, ?_⟩, fun z x hx ↦ extendOverCells_of_mem z _ hx,
    extendOverCells_map hK⟩
  rw [continuous_prod_complex_iff]
  refine ⟨fun m ⟨j, hj⟩ ↦ ?_, ?_⟩
  · rcases lt_or_ge m n with hmn | hmn
    · -- A cell of dimension below `n` lies in the `n`-skeleton, where the map is `G`.
      have hmem (y : closedBall (0 : Fin m → ℝ) 1) : map m j y ∈ (skeletonLT C n : Set X) :=
        skeletonLT_mono (by exact_mod_cast hmn) (closedCell_subset_skeletonLT m j ⟨y, y.2, rfl⟩)
      exact Continuous.congr (G.continuous.comp (continuous_fst.prodMk
        (((continuous_map_closedBall j).comp continuous_snd).subtype_mk fun p ↦ hmem p.2)))
        fun p ↦ (extendOverCells_of_mem p.1 ⟨_, _⟩ (hmem p.2)).symm
    · -- A cell of the `n + 1`-skeleton of dimension at least `n` is an `n`-cell, where the map is
      -- read off `K j`.
      obtain rfl : m = n := le_antisymm (Nat.lt_succ_iff.1 (by
        simpa only [RelCWComplex.skeletonLT_I, mem_ofPred_eq, Nat.cast_lt] using hj)) hmn
      exact (K j).continuous.congr fun p ↦ (extendOverCells_map hK j p.1 p.2).symm
  · have hmem (d : D) : (d : X) ∈ (skeletonLT C n : Set X) := (skeletonLT C n).base_subset d.2
    exact Continuous.congr (G.continuous.comp (continuous_fst.prodMk
      ((continuous_subtype_val.comp continuous_snd).subtype_mk fun p ↦ hmem p.2)))
      fun p ↦ (extendOverCells_of_mem p.1 ⟨_, _⟩ (hmem p.2)).symm

end Step

section Glue

variable {k : ℕ}

private lemma skeletonLT_add_subset_add {j j' : ℕ} (h : j ≤ j') :
    (skeletonLT C ((k + j : ℕ) : ℕ∞) : Set X) ⊆ skeletonLT C ((k + j' : ℕ) : ℕ∞) :=
  skeletonLT_mono (by exact_mod_cast Nat.add_le_add_left h k)

variable {F : ∀ j : ℕ, C(Z × (skeletonLT C ((k + j : ℕ) : ℕ∞) : Set X), Y)}

private lemma apply_of_le
    (hF : ∀ j z (x : X) (hx : x ∈ (skeletonLT C ((k + j : ℕ) : ℕ∞) : Set X)),
      F (j + 1) (z, ⟨x, skeletonLT_add_subset_add j.le_succ hx⟩) = F j (z, ⟨x, hx⟩))
    {j j' : ℕ} (h : j ≤ j') (z : Z) {x : X}
    (hx : x ∈ (skeletonLT C ((k + j : ℕ) : ℕ∞) : Set X)) :
    F j' (z, ⟨x, skeletonLT_add_subset_add h hx⟩) = F j (z, ⟨x, hx⟩) := by
  induction j', h using Nat.le_induction with
  | base => rfl
  | succ j' h ih => rw [hF j' z x (skeletonLT_add_subset_add h hx), ih]

variable (F) in
/-- The map on `Z × C` glued from a family of maps on the products of `Z` with the skeleta: at a
point of `C` it is the value of the map on any skeleton containing that point. -/
private def glued (p : Z × C) : Y :=
  F (exists_mem_skeletonLT_add k p.2.2).choose
    (p.1, ⟨p.2, (exists_mem_skeletonLT_add k p.2.2).choose_spec⟩)

private lemma glued_apply
    (hF : ∀ j z (x : X) (hx : x ∈ (skeletonLT C ((k + j : ℕ) : ℕ∞) : Set X)),
      F (j + 1) (z, ⟨x, skeletonLT_add_subset_add j.le_succ hx⟩) = F j (z, ⟨x, hx⟩))
    (j : ℕ) (z : Z) (x : C) (hx : (x : X) ∈ (skeletonLT C ((k + j : ℕ) : ℕ∞) : Set X)) :
    glued F (z, x) = F j (z, ⟨x, hx⟩) := by
  rw [glued]
  rcases le_total (exists_mem_skeletonLT_add k x.2).choose j with h | h
  · exact (apply_of_le hF h z _).symm
  · exact apply_of_le hF h z hx

variable (F) in
/-- **Gluing over the skeleta.**  Maps `F j` on `Z × skeletonLT C (k + j)` for all `j : ℕ`, each
restricting to the previous one, glue to a continuous map on `Z × C` that restricts to every
`F j`. -/
theorem exists_continuousMap_prod_complex_of_skeletonLT [LocallyCompactSpace Z]
    (hF : ∀ j z (x : X) (hx : x ∈ (skeletonLT C ((k + j : ℕ) : ℕ∞) : Set X)),
      F (j + 1) (z, ⟨x, skeletonLT_mono (by exact_mod_cast (k + j).le_succ) hx⟩) =
        F j (z, ⟨x, hx⟩)) :
    ∃ G : C(Z × C, Y), ∀ j z (x : X) (hx : x ∈ (skeletonLT C ((k + j : ℕ) : ℕ∞) : Set X)),
      G (z, ⟨x, (skeletonLT C _).subset_complex hx⟩) = F j (z, ⟨x, hx⟩) := by
  refine ⟨⟨glued F, ?_⟩, fun j z x hx ↦ glued_apply hF j z ⟨x, _⟩ hx⟩
  rw [continuous_prod_complex_iff]
  refine ⟨fun m j ↦ ?_, ?_⟩
  · -- An `m`-cell lies in the `k + (m + 1)`-skeleton.
    have hmem (y : closedBall (0 : Fin m → ℝ) 1) :
        map m j y ∈ (skeletonLT C ((k + (m + 1) : ℕ) : ℕ∞) : Set X) :=
      skeletonLT_mono (by exact_mod_cast Nat.le_add_left (m + 1) k)
        (closedCell_subset_skeletonLT m j ⟨y, y.2, rfl⟩)
    exact ((F (m + 1)).continuous.comp (continuous_fst.prodMk
      (((continuous_map_closedBall j).comp continuous_snd).subtype_mk fun p ↦ hmem p.2))).congr
      fun p ↦ (glued_apply hF (m + 1) p.1 ⟨_, _⟩ (hmem p.2)).symm
  · have hmem (d : D) : (d : X) ∈ (skeletonLT C ((k + 0 : ℕ) : ℕ∞) : Set X) :=
      (skeletonLT C _).base_subset d.2
    exact ((F 0).continuous.comp (continuous_fst.prodMk
      ((continuous_subtype_val.comp continuous_snd).subtype_mk fun p ↦ hmem p.2))).congr
      fun p ↦ (glued_apply hF 0 p.1 ⟨_, _⟩ (hmem p.2)).symm

end Glue

end TauCeti
