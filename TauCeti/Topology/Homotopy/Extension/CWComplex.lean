/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Subcomplex
public import TauCeti.Topology.CWComplex.Classical.Quotient
public import TauCeti.Topology.Homotopy.Extension.Ball

/-!
# Relative CW inclusions are closed cofibrations

The base `D` of a relative CW complex `C` has the homotopy extension property inside `C`, and so
does every skeleton of `C`.  As `X` is Hausdorff, these subsets are closed
(`TauCeti.HasHomotopyExtensionProperty.isClosed`), so their inclusions are closed cofibrations.
This is what makes skeletal induction and homotopy-invariance arguments for CW pairs work: maps
and homotopies can be modified on the base or on a skeleton and extended over the whole complex.

## Main results

* `TauCeti.hasHomotopyExtensionProperty_skeletonLT_succ`: `skeletonLT C n` has the homotopy
  extension property inside `skeletonLT C (n + 1)`.
* `TauCeti.hasHomotopyExtensionProperty_skeletonLT`: every skeleton has the homotopy extension
  property inside the complex.
* `TauCeti.hasHomotopyExtensionProperty_base`: **the base of a relative CW complex has the
  homotopy extension property inside the complex.**

## Related results

`TauCeti.hasHomotopyExtensionProperty_sphere_closedBall` gives the homotopy extension property
for the boundary of a closed cell. `TauCeti.continuous_prod_complex_iff` characterizes
continuity of maps on products with a relative CW complex, including homotopies.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, Proposition 0.16: a CW pair has the homotopy extension property.
-/

public section

noncomputable section

open Metric Set Topology Topology.RelCWComplex unitInterval

universe u

namespace TauCeti

variable {X : Type u} [TopologicalSpace X] [T2Space X] {C D : Set X} [RelCWComplex C D]

section Step

variable {n : ℕ}

/-- A point of `skeletonLT C (n + 1)` that lies in no open `n`-cell lies in `skeletonLT C n`. -/
private lemma mem_skeletonLT_of_forall_notMem_openCell {x : X}
    (hx : x ∈ (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X))
    (h : ∀ j : cell C n, x ∉ openCell n j) : x ∈ (skeletonLT C (n : ℕ∞) : Set X) := by
  obtain hx | ⟨m, hm, j, hxj⟩ := mem_skeletonLT_iff.1 hx
  · exact (skeletonLT C n).base_subset hx
  · have hm : m < n := by
      rcases (Nat.lt_succ_iff.1 (by exact_mod_cast hm)).lt_or_eq with hm | rfl
      · exact hm
      · exact absurd hxj (h j)
    exact skeletonLT_mono (by exact_mod_cast hm) (openCell_subset_skeletonLT m j hxj)

omit [T2Space X] in
/-- The inverse of a characteristic map sends a point of the open cell into the open ball. -/
private lemma symm_mem_ball {j : cell C n} {x : X} (hx : x ∈ openCell n j) :
    (map n j).symm x ∈ ball (0 : Fin n → ℝ) 1 := by
  rw [← source_eq n j]
  refine (map n j).map_target ?_
  rw [← (map n j).image_source_eq_target, source_eq n j]
  exact hx

omit [T2Space X] in
private lemma map_symm_eq {j : cell C n} {x : X} (hx : x ∈ openCell n j) :
    map n j ((map n j).symm x) = x := by
  refine (map n j).right_inv ?_
  rw [← (map n j).image_source_eq_target, source_eq n j]
  exact hx

/-- An open `n`-cell is disjoint from `skeletonLT C n`. -/
private lemma notMem_openCell_of_mem_skeletonLT {x : X} (hx : x ∈ (skeletonLT C n : Set X))
    (j : cell C n) : x ∉ openCell n j :=
  (disjoint_skeletonLT_openCell le_rfl).notMem_of_mem_left hx

omit [T2Space X] in
private lemma continuous_map_closedBall (j : cell C n) :
    Continuous fun y : closedBall (0 : Fin n → ℝ) 1 ↦ map n j y :=
  (continuousOn n j).comp_continuous continuous_subtype_val fun y ↦ y.2

private lemma map_mem_skeletonLT_succ (j : cell C n) (y : closedBall (0 : Fin n → ℝ) 1) :
    map n j y ∈ (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X) := by
  rw [Nat.cast_succ]
  exact closedCell_subset_skeletonLT n j ⟨y, y.2, rfl⟩

variable {Y : Type u} [TopologicalSpace Y]
  (f : C(skeletonLT C ((n + 1 : ℕ) : ℕ∞), Y))
  (G : C(I × (Subtype.val ⁻¹' (skeletonLT C n : Set X) :
    Set (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X)), Y))

/-- The extension of a homotopy `G` given on `skeletonLT C n` over `skeletonLT C (n + 1)`, built
from extensions `K j` of `G` over the closed `n`-cells: on an open `n`-cell it is read off `K j`
through the inverse of the characteristic map, and elsewhere it is `G`. -/
private def extendOverCells (K : cell C n → C(I × closedBall (0 : Fin n → ℝ) 1, Y))
    (p : I × (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X)) : Y :=
  open Classical in
  if h : ∃ j : cell C n, (p.2 : X) ∈ openCell n j then
    K h.choose (p.1, ⟨(map n h.choose).symm p.2,
      ball_subset_closedBall (symm_mem_ball h.choose_spec)⟩)
  else G (p.1, ⟨p.2, mem_skeletonLT_of_forall_notMem_openCell p.2.2 (not_exists.1 h)⟩)

variable {G} {K : cell C n → C(I × closedBall (0 : Fin n → ℝ) 1, Y)}

private lemma extendOverCells_of_mem (t : I) (x : (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X))
    (hx : (x : X) ∈ (skeletonLT C n : Set X)) :
    extendOverCells G K (t, x) = G (t, ⟨x, hx⟩) := by
  rw [extendOverCells, dite_eq_right fun ⟨j, hj⟩ ↦ notMem_openCell_of_mem_skeletonLT hx j hj]

private lemma extendOverCells_map
    (hK : ∀ j t (y : closedBall (0 : Fin n → ℝ) 1) (hy : (y : Fin n → ℝ) ∈ sphere 0 1),
      K j (t, y) = G (t, ⟨⟨map n j y, map_mem_skeletonLT_succ j y⟩,
        cellFrontier_subset_skeletonLT n j ⟨y, hy, rfl⟩⟩))
    (j : cell C n) (t : I) (y : closedBall (0 : Fin n → ℝ) 1) :
    extendOverCells G K (t, ⟨map n j y, map_mem_skeletonLT_succ j y⟩) = K j (t, y) := by
  by_cases hy : (y : Fin n → ℝ) ∈ ball 0 1
  · have hmem : map n j y ∈ openCell n j := ⟨y, hy, rfl⟩
    -- The open cell containing `map n j y` is the one of `j`, and `y` is recovered from its
    -- image by the inverse of the characteristic map.
    have key : ∀ (i : cell C n) (hi : map n j y ∈ openCell n i),
        K i (t, ⟨(map n i).symm (map n j y), ball_subset_closedBall (symm_mem_ball hi)⟩) =
          K j (t, y) := by
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
    rw [extendOverCells_of_mem _ _ (cellFrontier_subset_skeletonLT n j ⟨y, hs, rfl⟩), hK j t y hs]

end Step

/-- **`skeletonLT C n` has the homotopy extension property inside `skeletonLT C (n + 1)`.** -/
theorem hasHomotopyExtensionProperty_skeletonLT_succ (n : ℕ) :
    HasHomotopyExtensionProperty (Subtype.val ⁻¹' (skeletonLT C n : Set X) :
      Set (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X)) := by
  rw [hasHomotopyExtensionProperty_iff]
  intro Y _ f G hG
  -- Extend `G` over every closed `n`-cell, by the homotopy extension property of the boundary
  -- sphere inside the closed ball.
  have hext : ∀ j : cell C n, ∃ K : C(I × closedBall (0 : Fin n → ℝ) 1, Y),
      (∀ y, K (0, y) = f ⟨map n j y, map_mem_skeletonLT_succ j y⟩) ∧
      ∀ t (y : closedBall (0 : Fin n → ℝ) 1) (hy : (y : Fin n → ℝ) ∈ sphere 0 1),
        K (t, y) = G (t, ⟨⟨map n j y, map_mem_skeletonLT_succ j y⟩,
          cellFrontier_subset_skeletonLT n j ⟨y, hy, rfl⟩⟩) := by
    intro j
    obtain ⟨K, hK0, hKs⟩ :=
      (hasHomotopyExtensionProperty_sphere_closedBall (E := Fin n → ℝ)).exists_extension_of_isClosed
        (isClosed_sphere.preimage continuous_subtype_val)
        (f.comp ⟨fun y ↦ ⟨map n j y, map_mem_skeletonLT_succ j y⟩,
          (continuous_map_closedBall j).subtype_mk _⟩)
        (G.comp ⟨fun p ↦ (p.1, ⟨⟨map n j p.2, map_mem_skeletonLT_succ j p.2⟩,
          cellFrontier_subset_skeletonLT n j ⟨p.2, p.2.2, rfl⟩⟩),
          continuous_fst.prodMk ((((continuous_map_closedBall j).comp
            (continuous_subtype_val.comp continuous_snd)).subtype_mk _).subtype_mk _)⟩)
        fun a ↦ hG _
    exact ⟨K, hK0, fun t y hy ↦ hKs t ⟨y, hy⟩⟩
  choose K hK0 hKs using hext
  refine ⟨⟨extendOverCells G K, ?_⟩, fun x ↦ ?_, fun t a ↦ extendOverCells_of_mem t a.1 a.2⟩
  · rw [continuous_prod_complex_iff]
    refine ⟨fun m ⟨j, hj⟩ ↦ ?_, ?_⟩
    · rcases lt_or_ge m n with hmn | hmn
      · -- A cell of dimension below `n` lies in the `n`-skeleton, where the homotopy is `G`.
        have hmem (y : closedBall (0 : Fin m → ℝ) 1) : map m j y ∈ (skeletonLT C n : Set X) :=
          skeletonLT_mono (by exact_mod_cast hmn) (closedCell_subset_skeletonLT m j ⟨y, y.2, rfl⟩)
        refine Continuous.congr (G.continuous.comp (continuous_fst.prodMk
          ((((continuous_map_closedBall j).comp continuous_snd).subtype_mk _).subtype_mk
            fun p ↦ hmem p.2))) fun p ↦ (extendOverCells_of_mem _ _ (hmem p.2)).symm
      · -- A cell of the `n + 1`-skeleton of dimension at least `n` is an `n`-cell, where the
        -- homotopy is read off the extension `K j`.
        obtain rfl : m = n := le_antisymm (Nat.lt_succ_iff.1 (by
          simpa only [RelCWComplex.skeletonLT_I, mem_ofPred_eq, Nat.cast_lt] using hj)) hmn
        exact (K j).continuous.congr fun p ↦ (extendOverCells_map hKs j p.1 p.2).symm
    · have hmem (d : D) : (d : X) ∈ (skeletonLT C n : Set X) := (skeletonLT C n).base_subset d.2
      exact Continuous.congr (G.continuous.comp (continuous_fst.prodMk
        (((continuous_subtype_val.comp continuous_snd).subtype_mk _).subtype_mk
          fun p ↦ hmem p.2))) fun p ↦ (extendOverCells_of_mem _ _ (hmem p.2)).symm
  · by_cases hx : (x : X) ∈ (skeletonLT C n : Set X)
    · rw [ContinuousMap.coe_mk, extendOverCells_of_mem _ _ hx]
      exact hG ⟨x, hx⟩
    · obtain ⟨j, hj⟩ : ∃ j : cell C n, (x : X) ∈ openCell n j := by
        by_contra h
        exact hx (mem_skeletonLT_of_forall_notMem_openCell x.2 (not_exists.1 h))
      set y : closedBall (0 : Fin n → ℝ) 1 :=
        ⟨(map n j).symm x, ball_subset_closedBall (symm_mem_ball hj)⟩
      have hxy : x = ⟨map n j y, map_mem_skeletonLT_succ j y⟩ :=
        Subtype.ext (map_symm_eq hj).symm
      rw [ContinuousMap.coe_mk, hxy, extendOverCells_map hKs, hK0]

section Glue

variable {Y : Type u} [TopologicalSpace Y] {k : ℕ} {f : C(C, Y)}
  {H : C(I × (Subtype.val ⁻¹' (skeletonLT C k : Set X) : Set C), Y)}

private lemma skeletonLT_add_subset_add {j j' : ℕ} (h : j ≤ j') :
    (skeletonLT C ((k + j : ℕ) : ℕ∞) : Set X) ⊆ skeletonLT C ((k + j' : ℕ) : ℕ∞) :=
  skeletonLT_mono (by exact_mod_cast Nat.add_le_add_left h k)

variable (k f H) in
/-- The solutions of the homotopy extension problem `(f, H)` on the successive skeleta
`skeletonLT C (k + j)`, each obtained from the previous one by
`TauCeti.hasHomotopyExtensionProperty_skeletonLT_succ`. -/
private def extensionSeq (hH : ∀ a, H (0, a) = f a) : (j : ℕ) →
    {G : C(I × (skeletonLT C ((k + j : ℕ) : ℕ∞) : Set X), Y) //
      ∀ x, G (0, x) = f ⟨x, (skeletonLT C _).subset_complex x.2⟩}
  | 0 => ⟨H.comp ⟨fun p ↦ (p.1, ⟨⟨p.2, (skeletonLT C _).subset_complex p.2.2⟩, p.2.2⟩),
      by fun_prop⟩, fun x ↦ hH _⟩
  | j + 1 =>
    have h := (hasHomotopyExtensionProperty_skeletonLT_succ (C := C) (k + j)).exists_extension
      (f.comp ⟨fun x ↦ ⟨x, (skeletonLT C _).subset_complex x.2⟩, by fun_prop⟩)
      ((extensionSeq hH j).1.comp ⟨fun p ↦ (p.1, ⟨p.2, p.2.2⟩), by fun_prop⟩)
      fun a ↦ (extensionSeq hH j).2 _
    ⟨h.choose, h.choose_spec.1⟩

variable {hH : ∀ a, H (0, a) = f a}

private lemma extensionSeq_succ_apply (j : ℕ) (t : I)
    (x : (skeletonLT C ((k + (j + 1) : ℕ) : ℕ∞) : Set X))
    (hx : (x : X) ∈ (skeletonLT C ((k + j : ℕ) : ℕ∞) : Set X)) :
    (extensionSeq k f H hH (j + 1)).1 (t, x) = (extensionSeq k f H hH j).1 (t, ⟨x, hx⟩) := by
  rw [extensionSeq]
  exact ((hasHomotopyExtensionProperty_skeletonLT_succ (C := C) (k + j)).exists_extension _ _
    fun a ↦ (extensionSeq k f H hH j).2 _).choose_spec.2 t ⟨x, hx⟩

private lemma extensionSeq_apply_of_le {j j' : ℕ} (h : j ≤ j') (t : I) {x : X}
    (hx : x ∈ (skeletonLT C ((k + j : ℕ) : ℕ∞) : Set X)) :
    (extensionSeq k f H hH j').1 (t, ⟨x, skeletonLT_add_subset_add h hx⟩) =
      (extensionSeq k f H hH j).1 (t, ⟨x, hx⟩) := by
  induction j', h using Nat.le_induction with
  | base => rfl
  | succ j' h ih => rw [extensionSeq_succ_apply j' t _ (skeletonLT_add_subset_add h hx), ih]

private lemma exists_mem_skeletonLT_add (x : C) :
    ∃ j : ℕ, (x : X) ∈ (skeletonLT C ((k + j : ℕ) : ℕ∞) : Set X) := by
  have hx : (x : X) ∈ ⋃ j : ℕ, (skeletonLT C j : Set X) := by
    rw [iUnion_skeletonLT_eq_complex]
    exact x.2
  obtain ⟨j, hj⟩ := mem_iUnion.1 hx
  exact ⟨j, skeletonLT_mono (by exact_mod_cast Nat.le_add_left j k) hj⟩

variable (hH) in
/-- The solution of the homotopy extension problem `(f, H)` on all of `C`: at a point of `C` it is
the value of the solution on any skeleton containing that point. -/
private def glued (p : I × C) : Y :=
  (extensionSeq k f H hH (exists_mem_skeletonLT_add p.2).choose).1
    (p.1, ⟨p.2, (exists_mem_skeletonLT_add p.2).choose_spec⟩)

private lemma glued_apply (j : ℕ) (t : I) (x : C)
    (hx : (x : X) ∈ (skeletonLT C ((k + j : ℕ) : ℕ∞) : Set X)) :
    glued hH (t, x) = (extensionSeq k f H hH j).1 (t, ⟨x, hx⟩) := by
  rw [glued]
  rcases le_total (exists_mem_skeletonLT_add (k := k) x).choose j with h | h
  · exact (extensionSeq_apply_of_le h t _).symm
  · exact extensionSeq_apply_of_le h t hx

end Glue

/-- **Every skeleton of a relative CW complex has the homotopy extension property inside the
complex.** -/
theorem hasHomotopyExtensionProperty_skeletonLT (k : ℕ) :
    HasHomotopyExtensionProperty (Subtype.val ⁻¹' (skeletonLT C k : Set X) : Set C) := by
  rw [hasHomotopyExtensionProperty_iff]
  intro Y _ f H hH
  refine ⟨⟨glued hH, ?_⟩, fun x ↦ ?_, fun t a ↦ glued_apply 0 t a.1 a.2⟩
  · rw [continuous_prod_complex_iff]
    refine ⟨fun m j ↦ ?_, ?_⟩
    · -- An `m`-cell lies in the `k + (m + 1)`-skeleton.
      have hmem (y : closedBall (0 : Fin m → ℝ) 1) :
          map m j y ∈ (skeletonLT C ((k + (m + 1) : ℕ) : ℕ∞) : Set X) :=
        skeletonLT_mono (by exact_mod_cast Nat.le_add_left (m + 1) k)
          (closedCell_subset_skeletonLT m j ⟨y, y.2, rfl⟩)
      exact ((extensionSeq k f H hH (m + 1)).1.continuous.comp (continuous_fst.prodMk
        (((continuous_map_closedBall j).comp continuous_snd).subtype_mk fun p ↦ hmem p.2))).congr
        fun p ↦ (glued_apply (m + 1) p.1 ⟨_, _⟩ (hmem p.2)).symm
    · have hmem (d : D) : (d : X) ∈ (skeletonLT C k : Set X) := (skeletonLT C k).base_subset d.2
      exact (H.continuous.comp (continuous_fst.prodMk
        (((continuous_subtype_val.comp continuous_snd).subtype_mk _).subtype_mk
          fun p ↦ hmem p.2))).congr fun p ↦ (glued_apply 0 p.1 ⟨_, _⟩ (hmem p.2)).symm
  · obtain ⟨j, hj⟩ := exists_mem_skeletonLT_add (k := k) x
    rw [ContinuousMap.coe_mk, glued_apply j 0 x hj]
    exact (extensionSeq k f H hH j).2 _

/-- **Relative CW inclusions are cofibrations: the base of a relative CW complex has the homotopy
extension property inside the complex.**  The base is also closed
(`TauCeti.HasHomotopyExtensionProperty.isClosed`), so the inclusion is a closed cofibration. -/
theorem hasHomotopyExtensionProperty_base :
    HasHomotopyExtensionProperty (Subtype.val ⁻¹' D : Set C) := by
  simpa only [Nat.cast_zero, skeletonLT_zero_eq_base] using
    hasHomotopyExtensionProperty_skeletonLT (C := C) 0

end TauCeti
