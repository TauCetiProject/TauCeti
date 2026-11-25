/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Subcomplex
public import TauCeti.Topology.CWComplex.Classical.Subcomplex
public import TauCeti.Topology.CWComplex.Classical.Skeleton.Induction
public import TauCeti.Topology.Homotopy.Extension.Ball
import TauCeti.Topology.Homotopy.Extension.Segment

/-!
# Relative CW inclusions are closed cofibrations

The base `D` of a relative CW complex `C` has the homotopy extension property inside `C`, and so
do every skeleton and every subcomplex of `C`.  As `X` is Hausdorff, these subsets are closed
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
* `Topology.RelCWComplex.Subcomplex.hasHomotopyExtensionProperty`: a subcomplex has the homotopy
  extension property inside the complex, since the complex is a CW complex relative to it.
* `TauCeti.hasHomotopyExtensionProperty_range_of_coe_map_eq`: the range of a map between CW
  complexes carrying every cell onto a cell, characteristic maps included, has the homotopy
  extension property, being a subcomplex.
* `TauCeti.hasHomotopyExtensionProperty_singleton`: **every point of a relative CW complex outside
  its base has the homotopy extension property inside the complex**, and
  `TauCeti.hasHomotopyExtensionProperty_singleton_of_cwComplex` states this for a CW structure on
  the whole space.
* `TauCeti.exists_retraction_cylinderExtensionDomain_base`: skeletal cylinder retraction onto
  `{0} × C ∪ I × D` preserving every closed-cell-saturated subset of `X` (in particular every
  subcomplex).

A point of an open cell of positive dimension is not a subcomplex, so the singleton result does not
follow from the subcomplex case. Its proof works in the skeleton containing the cell, where the
open cell is open and the inverse characteristic map is a chart onto the open unit ball: a point
of a chart has the homotopy extension property
(`OpenPartialHomeomorph.hasHomotopyExtensionProperty_symm_image_segment`, for a degenerate
segment), and the skeleton has it inside the complex. The detour through the skeleton is needed,
since cells of higher dimension attached along the cell make it fail to be open in the complex.

## Related results

`TauCeti.hasHomotopyExtensionProperty_sphere_closedBall` gives the homotopy extension property
for the boundary of a closed cell.  The homotopies are extended over the closed cells and glued
over the skeleta by `TauCeti.exists_continuousMap_prod_skeletonLT_succ` and
`TauCeti.exists_continuousMap_prod_complex_of_skeletonLT`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, Proposition 0.16: a CW pair has the homotopy extension property; and the Appendix,
  Proposition A.4, on the local contractibility of CW complexes.
* F. T. Farrell, L. R. Taylor, J. B. Wagoner, *The Whitehead theorem in the proper category*,
  Compositio Math. 27 (1973), 1–23, Theorem 1.6.
* D. H. Baues, A. Quintero, *Infinite Homotopy Theory*, Kluwer Academic Publishers (2001),
  Chapter I, Proposition 3.8.
-/

public section

noncomputable section

open Metric Set Topology Topology.RelCWComplex unitInterval

universe u

namespace TauCeti

variable {X : Type u} [TopologicalSpace X] [T2Space X] {C D : Set X} [RelCWComplex C D]

/-- **`skeletonLT C n` has the homotopy extension property inside `skeletonLT C (n + 1)`.** -/
theorem hasHomotopyExtensionProperty_skeletonLT_succ (n : ℕ) :
    HasHomotopyExtensionProperty (Subtype.val ⁻¹' (skeletonLT C n : Set X) :
      Set (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X)) := by
  rw [hasHomotopyExtensionProperty_iff]
  intro Y _ f G hG
  -- Extend `G` over every closed `n`-cell, by the homotopy extension property of the boundary
  -- sphere inside the closed ball.
  have hext : ∀ j : cell C n, ∃ K : C(I × closedBall (0 : Fin n → ℝ) 1, Y),
      (∀ y, K (0, y) = f ⟨map n j y, map_mem_skeletonLT_succ j
          (mem_closedBall_zero_iff.1 y.property)⟩) ∧
      ∀ t (y : closedBall (0 : Fin n → ℝ) 1) (hy : (y : Fin n → ℝ) ∈ sphere 0 1),
        K (t, y) = G (t, ⟨⟨map n j y, map_mem_skeletonLT_succ j
            (mem_closedBall_zero_iff.1 y.property)⟩,
          cellFrontier_subset_skeletonLT n j ⟨y, hy, rfl⟩⟩) := by
    intro j
    obtain ⟨K, hK0, hKs⟩ :=
      (hasHomotopyExtensionProperty_sphere_closedBall (E := Fin n → ℝ)).exists_extension_of_isClosed
        (isClosed_sphere.preimage continuous_subtypeVal)
        (f.comp ⟨fun y ↦ ⟨map n j y, map_mem_skeletonLT_succ j
            (mem_closedBall_zero_iff.1 y.property)⟩,
          (continuous_map_closedBall j).subtype_mk _⟩)
        (G.comp ⟨fun p ↦ (p.1, ⟨⟨map n j p.2,
          map_mem_skeletonLT_succ j (mem_closedBall_zero_iff.1 p.2.val.property)⟩,
          cellFrontier_subset_skeletonLT n j ⟨p.2, p.2.property, rfl⟩⟩),
          continuous_fst.prodMk ((((continuous_map_closedBall j).comp
            (continuous_subtypeVal.comp continuous_snd)).subtype_mk _).subtype_mk _)⟩)
        fun a ↦ hG _
    exact ⟨K, hK0, fun t y hy ↦ hKs t ⟨y, hy⟩⟩
  choose K hK0 hKs using hext
  -- Glue `G` and the extensions `K j` over the closed `n`-cells.
  obtain ⟨F, hFG, hFK⟩ := exists_continuousMap_prod_skeletonLT_succ
    (G.comp ⟨fun p : I × (skeletonLT C n : Set X) ↦
      (p.1, ⟨⟨(p.2 : X), skeletonLT_mono
          (by exact_mod_cast n.le_succ) p.2.property⟩, p.2.property⟩),
      by fun_prop⟩) K hKs
  refine ⟨F, fun x ↦ ?_, fun t a ↦ hFG t a.val a.property⟩
  obtain hx | ⟨j, y, hy, hxy⟩ := mem_skeletonLT_or_exists_map x.property
  · rw [hFG 0 x hx]
    exact hG ⟨x, hx⟩
  · obtain rfl : x = ⟨map n j y, map_mem_skeletonLT_succ j hy.le⟩ := Subtype.ext hxy.symm
    exact (hFK j 0 ⟨y, mem_closedBall_zero_iff.2 hy.le⟩).trans (hK0 j _)

section Glue

variable {Y : Type u} [TopologicalSpace Y] {k : ℕ} {f : C(C, Y)}
  {H : C(I × (Subtype.val ⁻¹' (skeletonLT C k : Set X) : Set C), Y)}

variable (k f H) in
/-- The solutions of the homotopy extension problem `(f, H)` on the successive skeleta
`skeletonLT C (k + j)`, each obtained from the previous one by
`TauCeti.hasHomotopyExtensionProperty_skeletonLT_succ`. -/
private def extensionSeq (hH : ∀ a, H (0, a) = f a) : (j : ℕ) →
    {G : C(I × (skeletonLT C ((k + j : ℕ) : ℕ∞) : Set X), Y) //
      ∀ x, G (0, x) = f ⟨x, (skeletonLT C _).subset_complex x.property⟩}
  | 0 => ⟨H.comp ⟨fun p ↦ (p.1, ⟨⟨p.2, (skeletonLT C _).subset_complex p.2.property⟩,
      p.2.property⟩),
      by fun_prop⟩, fun x ↦ hH _⟩
  | j + 1 =>
    have h := (hasHomotopyExtensionProperty_skeletonLT_succ (C := C) (k + j)).exists_extension
      (f.comp ⟨fun x ↦ ⟨x, (skeletonLT C _).subset_complex x.property⟩, by fun_prop⟩)
      ((extensionSeq hH j).val.comp ⟨fun p ↦ (p.1, ⟨p.2, p.2.property⟩), by fun_prop⟩)
      fun a ↦ (extensionSeq hH j).property _
    ⟨h.choose, h.choose_spec.1⟩

private lemma extensionSeq_succ_apply {hH : ∀ a, H (0, a) = f a} (j : ℕ) (t : I)
    (x : X) (hx : x ∈ (skeletonLT C ((k + j : ℕ) : ℕ∞) : Set X)) :
    (extensionSeq k f H hH (j + 1)).val
        (t, ⟨x, skeletonLT_mono (by exact_mod_cast (k + j).le_succ) hx⟩) =
      (extensionSeq k f H hH j).val (t, ⟨x, hx⟩) := by
  rw [extensionSeq]
  exact ((hasHomotopyExtensionProperty_skeletonLT_succ (C := C) (k + j)).exists_extension _ _
    fun a ↦ (extensionSeq k f H hH j).property _).choose_spec.2 t ⟨_, hx⟩

end Glue

/-- **Every skeleton of a relative CW complex has the homotopy extension property inside the
complex.** -/
theorem hasHomotopyExtensionProperty_skeletonLT (k : ℕ) :
    HasHomotopyExtensionProperty (Subtype.val ⁻¹' (skeletonLT C k : Set X) : Set C) := by
  rw [hasHomotopyExtensionProperty_iff]
  intro Y _ f H hH
  -- Solve the problem on the successive skeleta and glue the solutions.
  obtain ⟨G, hG⟩ := exists_continuousMap_prod_complex_of_skeletonLT
    (fun j ↦ (extensionSeq k f H hH j).val) (extensionSeq_succ_apply (hH := hH))
  refine ⟨G, fun x ↦ ?_, fun t a ↦ hG 0 t a.val a.property⟩
  obtain ⟨j, hj⟩ := exists_mem_skeletonLT_add k x.property
  exact (hG j 0 x hj).trans ((extensionSeq k f H hH j).property _)

/-- **Relative CW inclusions are cofibrations: the base of a relative CW complex has the homotopy
extension property inside the complex.**  The base is also closed
(`TauCeti.HasHomotopyExtensionProperty.isClosed`), so the inclusion is a closed cofibration. -/
theorem hasHomotopyExtensionProperty_base :
    HasHomotopyExtensionProperty (Subtype.val ⁻¹' D : Set C) := by
  simpa only [Nat.cast_zero, skeletonLT_zero_eq_base] using
    hasHomotopyExtensionProperty_skeletonLT (C := C) 0

/-- **CW pairs are cofibrations: a subcomplex has the homotopy extension property inside the
complex.** The complex is a CW complex relative to the subcomplex
(`Topology.RelCWComplex.Subcomplex.relCWComplex`), whose base has the homotopy extension property.
-/
theorem _root_.Topology.RelCWComplex.Subcomplex.hasHomotopyExtensionProperty
    (E : Subcomplex C) : HasHomotopyExtensionProperty (Subtype.val ⁻¹' (E : Set X) : Set C) :=
  @hasHomotopyExtensionProperty_base X _ _ C E E.relCWComplex

/-- **The range of a map carrying cells onto cells has the homotopy extension property.** Let `W`
and `Y` carry CW structures on `univ`, and let `g : W → Y` carry every `n`-cell `i` of `W` onto an
`n`-cell `ι n i` of `Y`, in the sense that `map n (ι n i) = g ∘ map n i`. Then the range of `g`
is the subcomplex of `Y` made of these cells, so it has the homotopy extension property. -/
theorem hasHomotopyExtensionProperty_range_of_coe_map_eq {W Y : Type*} [TopologicalSpace W]
    [CWComplex (univ : Set W)] [TopologicalSpace Y] [T2Space Y] [CWComplex (univ : Set Y)]
    {g : W → Y} (ι : ∀ n, cell (univ : Set W) n → cell (univ : Set Y) n)
    (hι : ∀ n i, ⇑(map n (ι n i)) = g ∘ map n i) :
    HasHomotopyExtensionProperty (range g) := by
  have himage (n : ℕ) (i : cell (univ : Set W) n) (s : Set (Fin n → ℝ)) :
      map n (ι n i) '' s = g '' (map n i '' s) := by
    rw [hι, image_comp]
  -- The range of `g` is the subcomplex of `Y` whose cells are those in the range of `ι`.
  let E : Subcomplex (univ : Set Y) :=
    CWComplex.Subcomplex.mk' _ (range g) (fun n ↦ range (ι n))
    (fun n j ↦ by
      obtain ⟨_, i, rfl⟩ := j
      rw [closedCell, himage]
      exact image_subset_range _ _)
    (by
      refine Subset.antisymm (iUnion₂_subset fun n j ↦ ?_) ?_
      · obtain ⟨_, i, rfl⟩ := j
        rw [openCell, himage]
        exact image_subset_range _ _
      · rintro _ ⟨w, rfl⟩
        obtain ⟨n, i, hw⟩ := mem_iUnion₂.1 <|
          (CWComplex.iUnion_openCell_eq_complex (C := (univ : Set W))).symm ▸ mem_univ w
        refine mem_iUnion₂.2 ⟨n, ⟨ι n i, i, rfl⟩, ?_⟩
        rw [openCell, himage]
        exact mem_image_of_mem g hw)
  have h := E.hasHomotopyExtensionProperty.image (Homeomorph.Set.univ Y)
  rwa [Homeomorph.Set.univ_apply, image_preimage_eq_range_inter, Subtype.range_coe, univ_inter]
    at h

/-- **A point of a relative CW complex outside its base has the homotopy extension property
inside the complex.** -/
theorem hasHomotopyExtensionProperty_singleton {x : C} (hx : (x : X) ∉ D) :
    HasHomotopyExtensionProperty ({x} : Set C) := by
  obtain ⟨n, i, hxi⟩ : ∃ n, ∃ i : cell C n, (x : X) ∈ openCell n i := by
    have hmem : (x : X) ∈ D ∪ ⋃ (n : ℕ) (j : cell C n), openCell n j :=
      (union_iUnion_openCell_eq_complex (C := C)).symm.subset x.property
    simpa [hx] using hmem
  have hS : (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X) ⊆ C := (skeletonLT C _).subset_complex
  -- The point of the `n`-skeleton lying over `x`, in the source of the chart of the cell `i`.
  let x' : (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X) :=
    ⟨x, openCell_subset_skeletonLT n i hxi⟩
  have hx' : x' ∈ (openCellChart n i).source := by
    rw [openCellChart_source]
    exact hxi
  have h := (openCellChart n i).hasHomotopyExtensionProperty_symm_image_segment
    (x := openCellChart n i x') (y := openCellChart n i x')
    (by rw [segment_same, singleton_subset_iff]; exact (openCellChart n i).map_source hx')
  rw [segment_same, image_singleton, (openCellChart n i).left_inv hx'] at h
  have h' := h.image_of_isEmbedding (IsEmbedding.inclusion hS)
    (by rw [range_inclusion]; exact hasHomotopyExtensionProperty_skeletonLT (n + 1))
  rwa [image_singleton] at h'

/-- **A point of a Hausdorff CW complex has the homotopy extension property**, for a CW structure
on the whole space. -/
theorem hasHomotopyExtensionProperty_singleton_of_cwComplex {Y : Type*} [TopologicalSpace Y]
    [T2Space Y] [CWComplex (univ : Set Y)] (y : Y) :
    HasHomotopyExtensionProperty ({y} : Set Y) := by
  have h := (hasHomotopyExtensionProperty_singleton (C := (univ : Set Y))
    (x := ⟨y, mem_univ y⟩) (notMem_empty y)).image (Homeomorph.Set.univ Y)
  rwa [image_singleton, Homeomorph.Set.univ_apply] at h

section RelativeRetraction

/-- Single skeletal step of the cylinder retraction: given `G` on `I × skeletonLT C n` fixing time
`0` and landing in `cylinderExtensionDomain (Subtype.val ⁻¹' D)`, extend `G` over
`I × skeletonLT C (n + 1)` so that every `n`-cell-saturated subset preserved by `G` remains
preserved. -/
private theorem exists_retraction_step (n : ℕ)
    (G : C(I × (skeletonLT C n : Set X), I × C))
    (hG₀ : ∀ x, G (0, x) = (0, ⟨x, (skeletonLT C n).subset_complex x.property⟩))
    (hG_dom : ∀ p, G p ∈ cylinderExtensionDomain (Subtype.val ⁻¹' D : Set C)) :
    ∃ F : C(I × (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X), I × C),
      (∀ t (x : X) (hx : x ∈ (skeletonLT C n : Set X)),
        F (t, ⟨x, skeletonLT_mono (by exact_mod_cast n.le_succ) hx⟩) = G (t, ⟨x, hx⟩)) ∧
      (∀ x, F (0, x) = (0, ⟨x, (skeletonLT C ((n + 1 : ℕ) : ℕ∞)).subset_complex x.property⟩)) ∧
      (∀ p, F p ∈ cylinderExtensionDomain (Subtype.val ⁻¹' D : Set C)) ∧
      ∀ {S : Set X},
        (∀ j : cell C n, (openCell n j ∩ S).Nonempty → closedCell n j ⊆ S) →
        (∀ t (x : (skeletonLT C n : Set X)), (x : X) ∈ S → ((G (t, x)).2 : X) ∈ S) →
        ∀ t (x : (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X)),
          (x : X) ∈ S → ((F (t, x)).2 : X) ∈ S := by
  let fCell (j : cell C n) : C(closedBall (0 : Fin n → ℝ) 1, I × C) :=
    ⟨fun y ↦ (0, ⟨map n j y, closedCell_subset_complex n j ⟨y, y.property, rfl⟩⟩),
      continuous_const.prodMk ((continuous_map_closedBall j).subtype_mk _)⟩
  let HCell (j : cell C n) :
      C(I × (Subtype.val ⁻¹' sphere (0 : Fin n → ℝ) 1 : Set (closedBall (0 : Fin n → ℝ) 1)),
        I × C) :=
    G.comp ⟨fun q ↦
        (q.1, ⟨map n j q.2.val, cellFrontier_subset_skeletonLT n j ⟨q.2.val, q.2.property, rfl⟩⟩),
      continuous_fst.prodMk
        (((continuous_map_closedBall j).comp
          (continuous_subtypeVal.comp continuous_snd)).subtype_mk _)⟩
  -- Extend cell-by-cell with target `range (fCell j) ∪ range (HCell j)` so each `n`-cell stays
  -- inside its closed cell together with the `G`-image of its frontier.
  have hext (j : cell C n) : ∃ K : C(I × closedBall (0 : Fin n → ℝ) 1, I × C),
      (∀ y, K (0, y) = fCell j y) ∧
      (∀ t (y : closedBall (0 : Fin n → ℝ) 1) (hy : (y : Fin n → ℝ) ∈ sphere 0 1),
        K (t, y) = G (t, ⟨map n j y, cellFrontier_subset_skeletonLT n j ⟨y, hy, rfl⟩⟩)) ∧
      ∀ p, K p ∈ range (fCell j) ∪ range (HCell j) := by
    obtain ⟨K', hK'₀, hK's⟩ := (hasHomotopyExtensionProperty_sphere_closedBall
      (E := Fin n → ℝ)).exists_extension_of_isClosed
      (isClosed_sphere.preimage continuous_subtypeVal) (Y := ↥(range (fCell j) ∪ range (HCell j)))
      ⟨fun w ↦ ⟨fCell j w, .inl (mem_range_self w)⟩, by fun_prop⟩
      ⟨fun q ↦ ⟨HCell j q, .inr (mem_range_self q)⟩, by fun_prop⟩ fun _ ↦ Subtype.ext (hG₀ _)
    exact ⟨⟨fun p ↦ (K' p).val, continuous_subtypeVal.comp K'.continuous⟩,
      fun y ↦ congrArg Subtype.val (hK'₀ y), fun t y hy ↦ congrArg Subtype.val (hK's t ⟨y, hy⟩),
      fun p ↦ (K' p).property⟩
  choose K hK₀ hKs hKr using hext
  obtain ⟨F, hFG, hFK⟩ := exists_continuousMap_prod_skeletonLT_succ G K hKs
  refine ⟨F, hFG, fun x ↦ ?_, fun ⟨t, x⟩ ↦ ?_, fun {S} hSn hGS t x hxS ↦ ?_⟩
  · obtain hx | ⟨j, y, hy, hxy⟩ := mem_skeletonLT_or_exists_map x.property
    · exact (hFG 0 x hx).trans (hG₀ ⟨x, hx⟩)
    · obtain rfl : x = ⟨map n j y, map_mem_skeletonLT_succ j hy.le⟩ := Subtype.ext hxy.symm
      exact (hFK j 0 ⟨y, mem_closedBall_zero_iff.2 hy.le⟩).trans (hK₀ j _)
  · obtain hx | ⟨j, y, hy, hxy⟩ := mem_skeletonLT_or_exists_map x.property
    · exact hFG t x hx ▸ hG_dom _
    · obtain rfl : x = ⟨map n j y, map_mem_skeletonLT_succ j hy.le⟩ := Subtype.ext hxy.symm
      rw [hFK j t ⟨y, mem_closedBall_zero_iff.2 hy.le⟩]
      exact (hKr j _).elim (fun ⟨_, hw⟩ ↦ hw ▸ zero_mem_cylinderExtensionDomain _)
        fun ⟨_, hq⟩ ↦ hq ▸ hG_dom _
  · obtain hx | ⟨j, y, hy, hxy⟩ := mem_skeletonLT_or_exists_map x.property
    · exact hFG t x hx ▸ hGS t ⟨x, hx⟩ hxS
    · have hclosedS : closedCell n j ⊆ S := hSn j ⟨x, ⟨y, mem_ball_zero_iff.2 hy, hxy⟩, hxS⟩
      obtain rfl : x = ⟨map n j y, map_mem_skeletonLT_succ j hy.le⟩ := Subtype.ext hxy.symm
      rw [hFK j t ⟨y, mem_closedBall_zero_iff.2 hy.le⟩]
      exact (hKr j _).elim (fun ⟨w, hw⟩ ↦ hw ▸ hclosedS ⟨w, w.property, rfl⟩) fun ⟨q, hq⟩ ↦
        hq ▸ hGS q.1 _ (hclosedS (cellFrontier_subset_closedCell n j ⟨q.2.val, q.2.property, rfl⟩))

/-- Recursive sequence of skeletal cylinder retractions on `I × skeletonLT C (0 + j)`. -/
private def retractionSeq : (j : ℕ) →
    {G : C(I × (skeletonLT C ((0 + j : ℕ) : ℕ∞) : Set X), I × C) //
      (∀ x, G (0, x) = (0, ⟨x, (skeletonLT C _).subset_complex x.property⟩)) ∧
      ∀ p, G p ∈ cylinderExtensionDomain (Subtype.val ⁻¹' D : Set C)}
  | 0 =>
    ⟨⟨fun p ↦ (p.1, ⟨p.2, (skeletonLT C _).subset_complex p.2.property⟩),
        continuous_fst.prodMk (continuous_subtypeVal.comp continuous_snd |>.subtype_mk _)⟩,
      fun _ ↦ rfl,
      fun p ↦ mem_cylinderExtensionDomain_of_mem <| by
        have hx : (p.2 : X) ∈ (skeletonLT C (0 : ℕ∞) : Set X) := p.2.property
        rwa [skeletonLT_zero_eq_base] at hx⟩
  | j + 1 =>
    let prev := retractionSeq j
    let step := exists_retraction_step (0 + j) prev.val prev.property.1 prev.property.2
    ⟨step.choose, step.choose_spec.2.1, step.choose_spec.2.2.1⟩

private lemma retractionSeq_succ_apply (j : ℕ) (t : I) (x : X)
    (hx : x ∈ (skeletonLT C ((0 + j : ℕ) : ℕ∞) : Set X)) :
    (retractionSeq (C := C) (j + 1)).val
        (t, ⟨x, skeletonLT_mono (by exact_mod_cast (0 + j).le_succ) hx⟩) =
      (retractionSeq (C := C) j).val (t, ⟨x, hx⟩) := by
  rw [retractionSeq]
  exact (exists_retraction_step (0 + j) (retractionSeq j).val (retractionSeq j).property.1
    (retractionSeq j).property.2).choose_spec.1 t x hx

private lemma retractionSeq_preserves {S : Set X}
    (hS : ∀ (n : ℕ) (i : cell C n), (openCell n i ∩ S).Nonempty → closedCell n i ⊆ S) :
    ∀ (j : ℕ) (t : I) (x : (skeletonLT C ((0 + j : ℕ) : ℕ∞) : Set X)),
      (x : X) ∈ S → (((retractionSeq (C := C) j).val (t, x)).2 : X) ∈ S
  | 0, _, _, hxS => hxS
  | j + 1, t, x, hxS => by
    rw [retractionSeq]
    exact (exists_retraction_step (0 + j) (retractionSeq j).val (retractionSeq j).property.1
      (retractionSeq j).property.2).choose_spec.2.2.2 (hS (0 + j)) (retractionSeq_preserves hS j)
      t x hxS

/-- **Skeletal cylinder retraction preserving cell-saturated subsets.** For any Hausdorff relative
CW complex `(C, D)`, there is a continuous retraction `r : I × C → I × C` onto
`{0} × C ∪ I × (Subtype.val ⁻¹' D)` such that `r` preserves every subset `S ⊆ X` which contains
`closedCell n i` whenever it meets `openCell n i`. -/
theorem exists_retraction_cylinderExtensionDomain_base :
    ∃ r : C(I × C, I × C),
      (∀ p, r p ∈ cylinderExtensionDomain (Subtype.val ⁻¹' D : Set C)) ∧
      (∀ p ∈ cylinderExtensionDomain (Subtype.val ⁻¹' D : Set C), r p = p) ∧
      ∀ {S : Set X},
        (∀ (n : ℕ) (i : cell C n), (openCell n i ∩ S).Nonempty → closedCell n i ⊆ S) →
        ∀ (t : I) (x : C), (x : X) ∈ S → ((r (t, x)).2 : X) ∈ S := by
  obtain ⟨r, hr_apply⟩ := exists_continuousMap_prod_complex_of_skeletonLT
    (fun j ↦ (retractionSeq (C := C) j).val) retractionSeq_succ_apply
  refine ⟨r, fun ⟨t, x⟩ ↦ ?_, fun ⟨t, x⟩ hp ↦ ?_, fun {S} hS t x hxS ↦ ?_⟩
  · obtain ⟨j, hj⟩ := exists_mem_skeletonLT_add 0 x.property
    exact hr_apply j t x hj ▸ (retractionSeq (C := C) j).property.2 (t, ⟨x, hj⟩)
  · rcases mem_cylinderExtensionDomain_iff.1 hp with rfl | hxD
    · obtain ⟨j, hj⟩ := exists_mem_skeletonLT_add 0 x.property
      exact (hr_apply j 0 x hj).trans ((retractionSeq (C := C) j).property.1 ⟨x, hj⟩)
    · exact hr_apply 0 t x ((skeletonLT C ((0 + 0 : ℕ) : ℕ∞)).base_subset hxD)
  · obtain ⟨j, hj⟩ := exists_mem_skeletonLT_add 0 x.property
    exact hr_apply j t x hj ▸ retractionSeq_preserves hS j t ⟨x, hj⟩ hxS

end RelativeRetraction

end TauCeti
