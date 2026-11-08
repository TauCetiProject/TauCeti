/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Equiv
public import TauCeti.Topology.CWComplex.Classical.Disk
public import TauCeti.Topology.CWComplex.Classical.Image
public import TauCeti.Topology.CWComplex.Classical.Trans
import TauCeti.AlgebraicTopology.Disk
import TauCeti.Topology.CWComplex.Classical.CellularApproximation
import TauCeti.Topology.CWComplex.Classical.Sphere.Basic
import TauCeti.Topology.Homotopy.Extension.Pushout

/-!
# CW models of cell attachments

Let `W` be a CW complex and let `b i : ∂Dⁿⁱ → W` be a family of maps of the boundary spheres of
disks into `W`. If each `b i` lands in the skeleton `skeletonLT W (n i)`, the union of the cells of
`W` of dimension less than `n i`, then the space `W ∪_b ⨆ᵢ Dⁿⁱ` obtained by attaching the disks
along the `b i` is again a CW complex (`TauCeti.sigmaDiskAdjunctionCWComplex`). Its `m`-cells are
the `m`-cells of `W` together with the indices `i` with `n i = m`
(`TauCeti.sigmaDiskAdjunctionCWComplexCellEquiv`). The cells of `W` keep their characteristic
maps, followed by the closed embedding of `W` into the adjunction space
(`TauCeti.sigmaDiskAdjunctionCWComplex_map_inl`), and the new cells have the characteristic maps
of the disks (`TauCeti.sigmaDiskAdjunctionCWComplex_map_inr`). The image of `W` is a subcomplex,
made of the cells of `W` (`TauCeti.sigmaDiskAdjunctionSubcomplex`).

Every map of a sphere into a CW complex can be moved into the required skeleton by a homotopy
(`ContinuousMap.exists_homotopic_mapsTo_skeletonLT_diskBoundary`), by cellular approximation for
the CW structure of the sphere with one `0`-cell and one top cell. Since attaching along homotopic
maps, or to homotopy equivalent spaces, does not change the homotopy type, this gives CW models of
cell attachments: if `h : W ≃ₕ Z` is a homotopy equivalence from a CW complex to a space `Z`, and
`a i : ∂Dⁿⁱ → Z` are attaching maps, then there are attaching maps `b i` into the skeleta of `W`,
with `h ∘ b i` homotopic to `a i`, and a homotopy equivalence `W ∪_b ⨆ᵢ Dⁿⁱ ≃ₕ Z ∪_a ⨆ᵢ Dⁿⁱ`
which is `h` on `W` (`ContinuousMap.HomotopyEquiv.exists_homotopyEquiv_sigmaDiskAdjunction`). So
the attachment `Z ∪_a ⨆ᵢ Dⁿⁱ` has a CW model whose cells are the cells of the given model of `Z`,
with their characteristic maps, and one new `n i`-cell for each `i`. Iterating this is how a space
built by successive cell attachments, such as the sublevels of a Morse function across their
critical levels, receives a CW model.

The CW structure is the composite (`TauCeti.relCWComplexTrans`) of the relative CW structure of the
attachment over `W` (`TauCeti.relativeCWPushout`) with the CW structure of `W`, carried to the
adjunction space along the closed embedding of `W`. The boundary of the cell of the `i`-th disk is
the image of `b i`, which lies in `skeletonLT W (n i)`: this is the compatibility condition of the
composite. The homotopy equivalence composes the change of base along `h`
(`CategoryTheory.IsPushout.exists_homotopic_id_of_homotopic_id`) with the reattachment along a
homotopy `h ∘ b ≃ a` (`CategoryTheory.IsPushout.exists_homotopicRel_id_of_homotopy`).

## Main definitions

* `TauCeti.sigmaDiskAdjunctionCWComplex`: the CW structure on `W ∪_b ⨆ᵢ Dⁿⁱ`.
* `TauCeti.sigmaDiskAdjunctionCWComplexCellEquiv`: its `m`-cells are those of `W` and the indices
  `i` with `n i = m`.
* `TauCeti.sigmaDiskAdjunctionSubcomplex`: `W` as a subcomplex of `W ∪_b ⨆ᵢ Dⁿⁱ`.

## Main results

* `ContinuousMap.exists_homotopic_mapsTo_skeletonLT_diskBoundary`: a map of `∂Dᵐ` into a CW
  complex is homotopic to a map into `skeletonLT W m`.
* `ContinuousMap.HomotopyEquiv.exists_homotopyEquiv_sigmaDiskAdjunction`: **CW models of cell
  attachments.**

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, Proposition 0.18, and Section 4.1, Theorem 4.8 (cellular approximation).
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Lemmas 3.6 and 3.7 and the proof of Theorem 3.5, where cells attached to a space are moved by
  cellular approximation onto a CW model.
-/

public section

noncomputable section

universe u

open CategoryTheory Limits Metric Set Topology Topology.RelCWComplex
open scoped ContinuousMap

namespace TauCeti

variable {W : Type u} [TopologicalSpace W] [T2Space W] [CWComplex (univ : Set W)]

/-- **Cellular approximation of a map of a sphere.** Every map of the boundary sphere `∂Dᵐ` of the
`m`-disk into a CW complex `W` is homotopic to a map into the skeleton `skeletonLT W m`, the union
of the cells of `W` of dimension less than `m`. -/
theorem _root_.ContinuousMap.exists_homotopic_mapsTo_skeletonLT_diskBoundary {m : ℕ}
    (f : C(TopCat.diskBoundary.{u} m, W)) :
    ∃ g : C(TopCat.diskBoundary.{u} m, W), f.Homotopic g ∧
      ∀ x, g x ∈ (skeletonLT (univ : Set W) m : Set W) := by
  obtain _ | k := m
  · -- The boundary of the `0`-disk is empty.
    exact ⟨f, .refl f, isEmptyElim⟩
  -- Cellular approximation for the CW structure on `Sᵏ` with one `0`-cell and one `k`-cell,
  -- indexed by `ULift (Fin (k + 1))` so that the sphere lives in the universe of `W`.
  let ι := ULift.{u} (Fin (k + 1))
  have hι : Fintype.card ι = k + 1 := by simp [ι]
  let _ := sphereCWComplex hι
  let S := sphere (0 : EuclideanSpace ℝ ι) 1
  let E := diskBoundaryHomeomorph.{u} (k + 1)
  let down : C(TopCat.diskBoundary.{u} (k + 1), S) := E
  let val : C((univ : Set W), W) := ⟨Subtype.val, continuous_subtype_val⟩
  let φ : C(S, (univ : Set W)) := ⟨fun y ↦ ⟨f (E.symm y), mem_univ _⟩, by fun_prop⟩
  have hf : f = val.comp (φ.comp down) := by
    ext x
    simp [val, φ, down]
  obtain ⟨g, hg, hφg⟩ := exists_isCellular_homotopic (TopCat.ofHom φ)
  refine ⟨val.comp (g.hom.comp down), hf ▸ (ContinuousMap.Homotopic.refl val).comp
    (hφg.comp (ContinuousMap.Homotopic.refl down)), fun x ↦ hg (k + 1) ?_⟩
  -- Every point of `Sᵏ` lies in an open cell of dimension at most `k`.
  obtain ⟨l, -, j, hj⟩ := CWComplex.mem_skeletonLT_iff.1
    (by rw [← SetLike.mem_coe, skeletonLT_top]; exact (down x).2 :
      (down x : EuclideanSpace ℝ ι) ∈ skeletonLT S ⊤)
  have hl : l < k + 1 := by
    by_contra! hl
    exact (isEmpty_cell_sphereCWComplex hι hl).elim j
  exact CWComplex.mem_skeletonLT_iff.2 ⟨l, by exact_mod_cast hl, j, hj⟩

variable {ι : Type u} {n : ι → ℕ}

variable (b : ∀ i, C(TopCat.diskBoundary.{u} (n i), W))

/-- The CW structure of `W`, carried to its image in the adjunction space `W ∪_b ⨆ᵢ Dⁿⁱ`. -/
private abbrev sigmaDiskAdjunctionBaseCWComplex :
    letI := sigmaDiskRelCWComplex n
    RelCWComplex (range (pushout.inr (relCWBaseInclusion
      (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))))
        (TopCat.ofHom (sigmaDiskAttachingMap b)))) ∅ :=
  letI := sigmaDiskRelCWComplex n
  (isClosedEmbedding_pushout_inr_relCWBaseInclusion (sigmaDiskAttachingMap b)).relCWComplex
    (C := univ) (D := ∅) image_univ (image_empty _)

/-- The boundary of each `m`-cell of the attachment lies in the image of `skeletonLT W m`. -/
private theorem cellFrontier_relativeCWPushout_subset
    (hb : ∀ i x, b i x ∈ (skeletonLT (univ : Set W) (n i) : Set W)) (m : ℕ)
    (j : letI := sigmaDiskRelCWComplex n
      letI := relativeCWPushout (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i))))
        (sigmaDiskAttachingMap b)
      cell (univ : Set (relCWAdjunctionSpace
        (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))) (sigmaDiskAttachingMap b))) m) :
    letI := sigmaDiskRelCWComplex n
    letI := relativeCWPushout (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i))))
      (sigmaDiskAttachingMap b)
    cellFrontier m j ⊆ pushout.inr (relCWBaseInclusion
      (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))))
        (TopCat.ofHom (sigmaDiskAttachingMap b)) '' (skeletonLT (univ : Set W) m : Set W) := by
  let := sigmaDiskRelCWComplex n
  let := relativeCWPushout (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i))))
    (sigmaDiskAttachingMap b)
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨⟨i, z⟩, rfl, hs⟩ := exists_map_sigmaDiskRelCWComplex_eq
    (relativeCWPushoutCellEquiv _ (sigmaDiskAttachingMap b) _ j) hx
  -- The point of the base over `⟨i, z⟩` is glued to `b i z`.
  have hmap := relativeCWPushout_map_apply (sigmaDiskAttachingMap b) _ j
    ⟨x, sphere_subset_closedBall hx⟩
  have hcond := ConcreteCategory.congr_hom (pushout.condition (f := relCWBaseInclusion
    (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))))
      (g := TopCat.ofHom (sigmaDiskAttachingMap b))) ((sigmaDiskBoundaryHomeomorph n).symm ⟨i, z⟩)
  simp only [ConcreteCategory.comp_apply, TopCat.hom_ofHom, sigmaDiskAttachingMap_apply] at hcond
  refine ⟨b i z, hb i z, hcond.symm.trans ((congrArg _ (Subtype.ext ?_)).trans hmap.symm)⟩
  exact (coe_sigmaDiskBoundaryHomeomorph_symm_apply n ⟨i, z⟩).trans hs.symm

/-- The compatibility condition for composing the relative CW structure of the attachment over
`W` with the CW structure of `W`: the part in `W` of the boundary of an `m`-cell of the attachment
lies in the skeleton `skeletonLT m` of `W`. -/
private theorem cellFrontier_inter_subset_skeletonLT
    (hb : ∀ i x, b i x ∈ (skeletonLT (univ : Set W) (n i) : Set W)) :
    letI := sigmaDiskRelCWComplex n
    letI := relativeCWPushout (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i))))
      (sigmaDiskAttachingMap b)
    letI := sigmaDiskAdjunctionBaseCWComplex b
    ∀ m (j : cell (univ : Set (relCWAdjunctionSpace
        (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))) (sigmaDiskAttachingMap b))) m),
      cellFrontier m j ∩ range (pushout.inr (relCWBaseInclusion
        (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))))
          (TopCat.ofHom (sigmaDiskAttachingMap b))) ⊆
        skeletonLT (range (pushout.inr (relCWBaseInclusion
          (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))))
            (TopCat.ofHom (sigmaDiskAttachingMap b)))) m := by
  let := sigmaDiskRelCWComplex n
  let := relativeCWPushout (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i))))
    (sigmaDiskAttachingMap b)
  let := sigmaDiskAdjunctionBaseCWComplex b
  -- The image of `skeletonLT W m` lies in the skeleton `skeletonLT m` of the image of `W`.
  rintro m j _ ⟨hx, -⟩
  obtain ⟨w, hw, rfl⟩ := cellFrontier_relativeCWPushout_subset b hb m j hx
  obtain ⟨l, hl, k, hk⟩ := CWComplex.mem_skeletonLT_iff.1 hw
  have hf := isClosedEmbedding_pushout_inr_relCWBaseInclusion
    (C := univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))) (sigmaDiskAttachingMap b)
  refine RelCWComplex.mem_skeletonLT_iff.2
    (.inr ⟨l, hl, ((hf.relCWComplexCellEquiv image_univ (image_empty _)) l).symm k, ?_⟩)
  rw [hf.openCell_relCWComplex, Equiv.apply_symm_apply]
  exact mem_image_of_mem _ hk

variable (n)

/-- **Attaching cells to a CW complex along maps into skeleta.** Let `W` be a CW complex and let
`b i : ∂Dⁿⁱ → W` be maps into the skeleta `skeletonLT W (n i)`. The space `W ∪_b ⨆ᵢ Dⁿⁱ` obtained by
attaching the disks `Dⁿⁱ` to `W` along the `b i` is a CW complex. Its `m`-cells are the `m`-cells
of `W` and the indices `i` with `n i = m` (`TauCeti.sigmaDiskAdjunctionCWComplexCellEquiv`). -/
@[instance_reducible]
def sigmaDiskAdjunctionCWComplex (hb : ∀ i x, b i x ∈ (skeletonLT (univ : Set W) (n i) : Set W)) :
    letI := sigmaDiskRelCWComplex n
    CWComplex (univ : Set (relCWAdjunctionSpace
      (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))) (sigmaDiskAttachingMap b))) :=
  letI := sigmaDiskRelCWComplex n
  letI := relativeCWPushout (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i))))
    (sigmaDiskAttachingMap b)
  letI := sigmaDiskAdjunctionBaseCWComplex b
  @RelCWComplex.toCWComplex _ _ _
    (relCWComplexTrans _ _ ∅ (cellFrontier_inter_subset_skeletonLT b hb))

variable (hb : ∀ i x, b i x ∈ (skeletonLT (univ : Set W) (n i) : Set W))

/-- The `m`-cells of `W ∪_b ⨆ᵢ Dⁿⁱ` are the `m`-cells of `W` together with the indices `i` with
`n i = m`. -/
def sigmaDiskAdjunctionCWComplexCellEquiv (m : ℕ) :
    letI := sigmaDiskRelCWComplex n
    letI := sigmaDiskAdjunctionCWComplex n b hb
    cell (univ : Set (relCWAdjunctionSpace
      (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))) (sigmaDiskAttachingMap b))) m ≃
        cell (univ : Set W) m ⊕ {i // n i = m} :=
  letI := sigmaDiskRelCWComplex n
  letI := relativeCWPushout (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i))))
    (sigmaDiskAttachingMap b)
  letI := sigmaDiskAdjunctionBaseCWComplex b
  (relCWComplexTransCellEquiv (cellFrontier_inter_subset_skeletonLT b hb) m).trans
    (Equiv.sumCongr ((isClosedEmbedding_pushout_inr_relCWBaseInclusion
      (sigmaDiskAttachingMap b)).relCWComplexCellEquiv image_univ (image_empty _) m)
        (sigmaDiskAdjunctionSpaceCellEquiv b m))

/-- The characteristic map of a cell of `W`, as a cell of `W ∪_b ⨆ᵢ Dⁿⁱ`, is its characteristic
map in `W` followed by the inclusion of `W`. -/
@[simp]
theorem sigmaDiskAdjunctionCWComplex_map_inl (m : ℕ) (j : cell (univ : Set W) m)
    (x : Fin m → ℝ) :
    letI := sigmaDiskRelCWComplex n
    letI := sigmaDiskAdjunctionCWComplex n b hb
    map m ((sigmaDiskAdjunctionCWComplexCellEquiv n b hb m).symm (.inl j)) x =
      pushout.inr (relCWBaseInclusion
        (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))))
          (TopCat.ofHom (sigmaDiskAttachingMap b)) (map m j x) := by
  let := sigmaDiskRelCWComplex n
  let := relativeCWPushout (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i))))
    (sigmaDiskAttachingMap b)
  let := sigmaDiskAdjunctionBaseCWComplex b
  have hf := isClosedEmbedding_pushout_inr_relCWBaseInclusion
    (C := univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))) (sigmaDiskAttachingMap b)
  set k := (hf.relCWComplexCellEquiv image_univ (image_empty _) m).symm j
  have h₁ := map_relCWComplexTrans_inl (cellFrontier_inter_subset_skeletonLT b hb) m k
  have h₂ := hf.coe_map_relCWComplex image_univ (image_empty _) m k
  exact (congrArg (fun e : PartialEquiv _ _ ↦ e x) h₁).trans
    ((congrFun h₂ x).trans (by simp [k]))

/-- The characteristic map of the cell of the `i`-th disk in `W ∪_b ⨆ᵢ Dⁿⁱ` is the characteristic
map of that disk followed by the map of the disjoint union of the disks into the adjunction
space. -/
@[simp]
theorem sigmaDiskAdjunctionCWComplex_map_inr (i : ι) (x : closedBall (0 : Fin (n i) → ℝ) 1) :
    letI := sigmaDiskRelCWComplex n
    letI := sigmaDiskAdjunctionCWComplex n b hb
    map (n i) ((sigmaDiskAdjunctionCWComplexCellEquiv n b hb (n i)).symm (.inr ⟨i, rfl⟩)) x =
      pushout.inl (relCWBaseInclusion
        (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))))
          (TopCat.ofHom (sigmaDiskAttachingMap b))
            ⟨⟨i, (diskHomeomorphClosedBall (n i)).symm x⟩,
              mk_mem_sigma (mem_univ _) (mem_univ _)⟩ := by
  let := sigmaDiskRelCWComplex n
  let := relativeCWPushout (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i))))
    (sigmaDiskAttachingMap b)
  let := sigmaDiskAdjunctionBaseCWComplex b
  set c := (sigmaDiskAdjunctionSpaceCellEquiv b (n i)).symm ⟨i, rfl⟩
  have h₁ := map_relCWComplexTrans_inr (cellFrontier_inter_subset_skeletonLT b hb) (n i) c
  refine (congrArg (fun e : PartialEquiv (Fin (n i) → ℝ) _ ↦ e x) h₁).trans
    ((relativeCWPushout_map_apply (sigmaDiskAttachingMap b) (n i) c x).trans ?_)
  simp only [c, sigmaDiskAdjunctionSpaceCellEquiv_symm_mk, Equiv.apply_symm_apply,
    sigmaDiskRelCWComplex_map_apply]

/-- **`W` is a subcomplex of `W ∪_b ⨆ᵢ Dⁿⁱ`.** Its image in the adjunction space is the
subcomplex of `TauCeti.sigmaDiskAdjunctionCWComplex` made of the cells of `W`. -/
def sigmaDiskAdjunctionSubcomplex :
    letI := sigmaDiskRelCWComplex n
    letI := sigmaDiskAdjunctionCWComplex n b hb
    Subcomplex (univ : Set (relCWAdjunctionSpace
      (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))) (sigmaDiskAttachingMap b))) :=
  letI := sigmaDiskRelCWComplex n
  letI := sigmaDiskAdjunctionCWComplex n b hb
  letI := sigmaDiskAdjunctionBaseCWComplex b
  RelCWComplex.Subcomplex.mk'' _ (range (pushout.inr (relCWBaseInclusion
      (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))))
        (TopCat.ofHom (sigmaDiskAttachingMap b))))
    (fun m ↦ range fun j ↦ (sigmaDiskAdjunctionCWComplexCellEquiv n b hb m).symm (.inl j)) <| by
      ext x
      simp only [empty_union, mem_iUnion, Subtype.exists, mem_range, exists_prop,
        exists_exists_eq_and]
      constructor
      · rintro ⟨m, j, y, -, rfl⟩
        exact ⟨_, (sigmaDiskAdjunctionCWComplex_map_inl n b hb m j y).symm⟩
      · rintro ⟨w, rfl⟩
        obtain ⟨m, j, y, hy, rfl⟩ : ∃ m, ∃ j : cell (univ : Set W) m, w ∈ openCell m j := by
          simpa using
            (CWComplex.iUnion_openCell_eq_complex (C := (univ : Set W))).symm.subset (mem_univ w)
        exact ⟨m, j, y, hy, sigmaDiskAdjunctionCWComplex_map_inl n b hb m j y⟩

/-- The subcomplex `TauCeti.sigmaDiskAdjunctionSubcomplex` is the image of `W`. -/
@[simp]
theorem coe_sigmaDiskAdjunctionSubcomplex :
    letI := sigmaDiskRelCWComplex n
    letI := sigmaDiskAdjunctionCWComplex n b hb
    (sigmaDiskAdjunctionSubcomplex n b hb : Set (relCWAdjunctionSpace
      (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))) (sigmaDiskAttachingMap b))) =
      range (pushout.inr (relCWBaseInclusion
        (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))))
          (TopCat.ofHom (sigmaDiskAttachingMap b))) :=
  (rfl)

/-- The `m`-cells of the subcomplex `TauCeti.sigmaDiskAdjunctionSubcomplex` are the `m`-cells of
`W`. -/
theorem sigmaDiskAdjunctionSubcomplex_I (m : ℕ) :
    letI := sigmaDiskRelCWComplex n
    letI := sigmaDiskAdjunctionCWComplex n b hb
    (sigmaDiskAdjunctionSubcomplex n b hb).I m =
      range fun j ↦ (sigmaDiskAdjunctionCWComplexCellEquiv n b hb m).symm (.inl j) :=
  (rfl)

variable {n} {Z : Type u} [TopologicalSpace Z]

/-- **CW models of cell attachments.** Let `h : W ≃ₕ Z` be a homotopy equivalence from a CW complex
`W` to a space `Z`, and let `a i : ∂Dⁿⁱ → Z` be attaching maps of disks. Then there are attaching
maps `b i : ∂Dⁿⁱ → W` into the skeleta `skeletonLT W (n i)`, with `h ∘ b i` homotopic to `a i`, and
a homotopy equivalence `W ∪_b ⨆ᵢ Dⁿⁱ ≃ₕ Z ∪_a ⨆ᵢ Dⁿⁱ` which is `h` on `W`. By the first property
`W ∪_b ⨆ᵢ Dⁿⁱ` is a CW complex whose cells are those of `W` and one new `n i`-cell for each `i`
(`TauCeti.sigmaDiskAdjunctionCWComplex`). -/
theorem _root_.ContinuousMap.HomotopyEquiv.exists_homotopyEquiv_sigmaDiskAdjunction
    (h : W ≃ₕ Z) (a : ∀ i, C(TopCat.diskBoundary.{u} (n i), Z)) :
    letI := sigmaDiskRelCWComplex n
    ∃ (b : ∀ i, C(TopCat.diskBoundary.{u} (n i), W)),
      (∀ i x, b i x ∈ (skeletonLT (univ : Set W) (n i) : Set W)) ∧
      (∀ i, (h.toFun.comp (b i)).Homotopic (a i)) ∧
      ∃ Φ : relCWAdjunctionSpace (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i))))
          (sigmaDiskAttachingMap b) ≃ₕ
        relCWAdjunctionSpace (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i))))
          (sigmaDiskAttachingMap a),
        ∀ w : W, Φ (pushout.inr (relCWBaseInclusion
          (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))))
            (TopCat.ofHom (sigmaDiskAttachingMap b)) w) =
          pushout.inr (relCWBaseInclusion
            (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))))
              (TopCat.ofHom (sigmaDiskAttachingMap a)) (h w) := by
  let := sigmaDiskRelCWComplex n
  set C := univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))
  -- Move the attaching maps `h⁻¹ ∘ a i` into the skeleta of `W`.
  choose b hgb hb using fun i ↦
    (h.invFun.comp (a i)).exists_homotopic_mapsTo_skeletonLT_diskBoundary
  have hhb (i : ι) : (h.toFun.comp (b i)).Homotopic (a i) :=
    ((ContinuousMap.Homotopic.refl h.toFun).comp (hgb i)).symm.trans
      (h.right_inv.comp (ContinuousMap.Homotopic.refl (a i)))
  refine ⟨b, hb, hhb, ?_⟩
  have hi := isEmbedding_relCWBaseInclusion C
  have hA := hasHomotopyExtensionProperty_range_relCWBaseInclusion C
  let i₀ := relCWBaseInclusion C
  let ab := TopCat.ofHom (sigmaDiskAttachingMap b)
  let f := TopCat.ofHom h.toFun
  let g := TopCat.ofHom h.invFun
  -- First change the base `W` to `Z` along `h`, attaching along `h ∘ b`.
  have hP := IsPushout.of_hasPushout i₀ ab
  have hP' := IsPushout.of_hasPushout i₀ (ab ≫ f)
  have hw : i₀ ≫ pushout.inl i₀ (ab ≫ f) = ab ≫ f ≫ pushout.inr i₀ (ab ≫ f) := by
    rw [← Category.assoc]
    exact pushout.condition
  let F : pushout i₀ ab ⟶ pushout i₀ (ab ≫ f) :=
    hP.desc (pushout.inl i₀ (ab ≫ f)) (f ≫ pushout.inr i₀ (ab ≫ f)) hw
  obtain ⟨G, -, hFG, hGF⟩ := hP.exists_homotopic_id_of_homotopic_id hP' hi hA (g := g) rfl
    h.left_inv h.right_inv (hP.inl_desc _ _ hw) (hP.inr_desc _ _ hw)
  -- Then reattach along a homotopy `h ∘ b ≃ a`, assembled from the homotopies `h ∘ b i ≃ a i` on
  -- the boundary spheres.
  have hK : (ab ≫ f).hom.Homotopic (TopCat.ofHom (sigmaDiskAttachingMap a)).hom := by
    rw [TopCat.hom_comp, TopCat.hom_ofHom, TopCat.hom_ofHom, TopCat.hom_ofHom,
      ← ContinuousMap.sigmaDiskAttachingMap_comp]
    exact homotopic_sigmaDiskAttachingMap hhb
  obtain ⟨φ, ψ, hφ, -, hφψ, hψφ⟩ := hP'.exists_homotopicRel_id_of_homotopy
    (IsPushout.of_hasPushout i₀ (TopCat.ofHom (sigmaDiskAttachingMap a))) hi hA hK.some
  let E₁ : (pushout i₀ ab : TopCat.{u}) ≃ₕ (pushout i₀ (ab ≫ f) : TopCat.{u}) :=
    ⟨F.hom, G.hom, hFG, hGF⟩
  let E₂ : (pushout i₀ (ab ≫ f) : TopCat.{u}) ≃ₕ
      (pushout i₀ (TopCat.ofHom (sigmaDiskAttachingMap a)) : TopCat.{u}) :=
    ⟨φ.hom, ψ.hom, hφψ.homotopic, hψφ.homotopic⟩
  refine ⟨E₁.trans E₂, fun w ↦ ?_⟩
  have h₁ : F (pushout.inr i₀ ab w) = pushout.inr i₀ (ab ≫ f) (h w) :=
    ConcreteCategory.congr_hom (hP.inr_desc _ _ hw) w
  exact (congrArg φ h₁).trans (ConcreteCategory.congr_hom hφ (h w))

end TauCeti
