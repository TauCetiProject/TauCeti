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
import TauCeti.Topology.CWComplex.Classical.Sphere.CellularApproximation
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
made of the cells of `W` (`TauCeti.sigmaDiskAdjunctionSubcomplex`). Attaching finitely many cells
to a finite CW complex gives a finite CW complex (`TauCeti.finite_sigmaDiskAdjunctionCWComplex`).
More generally, if `W` is a CW complex relative to a base `D` and each `b i` lands in the relative
skeleton `skeletonLT W (n i)`, which contains `D`, then `W ∪_b ⨆ᵢ Dⁿⁱ` is a CW complex relative to
the image of `D`, with the same cells (`TauCeti.sigmaDiskAdjunctionRelCWComplex`).

Every map of a sphere into a CW complex, or a relative CW complex, can be moved into the required
skeleton by a homotopy
(`ContinuousMap.exists_homotopic_mapsTo_skeletonLT_diskBoundary`), by cellular approximation for
the CW structure of the sphere with one `0`-cell and one top cell. Since attaching along homotopic
maps, or to homotopy equivalent spaces, does not change the homotopy type, this gives CW models of
cell attachments: if `h : W ≃ₕ Z` is a homotopy equivalence from a CW complex to a space `Z`, and
`a i : ∂Dⁿⁱ → Z` are attaching maps, then there are attaching maps `b i` into the skeleta of `W`,
with `h ∘ b i` homotopic to `a i`, and a homotopy equivalence `W ∪_b ⨆ᵢ Dⁿⁱ ≃ₕ Z ∪_a ⨆ᵢ Dⁿⁱ`
which is `h` on `W` (`ContinuousMap.HomotopyEquiv.exists_homotopyEquiv_sigmaDiskAdjunction`). So
the attachment `Z ∪_a ⨆ᵢ Dⁿⁱ` has a CW model whose cells are the cells of the given model of `Z`,
with their characteristic maps, and one new `n i`-cell for each `i`. The same holds for a model
`W` which is a CW complex relative to a base `D`. Iterating this is how a space built by successive
cell attachments, such as the sublevels of a Morse function across their critical levels, receives
a CW model, or a relative CW model over its first stage.

Such attachments are often built in `TopCat` as the pushout of `∐ᵢ a i : ∐ᵢ ∂Dⁿⁱ ⟶ Z` along the
coproduct of the boundary inclusions `∐ᵢ ∂Dⁿⁱ ⟶ ∐ᵢ Dⁿⁱ`. That pushout is homeomorphic to the
adjunction space `Z ∪_a ⨆ᵢ Dⁿⁱ` used here, compatibly with the inclusions of `Z` and of the disks
(`TauCeti.sigmaDiskAdjunctionIsoPushout`).

The CW structure is the composite (`TauCeti.relCWComplexTrans`) of the relative CW structure of the
attachment over `W` (`TauCeti.relativeCWPushout`) with the CW structure of `W`, or its relative CW
structure over `D`, carried to the
adjunction space along the closed embedding of `W`. The boundary of the cell of the `i`-th disk is
the image of `b i`, which lies in `skeletonLT W (n i)`: this is the compatibility condition of the
composite. The homotopy equivalence composes the change of base along `h`
(`ContinuousMap.HomotopyEquiv.exists_homotopyEquiv_relCWAdjunctionSpace`) with the reattachment
along a homotopy `h ∘ b ≃ a` (`CategoryTheory.IsPushout.exists_homotopicRel_id_of_homotopy`).

## Main definitions

* `TauCeti.sigmaDiskAdjunctionCWComplex`: the CW structure on `W ∪_b ⨆ᵢ Dⁿⁱ`.
* `TauCeti.sigmaDiskAdjunctionCWComplexCellEquiv`: its `m`-cells are those of `W` and the indices
  `i` with `n i = m`.
* `TauCeti.sigmaDiskAdjunctionRelCWComplex` and `TauCeti.sigmaDiskAdjunctionRelCWComplexCellEquiv`:
  the same for a CW complex `W` relative to a base `D`, giving a CW complex relative to the image of
  `D`.
* `TauCeti.sigmaDiskAdjunctionSubcomplex`: `W` as a subcomplex of `W ∪_b ⨆ᵢ Dⁿⁱ`.
* `TauCeti.sigmaDiskAdjunctionIsoPushout`: `Z ∪_a ⨆ᵢ Dⁿⁱ` is the pushout of `∐ᵢ a i` along
  `∐ᵢ ∂Dⁿⁱ ⟶ ∐ᵢ Dⁿⁱ`.

## Main results

* `TauCeti.finite_sigmaDiskAdjunctionCWComplex`: attaching finitely many cells to a finite CW
  complex gives a finite CW complex.
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

attribute [local instance] sigmaDiskRelCWComplex

variable {W : Type u} [TopologicalSpace W] [T2Space W]

variable {ι : Type u} {n : ι → ℕ}

section Relative

variable {D : Set W} [RelCWComplex (univ : Set W) D]

variable (b : ∀ i, C(TopCat.diskBoundary.{u} (n i), W))

/-- The relative CW structure of `W` over `D`, carried to its image in the adjunction space
`W ∪_b ⨆ᵢ Dⁿⁱ`, whose base is the image `D'` of `D`. -/
private abbrev sigmaDiskAdjunctionBaseRelCWComplex
    {D' : Set (relCWAdjunctionSpace
      (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))) (sigmaDiskAttachingMap b))}
    (hD : pushout.inr (relCWBaseInclusion (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))))
      (TopCat.ofHom (sigmaDiskAttachingMap b)) '' D = D') :
    RelCWComplex (range (pushout.inr (relCWBaseInclusion
      (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))))
        (TopCat.ofHom (sigmaDiskAttachingMap b)))) D' :=
  (isClosedEmbedding_pushout_inr_relCWBaseInclusion (sigmaDiskAttachingMap b)).relCWComplex
    (C := univ) (D := D) image_univ hD

section PushoutAux

attribute [local instance] relativeCWPushout

/-- The boundary of each `m`-cell of the attachment lies in the image of `skeletonLT W m`. -/
private theorem cellFrontier_relativeCWPushout_subset
    (hb : ∀ i x, b i x ∈ (skeletonLT (univ : Set W) (n i) : Set W)) (m : ℕ)
    (j : cell (univ : Set (relCWAdjunctionSpace
      (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))) (sigmaDiskAttachingMap b))) m) :
    cellFrontier m j ⊆ pushout.inr (relCWBaseInclusion
      (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))))
        (TopCat.ofHom (sigmaDiskAttachingMap b)) '' (skeletonLT (univ : Set W) m : Set W) := by
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
`W` with the relative CW structure of `W` over `D`: the part in `W` of the boundary of an `m`-cell
of the attachment lies in the skeleton `skeletonLT m` of `W`. -/
private theorem cellFrontier_inter_subset_skeletonLT
    (hb : ∀ i x, b i x ∈ (skeletonLT (univ : Set W) (n i) : Set W))
    {D' : Set (relCWAdjunctionSpace
      (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))) (sigmaDiskAttachingMap b))}
    (hD : pushout.inr (relCWBaseInclusion (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))))
      (TopCat.ofHom (sigmaDiskAttachingMap b)) '' D = D')
    (m : ℕ)
    (j : cell (univ : Set (relCWAdjunctionSpace
      (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))) (sigmaDiskAttachingMap b))) m) :
    letI := sigmaDiskAdjunctionBaseRelCWComplex b hD
    cellFrontier m j ∩ range (pushout.inr (relCWBaseInclusion
      (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))))
        (TopCat.ofHom (sigmaDiskAttachingMap b))) ⊆
      skeletonLT (range (pushout.inr (relCWBaseInclusion
        (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))))
          (TopCat.ofHom (sigmaDiskAttachingMap b)))) m := by
  let := sigmaDiskAdjunctionBaseRelCWComplex b hD
  -- The image of `skeletonLT W m` lies in the skeleton `skeletonLT m` of the image of `W`.
  rintro _ ⟨hx, -⟩
  obtain ⟨w, hw, rfl⟩ := cellFrontier_relativeCWPushout_subset b hb m j hx
  have hf := isClosedEmbedding_pushout_inr_relCWBaseInclusion
    (C := univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))) (sigmaDiskAttachingMap b)
  rcases RelCWComplex.mem_skeletonLT_iff.1 hw with hwD | ⟨l, hl, k, hk⟩
  · exact RelCWComplex.mem_skeletonLT_iff.2 (.inl (hD ▸ mem_image_of_mem _ hwD))
  refine RelCWComplex.mem_skeletonLT_iff.2
    (.inr ⟨l, hl, ((hf.relCWComplexCellEquiv image_univ hD) l).symm k, ?_⟩)
  rw [hf.openCell_relCWComplex, Equiv.apply_symm_apply]
  exact mem_image_of_mem _ hk

variable (n) in
/-- The relative CW structure on `W ∪_b ⨆ᵢ Dⁿⁱ` over any set `D'` equal to the image of `D`. -/
private abbrev sigmaDiskAdjunctionRelCWComplexAux
    (hb : ∀ i x, b i x ∈ (skeletonLT (univ : Set W) (n i) : Set W))
    {D' : Set (relCWAdjunctionSpace
      (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))) (sigmaDiskAttachingMap b))}
    (hD : pushout.inr (relCWBaseInclusion (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))))
      (TopCat.ofHom (sigmaDiskAttachingMap b)) '' D = D') :
    RelCWComplex (univ : Set (relCWAdjunctionSpace
      (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))) (sigmaDiskAttachingMap b))) D' :=
  letI := sigmaDiskAdjunctionBaseRelCWComplex b hD
  relCWComplexTrans _ _ D' (cellFrontier_inter_subset_skeletonLT b hb hD)

end PushoutAux

variable (n)

/-- The cells of `TauCeti.sigmaDiskAdjunctionRelCWComplexAux`. -/
private def sigmaDiskAdjunctionRelCWComplexAuxCellEquiv
    (hb : ∀ i x, b i x ∈ (skeletonLT (univ : Set W) (n i) : Set W))
    {D' : Set (relCWAdjunctionSpace
      (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))) (sigmaDiskAttachingMap b))}
    (hD : pushout.inr (relCWBaseInclusion (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))))
      (TopCat.ofHom (sigmaDiskAttachingMap b)) '' D = D') (m : ℕ) :
    letI := sigmaDiskAdjunctionRelCWComplexAux n b hb hD
    cell (univ : Set (relCWAdjunctionSpace
      (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))) (sigmaDiskAttachingMap b))) m ≃
        cell (univ : Set W) m ⊕ {i // n i = m} :=
  letI := relativeCWPushout (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i))))
    (sigmaDiskAttachingMap b)
  letI := sigmaDiskAdjunctionBaseRelCWComplex b hD
  (relCWComplexTransCellEquiv (cellFrontier_inter_subset_skeletonLT b hb hD) m).trans
    (Equiv.sumCongr ((isClosedEmbedding_pushout_inr_relCWBaseInclusion
      (sigmaDiskAttachingMap b)).relCWComplexCellEquiv image_univ hD m)
        (sigmaDiskAdjunctionSpaceCellEquiv b m))

private theorem sigmaDiskAdjunctionRelCWComplexAux_map_inl
    (hb : ∀ i x, b i x ∈ (skeletonLT (univ : Set W) (n i) : Set W))
    {D' : Set (relCWAdjunctionSpace
      (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))) (sigmaDiskAttachingMap b))}
    (hD : pushout.inr (relCWBaseInclusion (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))))
      (TopCat.ofHom (sigmaDiskAttachingMap b)) '' D = D')
    (m : ℕ) (j : cell (univ : Set W) m) (x : Fin m → ℝ) :
    letI := sigmaDiskAdjunctionRelCWComplexAux n b hb hD
    map m ((sigmaDiskAdjunctionRelCWComplexAuxCellEquiv n b hb hD m).symm (.inl j)) x =
      pushout.inr (relCWBaseInclusion
        (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))))
          (TopCat.ofHom (sigmaDiskAttachingMap b)) (map m j x) := by
  let := relativeCWPushout (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i))))
    (sigmaDiskAttachingMap b)
  let := sigmaDiskAdjunctionBaseRelCWComplex b hD
  have hf := isClosedEmbedding_pushout_inr_relCWBaseInclusion
    (C := univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))) (sigmaDiskAttachingMap b)
  set k := (hf.relCWComplexCellEquiv image_univ hD m).symm j
  have h₁ := map_relCWComplexTrans_inl (cellFrontier_inter_subset_skeletonLT b hb hD) m k
  have h₂ := hf.coe_map_relCWComplex image_univ hD m k
  exact (congrArg (fun e : PartialEquiv _ _ ↦ e x) h₁).trans
    ((congrFun h₂ x).trans (by simp [k]))

private theorem sigmaDiskAdjunctionRelCWComplexAux_map_inr
    (hb : ∀ i x, b i x ∈ (skeletonLT (univ : Set W) (n i) : Set W))
    {D' : Set (relCWAdjunctionSpace
      (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))) (sigmaDiskAttachingMap b))}
    (hD : pushout.inr (relCWBaseInclusion (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))))
      (TopCat.ofHom (sigmaDiskAttachingMap b)) '' D = D')
    (i : ι) (x : closedBall (0 : Fin (n i) → ℝ) 1) :
    letI := sigmaDiskAdjunctionRelCWComplexAux n b hb hD
    map (n i) ((sigmaDiskAdjunctionRelCWComplexAuxCellEquiv n b hb hD (n i)).symm
        (.inr ⟨i, rfl⟩)) x =
      pushout.inl (relCWBaseInclusion
        (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))))
          (TopCat.ofHom (sigmaDiskAttachingMap b))
            ⟨⟨i, (diskHomeomorphClosedBall (n i)).symm x⟩,
              mk_mem_sigma (mem_univ _) (mem_univ _)⟩ := by
  let := relativeCWPushout (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i))))
    (sigmaDiskAttachingMap b)
  let := sigmaDiskAdjunctionBaseRelCWComplex b hD
  set c := (sigmaDiskAdjunctionSpaceCellEquiv b (n i)).symm ⟨i, rfl⟩
  have h₁ := map_relCWComplexTrans_inr (cellFrontier_inter_subset_skeletonLT b hb hD) (n i) c
  refine (congrArg (fun e : PartialEquiv (Fin (n i) → ℝ) _ ↦ e x) h₁).trans
    ((relativeCWPushout_map_apply (sigmaDiskAttachingMap b) (n i) c x).trans ?_)
  simp only [c, sigmaDiskAdjunctionSpaceCellEquiv_symm_mk, Equiv.apply_symm_apply,
    sigmaDiskRelCWComplex_map_apply]

/-- **Attaching cells to a relative CW complex along maps into skeleta.** Let `W` be a CW complex
relative to `D` and let `b i : ∂Dⁿⁱ → W` be maps into the skeleta `skeletonLT W (n i)`. The space
`W ∪_b ⨆ᵢ Dⁿⁱ` obtained by attaching the disks `Dⁿⁱ` to `W` along the `b i` is a CW complex relative
to the image of `D`. Its `m`-cells are the `m`-cells of `W` and the indices `i` with `n i = m`
(`TauCeti.sigmaDiskAdjunctionRelCWComplexCellEquiv`). For an absolute CW complex `W` this is
`TauCeti.sigmaDiskAdjunctionCWComplex`. -/
@[instance_reducible]
def sigmaDiskAdjunctionRelCWComplex
    (hb : ∀ i x, b i x ∈ (skeletonLT (univ : Set W) (n i) : Set W)) :
    RelCWComplex (univ : Set (relCWAdjunctionSpace
      (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))) (sigmaDiskAttachingMap b)))
      (pushout.inr (relCWBaseInclusion (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))))
        (TopCat.ofHom (sigmaDiskAttachingMap b)) '' D) :=
  sigmaDiskAdjunctionRelCWComplexAux n b hb rfl

variable (hb : ∀ i x, b i x ∈ (skeletonLT (univ : Set W) (n i) : Set W))

/-- The `m`-cells of `W ∪_b ⨆ᵢ Dⁿⁱ` relative to the image of `D` are the `m`-cells of `W` together
with the indices `i` with `n i = m`. -/
def sigmaDiskAdjunctionRelCWComplexCellEquiv (m : ℕ) :
    letI := sigmaDiskAdjunctionRelCWComplex n b hb
    cell (univ : Set (relCWAdjunctionSpace
      (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))) (sigmaDiskAttachingMap b))) m ≃
        cell (univ : Set W) m ⊕ {i // n i = m} :=
  sigmaDiskAdjunctionRelCWComplexAuxCellEquiv n b hb rfl m

/-- The characteristic map of a cell of `W`, as a cell of `W ∪_b ⨆ᵢ Dⁿⁱ` relative to the image of
`D`, is its characteristic map in `W` followed by the inclusion of `W`. -/
@[simp]
theorem sigmaDiskAdjunctionRelCWComplex_map_inl (m : ℕ) (j : cell (univ : Set W) m)
    (x : Fin m → ℝ) :
    letI := sigmaDiskAdjunctionRelCWComplex n b hb
    map m ((sigmaDiskAdjunctionRelCWComplexCellEquiv n b hb m).symm (.inl j)) x =
      pushout.inr (relCWBaseInclusion
        (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))))
          (TopCat.ofHom (sigmaDiskAttachingMap b)) (map m j x) :=
  sigmaDiskAdjunctionRelCWComplexAux_map_inl n b hb rfl m j x

/-- The characteristic map of the cell of the `i`-th disk in `W ∪_b ⨆ᵢ Dⁿⁱ` relative to the image
of `D` is the characteristic map of that disk followed by the map of the disjoint union of the disks
into the adjunction space. -/
@[simp]
theorem sigmaDiskAdjunctionRelCWComplex_map_inr (i : ι) (x : closedBall (0 : Fin (n i) → ℝ) 1) :
    letI := sigmaDiskAdjunctionRelCWComplex n b hb
    map (n i) ((sigmaDiskAdjunctionRelCWComplexCellEquiv n b hb (n i)).symm (.inr ⟨i, rfl⟩)) x =
      pushout.inl (relCWBaseInclusion
        (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))))
          (TopCat.ofHom (sigmaDiskAttachingMap b))
            ⟨⟨i, (diskHomeomorphClosedBall (n i)).symm x⟩,
              mk_mem_sigma (mem_univ _) (mem_univ _)⟩ :=
  sigmaDiskAdjunctionRelCWComplexAux_map_inr n b hb rfl i x

end Relative

section Absolute

variable [CWComplex (univ : Set W)] (b : ∀ i, C(TopCat.diskBoundary.{u} (n i), W))

variable (n)

/-- **Attaching cells to a CW complex along maps into skeleta.** Let `W` be a CW complex and let
`b i : ∂Dⁿⁱ → W` be maps into the skeleta `skeletonLT W (n i)`. The space `W ∪_b ⨆ᵢ Dⁿⁱ` obtained by
attaching the disks `Dⁿⁱ` to `W` along the `b i` is a CW complex. Its `m`-cells are the `m`-cells
of `W` and the indices `i` with `n i = m` (`TauCeti.sigmaDiskAdjunctionCWComplexCellEquiv`). -/
@[instance_reducible]
def sigmaDiskAdjunctionCWComplex (hb : ∀ i x, b i x ∈ (skeletonLT (univ : Set W) (n i) : Set W)) :
    CWComplex (univ : Set (relCWAdjunctionSpace
      (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))) (sigmaDiskAttachingMap b))) :=
  @RelCWComplex.toCWComplex _ _ _ (sigmaDiskAdjunctionRelCWComplexAux n b hb (image_empty _))

variable (hb : ∀ i x, b i x ∈ (skeletonLT (univ : Set W) (n i) : Set W))

/-- The `m`-cells of `W ∪_b ⨆ᵢ Dⁿⁱ` are the `m`-cells of `W` together with the indices `i` with
`n i = m`. -/
def sigmaDiskAdjunctionCWComplexCellEquiv (m : ℕ) :
    letI := sigmaDiskAdjunctionCWComplex n b hb
    cell (univ : Set (relCWAdjunctionSpace
      (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))) (sigmaDiskAttachingMap b))) m ≃
        cell (univ : Set W) m ⊕ {i // n i = m} :=
  sigmaDiskAdjunctionRelCWComplexAuxCellEquiv n b hb (image_empty _) m

/-- Attaching finitely many cells to a finite CW complex gives a finite CW complex. -/
theorem finite_sigmaDiskAdjunctionCWComplex [Finite ι] [RelCWComplex.Finite (univ : Set W)] :
    letI := sigmaDiskAdjunctionCWComplex n b hb
    RelCWComplex.Finite (univ : Set (relCWAdjunctionSpace
      (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))) (sigmaDiskAttachingMap b))) :=
  letI := sigmaDiskAdjunctionCWComplex n b hb
  have := RelCWComplex.finite_cells_of_finite (C := (univ : Set W))
  -- The cells are those of `W`, of all dimensions, together with one cell for each `i`.
  RelCWComplex.finite_of_finite_cells (.of_equiv ((Σ m, cell (univ : Set W) m) ⊕ ι)
    ((Equiv.sumCongr (.refl _) (Equiv.sigmaFiberEquiv n).symm).trans
      ((Equiv.sigmaSumDistrib _ _).symm.trans
        (Equiv.sigmaCongrRight fun m ↦ (sigmaDiskAdjunctionCWComplexCellEquiv n b hb m).symm))))

/-- The characteristic map of a cell of `W`, as a cell of `W ∪_b ⨆ᵢ Dⁿⁱ`, is its characteristic
map in `W` followed by the inclusion of `W`. -/
@[simp]
theorem sigmaDiskAdjunctionCWComplex_map_inl (m : ℕ) (j : cell (univ : Set W) m)
    (x : Fin m → ℝ) :
    letI := sigmaDiskAdjunctionCWComplex n b hb
    map m ((sigmaDiskAdjunctionCWComplexCellEquiv n b hb m).symm (.inl j)) x =
      pushout.inr (relCWBaseInclusion
        (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))))
          (TopCat.ofHom (sigmaDiskAttachingMap b)) (map m j x) :=
  sigmaDiskAdjunctionRelCWComplexAux_map_inl n b hb (image_empty _) m j x

/-- The characteristic map of the cell of the `i`-th disk in `W ∪_b ⨆ᵢ Dⁿⁱ` is the characteristic
map of that disk followed by the map of the disjoint union of the disks into the adjunction
space. -/
@[simp]
theorem sigmaDiskAdjunctionCWComplex_map_inr (i : ι) (x : closedBall (0 : Fin (n i) → ℝ) 1) :
    letI := sigmaDiskAdjunctionCWComplex n b hb
    map (n i) ((sigmaDiskAdjunctionCWComplexCellEquiv n b hb (n i)).symm (.inr ⟨i, rfl⟩)) x =
      pushout.inl (relCWBaseInclusion
        (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))))
          (TopCat.ofHom (sigmaDiskAttachingMap b))
            ⟨⟨i, (diskHomeomorphClosedBall (n i)).symm x⟩,
              mk_mem_sigma (mem_univ _) (mem_univ _)⟩ :=
  sigmaDiskAdjunctionRelCWComplexAux_map_inr n b hb (image_empty _) i x

/-- **`W` is a subcomplex of `W ∪_b ⨆ᵢ Dⁿⁱ`.** Its image in the adjunction space is the
subcomplex of `TauCeti.sigmaDiskAdjunctionCWComplex` made of the cells of `W`. -/
def sigmaDiskAdjunctionSubcomplex :
    letI := sigmaDiskAdjunctionCWComplex n b hb
    Subcomplex (univ : Set (relCWAdjunctionSpace
      (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))) (sigmaDiskAttachingMap b))) :=
  letI := sigmaDiskAdjunctionCWComplex n b hb
  letI := sigmaDiskAdjunctionBaseRelCWComplex (D' := ∅) b (image_empty _)
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
    letI := sigmaDiskAdjunctionCWComplex n b hb
    (sigmaDiskAdjunctionSubcomplex n b hb).I m =
      range fun j ↦ (sigmaDiskAdjunctionCWComplexCellEquiv n b hb m).symm (.inl j) :=
  (rfl)

end Absolute

variable {D : Set W} [RelCWComplex (univ : Set W) D] {Z : Type u} [TopologicalSpace Z]

/-- **CW models of cell attachments.** Let `h : W ≃ₕ Z` be a homotopy equivalence from a CW complex
`W`, or a CW complex relative to some base `D`, to a space `Z`, and let `a i : ∂Dⁿⁱ → Z` be
attaching maps of disks. Then there are attaching maps `b i : ∂Dⁿⁱ → W` into the skeleta
`skeletonLT W (n i)`, with `h ∘ b i` homotopic to `a i`, and a homotopy equivalence
`W ∪_b ⨆ᵢ Dⁿⁱ ≃ₕ Z ∪_a ⨆ᵢ Dⁿⁱ` which is `h` on `W`. By the first property `W ∪_b ⨆ᵢ Dⁿⁱ` is a CW
complex, or a CW complex relative to the image of `D`, whose cells are those of `W` and one new
`n i`-cell for each `i` (`TauCeti.sigmaDiskAdjunctionCWComplex`,
`TauCeti.sigmaDiskAdjunctionRelCWComplex`). -/
theorem _root_.ContinuousMap.HomotopyEquiv.exists_homotopyEquiv_sigmaDiskAdjunction
    (h : W ≃ₕ Z) (a : ∀ i, C(TopCat.diskBoundary.{u} (n i), Z)) :
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
  set C := univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))
  -- Move the attaching maps `h⁻¹ ∘ a i` into the skeleta of `W`.
  choose b hgb hb using fun i ↦
    (h.invFun.comp (a i)).exists_homotopic_mapsTo_skeletonLT_diskBoundary
  have hhb (i : ι) : (h.toFun.comp (b i)).Homotopic (a i) :=
    ((ContinuousMap.Homotopic.refl h.toFun).comp (hgb i)).symm.trans
      (h.right_inv.comp (ContinuousMap.Homotopic.refl (a i)))
  refine ⟨b, hb, hhb, ?_⟩
  -- First change the base `W` to `Z` along `h`, attaching along `h ∘ b`.
  obtain ⟨E₁, hE₁, -⟩ := h.exists_homotopyEquiv_relCWAdjunctionSpace C (sigmaDiskAttachingMap b)
  let i₀ := relCWBaseInclusion C
  let hb' := h.toFun.comp (sigmaDiskAttachingMap b)
  -- Then reattach along a homotopy `h ∘ b ≃ a`, assembled from the homotopies `h ∘ b i ≃ a i` on
  -- the boundary spheres.
  have hK : (TopCat.ofHom (h.toFun.comp (sigmaDiskAttachingMap b))).hom.Homotopic
      (TopCat.ofHom (sigmaDiskAttachingMap a)).hom := by
    rw [TopCat.hom_ofHom, TopCat.hom_ofHom, ← ContinuousMap.sigmaDiskAttachingMap_comp]
    exact homotopic_sigmaDiskAttachingMap hhb
  obtain ⟨φ, ψ, hφ, -, hφψ, hψφ⟩ :=
    (IsPushout.of_hasPushout i₀ (TopCat.ofHom hb')).exists_homotopicRel_id_of_homotopy
      (IsPushout.of_hasPushout i₀ (TopCat.ofHom (sigmaDiskAttachingMap a)))
      (isEmbedding_relCWBaseInclusion C) (hasHomotopyExtensionProperty_range_relCWBaseInclusion C)
      hK.some
  let E₂ : relCWAdjunctionSpace C hb' ≃ₕ relCWAdjunctionSpace C (sigmaDiskAttachingMap a) :=
    ⟨φ.hom, ψ.hom, hφψ.homotopic, hψφ.homotopic⟩
  refine ⟨E₁.trans E₂, fun w ↦ ?_⟩
  exact (congrArg φ (hE₁ w)).trans (ConcreteCategory.congr_hom hφ (h w))

section Pushout

variable {ι : Type u} (n : ι → ℕ) {Z : TopCat.{u}}

/-- The disjoint union of the disks `Dⁿⁱ`, as the subset `univ.sigma fun i ↦ univ` of
`Σ i, Dⁿⁱ`, is their coproduct in `TopCat`. -/
private def sigmaDiskIsoCoproduct :
    TopCat.of (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))) ≅
      ∐ fun i ↦ TopCat.disk.{u} (n i) :=
  TopCat.isoOfHomeo ((Homeomorph.setCongr (sigma_univ.trans preimage_univ)).trans
      (Homeomorph.Set.univ (Σ i, TopCat.disk.{u} (n i)))) ≪≫
    (TopCat.sigmaIsoSigma _).symm

/-- The disjoint union of the boundary spheres `∂Dⁿⁱ`, as a subset of `Σ i, Dⁿⁱ`, is their
coproduct in `TopCat`. -/
private def sigmaDiskBoundaryIsoCoproduct :
    TopCat.of (univ.sigma fun i ↦ range (TopCat.diskBoundaryInclusion.{u} (n i))) ≅
      ∐ fun i ↦ TopCat.diskBoundary.{u} (n i) :=
  TopCat.isoOfHomeo (sigmaDiskBoundaryHomeomorph n) ≪≫ (TopCat.sigmaIsoSigma _).symm

variable {n}

/-- The pushout of the attaching maps `∐ᵢ ∂Dⁿⁱ ⟶ Z` along the coproduct of the boundary
inclusions `∐ᵢ ∂Dⁿⁱ ⟶ ∐ᵢ Dⁿⁱ` is also a pushout of the inclusion of the boundary spheres into the
disjoint union of disks, as subsets of `Σ i, Dⁿⁱ`. -/
private theorem isPushout_relCWBaseInclusion_sigmaDiskAttachingMap
    (a : ∀ i, TopCat.diskBoundary.{u} (n i) ⟶ Z) :
    IsPushout (relCWBaseInclusion (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))))
      (TopCat.ofHom (sigmaDiskAttachingMap fun i ↦ (a i).hom))
      ((sigmaDiskIsoCoproduct n).hom ≫
        pushout.inr (Sigma.desc a) (Limits.Sigma.map fun i ↦ TopCat.diskBoundaryInclusion (n i)))
      (pushout.inl (Sigma.desc a) (Limits.Sigma.map fun i ↦ TopCat.diskBoundaryInclusion (n i))) :=
  (IsPushout.of_hasPushout (Sigma.desc a)
    (Limits.Sigma.map fun i ↦ TopCat.diskBoundaryInclusion (n i))).flip.of_iso
    (sigmaDiskBoundaryIsoCoproduct n).symm (sigmaDiskIsoCoproduct n).symm (.refl _) (.refl _)
    (Sigma.hom_ext _ _ fun i ↦ by
      refine ConcreteCategory.hom_ext _ _ fun s ↦ Subtype.ext ?_
      simp [sigmaDiskBoundaryIsoCoproduct, sigmaDiskIsoCoproduct]
      -- `Homeomorph.setCongr` and `Homeomorph.Set.univ` keep the underlying point, and have no
      -- `simp` lemmas saying so.
      rfl)
    (Sigma.hom_ext _ _ fun i ↦ by
      ext s
      simp [sigmaDiskBoundaryIsoCoproduct])
    (by simp) (by simp)

/-- **Cell attachments as adjunction spaces.** The adjunction space `Z ∪_a ⨆ᵢ Dⁿⁱ` of the disjoint
union of disks relative to their boundary spheres is homeomorphic to the pushout of the attaching
maps `∐ᵢ ∂Dⁿⁱ ⟶ Z` along the coproduct of the boundary inclusions `∐ᵢ ∂Dⁿⁱ ⟶ ∐ᵢ Dⁿⁱ`, the form in
which cell attachments are built in `TopCat`, by a homeomorphism compatible with the inclusions of
`Z` (`TauCeti.inr_sigmaDiskAdjunctionIsoPushout_hom`). -/
def sigmaDiskAdjunctionIsoPushout (a : ∀ i, TopCat.diskBoundary.{u} (n i) ⟶ Z) :
    relCWAdjunctionSpace (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i))))
        (sigmaDiskAttachingMap fun i ↦ (a i).hom) ≅
      pushout (Sigma.desc a) (Limits.Sigma.map fun i ↦ TopCat.diskBoundaryInclusion.{u} (n i)) :=
  (isPushout_relCWBaseInclusion_sigmaDiskAttachingMap a).isoPushout.symm

/-- The homeomorphism `TauCeti.sigmaDiskAdjunctionIsoPushout` is compatible with the inclusions
of `Z`. -/
@[reassoc (attr := simp)]
theorem inr_sigmaDiskAdjunctionIsoPushout_hom (a : ∀ i, TopCat.diskBoundary.{u} (n i) ⟶ Z) :
    pushout.inr (relCWBaseInclusion (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))))
        (TopCat.ofHom (sigmaDiskAttachingMap fun i ↦ (a i).hom)) ≫
          (sigmaDiskAdjunctionIsoPushout a).hom =
      pushout.inl (Sigma.desc a) (Limits.Sigma.map fun i ↦ TopCat.diskBoundaryInclusion (n i)) :=
  (isPushout_relCWBaseInclusion_sigmaDiskAttachingMap a).inr_isoPushout_inv

/-- The homeomorphism `TauCeti.sigmaDiskAdjunctionIsoPushout` is compatible with the inclusions
of the disks. -/
@[simp]
theorem sigmaDiskAdjunctionIsoPushout_hom_inl_apply (a : ∀ i, TopCat.diskBoundary.{u} (n i) ⟶ Z)
    (i : ι) (x : TopCat.disk.{u} (n i)) :
    (sigmaDiskAdjunctionIsoPushout a).hom
        (pushout.inl (relCWBaseInclusion (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))))
          (TopCat.ofHom (sigmaDiskAttachingMap fun i ↦ (a i).hom))
          ⟨⟨i, x⟩, mem_univ _, mem_univ _⟩) =
      pushout.inr (Sigma.desc a) (Limits.Sigma.map fun i ↦ TopCat.diskBoundaryInclusion (n i))
        (Sigma.ι (fun i ↦ TopCat.disk.{u} (n i)) i x) := by
  rw [sigmaDiskAdjunctionIsoPushout, Iso.symm_hom, ← ConcreteCategory.comp_apply,
    (isPushout_relCWBaseInclusion_sigmaDiskAttachingMap a).inl_isoPushout_inv]
  simp only [sigmaDiskIsoCoproduct, Iso.trans_hom, Iso.symm_hom, ConcreteCategory.comp_apply]
  -- `Homeomorph.setCongr` and `Homeomorph.Set.univ` keep the underlying point, and have no `simp`
  -- lemmas saying so.
  exact congrArg _ (TopCat.sigmaIsoSigma_inv_apply (fun i ↦ TopCat.disk.{u} (n i)) i x)

end Pushout

end TauCeti
