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

The same holds for any relative CW complex `C` with base `D` in place of the disjoint union of
disks. If `P` is a pushout of the inclusion `D → C` along a map `g : D → W` to a CW complex `W`,
relative to some base `A`, and `g` maps the part in `D` of the boundary of every `n`-cell of `C`
into `skeletonLT W n`, then `P` is a CW complex relative to the image of `A`, whose `n`-cells are
those of `W` and those of `C` (`CategoryTheory.IsPushout.relCWComplexOfMapsToSkeletonLT`,
`CategoryTheory.IsPushout.cwComplexOfMapsToSkeletonLT` for an absolute CW complex `W`). The
attachment of disks is the case where `C` is the disjoint union of the disks, whose cell boundaries
are the boundary spheres.

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
pushout over `W` (`CategoryTheory.IsPushout.relCWComplex`) with the CW structure of `W`, or its
relative CW structure over `A`, carried to the pushout along the closed embedding of `W`. A point of
the boundary of a cell of `C` glued to a point of `W` comes from `D`, so the part in `W` of the
boundary of an `n`-cell of the pushout lies in the image of `skeletonLT W n`: this is the
compatibility condition of the composite. For the disks, the boundary of the cell of the `i`-th
disk is the image of `b i`, which lies in `skeletonLT W (n i)`. The homotopy equivalence composes
the change of base along `h`
(`ContinuousMap.HomotopyEquiv.exists_homotopyEquiv_relCWAdjunctionSpace`) with the reattachment
along a homotopy `h ∘ b ≃ a` (`CategoryTheory.IsPushout.exists_homotopicRel_id_of_homotopy`).

## Main definitions

* `CategoryTheory.IsPushout.relCWComplexOfMapsToSkeletonLT` and
  `CategoryTheory.IsPushout.cwComplexOfMapsToSkeletonLT`: the CW structure on a pushout of a
  relative CW complex along a cellular map, with cells
  `CategoryTheory.IsPushout.relCWComplexOfMapsToSkeletonLTCellEquiv` and
  `CategoryTheory.IsPushout.cwComplexOfMapsToSkeletonLTCellEquiv`.
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

namespace CategoryTheory.IsPushout

open TauCeti

variable {X : Type u} [TopologicalSpace X] [T2Space X] {C D : Set X} [RelCWComplex C D]
  {W : Type u} [TopologicalSpace W] [T2Space W]
  {P : TopCat.{u}} {g : TopCat.of D ⟶ TopCat.of W} {i : TopCat.of C ⟶ P}
  {j : TopCat.of W ⟶ P} (h : IsPushout (relCWBaseInclusion C) g i j)

section Relative

variable {A : Set W} [RelCWComplex (univ : Set W) A]
  (hg : ∀ n (c : cell C n) (x : D), (x : X) ∈ cellFrontier n c →
    g x ∈ (skeletonLT (univ : Set W) n : Set W))

include h

omit [T2Space X] [T2Space W] in
/-- The map `j : W → P` opposite to the inclusion of the base of a relative CW complex is a closed
embedding. -/
private theorem isClosedEmbedding_right : IsClosedEmbedding j :=
  TopCat.isClosedEmbedding_of_isPushout h.flip
    (IsClosedEmbedding.inclusion base_subset_complex
      ((isClosedBase C).preimage continuous_subtype_val))

/-- The relative CW structure of `W` over `A`, carried to its image in `P`, with base any set `A'`
equal to the image of `A`. -/
private abbrev rangeRelCWComplex {A' : Set P} (hA : j '' A = A') : RelCWComplex (range j) A' :=
  (isClosedEmbedding_right h).relCWComplex (C := univ) (D := A) image_univ hA

include hg

/-- In a pushout `P` of `D → C` along `g : D → W`, the part in the image of `W` of the boundary of
an `n`-cell lies in the image of the skeleton `skeletonLT W n`, if `g` maps the part in `D` of the
boundary of every `n`-cell of `C` into that skeleton. -/
private theorem cellFrontier_inter_range_subset_image_skeletonLT (n : ℕ)
    (c : letI := h.relCWComplex; cell (univ : Set P) n) :
    letI := h.relCWComplex
    cellFrontier n c ∩ range j ⊆ j '' (skeletonLT (univ : Set W) n : Set W) := by
  let := h.relCWComplex
  rintro _ ⟨⟨x, hx, rfl⟩, w, hw⟩
  have hmap := h.relCWComplex_map_apply n c ⟨x, sphere_subset_closedBall hx⟩
  -- A point of `C` glued to a point of `W` comes from a point `s` of the base `D`.
  obtain ⟨s, hs, rfl⟩ := (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit
    ((forget TopCat).map_isPushout h).isColimit (isEmbedding_relCWBaseInclusion C).injective
      _ w).1 (hmap.symm.trans hw.symm)
  refine ⟨g s, hg n (h.relCWComplexCellEquiv n c) s ?_, hw⟩
  have hsx : (s : X) = RelCWComplex.map n (h.relCWComplexCellEquiv n c) x :=
    congrArg Subtype.val hs
  rw [hsx]
  exact mem_image_of_mem _ hx

/-- The compatibility condition for composing the relative CW structure of a pushout `P` of
`D → C` over the image of `W` with the relative CW structure of `W` over `A`. -/
private theorem cellFrontier_inter_range_subset_skeletonLT [T2Space P] {A' : Set P}
    (hA : j '' A = A') (n : ℕ)
    (c : letI := h.relCWComplex; cell (univ : Set P) n) :
    letI := h.relCWComplex
    letI := rangeRelCWComplex h hA
    cellFrontier n c ∩ range j ⊆ skeletonLT (range j) n := by
  let := h.relCWComplex
  let := rangeRelCWComplex h hA
  intro y hy
  obtain ⟨w, hw, rfl⟩ := cellFrontier_inter_range_subset_image_skeletonLT h hg n c hy
  rcases RelCWComplex.mem_skeletonLT_iff.1 hw with hwA | ⟨l, hl, k, hk⟩
  · exact RelCWComplex.mem_skeletonLT_iff.2 (.inl (hA ▸ mem_image_of_mem _ hwA))
  refine RelCWComplex.mem_skeletonLT_iff.2
    (.inr ⟨l, hl, (((isClosedEmbedding_right h).relCWComplexCellEquiv image_univ hA) l).symm k, ?_⟩)
  rw [(isClosedEmbedding_right h).openCell_relCWComplex, Equiv.apply_symm_apply]
  exact mem_image_of_mem _ hk

/-- The relative CW structure on a pushout `P` of `D → C` along a cellular map, over any set `A'`
equal to the image of `A`. -/
private abbrev relCWComplexOfMapsToSkeletonLTAux [T2Space P] {A' : Set P} (hA : j '' A = A') :
    RelCWComplex (univ : Set P) A' :=
  letI := h.relCWComplex
  letI := rangeRelCWComplex h hA
  relCWComplexTrans _ _ A' (cellFrontier_inter_range_subset_skeletonLT h hg hA)

/-- The cells of `CategoryTheory.IsPushout.relCWComplexOfMapsToSkeletonLTAux`. -/
private def relCWComplexOfMapsToSkeletonLTAuxCellEquiv [T2Space P] {A' : Set P}
    (hA : j '' A = A') (n : ℕ) :
    letI := relCWComplexOfMapsToSkeletonLTAux h hg hA
    cell (univ : Set P) n ≃ cell (univ : Set W) n ⊕ cell C n :=
  letI := h.relCWComplex
  letI := rangeRelCWComplex h hA
  (relCWComplexTransCellEquiv (cellFrontier_inter_range_subset_skeletonLT h hg hA) n).trans
    (Equiv.sumCongr ((isClosedEmbedding_right h).relCWComplexCellEquiv image_univ hA n)
      (h.relCWComplexCellEquiv n))

private theorem relCWComplexOfMapsToSkeletonLTAux_map_inl [T2Space P] {A' : Set P}
    (hA : j '' A = A')
    (n : ℕ) (c : cell (univ : Set W) n) (x : Fin n → ℝ) :
    letI := relCWComplexOfMapsToSkeletonLTAux h hg hA
    RelCWComplex.map n ((relCWComplexOfMapsToSkeletonLTAuxCellEquiv h hg hA n).symm (.inl c)) x =
      j (RelCWComplex.map n c x) := by
  let := h.relCWComplex
  let := rangeRelCWComplex h hA
  set k := ((isClosedEmbedding_right h).relCWComplexCellEquiv image_univ hA n).symm c
  have h₁ := map_relCWComplexTrans_inl (cellFrontier_inter_range_subset_skeletonLT h hg hA) n k
  have h₂ := (isClosedEmbedding_right h).coe_map_relCWComplex image_univ hA n k
  exact (congrArg (fun e : PartialEquiv _ _ ↦ e x) h₁).trans
    ((congrFun h₂ x).trans (by simp [k]))

private theorem relCWComplexOfMapsToSkeletonLTAux_map_inr [T2Space P] {A' : Set P}
    (hA : j '' A = A')
    (n : ℕ) (c : cell C n) (x : closedBall (0 : Fin n → ℝ) 1) :
    letI := relCWComplexOfMapsToSkeletonLTAux h hg hA
    RelCWComplex.map n ((relCWComplexOfMapsToSkeletonLTAuxCellEquiv h hg hA n).symm (.inr c)) x =
      i ⟨RelCWComplex.map n c x, closedCell_subset_complex n _ (mem_image_of_mem _ x.2)⟩ := by
  let := h.relCWComplex
  let := rangeRelCWComplex h hA
  set k := (h.relCWComplexCellEquiv n).symm c
  have h₁ := map_relCWComplexTrans_inr (cellFrontier_inter_range_subset_skeletonLT h hg hA) n k
  refine (congrArg (fun e : PartialEquiv (Fin n → ℝ) _ ↦ e x) h₁).trans
    ((h.relCWComplex_map_apply n k x).trans ?_)
  simp only [k, Equiv.apply_symm_apply]

/-- **Gluing a relative CW complex to a CW complex along a cellular map.** Let `C` be a CW complex
relative to `D`, let `W` be a CW complex relative to `A`, and let `P` be a pushout of the inclusion
`D → C` along `g : D → W`, with maps `i : C → P` and `j : W → P`. If `g` maps the part in `D` of
the boundary of every `n`-cell of `C` into the skeleton `skeletonLT W n`, then `P` is a CW complex
relative to the image of `A`. Its `n`-cells are those of `W` and those of `C`
(`CategoryTheory.IsPushout.relCWComplexOfMapsToSkeletonLTCellEquiv`), with their characteristic
maps followed by `j` and by `i`. -/
@[instance_reducible]
def relCWComplexOfMapsToSkeletonLT : RelCWComplex (univ : Set P) (j '' A) :=
  haveI := h.t2Space
  relCWComplexOfMapsToSkeletonLTAux h hg rfl

/-- The `n`-cells of a pushout `P` of `D → C` along a cellular map to a relative CW complex `W` are
the `n`-cells of `W` together with those of `C`. -/
def relCWComplexOfMapsToSkeletonLTCellEquiv (n : ℕ) :
    letI := h.relCWComplexOfMapsToSkeletonLT hg
    cell (univ : Set P) n ≃ cell (univ : Set W) n ⊕ cell C n :=
  haveI := h.t2Space
  relCWComplexOfMapsToSkeletonLTAuxCellEquiv h hg rfl n

/-- The characteristic map of a cell of `W`, as a cell of the pushout `P`, is its characteristic
map in `W` followed by `j`. -/
@[simp]
theorem relCWComplexOfMapsToSkeletonLT_map_inl (n : ℕ) (c : cell (univ : Set W) n)
    (x : Fin n → ℝ) :
    letI := h.relCWComplexOfMapsToSkeletonLT hg
    RelCWComplex.map n ((h.relCWComplexOfMapsToSkeletonLTCellEquiv hg n).symm (.inl c)) x =
      j (RelCWComplex.map n c x) :=
  have := h.t2Space
  relCWComplexOfMapsToSkeletonLTAux_map_inl h hg rfl n c x

/-- The characteristic map of a cell of `C`, as a cell of the pushout `P`, is its characteristic
map in `C` followed by `i`. -/
@[simp]
theorem relCWComplexOfMapsToSkeletonLT_map_inr (n : ℕ) (c : cell C n)
    (x : closedBall (0 : Fin n → ℝ) 1) :
    letI := h.relCWComplexOfMapsToSkeletonLT hg
    RelCWComplex.map n ((h.relCWComplexOfMapsToSkeletonLTCellEquiv hg n).symm (.inr c)) x =
      i ⟨RelCWComplex.map n c x, closedCell_subset_complex n _ (mem_image_of_mem _ x.2)⟩ :=
  have := h.t2Space
  relCWComplexOfMapsToSkeletonLTAux_map_inr h hg rfl n c x

end Relative

section Absolute

variable [CWComplex (univ : Set W)]
  (hg : ∀ n (c : cell C n) (x : D), (x : X) ∈ cellFrontier n c →
    g x ∈ (skeletonLT (univ : Set W) n : Set W))

include h hg

/-- **Gluing a CW complex relative to `D` to a CW complex along a cellular map.** Let `C` be a CW
complex relative to `D`, let `W` be a CW complex, and let `P` be a pushout of the inclusion
`D → C` along `g : D → W`. If `g` maps the part in `D` of the boundary of every `n`-cell of `C`
into the skeleton `skeletonLT W n`, then `P` is a CW complex, whose `n`-cells are those of `W` and
those of `C` (`CategoryTheory.IsPushout.cwComplexOfMapsToSkeletonLTCellEquiv`). -/
@[instance_reducible]
def cwComplexOfMapsToSkeletonLT : CWComplex (univ : Set P) :=
  haveI := h.t2Space
  @RelCWComplex.toCWComplex _ _ _ (relCWComplexOfMapsToSkeletonLTAux h hg (image_empty _))

/-- The `n`-cells of a pushout `P` of `D → C` along a cellular map to a CW complex `W` are the
`n`-cells of `W` together with those of `C`. -/
def cwComplexOfMapsToSkeletonLTCellEquiv (n : ℕ) :
    letI := h.cwComplexOfMapsToSkeletonLT hg
    cell (univ : Set P) n ≃ cell (univ : Set W) n ⊕ cell C n :=
  haveI := h.t2Space
  relCWComplexOfMapsToSkeletonLTAuxCellEquiv h hg (image_empty _) n

/-- The characteristic map of a cell of `W`, as a cell of the CW complex `P`, is its characteristic
map in `W` followed by `j`. -/
@[simp]
theorem cwComplexOfMapsToSkeletonLT_map_inl (n : ℕ) (c : cell (univ : Set W) n)
    (x : Fin n → ℝ) :
    letI := h.cwComplexOfMapsToSkeletonLT hg
    RelCWComplex.map n ((h.cwComplexOfMapsToSkeletonLTCellEquiv hg n).symm (.inl c)) x =
      j (RelCWComplex.map n c x) :=
  have := h.t2Space
  relCWComplexOfMapsToSkeletonLTAux_map_inl h hg (image_empty _) n c x

/-- The characteristic map of a cell of `C`, as a cell of the CW complex `P`, is its characteristic
map in `C` followed by `i`. -/
@[simp]
theorem cwComplexOfMapsToSkeletonLT_map_inr (n : ℕ) (c : cell C n)
    (x : closedBall (0 : Fin n → ℝ) 1) :
    letI := h.cwComplexOfMapsToSkeletonLT hg
    RelCWComplex.map n ((h.cwComplexOfMapsToSkeletonLTCellEquiv hg n).symm (.inr c)) x =
      i ⟨RelCWComplex.map n c x, closedCell_subset_complex n _ (mem_image_of_mem _ x.2)⟩ :=
  have := h.t2Space
  relCWComplexOfMapsToSkeletonLTAux_map_inr h hg (image_empty _) n c x

/-- Gluing a finite CW complex relative to `D` to a finite CW complex along a cellular map gives a
finite CW complex. -/
theorem finite_cwComplexOfMapsToSkeletonLT [RelCWComplex.Finite C]
    [RelCWComplex.Finite (univ : Set W)] :
    letI := h.cwComplexOfMapsToSkeletonLT hg
    RelCWComplex.Finite (univ : Set P) :=
  letI := h.cwComplexOfMapsToSkeletonLT hg
  have := RelCWComplex.finite_cells_of_finite (C := (univ : Set W))
  have := RelCWComplex.finite_cells_of_finite (C := C)
  RelCWComplex.finite_of_finite_cells (.of_equiv ((Σ n, cell (univ : Set W) n) ⊕ Σ n, cell C n)
    ((Equiv.sigmaSumDistrib _ _).symm.trans
      (Equiv.sigmaCongrRight fun n ↦ (h.cwComplexOfMapsToSkeletonLTCellEquiv hg n).symm)))

end Absolute

end CategoryTheory.IsPushout

namespace TauCeti

attribute [local instance] sigmaDiskRelCWComplex

variable {W : Type u} [TopologicalSpace W] [T2Space W]

variable {ι : Type u} {n : ι → ℕ}

section Relative

variable {D : Set W} [RelCWComplex (univ : Set W) D]

variable (b : ∀ i, C(TopCat.diskBoundary.{u} (n i), W))

/-- The part in the boundary spheres of the boundary of an `m`-cell of the disjoint union of disks
is sent by the attaching map `TauCeti.sigmaDiskAttachingMap b` into `skeletonLT W m`, if each `b i`
lands in `skeletonLT W (n i)`. -/
private theorem sigmaDiskAttachingMap_mem_skeletonLT
    (hb : ∀ i x, b i x ∈ (skeletonLT (univ : Set W) (n i) : Set W)) (m : ℕ)
    (c : cell (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))) m)
    (x : univ.sigma fun i ↦ range (TopCat.diskBoundaryInclusion.{u} (n i)))
    (hx : (x : Σ i, TopCat.disk.{u} (n i)) ∈ cellFrontier m c) :
    TopCat.ofHom (sigmaDiskAttachingMap b) x ∈ (skeletonLT (univ : Set W) m : Set W) := by
  obtain ⟨y, hy, hxy⟩ := hx
  obtain ⟨s, rfl, hs⟩ := exists_map_sigmaDiskRelCWComplex_eq c hy
  have hxs : x = (sigmaDiskBoundaryHomeomorph n).symm s :=
    Subtype.ext ((hs ▸ hxy).symm.trans (coe_sigmaDiskBoundaryHomeomorph_symm_apply n s).symm)
  rw [hxs, ConcreteCategory.hom_ofHom, sigmaDiskAttachingMap_apply]
  exact hb s.1 s.2

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
  (IsPushout.of_hasPushout _ _).relCWComplexOfMapsToSkeletonLTAux
    (sigmaDiskAttachingMap_mem_skeletonLT b hb) hD

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
  ((IsPushout.of_hasPushout _ _).relCWComplexOfMapsToSkeletonLTAuxCellEquiv
    (sigmaDiskAttachingMap_mem_skeletonLT b hb) hD m).trans
      (Equiv.sumCongr (.refl _) (sigmaDiskRelCWComplexCellEquiv n m))

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
          (TopCat.ofHom (sigmaDiskAttachingMap b)) (map m j x) :=
  (IsPushout.of_hasPushout _ _).relCWComplexOfMapsToSkeletonLTAux_map_inl
    (sigmaDiskAttachingMap_mem_skeletonLT b hb) hD m j x

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
  have hcell : (sigmaDiskRelCWComplexCellEquiv n (n i)).symm ⟨i, rfl⟩ =
      sigmaDiskRelCWComplexCell n i :=
    (Equiv.symm_apply_eq _).2 (sigmaDiskRelCWComplexCellEquiv_cell n i).symm
  have h := (IsPushout.of_hasPushout _ _).relCWComplexOfMapsToSkeletonLTAux_map_inr
    (sigmaDiskAttachingMap_mem_skeletonLT b hb) hD (n i) (sigmaDiskRelCWComplexCell n i) x
  simp only [sigmaDiskAdjunctionRelCWComplexAuxCellEquiv, Equiv.symm_trans_apply,
    Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inr, hcell]
  refine h.trans (congrArg _ (Subtype.ext ?_))
  exact sigmaDiskRelCWComplex_map_apply n i x

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
  letI := (IsPushout.of_hasPushout (relCWBaseInclusion
    (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))))
      (TopCat.ofHom (sigmaDiskAttachingMap b))).rangeRelCWComplex (A := ∅) (image_empty _)
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
