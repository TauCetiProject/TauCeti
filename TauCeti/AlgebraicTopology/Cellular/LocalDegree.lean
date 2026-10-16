/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
public import TauCeti.AlgebraicTopology.Cellular.Incidence
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Basic

/-!
# Cellular incidence numbers as local degrees of attaching maps

Let `x` be a point of the open `n`-cell `i` of a relative CW complex. This file shows that the
local homology `Hₙ(Xⁿ, Xⁿ ∖ {x})` of the `n`-skeleton at `x` reads off the coefficient of `i` in
the cellular chain group `Hₙ(Xⁿ, Xⁿ⁻¹)`, and deduces that the cellular incidence numbers are the
local degrees of the attaching maps.

* The image of the fundamental class of `(Dⁿ, Sⁿ⁻¹)` under the characteristic map of `i`, read in
  `Hₙ(Xⁿ, Xⁿ ∖ {x})`, is the *local class* of `i` at `x` (`TauCeti.cellLocalClass`). It generates
  the local homology: the characteristic map, as a map of pairs `(Dⁿ, Sⁿ⁻¹) ⟶ (Xⁿ, Xⁿ ∖ {x})`,
  induces isomorphisms on relative singular homology in every degree.
* The inclusion of pairs `(Xⁿ, Xⁿ⁻¹) ⟶ (Xⁿ, Xⁿ ∖ {x})` sends the summand of `i` in the cellular
  chain group to the local class, and the summand of every other `n`-cell to zero, because the
  closed cells of the other `n`-cells miss `x`.
* Hence, with coefficients in a ring, pushing the reduced fundamental class of the boundary sphere
  of an `(n + 1)`-cell `j` through its attaching map into `Hₙ(Xⁿ)`, and then into
  `Hₙ(Xⁿ, Xⁿ ∖ {x})`, gives the incidence coefficient `[j : i]` times the local class of `i` at
  `x`. Over `ℤ`, the incidence numbers of the cellular differential are therefore the local
  degrees of the attaching maps at any point of the open cell of `i`. In Hatcher's cellular
  boundary formula `[j : i]` is instead the degree of the attaching map of `j` followed by the
  collapse of `Xⁿ` onto the sphere `Xⁿ / (Xⁿ ∖ eᵢ)`; the local form proved here avoids the
  quotient space.

Coefficients are an object of an abelian category with coproducts, as everywhere in relative
singular homology; the description of the cellular chain group as a coproduct needs exact
coproducts indexed by the `n`-cells, and the incidence formula needs a ring.

## Implementation notes

Let `y` be the coordinate of `x` in the open unit ball, and `B` the closed ball about the origin
of radius halfway between `‖y‖` and `1`. The characteristic map of `i` factors as
`(Dⁿ, Sⁿ⁻¹) ⟶ (Dⁿ, Dⁿ ∖ B) ⟶ (Xⁿ, Xⁿ ∖ φ(B)) ⟶ (Xⁿ, Xⁿ ∖ {x})`, where `φ` is the characteristic
map. The first map is a homotopy equivalence of pairs by the radial deformation
`TauCeti.radialPush`; the second induces isomorphisms by excision of the complements of the open
cell and of the open ball, which correspond under `φ`; the third induces isomorphisms because
local homology is constant along convex sets in a chart
(`TauCeti.isIso_singularHomologyMap_compl_of_chart`), applied to the inverse characteristic map
`TauCeti.openCellChart`.

## Main definitions and results

* `TauCeti.skeletonPairToComplSingleton`: the inclusion `(Xⁿ, Xⁿ⁻¹) ⟶ (Xⁿ, Xⁿ ∖ {x})`.
* `TauCeti.cellLocalClass`: the local class of the cell `i` at `x`.
* `TauCeti.isIso_singularHomologyMap_characteristicCellPairMap_comp_skeletonPairToComplSingleton`
  and `TauCeti.isIso_cellLocalClass`: the characteristic map computes the local homology at `x`,
  and the local class generates it.
* `TauCeti.ι_cellularChainGroupIso_inv_comp_singularHomologyMap_skeletonPairToComplSingleton` and
  `TauCeti.ι_cellularChainGroupIso_inv_comp_singularHomologyMap_skeletonPairToComplSingleton_of_ne`:
  the local homology at `x` reads off the coefficient of `i` in the cellular chain group.
* `TauCeti.singularHomologyπ_cellAttachingMap_eq_cellularIncidence_smul` and
  `TauCeti.cellularIncidence_eq_inv_cellLocalClass`: **the incidence numbers are local degrees of
  the attaching maps**.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2: the cellular boundary formula, and Proposition 2.30 for computing degrees by local
  degrees; Section 3.3 for local homology.
-/

public section

noncomputable section

open CategoryTheory Limits Topology Topology.RelCWComplex

universe w v u

namespace TauCeti

variable {X : Type w} [TopologicalSpace X] [T2Space X] {D : Set X}
  (C : Set X) [RelCWComplex C D]

/-- The inclusion of pairs `(Xⁿ, Xⁿ⁻¹) ⟶ (Xⁿ, Xⁿ ∖ {x})` for a point `x` of the `n`-skeleton
outside the `(n-1)`-skeleton. -/
def skeletonPairToComplSingleton {n : ℕ} (x : skeletonObj C (n + 1))
    (hx : (x : X) ∉ (skeletonLT C (n : ℕ∞) : Set X)) :
    skeletonPair C n ⟶ TopPair.ofSubset ({x}ᶜ : Set (skeletonObj C (n + 1))) :=
  TopPair.ofHom (𝟙 _)
    (TopCat.ofHom ⟨fun y ↦ ⟨⟨y.1, skeletonLT_subset_skeletonLT_succ C n y.2⟩,
      fun h ↦ hx (congrArg Subtype.val h ▸ y.2)⟩, by fun_prop⟩) rfl

/-- The ambient component of `TauCeti.skeletonPairToComplSingleton` is the identity. -/
@[simp]
lemma skeletonPairToComplSingleton_fst {n : ℕ} (x : skeletonObj C (n + 1))
    (hx : (x : X) ∉ (skeletonLT C (n : ℕ∞) : Set X)) :
    TopPair.Hom.fst (skeletonPairToComplSingleton C x hx) = 𝟙 _ :=
  (rfl)

section Coefficients

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

/-- **The local class of a cell at a point of its open cell.** For a point `x` of the open
`n`-cell `i`, the image of the fundamental class of `(Dⁿ, Sⁿ⁻¹)` under the characteristic map of
`i`, read in the local homology `Hₙ(Xⁿ, Xⁿ ∖ {x})` of the `n`-skeleton at `x`. -/
def cellLocalClass {n : ℕ} {i : cell C n} (x : skeletonObj C (n + 1))
    (hx : (x : X) ∈ openCell n i) :
    R ⟶ (TopPair.ofSubset ({x}ᶜ : Set (skeletonObj C (n + 1)))).singularHomology R n :=
  (singularHomologyDiskBoundaryPairIso R n).inv ≫
    TopPair.singularHomologyMap (characteristicCellPairMap C i ≫
      skeletonPairToComplSingleton C x (notMem_skeletonLT_of_mem_openCell n hx)) R n

/-- `TauCeti.cellLocalClass` is the inverse of `Hₙ(Dⁿ, Sⁿ⁻¹) ≅ R` followed by the map induced by
the characteristic map of the cell. -/
lemma cellLocalClass_def {n : ℕ} {i : cell C n} (x : skeletonObj C (n + 1))
    (hx : (x : X) ∈ openCell n i) :
    cellLocalClass C R x hx = (singularHomologyDiskBoundaryPairIso R n).inv ≫
      TopPair.singularHomologyMap (characteristicCellPairMap C i ≫
        skeletonPairToComplSingleton C x (notMem_skeletonLT_of_mem_openCell n hx)) R n :=
  (rfl)

/-- The map `Hₙ(Xⁿ) ⟶ Hₙ(Xⁿ, Xⁿ ∖ {x})` factors through the cellular chain group. -/
@[reassoc (attr := simp)]
lemma skeletonPairπ_comp_singularHomologyMap_skeletonPairToComplSingleton {n : ℕ}
    (x : skeletonObj C (n + 1)) (hx : (x : X) ∉ (skeletonLT C (n : ℕ∞) : Set X)) :
    skeletonPairπ C R n ≫
        TopPair.singularHomologyMap (skeletonPairToComplSingleton C x hx) R n =
      (TopPair.ofSubset ({x}ᶜ : Set (skeletonObj C (n + 1)))).singularHomologyπ R n := by
  have h := SSetPair.homologyπ_naturality
    (TopPair.toSSetPair.map (skeletonPairToComplSingleton C x hx)) R n
  have hid : (TopPair.toSSetPair.map (skeletonPairToComplSingleton C x hx)).right = 𝟙 _ :=
    TopCat.toSSet.map_id _
  -- The ambient spaces of the two pairs are the `n`-skeleton in two presentations, so
  -- `SSet.homologyMap_id` only matches up to unfolding them.
  rw [hid] at h
  erw [SSet.homologyMap_id, Category.id_comp] at h
  exact h.symm

section Coproduct

variable {n : ℕ} [HasExactColimitsOfShape (Discrete (cell C n)) A]

/-- On the summand of the cell `i`, the map from the cellular chain group to the local homology at
a point `x` of the open cell `i` is the local class of `i` at `x`. -/
@[reassoc (attr := simp)]
lemma ι_cellularChainGroupIso_inv_comp_singularHomologyMap_skeletonPairToComplSingleton
    {i : cell C n} (x : skeletonObj C (n + 1)) (hx : (x : X) ∈ openCell n i) :
    Sigma.ι (fun _ : cell C n ↦ R) i ≫ (cellularChainGroupIso C R n).inv ≫
        TopPair.singularHomologyMap
          (skeletonPairToComplSingleton C x (notMem_skeletonLT_of_mem_openCell n hx)) R n =
      cellLocalClass C R x hx := by
  rw [ι_cellularChainGroupIso_inv_eq_singularHomologyMap_characteristicCellPairMap_assoc,
    ← TopPair.singularHomologyMap_comp, cellLocalClass_def]

/-- **Other cells vanish in the local homology at a point of an open cell.** On the summand of a
cell `k ≠ i`, the map from the cellular chain group to the local homology at a point `x` of the
open cell `i` is zero: the closed cell of `k` misses `x`. -/
@[reassoc (attr := simp)]
lemma ι_cellularChainGroupIso_inv_comp_singularHomologyMap_skeletonPairToComplSingleton_of_ne
    {i k : cell C n} (x : skeletonObj C (n + 1)) (hx : (x : X) ∈ openCell n i) (hk : k ≠ i) :
    Sigma.ι (fun _ : cell C n ↦ R) k ≫ (cellularChainGroupIso C R n).inv ≫
        TopPair.singularHomologyMap
          (skeletonPairToComplSingleton C x (notMem_skeletonLT_of_mem_openCell n hx)) R n =
      0 := by
  rw [ι_cellularChainGroupIso_inv_eq_singularHomologyMap_characteristicCellPairMap_assoc,
    ← TopPair.singularHomologyMap_comp]
  have hmiss : ∀ z : TopCat.disk.{w} n,
      (TopPair.Hom.fst (characteristicCellPairMap C k) z : skeletonObj C (n + 1)) ≠ x := by
    intro z hz
    have hmem : (x : X) ∈ closedCell n k := by
      -- The lemma states the characteristic map with the `n`-skeleton written as
      -- `skeletonLT C (n + 1)`, which `skeletonObj C (n + 1)` unfolds to only up to the cast.
      rw [← hz]
      erw [coe_characteristicCellPairMap_fst_apply]
      exact ⟨_, ((EuclideanSpace.equiv (Fin n) ℝ).image_unitBallHomeomorph_closedBall ▸
        Set.mem_image_of_mem _ (z.down.2)), rfl⟩
    exact (disjoint_closedCell_openCell_of_ne n le_rfl
      (fun h ↦ hk (eq_of_heq (Sigma.mk.inj_iff.1 h).2))).notMem_of_mem_left hmem hx
  -- The characteristic map of `k` lands in `Xⁿ ∖ {x}`, the subspace of the target pair.
  rw [TopPair.singularHomologyMap_eq_zero_of_fac
    (characteristicCellPairMap C k ≫ skeletonPairToComplSingleton C x _) R
    (TopCat.ofHom ⟨fun z ↦ ⟨TopPair.Hom.fst (characteristicCellPairMap C k) z, hmiss z⟩,
      (TopPair.Hom.fst (characteristicCellPairMap C k)).hom.continuous.subtype_mk _⟩) rfl,
    Limits.comp_zero]

end Coproduct

section Generation

open Metric Set unitInterval

variable {n : ℕ} (x : skeletonObj C (n + 1))

/-- The inverse characteristic map of `i`, as a chart of the `n`-skeleton valued in the lifted
space `ULift (Fin n → ℝ)`, so that it lies in the universe of the skeleton. -/
private def cellChart (i : cell C n) :
    OpenPartialHomeomorph (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X) (ULift.{w} (Fin n → ℝ)) :=
  (openCellChart n i).transHomeomorph Homeomorph.ulift.symm

private lemma cellChart_apply (i : cell C n) (m : (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X)) :
    cellChart C i m = ULift.up ((map n i).symm m) := by
  rw [cellChart, OpenPartialHomeomorph.transHomeomorph_apply, Function.comp_apply,
    openCellChart_apply]
  rfl

private lemma cellChart_source (i : cell C n) :
    (cellChart C i).source = Subtype.val ⁻¹' openCell n i := by
  rw [cellChart, OpenPartialHomeomorph.transHomeomorph_source, openCellChart_source]

private lemma mem_cellChart_target_iff (i : cell C n) (u : ULift.{w} (Fin n → ℝ)) :
    u ∈ (cellChart C i).target ↔ ‖u‖ < 1 := by
  rw [cellChart, OpenPartialHomeomorph.transHomeomorph_target, openCellChart_target]
  exact mem_ball_zero_iff

/-- The radius of the closed ball in the cell `i` which is removed from the skeleton: halfway
between the coordinate of `x` and the unit sphere. -/
private def cellRadius (i : cell C n) : ℝ := (1 + ‖(map n i).symm x‖) / 2

variable {i : cell C n} (hx : (x : X) ∈ openCell n i)

include hx in
private lemma norm_map_symm_lt_cellRadius : ‖(map n i).symm x‖ < cellRadius C x i := by
  have := mem_ball_zero_iff.1 (map_symm_mem_ball n hx)
  rw [cellRadius]
  linarith

include hx in
private lemma cellRadius_lt_one : cellRadius C x i < 1 := by
  have := mem_ball_zero_iff.1 (map_symm_mem_ball n hx)
  rw [cellRadius]
  linarith

/-- The image in the skeleton of the closed ball of radius `cellRadius C x i` in the open cell. -/
private def cellBall (i : cell C n) : Set (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X) :=
  (cellChart C i).symm '' closedBall 0 (cellRadius C x i)

include hx in
private lemma closedBall_subset_target_cellChart :
    closedBall (0 : ULift.{w} (Fin n → ℝ)) (cellRadius C x i) ⊆ (cellChart C i).target :=
  fun u hu ↦ (mem_cellChart_target_iff C i u).2
    ((mem_closedBall_zero_iff.1 hu).trans_lt (cellRadius_lt_one C x hx))

include hx in
private lemma mem_cellBall_iff (m : (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X)) :
    m ∈ cellBall C x i ↔ (m : X) ∈ openCell n i ∧ ‖(map n i).symm m‖ ≤ cellRadius C x i := by
  rw [cellBall, (cellChart C i).symm_image_eq_source_inter_preimage
    (closedBall_subset_target_cellChart C x hx)]
  rw [cellChart_source, mem_inter_iff, mem_preimage, mem_preimage, mem_closedBall_zero_iff,
    cellChart_apply, ULift.norm_up]

include hx in
private lemma isClosed_cellBall : IsClosed (cellBall C x i) := by
  have hK : IsCompact (closedBall (0 : ULift.{w} (Fin n → ℝ)) (cellRadius C x i)) := by
    have h : closedBall (0 : ULift.{w} (Fin n → ℝ)) (cellRadius C x i) =
        Homeomorph.ulift ⁻¹' closedBall 0 (cellRadius C x i) := by
      ext u
      rw [mem_preimage, mem_closedBall_zero_iff, mem_closedBall_zero_iff]
      rfl
    rw [h, Homeomorph.isCompact_preimage]
    exact isCompact_closedBall _ _
  exact (hK.image_of_continuousOn ((cellChart C i).continuousOn_symm.mono
    (closedBall_subset_target_cellChart C x hx))).isClosed

include hx in
private lemma cellChart_mem_closedBall :
    cellChart C i x ∈ closedBall (0 : ULift.{w} (Fin n → ℝ)) (cellRadius C x i) :=
  mem_closedBall_zero_iff.2 (by
    rw [cellChart_apply, ULift.norm_up]
    exact (norm_map_symm_lt_cellRadius C x hx).le)

/-- The closed ball of radius `cellRadius C x i` in the disk, in sup-norm coordinates. -/
private def diskCore (i : cell C n) : Set (TopCat.disk.{w} n) :=
  {z | ‖(diskHomeomorphClosedBall n z : Fin n → ℝ)‖ ≤ cellRadius C x i}

/-- The boundary sphere of the disk, in sup-norm coordinates. -/
private def diskSphere (n : ℕ) : Set (TopCat.disk.{w} n) :=
  {z | ‖(diskHomeomorphClosedBall n z : Fin n → ℝ)‖ = 1}

include hx in
private lemma mapsTo_diskSphere_compl_diskCore :
    MapsTo (𝟙 (TopCat.disk.{w} n)) (diskSphere n) (diskCore C x i)ᶜ := by
  intro z (hz : _ = _) (hz' : _ ≤ _)
  rw [ConcreteCategory.id_apply, hz] at hz'
  exact (cellRadius_lt_one C x hx).not_ge hz'

include hx in
/-- The characteristic map sends the disk minus `diskCore` into the skeleton minus `cellBall`. -/
private lemma mapsTo_cellDiskHom_compl :
    MapsTo (cellDiskHom i) (diskCore C x i)ᶜ (cellBall C x i)ᶜ := by
  intro z hz hmem
  rw [mem_cellBall_iff C x hx] at hmem
  obtain ⟨hop, hle⟩ := hmem
  rw [coe_cellDiskHom_apply] at hop hle
  have hz1 := mem_closedBall_zero_iff.1 (diskHomeomorphClosedBall n z).2
  rcases hz1.lt_or_eq with hlt | heq
  · -- Inside the open ball the inverse characteristic map recovers the coordinate.
    have hinv : (map n i).symm (map n i (diskHomeomorphClosedBall n z)) =
        diskHomeomorphClosedBall n z :=
      (map n i).left_inv (by rw [source_eq]; exact mem_ball_zero_iff.2 hlt)
    have hle' : ‖(diskHomeomorphClosedBall n z : Fin n → ℝ)‖ ≤ cellRadius C x i := hinv ▸ hle
    exact hz hle'
  · -- On the boundary sphere the characteristic map lands in the `(n-1)`-skeleton.
    exact notMem_skeletonLT_of_mem_openCell n hop (cellFrontier_subset_skeletonLT n i
      ⟨_, mem_sphere_zero_iff_norm.2 heq, rfl⟩)

include hx in
private lemma isIso_singularHomologyMap_compl_cellBall (k : ℕ) :
    IsIso (TopPair.singularHomologyMap (TopPair.ofSubsetMap
      (𝟙 (TopCat.of (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X)))
      ((cellChart C i).mapsTo_id_compl_symm_image (x := x) (by rw [cellChart_source]; exact hx)
        (cellChart_mem_closedBall C x hx))) R k) :=
  isIso_singularHomologyMap_compl_of_chart R (cellChart C i)
    (by rw [cellChart_source]; exact hx)
    ((convex_closedBall _ _).starConvex (cellChart_mem_closedBall C x hx))
    (cellChart_mem_closedBall C x hx) isBounded_closedBall isClosed_closedBall
    (isClosed_cellBall C x hx) (closedBall_subset_target_cellChart C x hx) k

/-- The interior of the disk, in sup-norm coordinates. -/
private def diskInterior (n : ℕ) : Set (TopCat.disk.{w} n) :=
  {z | ‖(diskHomeomorphClosedBall n z : Fin n → ℝ)‖ < 1}

private lemma isOpen_diskInterior : IsOpen (diskInterior.{w} n) :=
  isOpen_lt (continuous_norm.comp (continuous_subtype_val.comp
    (diskHomeomorphClosedBall n).continuous)) continuous_const

private lemma isClosed_diskCore (i : cell C n) : IsClosed (diskCore C x i) :=
  isClosed_le (continuous_norm.comp (continuous_subtype_val.comp
    (diskHomeomorphClosedBall n).continuous)) continuous_const

include hx in
private lemma diskCore_subset_diskInterior : diskCore C x i ⊆ diskInterior n :=
  fun z (hz : ‖(diskHomeomorphClosedBall n z : Fin n → ℝ)‖ ≤ cellRadius C x i) ↦
    hz.trans_lt (cellRadius_lt_one C x hx)

/-- On the interior of the disk, the characteristic map is an embedding into the skeleton. -/
private lemma isEmbedding_cellDiskHom_restrict (i : cell C n) :
    IsEmbedding ((diskInterior n).domRestrict (cellDiskHom i)) := by
  -- Read the interior of the disk as the open ball through `diskHomeomorphClosedBall`, then
  -- apply the homeomorphism of the open ball onto the open cell.
  have he₁ : IsEmbedding fun z : diskInterior.{w} n ↦
      (⟨(diskHomeomorphClosedBall n z : Fin n → ℝ), mem_ball_zero_iff.2 z.2⟩ :
        ball (0 : Fin n → ℝ) 1) :=
    (IsEmbedding.subtypeVal.comp ((diskHomeomorphClosedBall n).isEmbedding.comp
      IsEmbedding.subtypeVal)).codRestrict _ _
  have hsub : openCell n i ⊆ (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X) := by
    exact_mod_cast openCell_subset_skeletonLT n i
  have he₂ := (IsEmbedding.inclusion hsub).comp (openCellHomeomorph n i).isEmbedding
  convert he₂.comp he₁ using 1
  funext z
  exact Subtype.ext ((coe_cellDiskHom_apply i z.1).trans (openCellHomeomorph_apply n i
    ⟨(diskHomeomorphClosedBall n z : Fin n → ℝ), mem_ball_zero_iff.2 z.2⟩).symm)


include hx in
/-- **Excision onto the open cell.** The characteristic map induces isomorphisms from the
homology of the disk relative to the complement of `diskCore` to that of the skeleton relative
to the complement of `cellBall`. -/
private lemma isIso_singularHomologyMap_cellDiskHom (k : ℕ) :
    IsIso (TopPair.singularHomologyMap (TopPair.ofSubsetMap (cellDiskHom i)
      (mapsTo_cellDiskHom_compl C x hx)) R k) := by
  have := TopPair.isIso_singularHomologyMap_excisionMap_of_isClosed_subset R
    (X := TopCat.disk.{w} n) isOpen_diskInterior (isClosed_diskCore C x i)
    (diskCore_subset_diskInterior C x hx) k
  suffices h : IsIso (TopPair.singularHomologyMap
      (TopPair.excisionMap (diskInterior n) (diskCore C x i)ᶜ ≫
        TopPair.ofSubsetMap (cellDiskHom i) (mapsTo_cellDiskHom_compl C x hx))
      R k) by
    rw [TopPair.singularHomologyMap_comp] at h
    exact IsIso.of_isIso_comp_left
      (TopPair.singularHomologyMap (TopPair.excisionMap (diskInterior n) (diskCore C x i)ᶜ) R k) _
  -- On the interior of the disk the characteristic map is an embedding onto the open cell; the
  -- open cell and the complement of `cellBall` cover the skeleton.
  set g := TopPair.excisionMap (diskInterior n) (diskCore C x i)ᶜ ≫
    TopPair.ofSubsetMap (cellDiskHom i) (mapsTo_cellDiskHom_compl C x hx)
  have hg : ∀ z, TopPair.Hom.fst g z = cellDiskHom i z.1 := fun z ↦ by
    rw [TopPair.Hom.fst_comp, ConcreteCategory.comp_apply, TopPair.excisionMap_fst_apply]
    exact TopPair.ofSubsetMap_fst_apply _ _ _
  refine TopPair.isIso_singularHomologyMap_of_open_cover R g ?_ ?_
    (fun b : Bool ↦ bif b
      then (Subtype.val ⁻¹' openCell n i : Set (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X))
      else (cellBall C x i)ᶜ)
    (fun b ↦ ?_) ?_ (fun b ↦ ?_) k
  · have hg' : (ConcreteCategory.hom (TopPair.Hom.fst g) : diskInterior n → _) =
        (diskInterior n).domRestrict (cellDiskHom i) := funext hg
    have := isEmbedding_cellDiskHom_restrict C i
    rw [← hg'] at this
    exact this
  · intro z hz
    rw [TopPair.range_ofSubset_map, hg] at hz
    rw [TopPair.range_ofSubset_map]
    intro hcore
    refine hz ((mem_cellBall_iff C x hx _).2 ⟨⟨_, mem_ball_zero_iff.2 z.2,
      (coe_cellDiskHom_apply i z.1).symm⟩, ?_⟩)
    rw [coe_cellDiskHom_apply i z.1,
      (map n i).left_inv (by rw [source_eq]; exact mem_ball_zero_iff.2 z.2)]
    exact hcore
  · cases b
    · exact (isClosed_cellBall C x hx).isOpen_compl
    · exact isOpen_preimage_val_openCell n subset_rfl i
  · refine eq_univ_of_forall fun m ↦ mem_iUnion.2 ?_
    by_cases hm : m ∈ cellBall C x i
    · exact ⟨true, ((mem_cellBall_iff C x hx m).1 hm).1⟩
    · exact ⟨false, hm⟩
  · cases b
    · exact Or.inl TopPair.range_ofSubset_map.symm.subset
    · refine Or.inr fun (m : (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X))
        (hm : (m : X) ∈ openCell n i) ↦ ?_
      have hb : ‖(map n i).symm m‖ < 1 := mem_ball_zero_iff.1 (map_symm_mem_ball n hm)
      refine ⟨⟨(diskHomeomorphClosedBall n).symm
        ⟨(map n i).symm m, mem_closedBall_zero_iff.2 hb.le⟩, ?_⟩, ?_⟩
      · rw [diskInterior, mem_ofPred_eq, Homeomorph.apply_symm_apply]
        exact hb
      · refine (hg _).trans (Subtype.ext ?_)
        rw [coe_cellDiskHom_apply,
          Homeomorph.apply_symm_apply]
        exact map_map_symm n hm

/-- The radial deformation `TauCeti.radialPush r` of the disk, in sup-norm coordinates. -/
private def diskRadialPush {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    C(I × TopCat.disk.{w} n, TopCat.disk.{w} n) where
  toFun q := (diskHomeomorphClosedBall n).symm
    ⟨radialPush r q.1 (diskHomeomorphClosedBall n q.2 : Fin n → ℝ), mem_closedBall_zero_iff.2
      (norm_radialPush_le_one hr hr1 q.1
        (mem_closedBall_zero_iff.1 (diskHomeomorphClosedBall n q.2).2))⟩
  continuous_toFun := (diskHomeomorphClosedBall n).symm.continuous.comp
    (Continuous.subtype_mk ((continuous_radialPush hr.le).comp (continuous_fst.prodMk
      (continuous_subtype_val.comp ((diskHomeomorphClosedBall n).continuous.comp
        continuous_snd)))) _)

private lemma coe_diskHomeomorphClosedBall_diskRadialPush {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (q : I × TopCat.disk.{w} n) :
    (diskHomeomorphClosedBall n (diskRadialPush hr hr1 q) : Fin n → ℝ) =
      radialPush r q.1 (diskHomeomorphClosedBall n q.2 : Fin n → ℝ) := by
  rw [diskRadialPush, ContinuousMap.coe_mk, Homeomorph.apply_symm_apply]

/-- The radial deformation of the disk, from the identity to the map pushing the shell
`r ≤ ‖y‖` onto the boundary sphere. -/
private def diskRadialHomotopy {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    (ContinuousMap.id (TopCat.disk.{w} n)).Homotopy ((diskRadialPush hr hr1).curry 1) where
  toContinuousMap := diskRadialPush hr hr1
  map_zero_left z := (diskHomeomorphClosedBall n).injective <| Subtype.ext <|
    (coe_diskHomeomorphClosedBall_diskRadialPush hr hr1 (0, z)).trans (radialPush_zero _ _)
  map_one_left _ := rfl

include hx in
/-- **The radial deformation.** The inclusion of the boundary sphere of the disk into the
complement of `diskCore` induces isomorphisms on relative homology. -/
private lemma isIso_singularHomologyMap_diskSphere (k : ℕ) :
    IsIso (TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 (TopCat.disk.{w} n))
      (mapsTo_diskSphere_compl_diskCore C x hx)) R k) := by
  have hr : 0 < cellRadius C x i :=
    (norm_nonneg _).trans_lt (norm_map_symm_lt_cellRadius C x hx)
  have hr1 : cellRadius C x i ≤ 1 := (cellRadius_lt_one C x hx).le
  let H := diskRadialHomotopy (n := n) hr hr1
  have hH (t : I) (z : TopCat.disk.{w} n) :
      (diskHomeomorphClosedBall n (H (t, z)) : Fin n → ℝ) =
        radialPush (cellRadius C x i) t (diskHomeomorphClosedBall n z : Fin n → ℝ) :=
    coe_diskHomeomorphClosedBall_diskRadialPush hr hr1 (t, z)
  have hpush : MapsTo (TopCat.ofHom ((diskRadialPush hr hr1).curry 1)) (diskCore C x i)ᶜ
      (diskSphere n) := fun z hz ↦ by
    have hz' : cellRadius C x i < ‖(diskHomeomorphClosedBall n z : Fin n → ℝ)‖ := not_le.1 hz
    have h := norm_radialPush_one hr hz'.le
    rwa [← hH 1 z] at h
  have h₁ : MapsTo (𝟙 _ ≫ TopCat.ofHom ((diskRadialPush hr hr1).curry 1)) (diskSphere n)
      (diskSphere n) :=
    fun z hz ↦ hpush (mapsTo_diskSphere_compl_diskCore C x hx hz)
  have h₂ : MapsTo (TopCat.ofHom ((diskRadialPush hr hr1).curry 1) ≫ 𝟙 _) (diskCore C x i)ᶜ
      (diskCore C x i)ᶜ :=
    fun z hz ↦ mapsTo_diskSphere_compl_diskCore C x hx (hpush hz)
  refine TopPair.isIso_singularHomologyMap _ (TopPair.ofSubsetMap _ hpush) ?_ ?_ R k
  · -- The deformation fixes the boundary sphere.
    rw [← TopPair.ofSubsetMap_comp _ _ _ _ h₁, ← TopPair.ofSubsetMap_id (fun _ hz ↦ hz)]
    refine TopPair.ofSubsetHomotopy H.symm fun t z (hz : _ = _) ↦ ?_
    -- `ofSubsetHomotopy` sees the homotopy through the `TopCat` composite, so its `symm_apply`
    -- lemma does not match syntactically; restate the goal on the deformation.
    change ‖(diskHomeomorphClosedBall n (H (σ t, z)) : Fin n → ℝ)‖ = 1
    rw [hH, radialPush_of_norm_eq_one hr hr1 _ hz]
    exact hz
  · -- The deformation does not decrease norms, so it keeps the complement of `diskCore`.
    rw [← TopPair.ofSubsetMap_comp _ _ _ _ h₂, ← TopPair.ofSubsetMap_id (fun _ hz ↦ hz)]
    refine TopPair.ofSubsetHomotopy H.symm fun t z hz ↦ ?_
    rw [mem_compl_iff] at hz ⊢
    intro hle
    apply hz
    have hle' : ‖(diskHomeomorphClosedBall n (H (σ t, z)) : Fin n → ℝ)‖ ≤ cellRadius C x i :=
      hle
    rw [hH] at hle'
    exact (norm_le_norm_radialPush hr hr1 _
      (mem_closedBall_zero_iff.1 (diskHomeomorphClosedBall n z).2)).trans hle'

/-- The disk pair `(Dⁿ, Sⁿ⁻¹)` is the disk relative to `diskSphere n`. -/
private def diskBoundaryPairToDiskSphere (n : ℕ) :
    diskBoundaryPair.{w} n ⟶ TopPair.ofSubset (diskSphere.{w} n) :=
  TopPair.ofHom (𝟙 _) (TopCat.ofHom ⟨fun s ↦ ⟨TopCat.diskBoundaryInclusion n s,
    (norm_diskHomeomorphClosedBall_eq_one_iff _).2 ⟨s, rfl⟩⟩,
    (TopCat.diskBoundaryInclusion n).hom.continuous.subtype_mk _⟩) rfl

private lemma isIso_diskBoundaryPairToDiskSphere (n : ℕ) :
    IsIso (diskBoundaryPairToDiskSphere.{w} n) := by
  have : IsIso (TopPair.Hom.fst (diskBoundaryPairToDiskSphere.{w} n)) := IsIso.id _
  refine TopPair.isIso_of_isIso_fst_of_surjective_snd _ fun z ↦ ?_
  obtain ⟨s, hs⟩ := (norm_diskHomeomorphClosedBall_eq_one_iff z.1).1 z.2
  exact ⟨s, Subtype.ext hs⟩

include hx in
/-- **The characteristic map of a cell computes the local homology at a point of the open cell.**
For a point `x` of the open `n`-cell `i`, the characteristic map of `i`, as a map of pairs
`(Dⁿ, Sⁿ⁻¹) ⟶ (Xⁿ, Xⁿ ∖ {x})`, induces isomorphisms on relative singular homology in every
degree. -/
theorem isIso_singularHomologyMap_characteristicCellPairMap_comp_skeletonPairToComplSingleton
    (k : ℕ) :
    IsIso (TopPair.singularHomologyMap (characteristicCellPairMap C i ≫
      skeletonPairToComplSingleton C x (notMem_skeletonLT_of_mem_openCell n hx)) R k) := by
  have hfac : characteristicCellPairMap C i ≫
      skeletonPairToComplSingleton C x (notMem_skeletonLT_of_mem_openCell n hx) =
      diskBoundaryPairToDiskSphere n ≫
        TopPair.ofSubsetMap (𝟙 _) (mapsTo_diskSphere_compl_diskCore C x hx) ≫
        TopPair.ofSubsetMap (cellDiskHom i) (mapsTo_cellDiskHom_compl C x hx) ≫
        TopPair.ofSubsetMap (𝟙 (TopCat.of (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X)))
          ((cellChart C i).mapsTo_id_compl_symm_image (x := x) (by rw [cellChart_source]; exact hx)
            (cellChart_mem_closedBall C x hx)) := by
    apply TopPair.hom_ext_of_fst
    ext z
    refine (ConcreteCategory.congr_hom (characteristicCellPairMap_fst C i) z).trans ?_
    rw [TopPair.Hom.fst_comp, TopPair.Hom.fst_comp, TopPair.Hom.fst_comp, TopPair.ofSubsetMap_fst,
      TopPair.ofSubsetMap_fst]
    -- The last factor is stated on `TopCat.of (skeletonLT C ↑(n + 1))`, the ambient space of the
    -- target pair only up to unfolding `TopPair.ofSubset`.
    erw [TopPair.ofSubsetMap_fst]
    rfl
  have := isIso_diskBoundaryPairToDiskSphere.{w} n
  have : IsIso (TopPair.singularHomologyMap (diskBoundaryPairToDiskSphere.{w} n) R k) :=
    ⟨TopPair.singularHomologyMap (inv (diskBoundaryPairToDiskSphere.{w} n)) R k,
      by rw [← TopPair.singularHomologyMap_comp, IsIso.hom_inv_id, TopPair.singularHomologyMap_id],
      by rw [← TopPair.singularHomologyMap_comp, IsIso.inv_hom_id, TopPair.singularHomologyMap_id]⟩
  have := isIso_singularHomologyMap_diskSphere C R x hx k
  have := isIso_singularHomologyMap_cellDiskHom C R x hx k
  have := isIso_singularHomologyMap_compl_cellBall C R x hx k
  rw [hfac, TopPair.singularHomologyMap_comp, TopPair.singularHomologyMap_comp,
    TopPair.singularHomologyMap_comp]
  -- The four factors are invertible by the instances above, which match them only up to the
  -- presentation of the ambient spaces, so they are supplied by `‹_›` rather than by instance
  -- search.
  exact IsIso.comp_isIso' ‹_› (IsIso.comp_isIso' ‹_› (IsIso.comp_isIso' ‹_› ‹_›))

/-- **The local class of a cell generates the local homology** `Hₙ(Xⁿ, Xⁿ ∖ {x})` of the
`n`-skeleton at a point `x` of its open cell. -/
instance isIso_cellLocalClass : IsIso (cellLocalClass C R x hx) := by
  have := isIso_singularHomologyMap_characteristicCellPairMap_comp_skeletonPairToComplSingleton
    C R x hx n
  rw [cellLocalClass_def]
  infer_instance

end Generation

end Coefficients

section Ring

variable (R : Type w) [Ring R] {n : ℕ}

/-- The cellular basis vector of the cell `i` maps to the local class of `i` at a point `x` of its
open cell. -/
lemma singularHomologyMap_skeletonPairToComplSingleton_cellularChainBasis_self {i : cell C n}
    (x : skeletonObj C (n + 1)) (hx : (x : X) ∈ openCell n i) :
    TopPair.singularHomologyMap
        (skeletonPairToComplSingleton C x (notMem_skeletonLT_of_mem_openCell n hx))
        (ModuleCat.of R R) n (cellularChainBasis C R n i) =
      cellLocalClass C (ModuleCat.of R R) x hx 1 := by
  rw [cellularChainBasis_apply, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply,
    ι_cellularChainGroupIso_inv_comp_singularHomologyMap_skeletonPairToComplSingleton]

/-- The cellular basis vector of a cell `j ≠ i` vanishes in the local homology at a point `x` of
the open cell `i`. -/
lemma singularHomologyMap_skeletonPairToComplSingleton_cellularChainBasis_of_ne
    {i j : cell C n} (x : skeletonObj C (n + 1)) (hx : (x : X) ∈ openCell n i) (hj : j ≠ i) :
    TopPair.singularHomologyMap
        (skeletonPairToComplSingleton C x (notMem_skeletonLT_of_mem_openCell n hx))
        (ModuleCat.of R R) n (cellularChainBasis C R n j) = 0 := by
  rw [cellularChainBasis_apply, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply,
    ι_cellularChainGroupIso_inv_comp_singularHomologyMap_skeletonPairToComplSingleton_of_ne C _ x
      hx hj]
  rfl

/-- **Incidence numbers are local degrees of attaching maps.** Send the reduced fundamental class
of the boundary sphere of an `(n + 1)`-cell `j` through its attaching map into `Hₙ(Xⁿ)`, and then
into the local homology `Hₙ(Xⁿ, Xⁿ ∖ {x})` at a point `x` of the open `n`-cell `i`. The result is
the incidence coefficient of `i` in the cellular boundary of `j` times the local class of `i`
at `x`. -/
theorem singularHomologyπ_cellAttachingMap_eq_cellularIncidence_smul {i : cell C n}
    (x : skeletonObj C (n + 1)) (hx : (x : X) ∈ openCell n i) (j : cell C (n + 1)) :
    (TopPair.ofSubset ({x}ᶜ : Set (skeletonObj C (n + 1)))).singularHomologyπ (ModuleCat.of R R) n
        (SSet.homologyMap (TopCat.toSSet.map (cellAttachingMap j)) (ModuleCat.of R R) n
          ((reducedSingularHomologyι (ModuleCat.of R R) n).app (TopCat.diskBoundary.{w} (n + 1))
            ((reducedSingularHomologyTopCatSphereIso (ModuleCat.of R R) n).inv 1))) =
      cellularIncidence C R n i j • cellLocalClass C (ModuleCat.of R R) x hx 1 := by
  set a := SSet.homologyMap (TopCat.toSSet.map (cellAttachingMap j)) (ModuleCat.of R R) n
    ((reducedSingularHomologyι (ModuleCat.of R R) n).app (TopCat.diskBoundary.{w} (n + 1))
      ((reducedSingularHomologyTopCatSphereIso (ModuleCat.of R R) n).inv 1))
  have hπ := congrArg (fun f ↦ f a)
    (skeletonPairπ_comp_singularHomologyMap_skeletonPairToComplSingleton C (ModuleCat.of R R) x
      (notMem_skeletonLT_of_mem_openCell n hx))
  simp only [ConcreteCategory.comp_apply] at hπ
  -- The two presentations of the `n`-skeleton agree only up to unfolding, so `hπ` is used as a
  -- term rather than rewritten.
  refine hπ.symm.trans ?_
  rw [← (cellularChainBasis C R n).linearCombination_repr (skeletonPairπ C (ModuleCat.of R R) n a),
    ← cellularBoundaryColumn_eq_attaching, Finsupp.linearCombination_apply, map_finsuppSum,
    Finsupp.sum, Finset.sum_eq_single i]
  · rw [map_smul, singularHomologyMap_skeletonPairToComplSingleton_cellularChainBasis_self,
      cellularBoundaryColumn_apply]
  · intro l _ hl
    rw [map_smul, singularHomologyMap_skeletonPairToComplSingleton_cellularChainBasis_of_ne C R x
      hx hl, smul_zero]
  · intro hi
    rw [Finsupp.notMem_support_iff.1 hi, zero_smul, map_zero]

/-- **The incidence numbers are the local degrees of the attaching maps.** For a point `x` of
the open `n`-cell `i` and an `(n + 1)`-cell `j`, the incidence coefficient of `i` in the cellular
boundary of `j` is the coordinate, with respect to the local class of `i` at `x`, of the image of
the reduced fundamental class of the boundary sphere of `j` under its attaching map, read in the
local homology `Hₙ(Xⁿ, Xⁿ ∖ {x})`. -/
theorem cellularIncidence_eq_inv_cellLocalClass {i : cell C n} (x : skeletonObj C (n + 1))
    (hx : (x : X) ∈ openCell n i) (j : cell C (n + 1)) :
    cellularIncidence C R n i j =
      inv (cellLocalClass C (ModuleCat.of R R) x hx)
        ((TopPair.ofSubset ({x}ᶜ : Set (skeletonObj C (n + 1)))).singularHomologyπ
          (ModuleCat.of R R) n
          (SSet.homologyMap (TopCat.toSSet.map (cellAttachingMap j)) (ModuleCat.of R R) n
            ((reducedSingularHomologyι (ModuleCat.of R R) n).app (TopCat.diskBoundary.{w} (n + 1))
              ((reducedSingularHomologyTopCatSphereIso (ModuleCat.of R R) n).inv 1)))) := by
  rw [singularHomologyπ_cellAttachingMap_eq_cellularIncidence_smul C R x hx j, map_smul,
    ← ModuleCat.comp_apply,
    IsIso.hom_inv_id, ModuleCat.id_apply, smul_eq_mul, mul_one]

end Ring

end TauCeti
