/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.LocalDegree
public import TauCeti.AlgebraicTopology.Cellular.LocalCoefficients.Coproduct
public import TauCeti.AlgebraicTopology.Singular.Twisted.Acyclic
public import TauCeti.AlgebraicTopology.Singular.Twisted.DiskSphere

/-!
# Cellular chains with local coefficients in local homology at the centres of the cells

Let `C ⊆ X` be a relative CW complex with skeleta `Xⁿ`, let `L` be a local coefficient system on
`C`, and let `x` be a point of `Xⁿ` off `Xⁿ⁻¹`. The identity of `Xⁿ` is a map of pairs
`(Xⁿ, Xⁿ⁻¹) ⟶ (Xⁿ, Xⁿ ∖ {x})` (`TauCeti.skeletonPairToComplSingleton`). On the cellular chain
group it induces the **localization at `x`**

`Hₙ(Xⁿ, Xⁿ⁻¹; L) ⟶ Hₙ(Xⁿ, Xⁿ ∖ {x}; L)`

(`TauCeti.twistedCellularChainLocalization`), into the local homology of the `n`-skeleton at `x`
with coefficients in `L`. The cellular chain group is the coproduct of the contributions
`Hₙ(Dⁿ, Sⁿ⁻¹; χⱼ*L)` of the `n`-cells `j`, along their characteristic maps
(`TauCeti.isColimitCofanTwistedHomologyMapCharacteristicCellPairMap`), and the localization at a
point of the open cell of an `n`-cell `i` separates them:

* at the centre `x = χᵢ(0)`, the contribution of `i` maps isomorphically
  (`isIso_twistedHomologyMap_characteristicCellPairMap_comp_twistedCellularChainLocalization`);
* the contribution of every other `n`-cell maps to zero
  (`twistedHomologyMap_characteristicCellPairMap_comp_twistedCellularChainLocalization_eq_zero`),
  because its closed cell misses the open cell of `i`.

So the localization at the centre of `i` reads off the coefficient of `i` of a cellular chain with
local coefficients through local homology, without the decomposition of the chain group. This is
the local-coefficient form of the reading of cellular coordinates in
`TauCeti.AlgebraicTopology.Cellular.LocalDegree`, and the cellular counterpart of the localization
of the first page of the Serre spectral sequence along the fibre over the centre of a cell in
`TauCeti.AlgebraicTopology.Singular.Fibration.TopCell`. Together they let the first differential of
the Serre spectral sequence of a fibration and the cellular differential with coefficients in its
fibre homology be compared one target cell at a time.

## The computation

The characteristic map of `i`, as a map of pairs `(Dⁿ, Sⁿ⁻¹) ⟶ (Xⁿ, Xⁿ ∖ {x})`, factors as

`(Dⁿ, Sⁿ⁻¹) ⟶ (Dⁿ, Dⁿ ∖ {0}) ⟶ (Xⁿ, Xⁿ ∖ {x})`.

The first map induces isomorphisms with any local coefficients, since the boundary sphere includes
into the punctured disk as a homotopy equivalence
(`TauCeti.isIso_twistedHomologyMap_diskBoundaryPairToComplDiskCenter`). For the second, excise the
boundary sphere from `(Dⁿ, Dⁿ ∖ {0})`
(`TopPair.isIso_twistedHomologyMap_excisionMap_of_isClosed_subset`) and the complement of the open
cell from `(Xⁿ, Xⁿ ∖ {x})` (`TopPair.isIso_twistedHomologyMap_of_open_cover`): the characteristic
map embeds the interior of the disk onto the open cell (`TauCeti.isEmbedding_cellDiskHom_restrict`),
which is open in `Xⁿ` (`TauCeti.isOpen_preimage_val_openCell`).

## Main definitions and results

* `TauCeti.twistedCellularChainLocalization`: the localization of cellular chains with local
  coefficients at a point of `Xⁿ` off `Xⁿ⁻¹`.
* `TauCeti.isIso_twistedHomologyMap_characteristicCellPairMap_comp_skeletonPairToComplSingleton`:
  at the centre `x` of an `n`-cell `i`, the characteristic map of `i` induces isomorphisms
  `Hₖ(Dⁿ, Sⁿ⁻¹; χᵢ*K) ≅ Hₖ(Xⁿ, Xⁿ ∖ {x}; K)` for every local system `K` on `Xⁿ`, in every degree.
* `TauCeti.twistedHomologyMap_characteristicCellPairMap_comp_skeletonPairToComplSingleton_eq_zero`:
  the characteristic map of an `n`-cell `k ≠ i` induces zero into the local homology at any point
  of the open cell of `i`.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2 (the cellular boundary formula and local degrees),
  Section 3.3 (local homology) and Section 3.H (local coefficients).
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter VI.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Set Topology Topology.RelCWComplex

universe w v u

namespace TauCeti

variable {R : Type u} [Ring R] {X : Type w} [TopologicalSpace X] [T2Space X] {D : Set X}
  (C : Set X) [RelCWComplex C D]

/-! ### The characteristic map near the centre of a cell -/

section Disk

/-- The centre of the disk is sent to the centre of the closed unit ball of the sup norm. -/
private lemma coe_diskHomeomorphClosedBall_diskCenter (n : ℕ) :
    (diskHomeomorphClosedBall n (diskCenter.{w} n) : Fin n → ℝ) = 0 := by
  rw [coe_diskHomeomorphClosedBall_apply]
  -- The centre of `TopCat.disk n` is `0` only after unfolding its `ULift`, so `erw` is used.
  erw [coe_diskCenter_down, ContinuousLinearEquiv.unitBallHomeomorph_apply, map_zero,
    gaugeRescale_zero]

private lemma diskCenter_mem_diskInterior (n : ℕ) : diskCenter.{w} n ∈ diskInterior.{w} n := by
  rw [mem_diskInterior_iff, coe_diskHomeomorphClosedBall_diskCenter, norm_zero]
  exact zero_lt_one

/-- The inclusion `(B, B ∖ {0}) ⟶ (Dⁿ, Dⁿ ∖ {0})` of the interior `B` of the disk. -/
private abbrev diskInteriorPairι (n : ℕ) :=
  TopPair.excisionMap (diskInterior.{w} n) ({diskCenter n}ᶜ : Set (TopCat.disk.{w} n))

/-- **Excision of the boundary sphere** from `(Dⁿ, Dⁿ ∖ {0})`, with local coefficients. -/
private lemma isIso_twistedHomologyMap_diskInteriorPairι (n k : ℕ)
    (K : LocalCoefficientSystem.{u, w, max w v} R (TopCat.disk.{w} n)) :
    IsIso (TopPair.twistedHomologyMap (diskInteriorPairι.{w} n) K k) :=
  have : T2Space (TopCat.disk.{w} n) := (diskHomeomorphClosedBall n).symm.t2Space
  TopPair.isIso_twistedHomologyMap_excisionMap_of_isClosed_subset K isOpen_diskInterior
    isClosed_singleton (singleton_subset_iff.2 (diskCenter_mem_diskInterior n)) k

variable {C}

/-- The characteristic map of an `n`-cell `i` in sup-norm coordinates. -/
private lemma coe_characteristicCellPairMap_fst_apply' {n : ℕ} (i : cell C n)
    (z : TopCat.disk.{w} n) :
    (TopPair.Hom.fst (characteristicCellPairMap C i) z).val =
      map n i (diskHomeomorphClosedBall n z) :=
  (congrArg Subtype.val (ConcreteCategory.congr_hom (characteristicCellPairMap_fst C i) z)).trans
    (coe_cellDiskHom_apply i z)

/-- The characteristic map of an `n`-cell `i` takes the value at the centre only at the centre of
the disk. -/
private lemma characteristicCellPairMap_fst_eq_iff {n : ℕ} (i : cell C n) (z : TopCat.disk.{w} n) :
    (TopPair.Hom.fst (characteristicCellPairMap C i) z).val = map n i 0 ↔ z = diskCenter n := by
  rw [coe_characteristicCellPairMap_fst_apply',
    map_eq_map_zero_iff i (mem_closedBall_zero_iff.1 (diskHomeomorphClosedBall n z).property)]
  refine ⟨fun h ↦ (diskHomeomorphClosedBall n).injective (Subtype.ext ?_), fun h ↦ ?_⟩
  · rw [h, coe_diskHomeomorphClosedBall_diskCenter]
  · rw [h, coe_diskHomeomorphClosedBall_diskCenter]

variable {n : ℕ} (i : cell C n) (x : skeletonObj C (n + 1)) (hx : (x : X) = map n i 0)

include hx in
private lemma notMem_skeletonLT_of_eq_map_zero : (x : X) ∉ (skeletonLT C (n : ℕ∞) : Set X) :=
  hx ▸ map_zero_notMem_skeletonLT i

include hx in
/-- The characteristic map of `i` as a map of pairs `(Dⁿ, Dⁿ ∖ {0}) ⟶ (Xⁿ, Xⁿ ∖ {x})`, for the
centre `x` of `i`. -/
private def diskComplCenterToComplSingleton :
    TopPair.ofSubset ({diskCenter n}ᶜ : Set (TopCat.disk.{w} n)) ⟶
      TopPair.ofSubset ({x}ᶜ : Set (skeletonObj C (n + 1))) :=
  TopPair.ofSubsetMap (TopPair.Hom.fst (characteristicCellPairMap C i)) fun z hz h ↦
    hz ((characteristicCellPairMap_fst_eq_iff i z).1 ((congrArg Subtype.val h).trans hx))

private lemma diskComplCenterToComplSingleton_fst :
    TopPair.Hom.fst (diskComplCenterToComplSingleton i x hx) =
      TopPair.Hom.fst (characteristicCellPairMap C i) :=
  TopPair.ofSubsetMap_fst _ _

private lemma characteristicCellPairMap_comp_skeletonPairToComplSingleton_eq :
    characteristicCellPairMap C i ≫
        skeletonPairToComplSingleton C x (notMem_skeletonLT_of_eq_map_zero i x hx) =
      diskBoundaryPairToComplDiskCenter n ≫ diskComplCenterToComplSingleton i x hx :=
  TopPair.hom_ext_of_fst _ (by
    rw [TopPair.Hom.fst_comp, TopPair.Hom.fst_comp, skeletonPairToComplSingleton_fst,
      diskBoundaryPairToComplDiskCenter_fst, diskComplCenterToComplSingleton_fst]
    -- The identities are those of the `n`-skeleton and of the disk, written as the ambient spaces
    -- of different pairs, so the unit laws only match up to unfolding these.
    erw [Category.comp_id])

/-- The image of a point of the open interior of the disk under the characteristic map of `i`. -/
private lemma coe_fst_diskInteriorPairι_comp_diskComplCenterToComplSingleton_apply
    (z : diskInterior.{w} n) :
    (TopPair.Hom.fst (diskInteriorPairι n ≫ diskComplCenterToComplSingleton i x hx) z).val =
      map n i (diskHomeomorphClosedBall n z.val) := by
  rw [TopPair.Hom.fst_comp, diskComplCenterToComplSingleton_fst]
  exact coe_characteristicCellPairMap_fst_apply' i z.val

/-- On the open interior of the disk, the characteristic map of `i` is an embedding into the
`n`-skeleton: it is a homeomorphism onto the open cell. -/
private lemma isEmbedding_fst_diskInteriorPairι_comp_diskComplCenterToComplSingleton :
    IsEmbedding
      (TopPair.Hom.fst (diskInteriorPairι n ≫ diskComplCenterToComplSingleton i x hx)) := by
  have hfun : (TopPair.Hom.fst (diskInteriorPairι n ≫ diskComplCenterToComplSingleton i x hx) :
      diskInterior.{w} n → skeletonObj C (n + 1)) =
        (diskInterior n).domRestrict (cellDiskHom i) := by
    funext z
    rw [TopPair.Hom.fst_comp, diskComplCenterToComplSingleton_fst]
    exact ConcreteCategory.congr_hom (characteristicCellPairMap_fst C i) z.val
  exact hfun ▸ isEmbedding_cellDiskHom_restrict C i

/-- **Excision of the complement of the open cell** from `(Xⁿ, Xⁿ ∖ {x})`, read through the
characteristic map of `i` on the open interior of the disk, with local coefficients. -/
private lemma isIso_twistedHomologyMap_diskInteriorPairι_comp_diskComplCenterToComplSingleton
    (k : ℕ) (K : LocalCoefficientSystem.{u, w, max w v} R
      (TopPair.ofSubset ({x}ᶜ : Set (skeletonObj C (n + 1)))).fst) :
    IsIso (TopPair.twistedHomologyMap
      (diskInteriorPairι n ≫ diskComplCenterToComplSingleton i x hx) K k) := by
  refine TopPair.isIso_twistedHomologyMap_of_open_cover _ K
    (isEmbedding_fst_diskInteriorPairι_comp_diskComplCenterToComplSingleton i x hx) ?_
    (fun b : Bool ↦ bif b then (Subtype.val ⁻¹' openCell n i : Set (skeletonObj C (n + 1)))
      else ({x}ᶜ : Set (skeletonObj C (n + 1))))
    (fun b ↦ ?_) ?_ (fun b ↦ ?_) k
  · -- A point of the interior off the centre is sent off `x`.
    intro z hz
    rw [TopPair.range_ofSubset_map] at hz ⊢
    intro hc
    apply hz
    refine Subtype.ext ((coe_fst_diskInteriorPairι_comp_diskComplCenterToComplSingleton_apply
      i x hx z).trans ?_)
    rw [mem_singleton_iff.1 hc, coe_diskHomeomorphClosedBall_diskCenter, hx]
  · cases b
    · exact (isOpen_compl_singleton : IsOpen ({x}ᶜ : Set (skeletonObj C (n + 1))))
    · exact isOpen_preimage_val_openCell n subset_rfl i
  · refine eq_univ_of_forall fun y ↦ mem_iUnion.2 ?_
    by_cases hy : y = x
    · exact ⟨true, hy ▸ (hx ▸ map_zero_mem_openCell n i : (x : X) ∈ openCell n i)⟩
    · exact ⟨false, hy⟩
  · cases b
    · exact Or.inl fun y hy ↦ by rw [TopPair.range_ofSubset_map]; exact hy
    · -- A point of the open cell is the image of a point of the open interior of the disk.
      refine Or.inr fun y hy ↦ ?_
      let b := (openCellHomeomorph n i).symm ⟨y.val, hy⟩
      let z : diskInterior.{w} n := ⟨(diskHomeomorphClosedBall n).symm
        ⟨b, ball_subset_closedBall b.property⟩, by
          rw [mem_diskInterior_iff, Homeomorph.apply_symm_apply]
          exact mem_ball_zero_iff.1 b.property⟩
      refine ⟨z, Subtype.ext ?_⟩
      rw [coe_fst_diskInteriorPairι_comp_diskComplCenterToComplSingleton_apply]
      simp only [z, Homeomorph.apply_symm_apply]
      exact (openCellHomeomorph_apply n i b).symm.trans
        (congrArg Subtype.val ((openCellHomeomorph n i).apply_symm_apply ⟨y.val, hy⟩))

private lemma isIso_twistedHomologyMap_diskComplCenterToComplSingleton (k : ℕ)
    (K : LocalCoefficientSystem.{u, w, max w v} R
      (TopPair.ofSubset ({x}ᶜ : Set (skeletonObj C (n + 1)))).fst) :
    IsIso (TopPair.twistedHomologyMap (diskComplCenterToComplSingleton i x hx) K k) := by
  have h := isIso_twistedHomologyMap_diskInteriorPairι_comp_diskComplCenterToComplSingleton
    i x hx k K
  rw [TopPair.twistedHomologyMap_comp] at h
  have := isIso_twistedHomologyMap_diskInteriorPairι n k
    ((LocalCoefficientSystem.pullback
      (TopPair.Hom.fst (diskComplCenterToComplSingleton i x hx)).hom).obj K)
  rwa [isIso_comp_left_iff, isIso_comp_left_iff] at h

/-- **The characteristic map of a cell computes the local homology at its centre, with local
coefficients.** For the centre `x = χᵢ(0)` of an `n`-cell `i` and every local coefficient system
`K` on the `n`-skeleton `Xⁿ`, the characteristic map of `i`, as a map of pairs
`(Dⁿ, Sⁿ⁻¹) ⟶ (Xⁿ, Xⁿ ∖ {x})`, induces isomorphisms `Hₖ(Dⁿ, Sⁿ⁻¹; χᵢ*K) ≅ Hₖ(Xⁿ, Xⁿ ∖ {x}; K)` in
every degree. -/
theorem isIso_twistedHomologyMap_characteristicCellPairMap_comp_skeletonPairToComplSingleton
    (k : ℕ) (K : LocalCoefficientSystem.{u, w, max w v} R
      (TopPair.ofSubset ({x}ᶜ : Set (skeletonObj C (n + 1)))).fst) :
    IsIso (TopPair.twistedHomologyMap (characteristicCellPairMap C i ≫
      skeletonPairToComplSingleton C x (hx ▸ map_zero_notMem_skeletonLT i)) K k) := by
  rw [characteristicCellPairMap_comp_skeletonPairToComplSingleton_eq i x hx,
    TopPair.twistedHomologyMap_comp]
  have := isIso_twistedHomologyMap_diskComplCenterToComplSingleton i x hx k K
  have := isIso_twistedHomologyMap_diskBoundaryPairToComplDiskCenter n
    ((LocalCoefficientSystem.pullback
      (TopPair.Hom.fst (diskComplCenterToComplSingleton i x hx)).hom).obj K) k
  infer_instance

end Disk

/-! ### Other cells -/

variable {C} {n : ℕ} {i : cell C n} (x : skeletonObj C (n + 1)) (hx : (x : X) ∈ openCell n i)

/-- **Other cells vanish in the local homology at a point of an open cell, with local
coefficients.** For a point `x` of the open cell of an `n`-cell `i`, an `n`-cell `k ≠ i` and every
local coefficient system `K` on `Xⁿ`, the characteristic map of `k`, as a map of pairs
`(Dⁿ, Sⁿ⁻¹) ⟶ (Xⁿ, Xⁿ ∖ {x})`, induces zero on relative homology: the closed cell of `k` misses
`x`. -/
theorem twistedHomologyMap_characteristicCellPairMap_comp_skeletonPairToComplSingleton_eq_zero
    {k : cell C n} (hk : k ≠ i) (K : LocalCoefficientSystem.{u, w, max w v} R
      (TopPair.ofSubset ({x}ᶜ : Set (skeletonObj C (n + 1)))).fst) (m : ℕ) :
    TopPair.twistedHomologyMap (characteristicCellPairMap C k ≫
      skeletonPairToComplSingleton C x (notMem_skeletonLT_of_mem_openCell n hx)) K m = 0 := by
  have hmiss : ∀ z : TopCat.disk.{w} n,
      (TopPair.Hom.fst (characteristicCellPairMap C k) z : skeletonObj C (n + 1)) ≠ x := by
    intro z hz
    have hmem : (x : X) ∈ closedCell n k := by
      rw [← hz, coe_characteristicCellPairMap_fst_apply']
      exact mem_image_of_mem _ (diskHomeomorphClosedBall n z).property
    exact (disjoint_closedCell_openCell_of_ne n le_rfl
      (fun h ↦ hk (eq_of_heq (Sigma.mk.inj_iff.1 h).2))).notMem_of_mem_left hmem hx
  -- The characteristic map of `k` lands in `Xⁿ ∖ {x}`, the subspace of the target pair.
  exact TopPair.twistedHomologyMap_eq_zero_of_fac _ K
    (TopCat.ofHom ⟨fun z ↦ ⟨TopPair.Hom.fst (characteristicCellPairMap C k) z, hmiss z⟩,
      (TopPair.Hom.fst (characteristicCellPairMap C k)).hom.continuous.subtype_mk _⟩) (by
        rw [TopPair.Hom.fst_comp, skeletonPairToComplSingleton_fst]
        -- The identity is that of the `n`-skeleton, written as the ambient space of another pair.
        erw [Category.comp_id]
        rfl) m

/-! ### The localization of cellular chains with local coefficients -/

section Localization

variable (C) (L : LocalCoefficientSystem.{u, w, max w v} R (TopCat.of C))

/-- The identification of the coefficients `L` on `Xⁿ` with their pullback along the ambient
component of `TauCeti.skeletonPairToComplSingleton`, which is the identity of `Xⁿ`. -/
private def skeletonSystemIsoPullbackComplSingleton (x : skeletonObj C (n + 1))
    (hxn : (x : X) ∉ (skeletonLT C (n : ℕ∞) : Set X)) :
    skeletonSystem C L (n + 1) ≅ (LocalCoefficientSystem.pullback
      (TopPair.Hom.fst (skeletonPairToComplSingleton C x hxn)).hom).obj
        (skeletonSystem C L (n + 1)) :=
  ((LocalCoefficientSystem.pullbackIdIso (skeletonObj C (n + 1))).app _).symm ≪≫
    eqToIso (congrArg (fun f : skeletonObj C (n + 1) ⟶ skeletonObj C (n + 1) ↦
      (LocalCoefficientSystem.pullback f.hom).obj (skeletonSystem C L (n + 1)))
      (skeletonPairToComplSingleton_fst C x hxn).symm)

/-- **The localization of cellular chains with local coefficients** at a point `x` of the
`n`-skeleton off the `(n - 1)`-skeleton: the map `Hₙ(Xⁿ, Xⁿ⁻¹; L) ⟶ Hₙ(Xⁿ, Xⁿ ∖ {x}; L)` from the
cellular chain group with coefficients in `L` to the local homology of `Xⁿ` at `x`, induced by the
identity of `Xⁿ`. At the centre of an `n`-cell `i` it is an isomorphism on the contribution of `i`
(`isIso_twistedHomologyMap_characteristicCellPairMap_comp_twistedCellularChainLocalization`), and
at any point of the open cell of `i` it vanishes on the contributions of the other `n`-cells
(`twistedHomologyMap_characteristicCellPairMap_comp_twistedCellularChainLocalization_eq_zero`). -/
def twistedCellularChainLocalization (x : skeletonObj C (n + 1))
    (hxn : (x : X) ∉ (skeletonLT C (n : ℕ∞) : Set X)) :
    twistedCellularChainGroup C L n ⟶
      (TopPair.ofSubset ({x}ᶜ : Set (skeletonObj C (n + 1)))).twistedHomology
        (skeletonSystem C L (n + 1)) n :=
  (skeletonPair C n).twistedHomologyCoefficientMap
      (skeletonSystemIsoPullbackComplSingleton C L x hxn).hom n ≫
    TopPair.twistedHomologyMap (skeletonPairToComplSingleton C x hxn) (skeletonSystem C L (n + 1)) n

/-- On the contribution of an `n`-cell `k`, the localization at `x` is the map induced by the
characteristic map of `k`, as a map of pairs `(Dⁿ, Sⁿ⁻¹) ⟶ (Xⁿ, Xⁿ ∖ {x})`, up to the
identification of the coefficients. -/
private lemma twistedHomologyMap_characteristicCellPairMap_comp_localization_eq
    (x : skeletonObj C (n + 1)) (hxn : (x : X) ∉ (skeletonLT C (n : ℕ∞) : Set X))
    (k : cell C n) :
    TopPair.twistedHomologyMap (characteristicCellPairMap C k) (skeletonSystem C L (n + 1)) n ≫
        twistedCellularChainLocalization C L x hxn =
      (diskBoundaryPair.{w} n).twistedHomologyCoefficientMap
          ((LocalCoefficientSystem.pullback
            (TopPair.Hom.fst (characteristicCellPairMap C k)).hom).map
              (skeletonSystemIsoPullbackComplSingleton C L x hxn).hom) n ≫
        TopPair.twistedHomologyMap (characteristicCellPairMap C k)
          ((LocalCoefficientSystem.pullback
            (TopPair.Hom.fst (skeletonPairToComplSingleton C x hxn)).hom).obj
              (skeletonSystem C L (n + 1))) n ≫
        TopPair.twistedHomologyMap (skeletonPairToComplSingleton C x hxn)
          (skeletonSystem C L (n + 1)) n := by
  rw [twistedCellularChainLocalization]
  exact TopPair.twistedHomologyMap_naturality_assoc (characteristicCellPairMap C k) _
    (skeletonSystemIsoPullbackComplSingleton C L x hxn).hom n _

/-- **The localization at the centre of a cell is an isomorphism on its contribution.** For the
centre `x = χᵢ(0)` of an `n`-cell `i`, the contribution `Hₙ(Dⁿ, Sⁿ⁻¹; χᵢ*L)` of `i` to the
cellular chain group with local coefficients maps isomorphically onto the local homology
`Hₙ(Xⁿ, Xⁿ ∖ {x}; L)` under the localization at `x`. -/
theorem isIso_twistedHomologyMap_characteristicCellPairMap_comp_twistedCellularChainLocalization
    (i : cell C n) (x : skeletonObj C (n + 1)) (hx : (x : X) = map n i 0) :
    IsIso (TopPair.twistedHomologyMap (characteristicCellPairMap C i)
        (skeletonSystem C L (n + 1)) n ≫
      twistedCellularChainLocalization C L x (hx ▸ map_zero_notMem_skeletonLT i)) := by
  rw [twistedHomologyMap_characteristicCellPairMap_comp_localization_eq]
  have h := isIso_twistedHomologyMap_characteristicCellPairMap_comp_skeletonPairToComplSingleton
    i x hx n (skeletonSystem C L (n + 1))
  rw [TopPair.twistedHomologyMap_comp (characteristicCellPairMap C i)
    (skeletonPairToComplSingleton C x (hx ▸ map_zero_notMem_skeletonLT i))
    (skeletonSystem C L (n + 1)) n, isIso_comp_left_iff] at h
  -- The pulled-back systems are typed on the ambient spaces of different pairs, so instance search
  -- does not match the factors; the instances are supplied.
  let e := (LocalCoefficientSystem.pullback
    (TopPair.Hom.fst (characteristicCellPairMap C i)).hom).mapIso
      (skeletonSystemIsoPullbackComplSingleton C L x (hx ▸ map_zero_notMem_skeletonLT i))
  have he : IsIso ((diskBoundaryPair.{w} n).twistedHomologyCoefficientMap e.hom n) :=
    ⟨_, TopPair.twistedHomologyCoefficientMap_hom_inv_id _ e n,
      TopPair.twistedHomologyCoefficientMap_inv_hom_id _ e n⟩
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ he h

/-- **The localization at a point of an open cell vanishes on the contributions of the other
cells.** For a point `x` of the open cell of an `n`-cell `i` and an `n`-cell `k ≠ i`, the
contribution `Hₙ(Dⁿ, Sⁿ⁻¹; χₖ*L)` of `k` to the cellular chain group with local coefficients maps to
zero under the localization at `x`. -/
theorem twistedHomologyMap_characteristicCellPairMap_comp_twistedCellularChainLocalization_eq_zero
    {i k : cell C n} (hk : k ≠ i) (x : skeletonObj C (n + 1)) (hx : (x : X) ∈ openCell n i) :
    TopPair.twistedHomologyMap (characteristicCellPairMap C k) (skeletonSystem C L (n + 1)) n ≫
        twistedCellularChainLocalization C L x (notMem_skeletonLT_of_mem_openCell n hx) =
      0 := by
  rw [twistedHomologyMap_characteristicCellPairMap_comp_localization_eq]
  have h := twistedHomologyMap_characteristicCellPairMap_comp_skeletonPairToComplSingleton_eq_zero
    x hx hk (skeletonSystem C L (n + 1)) n
  rw [TopPair.twistedHomologyMap_comp (characteristicCellPairMap C k)
    (skeletonPairToComplSingleton C x (notMem_skeletonLT_of_mem_openCell n hx))
    (skeletonSystem C L (n + 1)) n] at h
  rw [(cancel_epi _).1 (h.trans comp_zero.symm), comp_zero]

end Localization

end TauCeti
