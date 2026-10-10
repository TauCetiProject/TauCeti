/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Empty
public import TauCeti.AlgebraicTopology.Singular.Sphere

/-!
# The relative homology of a disk and its boundary

The relative singular homology of the `n`-disk modulo its boundary is one copy of the coefficient
object in degree `n` and vanishes in every other degree.

The degree-zero relative homology of a positive-dimensional disk vanishes relative to its
boundary.  For the one-dimensional disk, both boundary points determine the same zeroth-homology
class of the disk; in higher dimensions the boundary itself is path-connected.  The lower bound is
sharp: for `n = 0`, the disk is a point and its boundary is empty, so the degree-zero group is one
copy of the coefficient object, identified by the augmentation.

In positive degrees, the disk is contractible, so the reduced connecting morphism of the pair
identifies `Hₖ₊₁(Dⁿ, Sⁿ⁻¹)` with the reduced homology `H~ₖ(Sⁿ⁻¹)` of the boundary sphere, which is
computed in `TauCeti/AlgebraicTopology/Singular/Sphere.lean`.  The isomorphism
`Hₙ(Dⁿ, Sⁿ⁻¹) ≅ R` in the top degree is this connecting morphism followed by the standard generator
`TauCeti.reducedSingularHomologyTopCatSphereIso` of `H~ₙ₋₁(Sⁿ⁻¹)`, so the connecting morphism
carries the generator of the pair to the standard generator of the sphere.

## Main results

* `TauCeti.isZero_singularHomology_diskBoundaryPair_zero`: `H₀(Dⁿ, Sⁿ⁻¹) = 0` for `n ≥ 1`.
* `TauCeti.isZero_singularHomology_diskBoundaryPair_of_ne`: `Hₖ(Dⁿ, Sⁿ⁻¹) = 0` for `k ≠ n`.
* `TauCeti.singularHomologyDiskBoundaryPairIso`: `Hₙ(Dⁿ, Sⁿ⁻¹) ≅ R`.
* `TauCeti.singularHomologyCubeBoundaryPairIso` and
  `TauCeti.isZero_singularHomology_cubeBoundaryPair_of_ne`: the same for the cube pair
  `(Iⁿ, ∂Iⁿ)`, transported along `TauCeti.diskBoundaryPairIsoCube`.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, Corollary 2.24 and Example 2.23.
-/

public section

noncomputable section
open CategoryTheory Limits
universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)

private lemma diskBoundary_singularHomologyMap_zero_epi {n : ℕ} (hn : 1 ≤ n) :
    Epi (((AlgebraicTopology.singularHomologyFunctor C 0).obj R).map
      (TopCat.diskBoundaryInclusion (n := n) :
        (TopCat.diskBoundary n : TopCat.{w}) ⟶ (TopCat.disk n : TopCat.{w}))) := by
  let i : (TopCat.diskBoundary n : TopCat.{w}) ⟶ (TopCat.disk n : TopCat.{w}) :=
    TopCat.diskBoundaryInclusion n
  have hne : Nonempty (TopCat.diskBoundary n) := by
    -- Unfolding `TopCat.diskBoundary` exposes its metric-sphere carrier.
    change Nonempty (ULift (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1))
    let i : Fin n := ⟨0, Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn)⟩
    let x : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i 1
    have hx : x ∈ Metric.sphere 0 1 := by simp [x]
    exact ⟨⟨x, hx⟩⟩
  let x : (TopCat.diskBoundary n : TopCat.{w}) := Classical.choice hne
  let hsplit : IsSplitEpi
      (TopCat.singularHomology₀ε (TopCat.diskBoundary n : TopCat.{w}) R) := by
    refine IsSplitEpi.mk' { section_ := TauCeti.singularHomology₀Section R x, id := ?_ }
    exact TauCeti.singularHomology₀Section_singularHomology₀ε R x
  let hε : Epi (TopCat.singularHomology₀ε (TopCat.diskBoundary n : TopCat.{w}) R) := by
    infer_instance
  let hp : IsIso (TopCat.singularHomology₀ε (TopCat.disk n : TopCat.{w}) R) := by
    let _ : ContractibleSpace (TopCat.disk n : TopCat.{w}) :=
      TauCeti.TopCat.contractibleSpace_disk n
    infer_instance
  let hεcomp : Epi
      (((AlgebraicTopology.singularHomologyFunctor C 0).obj R).map i ≫
        TopCat.singularHomology₀ε (TopCat.disk n : TopCat.{w}) R) := by
    rw [TauCeti.singularHomologyMap_singularHomology₀ε R i]
    exact hε
  exact (CategoryTheory.epi_comp_iff_of_isIso
    (((AlgebraicTopology.singularHomologyFunctor C 0).obj R).map i)
    (TopCat.singularHomology₀ε (TopCat.disk n : TopCat.{w}) R)).mp hεcomp

/-- The inclusion from the boundary of a disk of dimension at least two is an isomorphism on
zeroth singular homology. -/
lemma diskBoundary_singularHomologyMap_zero_isIso {n : ℕ} (hn : 2 ≤ n) :
    IsIso (((AlgebraicTopology.singularHomologyFunctor C 0).obj R).map
      (TopCat.diskBoundaryInclusion (n := n) :
        (TopCat.diskBoundary n : TopCat.{w}) ⟶ (TopCat.disk n : TopCat.{w}))) := by
  let i : (TopCat.diskBoundary n : TopCat.{w}) ⟶ (TopCat.disk n : TopCat.{w}) :=
    TopCat.diskBoundaryInclusion n
  let hp : IsIso (TopCat.singularHomology₀ε (TopCat.disk n : TopCat.{w}) R) := by
    let _ : ContractibleSpace (TopCat.disk n : TopCat.{w}) :=
      TauCeti.TopCat.contractibleSpace_disk n
    infer_instance
  let hq : IsIso (TopCat.singularHomology₀ε (TopCat.diskBoundary n : TopCat.{w}) R) := by
    let _ : PathConnectedSpace (TopCat.diskBoundary n : TopCat.{w}) :=
      TauCeti.TopCat.pathConnectedSpace_diskBoundary hn
    infer_instance
  let hcomp : IsIso
      (((AlgebraicTopology.singularHomologyFunctor C 0).obj R).map i ≫
        TopCat.singularHomology₀ε (TopCat.disk n : TopCat.{w}) R) := by
    rw [TauCeti.singularHomologyMap_singularHomology₀ε R i]
    exact hq
  exact IsIso.of_isIso_comp_right
    (((AlgebraicTopology.singularHomologyFunctor C 0).obj R).map i)
    (TopCat.singularHomology₀ε (TopCat.disk n : TopCat.{w}) R)

/-- The degree-zero relative homology of a positive-dimensional disk and its boundary vanishes. -/
lemma isZero_singularHomology_diskBoundaryPair_zero {n : ℕ} (hn : 1 ≤ n) :
    IsZero ((diskBoundaryPair n).singularHomology R 0) := by
  let P : TopPair.{w} := diskBoundaryPair n
  -- The singular homology functor is the composite of `TopCat.toSSet` and the simplicial
  -- homology functor; this records that composite on the boundary inclusion.
  have hmapBridge :
      SSet.homologyMap
          (TopCat.toSSet.map
            (TopCat.diskBoundaryInclusion (n := n) :
              (TopCat.diskBoundary n : TopCat.{w}) ⟶ (TopCat.disk n : TopCat.{w}))) R 0 =
        ((AlgebraicTopology.singularHomologyFunctor C 0).obj R).map
          (TopCat.diskBoundaryInclusion (n := n) :
            (TopCat.diskBoundary n : TopCat.{w}) ⟶ (TopCat.disk n : TopCat.{w})) := rfl
  have hmap :
      Epi (SSet.homologyMap
        (TopCat.toSSet.map
          (TopCat.diskBoundaryInclusion (n := n) :
            (TopCat.diskBoundary n : TopCat.{w}) ⟶ (TopCat.disk n : TopCat.{w}))) R 0) := by
    rw [hmapBridge]
    exact diskBoundary_singularHomologyMap_zero_epi (R := R) hn
  let S : ShortComplex C :=
    ShortComplex.mk
      (SSet.homologyMap (TopCat.toSSet.map P.map) R 0)
      (P.singularHomologyπ R 0) (P.homologyMap_comp_singularHomologyπ R 0)
  have hPmap : P.map = TopCat.diskBoundaryInclusion n := by
    simpa only [P] using (diskBoundaryPair_map n)
  have hEpiF : Epi S.f := by
    dsimp [S]
    rw [hPmap]
    exact hmap
  have hEpiG : Epi S.g := by
    simpa only [S, P, TopPair.toSSetPair_obj_right] using
      (inferInstance : Epi (P.singularHomologyπ R 0))
  -- `S.zero` is the short-complex relation `S.f ≫ S.g = 0`; epi of `S.f` forces
  -- `S.g = 0`, and epi of `S.g` then makes the target zero.
  have hgzero : S.g = 0 := zero_of_epi_comp S.f S.zero
  have hzero : IsZero S.X₃ := by
    have hz : (0 : S.X₂ ⟶ S.X₃) = S.g := hgzero.symm
    have hepiZero : Epi (0 : S.X₂ ⟶ S.X₃) := by
      rw [hz]
      exact hEpiG
    exact IsZero.of_epi_zero S.X₂ S.X₃
  simpa only [S] using hzero

section HigherDegrees

/-- The relative homology of the pair of the `0`-disk and its empty boundary is the ordinary
homology of the point `D⁰`: the quotient map from ambient to relative singular homology is an
isomorphism, and this is its inverse (`TauCeti.singularHomologyDiskBoundaryPairZeroIso_inv`). -/
def singularHomologyDiskBoundaryPairZeroIso (k : ℕ) :
    (diskBoundaryPair.{w} 0).singularHomology R k ≅
      ((AlgebraicTopology.singularHomologyFunctor C k).obj R).obj (TopCat.disk.{w} 0) :=
  (asIso ((diskBoundaryPair.{w} 0).singularHomologyπ R k)).symm

/-- The comparison from the relative homology of the `0`-disk pair to the ordinary homology of the
point is the inverse of the quotient map. -/
@[simp]
lemma singularHomologyDiskBoundaryPairZeroIso_hom (k : ℕ) :
    (singularHomologyDiskBoundaryPairZeroIso R k).hom =
      inv ((diskBoundaryPair.{w} 0).singularHomologyπ R k) := (rfl)

/-- The comparison from the ordinary homology of the point to the relative homology of the
`0`-disk pair is the quotient map from ambient to relative singular homology. -/
@[simp]
lemma singularHomologyDiskBoundaryPairZeroIso_inv (k : ℕ) :
    (singularHomologyDiskBoundaryPairZeroIso R k).inv =
      (diskBoundaryPair.{w} 0).singularHomologyπ R k := (rfl)

/-- **The relative homology of a disk modulo its boundary vanishes outside its dimension**:
`Hₖ(Dⁿ, Sⁿ⁻¹) = 0` for `k ≠ n`. -/
theorem isZero_singularHomology_diskBoundaryPair_of_ne {n k : ℕ} (hk : k ≠ n) :
    IsZero ((diskBoundaryPair.{w} n).singularHomology R k) := by
  cases n with
  | zero =>
    exact (isZero_singularHomologyFunctor_of_contractibleSpace R (TopCat.disk.{w} 0) hk).of_iso
      (singularHomologyDiskBoundaryPairZeroIso R k)
  | succ m =>
    cases k with
    | zero => exact isZero_singularHomology_diskBoundaryPair_zero R m.succ_pos
    | succ k =>
      exact (isZero_reducedSingularHomologyFunctor_topCatSphere_of_ne R (n := m) (k := k)
        fun h ↦ hk (by omega)).of_iso
        (@asIso _ _ _ _ ((diskBoundaryPair.{w} (m + 1)).reducedSingularHomologyδ R k)
          (TopPair.isIso_reducedSingularHomologyδ_of_contractibleSpace _ R k))

/-- **The relative homology of a disk modulo its boundary in its dimension**: `Hₙ(Dⁿ, Sⁿ⁻¹) ≅ R`.
For `n = m + 1` it is the reduced connecting isomorphism onto `H~ₘ(Sᵐ)` followed by the standard
generator `TauCeti.reducedSingularHomologyTopCatSphereIso` of the sphere
(`TauCeti.singularHomologyDiskBoundaryPairIso_succ_hom`); for `n = 0` the pair is a point modulo
the empty set and the isomorphism is the augmentation. -/
def singularHomologyDiskBoundaryPairIso :
    (n : ℕ) → ((diskBoundaryPair.{w} n).singularHomology R n ≅ R)
  | 0 => singularHomologyDiskBoundaryPairZeroIso R 0 ≪≫
      asIso ((TopCat.disk.{w} 0).singularHomology₀ε R)
  | m + 1 =>
    haveI := TopPair.isIso_reducedSingularHomologyδ_of_contractibleSpace
      (diskBoundaryPair.{w} (m + 1)) R m
    asIso ((diskBoundaryPair.{w} (m + 1)).reducedSingularHomologyδ R m) ≪≫
      reducedSingularHomologyTopCatSphereIso R m

/-- In positive dimension, the identification `Hₘ₊₁(Dᵐ⁺¹, Sᵐ) ≅ R` is the reduced connecting
morphism of the pair followed by the standard generator of `H~ₘ(Sᵐ)`. -/
@[simp]
lemma singularHomologyDiskBoundaryPairIso_succ_hom (m : ℕ) :
    (singularHomologyDiskBoundaryPairIso R (m + 1)).hom =
      (diskBoundaryPair.{w} (m + 1)).reducedSingularHomologyδ R m ≫
        (reducedSingularHomologyTopCatSphereIso R m).hom := by
  rfl

/-- The ordinary connecting morphism sends the disk generator to the boundary-sphere generator,
viewed in unreduced homology.  In dimension one this is the reduced class of the two endpoints. -/
@[reassoc]
lemma singularHomologyDiskBoundaryPairIso_inv_comp_singularHomologyδ (m : ℕ) :
    (singularHomologyDiskBoundaryPairIso R (m + 1)).inv ≫
        (diskBoundaryPair.{w} (m + 1)).singularHomologyδ R (m + 1) m =
      (reducedSingularHomologyTopCatSphereIso R m).inv ≫
        (reducedSingularHomologyι R m).app (TopCat.diskBoundary.{w} (m + 1)) := by
  have h : (singularHomologyDiskBoundaryPairIso R (m + 1)).inv ≫
      (diskBoundaryPair.{w} (m + 1)).reducedSingularHomologyδ R m =
        (reducedSingularHomologyTopCatSphereIso R m).inv := by
    apply (cancel_mono (reducedSingularHomologyTopCatSphereIso R m).hom).1
    -- `TopCat.sphere m` is the boundary of the `(m + 1)`-disk; these object presentations
    -- occur under the reduced homology functor on opposite sides of the associativity rewrite.
    erw [Category.assoc, ← singularHomologyDiskBoundaryPairIso_succ_hom,
      Iso.inv_hom_id, Iso.inv_hom_id]
  -- The ordinary singular homology target is also presented through the singular simplicial
  -- set of the boundary; `erw` identifies the two functor presentations.
  erw [← TopPair.reducedSingularHomologyδ_comp_ι, ← Category.assoc, h]
  rfl

/-- In dimension zero, the identification `H₀(D⁰, ∅) ≅ R` is the inverse of the quotient map from
the ordinary homology of the point followed by the augmentation. -/
@[simp]
lemma singularHomologyDiskBoundaryPairIso_zero_hom :
    (singularHomologyDiskBoundaryPairIso R 0).hom =
      inv ((diskBoundaryPair.{w} 0).singularHomologyπ R 0) ≫
        (TopCat.disk.{w} 0).singularHomology₀ε R := by
  rfl

end HigherDegrees

section CubePairHomology

variable (n : ℕ)

/-- **The relative homology of a cube modulo its boundary in its dimension**:
`Hₙ(Iⁿ, ∂Iⁿ; R) ≅ R`, transported from `TauCeti.singularHomologyDiskBoundaryPairIso` along the
isomorphism of pairs `TauCeti.diskBoundaryPairIsoCube`. -/
def singularHomologyCubeBoundaryPairIso : (cubeBoundaryPair.{w} n).singularHomology R n ≅ R :=
  (SSetPair.homologyFunctor R n).mapIso
      (TopPair.toSSetPair.mapIso (diskBoundaryPairIsoCube n)).symm ≪≫
    singularHomologyDiskBoundaryPairIso R n

/-- The generator of `Hₙ(Iⁿ, ∂Iⁿ; R)` is the image of the generator of `Hₙ(Dⁿ, Sⁿ⁻¹; R)` under
`TauCeti.diskBoundaryPairToCube`. -/
lemma singularHomologyCubeBoundaryPairIso_inv :
    (singularHomologyCubeBoundaryPairIso R n).inv =
      (singularHomologyDiskBoundaryPairIso R n).inv ≫
        TopPair.singularHomologyMap (diskBoundaryPairToCube.{w} n) R n := by
  rw [← diskBoundaryPairIsoCube_hom]
  -- This is the inverse of the composite defining `singularHomologyCubeBoundaryPairIso`.
  rfl

/-- The relative homology of a cube modulo its boundary vanishes outside its dimension:
`Hₖ(Iⁿ, ∂Iⁿ; R) = 0` for `k ≠ n`. -/
theorem isZero_singularHomology_cubeBoundaryPair_of_ne {k : ℕ} (hk : k ≠ n) :
    IsZero ((cubeBoundaryPair.{w} n).singularHomology R k) :=
  (isZero_singularHomology_diskBoundaryPair_of_ne R hk).of_iso
    ((SSetPair.homologyFunctor R k).mapIso
      (TopPair.toSSetPair.mapIso (diskBoundaryPairIsoCube n))).symm

end CubePairHomology

end TauCeti
