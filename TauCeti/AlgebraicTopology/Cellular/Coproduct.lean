/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.CharacteristicMap
public import TauCeti.AlgebraicTopology.Singular.Additivity
public import TauCeti.AlgebraicTopology.Singular.DiskSphere
public import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
public import TauCeti.CategoryTheory.Preadditive.Projective.Basic
import TauCeti.Topology.Constructions.SumProd

/-!
# The cellular chain group is a coproduct of copies of the coefficients, one per cell

For a relative CW complex and coefficients `R` in an abelian category in which coproducts indexed
by the `n`-cells are exact (for instance modules over a ring), the cellular chain group
`Hₙ(Xⁿ, Xⁿ⁻¹)` is the coproduct of one copy of `R` for each `n`-cell
(`TauCeti.cellularChainGroupIso`), so both it and the degree-`n` term of the cellular chain complex
are projective when `R` is (`TauCeti.projective_cellularChainGroup`,
`TauCeti.projective_cellularChainComplex_X`).  For modules over a ring `k`, this is the direct sum
of copies of the coefficient module `R`, one per `n`-cell; when `R = k`, it is the free `k`-module
on the `n`-cells.

The identification is induced by maps: the summand of the cell `j` is the image of the relative
homology `Hₙ(Dⁿ, Sⁿ⁻¹) ≅ R` of the Euclidean disk pair under the characteristic map of `j`
(`TauCeti.ι_cellularChainGroupIso_inv`).  It combines three facts.

* The characteristic maps identify `Hₙ(Xⁿ, Xⁿ⁻¹)` with the relative homology of the disjoint union
  `∐ⱼ (Dⁿ, Sⁿ⁻¹)` of closed unit balls of the sup norm on `Fin n → ℝ` relative to their boundary
  spheres (`TauCeti.cellularChainGroupIsoSigmaDiskPair`).
* That disjoint union is isomorphic, as a pair, to the disjoint union of copies of the Euclidean
  disk pair `TauCeti.diskBoundaryPair n` (`TauCeti.sigmaDiskBoundaryPairIso`), through the radial
  rescaling `ContinuousLinearEquiv.unitBallHomeomorph` of the coordinate identification of
  `EuclideanSpace ℝ (Fin n)` with `Fin n → ℝ`.
* Relative singular homology is additive (`TopPair.isColimitCofanSingularHomology`), and the
  Euclidean disk pair has `Hₙ(Dⁿ, Sⁿ⁻¹) ≅ R` (`TauCeti.singularHomologyDiskBoundaryPairIso`).

The same ingredients show that the relative homology of `∐ᵢ (Dⁿ, Sⁿ⁻¹)` vanishes outside degree
`n` (`TauCeti.isZero_singularHomology_sigmaDiskPair_of_ne`).

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Lemma 2.34.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Set Topology Topology.RelCWComplex

universe w v u

namespace TauCeti

section DiskPair

variable (ι : Type w) (n : ℕ)

private def sigmaDiskHomeomorph :
    (TopPair.sigma fun _ : ι ↦ diskBoundaryPair.{w} n).fst ≃ₜ
      Σ _ : ι, closedBall (0 : Fin n → ℝ) 1 :=
  Homeomorph.sigmaCongrRight fun _ ↦ diskHomeomorphClosedBall n

/-- The disjoint union of copies, indexed by `ι`, of the Euclidean disk pair
`TauCeti.diskBoundaryPair n` is isomorphic to `TauCeti.sigmaDiskPair ι n`, the disjoint union of
closed unit balls of the sup norm on `Fin n → ℝ` relative to their unit spheres.  On each summand
the isomorphism is the radial rescaling `ContinuousLinearEquiv.unitBallHomeomorph` of the
coordinate identification `EuclideanSpace.equiv`. -/
def sigmaDiskBoundaryPairIso :
    TopPair.sigma (fun _ : ι ↦ diskBoundaryPair.{w} n) ≅ sigmaDiskPair ι n :=
  TopPair.isoOfSubsetRange (TopPair.sigma fun _ : ι ↦ diskBoundaryPair.{w} n) ≪≫
    TopPair.ofSubsetIso (sigmaDiskHomeomorph ι n) fun p ↦ by
      rw [TopPair.mem_range_sigma_map, diskBoundaryPair_map,
        show sigmaDiskHomeomorph ι n p = ⟨p.1, diskHomeomorphClosedBall n p.2⟩ from
          Homeomorph.sigmaCongrRight_apply _ p]
      exact (norm_diskHomeomorphClosedBall_eq_one_iff p.2).symm

private lemma sigmaDiskBoundaryPairIso_hom_fst_apply
    (p : (TopPair.sigma fun _ : ι ↦ diskBoundaryPair.{w} n).fst) :
    TopPair.Hom.fst (sigmaDiskBoundaryPairIso ι n).hom p =
      ⟨p.1, diskHomeomorphClosedBall n p.2⟩ := by
  rw [sigmaDiskBoundaryPairIso, Iso.trans_hom, TopPair.Hom.fst_comp, TopCat.comp_app,
    TopPair.isoOfSubsetRange_hom_fst_apply]
  erw [TopPair.ofSubsetIso_hom, TopPair.ofSubsetMap_fst_apply]
  exact Homeomorph.sigmaCongrRight_apply (fun _ : ι ↦ diskHomeomorphClosedBall n) p

/-- On the ambient spaces, `TauCeti.sigmaDiskBoundaryPairIso` preserves the summand. -/
@[simp]
lemma sigmaDiskBoundaryPairIso_hom_fst_apply_fst
    (p : (TopPair.sigma fun _ : ι ↦ diskBoundaryPair.{w} n).fst) :
    (TopPair.Hom.fst (sigmaDiskBoundaryPairIso ι n).hom p).1 = p.1 :=
  congrArg Sigma.fst (sigmaDiskBoundaryPairIso_hom_fst_apply ι n p)

/-- On the ambient spaces, `TauCeti.sigmaDiskBoundaryPairIso` is the radial rescaling of the
coordinate identification `EuclideanSpace.equiv` in every summand. -/
@[simp]
lemma coe_sigmaDiskBoundaryPairIso_hom_fst_apply_snd
    (p : (TopPair.sigma fun _ : ι ↦ diskBoundaryPair.{w} n).fst) :
    ((TopPair.Hom.fst (sigmaDiskBoundaryPairIso ι n).hom p).2 : Fin n → ℝ) =
      (EuclideanSpace.equiv (Fin n) ℝ).unitBallHomeomorph
        ((p.2 : ULift.{w} (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).down :
          EuclideanSpace ℝ (Fin n)) := by
  rw [sigmaDiskBoundaryPairIso_hom_fst_apply]
  exact coe_diskHomeomorphClosedBall_apply p.2

end DiskPair

variable {X : Type w} [TopologicalSpace X] [T2Space X] {D : Set X} (C : Set X) [RelCWComplex C D]
  {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

/-- The relative singular homology of the disjoint union `∐ᵢ (Dⁿ, Sⁿ⁻¹)` of disk pairs vanishes
outside degree `n`, when coproducts indexed by `ι` are exact. -/
lemma isZero_singularHomology_sigmaDiskPair_of_ne (ι : Type w)
    [HasExactColimitsOfShape (Discrete ι) A] {n k : ℕ} (hk : k ≠ n) :
    IsZero ((sigmaDiskPair ι n).singularHomology R k) := by
  have h : IsZero ((TopPair.sigma fun _ : ι ↦ diskBoundaryPair.{w} n).singularHomology R k) :=
    (TopPair.isColimitCofanSingularHomology _ A R k).isZero_pt
      (Functor.isZero _ fun _ ↦ isZero_singularHomology_diskBoundaryPair_of_ne R hk)
  exact h.of_iso ((SSetPair.homologyFunctor R k).mapIso
    (TopPair.toSSetPair.mapIso (sigmaDiskBoundaryPairIso ι n))).symm

/-- **The cellular chain group is a coproduct of copies of the coefficients**: if coproducts
indexed by the `n`-cells are exact in `A`, then `Hₙ(Xⁿ, Xⁿ⁻¹)` is the coproduct of one copy of `R`
for each `n`-cell.  The summand of a cell is the image of `Hₙ(Dⁿ, Sⁿ⁻¹) ≅ R` under its
characteristic map (`TauCeti.ι_cellularChainGroupIso_inv`). -/
def cellularChainGroupIso (n : ℕ) [HasExactColimitsOfShape (Discrete (cell C n)) A] :
    cellularChainGroup C R n ≅ ∐ fun _ : cell C n ↦ R :=
  cellularChainGroupIsoSigmaDiskPair C R n ≪≫
    (SSetPair.homologyFunctor R n).mapIso
      (TopPair.toSSetPair.mapIso (sigmaDiskBoundaryPairIso (cell C n) n).symm) ≪≫
    (TopPair.isColimitCofanSingularHomology _ A R n).coconePointUniqueUpToIso
      (colimit.isColimit _) ≪≫
    Sigma.mapIso fun _ ↦ singularHomologyDiskBoundaryPairIso R n

/-- The inverse of `TauCeti.cellularChainGroupIso` on the summand of the cell `j` is the inverse of
`Hₙ(Dⁿ, Sⁿ⁻¹) ≅ R` followed by the map induced by the characteristic map of `j`, read on the
Euclidean disk pair. -/
@[reassoc]
lemma ι_cellularChainGroupIso_inv (n : ℕ) [HasExactColimitsOfShape (Discrete (cell C n)) A]
    (j : cell C n) :
    Sigma.ι (fun _ : cell C n ↦ R) j ≫ (cellularChainGroupIso C R n).inv =
      (singularHomologyDiskBoundaryPairIso R n).inv ≫
        TopPair.singularHomologyMap (TopPair.sigmaι (fun _ ↦ diskBoundaryPair.{w} n) j ≫
          (sigmaDiskBoundaryPairIso (cell C n) n).hom ≫ characteristicPairMap C n) R n := by
  simp only [cellularChainGroupIso, Iso.trans_inv, Sigma.ι_mapIso_inv_assoc, Category.assoc]
  congr 1
  rw [colimit.comp_coconePointUniqueUpToIso_inv_assoc]
  simp [TopPair.singularHomologyMap_comp]

/-- Read on the Euclidean disk of the cell `j`, the characteristic maps send the centre of the disk
to the centre `χⱼ(0)` of the cell. -/
lemma coe_characteristicPairMap_sigmaDiskBoundaryPairIso_diskCenter (n : ℕ) (j : cell C n) :
    (ConcreteCategory.hom (Y := TopCat.of (skeletonLT C (n + 1)))
      (TopPair.Hom.fst (characteristicPairMap C n))
        (TopPair.Hom.fst (sigmaDiskBoundaryPairIso (cell C n) n).hom
          (TopPair.Hom.fst (TopPair.sigmaι (fun _ : cell C n ↦ diskBoundaryPair.{w} n) j)
            (diskCenter n)))).val = map n j 0 := by
  let c := TopPair.Hom.fst (TopPair.sigmaι (fun _ : cell C n ↦ diskBoundaryPair.{w} n) j)
    (diskCenter n)
  have h₁ := sigmaDiskBoundaryPairIso_hom_fst_apply_fst (cell C n) n c
  have h₂ :
      ((TopPair.Hom.fst (sigmaDiskBoundaryPairIso (cell C n) n).hom c).2 : Fin n → ℝ) = 0 := by
    rw [coe_sigmaDiskBoundaryPairIso_hom_fst_apply_snd,
      ContinuousLinearEquiv.unitBallHomeomorph_apply]
    -- The summand of `c` is `diskCenter n` only after unfolding the inclusion of the summand.
    erw [coe_diskCenter_down, map_zero, gaugeRescale_zero]
  refine (characteristicPairMap_fst_apply C n _).trans ?_
  generalize TopPair.Hom.fst (sigmaDiskBoundaryPairIso (cell C n) n).hom c = q at h₁ h₂ ⊢
  obtain ⟨i, y⟩ := q
  obtain rfl : i = j := h₁
  exact congrArg (map n i) h₂

/-- With projective coefficients, the cellular chain group in degree `n` is projective whenever
coproducts indexed by the `n`-cells are exact in `A`. -/
instance projective_cellularChainGroup [Projective R] (n : ℕ)
    [HasExactColimitsOfShape (Discrete (cell C n)) A] :
    Projective (cellularChainGroup C R n) :=
  Projective.of_iso (cellularChainGroupIso C R n).symm
    (Projective.of_isColimit_cofan (coproductIsCoproduct _))

/-- With projective coefficients, the degree-`n` term of the cellular chain complex is projective
whenever coproducts indexed by the `n`-cells are exact in `A`. -/
instance projective_cellularChainComplex_X [Projective R] (n : ℕ)
    [HasExactColimitsOfShape (Discrete (cell C n)) A] :
    Projective ((cellularChainComplex C R).X n) := by
  rw [cellularChainComplex_X]
  infer_instance

end TauCeti
