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

/-!
# The cellular chain group is a coproduct of copies of the coefficients, one per cell

For a relative CW complex and coefficients `R` in an abelian category in which coproducts indexed
by the `n`-cells are exact (for instance modules over a ring), the cellular chain group
`Hₙ(Xⁿ, Xⁿ⁻¹)` is the coproduct of one copy of `R` for each `n`-cell
(`TauCeti.cellularChainGroupIso`).  For modules over a ring `k`, this is the direct sum of copies
of the coefficient module `R`, one per `n`-cell; when `R = k`, it is the free `k`-module on the
`n`-cells.

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

/-- The rescaled coordinate homeomorphism from the Euclidean closed unit disk onto the closed unit
ball of the sup norm on `Fin n → ℝ`. -/
private def diskHomeomorph : TopCat.disk.{w} n ≃ₜ closedBall (0 : Fin n → ℝ) 1 :=
  Homeomorph.ulift.trans <| ((EuclideanSpace.equiv (Fin n) ℝ).unitBallHomeomorph.image _).trans
    (Homeomorph.setCongr (EuclideanSpace.equiv (Fin n) ℝ).image_unitBallHomeomorph_closedBall)

/-- The disk homeomorphisms of all the summands, as an isomorphism in `TopCat` from the disjoint
union of Euclidean disks to `(TauCeti.sigmaDiskPair ι n).fst`. -/
private def sigmaDiskIso :
    TopCat.of (Σ _ : ι, TopCat.disk.{w} n) ≅
      TopCat.of (Σ _ : ι, closedBall (0 : Fin n → ℝ) 1) :=
  TopCat.isoOfHomeo
    { toEquiv := Equiv.sigmaCongrRight fun _ ↦ (diskHomeomorph n).toEquiv
      continuous_toFun := continuous_sigma fun _ ↦ continuous_sigmaMk.comp
        (diskHomeomorph n).continuous
      continuous_invFun := continuous_sigma fun _ ↦ continuous_sigmaMk.comp
        (diskHomeomorph n).symm.continuous }

private lemma norm_diskHomeomorph_diskBoundaryInclusion (y : TopCat.diskBoundary.{w} n) :
    ‖(diskHomeomorph n (TopCat.diskBoundaryInclusion n y) : Fin n → ℝ)‖ = 1 := by
  obtain ⟨⟨y, hy⟩⟩ := y
  -- On a point of the Euclidean unit sphere, the composite is the rescaled coordinate map.
  have h : (diskHomeomorph n (TopCat.diskBoundaryInclusion n ⟨⟨y, hy⟩⟩) : Fin n → ℝ) =
      (EuclideanSpace.equiv (Fin n) ℝ).unitBallHomeomorph y :=
    rfl
  rw [h, ← mem_sphere_zero_iff_norm,
    ← (EuclideanSpace.equiv (Fin n) ℝ).image_unitBallHomeomorph_sphere]
  exact mem_image_of_mem _ hy

/-- The map of pairs `∐ᵢ (Dⁿ, Sⁿ⁻¹) ⟶ TauCeti.sigmaDiskPair ι n` from the disjoint union of
Euclidean disk pairs, given by `diskHomeomorph` on every summand. -/
private def sigmaDiskBoundaryPairHom :
    TopPair.sigma (fun _ : ι ↦ diskBoundaryPair.{w} n) ⟶ sigmaDiskPair ι n :=
  TopPair.ofHom (sigmaDiskIso ι n).hom
    (TopCat.ofHom ⟨fun p ↦ ⟨(sigmaDiskIso ι n).hom ((TopPair.sigma _).map p),
      norm_diskHomeomorph_diskBoundaryInclusion n p.2⟩,
      ((sigmaDiskIso ι n).hom.hom.continuous.comp
        (TopPair.sigma _).map.hom.continuous).subtype_mk _⟩)
    (by ext; rfl)

private lemma surjective_snd_sigmaDiskBoundaryPairHom :
    Function.Surjective (TopPair.Hom.snd (sigmaDiskBoundaryPairHom ι n)) := by
  rintro ⟨⟨i, x⟩, hx : ‖(x : Fin n → ℝ)‖ = 1⟩
  obtain ⟨y, hy, hyx⟩ : (x : Fin n → ℝ) ∈
      (EuclideanSpace.equiv (Fin n) ℝ).unitBallHomeomorph '' sphere 0 1 := by
    rw [(EuclideanSpace.equiv (Fin n) ℝ).image_unitBallHomeomorph_sphere]
    simpa using hx
  refine ⟨⟨i, (ULift.up ⟨y, hy⟩ : ULift.{w} (sphere (0 : EuclideanSpace ℝ (Fin n)) 1))⟩, ?_⟩
  refine Subtype.ext (Sigma.ext rfl (heq_of_eq (Subtype.ext ?_)))
  -- On a point of the Euclidean unit sphere, the map is the rescaled coordinate map.
  exact hyx

/-- The disjoint union of copies, indexed by `ι`, of the Euclidean disk pair
`TauCeti.diskBoundaryPair n` is isomorphic to `TauCeti.sigmaDiskPair ι n`, the disjoint union of
closed unit balls of the sup norm on `Fin n → ℝ` relative to their unit spheres.  On each summand
the isomorphism is the radial rescaling `ContinuousLinearEquiv.unitBallHomeomorph` of the
coordinate identification `EuclideanSpace.equiv`. -/
def sigmaDiskBoundaryPairIso :
    TopPair.sigma (fun _ : ι ↦ diskBoundaryPair.{w} n) ≅ sigmaDiskPair ι n :=
  have : IsIso (TopPair.Hom.fst (sigmaDiskBoundaryPairHom ι n)) :=
    inferInstanceAs (IsIso (sigmaDiskIso ι n).hom)
  have := TopPair.isIso_of_isIso_fst_of_surjective_snd _
    (surjective_snd_sigmaDiskBoundaryPairHom ι n)
  asIso (sigmaDiskBoundaryPairHom ι n)

/-- On the ambient spaces, `TauCeti.sigmaDiskBoundaryPairIso` preserves the summand. -/
@[simp]
lemma sigmaDiskBoundaryPairIso_hom_fst_apply_fst
    (p : (TopPair.sigma fun _ : ι ↦ diskBoundaryPair.{w} n).fst) :
    (TopPair.Hom.fst (sigmaDiskBoundaryPairIso ι n).hom p).1 = p.1 :=
  (rfl)

/-- On the ambient spaces, `TauCeti.sigmaDiskBoundaryPairIso` is the radial rescaling of the
coordinate identification `EuclideanSpace.equiv` in every summand. -/
@[simp]
lemma coe_sigmaDiskBoundaryPairIso_hom_fst_apply_snd
    (p : (TopPair.sigma fun _ : ι ↦ diskBoundaryPair.{w} n).fst) :
    ((TopPair.Hom.fst (sigmaDiskBoundaryPairIso ι n).hom p).2 : Fin n → ℝ) =
      (EuclideanSpace.equiv (Fin n) ℝ).unitBallHomeomorph
        ((p.2 : ULift.{w} (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).down :
          EuclideanSpace ℝ (Fin n)) :=
  (rfl)

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

end TauCeti
