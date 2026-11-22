/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Fibration.ZeroColumn.Basic
public import TauCeti.AlgebraicTopology.Cellular.LocalCoefficients.Coproduct
public import TauCeti.AlgebraicTopology.Cellular.LocalCoefficients.EdgeIncidence
public import TauCeti.AlgebraicTopology.Cellular.LocalCoefficients.Homology

/-!
# The column `p = 0` of the second page of the Serre spectral sequence with local coefficients

Let `p : E ⟶ B` be a Serre fibration and `C ⊆ B` a relative CW complex with skeleta `Xⁿ` and base
`X⁻¹ = D`. The fibre homology `b ↦ Hq(p⁻¹(b); R)` is a local coefficient system on `B` with
path-transport monodromy (`TauCeti.TopCat.serreFiberLocalSystem`); write `Hq(F)` for its restriction
to `C` (`TauCeti.TopCat.serreFiberLocalSystemOn`). This file identifies the column `p = 0` of the
second page of the Serre spectral sequence with the zeroth homology of `C` relative to `D` with
these coefficients,

`E²_{0,q} ≅ H₀(C, D; Hq(F))`

(`TauCeti.TopCat.serreSpectralSequenceSecondPageXZeroIsoTwistedHomology`), through the cellular
homology in degree zero
(`TauCeti.TopCat.serreSpectralSequenceSecondPageXZeroIsoTwistedCellularHomology`). This is the
column `p = 0` of the classical identification `E²_{p,q} ≅ H_p(B; H_q(F))`.

The column `p = 0` of the second page is the quotient of the fibre homology over the `0`-skeleton
`E¹_{0,q} = Hq(p⁻¹(X⁰), p⁻¹(X⁻¹); R)` by the transport differences `a - τⱼ a` along the `1`-cells
(`TauCeti.TopCat.serreSpectralSequenceSecondPageXZeroIsoCokernel`). The cellular homology in degree
zero is the quotient of the cellular chain group `H₀(X⁰, X⁻¹; Hq(F))` by the image of the cellular
differential, which sends a `1`-cell to the difference of its two end points, each read through
the transport along the cell
(`TauCeti.twistedHomologyMap_characteristicCellPairMap_comp_twistedCellularDifferential_zero`).
The comparison has two steps.

* Both `E¹_{0,q}` and `H₀(X⁰, X⁻¹; Hq(F))` are the direct sum of the fibre homology over the
  centres of the `0`-cells (`TauCeti.TopCat.isColimitCofanFiberHomologyToPreimageSkeletonZero` and
  `TauCeti.isColimitCofanιTwistedHomology₀ZeroCellCenter`). This gives an isomorphism
  `Hq(p⁻¹(X⁰), p⁻¹(X⁻¹); R) ≅ H₀(X⁰, X⁻¹; Hq(F))` (`TauCeti.TopCat.serreZeroChainsIso`) which sends
  the class of a fibre homology class over any point of the `0`-skeleton to its class with local
  coefficients (`TauCeti.TopCat.fiberHomologyToPreimageSkeletonZero_comp_serreZeroChainsIso_hom`):
  over a point of `X⁻¹` both vanish, and every other point of `X⁰` is the centre of a `0`-cell.
* Under this isomorphism, the cellular differential of a `1`-cell `j` is the transport difference
  along `j`. The two end points of `D¹` are joined in the simply connected disk, and the
  characteristic map carries the segment between them to the path `TauCeti.cellPath` of the cell
  along which the transport `τⱼ` is taken (`TauCeti.map_characteristicCellMap_eq_cellPath`). So
  the two maps have the same image and the two quotients agree.

## Main definitions

* `TauCeti.TopCat.serreFiberLocalSystemOn`: the local system of fibre homology on `C`.
* `TauCeti.TopCat.serreZeroChainsIso`: `Hq(p⁻¹(X⁰), p⁻¹(X⁻¹); R) ≅ H₀(X⁰, X⁻¹; Hq(F))`.
* `TauCeti.TopCat.serreSpectralSequenceSecondPageXZeroIsoTwistedCellularHomology`: `E²_{0,q}` is
  the cellular homology `H₀(C, D; Hq(F))` of `C` relative to `D`.
* `TauCeti.TopCat.serreSpectralSequenceSecondPageXZeroIsoTwistedHomology`: `E²_{0,q}` is the
  relative singular homology `H₀(C, D; Hq(F))`.

## Main results

* `TauCeti.TopCat.fiberHomologyToPreimageSkeletonZero_comp_serreZeroChainsIso_hom`: the
  identification of the column `p = 0` of the first page with the cellular chains on fibre classes.
* `TauCeti.TopCat.homologyπ_comp_serreSpectralSequenceSecondPageXZeroIsoTwistedCellularHomology_hom`
  says that on the second page the identification is induced by that of the first page, and
  `TauCeti.TopCat.homologyπ_comp_serreSpectralSequenceSecondPageXZeroIsoTwistedHomology_hom` says
  the same for the singular version.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505, Chapter II.
* A. Hatcher,
  [*Spectral Sequences in Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/SSAT/SSch1.pdf),
  Chapter 1, the proof of Theorem 1.3 (the second page with local coefficients).
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Theorem 5.2.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Set Topology Topology.RelCWComplex

universe u

namespace TauCeti

namespace TopCat

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} [T2Space B] {C D : Set B} [RelCWComplex C D]

/-! ### The fibre homology over the `0`-skeleton as cellular chains with local coefficients -/

section ZeroChains

variable (R : Type u) [Ring R] (hp : serreFibrations p)

variable (C) in
/-- The class in the cellular chain group `H₀(X⁰, X⁻¹; Hq(F))` of a fibre homology class over a
point `y` of the `0`-skeleton. -/
def fiberHomologyToTwistedZeroChains (q : ℕ) (y : skeletonObj C 1) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (p.fiber (y : B)) ⟶
      twistedCellularChainGroup.{u, u, u} C (serreFiberLocalSystemOn C R hp q) 0 :=
  (serreFiberLocalSystemObjIso hp (ModuleCat.of R R) q (FundamentalGroupoid.mk (y : B))).inv ≫
    LocalCoefficientSystem.ιTwistedHomology₀
        (skeletonSystem C (serreFiberLocalSystemOn C R hp q) 1) y ≫
      (skeletonPair C 0).twistedHomologyπ _ 0

/-- The class of a fibre homology class over a point `y` of the `0`-skeleton is the class in
`H₀(X⁰, X⁻¹; Hq(F))` of the coefficient at `y`. -/
lemma fiberHomologyToTwistedZeroChains_def (q : ℕ) (y : skeletonObj C 1) :
    fiberHomologyToTwistedZeroChains C R hp q y =
      (serreFiberLocalSystemObjIso hp (ModuleCat.of R R) q (FundamentalGroupoid.mk (y : B))).inv ≫
        LocalCoefficientSystem.ιTwistedHomology₀
            (skeletonSystem C (serreFiberLocalSystemOn C R hp q) 1) y ≫
          (skeletonPair C 0).twistedHomologyπ _ 0 :=
  (rfl)

variable (C) in
/-- **The fibre homology over the `0`-skeleton is the cellular chain group in degree zero with
coefficients in the fibre homology.** The isomorphism
`Hq(p⁻¹(X⁰), p⁻¹(X⁻¹); R) ≅ H₀(X⁰, X⁻¹; Hq(F))` sends the class of a fibre homology class over a
point of the `0`-skeleton to its class with local coefficients
(`TauCeti.TopCat.fiberHomologyToPreimageSkeletonZero_comp_serreZeroChainsIso_hom`). -/
def serreZeroChainsIso (q : ℕ) :
    (preimageSkeletonPair p C 0).singularHomology (ModuleCat.of R R) q ≅
      twistedCellularChainGroup.{u, u, u} C (serreFiberLocalSystemOn C R hp q) 0 :=
  (isColimitCofanFiberHomologyToPreimageSkeletonZero C R hp q).coconePointUniqueUpToIso
    (((IsColimit.precomposeHomEquiv (Discrete.natIso fun k ↦ (serreFiberLocalSystemObjIso hp
        (ModuleCat.of R R) q (FundamentalGroupoid.mk (map 0 k.as 0))).symm) _).symm
      (isColimitCofanιTwistedHomology₀ZeroCellCenter C
        (serreFiberLocalSystemOn C R hp q))).ofIsoColimit
      (Cofan.ext (Iso.refl _) fun _ ↦ Category.comp_id _))

/-- A fibre homology class over a point of `X⁻¹` vanishes in `Hq(p⁻¹(X⁰), p⁻¹(X⁻¹); R)`. -/
private lemma fiberHomologyToPreimageSkeletonZero_eq_zero (q : ℕ) {b : B}
    (hb : b ∈ (skeletonLT C ((0 + 1 : ℕ) : ℕ∞) : Set B))
    (hb' : b ∈ (skeletonLT C (0 : ℕ∞) : Set B)) :
    fiberHomologyToPreimageSkeletonZero p C R q hb = 0 := by
  let g : p.fiber b ⟶ (preimageSkeletonPair p C 0).snd :=
    _root_.TopCat.ofHom ⟨fun e ↦ ⟨e.val, by
      rw [mem_preimage, p.apply_coe_fiber b e]; exact hb'⟩, by fun_prop⟩
  have hg : g ≫ (preimageSkeletonPair p C 0).map = fiberToPreimageSkeletonZero p C hb := by
    ext e
    exact Subtype.ext (coe_fiberToPreimageSkeletonZero_apply hb e).symm
  rw [fiberHomologyToPreimageSkeletonZero_def, ← hg, Functor.map_comp]
  -- The middle object is the ambient homology only up to unfolding `TopPair.toSSetPair`, so the
  -- composite is reassociated by unification rather than by rewriting.
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    ((preimageSkeletonPair p C 0).homologyMap_comp_singularHomologyπ (ModuleCat.of R R) q)).trans
      comp_zero)

/-- A fibre homology class over a point of `X⁻¹` has class zero in `H₀(X⁰, X⁻¹; Hq(F))`. -/
lemma fiberHomologyToTwistedZeroChains_eq_zero (q : ℕ) (y : skeletonObj C 1)
    (hy : (y : B) ∈ (skeletonLT C (0 : ℕ∞) : Set B)) :
    fiberHomologyToTwistedZeroChains C R hp q y = 0 := by
  let y' : (skeletonPair C 0).snd := ⟨y, hy⟩
  have h := LocalCoefficientSystem.ιTwistedHomology₀_homologyMap
    (skeletonSystem C (serreFiberLocalSystemOn C R hp q) (0 + 1)) (skeletonPair C 0).map y'
  rw [fiberHomologyToTwistedZeroChains_def]
  -- `skeletonSystem C _ 1` and `skeletonSystem C _ (0 + 1)` agree only up to unfolding, so the goal
  -- is not type-correct at instance transparency and `rw` cannot reassociate; the composites are
  -- matched by unification.
  refine (congrArg (_ ≫ ·) ((congrArg (· ≫ _) h.symm).trans ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) ((skeletonPair C 0).twistedHomologyMap_comp_twistedHomologyπ _ 0))))).trans ?_
  exact (congrArg (_ ≫ ·) comp_zero).trans comp_zero

variable (C) in
/-- Through `Hq(p⁻¹(X⁰), p⁻¹(X⁻¹); R) ≅ H₀(X⁰, X⁻¹; Hq(F))`, the class of a fibre homology class
over a point `y` of the `0`-skeleton is its class with local coefficients. -/
@[reassoc (attr := simp)]
theorem fiberHomologyToPreimageSkeletonZero_comp_serreZeroChainsIso_hom
    (q : ℕ) (y : skeletonObj C 1) :
    fiberHomologyToPreimageSkeletonZero p C R q y.property ≫
        (serreZeroChainsIso C R hp q).hom =
      fiberHomologyToTwistedZeroChains C R hp q y := by
  rcases mem_skeletonLT_or_exists_map (n := 0) y.property with h | ⟨k, z, -, hz⟩
  · rw [fiberHomologyToPreimageSkeletonZero_eq_zero R q y.property h, zero_comp,
      fiberHomologyToTwistedZeroChains_eq_zero R hp q y h]
  · obtain rfl : y = zeroCellCenter C k :=
      Subtype.ext (hz.symm.trans (congrArg (map 0 k) (Subsingleton.elim _ _)))
    exact (isColimitCofanFiberHomologyToPreimageSkeletonZero C R hp q
      ).comp_coconePointUniqueUpToIso_hom _ ⟨k⟩

end ZeroChains

/-! ### The transport along a `1`-cell through its characteristic map -/

section Edge

variable (j : cell C 1) (R : Type u) [Ring R] (hp : serreFibrations p) (q : ℕ)

/-- Along the characteristic map of a `1`-cell, the pulled-back local system of fibre homology acts
by the local system of fibre homology of `p` on the image path classes. -/
private lemma map_pullback_characteristicCellPairMap
    {x y : FundamentalGroupoid (_root_.TopCat.disk.{u} 1)} (δ : x ⟶ y) :
    ((LocalCoefficientSystem.pullback (TopPair.Hom.fst (characteristicCellPairMap C j)).hom).obj
        (skeletonSystem C (serreFiberLocalSystemOn C R hp q) (1 + 1))).map δ =
      (serreFiberLocalSystem hp (ModuleCat.of R R) q).map
        ((FundamentalGroupoid.map (characteristicCellMap C j)).map δ) := by
  -- The pulled-back system is presented on the ambient space of the disk pair, which is the disk
  -- only up to unfolding `diskBoundaryPair`, so `pullback_obj_map` is applied as a term.
  refine (LocalCoefficientSystem.pullback_obj_map _ _ δ).trans ?_
  -- `skeletonSystem` and `serreFiberLocalSystemOn` are pullbacks along the inclusions of the
  -- skeleton and of `C`, and `TauCeti.characteristicCellMap` is the composite of these inclusions
  -- with the characteristic map, so on the class of a path both sides are transport along the same
  -- path of the base.
  induction δ using Path.Homotopic.Quotient.ind with | mk γ => rfl

/-- A path class in `D¹` from the centre to a point. -/
private def diskPathClass (x : _root_.TopCat.disk.{u} 1) :
    FundamentalGroupoid.mk (diskCenter.{u} 1) ⟶ FundamentalGroupoid.mk x :=
  Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath _ _)

/-- The identification of the fibre of the pulled-back local system at the centre of `D¹` with the
homology of the fibre of `p` over the end point `χⱼ(-1)` of a `1`-cell, by transport along the cell
from the centre to `-e₀`. -/
private def cellCenterToEndIso :
    ((LocalCoefficientSystem.pullback (TopPair.Hom.fst (characteristicCellPairMap C j)).hom).obj
        (skeletonSystem C (serreFiberLocalSystemOn C R hp q) (1 + 1))).obj
          (FundamentalGroupoid.mk (diskCenter.{u} 1)) ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (p.fiber (map 1 j fun _ ↦ -1)) :=
  (serreFiberLocalSystem hp (ModuleCat.of R R) q).mapIso
      ((Groupoid.isoEquivHom _ _).symm
        ((FundamentalGroupoid.map (characteristicCellMap C j)).map
            (diskPathClass ((diskBoundaryPair.{u} 1).map sphereMinus)) ≫
          eqToHom (congrArg FundamentalGroupoid.mk (characteristicCellMap_sphereMinus C j)))) ≪≫
    serreFiberLocalSystemObjIso hp (ModuleCat.of R R) q _

/-- The forward map of `TauCeti.TopCat.cellCenterToEndIso` is the transport in the base. -/
private lemma cellCenterToEndIso_hom :
    (cellCenterToEndIso j R hp q).hom =
      (serreFiberLocalSystem hp (ModuleCat.of R R) q).map
          ((FundamentalGroupoid.map (characteristicCellMap C j)).map
              (diskPathClass ((diskBoundaryPair.{u} 1).map sphereMinus)) ≫
            eqToHom (congrArg FundamentalGroupoid.mk (characteristicCellMap_sphereMinus C j))) ≫
        (serreFiberLocalSystemObjIso hp (ModuleCat.of R R) q _).hom :=
  (rfl)

/-- In the fundamental groupoid of the base, transport from the image of the centre of `D¹` to
`χⱼ(-1)`, followed by the path of the cell, is transport from the image of the centre to
`χⱼ(1)`. -/
private lemma map_diskPathClass_comp_cellPath :
    (FundamentalGroupoid.map (characteristicCellMap C j)).map
        (diskPathClass ((diskBoundaryPair.{u} 1).map sphereMinus)) ≫
      eqToHom (congrArg FundamentalGroupoid.mk (characteristicCellMap_sphereMinus C j)) ≫
        (Path.Homotopic.Quotient.mk (cellPath C j) :
          FundamentalGroupoid.mk (map 1 j fun _ ↦ -1) ⟶
            FundamentalGroupoid.mk (map 1 j fun _ ↦ 1)) =
      (FundamentalGroupoid.map (characteristicCellMap C j)).map
          (diskPathClass ((diskBoundaryPair.{u} 1).map spherePlus)) ≫
        eqToHom (congrArg FundamentalGroupoid.mk (characteristicCellMap_spherePlus C j)) := by
  -- In the simply connected `D¹`, the class from the centre to `e₀` passes through `-e₀`.
  have hδ : diskPathClass ((diskBoundaryPair.{u} 1).map spherePlus) =
      diskPathClass ((diskBoundaryPair.{u} 1).map sphereMinus) ≫
        Path.Homotopic.Quotient.mk diskSegment :=
    Subsingleton.elim (α := Path.Homotopic.Quotient _ _) _ _
  rw [hδ, Functor.map_comp]
  -- The remaining identity is stated at points of `S⁰` read in `D¹`, which instance-level rewriting
  -- does not see through, so it is assembled by unification.
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine congrArg (_ ≫ ·) (Eq.symm ?_)
  refine (congrArg
    (· ≫ eqToHom (congrArg FundamentalGroupoid.mk (characteristicCellMap_spherePlus C j)))
    (map_characteristicCellMap_eq_cellPath C j (Path.Homotopic.Quotient.mk diskSegment))).trans ?_
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) ((eqToHom_trans _ _).trans (eqToHom_refl _ _))).trans (Category.comp_id _))))

omit [T2Space B] in
/-- Transport of fibre homology along a path, read in the local system of fibre homology. -/
private lemma objIso_hom_comp_fiberHomologyTransport_comp {b₀ b₁ : B} (γ : Path b₀ b₁)
    {Z : ModuleCat.{u} R}
    (r : ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
      (ModuleCat.of R R)).obj (p.fiber b₁) ⟶ Z) :
    (serreFiberLocalSystemObjIso hp (ModuleCat.of R R) q (FundamentalGroupoid.mk b₀)).hom ≫
        fiberHomologyTransport hp (ModuleCat.of R R) q γ ≫ r =
      (serreFiberLocalSystem hp (ModuleCat.of R R) q).map (Path.Homotopic.Quotient.mk γ) ≫
        (serreFiberLocalSystemObjIso hp (ModuleCat.of R R) q (FundamentalGroupoid.mk b₁)).hom ≫
          r := by
  simp

/-- **One end point of the edge formula.** A term of the cellular differential of a `1`-cell `j`
with coefficients in the fibre homology, at an end point `s` of `D¹` that the characteristic map
sends to the point `y` of the `0`-skeleton, is transport in the base along the image of the path
class from the centre, followed by the class of the fibre homology over `y`. -/
private lemma pullback_map_comp_ιTwistedHomology₀_eq (s : _root_.TopCat.diskBoundary.{u} 1)
    (y : skeletonObj C 1) (hy : characteristicCellMap C j ((diskBoundaryPair.{u} 1).map s) = y)
    (δ : FundamentalGroupoid.mk (diskCenter.{u} 1) ⟶
      FundamentalGroupoid.mk ((diskBoundaryPair.{u} 1).map s)) :
    ((LocalCoefficientSystem.pullback (TopPair.Hom.fst (characteristicCellPairMap C j)).hom).obj
          (skeletonSystem C (serreFiberLocalSystemOn C R hp q) (1 + 1))).map δ ≫
        (TopPair.subspaceSystemPullbackIso (characteristicCellPairMap C j)
          (skeletonSystem C (serreFiberLocalSystemOn C R hp q) (1 + 1))).hom.app
          (FundamentalGroupoid.mk s) ≫
        LocalCoefficientSystem.ιTwistedHomology₀
            (skeletonSystem C (serreFiberLocalSystemOn C R hp q) 1)
            (TopPair.Hom.snd (characteristicCellPairMap C j) s) ≫
          (skeletonPair C 0).twistedHomologyπ _ 0 =
      (serreFiberLocalSystem hp (ModuleCat.of R R) q).map
          ((FundamentalGroupoid.map (characteristicCellMap C j)).map δ ≫
            eqToHom (congrArg FundamentalGroupoid.mk hy)) ≫
        (serreFiberLocalSystemObjIso hp (ModuleCat.of R R) q _).hom ≫
          fiberHomologyToTwistedZeroChains C R hp q y := by
  have hs : TopPair.Hom.snd (characteristicCellPairMap C j) s = y :=
    Subtype.ext ((congrArg Subtype.val
      (TopPair.Hom.w_apply (characteristicCellPairMap C j) s)).trans hy)
  rw [map_pullback_characteristicCellPairMap, fiberHomologyToTwistedZeroChains_def,
    Iso.hom_inv_id_assoc, Functor.map_comp_assoc]
  -- The pulled-back systems on `D¹` and `S⁰` are presented on the spaces of the disk pair and the
  -- subspace system on the `0`-skeleton is `skeletonSystem C _ 1` only up to unfolding, so the goal
  -- is not type-correct at reducible transparency and the fibrewise lemmas are matched by `erw`.
  erw [eqToHom_map, TopPair.subspaceSystemPullbackIso_hom_app,
    ← LocalCoefficientSystem.eqToHom_comp_ιTwistedHomology₀ _ hs]
  exact congrArg (_ ≫ ·) ((congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans
    (eqToHom_trans_assoc _ _ _))

/-- **The cellular differential of a `1`-cell with coefficients in the fibre homology is the
transport difference along the cell.** Read through the identification of the fibre at the centre
of the disk with the fibre homology over the end point `χⱼ(-1)`, and through
`Hq(p⁻¹(X⁰), p⁻¹(X⁻¹); R) ≅ H₀(X⁰, X⁻¹; Hq(F))`, the cellular differential of the `1`-cell `j` is
the map `a ↦ a - τⱼ a` of `TauCeti.TopCat.oneCellTransportDifference`. -/
@[reassoc]
private lemma twistedCellularDifferential_zero_eq :
    (twistedHomologyDiskBoundaryPairIso 1
        ((LocalCoefficientSystem.pullback (TopPair.Hom.fst (characteristicCellPairMap C j)).hom).obj
          (skeletonSystem C (serreFiberLocalSystemOn C R hp q) (1 + 1)))).inv ≫
      TopPair.twistedHomologyMap (characteristicCellPairMap C j)
        (skeletonSystem C (serreFiberLocalSystemOn C R hp q) (1 + 1)) 1 ≫
      twistedCellularDifferential C (serreFiberLocalSystemOn C R hp q) 0 =
    (cellCenterToEndIso j R hp q).hom ≫ Sigma.ι (fun j : cell C 1 ↦
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (p.fiber (map 1 j fun _ ↦ -1))) j ≫
      oneCellTransportDifference C R hp q ≫
      (serreZeroChainsIso C R hp q).hom := by
  -- Both sides are differences of two terms, one for each end point of the cell: the edge formula
  -- of the cellular differential, and `a ↦ a - τⱼ a`. The terms are matched separately, through
  -- the identification of the fibre classes over the end points with their cellular classes.
  rw [twistedHomologyMap_characteristicCellPairMap_comp_twistedCellularDifferential_zero C _ j
      (diskPathClass _) (diskPathClass _),
    pullback_map_comp_ιTwistedHomology₀_eq j R hp q sphereMinus
      ⟨_, map_mem_skeletonLT_one C j (by norm_num)⟩ (characteristicCellMap_sphereMinus C j),
    pullback_map_comp_ιTwistedHomology₀_eq j R hp q spherePlus
      ⟨_, map_mem_skeletonLT_one C j (by norm_num)⟩ (characteristicCellMap_spherePlus C j),
    ι_oneCellTransportDifference_assoc, Preadditive.sub_comp, Preadditive.comp_sub,
    Category.assoc, fiberHomologyToPreimageSkeletonZero_comp_serreZeroChainsIso_hom C R hp q
      ⟨_, map_mem_skeletonLT_one C j (by norm_num : |(-1 : ℝ)| = 1)⟩,
    fiberHomologyToPreimageSkeletonZero_comp_serreZeroChainsIso_hom C R hp q
      ⟨_, map_mem_skeletonLT_one C j (by norm_num : |(1 : ℝ)| = 1)⟩,
    cellCenterToEndIso_hom]
  -- The terms at the end point `χⱼ(-1)` agree on the nose; at `χⱼ(1)`, the transport along the
  -- cell is absorbed into the path class from the centre of the disk.
  congr 1
  -- The implicit objects of the goal still mention the pulled-back system on the disk pair, which
  -- is not type-correct at instance transparency, so `rw` cannot abstract the composites; `erw`
  -- rewrites at default transparency.
  erw [Category.assoc, objIso_hom_comp_fiberHomologyTransport_comp, ← Functor.map_comp_assoc,
    Category.assoc, map_diskPathClass_comp_cellPath]

end Edge

/-! ### The column `p = 0` of the second page -/

section SecondPage

variable (R : Type u) [Ring R] (hp : serreFibrations p)

variable (C) in
/-- The transport differences along the `1`-cells, read in `H₀(X⁰, X⁻¹; Hq(F))`, and the cellular
differential out of the `1`-cells with coefficients in the fibre homology have the same cokernel. -/
private def cokernelOneCellTransportDifferenceIso (q : ℕ) :
    cokernel (oneCellTransportDifference C R hp q ≫
        (serreZeroChainsIso C R hp q).hom) ≅
      cokernel (twistedCellularDifferential.{u, u, u} C (serreFiberLocalSystemOn C R hp q) 0) where
  hom := cokernel.desc _ (cokernel.π _) (Sigma.hom_ext _ _ fun j ↦ by
    rw [← cancel_epi (cellCenterToEndIso j R hp q).hom]
    simp only [Category.assoc, comp_zero]
    rw [← twistedCellularDifferential_zero_eq_assoc, cokernel.condition, comp_zero, comp_zero])
  inv := cokernel.desc _ (cokernel.π _)
    ((isColimitCofanTwistedHomologyMapCharacteristicCellPairMap C
      (serreFiberLocalSystemOn C R hp q) 1).hom_ext fun ⟨j⟩ ↦ by
    rw [← cancel_epi (twistedHomologyDiskBoundaryPairIso 1 _).inv]
    simp only [Cofan.mk_pt, Cofan.mk_ι_app, comp_zero]
    rw [twistedCellularDifferential_zero_eq_assoc,
      ← Category.assoc (oneCellTransportDifference C R hp q), cokernel.condition, comp_zero,
      comp_zero])
  hom_inv_id := by rw [← cancel_epi (cokernel.π _)]; simp
  inv_hom_id := by rw [← cancel_epi (cokernel.π _)]; simp

variable (C) in
/-- **The column `p = 0` of the second page of the Serre spectral sequence is cellular homology in
degree zero with coefficients in the fibre homology.** For a Serre fibration `p : E ⟶ B` and a
relative CW complex `C ⊆ B` with base `D`, the object `E²_{0,q}` of the second page (numbered `3`)
of the Serre spectral sequence, at `pq = (a, b)` with `b = -1` and `a + b = -q`, is the cellular
homology `H₀(C, D; Hq(F))` of `C` relative to `D` in degree zero, with coefficients in the local
system of fibre homology `b ↦ Hq(p⁻¹(b); R)` with its path-transport monodromy. -/
def serreSpectralSequenceSecondPageXZeroIsoTwistedCellularHomology (q : ℕ) (pq : ℤ × ℤ)
    (hb : pq.2 = -1) (ha : pq.1 + pq.2 = -q) :
    ((serreSpectralSequence C p R).page 3).X pq ≅
      (twistedCellularChainComplex.{u, u, u} C (serreFiberLocalSystemOn C R hp q)).homology 0 :=
  serreSpectralSequenceSecondPageXZeroIsoCokernel C R hp q pq hb ha ≪≫
    (cokernelCompIsIso (serreZeroChainsIso C R hp q).hom _).symm ≪≫
    cokernelOneCellTransportDifferenceIso C R hp q ≪≫
    (twistedCellularChainComplexHomologyZeroIso C (serreFiberLocalSystemOn C R hp q)).symm

variable (C) in
/-- Under `TauCeti.TopCat.serreSpectralSequenceSecondPageXZeroIsoTwistedCellularHomology`, the
projection of the first page onto the second is the identification
`Hq(p⁻¹(X⁰), p⁻¹(X⁻¹); R) ≅ H₀(X⁰, X⁻¹; Hq(F))` of
`TauCeti.TopCat.serreZeroChainsIso`, followed by the projection of the
cellular chains in degree zero onto cellular homology. -/
@[reassoc]
lemma homologyπ_comp_serreSpectralSequenceSecondPageXZeroIsoTwistedCellularHomology_hom (q : ℕ)
    (pq : ℤ × ℤ) (hb : pq.2 = -1) (ha : pq.1 + pq.2 = -q) :
    ((serreSpectralSequence C p R).page 2).homologyπ pq ≫
        ((serreSpectralSequence C p R).iso 2 3 pq rfl le_rfl).hom ≫
        (serreSpectralSequenceSecondPageXZeroIsoTwistedCellularHomology C R hp q pq hb ha).hom =
      ((serreSpectralSequence C p R).page 2).iCycles pq ≫
        (filteredSpaceSpectralSequenceFirstPageXIso (ModuleCat.of R R)
          (monotone_preimageSkeleton p) pq pq.2 (pq.2 + 1) rfl rfl _ rfl q ha).hom ≫
        eqToHom (congrArg (fun P : TopPair.{u} ↦ P.singularHomology (ModuleCat.of R R) q)
          (ofInclusion_preimageSkeleton_eq_preimageSkeletonPair 0 pq.2 (by lia))) ≫
        (serreZeroChainsIso C R hp q).hom ≫
        cokernel.π (twistedCellularDifferential.{u, u, u} C (serreFiberLocalSystemOn C R hp q) 0) ≫
        (twistedCellularChainComplexHomologyZeroIso C (serreFiberLocalSystemOn C R hp q)).inv := by
  rw [serreSpectralSequenceSecondPageXZeroIsoTwistedCellularHomology, Iso.trans_hom, Iso.trans_hom,
    Iso.trans_hom, homologyπ_comp_serreSpectralSequenceSecondPageXZeroIsoCokernel_hom_assoc]
  simp [cokernelOneCellTransportDifferenceIso]

variable (C) in
/-- **The column `p = 0` of the second page of the Serre spectral sequence is the zeroth homology of
`C` relative to `D` with coefficients in the fibre homology.** For a Serre fibration `p : E ⟶ B`
and a relative CW complex `C ⊆ B` with base `D`, the object `E²_{0,q}` of the second page (numbered
`3`) of the Serre spectral sequence, at `pq = (a, b)` with `b = -1` and `a + b = -q`, is the
relative singular homology `H₀(C, D; Hq(F))` with coefficients in the local system of fibre
homology. -/
def serreSpectralSequenceSecondPageXZeroIsoTwistedHomology (q : ℕ) (pq : ℤ × ℤ)
    (hb : pq.2 = -1) (ha : pq.1 + pq.2 = -q) :
    ((serreSpectralSequence C p R).page 3).X pq ≅
      (complexBasePair C).twistedHomology (serreFiberLocalSystemOn C R hp q) 0 :=
  serreSpectralSequenceSecondPageXZeroIsoTwistedCellularHomology C R hp q pq hb ha ≪≫
    twistedCellularSingularHomologyIso C (serreFiberLocalSystemOn C R hp q) 0

variable (C) in
/-- Under `TauCeti.TopCat.serreSpectralSequenceSecondPageXZeroIsoTwistedHomology`, the projection of
the first page onto the second is the identification `Hq(p⁻¹(X⁰), p⁻¹(X⁻¹); R) ≅ H₀(X⁰, X⁻¹; Hq(F))`
of `TauCeti.TopCat.serreZeroChainsIso`, followed by the projection of the cellular chains in degree
zero onto cellular homology and the comparison of cellular with singular homology. -/
@[reassoc]
lemma homologyπ_comp_serreSpectralSequenceSecondPageXZeroIsoTwistedHomology_hom (q : ℕ)
    (pq : ℤ × ℤ) (hb : pq.2 = -1) (ha : pq.1 + pq.2 = -q) :
    ((serreSpectralSequence C p R).page 2).homologyπ pq ≫
        ((serreSpectralSequence C p R).iso 2 3 pq rfl le_rfl).hom ≫
        (serreSpectralSequenceSecondPageXZeroIsoTwistedHomology C R hp q pq hb ha).hom =
      ((serreSpectralSequence C p R).page 2).iCycles pq ≫
        (filteredSpaceSpectralSequenceFirstPageXIso (ModuleCat.of R R)
          (monotone_preimageSkeleton p) pq pq.2 (pq.2 + 1) rfl rfl _ rfl q ha).hom ≫
        eqToHom (congrArg (fun P : TopPair.{u} ↦ P.singularHomology (ModuleCat.of R R) q)
          (ofInclusion_preimageSkeleton_eq_preimageSkeletonPair 0 pq.2 (by lia))) ≫
        (serreZeroChainsIso C R hp q).hom ≫
        cokernel.π (twistedCellularDifferential.{u, u, u} C (serreFiberLocalSystemOn C R hp q) 0) ≫
        (twistedCellularChainComplexHomologyZeroIso C (serreFiberLocalSystemOn C R hp q)).inv ≫
        (twistedCellularSingularHomologyIso C (serreFiberLocalSystemOn C R hp q) 0).hom := by
  rw [serreSpectralSequenceSecondPageXZeroIsoTwistedHomology, Iso.trans_hom,
    homologyπ_comp_serreSpectralSequenceSecondPageXZeroIsoTwistedCellularHomology_hom_assoc]

end SecondPage

end TopCat

end TauCeti
