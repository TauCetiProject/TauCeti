/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.ConstantNaturality
public import TauCeti.Topology.VectorBundle.Orientation.LocalSystem
public import TauCeti.Topology.VectorBundle.Orientation.ThomClass
import TauCeti.Algebra.Category.ModuleCat.SpanSingleton
import TauCeti.AlgebraicTopology.Singular.CompactSupport
import TauCeti.AlgebraicTopology.Singular.MayerVietoris.FiniteUnion
import TauCeti.AlgebraicTopology.Singular.Twisted.Coefficients
import TauCeti.AlgebraicTopology.Singular.Twisted.Equivalence
import TauCeti.Topology.Category.TopCat.Limits.Basic
import TauCeti.Topology.VectorBundle.MayerVietoris.Twisted
import TauCeti.Topology.VectorBundle.MayerVietoris.TwistedDirectedUnion
import TauCeti.Topology.VectorBundle.Thom.Class
import TauCeti.Topology.VectorBundle.Thom.RankDegreeHomology

/-!
# The Thom pair in the rank degree with coefficients in the orientation system

Let `E → B` be a real vector bundle of rank `r` with Thom pair `(E, E₀)`, `E₀` the complement of
the zero section, let `R` be a ring, and let `o(E)` be the orientation local system of `E`
(`TauCeti.VectorBundleOrientationCover.signLocalSystem`), whose fibre over `b` is a copy of `R`
with the two orientations of `E_b` as generators. Pull it back to the total space along the
projection `π`: `π^*o(E)` (`TauCeti.thomPairSignLocalSystem`). This file computes the first
homology group of the Thom pair with these coefficients that can be nonzero,

`Hᵣ(E, E₀; π^*o(E)) ≅ H₀(B; R)`,

over an arbitrary base and without any orientation of `E`
(`TauCeti.thomPairTwistedHomologyFinrankIso`). The twist cancels: on the fibre over `b` the
coefficients are the constant module `o(E)_b`, and the class of the fibre pair `(E_b, E_b ∖ {0})`
read through a linear trivialization, tensored with the orientation of `E_b` read by the same
trivialization, does not change when both readings are reversed. So these classes, the fibre
classes `TauCeti.thomPairSignFiberClass`, are canonical up to the choice of an orientation `ω` of
the model fibre, and the isomorphism sends the fibre class over `b` to the class of the point `b`
(`TauCeti.thomPairTwistedHomologyFinrankIso_hom_thomPairSignFiberClass`). Without twisted
coefficients, `TauCeti.thomPairSingularHomologyFinrankIso` and its oriented variant
`TauCeti.VectorBundleOrientation.thomPairSingularHomologyFinrankIso` identify `Hᵣ(E, E₀; K)` with
`H₀(B; K)` when `1` is the only unit of the commutative ring `K`, or for an oriented bundle.

This is the bottom degree of the Thom isomorphism with coefficients twisted by the orientation
system: by universal coefficients, a homomorphism `Hᵣ(E, E₀; π^*o(E)) ⟶ R` taking the value `1` on
every fibre class is a twisted Thom class of `E`.

## The proof

The proof follows the computation of `Hᵣ(E, E₀; R) ≅ H₀(B; R)` for oriented bundles in
`TauCeti.Topology.VectorBundle.Thom.RankDegreeHomology`, and shares with it the point class
`TauCeti.complZeroPairPointHom` of `Hᵣ(F, F ∖ {0}; R)` and the Mayer–Vietoris induction
`TauCeti.isIso_biUnion_of_mayerVietoris`. The map `H₀(W; R) ⟶ Hᵣ(E|_W, E₀|_W; π^*o(E))`
(`TauCeti.thomPairOverTwistedHomologyFinrankInv`) sends the class of a point to the fibre class
over it (`TauCeti.thomPairOverSignFiberClass`); it is well defined because the fibre classes are
constant along paths (`TauCeti.thomPairOverSignFiberClass_eq_of_path`). Every linear trivialization
at `x` reads the fibre class over `x` the same way (`TauCeti.thomPairOverSignFiberClass_eq`): if it
reads the orientations of `E_x` oppositely, both the generator of the fibre pair and the
trivialization of the coefficients change sign. Over a subset `W` of the base set of a
trivialization of the atlas, the orientations of the fibres read by the trivialization trivialize
`π^*o(E)` over `E|_W`, which identifies the twisted homology with the untwisted homology of the
product `W × F`, and so with `H₀(W; R)`, carrying fibre classes to classes of points. The
Mayer–Vietoris sequence of Thom pairs with local coefficients
(`TauCeti.thomPairOverTwistedMayerVietoris_exact₂`) ends in degree `r`, since the twisted homology
of the Thom pair vanishes below the rank, so the map is an isomorphism over every finite union of
trivializing open sets (`TauCeti.isIso_thomPairOverTwistedHomologyFinrankInv_biUnion`). Both
`H₀(B; R)` and `Hᵣ(E, E₀; π^*o(E))` are the filtered colimits of the corresponding groups over the
finite unions of the chosen trivializing open sets
(`TauCeti.isColimitThomPairFiniteTrivializingUnionTwistedHomologyCocone`), giving the isomorphism
over an arbitrary base.

## Main definitions and results

* `TauCeti.thomPairSignLocalSystem`: the orientation local system pulled back to the total space.
* `TauCeti.fiberThomPairSignLocalSystemIso` and `TauCeti.thomPairSignFiberMap`: the trivialization
  of `π^*o(E)` over the fibre pair over `b` by an orientation `o` of `E_b`, and the map
  `Hₙ(E_b, E_b ∖ {0}; R) ⟶ Hₙ(E, E₀; π^*o(E))` it gives with the inclusion of the fibre pair;
  replacing `o` by `-o` negates it (`TauCeti.thomPairSignFiberMap_neg`).
* `TauCeti.thomPairSignFiberClass`: the fibre class over a point; replacing `ω` by `-ω` negates it
  (`TauCeti.thomPairSignFiberClass_neg`).
* `TauCeti.thomPairOverSignFiberClass_eq`: every linear trivialization at `x` reads the fibre class
  over `x` as the generator of the fibre pair.
* `TauCeti.thomPairSignFiberClass_eq_thomPairSignFiberMap`: for every orientation `o` of `E_b`, the
  fibre class over `b` is the image under `TauCeti.thomPairSignFiberMap` of the generator of
  `Hᵣ(E_b, E_b ∖ {0}; R)` attached to `o` (`TauCeti.orientedFiberGenerator`). This reads the fibre
  class without a trivialization of `E`, as needed to compare it with fibre classes of other
  bundles.
* `TauCeti.isIso_thomPairOverTwistedHomologyFinrankInv_biUnion`:
  `H₀(W; R) ≅ Hᵣ(E|_W, E₀|_W; π^*o(E))` for a finite union `W` of trivializing open sets.
* `TauCeti.thomPairTwistedHomologyFinrankIso`: `Hᵣ(E, E₀; π^*o(E)) ≅ H₀(B; R)` over an arbitrary
  base.
* `TauCeti.thomPairTwistedHomologyFinrankIso_hom_thomPairSignFiberClass`: it sends the fibre class
  over `b` to the class of `b`.
* `TauCeti.thomPairTwistedHomology_hom_ext`: morphisms out of `Hᵣ(E, E₀; π^*o(E))` are determined
  by their values on the fibre classes.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Lemma 10.3 and the proof of Theorem 10.4 (the induction over finite unions
  of trivializing open sets and directed unions of chains), and §12 (the orientation double cover
  and twisted coefficients).
* A. Hatcher, *Algebraic Topology*, Section 3.H (local coefficients and the orientation system)
  and Section 4.D, Theorem 4D.10 and its proof.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Bundle Module Set Topology
open TauCeti.LocalCoefficientSystem (constantFunctor)
open TauCeti.VectorBundleOrientationCover (signLocalSystem signLocalSystemFiberEquiv
  signLocalSystemObjEquiv_pullbackSignLocalSystemIsoOfLift_inv_app_apply)

universe w

namespace TauCeti

variable {B : Type w} [TopologicalSpace B] {F : Type w}
  [NormedAddCommGroup F] [NormedSpace ℝ F] {E : B → Type w}
  [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E] {ι : Type w} [Fintype ι]
  {R : Type w} [Ring R] (hι : Fintype.card ι = finrank ℝ F)

/-! ### The orientation system on the total space -/

variable (F E R) in
/-- The orientation local system `o(E)` of a real vector bundle, pulled back to its total space
along the projection: its fibre over a vector `v` is the fibre of `o(E)` over `π v`. -/
def thomPairSignLocalSystem : LocalCoefficientSystem R (TopCat.of (TotalSpace F E)) :=
  (LocalCoefficientSystem.pullback (X := TopCat.of (TotalSpace F E)) (Y := TopCat.of B)
    ⟨π F E, FiberBundle.continuous_proj F E⟩).obj
      (signLocalSystem F E R hι)

theorem thomPairSignLocalSystem_def :
    thomPairSignLocalSystem F E R hι =
      (LocalCoefficientSystem.pullback (X := TopCat.of (TotalSpace F E)) (Y := TopCat.of B)
        ⟨π F E, FiberBundle.continuous_proj F E⟩).obj (signLocalSystem F E R hι) :=
  (rfl)

/-- The fibres of the pulled-back orientation system are fibres of `o(E)`, so they are projective.
-/
instance projective_thomPairSignLocalSystem_obj [FiniteDimensional ℝ F]
    (v : FundamentalGroupoid (thomPair F E).fst) :
    Projective ((thomPairSignLocalSystem F E R hι).obj v) :=
  LocalCoefficientSystem.projective_pullback_obj_obj (X := TopCat.of (TotalSpace F E)) _ _ v

variable (F E R) in
/-- The pulled-back orientation system `π^*o(E)` restricted to the part `E|_W` of the total space
over `W`. -/
abbrev thomPairOverSignLocalSystem (W : Set B) :
    LocalCoefficientSystem R (thomPairOver F E W).fst :=
  (LocalCoefficientSystem.pullback (X := TopCat.of ↥(π F E ⁻¹' W))
    (ContinuousMap.subtypeVal (π F E ⁻¹' W))).obj (thomPairSignLocalSystem F E R hι)

/-- The trivialization of the pulled-back orientation system over the fibre `E_x` by evaluation
at an orientation of `E_x`: every path in `E_x` projects to the constant path at `x`. -/
private def fiberSignIso {W : Set B} {x : B} (hx : x ∈ W) (ω : Orientation ℝ (E x) ι) :
    (LocalCoefficientSystem.pullback (TopPair.Hom.fst (fiberThomPairOverMap F E hx)).hom).obj
        (thomPairOverSignLocalSystem F E R hι W) ≅
      (constantFunctor _).obj (ModuleCat.of R R) :=
  NatIso.ofComponents (fun _ ↦ (signLocalSystemFiberEquiv hι ω).toModuleIso)
    fun {v v'} q ↦ by
      have h : (FundamentalGroupoid.map (X := TopCat.of (TotalSpace F E)) (Y := TopCat.of B)
          ⟨π F E, FiberBundle.continuous_proj F E⟩).map
          ((FundamentalGroupoid.map (X := TopCat.of ↥(π F E ⁻¹' W))
            (ContinuousMap.subtypeVal (π F E ⁻¹' W))).map
            ((FundamentalGroupoid.map (TopPair.Hom.fst (fiberThomPairOverMap F E hx)).hom).map q)) =
          𝟙 (FundamentalGroupoid.mk x) := by
        induction q using Quotient.ind
        -- `Path.ext rfl` unfolds `fiberThomPairOverMap` (exposed for this purpose): the projected
        -- path is `t ↦ x` by definition.
        exact congrArg (Quotient.mk _) (Path.ext rfl)
      have h' : ((LocalCoefficientSystem.pullback
          (TopPair.Hom.fst (fiberThomPairOverMap F E hx)).hom).obj
          (thomPairOverSignLocalSystem F E R hι W)).map q = 𝟙 _ :=
        (congrArg (signLocalSystem F E R hι).map h).trans
          ((signLocalSystem F E R hι).map_id _)
      rw [h', LocalCoefficientSystem.constantFunctor_obj_map]
      exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- The trivialization of a fibre by the opposite orientation is the negative of the one by `o`. -/
private theorem fiberSignIso_neg_inv {W : Set B} {x : B} (hx : x ∈ W) (o : Orientation ℝ (E x) ι) :
    (fiberSignIso (R := R) hι hx (-o)).inv = -(fiberSignIso hι hx o).inv := by
  ext v : 2
  exact congrArg ModuleCat.ofHom
    (VectorBundleOrientationCover.signLocalSystemFiberEquiv_neg_symm hι o)

/-- Over a subset `W` of the base set of a trivialization `e` of the atlas, the pulled-back
orientation system is trivialized by evaluating at the orientation read as `ω` by it. -/
private def baseSetSignIso (e : Trivialization F (π F E)) [MemTrivializationAtlas e] {W : Set B}
    (hW : W ⊆ e.baseSet) (ω : Orientation ℝ F ι) :
    thomPairOverSignLocalSystem F E R hι W ≅
      (constantFunctor _).obj (ModuleCat.of R R) :=
  ((LocalCoefficientSystem.pullbackCompIso (X := (thomPairOver F E W).fst)
      (Y := TopCat.of (TotalSpace F E)) (Z := TopCat.of B)
      (ContinuousMap.subtypeVal (π F E ⁻¹' W))
      ⟨π F E, FiberBundle.continuous_proj F E⟩).app (signLocalSystem F E R hι)).symm ≪≫
    VectorBundleOrientationCover.pullbackSignLocalSystemIso R hι e ω
      (Y := (thomPairOver F E W).fst)
      ((⟨π F E, FiberBundle.continuous_proj F E⟩ : C(TotalSpace F E, B)).comp
        (ContinuousMap.subtypeVal (π F E ⁻¹' W)))
      fun v ↦ hW v.property

/-- The trivialization over the base set, restricted to a fibre, is the trivialization of the
fibre by the orientation it reads as `ω`. -/
private theorem pullback_map_baseSetSignIso_hom (e : Trivialization F (π F E))
    [MemTrivializationAtlas e] {W : Set B} (hW : W ⊆ e.baseSet) (ω : Orientation ℝ F ι) {x : B}
    (hxW : x ∈ W) :
    (LocalCoefficientSystem.pullback (TopPair.Hom.fst (fiberThomPairOverMap F E hxW)).hom).map
        (baseSetSignIso (R := R) hι e hW ω).hom ≫
      (LocalCoefficientSystem.pullbackConstantIso _ (ModuleCat.of R R)).hom =
    (fiberSignIso hι hxW ((e.mapOrientation ι (hW hxW)).symm ω)).hom := by
  ext v : 2
  unfold baseSetSignIso
  -- `erw`: the components act on fibres of local systems, which are objects of `ModuleCat` only
  -- after unfolding `LocalCoefficientSystem.pullback`, and `pullbackCompIso_inv_app_app` gives the
  -- identity on each fibre.
  erw [NatTrans.comp_app, LocalCoefficientSystem.pullbackConstantIso_hom_app, Category.comp_id,
    LocalCoefficientSystem.pullback_map_app, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Iso.app_inv, LocalCoefficientSystem.pullbackCompIso_inv_app_app, Category.id_comp]
  refine ModuleCat.hom_ext (LinearMap.ext fun f ↦ ?_)
  exact VectorBundleOrientationCover.pullbackSignLocalSystemIso_hom_app_apply hι e ω
    (Y := (thomPairOver F E W).fst)
    ((⟨π F E, FiberBundle.continuous_proj F E⟩ : C(TotalSpace F E, B)).comp
      (ContinuousMap.subtypeVal (π F E ⁻¹' W)))
    (fun v ↦ hW v.property) _ f

/-- Over a subset of the base set of a trivialization `e` of the atlas, the fibre inclusion over
`x`, read through the trivializations of the coefficient systems by the orientation that this
trivialization reads as `ω`, is the fibre inclusion in ordinary homology. -/
@[reassoc]
private theorem fiberSign_comp_twistedHomologyMap_comp_baseSetSign (e : Trivialization F (π F E))
    [MemTrivializationAtlas e] {W : Set B} (hW : W ⊆ e.baseSet) (ω : Orientation ℝ F ι) {x : B}
    (hxW : x ∈ W) (n : ℕ) :
    ((TopPair.ofSubset (X := TopCat.of (E x)) ({0}ᶜ : Set (E x))).twistedHomologyConstantIso
        (ModuleCat.of R R) n).inv ≫
      (TopPair.ofSubset (X := TopCat.of (E x)) ({0}ᶜ : Set (E x))).twistedHomologyCoefficientMap
        (fiberSignIso hι hxW ((e.mapOrientation ι (hW hxW)).symm ω)).inv n ≫
      TopPair.twistedHomologyMap (fiberThomPairOverMap F E hxW)
        (thomPairOverSignLocalSystem F E R hι W) n ≫
      (thomPairOver F E W).twistedHomologyCoefficientMap (baseSetSignIso hι e hW ω).hom n ≫
      ((thomPairOver F E W).twistedHomologyConstantIso (ModuleCat.of R R) n).hom =
    TopPair.singularHomologyMap (fiberThomPairOverMap F E hxW) (ModuleCat.of R R) n := by
  -- Move the change of coefficients over `W` past the fibre inclusion, then compare the two
  -- trivializations of the coefficients on the fibre.
  rw [TopPair.twistedHomologyMap_naturality_assoc,
    TopPair.twistedHomologyConstantIso_hom_pair_naturality,
    ← TopPair.twistedHomologyCoefficientMap_comp_assoc,
    ← TopPair.twistedHomologyCoefficientMap_comp_assoc, Category.assoc,
    pullback_map_baseSetSignIso_hom, Iso.inv_hom_id, TopPair.twistedHomologyCoefficientMap_id,
    Category.id_comp, Iso.inv_hom_id_assoc]

/-- The inclusion `(E|_W, E₀|_W) ⟶ (E|_{W'}, E₀|_{W'})` for `W ⊆ W'`, in the form used by the
restriction maps of pairs of subsets. -/
private abbrev overInclusion {W W' : Set B} (h : W ⊆ W') :
    thomPairOver F E W ⟶ thomPairOver F E W' :=
  TopPair.ofHom (X := TopPair.ofInclusion (inter_subset_left :
      π F E ⁻¹' W ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' W))
    (Y := TopPair.ofInclusion (inter_subset_left :
      π F E ⁻¹' W' ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' W'))
    (TopCat.ofHom (ContinuousMap.inclusion (preimage_mono h)))
    (TopCat.ofHom (ContinuousMap.inclusion (inter_subset_inter_left _ (preimage_mono h)))) rfl

variable (R) in
/-- The identification of the restriction to `W` of the pulled-back orientation system with the
pullback of its restriction to `W'`. -/
private def overRestrIso {W W' : Set B} (h : W ⊆ W') :
    thomPairOverSignLocalSystem F E R hι W ⟶
      (LocalCoefficientSystem.pullback
        (TopPair.Hom.fst (overInclusion (F := F) (E := E) h)).hom).obj
        (thomPairOverSignLocalSystem F E R hι W') :=
  (LocalCoefficientSystem.pullbackCompIso
    (TopCat.ofHom (ContinuousMap.inclusion (preimage_mono h))).hom
    (TopCat.ofHom (ContinuousMap.subtypeVal (π F E ⁻¹' W'))).hom).hom.app
      (thomPairSignLocalSystem F E R hι)

private theorem overRestrIso_app {W W' : Set B} (h : W ⊆ W') (y : FundamentalGroupoid _) :
    (overRestrIso R hι h (F := F) (E := E)).app y = 𝟙 _ :=
  LocalCoefficientSystem.pullbackCompIso_hom_app_app _ _ _ y

private theorem thomPairOverTwistedHomologyMap_eq {W W' : Set B} (h : W ⊆ W') (n : ℕ) :
    thomPairOverTwistedHomologyMap (thomPairSignLocalSystem F E R hι) h n =
      (thomPairOver F E W).twistedHomologyCoefficientMap (overRestrIso R hι h) n ≫
        TopPair.twistedHomologyMap (overInclusion h) (thomPairOverSignLocalSystem F E R hι W') n :=
  (thomPairOverTwistedHomologyMap_def _ h n).trans <|
    (congrArg (HomologicalComplex.homologyMap · n)
      (LocalCoefficientSystem.subsetPairTwistedChainComplexMap_def
        (thomPairSignLocalSystem F E R hι) inter_subset_left inter_subset_left (preimage_mono h)
        (inter_subset_inter_left _ (preimage_mono h)))).trans
      (HomologicalComplex.homologyMap_comp _ _ _)

/-- The restricted orientation system over `W` is the pull-back of `π^*o(E)` along the inclusion
`TopCat.restrictPreimagePairMap` of the pair over `W` into `(E, E₀)`. -/
private theorem thomPairOverSignLocalSystem_eq_pullback_restrictPreimagePairMap (W : Set B) :
    thomPairOverSignLocalSystem F E R hι W =
      (LocalCoefficientSystem.pullback (TopPair.Hom.fst (TopCat.restrictPreimagePairMap
        (X := TopCat.of (TotalSpace F E)) (π F E) (zeroSectionCompl F E) W)).hom).obj
        (thomPairSignLocalSystem F E R hι) := by
  rw [TopCat.restrictPreimagePairMap_fst]
  rfl

/-- The twisted homology of the Thom pair over the whole base, as a pair of subsets of the total
space, is that of the Thom pair `(E, E₀)`. -/
private def overUnivIso (n : ℕ) :
    (thomPairOver F E univ).twistedHomology (thomPairOverSignLocalSystem F E R hι univ) n ≅
      (thomPair F E).twistedHomology (thomPairSignLocalSystem F E R hι) n :=
  have := TopCat.isIso_restrictPreimagePairMap (X := TopCat.of (TotalSpace F E)) (π F E)
    (zeroSectionCompl F E) (S := univ) fun _ ↦ trivial
  have := LocalCoefficientSystem.isIso_relativeTwistedHomologyMap_of_isIso
    (thomPairSignLocalSystem F E R hι)
    (TopCat.restrictPreimagePairMap (X := TopCat.of (TotalSpace F E)) (π F E)
      (zeroSectionCompl F E) univ) n
  (HomologicalComplex.homologyFunctor _ _ n).mapIso
      ((thomPairOver F E univ).twistedChainComplexCoefficientIso
        (eqToIso (thomPairOverSignLocalSystem_eq_pullback_restrictPreimagePairMap hι univ))) ≪≫
    asIso (TopPair.twistedHomologyMap (TopCat.restrictPreimagePairMap
      (X := TopCat.of (TotalSpace F E)) (π F E) (zeroSectionCompl F E) univ)
      (thomPairSignLocalSystem F E R hι) n)

private theorem overUnivIso_hom (n : ℕ) :
    (overUnivIso (R := R) (F := F) (E := E) hι n).hom =
      (thomPairOver F E univ).twistedHomologyCoefficientMap
          (eqToHom (thomPairOverSignLocalSystem_eq_pullback_restrictPreimagePairMap hι univ)) n ≫
        TopPair.twistedHomologyMap (TopCat.restrictPreimagePairMap
          (X := TopCat.of (TotalSpace F E)) (π F E) (zeroSectionCompl F E) univ)
          (thomPairSignLocalSystem F E R hι) n := by
  rw [overUnivIso, Iso.trans_hom, Functor.mapIso_hom, HomologicalComplex.homologyFunctor_map]
  -- `erw`: the coefficient isomorphism is stated for `thomPairOver F E univ` reached through
  -- `TopCat.of`, which `rw` does not see through.
  erw [TopPair.twistedChainComplexCoefficientIso_hom]
  rfl

/-- Comparing `subsetPairTwistedChainComplexMap` with
`TopPair.restrictPreimagePairTwistedChainComplexMap` along the identification of their coefficient
systems. -/
private theorem subsetPairTwistedChainComplexMap_comp_eqToHom {W W' : Set B} (h : W ⊆ W') :
    LocalCoefficientSystem.subsetPairTwistedChainComplexMap (thomPairSignLocalSystem F E R hι)
        inter_subset_left inter_subset_left (preimage_mono h)
        (inter_subset_inter_left _ (preimage_mono h)) ≫
      (thomPairOver F E W').twistedChainComplexCoefficientMap
        (eqToHom (thomPairOverSignLocalSystem_eq_pullback_restrictPreimagePairMap hι W')) =
    (thomPairOver F E W).twistedChainComplexCoefficientMap
        (eqToHom (thomPairOverSignLocalSystem_eq_pullback_restrictPreimagePairMap hι W)) ≫
      TopPair.restrictPreimagePairTwistedChainComplexMap (X := TopCat.of (TotalSpace F E))
        (zeroSectionCompl F E) (thomPairSignLocalSystem F E R hι) (π F E) h := by
  -- Both sides become the inclusion of the pair over `W` into `(E, E₀)` after composing with the
  -- monomorphism from the pair over `W'`.
  refine (cancel_mono (TopPair.twistedChainComplexMap (TopCat.restrictPreimagePairMap
    (X := TopCat.of (TotalSpace F E)) (π F E) (zeroSectionCompl F E) W')
    (thomPairSignLocalSystem F E R hι))).1 ?_
  have hcomp : overInclusion (F := F) (E := E) h ≫
      TopCat.restrictPreimagePairMap (X := TopCat.of (TotalSpace F E)) (π F E)
        (zeroSectionCompl F E) W' =
      TopCat.restrictPreimagePairMap (X := TopCat.of (TotalSpace F E)) (π F E)
        (zeroSectionCompl F E) W :=
    TopPair.hom_ext_of_fst _ (TopCat.ext fun v ↦
      (TopCat.restrictPreimagePairMap_fst_apply _ _ _ _).trans
        (TopCat.restrictPreimagePairMap_fst_apply _ _ _ v).symm)
  -- `erw`: the coefficient systems live on `(thomPairOver F E W').fst`, matching `TopCat.of` only
  -- after unfolding.
  erw [Category.assoc, Category.assoc,
    TopPair.restrictPreimagePairTwistedChainComplexMap_comp_twistedChainComplexMap,
    LocalCoefficientSystem.subsetPairTwistedChainComplexMap_def, Category.assoc,
    TopPair.twistedChainComplexMap_naturality_assoc,
    TopPair.twistedChainComplexMap_congr (thomPairSignLocalSystem F E R hι)
      (congrArg TopPair.Hom.fst hcomp.symm)]
  erw [TopPair.twistedChainComplexMap_comp (overInclusion h)
      (TopCat.restrictPreimagePairMap (X := TopCat.of (TotalSpace F E)) (π F E)
        (zeroSectionCompl F E) W') (thomPairSignLocalSystem F E R hι),
    ← TopPair.twistedChainComplexCoefficientMap_comp_assoc,
    ← TopPair.twistedChainComplexCoefficientMap_comp_assoc,
    ← TopPair.twistedChainComplexCoefficientMap_comp_assoc]
  refine congrArg (fun η ↦ (thomPairOver F E W).twistedChainComplexCoefficientMap (R := R) η ≫ _)
    ?_
  ext v : 2
  erw [NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app,
    LocalCoefficientSystem.pullback_map_app, LocalCoefficientSystem.pullbackCompIso_hom_app_app,
    TopPair.fstPullbackCompIso_hom_app, eqToHom_app, eqToHom_app, eqToHom_app, Category.id_comp,
    Category.comp_id, eqToHom_trans]
  -- Both sides are `eqToHom` between the same fibres, equal by proof irrelevance.
  rfl

/-- Comparing `thomPairOverTwistedHomologyMap` with
`TopPair.restrictPreimagePairTwistedChainComplexMap` along the identification of their coefficient
systems. -/
private theorem thomPairOverTwistedHomologyMap_comp_eqToHom {W W' : Set B} (h : W ⊆ W') (n : ℕ) :
    thomPairOverTwistedHomologyMap (thomPairSignLocalSystem F E R hι) h n ≫
        (thomPairOver F E W').twistedHomologyCoefficientMap
          (eqToHom (thomPairOverSignLocalSystem_eq_pullback_restrictPreimagePairMap hι W')) n =
      (thomPairOver F E W).twistedHomologyCoefficientMap
          (eqToHom (thomPairOverSignLocalSystem_eq_pullback_restrictPreimagePairMap hι W)) n ≫
        HomologicalComplex.homologyMap (TopPair.restrictPreimagePairTwistedChainComplexMap
          (X := TopCat.of (TotalSpace F E)) (zeroSectionCompl F E)
          (thomPairSignLocalSystem F E R hι) (π F E) h) n := by
  rw [thomPairOverTwistedHomologyMap_def]
  exact ((HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    (congrArg (HomologicalComplex.homologyMap · n)
      (subsetPairTwistedChainComplexMap_comp_eqToHom hι h))).trans
    (HomologicalComplex.homologyMap_comp _ _ n)

/-- Restriction from `W` to `univ`, followed by `overUnivIso`, is the inclusion of the pair over
`W` into `(E, E₀)` (up to the identification of coefficient systems). -/
private theorem thomPairOverTwistedHomologyMap_subset_univ_comp_overUnivIso_hom (W : Set B)
    (n : ℕ) :
    thomPairOverTwistedHomologyMap (thomPairSignLocalSystem F E R hι) (subset_univ W) n ≫
        (overUnivIso hι n).hom =
      (thomPairOver F E W).twistedHomologyCoefficientMap
          (eqToHom (thomPairOverSignLocalSystem_eq_pullback_restrictPreimagePairMap hι W)) n ≫
        TopPair.twistedHomologyMap (TopCat.restrictPreimagePairMap
          (X := TopCat.of (TotalSpace F E)) (π F E) (zeroSectionCompl F E) W)
          (thomPairSignLocalSystem F E R hι) n := by
  rw [overUnivIso_hom, ← Category.assoc, thomPairOverTwistedHomologyMap_comp_eqToHom,
    Category.assoc]
  congr 1
  exact (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    (congrArg (HomologicalComplex.homologyMap · n)
      (TopPair.restrictPreimagePairTwistedChainComplexMap_comp_twistedChainComplexMap
        (X := TopCat.of (TotalSpace F E)) (zeroSectionCompl F E)
        (thomPairSignLocalSystem F E R hι) (π F E) (subset_univ W)))

private theorem thomPairOverTwistedMayerVietorisToBiprod_eq (U V : Set B) (n : ℕ) :
    thomPairOverTwistedMayerVietorisToBiprod (thomPairSignLocalSystem F E R hι) U V n =
      biprod.lift
        (thomPairOverTwistedHomologyMap (thomPairSignLocalSystem F E R hι)
          (inter_subset_left : U ∩ V ⊆ U) n)
        (-thomPairOverTwistedHomologyMap (thomPairSignLocalSystem F E R hι)
          (inter_subset_right : U ∩ V ⊆ V) n) := by
  apply biprod.hom_ext <;> simp

private theorem thomPairOverTwistedMayerVietorisFromBiprod_eq (U V : Set B) (n : ℕ) :
    thomPairOverTwistedMayerVietorisFromBiprod (thomPairSignLocalSystem F E R hι) U V n =
      biprod.desc
        (thomPairOverTwistedHomologyMap (thomPairSignLocalSystem F E R hι)
          (subset_union_left : U ⊆ U ∪ V) n)
        (thomPairOverTwistedHomologyMap (thomPairSignLocalSystem F E R hι)
          (subset_union_right : V ⊆ U ∪ V) n) := by
  apply biprod.hom_ext' <;> simp

/-! ### Fibre trivializations and the fibre map -/

omit [Fintype ι] in
/-- The constant lift `⟨b, o⟩` lies over the projection of the fibre over `b`. -/
private theorem proj_const_eq_proj_fiberThomPairMap (b : B) (o : Orientation ℝ (E b) ι)
    (x : (TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).fst) :
    (ContinuousMap.const _ (⟨b, o⟩ : VectorBundleOrientationCover F E ι) x).proj =
      ((⟨π F E, FiberBundle.continuous_proj F E⟩ : C(TotalSpace F E, B)).comp
        (TopPair.Hom.fst (fiberThomPairMap F E b)).hom) x :=
  (congrArg TotalSpace.proj (fiberThomPairMap_fst_apply F E b x)).symm

variable (F E R) in
/-- The trivialization of the pulled-back orientation system `π^*o(E)` over the fibre pair
`(E_b, E_b ∖ {0})` by evaluation at an orientation `o` of `E_b`: the trivialization along the
constant lift `⟨b, o⟩` of the fibre to the orientation cover. -/
def fiberThomPairSignLocalSystemIso (b : B) (o : Orientation ℝ (E b) ι) :
    (LocalCoefficientSystem.pullback (TopPair.Hom.fst (fiberThomPairMap F E b)).hom).obj
        (thomPairSignLocalSystem F E R hι) ≅
      (constantFunctor _).obj (ModuleCat.of R R) :=
  (LocalCoefficientSystem.pullback (TopPair.Hom.fst (fiberThomPairMap F E b)).hom).mapIso
      (eqToIso (thomPairSignLocalSystem_def hι)) ≪≫
    ((LocalCoefficientSystem.pullbackCompIso (TopPair.Hom.fst (fiberThomPairMap F E b)).hom
      (Y := TopCat.of (TotalSpace F E)) (Z := TopCat.of B)
      ⟨π F E, FiberBundle.continuous_proj F E⟩).app (signLocalSystem F E R hι)).symm ≪≫
    VectorBundleOrientationCover.pullbackSignLocalSystemIsoOfLift R hι
      ((⟨π F E, FiberBundle.continuous_proj F E⟩ : C(TotalSpace F E, B)).comp
        (TopPair.Hom.fst (fiberThomPairMap F E b)).hom)
      (ContinuousMap.const _ ⟨b, o⟩) (proj_const_eq_proj_fiberThomPairMap b o)

/-- The trivializations of the fibre pair by opposite orientations are opposite. -/
@[simp]
theorem fiberThomPairSignLocalSystemIso_neg_inv (b : B) (o : Orientation ℝ (E b) ι) :
    (fiberThomPairSignLocalSystemIso F E R hι b (-o)).inv =
      -(fiberThomPairSignLocalSystemIso F E R hι b o).inv := by
  unfold fiberThomPairSignLocalSystemIso
  -- `erw`: the composite of isomorphisms of local systems lives in the functor category
  -- `LocalCoefficientSystem`, and `pullbackCompIso` uses `Functor.comp_obj`.
  erw [Iso.trans_inv, Iso.trans_inv, Iso.trans_inv, Iso.trans_inv,
    VectorBundleOrientationCover.pullbackSignLocalSystemIsoOfLift_inv_of_eq_deck hι _
      (s := ContinuousMap.const _ ⟨b, o⟩) (proj_const_eq_proj_fiberThomPairMap b o)
      (proj_const_eq_proj_fiberThomPairMap b (-o)) fun _ ↦
      (VectorBundleOrientationCover.deck_apply (⟨b, o⟩ : VectorBundleOrientationCover F E ι)).symm,
    Preadditive.neg_comp, Preadditive.neg_comp]

variable (F E R) in
/-- The map `Hₙ(E_b, E_b ∖ {0}; R) ⟶ Hₙ(E, E₀; π^*o(E))` induced by the inclusion of the fibre pair
over `b`, with the coefficients over the fibre trivialized by an orientation `o` of `E_b`
(`TauCeti.fiberThomPairSignLocalSystemIso`). -/
def thomPairSignFiberMap (b : B) (o : Orientation ℝ (E b) ι) (n : ℕ) :
    (TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).singularHomology
        (ModuleCat.of R R) n ⟶
      (thomPair F E).twistedHomology (thomPairSignLocalSystem F E R hι) n :=
  ((TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).twistedHomologyConstantIso
      (ModuleCat.of R R) n).inv ≫
    (TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).twistedHomologyCoefficientMap
      (fiberThomPairSignLocalSystemIso F E R hι b o).inv n ≫
    TopPair.twistedHomologyMap (fiberThomPairMap F E b) (thomPairSignLocalSystem F E R hι) n

/-- The fibre map is the comparison with chains twisted by the constant system, the change of
coefficients by the inverse of the trivialization by `o`, and the inclusion of the fibre pair. -/
theorem thomPairSignFiberMap_def (b : B) (o : Orientation ℝ (E b) ι) (n : ℕ) :
    thomPairSignFiberMap F E R hι b o n =
      ((TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).twistedHomologyConstantIso
          (ModuleCat.of R R) n).inv ≫
        (TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).twistedHomologyCoefficientMap
          (fiberThomPairSignLocalSystemIso F E R hι b o).inv n ≫
        TopPair.twistedHomologyMap (fiberThomPairMap F E b) (thomPairSignLocalSystem F E R hι) n :=
  (rfl)

/-- Trivializing the coefficients by the opposite orientation negates the fibre map. -/
@[simp]
theorem thomPairSignFiberMap_neg (b : B) (o : Orientation ℝ (E b) ι) (n : ℕ) :
    thomPairSignFiberMap F E R hι b (-o) n = -thomPairSignFiberMap F E R hι b o n := by
  rw [thomPairSignFiberMap, thomPairSignFiberMap, fiberThomPairSignLocalSystemIso_neg_inv,
    TopPair.twistedHomologyCoefficientMap_neg, Preadditive.neg_comp, Preadditive.comp_neg]

/-- Over a vector `v` of the fibre, the inverse of the trivialization by `o` sends `r` to the
element of the fibre of `o(E)` whose value at the orientation `o` is `r`. -/
theorem liftFiberEquiv_fiberThomPairSignLocalSystemIso_inv_app_apply (x : B)
    (o : Orientation ℝ (E x) ι)
    (v : FundamentalGroupoid (TopPair.ofSubset (X := TopCat.of (E x)) ({0}ᶜ : Set (E x))).fst)
    (r : R) :
    VectorBundleOrientationCover.liftFiberEquiv hι ⟨x, o⟩
        (congrArg TotalSpace.proj (fiberThomPairMap_fst_apply F E x v.as)).symm
        (((LocalCoefficientSystem.pullback (TopPair.Hom.fst (fiberThomPairMap F E x)).hom).map
          (eqToHom (thomPairSignLocalSystem_def hι))).app v
          ((fiberThomPairSignLocalSystemIso F E R hι x o).inv.app v r)) = r := by
  unfold fiberThomPairSignLocalSystemIso
  -- `erw`: the composite of isomorphisms of local systems is in the functor category.
  erw [Iso.trans_inv, Iso.trans_inv, NatTrans.comp_app, NatTrans.comp_app,
    ← ConcreteCategory.comp_apply, Category.assoc, Functor.mapIso_inv, eqToIso.inv,
    LocalCoefficientSystem.pullback_map_app, eqToHom_app, eqToHom_trans, eqToHom_refl,
    Category.comp_id, Iso.symm_inv, Iso.app_hom,
    LocalCoefficientSystem.pullbackCompIso_hom_app_app, Category.comp_id]
  exact (VectorBundleOrientationCover.liftFiberEquiv_apply hι _ _ _).trans
    (signLocalSystemObjEquiv_pullbackSignLocalSystemIsoOfLift_inv_app_apply
      hι ((⟨π F E, FiberBundle.continuous_proj F E⟩ : C(TotalSpace F E, B)).comp
        (TopPair.Hom.fst (fiberThomPairMap F E x)).hom) (ContinuousMap.const _ ⟨x, o⟩)
      (proj_const_eq_proj_fiberThomPairMap x o) v.as r)

/-- On the fibre pair over `x`, the trivialization by `o` of the orientation system over the whole
base, carried to the Thom pair, is the trivialization by `o` of `π^*o(E)` over the fibre pair. -/
private theorem fiberSignIso_inv_comp_eqToHom (x : B) (o : Orientation ℝ (E x) ι) :
    ((fiberSignIso (R := R) hι (mem_univ x) o).inv ≫
      (LocalCoefficientSystem.pullback
        (TopPair.Hom.fst (fiberThomPairOverMap F E (mem_univ x))).hom).map
        (eqToHom (thomPairOverSignLocalSystem_eq_pullback_restrictPreimagePairMap hι univ))) ≫
      (TopPair.fstPullbackCompIso (fiberThomPairOverMap F E (mem_univ x))
        (TopCat.restrictPreimagePairMap (X := TopCat.of (TotalSpace F E)) (π F E)
          (zeroSectionCompl F E) univ) (thomPairSignLocalSystem F E R hι)).inv ≫
      eqToHom (congrArg (fun g ↦ (LocalCoefficientSystem.pullback (TopPair.Hom.fst g).hom).obj
        (thomPairSignLocalSystem F E R hι))
        (fiberThomPairOverMap_comp_restrictPreimagePairMap F E (mem_univ x))) =
    (fiberThomPairSignLocalSystemIso F E R hι x o).inv := by
  have hfg := fiberThomPairOverMap_comp_restrictPreimagePairMap F E (mem_univ x)
  ext v : 2
  refine ModuleCat.hom_ext (LinearMap.ext fun r ↦ ?_)
  apply (VectorBundleOrientationCover.liftFiberEquiv hι ⟨x, o⟩
    (proj_const_eq_proj_fiberThomPairMap x o v.as)).injective
  -- Both sides evaluate at `⟨x, o⟩` to `r`, after cancelling the transports between fibres
  -- over `x`.
  refine Eq.trans ?_
    (liftFiberEquiv_fiberThomPairSignLocalSystemIso_inv_app_apply (R := R) hι x o v r).symm
  -- `erw`: `TopPair.fstPullbackCompIso_inv_app` and `ModuleCat.comp_apply` match only up to
  -- unfolding `LocalCoefficientSystem.pullback`.
  simp only [NatTrans.comp_app, LocalCoefficientSystem.pullback_map_app, eqToHom_app]
  erw [TopPair.fstPullbackCompIso_inv_app, Category.id_comp, ModuleCat.comp_apply]
  have hv : (TopPair.Hom.fst (fiberThomPairOverMap F E (mem_univ x) ≫
      TopCat.restrictPreimagePairMap (X := TopCat.of (TotalSpace F E)) (π F E)
        (zeroSectionCompl F E) univ) v.as).proj = x :=
    (congrArg (fun g ↦ π F E (TopPair.Hom.fst g v.as)) hfg).trans
      (congrArg TotalSpace.proj (fiberThomPairMap_fst_apply F E x v.as))
  refine (VectorBundleOrientationCover.liftFiberEquiv_eqToHom_apply (R := R) hι
    (congrArg (fun g ↦ π F E (TopPair.Hom.fst g v.as)) hfg) _
    (rfl : (⟨x, o⟩ : VectorBundleOrientationCover F E ι) = ⟨x, o⟩) hv.symm _ _).trans ?_
  erw [ModuleCat.comp_apply]
  refine (VectorBundleOrientationCover.liftFiberEquiv_eqToHom_apply (R := R) hι hv.symm _ rfl rfl
    hv.symm _).trans ?_
  exact ((VectorBundleOrientationCover.liftFiberEquiv_apply hι _ _ _).trans
    (VectorBundleOrientationCover.signLocalSystemFiberEquiv_apply hι o _).symm).trans
    ((VectorBundleOrientationCover.signLocalSystemFiberEquiv (R := R) hι o).apply_symm_apply r)

/-- Through the identification of the pair over the whole base with the Thom pair, the fibre
inclusion into the pair over the whole base, with the coefficients trivialized by `o`, is the fibre
inclusion into the Thom pair, with the coefficients trivialized by `o`. -/
private theorem twistedHomologyCoefficientMap_fiberSignIso_inv_comp_overUnivIso_hom (x : B)
    (o : Orientation ℝ (E x) ι) (n : ℕ) :
    (TopPair.ofSubset (X := TopCat.of (E x)) ({0}ᶜ : Set (E x))).twistedHomologyCoefficientMap
        (fiberSignIso (R := R) hι (mem_univ x) o).inv n ≫
      TopPair.twistedHomologyMap (fiberThomPairOverMap F E (mem_univ x))
        (thomPairOverSignLocalSystem F E R hι univ) n ≫ (overUnivIso hι n).hom =
    (TopPair.ofSubset (X := TopCat.of (E x)) ({0}ᶜ : Set (E x))).twistedHomologyCoefficientMap
        (fiberThomPairSignLocalSystemIso F E R hι x o).inv n ≫
      TopPair.twistedHomologyMap (fiberThomPairMap F E x) (thomPairSignLocalSystem F E R hι) n := by
  rw [overUnivIso_hom, TopPair.twistedHomologyMap_naturality_assoc,
    TopPair.twistedHomologyMap_comp_of_comp_eq (fiberThomPairOverMap F E (mem_univ x))
      (TopCat.restrictPreimagePairMap (X := TopCat.of (TotalSpace F E)) (π F E)
        (zeroSectionCompl F E) univ) (thomPairSignLocalSystem F E R hι)
      (fiberThomPairOverMap_comp_restrictPreimagePairMap F E (mem_univ x)),
    ← TopPair.twistedHomologyCoefficientMap_comp_assoc,
    ← TopPair.twistedHomologyCoefficientMap_comp_assoc]
  congr 2
  exact fiberSignIso_inv_comp_eqToHom hι x o

/-! ### Fibre classes over subsets of the base -/

section FiberClass

variable [FiniteDimensional ℝ F] (ω : Orientation ℝ F ι)

variable (R) in
/-- The fibre class over `x ∈ W` in `Hᵣ(E|_W, E₀|_W; π^*o(E))`, read through a linear trivialization
`e` at `x`: the image of the class of the fibre pair `(E_x, E_x ∖ {0})` which `e` reads as the
point class of `1` in `Hᵣ(F, F ∖ {0}; R)`, with the coefficients `o(E)_x` trivialized by the
orientation of `E_x` which `e` reads as `ω`. It does not depend on `e`
(`TauCeti.thomPairOverSignFiberClassOf_eq`). -/
def thomPairOverSignFiberClassOf (e : Trivialization F (π F E)) [e.IsLinear ℝ] {x : B}
    (hx : x ∈ e.baseSet) {W : Set B} (hxW : x ∈ W) :
    (thomPairOver F E W).twistedHomology (thomPairOverSignLocalSystem F E R hι W) (finrank ℝ F) :=
  TopPair.twistedHomologyMap (fiberThomPairOverMap F E hxW) (thomPairOverSignLocalSystem F E R hι W)
    (finrank ℝ F)
    ((TopPair.ofSubset (X := TopCat.of (E x)) ({0}ᶜ : Set (E x))).twistedHomologyCoefficientMap
      (fiberSignIso hι hxW ((e.mapOrientation ι hx).symm ω)).inv (finrank ℝ F)
      (((TopPair.ofSubset (X := TopCat.of (E x)) ({0}ᶜ : Set (E x))).twistedHomologyConstantIso
        (ModuleCat.of R R) (finrank ℝ F)).inv
        (TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ x hx).complZeroPairIso.inv
          (ModuleCat.of R R) (finrank ℝ F)
          (complZeroPairPointHom (ModuleCat.of R R) F (finrank ℝ F) rfl (1 : R)))))

/-- Over a subset `W` of the base set of a trivialization `e` of the atlas, the trivialization
identifies `Hᵣ(E|_W, E₀|_W; π^*o(E))` with `H₀(W; R)`. -/
private def localIso (e : Trivialization F (π F E)) [MemTrivializationAtlas e] {W : Set B}
    (hW : W ⊆ e.baseSet) :
    (thomPairOver F E W).twistedHomology (thomPairOverSignLocalSystem F E R hι W) (finrank ℝ F) ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} R) 0).obj
        (ModuleCat.of R R)).obj (TopCat.of W) :=
  (HomologicalComplex.homologyFunctor _ _ (finrank ℝ F)).mapIso
      ((thomPairOver F E W).twistedChainComplexCoefficientIso (baseSetSignIso hι e hW ω)) ≪≫
    (thomPairOver F E W).twistedHomologyConstantIso (ModuleCat.of R R) (finrank ℝ F) ≪≫
    asIso (TopPair.singularHomologyMap (e.thomPairOverIso ℝ hW).hom
      (ModuleCat.of R R) (finrank ℝ F)) ≪≫
    prodThomPairSingularHomologyIso (ModuleCat.of R R) W F 0 (finrank ℝ F)

private theorem localIso_hom (e : Trivialization F (π F E)) [MemTrivializationAtlas e] {W : Set B}
    (hW : W ⊆ e.baseSet) :
    (localIso (R := R) hι ω e hW).hom =
      (thomPairOver F E W).twistedHomologyCoefficientMap (baseSetSignIso hι e hW ω).hom
          (finrank ℝ F) ≫
        ((thomPairOver F E W).twistedHomologyConstantIso (ModuleCat.of R R) (finrank ℝ F)).hom ≫
        TopPair.singularHomologyMap (e.thomPairOverIso ℝ hW).hom
          (ModuleCat.of R R) (finrank ℝ F) ≫
        (prodThomPairSingularHomologyIso (ModuleCat.of R R) W F 0 (finrank ℝ F)).hom := by
  simp only [localIso, Iso.trans_hom, Functor.mapIso_hom, HomologicalComplex.homologyFunctor_map,
    TopPair.twistedChainComplexCoefficientIso_hom, asIso_hom]

/-- Through a trivialization `e` of the atlas, the fibre class over `x ∈ W` read through that
trivialization is the class of the point `x`. -/
private theorem localIso_hom_thomPairOverSignFiberClassOf (e : Trivialization F (π F E))
    [MemTrivializationAtlas e] {W : Set B} (hW : W ⊆ e.baseSet) {x : B} (hxW : x ∈ W) :
    (localIso hι ω e hW).hom (thomPairOverSignFiberClassOf R hι ω e (hW hxW) hxW) =
      singularHomology₀Section (ModuleCat.of R R) (X := TopCat.of W) ⟨x, hxW⟩ 1 := by
  have h := ConcreteCategory.congr_hom
    (fiberSign_comp_twistedHomologyMap_comp_baseSetSign_assoc (R := R) hι e hW ω hxW (finrank ℝ F)
      (TopPair.singularHomologyMap (e.thomPairOverIso ℝ hW).hom
          (ModuleCat.of R R) (finrank ℝ F) ≫
        (prodThomPairSingularHomologyIso (ModuleCat.of R R) W F 0 (finrank ℝ F)).hom))
    (TopPair.singularHomologyMap (e.continuousLinearEquivAt
      ℝ x (hW hxW)).complZeroPairIso.inv (ModuleCat.of R R) (finrank ℝ F)
      (complZeroPairPointHom (ModuleCat.of R R) F (finrank ℝ F) rfl (1 : R)))
  rw [localIso_hom, thomPairOverSignFiberClassOf]
  simp only [ConcreteCategory.comp_apply] at h ⊢
  rw [h, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← TopPair.singularHomologyMap_comp_assoc,
    Trivialization.fiberThomPairOverMap_comp_thomPairOverIso_hom, ← ConcreteCategory.comp_apply,
    ← TopPair.singularHomologyMap_comp_assoc, Iso.inv_hom_id_assoc, ConcreteCategory.comp_apply,
    singularHomologyMap_prodThomPairFiberMap_complZeroPairPointHom_one, Iso.inv_hom_id_apply]

/-- **The fibre class does not depend on the linear trivialization through which it is read**: two
trivializations reading the fibre orientation alike read the generator alike, and reading it
oppositely changes both the generator and the trivialization of the coefficients by a sign. -/
theorem thomPairOverSignFiberClassOf_eq (e e' : Trivialization F (π F E)) [e.IsLinear ℝ]
    [e'.IsLinear ℝ] {x : B} (hx : x ∈ e.baseSet) (hx' : x ∈ e'.baseSet) {W : Set B} (hxW : x ∈ W) :
    thomPairOverSignFiberClassOf R hι ω e hx hxW =
      thomPairOverSignFiberClassOf R hι ω e' hx' hxW := by
  set o := (e.mapOrientation ι hx).symm ω
  have ho : e.mapOrientation ι hx o = ω := Equiv.apply_symm_apply _ ω
  rcases Orientation.eq_or_eq_neg (e'.mapOrientation ι hx' o) ω
    (Nat.card_eq_fintype_card.trans hι) with h | h
  · have h' : (e'.mapOrientation ι hx').symm ω = o := (Equiv.symm_apply_eq _).2 h.symm
    have hinv := e.singularHomologyMap_complZeroPairIso_inv_eq_of_mapOrientation_eq e' hx hx' hι
      (ModuleCat.of R R) (h.trans ho.symm) (finrank ℝ F)
    rw [thomPairOverSignFiberClassOf, thomPairOverSignFiberClassOf, h', hinv]
  · have h' : (e'.mapOrientation ι hx').symm ω = -o := e'.mapOrientation_symm_eq_neg_of_eq_neg hx' h
    have hinv := e.singularHomologyMap_complZeroPairIso_inv_eq_neg_of_mapOrientation_eq_neg e' hx
      hx' hι (ModuleCat.of R R) (h.trans (congrArg Neg.neg ho.symm)) (finrank ℝ F)
    rw [thomPairOverSignFiberClassOf, thomPairOverSignFiberClassOf, h', hinv, fiberSignIso_neg_inv,
      TopPair.twistedHomologyCoefficientMap_neg]
    simp only [ModuleCat.hom_neg, LinearMap.neg_apply, map_neg, neg_neg, o]

/-- Restriction carries fibre classes to fibre classes. -/
private theorem thomPairOverTwistedHomologyMap_thomPairOverSignFiberClassOf
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] {x : B} (hx : x ∈ e.baseSet) {W W' : Set B}
    (h : W ⊆ W') (hxW : x ∈ W) :
    thomPairOverTwistedHomologyMap (thomPairSignLocalSystem F E R hι) h (finrank ℝ F)
        (thomPairOverSignFiberClassOf R hι ω e hx hxW) =
      thomPairOverSignFiberClassOf R hι ω e hx (h hxW) := by
  have hfg : fiberThomPairOverMap F E hxW ≫ overInclusion h = fiberThomPairOverMap F E (h hxW) :=
    TopPair.hom_ext_of_fst _ (TopCat.ext fun _ ↦ rfl)
  have hco : ((fiberSignIso hι hxW ((e.mapOrientation ι hx).symm ω)).inv ≫
      (LocalCoefficientSystem.pullback (TopPair.Hom.fst (fiberThomPairOverMap F E hxW)).hom).map
        (overRestrIso R hι h)) ≫
      (TopPair.fstPullbackCompIso (fiberThomPairOverMap F E hxW) (overInclusion h)
        (thomPairOverSignLocalSystem F E R hι W')).inv ≫
      eqToHom (congrArg (fun g ↦ (LocalCoefficientSystem.pullback (TopPair.Hom.fst g).hom).obj
        (thomPairOverSignLocalSystem F E R hι W')) hfg) =
      (fiberSignIso hι (h hxW) ((e.mapOrientation ι hx).symm ω)).inv := by
    ext v : 2
    simp only [NatTrans.comp_app, LocalCoefficientSystem.pullback_map_app, overRestrIso_app,
      TopPair.fstPullbackCompIso_inv_app, eqToHom_app]
    -- Both sides are evaluation at the same orientation of `E_x`; the remaining `eqToHom` is
    -- between fibres of `o(E)` over the projections of `v` along the two fibre inclusions, which
    -- are `x` by definition of `fiberThomPairOverMap`, so it is the identity.
    rfl
  rw [thomPairOverTwistedHomologyMap_eq, thomPairOverSignFiberClassOf, thomPairOverSignFiberClassOf,
    ← ConcreteCategory.comp_apply, TopPair.twistedHomologyMap_naturality_assoc,
    TopPair.twistedHomologyMap_comp_of_comp_eq _ _ _ hfg, ← ConcreteCategory.comp_apply,
    ← TopPair.twistedHomologyCoefficientMap_comp_assoc,
    ← TopPair.twistedHomologyCoefficientMap_comp_assoc, hco, ConcreteCategory.comp_apply]

variable (F E R) in
/-- The fibre class over `x ∈ W` in `Hᵣ(E|_W, E₀|_W; π^*o(E))`: the image of the generator of the
fibre pair over `x`, read through the chosen trivialization at `x`, with coefficients trivialized by
the orientation that this trivialization reads as `ω`. Every linear trivialization at `x` reads it
the same way (`TauCeti.thomPairOverSignFiberClass_eq`). -/
def thomPairOverSignFiberClass {W : Set B} {x : B} (hxW : x ∈ W) :
    (thomPairOver F E W).twistedHomology (thomPairOverSignLocalSystem F E R hι W) (finrank ℝ F) :=
  thomPairOverSignFiberClassOf R hι ω (trivializationAt F E x)
    (FiberBundle.mem_baseSet_trivializationAt' x) hxW

/-- **Canonicity of the fibre class**: every linear trivialization `e` at `x` reads the fibre class
over `x` as the generator of the fibre pair, with the coefficients trivialized by the orientation
which `e` reads as `ω`. -/
theorem thomPairOverSignFiberClass_eq (e : Trivialization F (π F E)) [e.IsLinear ℝ] {x : B}
    (hx : x ∈ e.baseSet) {W : Set B} (hxW : x ∈ W) :
    thomPairOverSignFiberClass F E R hι ω hxW = thomPairOverSignFiberClassOf R hι ω e hx hxW :=
  thomPairOverSignFiberClassOf_eq hι ω _ e _ hx hxW

/-- Reading the fibre orientation through `-ω` instead of `ω` negates the fibre class read through
a linear trivialization. -/
@[simp]
theorem thomPairOverSignFiberClassOf_neg (e : Trivialization F (π F E)) [e.IsLinear ℝ] {x : B}
    (hx : x ∈ e.baseSet) {W : Set B} (hxW : x ∈ W) :
    thomPairOverSignFiberClassOf R hι (-ω) e hx hxW =
      -thomPairOverSignFiberClassOf R hι ω e hx hxW := by
  have h : (e.mapOrientation ι hx).symm (-ω) = -(e.mapOrientation ι hx).symm ω := by
    rw [Equiv.symm_apply_eq, Trivialization.mapOrientation_neg, Equiv.apply_symm_apply]
  rw [thomPairOverSignFiberClassOf, thomPairOverSignFiberClassOf, h, fiberSignIso_neg_inv,
    TopPair.twistedHomologyCoefficientMap_neg]
  simp only [ModuleCat.hom_neg, LinearMap.neg_apply, map_neg]

/-- Replacing the orientation `ω` of the model fibre by `-ω` negates the fibre classes. -/
@[simp]
theorem thomPairOverSignFiberClass_neg {W : Set B} {x : B} (hxW : x ∈ W) :
    thomPairOverSignFiberClass F E R hι (-ω) hxW = -thomPairOverSignFiberClass F E R hι ω hxW :=
  thomPairOverSignFiberClassOf_neg hι ω _ _ hxW

private theorem localIso_hom_thomPairOverSignFiberClass (e : Trivialization F (π F E))
    [MemTrivializationAtlas e] {W : Set B} (hW : W ⊆ e.baseSet) {x : B} (hxW : x ∈ W) :
    (localIso hι ω e hW).hom (thomPairOverSignFiberClass F E R hι ω hxW) =
      singularHomology₀Section (ModuleCat.of R R) (X := TopCat.of W) ⟨x, hxW⟩ 1 := by
  rw [thomPairOverSignFiberClass, thomPairOverSignFiberClassOf_eq hι ω _ e _ (hW hxW),
    localIso_hom_thomPairOverSignFiberClassOf]

private theorem thomPairOverTwistedHomologyMap_thomPairOverSignFiberClass {W W' : Set B}
    (h : W ⊆ W') {x : B} (hxW : x ∈ W) :
    thomPairOverTwistedHomologyMap (thomPairSignLocalSystem F E R hι) h (finrank ℝ F)
        (thomPairOverSignFiberClass F E R hι ω hxW) =
      thomPairOverSignFiberClass F E R hι ω (h hxW) :=
  thomPairOverTwistedHomologyMap_thomPairOverSignFiberClassOf hι ω _ _ h hxW

/-- **The fibre classes are constant along paths**: near each point `b` they are read through the
chosen trivialization at `b` as the classes of the points. -/
theorem thomPairOverSignFiberClass_eq_of_path {W : Set B} {x y : W} (γ : Path x y) :
    thomPairOverSignFiberClass F E R hι ω x.property =
      thomPairOverSignFiberClass F E R hι ω y.property :=
  eq_of_path_of_mono (fun h ↦ thomPairOverTwistedHomologyMap (thomPairSignLocalSystem F E R hι) h
      (finrank ℝ F))
    (fun _ x ↦ thomPairOverSignFiberClass F E R hι ω x.property)
    (fun h x ↦ thomPairOverTwistedHomologyMap_thomPairOverSignFiberClass hι ω h x.property)
    (fun b ↦ (trivializationAt F E b).baseSet)
    (fun b ↦ (trivializationAt F E b).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' b))
    (fun b _ ↦ ⟨(localIso hι ω (trivializationAt F E b) inter_subset_right).hom, 1,
      inferInstance, fun x ↦ by rw [localIso_hom_thomPairOverSignFiberClass, one_smul]⟩) γ

variable (F E R) in
/-- The map `H₀(W; R) ⟶ Hᵣ(E|_W, E₀|_W; π^*o(E))` sending the class of a point to the fibre class
over it (`TauCeti.thomPairOverSignFiberClass`). It is an isomorphism over every finite union of open
sets each inside the base set of a trivialization of the atlas
(`TauCeti.isIso_thomPairOverTwistedHomologyFinrankInv_biUnion`). -/
def thomPairOverTwistedHomologyFinrankInv (W : Set B) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} R) 0).obj (ModuleCat.of R R)).obj
        (TopCat.of W) ⟶
      (thomPairOver F E W).twistedHomology (thomPairOverSignLocalSystem F E R hι W) (finrank ℝ F) :=
  singularHomology₀Desc (ModuleCat.of R R) (X := TopCat.of W)
    (fun x ↦ ModuleCat.ofHom
      (LinearMap.toSpanSingleton R _ (thomPairOverSignFiberClass F E R hι ω x.property)))
    fun _ _ γ ↦ by rw [thomPairOverSignFiberClass_eq_of_path hι ω γ]

/-- The map `H₀(W; R) ⟶ Hᵣ(E|_W, E₀|_W; π^*o(E))` sends the class of a point to the fibre class
over it. -/
@[reassoc]
theorem singularHomology₀Section_thomPairOverTwistedHomologyFinrankInv {W : Set B} (x : W) :
    singularHomology₀Section (ModuleCat.of R R) (X := TopCat.of W) x ≫
        thomPairOverTwistedHomologyFinrankInv F E R hι ω W =
      ModuleCat.ofHom
        (LinearMap.toSpanSingleton R _ (thomPairOverSignFiberClass F E R hι ω x.property)) :=
  singularHomology₀Section_singularHomology₀Desc (X := TopCat.of W) _ _ _ x

/-- The maps over `W ⊆ W'` commute with the restrictions. -/
@[reassoc]
private theorem thomPairOverTwistedHomologyFinrankInv_naturality {W W' : Set B} (h : W ⊆ W') :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} R) 0).obj (ModuleCat.of R R)).map
        (TopCat.ofHom (ContinuousMap.inclusion h)) ≫
        thomPairOverTwistedHomologyFinrankInv F E R hι ω W' =
      thomPairOverTwistedHomologyFinrankInv F E R hι ω W ≫
        thomPairOverTwistedHomologyMap (thomPairSignLocalSystem F E R hι) h (finrank ℝ F) := by
  refine singularHomology₀_hom_ext _ fun x ↦ ?_
  rw [singularHomology₀Section_naturality_assoc,
    singularHomology₀Section_thomPairOverTwistedHomologyFinrankInv,
    singularHomology₀Section_thomPairOverTwistedHomologyFinrankInv_assoc,
    ModuleCat.ofHom_toSpanSingleton_comp, thomPairOverTwistedHomologyMap_thomPairOverSignFiberClass]
  simp only [TopCat.hom_ofHom, ContinuousMap.inclusion_apply_coe]

/-- Over a subset of the base set of a chosen trivialization, the map is an isomorphism, inverse to
`localIso`. -/
private theorem thomPairOverTwistedHomologyFinrankInv_comp_localIso_hom
    (e : Trivialization F (π F E)) [MemTrivializationAtlas e] {W : Set B} (hW : W ⊆ e.baseSet) :
    thomPairOverTwistedHomologyFinrankInv F E R hι ω W ≫ (localIso hι ω e hW).hom = 𝟙 _ := by
  refine singularHomology₀_hom_ext _ fun x ↦ ?_
  rw [singularHomology₀Section_thomPairOverTwistedHomologyFinrankInv_assoc,
    ModuleCat.ofHom_toSpanSingleton_comp,
    localIso_hom_thomPairOverSignFiberClass, Category.comp_id]
  ext
  simp

private theorem isIso_thomPairOverTwistedHomologyFinrankInv_of_subset (e : Trivialization F (π F E))
    [MemTrivializationAtlas e] {W : Set B} (hW : W ⊆ e.baseSet) :
    IsIso (thomPairOverTwistedHomologyFinrankInv F E R hι ω W) := by
  rw [(Iso.comp_hom_eq_id _).1 (thomPairOverTwistedHomologyFinrankInv_comp_localIso_hom hι ω e hW)]
  infer_instance

/-! ### Finite unions of trivializing open sets -/

/-- **The rank-degree homology over a finite union of trivializing open sets**: if `W` is the union
of finitely many open sets, each inside the base set of a trivialization of the atlas, then
`H₀(W; R) ⟶ Hᵣ(E|_W, E₀|_W; π^*o(E))`, sending the class of a point to the fibre class over it, is
an isomorphism. -/
theorem isIso_thomPairOverTwistedHomologyFinrankInv_biUnion {κ : Type*} (s : Finset κ)
    {W : κ → Set B} (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : MemTrivializationAtlas e),
      W i ⊆ e.baseSet) :
    IsIso (thomPairOverTwistedHomologyFinrankInv F E R hι ω (⋃ i ∈ s, W i)) :=
  -- The Mayer–Vietoris induction over finite unions of open sets in the base sets of
  -- trivializations of the atlas; the homology over `U ∩ V` vanishes in degree `r - 1` for such a
  -- `U`.
  isIso_biUnion_of_mayerVietoris
    (A := TopCat.subspaceDiagram (A := (id : Set B → Set B)) monotone_id ⋙
      (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} R) 0).obj (ModuleCat.of R R))
    (fun _ _ h ↦ thomPairOverTwistedHomologyMap (thomPairSignLocalSystem F E R hι) h (finrank ℝ F))
    (thomPairOverTwistedHomologyFinrankInv F E R hι ω)
    (fun _ _ h ↦ thomPairOverTwistedHomologyFinrankInv_naturality hι ω h)
    (fun U V _ _ ↦ epi_biprod_desc_singularHomologyMap_inclusion _ U V)
    (fun W ↦ ∃ (e : Trivialization F (π F E)) (_ : MemTrivializationAtlas e), W ⊆ e.baseSet)
    (fun _ _ h ⟨e, he, hW⟩ ↦ ⟨e, he, h.trans hW⟩)
    (fun _ ⟨e, _, hW⟩ ↦ isIso_thomPairOverTwistedHomologyFinrankInv_of_subset hι ω e hW)
    (isIso_of_source_target_iso_zero _
      (isZero_singularHomology_of_isEmpty _ (TopCat.of (∅ : Set B)) _).isoZero
      (isZero_thomPairOverTwistedHomology_empty (thomPairSignLocalSystem F E R hι) _).isoZero)
    (fun U V ↦ by
      rw [← thomPairOverTwistedMayerVietorisToBiprod_eq,
        ← thomPairOverTwistedMayerVietorisFromBiprod_eq]
      exact thomPairOverTwistedMayerVietorisToBiprod_fromBiprod
        (thomPairSignLocalSystem F E R hι) U V (finrank ℝ F))
    (fun U V hU hV ↦ by
      have hex := thomPairOverTwistedMayerVietoris_exact₂ (thomPairSignLocalSystem F E R hι) hU hV
        (finrank ℝ F)
      simpa only [thomPairOverTwistedMayerVietorisToBiprod_eq,
        thomPairOverTwistedMayerVietorisFromBiprod_eq] using hex)
    (fun U V hU hV ⟨e, _, hW⟩ ↦ by
      rw [← thomPairOverTwistedMayerVietorisFromBiprod_eq]
      exact epi_thomPairOverTwistedMayerVietorisFromBiprod_of_isZero
        (thomPairSignLocalSystem F E R hι) hU hV (n := finrank ℝ F) fun _ hm ↦
          e.isZero_thomPairOverTwistedHomology (thomPairSignLocalSystem F E R hι)
            (inter_subset_left.trans hW) (by omega))
    s hWo hWe

/-! ### The Thom pair over an arbitrary base -/

variable (F E R) in
/-- The fibre class over `b` in the homology of the Thom pair with coefficients in the pulled-back
orientation system: the image of the class of the fibre pair `(E_b, E_b ∖ {0})` which a linear
trivialization at `b` reads as the class of the point, with the coefficients `o(E)_b` trivialized
by the orientation of `E_b` which this trivialization reads as `ω`. Reversing both readings
together does not change it, so it does not depend on the trivialization. -/
def thomPairSignFiberClass (b : B) :
    (thomPair F E).twistedHomology (thomPairSignLocalSystem F E R hι) (finrank ℝ F) :=
  (overUnivIso hι (finrank ℝ F)).hom (thomPairOverSignFiberClass F E R hι ω (mem_univ b))

/-- Replacing the orientation `ω` of the model fibre by `-ω` negates the fibre classes. -/
@[simp]
theorem thomPairSignFiberClass_neg (b : B) :
    thomPairSignFiberClass F E R hι (-ω) b = -thomPairSignFiberClass F E R hι ω b := by
  rw [thomPairSignFiberClass, thomPairSignFiberClass, thomPairOverSignFiberClass_neg, map_neg]

/-- **The fibre class through the fibre inclusion.** For every orientation `o` of `E_b`, the fibre
class over `b` is the image of the generator of `Hᵣ(E_b, E_b ∖ {0}; R)` attached to `o`
(`TauCeti.orientedFiberGenerator`) under the inclusion of the fibre pair, with the coefficients over
the fibre trivialized by `o`. Replacing `o` by `-o` negates both the generator and the
trivialization. -/
theorem thomPairSignFiberClass_eq_thomPairSignFiberMap (b : B) (o : Orientation ℝ (E b) ι) :
    thomPairSignFiberClass F E R hι ω b =
      thomPairSignFiberMap F E R hι b o (finrank ℝ F) (orientedFiberGenerator R ω o) := by
  set e := trivializationAt F E b
  have hb : b ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' b
  set o₀ := (e.mapOrientation ι hb).symm ω
  have ho₀ : e.mapOrientation ι hb o₀ = ω := Equiv.apply_symm_apply _ ω
  -- For the orientation read as `ω` by the chosen trivialization, this is the definition of the
  -- fibre class, read in the Thom pair rather than in the pair over the whole base.
  have key : thomPairSignFiberClass F E R hι ω b =
      thomPairSignFiberMap F E R hι b o₀ (finrank ℝ F) (orientedFiberGenerator R ω o₀) := by
    rw [orientedFiberGenerator_of_mapOrientation_eq ω hι e hb ho₀, thomPairSignFiberClass,
      thomPairOverSignFiberClass, thomPairOverSignFiberClassOf, thomPairSignFiberMap,
      ModuleCat.comp_apply, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← twistedHomologyCoefficientMap_fiberSignIso_inv_comp_overUnivIso_hom]
  rcases (e.mapOrientation ι hb o).eq_or_eq_neg ω (Nat.card_eq_fintype_card.trans hι) with h | h
  · rwa [(e.mapOrientation ι hb).injective (h.trans ho₀.symm)]
  · have ho : o = -o₀ := by
      have h' : o₀ = -o := e.mapOrientation_symm_eq_neg_of_eq_neg hb h
      rw [h']
      exact (neg_neg o).symm
    rw [ho, thomPairSignFiberMap_neg, orientedFiberGenerator_neg ω hι]
    simpa only [ModuleCat.hom_neg, LinearMap.neg_apply, map_neg, neg_neg] using key

/-- The map `H₀(B; R) ⟶ Hᵣ(E, E₀; π^*o(E))` sending the class of a point to the fibre class over
it. -/
private def thomPairTwistedHomologyFinrankInv :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} R) 0).obj (ModuleCat.of R R)).obj
        (TopCat.of B) ⟶
      (thomPair F E).twistedHomology (thomPairSignLocalSystem F E R hι) (finrank ℝ F) :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} R) 0).obj (ModuleCat.of R R)).map
      (TopCat.isoOfHomeo (Homeomorph.Set.univ B).symm).hom ≫
    thomPairOverTwistedHomologyFinrankInv F E R hι ω univ ≫
    (overUnivIso hι (finrank ℝ F)).hom

private theorem singularHomology₀Section_thomPairTwistedHomologyFinrankInv (b : B) :
    singularHomology₀Section (ModuleCat.of R R) (X := TopCat.of B) b ≫
        thomPairTwistedHomologyFinrankInv hι ω =
      ModuleCat.ofHom (LinearMap.toSpanSingleton R _ (thomPairSignFiberClass F E R hι ω b)) := by
  rw [thomPairTwistedHomologyFinrankInv, singularHomology₀Section_naturality_assoc,
    singularHomology₀Section_thomPairOverTwistedHomologyFinrankInv_assoc,
    ModuleCat.ofHom_toSpanSingleton_comp, thomPairSignFiberClass]
  rfl

/-- On any subset `W` of the base, `thomPairTwistedHomologyFinrankInv` restricts to
`thomPairOverTwistedHomologyFinrankInv W` followed by the inclusion into `(E, E₀)`. -/
private theorem thomPairTwistedHomologyFinrankInv_restrict (W : Set B) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} R) 0).obj (ModuleCat.of R R)).map
        (TopCat.ofHom (ContinuousMap.subtypeVal W)) ≫
        thomPairTwistedHomologyFinrankInv hι ω =
      thomPairOverTwistedHomologyFinrankInv F E R hι ω W ≫
        (thomPairOver F E W).twistedHomologyCoefficientMap
          (eqToHom (thomPairOverSignLocalSystem_eq_pullback_restrictPreimagePairMap hι W))
          (finrank ℝ F) ≫
        TopPair.twistedHomologyMap (TopCat.restrictPreimagePairMap
          (X := TopCat.of (TotalSpace F E)) (π F E) (zeroSectionCompl F E) W)
          (thomPairSignLocalSystem F E R hι) (finrank ℝ F) := by
  rw [← thomPairOverTwistedHomologyMap_subset_univ_comp_overUnivIso_hom,
    ← thomPairOverTwistedHomologyFinrankInv_naturality_assoc (R := R) hι ω (subset_univ W)]
  refine singularHomology₀_hom_ext _ fun x ↦ ?_
  rw [singularHomology₀Section_naturality_assoc,
    singularHomology₀Section_thomPairTwistedHomologyFinrankInv,
    singularHomology₀Section_naturality_assoc,
    singularHomology₀Section_thomPairOverTwistedHomologyFinrankInv_assoc,
    ModuleCat.ofHom_toSpanSingleton_comp, thomPairSignFiberClass]
  rfl

/-- Over finite unions of the chosen trivializing open sets, `thomPairOverTwistedHomologyFinrankInv`
gives a natural isomorphism between the `H₀` diagram of the base and the twisted `Hᵣ` diagram of the
Thom pairs. -/
private def thomPairFiniteTrivializingUnionNatIso :
    subsetDiagram (X := TopCat.of B) (monotone_biUnion_baseSet_trivializationAt F E) ⋙
        (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} R) 0).obj (ModuleCat.of R R) ≅
      TopPair.restrictPreimagePairTwistedHomologyFunctor (X := TopCat.of (TotalSpace F E))
        (zeroSectionCompl F E) (thomPairSignLocalSystem F E R hι) (π F E)
        (monotone_biUnion_baseSet_trivializationAt F E) (finrank ℝ F) :=
  let U : Finset B → Set B := fun s ↦ ⋃ b ∈ s, (trivializationAt F E b).baseSet
  have hfin (s : Finset B) : IsIso (thomPairOverTwistedHomologyFinrankInv F E R hι ω (U s)) :=
    isIso_thomPairOverTwistedHomologyFinrankInv_biUnion hι ω s
      (fun b _ ↦ (trivializationAt F E b).open_baseSet) fun b _ ↦ ⟨_, inferInstance, subset_rfl⟩
  let app (s : Finset B) := @asIso _ _ _ _ (thomPairOverTwistedHomologyFinrankInv F E R hι ω (U s))
    (hfin s) ≪≫ (HomologicalComplex.homologyFunctor _ _ (finrank ℝ F)).mapIso
      ((thomPairOver F E (U s)).twistedChainComplexCoefficientIso
        (eqToIso (thomPairOverSignLocalSystem_eq_pullback_restrictPreimagePairMap hι (U s))))
  have happ (s : Finset B) : (app s).hom = thomPairOverTwistedHomologyFinrankInv F E R hι ω (U s) ≫
      (thomPairOver F E (U s)).twistedHomologyCoefficientMap
        (eqToHom (thomPairOverSignLocalSystem_eq_pullback_restrictPreimagePairMap hι (U s)))
        (finrank ℝ F) := by
    -- `erw`: unfold the composite of isomorphisms across `TopPair.twistedHomology`.
    erw [Iso.trans_hom, asIso_hom, Functor.mapIso_hom, HomologicalComplex.homologyFunctor_map,
      TopPair.twistedChainComplexCoefficientIso_hom]
    rfl
  NatIso.ofComponents app fun {s t} f ↦ by
    -- `erw`: unfold `subsetDiagram` and `restrictPreimagePairTwistedHomologyFunctor` on morphisms.
    erw [happ t, happ s, Category.assoc,
      thomPairOverTwistedHomologyFinrankInv_naturality_assoc (E := E) (R := R) hι ω
        (monotone_biUnion_baseSet_trivializationAt F E f.le)]
    exact congrArg (_ ≫ ·) (thomPairOverTwistedHomologyMap_comp_eqToHom (E := E) (R := R) hι
      (monotone_biUnion_baseSet_trivializationAt F E f.le) (finrank ℝ F))

private theorem thomPairFiniteTrivializingUnionNatIso_hom_app (s : Finset B) :
    (thomPairFiniteTrivializingUnionNatIso (F := F) (E := E) (R := R) hι ω).hom.app s =
      thomPairOverTwistedHomologyFinrankInv F E R hι ω
          (⋃ b ∈ s, (trivializationAt F E b).baseSet) ≫
        (thomPairOver F E (⋃ b ∈ s, (trivializationAt F E b).baseSet)).twistedHomologyCoefficientMap
          (eqToHom (thomPairOverSignLocalSystem_eq_pullback_restrictPreimagePairMap hι
            (⋃ b ∈ s, (trivializationAt F E b).baseSet))) (finrank ℝ F) := by
  unfold thomPairFiniteTrivializingUnionNatIso
  dsimp only [NatIso.ofComponents]
  -- `erw`: unfold the composite of isomorphisms across `TopPair.twistedHomology`.
  erw [Iso.trans_hom, asIso_hom, Functor.mapIso_hom, HomologicalComplex.homologyFunctor_map,
    TopPair.twistedChainComplexCoefficientIso_hom]
  rfl

/-- **The passage to the whole base**: both `H₀(B; R)` and `Hᵣ(E, E₀; π^*o(E))` are the filtered
colimits of the corresponding groups over finite unions of the chosen trivializing open sets, on
each of which `thomPairOverTwistedHomologyFinrankInv` is an isomorphism. -/
private theorem isIso_thomPairTwistedHomologyFinrankInv :
    IsIso (thomPairTwistedHomologyFinrankInv (F := F) (E := E) (R := R) hι ω) := by
  let c₁ := isColimitMapCoconeSingularHomologySubset (X := TopCat.of B) (ModuleCat.of R R) 0
    (monotone_biUnion_baseSet_trivializationAt F E) fun _ hL ↦
      hL.elim_finite_subcover _ (fun b ↦ (trivializationAt F E b).open_baseSet) fun b _ ↦
        mem_iUnion.2 ⟨b, FiberBundle.mem_baseSet_trivializationAt' b⟩
  let c₂ := isColimitThomPairFiniteTrivializingUnionTwistedHomologyCocone (F := F) (E := E)
    (thomPairSignLocalSystem F E R hι) (finrank ℝ F)
  let α := thomPairFiniteTrivializingUnionNatIso (F := F) (E := E) (R := R) hι ω
  have h : thomPairTwistedHomologyFinrankInv (F := F) (E := E) (R := R) hι ω =
      (c₁.coconePointsIsoOfNatIso c₂ α).hom := by
    refine c₁.hom_ext fun s ↦ ?_
    refine Eq.trans ?_ (c₁.comp_coconePointsIsoOfNatIso_hom c₂ α s).symm
    -- `erw`: unfold `c₁.ι` and `c₂.ι` across `(thomPair F E).fst = TopCat.of (TotalSpace F E)`.
    erw [Functor.mapCocone_ι_app, TopPair.restrictPreimagePairTwistedHomologyCocone_ι_app,
      thomPairFiniteTrivializingUnionNatIso_hom_app, Category.assoc]
    exact thomPairTwistedHomologyFinrankInv_restrict hι ω _
  exact h.symm ▸ inferInstanceAs (IsIso (c₁.coconePointsIsoOfNatIso c₂ α).hom)

variable (F E R) in
/-- **The homology of the Thom pair in the rank degree with coefficients in the pulled-back
orientation system.** For a real vector bundle `E → B` of rank `r` over an arbitrary base, with
Thom pair `(E, E₀)`, and a ring `R`, `Hᵣ(E, E₀; π^*o(E)) ≅ H₀(B; R)`, where `π^*o(E)` is the
orientation local system of `E` pulled back to the total space
(`TauCeti.thomPairSignLocalSystem`). No orientation of `E` is needed: the isomorphism is
normalized by an orientation `ω` of the model fibre, and sends the fibre class over `b`
(`TauCeti.thomPairSignFiberClass`) to the class of `b`
(`TauCeti.thomPairTwistedHomologyFinrankIso_hom_thomPairSignFiberClass`). -/
def thomPairTwistedHomologyFinrankIso :
    (thomPair F E).twistedHomology (thomPairSignLocalSystem F E R hι) (finrank ℝ F) ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} R) 0).obj
        (ModuleCat.of R R)).obj (TopCat.of B) :=
  have := isIso_thomPairTwistedHomologyFinrankInv (F := F) (E := E) (R := R) hι ω
  (asIso (thomPairTwistedHomologyFinrankInv (F := F) (E := E) (R := R) hι ω)).symm

/-- The isomorphism `Hᵣ(E, E₀; π^*o(E)) ≅ H₀(B; R)` sends the fibre class over `b` to the class of
the point `b`. -/
@[simp]
theorem thomPairTwistedHomologyFinrankIso_hom_thomPairSignFiberClass (b : B) :
    (thomPairTwistedHomologyFinrankIso F E R hι ω).hom (thomPairSignFiberClass F E R hι ω b) =
      singularHomology₀Section (ModuleCat.of R R) (X := TopCat.of B) b 1 := by
  have := isIso_thomPairTwistedHomologyFinrankInv (F := F) (E := E) (R := R) hι ω
  have hb := ConcreteCategory.congr_hom
    (singularHomology₀Section_thomPairTwistedHomologyFinrankInv (F := F) (E := E) (R := R) hι ω b)
    1
  simp only [ConcreteCategory.comp_apply, ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply,
    one_smul] at hb
  rw [thomPairTwistedHomologyFinrankIso, Iso.symm_hom, asIso_inv, ← hb, IsIso.hom_inv_id_apply]

/-- **Morphisms out of `Hᵣ(E, E₀; π^*o(E))` are determined by the fibre classes**: two morphisms to
a module `M` that agree on the fibre class over every point are equal. -/
theorem thomPairTwistedHomology_hom_ext {M : ModuleCat.{w} R}
    {f g : (thomPair F E).twistedHomology (thomPairSignLocalSystem F E R hι) (finrank ℝ F) ⟶ M}
    (h : ∀ b, f.hom (thomPairSignFiberClass F E R hι ω b) =
      g.hom (thomPairSignFiberClass F E R hι ω b)) :
    f = g := by
  rw [← Iso.hom_inv_id_assoc (thomPairTwistedHomologyFinrankIso F E R hι ω) f,
    ← Iso.hom_inv_id_assoc (thomPairTwistedHomologyFinrankIso F E R hι ω) g]
  congr 1
  refine singularHomology₀_hom_ext _ fun b ↦ ?_
  -- The class of `b` is the image of the fibre class over `b`.
  have hb : singularHomology₀Section (ModuleCat.of R R) (X := TopCat.of B) b =
      ModuleCat.ofHom (LinearMap.toSpanSingleton R _ ((thomPairTwistedHomologyFinrankIso F E R hι
        ω).hom (thomPairSignFiberClass F E R hι ω b))) := by
    rw [thomPairTwistedHomologyFinrankIso_hom_thomPairSignFiberClass]
    exact ModuleCat.hom_ext (LinearMap.ext_ring (by simp))
  rw [hb, ModuleCat.ofHom_toSpanSingleton_comp, ModuleCat.ofHom_toSpanSingleton_comp,
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, Iso.hom_inv_id_apply, h b]

end FiberClass

end TauCeti
