/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.Equivalence
public import TauCeti.AlgebraicTopology.Singular.Twisted.MayerVietoris.Pair
public import TauCeti.Topology.VectorBundle.MayerVietoris.Basic
public import TauCeti.Topology.VectorBundle.Orientation.LocalSystem
public import TauCeti.Topology.VectorBundle.Orientation.ThomClass
public import TauCeti.Topology.VectorBundle.Thom.RankDegreeHomology
import TauCeti.Algebra.Category.ModuleCat.SpanSingleton
import TauCeti.Topology.Category.TopCat.Limits.Basic
import TauCeti.AlgebraicTopology.Singular.MayerVietoris.FiniteUnion
import TauCeti.AlgebraicTopology.Singular.Twisted.Coefficients
import TauCeti.AlgebraicTopology.Singular.Twisted.ConstantNaturality
import TauCeti.Topology.VectorBundle.Thom.Class

/-!
# The Thom pair in the rank degree with coefficients in the orientation system

Let `E → B` be a real vector bundle of rank `r` with Thom pair `(E, E₀)`, `E₀` the complement of
the zero section, let `R` be a ring, and let `o(E)` be the orientation local system of `E`
(`TauCeti.VectorBundleOrientationCover.signLocalSystem`), whose fibre over `b` is a copy of `R`
with the two orientations of `E_b` as generators. Pull it back to the total space along the
projection `π`: `π^*o(E)` (`TauCeti.thomPairSignLocalSystem`). This file computes the first
homology group of the Thom pair with these coefficients that can be nonzero,

`Hᵣ(E, E₀; π^*o(E)) ≅ H₀(B; R)`,

for a compact base and without any orientation of `E`
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
Mayer–Vietoris sequence of pairs with local coefficients
(`TauCeti.LocalCoefficientSystem.pairTwistedMayerVietoris_exact₂`) ends in degree `r`, since the
twisted homology of the Thom pair vanishes below the rank, so the map is an isomorphism over a
finite union of trivializing open sets
(`TauCeti.isIso_thomPairOverTwistedHomologyFinrankInv_biUnion`), hence over a compact base.

## Main definitions and results

* `TauCeti.thomPairSignLocalSystem`: the orientation local system pulled back to the total space.
* `TauCeti.thomPairSignFiberClass`: the fibre class over a point; replacing `ω` by `-ω` negates it
  (`TauCeti.thomPairSignFiberClass_neg`).
* `TauCeti.thomPairOverSignFiberClass_eq`: every linear trivialization at `x` reads the fibre class
  over `x` as the generator of the fibre pair.
* `TauCeti.isIso_thomPairOverTwistedHomologyFinrankInv_biUnion`:
  `H₀(W; R) ≅ Hᵣ(E|_W, E₀|_W; π^*o(E))` for a finite union `W` of trivializing open sets.
* `TauCeti.thomPairTwistedHomologyFinrankIso`: `Hᵣ(E, E₀; π^*o(E)) ≅ H₀(B; R)` over a compact base.
* `TauCeti.thomPairTwistedHomologyFinrankIso_hom_thomPairSignFiberClass`: it sends the fibre class
  over `b` to the class of `b`.
* `TauCeti.thomPairTwistedHomology_hom_ext`: over a compact base, morphisms out of
  `Hᵣ(E, E₀; π^*o(E))` are determined by their values on the fibre classes.
* `TauCeti.fiberThomPairSignLocalSystemIso` and `TauCeti.thomPairSignFiberMap`: the trivialization
  of `π^*o(E)` over the fibre pair over `b` by an orientation `o` of `E_b`, and the map
  `Hₙ(E_b, E_b ∖ {0}; R) ⟶ Hₙ(E, E₀; π^*o(E))` it gives with the inclusion of the fibre pair;
  replacing `o` by `-o` negates it (`TauCeti.thomPairSignFiberMap_neg`).
* `TauCeti.thomPairSignFiberClass_eq_thomPairSignFiberMap`: for every orientation `o` of `E_b`, the
  fibre class over `b` is the image under this map of the generator of `Hᵣ(E_b, E_b ∖ {0}; R)`
  attached to `o` (`TauCeti.orientedFiberGenerator`). This reads the fibre class without a
  trivialization of `E`, as needed to compare it with fibre classes of other bundles.
* `TauCeti.fiberThomPairSignIso`: the trivialization of `π^*o(E)` on the fibre pair over `b` by an
  orientation of `E_b`. Its components evaluate at that orientation
  (`TauCeti.fiberThomPairSignIso_hom_app`), so it is the trivialization along the constant lift to
  the orientation cover (`TauCeti.fiberThomPairSignIso_hom`).
* `TauCeti.thomPairSignFiberClass_eq_twistedHomologyMap`: the fibre class over `b` is the image of
  the point class of the fibre pair under the fibre inclusion `(E_b, E_b ∖ {0}) ⟶ (E, E₀)`, with
  the coefficients trivialized by `TauCeti.fiberThomPairSignIso`. Through it the Kronecker pairing
  of a twisted class with a fibre class is computed from the restriction of the class to the
  fibre pair.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Lemma 10.3 and the proof of Theorem 10.4 (the induction over finite unions
  of trivializing open sets), and §12 (the orientation double cover and twisted coefficients).
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
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {E : B → Type w}
  [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E] {ι : Type} [Fintype ι]
  {R : Type w} [Ring R] (hι : Fintype.card ι = finrank ℝ F)

/-! ### The orientation system on the total space -/

variable (F E R) in
/-- The orientation local system `o(E)` of a real vector bundle, pulled back to its total space
along the projection: its fibre over a vector `v` is the fibre of `o(E)` over `π v`. -/
def thomPairSignLocalSystem : LocalCoefficientSystem R (TopCat.of (TotalSpace F E)) :=
  (LocalCoefficientSystem.pullback (X := TopCat.of (TotalSpace F E)) (Y := TopCat.of B)
    ⟨π F E, FiberBundle.continuous_proj F E⟩).obj
      (signLocalSystem F E R hι)

omit [FiniteDimensional ℝ F] in
theorem thomPairSignLocalSystem_def :
    thomPairSignLocalSystem F E R hι =
      (LocalCoefficientSystem.pullback (X := TopCat.of (TotalSpace F E)) (Y := TopCat.of B)
        ⟨π F E, FiberBundle.continuous_proj F E⟩).obj (signLocalSystem F E R hι) :=
  (rfl)

/-- The fibres of the pulled-back orientation system are fibres of `o(E)`, so they are projective.
-/
instance projective_thomPairSignLocalSystem_obj (v : FundamentalGroupoid (thomPair F E).fst) :
    Projective ((thomPairSignLocalSystem F E R hι).obj v) :=
  LocalCoefficientSystem.projective_pullback_obj_obj (X := TopCat.of (TotalSpace F E)) _ _ v

variable (F E R) in
/-- The pulled-back orientation system `π^*o(E)` restricted to the part `E|_W` of the total space
over `W`. -/
def thomPairOverSignLocalSystem (W : Set B) :
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

omit [NormedSpace ℝ F] [FiniteDimensional ℝ F] [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E] in
/-- A vector over a subset of the base set of a trivialization lies over its base set. -/
private theorem proj_mem_baseSet {e : Trivialization F (π F E)} {W : Set B} (hW : W ⊆ e.baseSet)
    (v : π F E ⁻¹' W) : v.val.proj ∈ e.baseSet :=
  hW v.property

/-- Over a subset `W` of the base set of a trivialization `e` of the atlas, the pulled-back
orientation system is trivialized by evaluating at the orientation read as `ω` by it. -/
private def baseSetSignIso (e : Trivialization F (π F E)) [MemTrivializationAtlas e] {W : Set B}
    (hW : W ⊆ e.baseSet)
    (ω : Orientation ℝ F ι) :
    thomPairOverSignLocalSystem F E R hι W ≅
      (constantFunctor _).obj (ModuleCat.of R R) :=
  NatIso.ofComponents (fun v ↦ (signLocalSystemFiberEquiv hι
      ((e.mapOrientation ι (proj_mem_baseSet hW v.as)).symm ω)).toModuleIso)
    fun {v v'} q ↦ ModuleCat.hom_ext <| LinearMap.ext fun f ↦ by
      -- The section of the orientation cover read as `ω` lifts the projection of the path.
      have h := (VectorBundleOrientationCover.isCoveringMap_proj (F := F) (E := E)
        hι).monodromy_map_of_lift
        (g := (⟨π F E, FiberBundle.continuous_proj F E⟩ : C(TotalSpace F E, B)).comp
          (ContinuousMap.subtypeVal (π F E ⁻¹' W)))
        (s := fun v : π F E ⁻¹' W ↦ (⟨v.val.proj, (e.mapOrientation ι
          (proj_mem_baseSet hW v)).symm ω⟩ : VectorBundleOrientationCover F E ι))
        ((VectorBundleOrientationCover.continuous_mk_mapOrientation_symm hι _ ω).comp
          (((FiberBundle.continuous_proj F E).comp continuous_subtypeVal).subtype_mk
            (proj_mem_baseSet hW))) (fun _ ↦ rfl) q
      -- `erw`: the path class lives in the fundamental groupoid of `(thomPairOver F E W).fst`,
      -- which is the subspace `π⁻¹ W` only after unfolding the pair.
      erw [Path.Homotopic.Quotient.map_comp, ← FundamentalGroupoid.map_map,
        ← FundamentalGroupoid.map_map] at h
      -- The closing `rfl` unfolds `pullback`: the transport of the pulled-back system along `q` is
      -- the transport of `o(E)` along the projection of `q`, and the constant system transports by
      -- the identity.
      exact (VectorBundleOrientationCover.signLocalSystemFiberEquiv_map hι _ h f).trans rfl

omit [FiniteDimensional ℝ F] in
/-- The components of `fiberSignIso` are evaluation at the orientation. -/
private theorem fiberSignIso_hom_app {W : Set B} {x : B} (hx : x ∈ W) (o : Orientation ℝ (E x) ι)
    (v : FundamentalGroupoid (TopPair.ofSubset (X := TopCat.of (E x)) ({0}ᶜ : Set (E x))).fst) :
    (fiberSignIso (R := R) hι hx o).hom.app v = (signLocalSystemFiberEquiv hι o).toModuleIso.hom :=
  (rfl)

omit [FiniteDimensional ℝ F] in
/-- The trivialization of a fibre by the opposite orientation is the negative of the one by `o`. -/
private theorem fiberSignIso_neg_inv {W : Set B} {x : B} (hx : x ∈ W) (o : Orientation ℝ (E x) ι) :
    (fiberSignIso (R := R) hι hx (-o)).inv = -(fiberSignIso hι hx o).inv := by
  ext v : 2
  exact congrArg ModuleCat.ofHom
    (VectorBundleOrientationCover.signLocalSystemFiberEquiv_neg_symm hι o)

section FiberClass

variable (ω : Orientation ℝ F ι)

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

omit [FiniteDimensional ℝ F] in
/-- The trivialization over the base set, restricted to a fibre, is the trivialization of the
fibre by the orientation it reads as `ω`. -/
private theorem pullback_map_baseSetSignIso_hom (e : Trivialization F (π F E))
    [MemTrivializationAtlas e] {W : Set B}
    (hW : W ⊆ e.baseSet) {x : B} (hxW : x ∈ W) :
    (LocalCoefficientSystem.pullback (TopPair.Hom.fst (fiberThomPairOverMap F E hxW)).hom).map
        (baseSetSignIso (R := R) hι e hW ω).hom ≫
      (LocalCoefficientSystem.pullbackConstantIso _ (ModuleCat.of R R)).hom =
    (fiberSignIso hι hxW ((e.mapOrientation ι (hW hxW)).symm ω)).hom := by
  ext v : 2
  rw [NatTrans.comp_app, LocalCoefficientSystem.pullbackConstantIso_hom_app]
  -- After the unit law, both components are evaluation at the orientation of `E_x` read as `ω`:
  -- the closing `rfl` unfolds `fiberThomPairOverMap`, by which the point of `E|_W` under `v` lies
  -- over `x`.
  exact (Category.comp_id _).trans rfl

omit [FiniteDimensional ℝ F] in
/-- Over a subset of the base set of a trivialization `e` of the atlas, the fibre inclusion over
`x`, read through the trivializations of the coefficient systems by the orientation that this
trivialization reads as `ω`, is the fibre inclusion in ordinary homology. -/
@[reassoc]
private theorem fiberSign_comp_twistedHomologyMap_comp_baseSetSign (e : Trivialization F (π F E))
    [MemTrivializationAtlas e] {W : Set B}
    (hW : W ⊆ e.baseSet) {x : B} (hxW : x ∈ W) :
    ((TopPair.ofSubset (X := TopCat.of (E x)) ({0}ᶜ : Set (E x))).twistedHomologyConstantIso
        (ModuleCat.of R R) (finrank ℝ F)).inv ≫
      (TopPair.ofSubset (X := TopCat.of (E x)) ({0}ᶜ : Set (E x))).twistedHomologyCoefficientMap
        (fiberSignIso hι hxW ((e.mapOrientation ι (hW hxW)).symm ω)).inv
        (finrank ℝ F) ≫
      TopPair.twistedHomologyMap (fiberThomPairOverMap F E hxW)
        (thomPairOverSignLocalSystem F E R hι W)
        (finrank ℝ F) ≫
      (thomPairOver F E W).twistedHomologyCoefficientMap (baseSetSignIso hι e hW ω).hom
        (finrank ℝ F) ≫
      ((thomPairOver F E W).twistedHomologyConstantIso (ModuleCat.of R R) (finrank ℝ F)).hom =
    TopPair.singularHomologyMap (fiberThomPairOverMap F E hxW) (ModuleCat.of R R)
      (finrank ℝ F) := by
  -- Move the change of coefficients over `W` past the fibre inclusion, then compare the two
  -- trivializations of the coefficients on the fibre.
  rw [TopPair.twistedHomologyMap_naturality_assoc,
    TopPair.twistedHomologyConstantIso_hom_pair_naturality,
    ← TopPair.twistedHomologyCoefficientMap_comp_assoc,
    ← TopPair.twistedHomologyCoefficientMap_comp_assoc, Category.assoc,
    pullback_map_baseSetSignIso_hom, Iso.inv_hom_id, TopPair.twistedHomologyCoefficientMap_id,
    Category.id_comp, Iso.inv_hom_id_assoc]

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
    [MemTrivializationAtlas e] {W : Set B}
    (hW : W ⊆ e.baseSet) {x : B} (hxW : x ∈ W) :
    (localIso hι ω e hW).hom (thomPairOverSignFiberClassOf R hι ω e (hW hxW) hxW) =
      singularHomology₀Section (ModuleCat.of R R) (X := TopCat.of W) ⟨x, hxW⟩ 1 := by
  have h := ConcreteCategory.congr_hom
    (fiberSign_comp_twistedHomologyMap_comp_baseSetSign_assoc (R := R) hι ω e hW hxW
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
    [e'.IsLinear ℝ]
    {x : B} (hx : x ∈ e.baseSet) (hx' : x ∈ e'.baseSet) {W : Set B} (hxW : x ∈ W) :
    thomPairOverSignFiberClassOf R hι ω e hx hxW =
      thomPairOverSignFiberClassOf R hι ω e' hx' hxW := by
  set o := (e.mapOrientation ι hx).symm ω
  have ho : e.mapOrientation ι hx o = ω := Equiv.apply_symm_apply _ ω
  rcases Orientation.eq_or_eq_neg (e'.mapOrientation ι hx' o) ω
    (Nat.card_eq_fintype_card.trans hι) with h | h
  · have h' : (e'.mapOrientation ι hx').symm ω = o := (Equiv.symm_apply_eq _).2 h.symm
    have hinv := congrArg (fun I ↦ I.inv) (Iso.ext
      (α := TopPair.singularHomologyMapIso (ModuleCat.of R R)
      (e.continuousLinearEquivAt ℝ x hx).complZeroPairIso (finrank ℝ F))
      (β := TopPair.singularHomologyMapIso (ModuleCat.of R R)
      (e'.continuousLinearEquivAt ℝ x hx').complZeroPairIso (finrank ℝ F))
      (Trivialization.singularHomologyMap_complZeroPairIso_hom_eq_of_mapOrientation_eq e e' hx hx'
        hι (ModuleCat.of R R) (h.trans ho.symm) (finrank ℝ F)).symm)
    simp only [TopPair.singularHomologyMapIso_inv] at hinv
    rw [thomPairOverSignFiberClassOf, thomPairOverSignFiberClassOf, h', hinv]
  · have h' : (e'.mapOrientation ι hx').symm ω = -o := e'.mapOrientation_symm_eq_neg_of_eq_neg hx' h
    have hinv : TopPair.singularHomologyMap
        (e'.continuousLinearEquivAt ℝ x hx').complZeroPairIso.inv
        (ModuleCat.of R R) (finrank ℝ F) =
        -TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ x hx).complZeroPairIso.inv
          (ModuleCat.of R R) (finrank ℝ F) :=
      Iso.inv_ext (f := TopPair.singularHomologyMapIso (ModuleCat.of R R)
        (e'.continuousLinearEquivAt ℝ x hx').complZeroPairIso (finrank ℝ F)) (by
        rw [TopPair.singularHomologyMapIso_hom,
          Trivialization.singularHomologyMap_complZeroPairIso_hom_eq_neg_of_mapOrientation_eq_neg e
            e' hx hx' hι (ModuleCat.of R R) (h.trans (congrArg Neg.neg ho.symm)) (finrank ℝ F),
          Preadditive.neg_comp_neg, ← TopPair.singularHomologyMapIso_hom,
          ← TopPair.singularHomologyMapIso_inv, Iso.hom_inv_id])
    rw [thomPairOverSignFiberClassOf, thomPairOverSignFiberClassOf, h', hinv, fiberSignIso_neg_inv,
      TopPair.twistedHomologyCoefficientMap_neg]
    simp only [ModuleCat.hom_neg, LinearMap.neg_apply, map_neg, neg_neg, o]

variable (F E R) in
/-- The restriction `Hₙ(E|_W, E₀|_W; π^*o(E)) ⟶ Hₙ(E|_{W'}, E₀|_{W'}; π^*o(E))` for `W ⊆ W'`, the
map of the Mayer–Vietoris sequence of pairs of subsets of the total space. -/
private abbrev restr {W W' : Set B} (h : W ⊆ W') (n : ℕ) :
    (thomPairOver F E W).twistedHomology (thomPairOverSignLocalSystem F E R hι W) n ⟶
      (thomPairOver F E W').twistedHomology (thomPairOverSignLocalSystem F E R hι W') n :=
  (thomPairSignLocalSystem F E R hι).subsetPairTwistedHomologyMap
    inter_subset_left inter_subset_left (preimage_mono h)
    (inter_subset_inter_left _ (preimage_mono h)) n

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

omit [FiniteDimensional ℝ F] in
private theorem overRestrIso_app {W W' : Set B} (h : W ⊆ W') (y : FundamentalGroupoid _) :
    (overRestrIso R hι h (F := F) (E := E)).app y = 𝟙 _ :=
  LocalCoefficientSystem.pullbackCompIso_hom_app_app _ _ _ y

omit [FiniteDimensional ℝ F] in
private theorem restr_eq {W W' : Set B} (h : W ⊆ W') (n : ℕ) :
    restr F E R hι h n =
      (thomPairOver F E W).twistedHomologyCoefficientMap (overRestrIso R hι h) n ≫
      TopPair.twistedHomologyMap (overInclusion h) (thomPairOverSignLocalSystem F E R hι W') n :=
  (congrArg (HomologicalComplex.homologyMap · n)
    (LocalCoefficientSystem.subsetPairTwistedChainComplexMap_def (thomPairSignLocalSystem F E R hι)
      inter_subset_left inter_subset_left (preimage_mono h)
      (inter_subset_inter_left _ (preimage_mono h)))).trans
    (HomologicalComplex.homologyMap_comp _ _ _)

/-- Restriction carries fibre classes to fibre classes. -/
private theorem restr_thomPairOverSignFiberClassOf (e : Trivialization F (π F E)) [e.IsLinear ℝ]
    {x : B}
    (hx : x ∈ e.baseSet) {W W' : Set B} (h : W ⊆ W') (hxW : x ∈ W) :
    restr F E R hι h (finrank ℝ F) (thomPairOverSignFiberClassOf R hι ω e hx hxW) =
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
  rw [restr_eq, thomPairOverSignFiberClassOf, thomPairOverSignFiberClassOf,
    ← ConcreteCategory.comp_apply,
    TopPair.twistedHomologyMap_naturality_assoc,
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
    [MemTrivializationAtlas e] {W : Set B}
    (hW : W ⊆ e.baseSet) {x : B} (hxW : x ∈ W) :
    (localIso hι ω e hW).hom (thomPairOverSignFiberClass F E R hι ω hxW) =
      singularHomology₀Section (ModuleCat.of R R) (X := TopCat.of W) ⟨x, hxW⟩ 1 := by
  rw [thomPairOverSignFiberClass, thomPairOverSignFiberClassOf_eq hι ω _ e _ (hW hxW),
    localIso_hom_thomPairOverSignFiberClassOf]

private theorem restr_thomPairOverSignFiberClass {W W' : Set B} (h : W ⊆ W') {x : B} (hxW : x ∈ W) :
    restr F E R hι h (finrank ℝ F) (thomPairOverSignFiberClass F E R hι ω hxW) =
      thomPairOverSignFiberClass F E R hι ω (h hxW) :=
  restr_thomPairOverSignFiberClassOf hι ω _ _ h hxW

/-- **The fibre classes are constant along paths**: near each point `b` they are read through the
chosen trivialization at `b` as the classes of the points. -/
theorem thomPairOverSignFiberClass_eq_of_path {W : Set B} {x y : W} (γ : Path x y) :
    thomPairOverSignFiberClass F E R hι ω x.property =
      thomPairOverSignFiberClass F E R hι ω y.property :=
  eq_of_path_of_mono (fun h ↦ restr F E R hι h (finrank ℝ F))
    (fun _ x ↦ thomPairOverSignFiberClass F E R hι ω x.property)
    (fun h x ↦ restr_thomPairOverSignFiberClass hι ω h x.property)
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
private theorem thomPairOverTwistedHomologyFinrankInv_naturality {W W' : Set B} (h : W ⊆ W') :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} R) 0).obj (ModuleCat.of R R)).map
        (TopCat.ofHom (ContinuousMap.inclusion h)) ≫
        thomPairOverTwistedHomologyFinrankInv F E R hι ω W' =
      thomPairOverTwistedHomologyFinrankInv F E R hι ω W ≫ restr F E R hι h (finrank ℝ F) := by
  refine singularHomology₀_hom_ext _ fun x ↦ ?_
  rw [singularHomology₀Section_naturality_assoc,
    singularHomology₀Section_thomPairOverTwistedHomologyFinrankInv,
    singularHomology₀Section_thomPairOverTwistedHomologyFinrankInv_assoc,
    ModuleCat.ofHom_toSpanSingleton_comp, restr_thomPairOverSignFiberClass]
  simp only [TopCat.hom_ofHom, ContinuousMap.inclusion_apply_coe]

/-- Over a subset of the base set of a chosen trivialization, the map is an isomorphism, inverse to
`localIso`. -/
private theorem thomPairOverTwistedHomologyFinrankInv_comp_localIso_hom
    (e : Trivialization F (π F E))
    [MemTrivializationAtlas e] {W : Set B}
    (hW : W ⊆ e.baseSet) :
    thomPairOverTwistedHomologyFinrankInv F E R hι ω W ≫ (localIso hι ω e hW).hom = 𝟙 _ := by
  refine singularHomology₀_hom_ext _ fun x ↦ ?_
  rw [singularHomology₀Section_thomPairOverTwistedHomologyFinrankInv_assoc,
    ModuleCat.ofHom_toSpanSingleton_comp,
    localIso_hom_thomPairOverSignFiberClass, Category.comp_id]
  ext
  simp

private theorem isIso_thomPairOverTwistedHomologyFinrankInv_of_subset (e : Trivialization F (π F E))
    [MemTrivializationAtlas e] {W : Set B}
    (hW : W ⊆ e.baseSet) : IsIso (thomPairOverTwistedHomologyFinrankInv F E R hι ω W) := by
  rw [(Iso.comp_hom_eq_id _).1 (thomPairOverTwistedHomologyFinrankInv_comp_localIso_hom hι ω e hW)]
  infer_instance

/-! ### The Mayer–Vietoris step -/

omit [FiniteDimensional ℝ F] in
/-- Restrictions compose. -/
private theorem restr_comp_restr {W W' W'' : Set B} (h : W ⊆ W') (h' : W' ⊆ W'') (n : ℕ) :
    restr F E R hι h n ≫ restr F E R hι h' n = restr F E R hι (h.trans h') n :=
  LocalCoefficientSystem.subsetPairTwistedHomologyMap_comp _ _ _ _ _ _ _ _ n

variable (F E R) in
/-- The Mayer–Vietoris sequence of the Thom pairs over `U ∩ V`, `U`, `V` and `U ∪ V` with
coefficients in the pulled-back orientation system, around the middle term. -/
private abbrev mvShortComplex (U V : Set B) (n : ℕ) : ShortComplex (ModuleCat.{w} R) :=
  ShortComplex.mk (biprod.lift (restr F E R hι (inter_subset_left : U ∩ V ⊆ U) n)
      (-restr F E R hι (inter_subset_right : U ∩ V ⊆ V) n))
    (biprod.desc (restr F E R hι (subset_union_left : U ⊆ U ∪ V) n)
      (restr F E R hι (subset_union_right : V ⊆ U ∪ V) n)) (by
    rw [biprod.lift_desc, Preadditive.neg_comp, restr_comp_restr, restr_comp_restr, add_neg_cancel])

/-- The Mayer–Vietoris sequence of the Thom pairs, read on the pairs `(E|_W, E₀|_W)`, is the
Mayer–Vietoris sequence of the pairs `(π⁻¹ U, π⁻¹ U ∩ E₀)` and `(π⁻¹ V, π⁻¹ V ∩ E₀)` of subsets of
the total space. -/
private def mvShortComplexIso (U V : Set B) (n : ℕ) :
    mvShortComplex F E R hι U V n ≅ ShortComplex.mk _ _
      ((thomPairSignLocalSystem F E R hι).pairTwistedMayerVietorisToBiprod_fromBiprod
        (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
        (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V) n) := by
  refine ShortComplex.isoMk
    ((thomPairSignLocalSystem F E R hι).subsetPairTwistedHomologyIsoOfEq inter_subset_left _
      (preimage_inter) (by ext; simp; tauto) n)
    (Iso.refl _)
    ((thomPairSignLocalSystem F E R hι).subsetPairTwistedHomologyIsoOfEq inter_subset_left _
      (preimage_union) (by ext; simp; tauto) n) ?_ ?_
  -- The objects `(thomPairOver F E W).twistedHomology (thomPairOverSignLocalSystem F E R hι W) n`
  -- and the homology of the pair of subsets `(π⁻¹ W, π⁻¹ W ∩ E₀)` agree only after unfolding
  -- `thomPairOver`, so `simp` and `rw` meet compositions that are not type correct at reducible
  -- transparency and make no progress; the two squares are assembled with `Eq.trans` instead.
  · apply biprod.hom_ext
    · exact (congrArg (· ≫ _)
        (LocalCoefficientSystem.subsetPairTwistedHomologyIsoOfEq_hom _ _ _ _ _ n)).trans <|
        (congrArg (_ ≫ ·)
          (LocalCoefficientSystem.pairTwistedMayerVietorisToBiprod_fst _ _ _ n)).trans
        ((LocalCoefficientSystem.subsetPairTwistedHomologyMap_comp _ _ _ _ _ _ _ _ n).trans
          ((biprod.lift_fst _ _).symm.trans (congrArg (· ≫ biprod.fst) (Category.comp_id _).symm)))
    · exact (congrArg (· ≫ _)
        (LocalCoefficientSystem.subsetPairTwistedHomologyIsoOfEq_hom _ _ _ _ _ n)).trans <|
        (congrArg (_ ≫ ·)
          (LocalCoefficientSystem.pairTwistedMayerVietorisToBiprod_snd _ _ _ n)).trans
        (((Preadditive.comp_neg _ _).trans
          (congrArg Neg.neg (LocalCoefficientSystem.subsetPairTwistedHomologyMap_comp
            _ _ _ _ _ _ _ _ n))).trans
          ((biprod.lift_snd _ _).symm.trans (congrArg (· ≫ biprod.snd) (Category.comp_id _).symm)))
  · apply biprod.hom_ext'
    · exact ((congrArg (biprod.inl ≫ ·) (Category.id_comp _)).trans
        (LocalCoefficientSystem.inl_pairTwistedMayerVietorisFromBiprod _ _ _ n)).trans
          ((biprod.inl_desc_assoc _ _ _).trans <|
            (congrArg (_ ≫ ·)
              (LocalCoefficientSystem.subsetPairTwistedHomologyIsoOfEq_hom _ _ _ _ _ n)).trans
            (LocalCoefficientSystem.subsetPairTwistedHomologyMap_comp _ _ _ _ _ _ _ _ n)).symm
    · exact ((congrArg (biprod.inr ≫ ·) (Category.id_comp _)).trans
        (LocalCoefficientSystem.inr_pairTwistedMayerVietorisFromBiprod _ _ _ n)).trans
          ((biprod.inr_desc_assoc _ _ _).trans <|
            (congrArg (_ ≫ ·)
              (LocalCoefficientSystem.subsetPairTwistedHomologyIsoOfEq_hom _ _ _ _ _ n)).trans
            (LocalCoefficientSystem.subsetPairTwistedHomologyMap_comp _ _ _ _ _ _ _ _ n)).symm

omit [FiniteDimensional ℝ F] in
private theorem mvShortComplex_exact {U V : Set B} (hU : IsOpen U) (hV : IsOpen V) (n : ℕ) :
    (mvShortComplex F E R hι U V n).Exact := by
  obtain ⟨hA, hB, hC, hD⟩ := isOpen_thomPairOver_mayerVietoris (F := F) (E := E) hU hV
  exact (ShortComplex.exact_iff_of_iso (mvShortComplexIso hι U V n)).2
    ((thomPairSignLocalSystem F E R hι).pairTwistedMayerVietoris_exact₂ _ _ hA hB hC hD n)

include ω in
/-- Over a subset of the base set of a chosen trivialization, the homology of the Thom pair with
coefficients in the pulled-back orientation system vanishes below the rank. -/
private theorem isZero_twistedHomology_thomPairOver (e : Trivialization F (π F E))
    [MemTrivializationAtlas e] {W : Set B}
    (hW : W ⊆ e.baseSet) {m : ℕ} (hm : m < finrank ℝ F) :
    IsZero ((thomPairOver F E W).twistedHomology (thomPairOverSignLocalSystem F E R hι W) m) :=
  (e.isZero_singularHomology_thomPairOver hW (ModuleCat.of R R) hm).of_iso
    ((HomologicalComplex.homologyFunctor _ _ m).mapIso
      ((thomPairOver F E W).twistedChainComplexCoefficientIso (baseSetSignIso hι e hW ω)) ≪≫
      (thomPairOver F E W).twistedHomologyConstantIso (ModuleCat.of R R) m)

omit [FiniteDimensional ℝ F] in
private theorem epi_mvShortComplex_g {U V : Set B} (hU : IsOpen U) (hV : IsOpen V) (n : ℕ)
    (hUV : ∀ m, m + 1 = n →
      IsZero ((thomPairOver F E (U ∩ V)).twistedHomology
        (thomPairOverSignLocalSystem F E R hι (U ∩ V)) m)) :
    Epi (mvShortComplex F E R hι U V n).g := by
  obtain ⟨hA, hB, hC, hD⟩ := isOpen_thomPairOver_mayerVietoris (F := F) (E := E) hU hV
  set e := mvShortComplexIso (F := F) (E := E) (R := R) hι U V n
  have : Epi e.hom.τ₂ := inferInstance
  have hepi : Epi ((thomPairSignLocalSystem F E R hι).pairTwistedMayerVietorisFromBiprod
      (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
      (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V) n) := by
    rcases n with _ | m
    · exact (thomPairSignLocalSystem F E R hι).epi_pairTwistedMayerVietorisFromBiprod_zero _ _ hA
        hB hC hD
    · exact ((thomPairSignLocalSystem F E R hι).pairTwistedMayerVietoris_exact₃ _ _ hA hB hC hD
        (m + 1) m).epi_f (((hUV m rfl).of_iso
          ((thomPairSignLocalSystem F E R hι).subsetPairTwistedHomologyIsoOfEq _ _ (preimage_inter)
            (by ext; simp; tauto) m).symm).eq_of_tgt _ _)
  have hg : (mvShortComplex F E R hι U V n).g = e.hom.τ₂ ≫
      ((thomPairSignLocalSystem F E R hι).pairTwistedMayerVietorisFromBiprod
        (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
        (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V) n) ≫ e.inv.τ₃ := by
    rw [← Category.assoc, e.hom.comm₂₃, Category.assoc, ← ShortComplex.comp_τ₃, e.hom_inv_id,
      ShortComplex.id_τ₃, Category.comp_id]
  rw [hg]
  infer_instance

omit [FiniteDimensional ℝ F] in
/-- Over the empty set, the homology of the Thom pair vanishes. -/
private theorem isZero_twistedHomology_thomPairOver_empty :
    IsZero ((thomPairOver F E ∅).twistedHomology (thomPairOverSignLocalSystem F E R hι ∅)
      (finrank ℝ F)) :=
  have : IsEmpty (thomPairOver F E (∅ : Set B)).fst := ⟨fun v ↦ v.property⟩
  have : IsEmpty (thomPairOver F E (∅ : Set B)).snd := ⟨fun v ↦ v.property.1⟩
  (LocalCoefficientSystem.isZero_twistedHomology_of_isEmpty _ _).of_iso
    (asIso ((thomPairOver F E ∅).twistedHomologyπ _ _)).symm

/-! ### The Thom pair over a compact base -/

/-- The twisted homology of the Thom pair over the whole base, as a pair of subsets of the total
space, is that of the Thom pair `(E, E₀)`. -/
private def overUnivIso (n : ℕ) :
    (thomPairOver F E univ).twistedHomology (thomPairOverSignLocalSystem F E R hι univ) n ≅
      (thomPair F E).twistedHomology (thomPairSignLocalSystem F E R hι) n :=
  have hiso : IsIso (TopPair.twistedHomologyMap (thomPairOverUnivIso F E).hom
      (thomPairSignLocalSystem F E R hι) n) :=
    (thomPairSignLocalSystem F E R hι).isIso_relativeTwistedHomologyMap_of_homotopyInverse
      (thomPairOverUnivIso F E).hom (thomPairOverUnivIso F E).inv
      (by rw [Iso.hom_inv_id]; exact ⟨TopPair.Homotopy.refl _⟩)
      (by rw [Iso.inv_hom_id]; exact ⟨TopPair.Homotopy.refl _⟩) n
  (HomologicalComplex.homologyFunctor _ _ n).mapIso
      ((thomPairOver F E univ).twistedChainComplexCoefficientIso
        (eqToIso (congrArg (fun g ↦ (LocalCoefficientSystem.pullback g).obj
          (thomPairSignLocalSystem F E R hι)) (thomPairOverUnivIso_hom_fst_eq F E).symm))) ≪≫
    @asIso _ _ _ _ (TopPair.twistedHomologyMap (thomPairOverUnivIso F E).hom
      (thomPairSignLocalSystem F E R hι) n) hiso

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
    (fun _ _ h ↦ restr F E R hι h (finrank ℝ F)) (thomPairOverTwistedHomologyFinrankInv F E R hι ω)
    (fun _ _ h ↦ thomPairOverTwistedHomologyFinrankInv_naturality hι ω h)
    (fun U V _ _ ↦ epi_biprod_desc_singularHomologyMap_inclusion _ U V)
    (fun W ↦ ∃ (e : Trivialization F (π F E)) (_ : MemTrivializationAtlas e), W ⊆ e.baseSet)
    (fun _ _ h ⟨e, he, hW⟩ ↦ ⟨e, he, h.trans hW⟩)
    (fun _ ⟨e, _, hW⟩ ↦ isIso_thomPairOverTwistedHomologyFinrankInv_of_subset hι ω e hW)
    (isIso_of_source_target_iso_zero _
      (isZero_singularHomology_of_isEmpty _ (TopCat.of (∅ : Set B)) _).isoZero
      (isZero_twistedHomology_thomPairOver_empty hι).isoZero)
    (fun U V ↦ (mvShortComplex F E R hι U V (finrank ℝ F)).zero)
    (fun _ _ hU hV ↦ mvShortComplex_exact hι hU hV _)
    (fun _ _ hU hV ⟨e, _, hW⟩ ↦ epi_mvShortComplex_g hι hU hV _ fun _ hm ↦
      isZero_twistedHomology_thomPairOver hι ω e (inter_subset_left.trans hW) (by omega))
    s hWo hWe

private theorem isIso_thomPairOverTwistedHomologyFinrankInv_univ [CompactSpace B] :
    IsIso (thomPairOverTwistedHomologyFinrankInv F E R hι ω univ) := by
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun b : B ↦ (trivializationAt F E b).baseSet)
    (fun b ↦ (trivializationAt F E b).open_baseSet)
    (fun b _ ↦ mem_iUnion.2 ⟨b, FiberBundle.mem_baseSet_trivializationAt' b⟩)
  have h := isIso_thomPairOverTwistedHomologyFinrankInv_biUnion (R := R) hι ω s
    (W := fun b ↦ (trivializationAt F E b).baseSet)
    (fun b _ ↦ (trivializationAt F E b).open_baseSet) fun b _ ↦ ⟨_, inferInstance, subset_rfl⟩
  rwa [eq_univ_of_univ_subset hs] at h

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

variable (F E R) in
/-- **The homology of the Thom pair in the rank degree with coefficients in the pulled-back
orientation system.** For a real vector bundle `E → B` of rank `r` over a compact base, with Thom
pair `(E, E₀)`, and a ring `R`, `Hᵣ(E, E₀; π^*o(E)) ≅ H₀(B; R)`, where `π^*o(E)` is the
orientation local system of `E` pulled back to the total space
(`TauCeti.thomPairSignLocalSystem`). No orientation of `E` is needed: the isomorphism is
normalized by an orientation `ω` of the model fibre, and sends the fibre class over `b`
(`TauCeti.thomPairSignFiberClass`) to the class of `b`
(`TauCeti.thomPairTwistedHomologyFinrankIso_hom_thomPairSignFiberClass`). -/
def thomPairTwistedHomologyFinrankIso [CompactSpace B] :
    (thomPair F E).twistedHomology (thomPairSignLocalSystem F E R hι) (finrank ℝ F) ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} R) 0).obj
        (ModuleCat.of R R)).obj (TopCat.of B) :=
  (overUnivIso hι (finrank ℝ F)).symm ≪≫
    (@asIso _ _ _ _ (thomPairOverTwistedHomologyFinrankInv F E R hι ω univ)
      (isIso_thomPairOverTwistedHomologyFinrankInv_univ hι ω)).symm ≪≫
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} R) 0).obj
      (ModuleCat.of R R)).mapIso (TopCat.isoOfHomeo (Homeomorph.Set.univ B))

/-- The isomorphism `Hᵣ(E, E₀; π^*o(E)) ≅ H₀(B; R)` sends the fibre class over `b` to the class of
the point `b`. -/
@[simp]
theorem thomPairTwistedHomologyFinrankIso_hom_thomPairSignFiberClass [CompactSpace B] (b : B) :
    (thomPairTwistedHomologyFinrankIso F E R hι ω).hom (thomPairSignFiberClass F E R hι ω b) =
      singularHomology₀Section (ModuleCat.of R R) (X := TopCat.of B) b 1 := by
  have hb := ConcreteCategory.congr_hom
    (singularHomology₀Section_thomPairOverTwistedHomologyFinrankInv (F := F) (E := E) (R := R) hι ω
      (⟨b, mem_univ b⟩ : (univ : Set B))) 1
  simp only [ConcreteCategory.comp_apply, ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply,
    one_smul] at hb
  simp only [thomPairTwistedHomologyFinrankIso, thomPairSignFiberClass, Iso.trans_hom,
    Iso.symm_hom, ConcreteCategory.comp_apply, Iso.hom_inv_id_apply, asIso_inv]
  rw [← hb, IsIso.hom_inv_id_apply, Functor.mapIso_hom, ← ConcreteCategory.comp_apply,
    singularHomology₀Section_naturality]
  simp only [TopCat.isoOfHomeo_hom, TopCat.hom_ofHom, ContinuousMap.coe_ofClass,
    Homeomorph.Set.univ_apply]

/-- **Morphisms out of `Hᵣ(E, E₀; π^*o(E))` are determined by the fibre classes.** Over a compact
base, two morphisms to a module `M` that agree on the fibre class over every point are equal. -/
theorem thomPairTwistedHomology_hom_ext [CompactSpace B] {M : ModuleCat.{w} R}
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

/-! ### The fibre classes through the fibre inclusions -/

omit [FiniteDimensional ℝ F] [Fintype ι] in
/-- The constant lift `⟨b, o⟩` lies over the projection of the fibre over `b`. -/
private theorem proj_const_eq_proj_fiberThomPairMap (b : B) (o : Orientation ℝ (E b) ι)
    (x : (TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).fst) :
    (ContinuousMap.const _ (⟨b, o⟩ : VectorBundleOrientationCover F E ι) x).proj =
      ((⟨π F E, FiberBundle.continuous_proj F E⟩ : C(TotalSpace F E, B)).comp
        (TopPair.Hom.fst (fiberThomPairMap F E b)).hom) x :=
  (congrArg TotalSpace.proj (fiberThomPairMap_fst_apply F E b x)).symm

variable (F E R) in
/-- The trivialization of the pulled-back orientation system `π^*o(E)`, written out as a pull-back
(`TauCeti.thomPairSignLocalSystem_def`), over the fibre pair `(E_b, E_b ∖ {0})` by evaluation at an
orientation `o` of `E_b`: the trivialization along the constant lift `⟨b, o⟩` of the fibre to the
orientation cover. -/
def fiberThomPairSignLocalSystemIso (b : B) (o : Orientation ℝ (E b) ι) :
    (LocalCoefficientSystem.pullback (TopPair.Hom.fst (fiberThomPairMap F E b)).hom).obj
        ((LocalCoefficientSystem.pullback (X := TopCat.of (TotalSpace F E)) (Y := TopCat.of B)
          ⟨π F E, FiberBundle.continuous_proj F E⟩).obj (signLocalSystem F E R hι)) ≅
      (constantFunctor _).obj (ModuleCat.of R R) :=
  ((LocalCoefficientSystem.pullbackCompIso (TopPair.Hom.fst (fiberThomPairMap F E b)).hom
      (Y := TopCat.of (TotalSpace F E)) (Z := TopCat.of B)
      ⟨π F E, FiberBundle.continuous_proj F E⟩).app (signLocalSystem F E R hι)).symm ≪≫
    VectorBundleOrientationCover.pullbackSignLocalSystemIsoOfLift R hι
      ((⟨π F E, FiberBundle.continuous_proj F E⟩ : C(TotalSpace F E, B)).comp
        (TopPair.Hom.fst (fiberThomPairMap F E b)).hom)
      (ContinuousMap.const _ ⟨b, o⟩) (proj_const_eq_proj_fiberThomPairMap b o)

omit [FiniteDimensional ℝ F] in
/-- The trivializations of the fibre pair by opposite orientations are opposite. -/
@[simp]
theorem fiberThomPairSignLocalSystemIso_neg_inv (b : B) (o : Orientation ℝ (E b) ι) :
    (fiberThomPairSignLocalSystemIso F E R hι b (-o)).inv =
      -(fiberThomPairSignLocalSystemIso F E R hι b o).inv := by
  unfold fiberThomPairSignLocalSystemIso
  -- `erw`: the definition states its source as an iterated pull-back, while the composite starts at
  -- the object of the composite functor `pullback _ ⋙ pullback _` that `pullbackCompIso` produces;
  -- the two agree only after unfolding `Functor.comp_obj`, which `rw` does not do.
  erw [Iso.trans_inv, Iso.trans_inv,
    VectorBundleOrientationCover.pullbackSignLocalSystemIsoOfLift_inv_of_eq_deck hι _
      (s := ContinuousMap.const _ ⟨b, o⟩) (proj_const_eq_proj_fiberThomPairMap b o)
      (proj_const_eq_proj_fiberThomPairMap b (-o)) fun _ ↦
      (VectorBundleOrientationCover.deck_apply (⟨b, o⟩ : VectorBundleOrientationCover F E ι)).symm,
    Preadditive.neg_comp]

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
      ((fiberThomPairSignLocalSystemIso F E R hι b o).inv ≫
        eqToHom (congrArg (LocalCoefficientSystem.pullback
          (TopPair.Hom.fst (fiberThomPairMap F E b)).hom).obj
          (thomPairSignLocalSystem_def (F := F) (E := E) (R := R) hι).symm)) n ≫
    TopPair.twistedHomologyMap (fiberThomPairMap F E b) (thomPairSignLocalSystem F E R hι) n

omit [FiniteDimensional ℝ F] in
/-- The fibre map is the comparison with chains twisted by the constant system, the change of
coefficients by the inverse of the trivialization by `o`, and the inclusion of the fibre pair. -/
theorem thomPairSignFiberMap_def (b : B) (o : Orientation ℝ (E b) ι) (n : ℕ) :
    thomPairSignFiberMap F E R hι b o n =
      ((TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).twistedHomologyConstantIso
          (ModuleCat.of R R) n).inv ≫
        (TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).twistedHomologyCoefficientMap
          ((fiberThomPairSignLocalSystemIso F E R hι b o).inv ≫
            eqToHom (congrArg (LocalCoefficientSystem.pullback
              (TopPair.Hom.fst (fiberThomPairMap F E b)).hom).obj
              (thomPairSignLocalSystem_def (F := F) (E := E) (R := R) hι).symm)) n ≫
        TopPair.twistedHomologyMap (fiberThomPairMap F E b) (thomPairSignLocalSystem F E R hι) n :=
  (rfl)

omit [FiniteDimensional ℝ F] in
/-- Trivializing the coefficients by the opposite orientation negates the fibre map. -/
@[simp]
theorem thomPairSignFiberMap_neg (b : B) (o : Orientation ℝ (E b) ι) (n : ℕ) :
    thomPairSignFiberMap F E R hι b (-o) n = -thomPairSignFiberMap F E R hι b o n := by
  rw [thomPairSignFiberMap, thomPairSignFiberMap, fiberThomPairSignLocalSystemIso_neg_inv,
    Preadditive.neg_comp, TopPair.twistedHomologyCoefficientMap_neg, Preadditive.neg_comp,
    Preadditive.comp_neg]


omit [FiniteDimensional ℝ F] in
/-- Over the whole base, the restricted orientation system is the pull-back of `π^*o(E)` along the
identification of the pair over the whole base with the Thom pair. -/
private theorem thomPairOverSignLocalSystem_univ :
    thomPairOverSignLocalSystem F E R hι univ =
      (LocalCoefficientSystem.pullback (TopPair.Hom.fst (thomPairOverUnivIso F E).hom).hom).obj
        (thomPairSignLocalSystem F E R hι) :=
  congrArg (fun g ↦ (LocalCoefficientSystem.pullback g).obj (thomPairSignLocalSystem F E R hι))
    (ContinuousMap.ext fun v ↦ (thomPairOverUnivIso_hom_fst_apply F E v).symm)

omit [FiniteDimensional ℝ F] in
private theorem overUnivIso_hom (n : ℕ) :
    (overUnivIso (R := R) (F := F) (E := E) hι n).hom =
      (thomPairOver F E univ).twistedHomologyCoefficientMap
          (eqToHom (thomPairOverSignLocalSystem_univ hι)) n ≫
        TopPair.twistedHomologyMap (thomPairOverUnivIso F E).hom
          (thomPairSignLocalSystem F E R hι) n := by
  rw [overUnivIso, Iso.trans_hom, Functor.mapIso_hom, HomologicalComplex.homologyFunctor_map]
  -- `erw`: the coefficient isomorphism is stated for the pair `thomPair F E` reached through
  -- `TopCat.of`, which `rw` does not see through.
  erw [TopPair.twistedChainComplexCoefficientIso_hom]
  -- `rfl`: it unfolds `eqToIso.hom`, `asIso_hom` and the abbreviation
  -- `TopPair.twistedHomologyCoefficientMap`, none of which `rw` matches here because the objects
  -- are reached through `TopCat.of` as above; the two proofs of the equality of coefficient
  -- systems then agree by proof irrelevance.
  rfl

omit [FiniteDimensional ℝ F] in
/-- Over a vector `v` of the fibre, the inverse of the trivialization by `o` sends `r` to the
element of the fibre of `o(E)` whose value at the orientation `o` is `r`. -/
theorem liftFiberEquiv_fiberThomPairSignLocalSystemIso_inv_app_apply (x : B)
    (o : Orientation ℝ (E x) ι)
    (v : FundamentalGroupoid (TopPair.ofSubset (X := TopCat.of (E x)) ({0}ᶜ : Set (E x))).fst)
    (r : R) :
    VectorBundleOrientationCover.liftFiberEquiv hι ⟨x, o⟩
        (congrArg TotalSpace.proj (fiberThomPairMap_fst_apply F E x v.as)).symm
        ((fiberThomPairSignLocalSystemIso F E R hι x o).inv.app v r) = r := by
  unfold fiberThomPairSignLocalSystemIso
  -- `erw`: the composite of isomorphisms of local systems is in the functor category.
  erw [Iso.trans_inv, NatTrans.comp_app, Iso.symm_inv, Iso.app_hom,
    LocalCoefficientSystem.pullbackCompIso_hom_app_app, Category.comp_id]
  exact (VectorBundleOrientationCover.liftFiberEquiv_apply hι _ _ _).trans
    (signLocalSystemObjEquiv_pullbackSignLocalSystemIsoOfLift_inv_app_apply
      hι ((⟨π F E, FiberBundle.continuous_proj F E⟩ : C(TotalSpace F E, B)).comp
        (TopPair.Hom.fst (fiberThomPairMap F E x)).hom) (ContinuousMap.const _ ⟨x, o⟩)
      (proj_const_eq_proj_fiberThomPairMap x o) v.as r)

omit [FiniteDimensional ℝ F] in
/-- On the fibre pair over `x`, the trivialization by `o` of the orientation system over the whole
base, carried to the Thom pair, is the trivialization by `o` of `π^*o(E)` over the fibre pair. -/
private theorem fiberSignIso_inv_comp_eqToHom (x : B) (o : Orientation ℝ (E x) ι) :
    ((fiberSignIso (R := R) hι (mem_univ x) o).inv ≫
      (LocalCoefficientSystem.pullback
        (TopPair.Hom.fst (fiberThomPairOverMap F E (mem_univ x))).hom).map
        (eqToHom (thomPairOverSignLocalSystem_univ hι))) ≫
      (TopPair.fstPullbackCompIso (fiberThomPairOverMap F E (mem_univ x))
        (thomPairOverUnivIso F E).hom (thomPairSignLocalSystem F E R hι)).inv ≫
      eqToHom (congrArg (fun g ↦ (LocalCoefficientSystem.pullback (TopPair.Hom.fst g).hom).obj
        (thomPairSignLocalSystem F E R hι))
        (fiberThomPairOverMap_comp_thomPairOverUnivIso_hom F E x)) =
    (fiberThomPairSignLocalSystemIso F E R hι x o).inv ≫
      eqToHom (congrArg (LocalCoefficientSystem.pullback
        (TopPair.Hom.fst (fiberThomPairMap F E x)).hom).obj
        (thomPairSignLocalSystem_def (F := F) (E := E) (R := R) hι).symm) := by
  have hfg := fiberThomPairOverMap_comp_thomPairOverUnivIso_hom F E x
  ext v : 2
  refine ModuleCat.hom_ext (LinearMap.ext fun r ↦ ?_)
  apply (VectorBundleOrientationCover.liftFiberEquiv hι ⟨x, o⟩
    (proj_const_eq_proj_fiberThomPairMap x o v.as)).injective
  have hR : VectorBundleOrientationCover.liftFiberEquiv hι ⟨x, o⟩
      (proj_const_eq_proj_fiberThomPairMap x o v.as)
      ((((fiberThomPairSignLocalSystemIso F E R hι x o).inv ≫
        eqToHom (congrArg (LocalCoefficientSystem.pullback
          (TopPair.Hom.fst (fiberThomPairMap F E x)).hom).obj
          (thomPairSignLocalSystem_def (F := F) (E := E) (R := R) hι).symm)).app v) r) = r := by
    -- `erw`: the components are maps between fibres of local systems, which are objects of
    -- `ModuleCat` only through the functors, so `ModuleCat.comp_apply` and the evaluation lemma
    -- match only up to unfolding the pull-backs.
    erw [NatTrans.comp_app, eqToHom_app, ModuleCat.comp_apply,
      VectorBundleOrientationCover.liftFiberEquiv_eqToHom_apply (R := R) hι rfl _ rfl _
        (proj_const_eq_proj_fiberThomPairMap x o v.as)]
    exact liftFiberEquiv_fiberThomPairSignLocalSystemIso_inv_app_apply (R := R) hι x o v r
  refine Eq.trans ?_ hR.symm
  rw [NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app]
  -- `erw`: `TopPair.fstPullbackCompIso_inv_app` gives an identity on the fibre of the iterated
  -- pull-back, while the next component starts at the fibre of the pull-back along the composite;
  -- the two fibres agree only up to unfolding `LocalCoefficientSystem.pullback`. The same mismatch
  -- of fibres, which are objects of `ModuleCat` only through the local systems, blocks `rw` with
  -- `ModuleCat.comp_apply`.
  erw [TopPair.fstPullbackCompIso_inv_app, Category.id_comp]
  rw [LocalCoefficientSystem.pullback_map_app, eqToHom_app, eqToHom_app]
  erw [ModuleCat.comp_apply]
  -- What remains are two transports between fibres of `o(E)` over points equal to `x`, around the
  -- inverse of evaluation at `o`.
  have hv : (TopPair.Hom.fst (fiberThomPairOverMap F E (mem_univ x) ≫
      (thomPairOverUnivIso F E).hom) v.as).proj = x :=
    (congrArg (fun g ↦ π F E (TopPair.Hom.fst g v.as)) hfg).trans
      (congrArg TotalSpace.proj (fiberThomPairMap_fst_apply F E x v.as))
  refine (VectorBundleOrientationCover.liftFiberEquiv_eqToHom_apply (R := R) hι
    (congrArg (fun g ↦ π F E (TopPair.Hom.fst g v.as)) hfg) _
    (rfl : (⟨x, o⟩ : VectorBundleOrientationCover F E ι) = ⟨x, o⟩) hv.symm _ _).trans ?_
  -- `erw`: as above, the composite is between fibres of local systems.
  erw [ModuleCat.comp_apply]
  refine (VectorBundleOrientationCover.liftFiberEquiv_eqToHom_apply (R := R) hι hv.symm _ rfl rfl
    hv.symm _).trans ?_
  -- Evaluation at `⟨x, o⟩` is `signLocalSystemFiberEquiv hι o`, whose inverse is the component of
  -- `fiberSignIso`.
  exact ((VectorBundleOrientationCover.liftFiberEquiv_apply hι _ _ _).trans
    (VectorBundleOrientationCover.signLocalSystemFiberEquiv_apply hι o _).symm).trans
    ((VectorBundleOrientationCover.signLocalSystemFiberEquiv (R := R) hι o).apply_symm_apply r)

omit [FiniteDimensional ℝ F] in
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
        ((fiberThomPairSignLocalSystemIso F E R hι x o).inv ≫
          eqToHom (congrArg (LocalCoefficientSystem.pullback
            (TopPair.Hom.fst (fiberThomPairMap F E x)).hom).obj
            (thomPairSignLocalSystem_def (F := F) (E := E) (R := R) hι).symm)) n ≫
      TopPair.twistedHomologyMap (fiberThomPairMap F E x) (thomPairSignLocalSystem F E R hι) n := by
  rw [overUnivIso_hom, TopPair.twistedHomologyMap_naturality_assoc,
    TopPair.twistedHomologyMap_comp_of_comp_eq (fiberThomPairOverMap F E (mem_univ x))
      (thomPairOverUnivIso F E).hom (thomPairSignLocalSystem F E R hι)
      (fiberThomPairOverMap_comp_thomPairOverUnivIso_hom F E x),
    ← TopPair.twistedHomologyCoefficientMap_comp_assoc,
    ← TopPair.twistedHomologyCoefficientMap_comp_assoc]
  congr 2
  exact fiberSignIso_inv_comp_eqToHom hι x o

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

end FiberClass

/-! ### The fibre classes read through the fibre inclusions -/

section FiberInclusion

variable (F E R) in
/-- The orientation system `π^*o(E)` pulled back to the fibre pair `(E_b, E_b ∖ {0})` along the
fibre inclusion `(E_b, E_b ∖ {0}) ⟶ (E, E₀)`, trivialized by evaluating at an orientation `o` of
`E_b`: every path in `E_b` projects to the constant path at `b`. It is the
trivialization along the constant lift `⟨b, o⟩` to the orientation cover
(`TauCeti.fiberThomPairSignIso_hom`). -/
def fiberThomPairSignIso (b : B) (o : Orientation ℝ (E b) ι) :
    (LocalCoefficientSystem.pullback (TopPair.Hom.fst (fiberThomPairMap F E b)).hom).obj
        (thomPairSignLocalSystem F E R hι) ≅
      (constantFunctor _).obj (ModuleCat.of R R) :=
  eqToIso (congrArg (fun g : _ ⟶ (thomPair F E).fst ↦
      (LocalCoefficientSystem.pullback g.hom).obj (thomPairSignLocalSystem F E R hι))
      (congrArg TopPair.Hom.fst
        (fiberThomPairOverMap_comp_thomPairOverUnivIso_hom F E b)).symm) ≪≫
    TopPair.fstPullbackCompIso _ _ _ ≪≫
    (LocalCoefficientSystem.pullback
        (TopPair.Hom.fst (fiberThomPairOverMap F E (mem_univ b))).hom).mapIso
      (eqToIso (congrArg (fun g ↦ (LocalCoefficientSystem.pullback
        (X := (thomPairOver F E univ).fst) g).obj (thomPairSignLocalSystem F E R hι))
          (thomPairOverUnivIso_hom_fst_eq F E))) ≪≫
    fiberSignIso hι (mem_univ b) o

omit [FiniteDimensional ℝ F] in
/-- The components of `fiberThomPairSignIso` are the transports between the pull-backs along the
two descriptions of the fibre inclusion, followed by the trivialization `fiberSignIso` of the fibre
over `b` as a fibre of the pair over the whole base: the comparison `TopPair.fstPullbackCompIso`
between them is the identity on each fibre. -/
private theorem fiberThomPairSignIso_hom_app_eq (b : B) (o : Orientation ℝ (E b) ι)
    (x : FundamentalGroupoid (TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).fst) :
    (fiberThomPairSignIso F E R hι b o).hom.app x =
      (eqToHom (congrArg (fun g : _ ⟶ (thomPair F E).fst ↦
          (LocalCoefficientSystem.pullback g.hom).obj (thomPairSignLocalSystem F E R hι))
          (congrArg TopPair.Hom.fst
            (fiberThomPairOverMap_comp_thomPairOverUnivIso_hom F E b)).symm)).app x ≫
        ((LocalCoefficientSystem.pullback
            (TopPair.Hom.fst (fiberThomPairOverMap F E (mem_univ b))).hom).map
          (eqToHom (congrArg (fun g : C((thomPairOver F E univ).fst, (thomPair F E).fst) ↦
            (LocalCoefficientSystem.pullback g).obj (thomPairSignLocalSystem F E R hι))
              (thomPairOverUnivIso_hom_fst_eq F E)))).app x ≫
        (fiberSignIso hι (mem_univ b) o).hom.app x :=
  -- A term rather than `rw`: `fstPullbackCompIso` pulls back `thomPairSignLocalSystem` along maps
  -- into `(thomPair F E).fst`, which is the total space only after unfolding.
  congrArg (_ ≫ ·) ((congrArg (· ≫ _) (TopPair.fstPullbackCompIso_hom_app
    (fiberThomPairOverMap F E (mem_univ b)) (thomPairOverUnivIso F E).hom
    (thomPairSignLocalSystem F E R hι) x)).trans (Category.id_comp _))

omit [FiniteDimensional ℝ F] in
/-- The components of `fiberThomPairSignIso` at `o` are evaluation at the orientation `o` of the
fibre `E_b` over the projection `b` of each point. -/
theorem fiberThomPairSignIso_hom_app (b : B) (o : Orientation ℝ (E b) ι)
    (x : FundamentalGroupoid (TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).fst) :
    (fiberThomPairSignIso F E R hι b o).hom.app x =
      ((LocalCoefficientSystem.pullback (TopPair.Hom.fst (fiberThomPairMap F E b)).hom).map
          (eqToHom (thomPairSignLocalSystem_def hι))).app x ≫
        (VectorBundleOrientationCover.liftFiberEquiv hι ⟨b, o⟩
          (congrArg TotalSpace.proj
            (fiberThomPairMap_fst_apply F E b x.as)).symm).toModuleIso.hom := by
  -- Every component except the evaluation at `o` is an identity or a transport between fibres of
  -- `o(E)` over equal points.
  simp only [fiberThomPairSignIso_hom_app_eq, eqToHom_map, eqToHom_app, fiberSignIso_hom_app]
  -- The two transports compose; their middle fibres agree only after unfolding, out of `simp`'s
  -- reach.
  refine (eqToHom_trans_assoc _ _ _).trans ?_
  -- Both sides evaluate at the orientation `o`, after transporting along `π (j x) = b`.
  refine ModuleCat.hom_ext (LinearMap.ext fun f ↦ ?_)
  refine (VectorBundleOrientationCover.signLocalSystemFiberEquiv_apply (R := R) hι o _).trans ?_
  refine Eq.trans ?_ (VectorBundleOrientationCover.liftFiberEquiv_apply hι _ _ _).symm
  exact VectorBundleOrientationCover.signLocalSystemObjEquiv_eqToHom_apply (R := R) hι
    (congrArg TotalSpace.proj (fiberThomPairMap_fst_apply F E b x.as)) f ⟨b, o⟩ _ rfl

omit [FiniteDimensional ℝ F] in
/-- The inverse of `fiberThomPairSignIso` is the inverse of the trivialization `fiberSignIso` of the
fibre over `b` as a fibre of the pair over the whole base, followed by the transports between the
pull-backs along the two descriptions of the fibre inclusion. -/
private theorem fiberThomPairSignIso_inv (b : B) (o : Orientation ℝ (E b) ι) :
    (fiberThomPairSignIso F E R hι b o).inv =
      (fiberSignIso hι (mem_univ b) o).inv ≫
        (LocalCoefficientSystem.pullback
            (TopPair.Hom.fst (fiberThomPairOverMap F E (mem_univ b))).hom).map
          (eqToHom (congrArg (fun g : C((thomPairOver F E univ).fst, (thomPair F E).fst) ↦
            (LocalCoefficientSystem.pullback g).obj (thomPairSignLocalSystem F E R hι))
              (thomPairOverUnivIso_hom_fst_eq F E).symm)) ≫
        (TopPair.fstPullbackCompIso _ _ _).inv ≫
        eqToHom (congrArg (fun g : _ ⟶ (thomPair F E).fst ↦
          (LocalCoefficientSystem.pullback g.hom).obj (thomPairSignLocalSystem F E R hι))
          (congrArg TopPair.Hom.fst (fiberThomPairOverMap_comp_thomPairOverUnivIso_hom F E b))) :=
  (rfl)

variable (ω : Orientation ℝ F ι)

/-- **The fibre class through the fibre inclusion.** The fibre class over `b` is the image under the
fibre inclusion `(E_b, E_b ∖ {0}) ⟶ (E, E₀)` of the class of the fibre pair which a linear
trivialization `e` at `b` reads as the point class of `1`, with the coefficients trivialized by the
orientation of `E_b` which `e` reads as `ω` (`TauCeti.fiberThomPairSignIso`). -/
theorem thomPairSignFiberClass_eq_twistedHomologyMap (e : Trivialization F (π F E))
    [e.IsLinear ℝ] {b : B} (hb : b ∈ e.baseSet) :
    thomPairSignFiberClass F E R hι ω b =
      TopPair.twistedHomologyMap (fiberThomPairMap F E b) (thomPairSignLocalSystem F E R hι)
        (finrank ℝ F)
        ((TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).twistedHomologyCoefficientMap
          (fiberThomPairSignIso F E R hι b ((e.mapOrientation ι hb).symm ω)).inv (finrank ℝ F)
          (((TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).twistedHomologyConstantIso
            (ModuleCat.of R R) (finrank ℝ F)).inv
            (TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.inv
              (ModuleCat.of R R) (finrank ℝ F)
              (complZeroPairPointHom (ModuleCat.of R R) F (finrank ℝ F) rfl (1 : R))))) := by
  rw [thomPairSignFiberClass, thomPairOverSignFiberClass_eq hι ω e hb (mem_univ b),
    thomPairOverSignFiberClassOf]
  generalize ((TopPair.ofSubset (X := TopCat.of (E b))
    ({0}ᶜ : Set (E b))).twistedHomologyConstantIso (ModuleCat.of R R) (finrank ℝ F)).inv _ = y
  suffices h : (TopPair.ofSubset (X := TopCat.of (E b))
        ({0}ᶜ : Set (E b))).twistedHomologyCoefficientMap
          (fiberSignIso hι (mem_univ b) ((e.mapOrientation ι hb).symm ω)).inv (finrank ℝ F) ≫
      TopPair.twistedHomologyMap (fiberThomPairOverMap F E (mem_univ b))
        (thomPairOverSignLocalSystem F E R hι univ) (finrank ℝ F) ≫
      (overUnivIso hι (finrank ℝ F)).hom =
    (TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).twistedHomologyCoefficientMap
        (fiberThomPairSignIso F E R hι b ((e.mapOrientation ι hb).symm ω)).inv (finrank ℝ F) ≫
      TopPair.twistedHomologyMap (fiberThomPairMap F E b) (thomPairSignLocalSystem F E R hι)
        (finrank ℝ F) from
    ConcreteCategory.congr_hom h y
  have h2 := TopPair.twistedHomologyMap_comp (fiberThomPairOverMap F E (mem_univ b))
    (thomPairOverUnivIso F E).hom (thomPairSignLocalSystem F E R hι) (finrank ℝ F)
  rw [TopPair.twistedHomologyMap_congr (thomPairSignLocalSystem F E R hι)
    (congrArg TopPair.Hom.fst (fiberThomPairOverMap_comp_thomPairOverUnivIso_hom F E b)).symm, h2]
  rw [overUnivIso_hom]
  -- `erw`: the coefficient system of the pair over the whole base is
  -- `thomPairOverSignLocalSystem F E R hι univ` only after unfolding it.
  erw [TopPair.twistedHomologyMap_naturality_assoc]
  simp only [← TopPair.twistedHomologyCoefficientMap_comp_assoc]
  congr 2
  rw [fiberThomPairSignIso_inv]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Iso.inv_hom_id,
    Category.comp_id]

end FiberInclusion

section FiberInclusionLift

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  [VectorBundle ℝ F E] {ι : Type} [Fintype ι] {R : Type w} [Ring R]
  (hι : Fintype.card ι = finrank ℝ F)

/-- The trivialization `fiberThomPairSignIso` at `o` is the trivialization of the orientation system
pulled back along the projection of the fibre, by the constant lift `⟨b, o⟩` to the orientation
cover (`TauCeti.VectorBundleOrientationCover.pullbackSignLocalSystemIsoOfLift`). -/
theorem fiberThomPairSignIso_hom (b : B) (o : Orientation ℝ (E b) ι) :
    (fiberThomPairSignIso F E R hι b o).hom =
      (LocalCoefficientSystem.pullback (TopPair.Hom.fst (fiberThomPairMap F E b)).hom).map
          (eqToHom (thomPairSignLocalSystem_def hι)) ≫
        ((LocalCoefficientSystem.pullbackCompIso (TopPair.Hom.fst (fiberThomPairMap F E b)).hom
          (Y := TopCat.of (TotalSpace F E)) (Z := TopCat.of B)
          ⟨π F E, FiberBundle.continuous_proj F E⟩).app (signLocalSystem F E R hι)).inv ≫
        (VectorBundleOrientationCover.pullbackSignLocalSystemIsoOfLift R hι
          ((⟨π F E, FiberBundle.continuous_proj F E⟩ :
            C(TopCat.of (TotalSpace F E), TopCat.of B)).comp
              (TopPair.Hom.fst (fiberThomPairMap F E b)).hom)
          (ContinuousMap.const _ ⟨b, o⟩)
          (fun x ↦ (congrArg TotalSpace.proj (fiberThomPairMap_fst_apply F E b x)).symm)).hom := by
  refine NatTrans.ext (funext fun x ↦ ?_)
  simp only [NatTrans.comp_app, fiberThomPairSignIso_hom_app]
  congr 1
  -- `erw`: the composite is one of local systems on the fibre pair, which is a functor category
  -- only after unfolding `LocalCoefficientSystem`.
  erw [NatTrans.comp_app, Iso.app_inv, LocalCoefficientSystem.pullbackCompIso_inv_app_app,
    Category.id_comp]
  -- Both sides evaluate at the orientation `o`.
  refine ModuleCat.hom_ext (LinearMap.ext fun f ↦ ?_)
  refine Eq.trans ?_ (VectorBundleOrientationCover.pullbackSignLocalSystemIsoOfLift_hom_app_apply
    (R := R) (F := F) (E := E) hι _ _ _ x.as _).symm
  exact VectorBundleOrientationCover.liftFiberEquiv_apply hι _ _ f

/-- The trivialization `fiberThomPairSignIso` at `o` is the identification of `π^*o(E)` with its
written-out form (`TauCeti.thomPairSignLocalSystem_def`), followed by the trivialization
`fiberThomPairSignLocalSystemIso` of the written-out form at `o`. -/
theorem fiberThomPairSignIso_hom_eq (b : B) (o : Orientation ℝ (E b) ι) :
    (fiberThomPairSignIso F E R hι b o).hom =
      (LocalCoefficientSystem.pullback (TopPair.Hom.fst (fiberThomPairMap F E b)).hom).map
          (eqToHom (thomPairSignLocalSystem_def hι)) ≫
        (fiberThomPairSignLocalSystemIso F E R hι b o).hom :=
  fiberThomPairSignIso_hom hι b o

end FiberInclusionLift

end TauCeti
