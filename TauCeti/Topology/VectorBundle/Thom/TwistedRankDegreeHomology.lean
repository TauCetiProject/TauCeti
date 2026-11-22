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
public import TauCeti.Topology.VectorBundle.Thom.RankDegreeHomology
import TauCeti.Algebra.Category.ModuleCat.SpanSingleton
import TauCeti.AlgebraicTopology.Singular.MayerVietoris.FiniteUnion
import TauCeti.AlgebraicTopology.Singular.Twisted.Coefficients
import TauCeti.AlgebraicTopology.Singular.Twisted.ConstantNaturality
import TauCeti.Topology.VectorBundle.Orientation.ThomClass
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
`TauCeti.isIso_biUnion_of_mayerVietoris`. The map `H₀(W; R) ⟶ Hᵣ(E|_W, E₀|_W;
π^*o(E))` sends the class of a point to the fibre class over it; it is well defined because the
fibre classes are constant along paths. Over a subset `W` of the base set of a linear
trivialization, the orientations of the fibres read by the trivialization trivialize `π^*o(E)` over
`E|_W`, which identifies the twisted homology with the untwisted homology of the product
`W × F`, and so with `H₀(W; R)`, carrying fibre classes to classes of points. The Mayer–Vietoris
sequence of pairs with local coefficients
(`TauCeti.LocalCoefficientSystem.pairTwistedMayerVietoris_exact₂`) ends in degree `r`, since the
twisted homology of the Thom pair vanishes below the rank, so the map is an isomorphism over a
finite union of trivializing open sets, hence over a compact base.

## Main definitions and results

* `TauCeti.thomPairSignLocalSystem`: the orientation local system pulled back to the total space.
* `TauCeti.thomPairSignFiberClass`: the fibre class over a point.
* `TauCeti.thomPairTwistedHomologyFinrankIso`: `Hᵣ(E, E₀; π^*o(E)) ≅ H₀(B; R)` over a compact base.
* `TauCeti.thomPairTwistedHomologyFinrankIso_hom_thomPairSignFiberClass`: it sends the fibre class
  over `b` to the class of `b`.
* `TauCeti.thomPairTwistedHomology_hom_ext`: over a compact base, morphisms out of
  `Hᵣ(E, E₀; π^*o(E))` are determined by their values on the fibre classes.
* `TauCeti.thomPairSignFiberClass_neg`: reversing `ω` negates the fibre classes.

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
open TauCeti.VectorBundleOrientationCover (signLocalSystem signLocalSystemFiberEquiv)

universe w

namespace TauCeti

variable {B : Type w} [TopologicalSpace B] {F : Type w}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {E : B → Type w}
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

omit [FiniteDimensional ℝ F] in
theorem thomPairSignLocalSystem_def :
    thomPairSignLocalSystem F E R hι =
      (LocalCoefficientSystem.pullback (X := TopCat.of (TotalSpace F E)) (Y := TopCat.of B)
        ⟨π F E, FiberBundle.continuous_proj F E⟩).obj (signLocalSystem F E R hι) :=
  (rfl)

/-- The fibres of the orientation system pulled back to the total space are projective, as those of
the orientation system are (`TauCeti.VectorBundleOrientationCover.projective_signLocalSystem_obj`).
Stated over the total space of the Thom pair, where twisted cohomology of the pair looks for it. -/
instance projective_thomPairSignLocalSystem_obj (x : FundamentalGroupoid (thomPair F E).fst) :
    CategoryTheory.Projective ((thomPairSignLocalSystem F E R hι).obj x) :=
  inferInstanceAs (CategoryTheory.Projective ((signLocalSystem F E R hι).obj _))

variable (F E R) in
/-- The pulled-back orientation system restricted to the part of the total space over `W`. -/
private def overSignLocalSystem (W : Set B) :
    LocalCoefficientSystem R (thomPairOver F E W).fst :=
  (LocalCoefficientSystem.pullback (X := TopCat.of ↥(π F E ⁻¹' W))
    (ContinuousMap.subtypeVal (π F E ⁻¹' W))).obj (thomPairSignLocalSystem F E R hι)

/-- The trivialization of the pulled-back orientation system over the fibre `E_x` by evaluation
at an orientation of `E_x`: every path in `E_x` projects to the constant path at `x`. -/
private def fiberSignIso {W : Set B} {x : B} (hx : x ∈ W) (ω : Orientation ℝ (E x) ι) :
    (LocalCoefficientSystem.pullback (TopPair.Hom.fst (fiberThomPairOverMap F E hx)).hom).obj
        (overSignLocalSystem F E R hι W) ≅
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
          (overSignLocalSystem F E R hι W)).map q = 𝟙 _ :=
        (congrArg (signLocalSystem F E R hι).map h).trans
          ((signLocalSystem F E R hι).map_id _)
      rw [h', LocalCoefficientSystem.constantFunctor_obj_map]
      exact (Category.id_comp _).trans (Category.comp_id _).symm

omit [NormedSpace ℝ F] [FiniteDimensional ℝ F] [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)]
  [VectorBundle ℝ F E] in
/-- A vector over a subset of the base set of a trivialization lies over its base set. -/
private theorem proj_mem_baseSet {c : B} {W : Set B} (hW : W ⊆ (trivializationAt F E c).baseSet)
    (v : π F E ⁻¹' W) : v.val.proj ∈ (trivializationAt F E c).baseSet :=
  hW v.property

/-- Over a subset `W` of the base set of the chosen trivialization at `c`, the pulled-back
orientation system is trivialized by evaluating at the orientation read as `ω` by it. -/
private def baseSetSignIso (c : B) {W : Set B} (hW : W ⊆ (trivializationAt F E c).baseSet)
    (ω : Orientation ℝ F ι) :
    overSignLocalSystem F E R hι W ≅
      (constantFunctor _).obj (ModuleCat.of R R) :=
  NatIso.ofComponents (fun v ↦ (signLocalSystemFiberEquiv hι
      (((trivializationAt F E c).mapOrientation ι (proj_mem_baseSet hW v.as)).symm ω)).toModuleIso)
    fun {v v'} q ↦ ModuleCat.hom_ext <| LinearMap.ext fun f ↦ by
      -- The section of the orientation cover read as `ω` lifts the projection of the path.
      have h := (VectorBundleOrientationCover.isCoveringMap_proj (F := F) (E := E)
        hι).monodromy_map_of_lift
        (g := (⟨π F E, FiberBundle.continuous_proj F E⟩ : C(TotalSpace F E, B)).comp
          (ContinuousMap.subtypeVal (π F E ⁻¹' W)))
        (s := fun v : π F E ⁻¹' W ↦ (⟨v.val.proj, ((trivializationAt F E c).mapOrientation ι
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
/-- The trivialization of a fibre by the opposite orientation is the negative of the one by `o`. -/
private theorem fiberSignIso_neg_inv {W : Set B} {x : B} (hx : x ∈ W) (o : Orientation ℝ (E x) ι) :
    (fiberSignIso (R := R) hι hx (-o)).inv = -(fiberSignIso hι hx o).inv := by
  ext v : 2
  exact congrArg ModuleCat.ofHom
    (VectorBundleOrientationCover.signLocalSystemFiberEquiv_neg_symm hι o)

section FiberClass

variable (ω : Orientation ℝ F ι)

variable (R) in
/-- The fibre class over `x ∈ W` read through a linear trivialization `e` at `x`. -/
private def fiberClassAux (e : Trivialization F (π F E)) [e.IsLinear ℝ] {x : B}
    (hx : x ∈ e.baseSet) {W : Set B} (hxW : x ∈ W) :
    (thomPairOver F E W).twistedHomology (overSignLocalSystem F E R hι W) (finrank ℝ F) :=
  TopPair.twistedHomologyMap (fiberThomPairOverMap F E hxW) (overSignLocalSystem F E R hι W)
    (finrank ℝ F)
    ((TopPair.ofSubset (X := TopCat.of (E x)) ({0}ᶜ : Set (E x))).twistedHomologyCoefficientMap
      (fiberSignIso hι hxW ((e.mapOrientation ι hx).symm ω)).inv (finrank ℝ F)
      (((TopPair.ofSubset (X := TopCat.of (E x)) ({0}ᶜ : Set (E x))).twistedHomologyConstantIso
        (ModuleCat.of R R) (finrank ℝ F)).inv
        (TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ x hx).complZeroPairIso.inv
          (ModuleCat.of R R) (finrank ℝ F)
          (complZeroPairPointHom (ModuleCat.of R R) F (finrank ℝ F) rfl (1 : R)))))

/-- Over a subset `W` of the base set of the chosen trivialization at `c`, the trivialization
identifies `Hᵣ(E|_W, E₀|_W; π^*o(E))` with `H₀(W; R)`. -/
private def localIso (c : B) {W : Set B}
    (hW : W ⊆ (trivializationAt F E c).baseSet) :
    (thomPairOver F E W).twistedHomology (overSignLocalSystem F E R hι W) (finrank ℝ F) ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} R) 0).obj
        (ModuleCat.of R R)).obj (TopCat.of W) :=
  (HomologicalComplex.homologyFunctor _ _ (finrank ℝ F)).mapIso
      ((thomPairOver F E W).twistedChainComplexCoefficientIso (baseSetSignIso hι c hW ω)) ≪≫
    (thomPairOver F E W).twistedHomologyConstantIso (ModuleCat.of R R) (finrank ℝ F) ≪≫
    asIso (TopPair.singularHomologyMap ((trivializationAt F E c).thomPairOverIso ℝ hW).hom
      (ModuleCat.of R R) (finrank ℝ F)) ≪≫
    prodThomPairSingularHomologyIso (ModuleCat.of R R) W F 0 (finrank ℝ F)

omit [FiniteDimensional ℝ F] in
/-- The trivialization over the base set, restricted to a fibre, is the trivialization of the
fibre by the orientation it reads as `ω`. -/
private theorem pullback_map_baseSetSignIso_hom (c : B) {W : Set B}
    (hW : W ⊆ (trivializationAt F E c).baseSet) {x : B} (hxW : x ∈ W) :
    (LocalCoefficientSystem.pullback (TopPair.Hom.fst (fiberThomPairOverMap F E hxW)).hom).map
        (baseSetSignIso (R := R) hι c hW ω).hom ≫
      (LocalCoefficientSystem.pullbackConstantIso _ (ModuleCat.of R R)).hom =
    (fiberSignIso hι hxW (((trivializationAt F E c).mapOrientation ι (hW hxW)).symm ω)).hom := by
  ext v : 2
  rw [NatTrans.comp_app, LocalCoefficientSystem.pullbackConstantIso_hom_app]
  -- After the unit law, both components are evaluation at the orientation of `E_x` read as `ω`:
  -- the closing `rfl` unfolds `fiberThomPairOverMap`, by which the point of `E|_W` under `v` lies
  -- over `x`.
  exact (Category.comp_id _).trans rfl

omit [FiniteDimensional ℝ F] in
/-- Over a subset of the base set of the trivialization at `c`, the fibre inclusion over `x`, read
through the trivializations of the coefficient systems by the orientation that this trivialization
reads as `ω`, is the fibre inclusion in ordinary homology. -/
@[reassoc]
private theorem fiberSign_comp_twistedHomologyMap_comp_baseSetSign (c : B) {W : Set B}
    (hW : W ⊆ (trivializationAt F E c).baseSet) {x : B} (hxW : x ∈ W) :
    ((TopPair.ofSubset (X := TopCat.of (E x)) ({0}ᶜ : Set (E x))).twistedHomologyConstantIso
        (ModuleCat.of R R) (finrank ℝ F)).inv ≫
      (TopPair.ofSubset (X := TopCat.of (E x)) ({0}ᶜ : Set (E x))).twistedHomologyCoefficientMap
        (fiberSignIso hι hxW (((trivializationAt F E c).mapOrientation ι (hW hxW)).symm ω)).inv
        (finrank ℝ F) ≫
      TopPair.twistedHomologyMap (fiberThomPairOverMap F E hxW) (overSignLocalSystem F E R hι W)
        (finrank ℝ F) ≫
      (thomPairOver F E W).twistedHomologyCoefficientMap (baseSetSignIso hι c hW ω).hom
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

private theorem localIso_hom (c : B) {W : Set B} (hW : W ⊆ (trivializationAt F E c).baseSet) :
    (localIso (R := R) hι ω c hW).hom =
      (thomPairOver F E W).twistedHomologyCoefficientMap (baseSetSignIso hι c hW ω).hom
          (finrank ℝ F) ≫
        ((thomPairOver F E W).twistedHomologyConstantIso (ModuleCat.of R R) (finrank ℝ F)).hom ≫
        TopPair.singularHomologyMap ((trivializationAt F E c).thomPairOverIso ℝ hW).hom
          (ModuleCat.of R R) (finrank ℝ F) ≫
        (prodThomPairSingularHomologyIso (ModuleCat.of R R) W F 0 (finrank ℝ F)).hom := by
  simp only [localIso, Iso.trans_hom, Functor.mapIso_hom, HomologicalComplex.homologyFunctor_map,
    TopPair.twistedChainComplexCoefficientIso_hom, asIso_hom]

/-- Through the trivialization at `c`, the fibre class over `x ∈ W` read through that
trivialization is the class of the point `x`. -/
private theorem localIso_hom_fiberClassAux (c : B) {W : Set B}
    (hW : W ⊆ (trivializationAt F E c).baseSet) {x : B} (hxW : x ∈ W) :
    (localIso hι ω c hW).hom (fiberClassAux R hι ω (trivializationAt F E c) (hW hxW) hxW) =
      singularHomology₀Section (ModuleCat.of R R) (X := TopCat.of W) ⟨x, hxW⟩ 1 := by
  have h := ConcreteCategory.congr_hom
    (fiberSign_comp_twistedHomologyMap_comp_baseSetSign_assoc (R := R) hι ω c hW hxW
      (TopPair.singularHomologyMap ((trivializationAt F E c).thomPairOverIso ℝ hW).hom
          (ModuleCat.of R R) (finrank ℝ F) ≫
        (prodThomPairSingularHomologyIso (ModuleCat.of R R) W F 0 (finrank ℝ F)).hom))
    (TopPair.singularHomologyMap ((trivializationAt F E c).continuousLinearEquivAt
      ℝ x (hW hxW)).complZeroPairIso.inv (ModuleCat.of R R) (finrank ℝ F)
      (complZeroPairPointHom (ModuleCat.of R R) F (finrank ℝ F) rfl (1 : R)))
  rw [localIso_hom, fiberClassAux]
  simp only [ConcreteCategory.comp_apply] at h ⊢
  rw [h, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← TopPair.singularHomologyMap_comp_assoc,
    Trivialization.fiberThomPairOverMap_comp_thomPairOverIso_hom, ← ConcreteCategory.comp_apply,
    ← TopPair.singularHomologyMap_comp_assoc, Iso.inv_hom_id_assoc, ConcreteCategory.comp_apply,
    singularHomologyMap_prodThomPairFiberMap_complZeroPairPointHom_one, Iso.inv_hom_id_apply]

/-- The fibre class does not depend on the linear trivialization through which it is read: two
trivializations reading the fibre orientation alike read the generator alike, and reading it
oppositely changes both the generator and the trivialization of the coefficients by a sign. -/
private theorem fiberClassAux_eq (e e' : Trivialization F (π F E)) [e.IsLinear ℝ] [e'.IsLinear ℝ]
    {x : B} (hx : x ∈ e.baseSet) (hx' : x ∈ e'.baseSet) {W : Set B} (hxW : x ∈ W) :
    fiberClassAux R hι ω e hx hxW = fiberClassAux R hι ω e' hx' hxW := by
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
    rw [fiberClassAux, fiberClassAux, h', hinv]
  · have h' : (e'.mapOrientation ι hx').symm ω = -o := by
      rw [Equiv.symm_apply_eq, Trivialization.mapOrientation_neg, h]
      exact (neg_neg ω).symm
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
    rw [fiberClassAux, fiberClassAux, h', hinv, fiberSignIso_neg_inv,
      TopPair.twistedHomologyCoefficientMap_neg]
    simp only [ModuleCat.hom_neg, LinearMap.neg_apply, map_neg, neg_neg, o]

variable (F E R) in
/-- The restriction `Hₙ(E|_W, E₀|_W; π^*o(E)) ⟶ Hₙ(E|_{W'}, E₀|_{W'}; π^*o(E))` for `W ⊆ W'`, the
map of the Mayer–Vietoris sequence of pairs of subsets of the total space. -/
private abbrev restr {W W' : Set B} (h : W ⊆ W') (n : ℕ) :
    (thomPairOver F E W).twistedHomology (overSignLocalSystem F E R hι W) n ⟶
      (thomPairOver F E W').twistedHomology (overSignLocalSystem F E R hι W') n :=
  HomologicalComplex.homologyMap
    ((thomPairSignLocalSystem F E R hι).subsetPairTwistedChainComplexMap
    inter_subset_left inter_subset_left (preimage_mono h)
    (inter_subset_inter_left _ (preimage_mono h))) n

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
    overSignLocalSystem F E R hι W ⟶
      (LocalCoefficientSystem.pullback
        (TopPair.Hom.fst (overInclusion (F := F) (E := E) h)).hom).obj
        (overSignLocalSystem F E R hι W') :=
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
      TopPair.twistedHomologyMap (overInclusion h) (overSignLocalSystem F E R hι W') n :=
  (congrArg (HomologicalComplex.homologyMap · n)
    (LocalCoefficientSystem.subsetPairTwistedChainComplexMap_def (thomPairSignLocalSystem F E R hι)
      inter_subset_left inter_subset_left (preimage_mono h)
      (inter_subset_inter_left _ (preimage_mono h)))).trans
    (HomologicalComplex.homologyMap_comp _ _ _)

/-- Restriction carries fibre classes to fibre classes. -/
private theorem restr_fiberClassAux (e : Trivialization F (π F E)) [e.IsLinear ℝ] {x : B}
    (hx : x ∈ e.baseSet) {W W' : Set B} (h : W ⊆ W') (hxW : x ∈ W) :
    restr F E R hι h (finrank ℝ F) (fiberClassAux R hι ω e hx hxW) =
      fiberClassAux R hι ω e hx (h hxW) := by
  have hfg : fiberThomPairOverMap F E hxW ≫ overInclusion h = fiberThomPairOverMap F E (h hxW) :=
    TopPair.hom_ext_of_fst _ (TopCat.ext fun _ ↦ rfl)
  have key := TopPair.twistedHomologyMap_comp (fiberThomPairOverMap F E hxW) (overInclusion h)
    (overSignLocalSystem F E R hι W') (finrank ℝ F)
  rw [TopPair.twistedHomologyMap_congr _ (congrArg TopPair.Hom.fst hfg)] at key
  have key' : TopPair.twistedHomologyMap (fiberThomPairOverMap F E hxW)
        ((LocalCoefficientSystem.pullback (TopPair.Hom.fst (overInclusion h)).hom).obj
          (overSignLocalSystem F E R hι W')) (finrank ℝ F) ≫
      TopPair.twistedHomologyMap (overInclusion h) (overSignLocalSystem F E R hι W') (finrank ℝ F) =
      (TopPair.ofSubset (X := TopCat.of (E x)) ({0}ᶜ : Set (E x))).twistedHomologyCoefficientMap
          (TopPair.fstPullbackCompIso (fiberThomPairOverMap F E hxW) (overInclusion h)
            (overSignLocalSystem F E R hι W')).inv (finrank ℝ F) ≫
        (TopPair.ofSubset (X := TopCat.of (E x)) ({0}ᶜ : Set (E x))).twistedHomologyCoefficientMap
          (eqToHom (congrArg (fun g ↦ (LocalCoefficientSystem.pullback (TopPair.Hom.fst g).hom).obj
            (overSignLocalSystem F E R hι W')) hfg)) (finrank ℝ F) ≫
        TopPair.twistedHomologyMap (fiberThomPairOverMap F E (h hxW))
          (overSignLocalSystem F E R hι W') (finrank ℝ F) := by
    rw [key, ← TopPair.twistedHomologyCoefficientMap_comp_assoc, Iso.inv_hom_id,
      TopPair.twistedHomologyCoefficientMap_id, Category.id_comp]
  have hco : (((fiberSignIso hι hxW ((e.mapOrientation ι hx).symm ω)).inv ≫
      (LocalCoefficientSystem.pullback (TopPair.Hom.fst (fiberThomPairOverMap F E hxW)).hom).map
        (overRestrIso R hι h)) ≫
      (TopPair.fstPullbackCompIso (fiberThomPairOverMap F E hxW) (overInclusion h)
        (overSignLocalSystem F E R hι W')).inv) ≫
      eqToHom (congrArg (fun g ↦ (LocalCoefficientSystem.pullback (TopPair.Hom.fst g).hom).obj
        (overSignLocalSystem F E R hι W')) hfg) =
      (fiberSignIso hι (h hxW) ((e.mapOrientation ι hx).symm ω)).inv := by
    ext v : 2
    simp only [NatTrans.comp_app, LocalCoefficientSystem.pullback_map_app, overRestrIso_app,
      TopPair.fstPullbackCompIso_inv_app, eqToHom_app]
    -- Both sides are evaluation at the same orientation of `E_x`; the remaining `eqToHom` is
    -- between fibres of `o(E)` over the projections of `v` along the two fibre inclusions, which
    -- are `x` by definition of `fiberThomPairOverMap`, so it is the identity.
    rfl
  rw [restr_eq, fiberClassAux, fiberClassAux, ← ConcreteCategory.comp_apply,
    TopPair.twistedHomologyMap_naturality_assoc, key', ← ConcreteCategory.comp_apply,
    ← TopPair.twistedHomologyCoefficientMap_comp_assoc,
    ← TopPair.twistedHomologyCoefficientMap_comp_assoc,
    ← TopPair.twistedHomologyCoefficientMap_comp_assoc, hco, ConcreteCategory.comp_apply]

variable (F E R) in
/-- The fibre class over `x ∈ W`: the image of the generator of the fibre pair over `x`, read
through the chosen trivialization at `x`, with coefficients trivialized by the orientation that this
trivialization reads as `ω`. It does not depend on the trivialization (`fiberClassAux_eq`). -/
private def fiberClass {W : Set B} {x : B} (hxW : x ∈ W) :
    (thomPairOver F E W).twistedHomology (overSignLocalSystem F E R hι W) (finrank ℝ F) :=
  fiberClassAux R hι ω (trivializationAt F E x) (FiberBundle.mem_baseSet_trivializationAt' x) hxW

private theorem localIso_hom_fiberClass (c : B) {W : Set B}
    (hW : W ⊆ (trivializationAt F E c).baseSet) {x : B} (hxW : x ∈ W) :
    (localIso hι ω c hW).hom (fiberClass F E R hι ω hxW) =
      singularHomology₀Section (ModuleCat.of R R) (X := TopCat.of W) ⟨x, hxW⟩ 1 := by
  rw [fiberClass, fiberClassAux_eq hι ω _ (trivializationAt F E c) _ (hW hxW),
    localIso_hom_fiberClassAux]

private theorem restr_fiberClass {W W' : Set B} (h : W ⊆ W') {x : B} (hxW : x ∈ W) :
    restr F E R hι h (finrank ℝ F) (fiberClass F E R hι ω hxW) = fiberClass F E R hι ω (h hxW) :=
  restr_fiberClassAux hι ω _ _ h hxW

/-- **The fibre classes are constant along paths**: near each point `b` they are read through the
chosen trivialization at `b` as the classes of the points. -/
private theorem fiberClass_eq_of_path {W : Set B} {x y : W} (γ : Path x y) :
    fiberClass F E R hι ω x.property = fiberClass F E R hι ω y.property :=
  eq_of_path_of_mono (fun h ↦ restr F E R hι h (finrank ℝ F))
    (fun _ x ↦ fiberClass F E R hι ω x.property) (fun h x ↦ restr_fiberClass hι ω h x.property)
    (fun b ↦ (trivializationAt F E b).baseSet)
    (fun b ↦ (trivializationAt F E b).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' b))
    (fun b _ ↦ ⟨(localIso hι ω b inter_subset_right).hom, 1, inferInstance, fun x ↦ by
      rw [localIso_hom_fiberClass, one_smul]⟩) γ

variable (F E R) in
/-- The map `H₀(W; R) ⟶ Hᵣ(E|_W, E₀|_W; π^*o(E))` sending the class of a point to the fibre class
over it. -/
private def toThomPairOver (W : Set B) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} R) 0).obj (ModuleCat.of R R)).obj
        (TopCat.of W) ⟶
      (thomPairOver F E W).twistedHomology (overSignLocalSystem F E R hι W) (finrank ℝ F) :=
  singularHomology₀Desc (ModuleCat.of R R) (X := TopCat.of W)
    (fun x ↦ ModuleCat.ofHom (LinearMap.toSpanSingleton R _ (fiberClass F E R hι ω x.property)))
    fun _ _ γ ↦ by rw [fiberClass_eq_of_path hι ω γ]

@[reassoc]
private theorem singularHomology₀Section_toThomPairOver {W : Set B} (x : W) :
    singularHomology₀Section (ModuleCat.of R R) (X := TopCat.of W) x ≫
        toThomPairOver F E R hι ω W =
      ModuleCat.ofHom (LinearMap.toSpanSingleton R _ (fiberClass F E R hι ω x.property)) :=
  singularHomology₀Section_singularHomology₀Desc (X := TopCat.of W) _ _ _ x

/-- The maps over `W ⊆ W'` commute with the restrictions. -/
private theorem toThomPairOver_naturality {W W' : Set B} (h : W ⊆ W') :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} R) 0).obj (ModuleCat.of R R)).map
        (TopCat.ofHom (ContinuousMap.inclusion h)) ≫ toThomPairOver F E R hι ω W' =
      toThomPairOver F E R hι ω W ≫ restr F E R hι h (finrank ℝ F) := by
  refine singularHomology₀_hom_ext _ fun x ↦ ?_
  rw [singularHomology₀Section_naturality_assoc, singularHomology₀Section_toThomPairOver,
    singularHomology₀Section_toThomPairOver_assoc, ModuleCat.ofHom_toSpanSingleton_comp,
    restr_fiberClass]
  simp only [TopCat.hom_ofHom, ContinuousMap.inclusion_apply_coe]

/-- Over a subset of the base set of a chosen trivialization, the map is an isomorphism, inverse to
`localIso`. -/
private theorem toThomPairOver_comp_localIso_hom (c : B) {W : Set B}
    (hW : W ⊆ (trivializationAt F E c).baseSet) :
    toThomPairOver F E R hι ω W ≫ (localIso hι ω c hW).hom = 𝟙 _ := by
  refine singularHomology₀_hom_ext _ fun x ↦ ?_
  rw [singularHomology₀Section_toThomPairOver_assoc, ModuleCat.ofHom_toSpanSingleton_comp,
    localIso_hom_fiberClass, Category.comp_id]
  ext
  simp

private theorem isIso_toThomPairOver_of_subset (c : B) {W : Set B}
    (hW : W ⊆ (trivializationAt F E c).baseSet) : IsIso (toThomPairOver F E R hι ω W) := by
  rw [(Iso.comp_hom_eq_id _).1 (toThomPairOver_comp_localIso_hom hι ω c hW)]
  infer_instance

/-! ### The Mayer–Vietoris step -/

variable (F E R) in
/-- The map between the relative twisted homology of two pairs of subsets of the total space, for
inclusions of the subsets. -/
private abbrev rmap {A₁ C₁ A₂ C₂ : Set (TotalSpace F E)} (h₁ : C₁ ⊆ A₁)
    (h₂ : C₂ ⊆ A₂) (hA : A₁ ⊆ A₂) (hC : C₁ ⊆ C₂) (n : ℕ) :
    (TopPair.ofInclusion (X := TopCat.of (TotalSpace F E)) h₁).twistedHomology
      ((LocalCoefficientSystem.pullback (X := TopCat.of ↥A₁) (ContinuousMap.subtypeVal A₁)).obj
        (thomPairSignLocalSystem F E R hι)) n ⟶
    (TopPair.ofInclusion (X := TopCat.of (TotalSpace F E)) h₂).twistedHomology
      ((LocalCoefficientSystem.pullback (X := TopCat.of ↥A₂) (ContinuousMap.subtypeVal A₂)).obj
        (thomPairSignLocalSystem F E R hι)) n :=
  HomologicalComplex.homologyMap
    ((thomPairSignLocalSystem F E R hι).subsetPairTwistedChainComplexMap h₁ h₂ hA hC) n

omit [FiniteDimensional ℝ F] in
private theorem rmap_comp_rmap {A₁ C₁ A₂ C₂ A₃ C₃ : Set (TotalSpace F E)} (h₁ : C₁ ⊆ A₁)
    (h₂ : C₂ ⊆ A₂) (h₃ : C₃ ⊆ A₃) (hA : A₁ ⊆ A₂) (hC : C₁ ⊆ C₂) (hA' : A₂ ⊆ A₃) (hC' : C₂ ⊆ C₃)
    (n : ℕ) :
    rmap F E R hι h₁ h₂ hA hC n ≫ rmap F E R hι h₂ h₃ hA' hC' n =
      rmap F E R hι h₁ h₃ (hA.trans hA') (hC.trans hC') n :=
  (HomologicalComplex.homologyMap_comp _ _ _).symm.trans
    (congrArg (HomologicalComplex.homologyMap · n)
      (LocalCoefficientSystem.subsetPairTwistedChainComplexMap_comp_subsetPairTwistedChainComplexMap
        _ _ _ _ _ _ _ _))

omit [FiniteDimensional ℝ F] in
private theorem rmap_self {A₁ C₁ : Set (TotalSpace F E)} (h₁ : C₁ ⊆ A₁) (n : ℕ) :
    rmap F E R hι h₁ h₁ subset_rfl subset_rfl n = 𝟙 _ :=
  (congrArg (HomologicalComplex.homologyMap · n)
    (LocalCoefficientSystem.subsetPairTwistedChainComplexMap_self _ _)).trans
      (HomologicalComplex.homologyMap_id _ _)

omit [FiniteDimensional ℝ F] in
/-- Restrictions compose: `restr` is `rmap` for the pairs `(π⁻¹ W, π⁻¹ W ∩ E₀)`. -/
private theorem restr_comp_restr {W W' W'' : Set B} (h : W ⊆ W') (h' : W' ⊆ W'') (n : ℕ) :
    restr F E R hι h n ≫ restr F E R hι h' n = restr F E R hι (h.trans h') n :=
  rmap_comp_rmap hι _ _ _ _ _ _ _ n

variable (F E R) in
/-- Equal pairs of subsets have isomorphic relative twisted homology. -/
private def rmapIso {A₁ C₁ A₂ C₂ : Set (TotalSpace F E)} (h₁ : C₁ ⊆ A₁)
    (h₂ : C₂ ⊆ A₂) (hA : A₁ = A₂) (hC : C₁ = C₂) (n : ℕ) :
    (TopPair.ofInclusion (X := TopCat.of (TotalSpace F E)) h₁).twistedHomology
      ((LocalCoefficientSystem.pullback (X := TopCat.of ↥A₁) (ContinuousMap.subtypeVal A₁)).obj
        (thomPairSignLocalSystem F E R hι)) n ≅
    (TopPair.ofInclusion (X := TopCat.of (TotalSpace F E)) h₂).twistedHomology
      ((LocalCoefficientSystem.pullback (X := TopCat.of ↥A₂) (ContinuousMap.subtypeVal A₂)).obj
        (thomPairSignLocalSystem F E R hι)) n where
  hom := rmap F E R hι h₁ h₂ hA.subset hC.subset n
  inv := rmap F E R hι h₂ h₁ hA.symm.subset hC.symm.subset n
  hom_inv_id := (rmap_comp_rmap hι _ _ _ _ _ _ _ n).trans (rmap_self hι h₁ n)
  inv_hom_id := (rmap_comp_rmap hι _ _ _ _ _ _ _ n).trans (rmap_self hι h₂ n)

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
    (rmapIso F E R hι inter_subset_left _ (preimage_inter) (by ext; simp; tauto) n)
    (Iso.refl _)
    (rmapIso F E R hι inter_subset_left _ (preimage_union) (by ext; simp; tauto) n) ?_ ?_
  -- The objects `(thomPairOver F E W).twistedHomology (overSignLocalSystem F E R hι W) n` and the
  -- homology of the pair of subsets `(π⁻¹ W, π⁻¹ W ∩ E₀)` agree only after unfolding
  -- `thomPairOver`, so `simp` and `rw` meet compositions that are not type correct at reducible
  -- transparency and make no progress; the two squares are assembled with `Eq.trans` instead.
  · apply biprod.hom_ext
    · exact (congrArg (_ ≫ ·)
        (LocalCoefficientSystem.pairTwistedMayerVietorisToBiprod_fst _ _ _ n)).trans
        ((rmap_comp_rmap hι _ _ _ _ _ _ _ n).trans
          ((biprod.lift_fst _ _).symm.trans (congrArg (· ≫ biprod.fst) (Category.comp_id _).symm)))
    · exact (congrArg (_ ≫ ·)
        (LocalCoefficientSystem.pairTwistedMayerVietorisToBiprod_snd _ _ _ n)).trans
        (((Preadditive.comp_neg _ _).trans
          (congrArg Neg.neg (rmap_comp_rmap hι _ _ _ _ _ _ _ n))).trans
          ((biprod.lift_snd _ _).symm.trans (congrArg (· ≫ biprod.snd) (Category.comp_id _).symm)))
  · apply biprod.hom_ext'
    · exact ((congrArg (biprod.inl ≫ ·) (Category.id_comp _)).trans
        (LocalCoefficientSystem.inl_pairTwistedMayerVietorisFromBiprod _ _ _ n)).trans
          ((biprod.inl_desc_assoc _ _ _).trans (rmap_comp_rmap hι _ _ _ _ _ _ _ n)).symm
    · exact ((congrArg (biprod.inr ≫ ·) (Category.id_comp _)).trans
        (LocalCoefficientSystem.inr_pairTwistedMayerVietorisFromBiprod _ _ _ n)).trans
          ((biprod.inr_desc_assoc _ _ _).trans (rmap_comp_rmap hι _ _ _ _ _ _ _ n)).symm

omit [FiniteDimensional ℝ F] in
private theorem mvShortComplex_exact {U V : Set B} (hU : IsOpen U) (hV : IsOpen V) (n : ℕ) :
    (mvShortComplex F E R hι U V n).Exact := by
  obtain ⟨hA, hB, hC, hD⟩ := isOpen_thomPairOver_mayerVietoris (F := F) (E := E) hU hV
  exact (ShortComplex.exact_iff_of_iso (mvShortComplexIso hι U V n)).2
    ((thomPairSignLocalSystem F E R hι).pairTwistedMayerVietoris_exact₂ _ _ hA hB hC hD n)

include ω in
/-- Over a subset of the base set of a chosen trivialization, the homology of the Thom pair with
coefficients in the pulled-back orientation system vanishes below the rank. -/
private theorem isZero_twistedHomology_thomPairOver (c : B) {W : Set B}
    (hW : W ⊆ (trivializationAt F E c).baseSet) {m : ℕ} (hm : m < finrank ℝ F) :
    IsZero ((thomPairOver F E W).twistedHomology (overSignLocalSystem F E R hι W) m) :=
  ((trivializationAt F E c).isZero_singularHomology_thomPairOver hW (ModuleCat.of R R) hm).of_iso
    ((HomologicalComplex.homologyFunctor _ _ m).mapIso
      ((thomPairOver F E W).twistedChainComplexCoefficientIso (baseSetSignIso hι c hW ω)) ≪≫
      (thomPairOver F E W).twistedHomologyConstantIso (ModuleCat.of R R) m)

omit [FiniteDimensional ℝ F] in
private theorem epi_mvShortComplex_g {U V : Set B} (hU : IsOpen U) (hV : IsOpen V) (n : ℕ)
    (hUV : ∀ m, m + 1 = n →
      IsZero ((thomPairOver F E (U ∩ V)).twistedHomology
        (overSignLocalSystem F E R hι (U ∩ V)) m)) :
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
        (m + 1) m).epi_f (((hUV m rfl).of_iso (rmapIso F E R hι _ _ (preimage_inter)
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
    IsZero ((thomPairOver F E ∅).twistedHomology (overSignLocalSystem F E R hι ∅)
      (finrank ℝ F)) :=
  have : IsEmpty (thomPairOver F E (∅ : Set B)).fst := ⟨fun v ↦ v.property⟩
  have : IsEmpty (thomPairOver F E (∅ : Set B)).snd := ⟨fun v ↦ v.property.1⟩
  (LocalCoefficientSystem.isZero_twistedHomology_of_isEmpty _ _).of_iso
    (asIso ((thomPairOver F E ∅).twistedHomologyπ _ _)).symm

/-! ### The Thom pair over a compact base -/

/-- The twisted homology of the Thom pair over the whole base, as a pair of subsets of the total
space, is that of the Thom pair `(E, E₀)`. -/
private def overUnivIso (n : ℕ) :
    (thomPairOver F E univ).twistedHomology (overSignLocalSystem F E R hι univ) n ≅
      (thomPair F E).twistedHomology (thomPairSignLocalSystem F E R hι) n :=
  have hmap : (ContinuousMap.subtypeVal (π F E ⁻¹' univ) :
      C((thomPairOver F E univ).fst, TotalSpace F E)) =
        (TopPair.Hom.fst (thomPairOverUnivIso F E).hom).hom :=
    ContinuousMap.ext fun v ↦ (thomPairOverUnivIso_hom_fst_apply F E v).symm
  have hiso : IsIso (TopPair.twistedHomologyMap (thomPairOverUnivIso F E).hom
      (thomPairSignLocalSystem F E R hι) n) :=
    (thomPairSignLocalSystem F E R hι).isIso_relativeTwistedHomologyMap_of_homotopyInverse
      (thomPairOverUnivIso F E).hom (thomPairOverUnivIso F E).inv
      (by rw [Iso.hom_inv_id]; exact ⟨TopPair.Homotopy.refl _⟩)
      (by rw [Iso.inv_hom_id]; exact ⟨TopPair.Homotopy.refl _⟩) n
  (HomologicalComplex.homologyFunctor _ _ n).mapIso
      ((thomPairOver F E univ).twistedChainComplexCoefficientIso
        (eqToIso (congrArg (fun g ↦ (LocalCoefficientSystem.pullback g).obj
          (thomPairSignLocalSystem F E R hι)) hmap))) ≪≫
    @asIso _ _ _ _ (TopPair.twistedHomologyMap (thomPairOverUnivIso F E).hom
      (thomPairSignLocalSystem F E R hι) n) hiso

private theorem isIso_toThomPairOver_univ [CompactSpace B] :
    IsIso (toThomPairOver F E R hι ω univ) := by
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun b : B ↦ (trivializationAt F E b).baseSet)
    (fun b ↦ (trivializationAt F E b).open_baseSet)
    (fun b _ ↦ mem_iUnion.2 ⟨b, FiberBundle.mem_baseSet_trivializationAt' b⟩)
  -- The Mayer–Vietoris induction over finite unions of open sets in the base sets of the chosen
  -- trivializations; the homology over `U ∩ V` vanishes in degree `r - 1` for such a `U`.
  have h := isIso_biUnion_of_mayerVietoris (fun h ↦ restr F E R hι h (finrank ℝ F))
    (toThomPairOver F E R hι ω) (toThomPairOver_naturality hι ω)
    (fun h h' ↦ restr_comp_restr hι h h' _) (fun W ↦ ∃ c, W ⊆ (trivializationAt F E c).baseSet)
    (fun h ⟨c, hc⟩ ↦ ⟨c, h.trans hc⟩)
    (fun _ ⟨c, hc⟩ ↦ isIso_toThomPairOver_of_subset hι ω c hc)
    (isZero_twistedHomology_thomPairOver_empty hι)
    (fun hU hV ↦ mvShortComplex_exact hι hU hV _)
    (fun hU hV ⟨c, hc⟩ ↦ epi_mvShortComplex_g hι hU hV _ fun _ hm ↦
      isZero_twistedHomology_thomPairOver hι ω c (inter_subset_left.trans hc) (by omega))
    s (W := fun b ↦ (trivializationAt F E b).baseSet)
    (fun b _ ↦ (trivializationAt F E b).open_baseSet) fun b _ ↦ ⟨b, subset_rfl⟩
  rwa [eq_univ_of_univ_subset hs] at h

variable (F E R) in
/-- The fibre class over `b` in the homology of the Thom pair with coefficients in the pulled-back
orientation system: the image of the class of the fibre pair `(E_b, E_b ∖ {0})` which a linear
trivialization at `b` reads as the class of the point, with the coefficients `o(E)_b` trivialized
by the orientation of `E_b` which this trivialization reads as `ω`. Reversing both readings
together does not change it, so it does not depend on the trivialization. -/
def thomPairSignFiberClass (b : B) :
    (thomPair F E).twistedHomology (thomPairSignLocalSystem F E R hι) (finrank ℝ F) :=
  (overUnivIso hι (finrank ℝ F)).hom (fiberClass F E R hι ω (mem_univ b))

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
    (@asIso _ _ _ _ (toThomPairOver F E R hι ω univ) (isIso_toThomPairOver_univ hι ω)).symm ≪≫
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} R) 0).obj
      (ModuleCat.of R R)).mapIso (TopCat.isoOfHomeo (Homeomorph.Set.univ B))

/-- The isomorphism `Hᵣ(E, E₀; π^*o(E)) ≅ H₀(B; R)` sends the fibre class over `b` to the class of
the point `b`. -/
@[simp]
theorem thomPairTwistedHomologyFinrankIso_hom_thomPairSignFiberClass [CompactSpace B] (b : B) :
    (thomPairTwistedHomologyFinrankIso F E R hι ω).hom (thomPairSignFiberClass F E R hι ω b) =
      singularHomology₀Section (ModuleCat.of R R) (X := TopCat.of B) b 1 := by
  have hb := ConcreteCategory.congr_hom
    (singularHomology₀Section_toThomPairOver (F := F) (E := E) (R := R) hι ω
      (⟨b, mem_univ b⟩ : (univ : Set B))) 1
  simp only [ConcreteCategory.comp_apply, ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply,
    one_smul] at hb
  simp only [thomPairTwistedHomologyFinrankIso, thomPairSignFiberClass, Iso.trans_hom,
    Iso.symm_hom, ConcreteCategory.comp_apply, Iso.hom_inv_id_apply, asIso_inv]
  rw [← hb, IsIso.hom_inv_id_apply, Functor.mapIso_hom, ← ConcreteCategory.comp_apply,
    singularHomology₀Section_naturality]
  simp only [TopCat.isoOfHomeo_hom, TopCat.hom_ofHom, ContinuousMap.coe_ofClass,
    Homeomorph.Set.univ_apply]

/-- Reversing the orientation `ω` of the model fibre negates the fibre classes. -/
theorem thomPairSignFiberClass_neg (b : B) :
    thomPairSignFiberClass F E R hι (-ω) b = -thomPairSignFiberClass F E R hι ω b := by
  have h : ((trivializationAt F E b).mapOrientation ι
      (FiberBundle.mem_baseSet_trivializationAt' b)).symm (-ω) =
      -((trivializationAt F E b).mapOrientation ι
        (FiberBundle.mem_baseSet_trivializationAt' b)).symm ω := by
    rw [Equiv.symm_apply_eq, Trivialization.mapOrientation_neg, Equiv.apply_symm_apply]
  rw [thomPairSignFiberClass, thomPairSignFiberClass, fiberClass, fiberClass, fiberClassAux,
    fiberClassAux, h, fiberSignIso_neg_inv, TopPair.twistedHomologyCoefficientMap_neg]
  simp only [ModuleCat.hom_neg, LinearMap.neg_apply, map_neg]

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

end FiberClass

end TauCeti
