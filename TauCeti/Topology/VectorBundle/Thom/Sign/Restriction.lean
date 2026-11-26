/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.MayerVietoris.Twisted
public import TauCeti.Topology.VectorBundle.MayerVietoris.TwistedDirectedUnion
public import TauCeti.Topology.VectorBundle.Thom.Sign.LocalSystem
import TauCeti.AlgebraicTopology.Singular.Twisted.Coefficients
import TauCeti.AlgebraicTopology.Singular.Twisted.ConstantNaturality

/-!
# Restrictions and local trivializations of the Thom-pair orientation system

Let `E → B` be a real vector bundle of rank `r` with Thom pair `(E, E₀)` and pulled-back
orientation local system `π^*o(E)` (`TauCeti.thomPairSignLocalSystem`). For any subset `W ⊆ B`,
its restriction `TauCeti.thomPairOverSignLocalSystem F E R hι W` to `(E|_W, E₀|_W)` admits two
compatible families of all-degree trivializations:

* On any single fibre `E_x` with `x ∈ W`, an orientation `o` of `E_x` trivializes the restricted
  system (`TauCeti.fiberThomPairOverSignLocalSystemIso`), obtained from
  `TauCeti.fiberThomPairSignLocalSystemIso` via the factorization `E_x ↪ E|_W ↪ E`.
* Over any subset `W ⊆ e.baseSet` of the base set of a linear trivialization `e`, a fixed
  orientation `ω` of the model fibre `F` trivializes the restricted system
  (`TauCeti.thomPairOverSignLocalSystemIso`) by evaluating at the orientations which `e` reads as
  `ω`.

## Main definitions and results

* `TauCeti.fiberThomPairOverSignLocalSystemIso`: fibrewise trivialization of `π^*o(E)|_{E|_W}` over
  `E_x` by an orientation `o`, with component evaluation lemmas
  (`TauCeti.fiberThomPairOverSignLocalSystemIso_hom_app_apply`,
  `TauCeti.fiberThomPairOverSignLocalSystemIso_inv_app`), sign law
  (`TauCeti.fiberThomPairOverSignLocalSystemIso_neg_inv`), and compatibility with
  `TopCat.restrictPreimagePairMap` and `TauCeti.thomPairOverMap`.
* `TauCeti.thomPairOverSignLocalSystemIso`: local trivialization of `π^*o(E)|_{E|_W}` over a subset
  `W` of the base set of a linear trivialization `e`, with component evaluation
  (`TauCeti.thomPairOverSignLocalSystemIso_hom_app_apply`), fibre restriction comparison
  (`TauCeti.pullback_map_thomPairOverSignLocalSystemIso_hom`), and all-degree homology comparison
  (`TauCeti.fiberThomPairOverSign_comp_twistedHomologyMap_comp_iso`).
-/

public section

noncomputable section

open CategoryTheory Bundle Module Set Topology
open TauCeti.LocalCoefficientSystem (constantFunctor)
open TauCeti.VectorBundleOrientationCover (signLocalSystem)

universe w

namespace TauCeti

variable {B : Type w} [TopologicalSpace B] {F : Type w}
  [NormedAddCommGroup F] [NormedSpace ℝ F] {E : B → Type w}
  [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E] {ι : Type} [Fintype ι]
  {R : Type w} [Ring R] (hι : Fintype.card ι = finrank ℝ F)

/-! ### Fibrewise trivializations over subsets of the base -/

variable (F E R) in
/-- The trivialization of the pulled-back orientation system over the fibre `E_x` in `E|_W` by an
orientation `o` of `E_x`, obtained from `TauCeti.fiberThomPairSignLocalSystemIso` via the
factorization `E_x ↪ E|_W ↪ E`. -/
def fiberThomPairOverSignLocalSystemIso {W : Set B} {x : B} (hx : x ∈ W)
    (o : Orientation ℝ (E x) ι) :
    (LocalCoefficientSystem.pullback (TopPair.Hom.fst (fiberThomPairOverMap F E hx)).hom).obj
        (thomPairOverSignLocalSystem F E R hι W) ≅
      (constantFunctor _).obj (ModuleCat.of R R) :=
  (LocalCoefficientSystem.pullback (TopPair.Hom.fst (fiberThomPairOverMap F E hx)).hom).mapIso
      (eqToIso (TopPair.pullback_subtypeVal_eq_pullback_restrictPreimagePairMap
        (X := TopCat.of (TotalSpace F E)) (zeroSectionCompl F E)
        (thomPairSignLocalSystem F E R hι) (π F E) W)) ≪≫
    (TopPair.fstPullbackCompIso (fiberThomPairOverMap F E hx)
      (TopCat.restrictPreimagePairMap (X := TopCat.of (TotalSpace F E)) (π F E)
        (zeroSectionCompl F E) W) (thomPairSignLocalSystem F E R hι)).symm ≪≫
    eqToIso (congrArg (fun g ↦ (LocalCoefficientSystem.pullback (TopPair.Hom.fst g).hom).obj
      (thomPairSignLocalSystem F E R hι))
      (fiberThomPairOverMap_comp_restrictPreimagePairMap F E hx)) ≪≫
    fiberThomPairSignLocalSystemIso F E R hι x o

/-- Component formula for the inverse of `TauCeti.fiberThomPairOverSignLocalSystemIso`: on each
fibre point `v`, it is the inverse of `TauCeti.fiberThomPairSignLocalSystemIso` followed by the
equality transport between the pulled-back fibres over `E_x ↪ E` and `E_x ↪ E|_W ↪ E`. -/
theorem fiberThomPairOverSignLocalSystemIso_inv_app {W : Set B} {x : B} (hx : x ∈ W)
    (o : Orientation ℝ (E x) ι)
    (v : FundamentalGroupoid (TopPair.ofSubset (X := TopCat.of (E x)) ({0}ᶜ : Set (E x))).fst) :
    (fiberThomPairOverSignLocalSystemIso F E R hι hx o).inv.app v =
      (fiberThomPairSignLocalSystemIso F E R hι x o).inv.app v ≫
        eqToHom (by
          -- Both sides evaluate `thomPairSignLocalSystem` at `⟨x, v.as⟩`.
          have h₁ := congrArg (fun L ↦ L.obj v)
            (congrArg (fun g ↦ (LocalCoefficientSystem.pullback (TopPair.Hom.fst g).hom).obj
              (thomPairSignLocalSystem F E R hι))
              (fiberThomPairOverMap_comp_restrictPreimagePairMap F E hx))
          have h₂ := congrArg (fun L ↦ L.obj v)
            (congrArg (LocalCoefficientSystem.pullback
              (TopPair.Hom.fst (fiberThomPairOverMap F E hx)).hom).obj
              (TopPair.pullback_subtypeVal_eq_pullback_restrictPreimagePairMap
                (X := TopCat.of (TotalSpace F E)) (zeroSectionCompl F E)
                (thomPairSignLocalSystem F E R hι) (π F E) W))
          exact h₁.symm.trans h₂.symm) := by
  unfold fiberThomPairOverSignLocalSystemIso
  -- `erw`: unfold the three transport prefix isomorphisms of `fiberThomPairOverSignLocalSystemIso`.
  erw [Iso.trans_inv, Iso.trans_inv, Iso.trans_inv, Category.assoc, Category.assoc,
    NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app, Functor.mapIso_inv, eqToIso.inv,
    eqToIso.inv, Iso.symm_inv, TopPair.fstPullbackCompIso_hom_app, Category.id_comp,
    LocalCoefficientSystem.pullback_map_app, eqToHom_app, eqToHom_app, eqToHom_trans]

/-- Evaluating `TauCeti.fiberThomPairOverSignLocalSystemIso` at a point `v` of the fibre pair
evaluates the fibre of `o(E)` at `o` after transporting to the fibre over `π (fiberThomPairMap v)`.
-/
@[simp]
theorem fiberThomPairOverSignLocalSystemIso_hom_app_apply {W : Set B} {x : B} (hx : x ∈ W)
    (o : Orientation ℝ (E x) ι)
    (v : FundamentalGroupoid (TopPair.ofSubset (X := TopCat.of (E x)) ({0}ᶜ : Set (E x))).fst)
    (f : (thomPairOverSignLocalSystem F E R hι W).obj
      ((FundamentalGroupoid.map (TopPair.Hom.fst (fiberThomPairOverMap F E hx)).hom).obj v)) :
    (ConcreteCategory.hom
        (X := (thomPairOverSignLocalSystem F E R hι W).obj
          ((FundamentalGroupoid.map (TopPair.Hom.fst (fiberThomPairOverMap F E hx)).hom).obj v))
        (Y := ModuleCat.of R R)
        ((fiberThomPairOverSignLocalSystemIso F E R hι hx o).hom.app v)) f =
      VectorBundleOrientationCover.liftFiberEquiv hι ⟨x, o⟩
        (congrArg TotalSpace.proj (fiberThomPairMap_fst_apply F E x v.as)).symm
        ((eqToHom (X := (thomPairOverSignLocalSystem F E R hι W).obj
            ((FundamentalGroupoid.map (TopPair.Hom.fst (fiberThomPairOverMap F E hx)).hom).obj v))
          (Y := (signLocalSystem F E R hι).obj
            (FundamentalGroupoid.mk (TopPair.Hom.fst (fiberThomPairMap F E x) v.as).proj))
          (by
            have h₁ := congrArg (fun L ↦ L.obj v)
              (congrArg (LocalCoefficientSystem.pullback
                (TopPair.Hom.fst (fiberThomPairOverMap F E hx)).hom).obj
                (TopPair.pullback_subtypeVal_eq_pullback_restrictPreimagePairMap
                  (X := TopCat.of (TotalSpace F E)) (zeroSectionCompl F E)
                  (thomPairSignLocalSystem F E R hι) (π F E) W))
            have h₂ := congrArg (fun L ↦ L.obj v)
              (congrArg (fun g ↦ (LocalCoefficientSystem.pullback (TopPair.Hom.fst g).hom).obj
                (thomPairSignLocalSystem F E R hι))
                (fiberThomPairOverMap_comp_restrictPreimagePairMap F E hx))
            have h₃ := congrArg (fun L ↦ ((LocalCoefficientSystem.pullback
                (TopPair.Hom.fst (fiberThomPairMap F E x)).hom).obj L).obj v)
              (thomPairSignLocalSystem_def (F := F) (E := E) (R := R) hι)
            exact h₁.trans (h₂.trans h₃))) f) := by
  unfold fiberThomPairOverSignLocalSystemIso
  -- `erw`: evaluate the prefixes via `fiberThomPairSignLocalSystemIso_hom_app_apply`.
  erw [Iso.trans_hom, Iso.trans_hom, Iso.trans_hom, NatTrans.comp_app, NatTrans.comp_app,
    NatTrans.comp_app, Functor.mapIso_hom, eqToIso.hom, eqToIso.hom, Iso.symm_hom,
    TopPair.fstPullbackCompIso_inv_app, LocalCoefficientSystem.pullback_map_app, eqToHom_app,
    eqToHom_app, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, ConcreteCategory.id_apply,
    fiberThomPairSignLocalSystemIso_hom_app_apply, LocalCoefficientSystem.pullback_map_app,
    eqToHom_app, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, eqToHom_trans,
    eqToHom_trans]
  -- Both sides apply `liftFiberEquiv` to the same transported fibre element.
  rfl

/-- Reversing the orientation negates the inverse of `TauCeti.fiberThomPairOverSignLocalSystemIso`.
-/
@[simp]
theorem fiberThomPairOverSignLocalSystemIso_neg_inv {W : Set B} {x : B} (hx : x ∈ W)
    (o : Orientation ℝ (E x) ι) :
    (fiberThomPairOverSignLocalSystemIso F E R hι hx (-o)).inv =
      -(fiberThomPairOverSignLocalSystemIso F E R hι hx o).inv := by
  ext v : 2
  -- `(-α).app v` is `-(α.app v)` by definition in the functor category.
  change (fiberThomPairOverSignLocalSystemIso F E R hι hx (-o)).inv.app v =
    -(fiberThomPairOverSignLocalSystemIso F E R hι hx o).inv.app v
  rw [fiberThomPairOverSignLocalSystemIso_inv_app, fiberThomPairOverSignLocalSystemIso_inv_app,
    fiberThomPairSignLocalSystemIso_neg_inv]
  exact Preadditive.neg_comp _ _

/-- On the fibre pair over `x`, the trivialization by `o` of the orientation system over `W`,
carried to the Thom pair along `TopCat.restrictPreimagePairMap`, is
`TauCeti.fiberThomPairSignLocalSystemIso`. -/
theorem fiberThomPairOverSignLocalSystemIso_inv_comp_eqToHom {W : Set B} {x : B} (hx : x ∈ W)
    (o : Orientation ℝ (E x) ι) :
    ((fiberThomPairOverSignLocalSystemIso F E R hι hx o).inv ≫
      (LocalCoefficientSystem.pullback (TopPair.Hom.fst (fiberThomPairOverMap F E hx)).hom).map
        (eqToHom (TopPair.pullback_subtypeVal_eq_pullback_restrictPreimagePairMap
          (X := TopCat.of (TotalSpace F E)) (zeroSectionCompl F E)
          (thomPairSignLocalSystem F E R hι) (π F E) W))) ≫
      (TopPair.fstPullbackCompIso (fiberThomPairOverMap F E hx)
        (TopCat.restrictPreimagePairMap (X := TopCat.of (TotalSpace F E)) (π F E)
          (zeroSectionCompl F E) W) (thomPairSignLocalSystem F E R hι)).inv ≫
      eqToHom (congrArg (fun g ↦ (LocalCoefficientSystem.pullback (TopPair.Hom.fst g).hom).obj
        (thomPairSignLocalSystem F E R hι))
        (fiberThomPairOverMap_comp_restrictPreimagePairMap F E hx)) =
    (fiberThomPairSignLocalSystemIso F E R hι x o).inv := by
  unfold fiberThomPairOverSignLocalSystemIso
  -- `erw`: cancel the three prefix isomorphisms of `fiberThomPairOverSignLocalSystemIso`.
  erw [Iso.trans_inv, Iso.trans_inv, Iso.trans_inv, Category.assoc, Category.assoc, Category.assoc,
    Functor.mapIso_inv, eqToIso.inv, eqToIso.inv, ← Functor.map_comp_assoc, eqToHom_trans,
    eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp, Iso.symm_inv,
    Iso.hom_inv_id_assoc, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- On the fibre pair over `x ∈ W ⊆ W'`, transporting
`TauCeti.fiberThomPairOverSignLocalSystemIso` along `TauCeti.thomPairOverMap` recovers
`TauCeti.fiberThomPairOverSignLocalSystemIso` over `W'`. -/
theorem fiberThomPairOverSignLocalSystemIso_inv_comp_thomPairOverMap {W W' : Set B} (h : W ⊆ W')
    {x : B} (hxW : x ∈ W) (o : Orientation ℝ (E x) ι) :
    ((fiberThomPairOverSignLocalSystemIso F E R hι hxW o).inv ≫
      (LocalCoefficientSystem.pullback (TopPair.Hom.fst (fiberThomPairOverMap F E hxW)).hom).map
        ((LocalCoefficientSystem.pullbackCompIso
            (TopCat.ofHom (ContinuousMap.inclusion (preimage_mono h))).hom
            (TopCat.ofHom (ContinuousMap.subtypeVal (π F E ⁻¹' W'))).hom).hom.app
            (thomPairSignLocalSystem F E R hι) ≫
          eqToHom (congrArg (fun g : (thomPairOver F E W).fst ⟶ (thomPairOver F E W').fst ↦
            (LocalCoefficientSystem.pullback g.hom).obj
              ((LocalCoefficientSystem.pullback
                (TopCat.ofHom (ContinuousMap.subtypeVal (π F E ⁻¹' W'))).hom).obj
                (thomPairSignLocalSystem F E R hι)))
            (thomPairOverMap_fst F E h).symm))) ≫
      (TopPair.fstPullbackCompIso (fiberThomPairOverMap F E hxW) (thomPairOverMap F E h)
        (thomPairOverSignLocalSystem F E R hι W')).inv ≫
      eqToHom (congrArg (fun g ↦ (LocalCoefficientSystem.pullback (TopPair.Hom.fst g).hom).obj
        (thomPairOverSignLocalSystem F E R hι W'))
        (fiberThomPairOverMap_comp_thomPairOverMap F E h hxW)) =
      (fiberThomPairOverSignLocalSystemIso F E R hι (h hxW) o).inv := by
  ext v : 2
  simp only [NatTrans.comp_app, fiberThomPairOverSignLocalSystemIso_inv_app,
    LocalCoefficientSystem.pullback_map_app, TopPair.fstPullbackCompIso_inv_app, eqToHom_app,
    Category.assoc]
  -- `erw`: collapse `pullbackCompIso` and the remaining `eqToHom` transports across `TopPair.fst`.
  erw [NatTrans.comp_app, LocalCoefficientSystem.pullbackCompIso_hom_app_app, eqToHom_app,
    Category.id_comp, Category.id_comp, eqToHom_trans, eqToHom_trans]

/-- Through the identification of the pair over the whole base with the Thom pair, the fibre
inclusion into the pair over the whole base, with the coefficients trivialized by `o`, is the fibre
inclusion into the Thom pair, with the coefficients trivialized by `o`. -/
theorem twistedHomologyCoefficientMap_fiberThomPairOverSignLocalSystemIso_inv_comp_overUnivIso_hom
    (x : B) (o : Orientation ℝ (E x) ι) (n : ℕ) :
    (TopPair.ofSubset (X := TopCat.of (E x)) ({0}ᶜ : Set (E x))).twistedHomologyCoefficientMap
        (fiberThomPairOverSignLocalSystemIso F E R hι (mem_univ x) o).inv n ≫
      TopPair.twistedHomologyMap (fiberThomPairOverMap F E (mem_univ x))
        (thomPairOverSignLocalSystem F E R hι univ) n ≫
      (thomPairOverTwistedHomologyUnivIso (thomPairSignLocalSystem F E R hι) n).hom =
    (TopPair.ofSubset (X := TopCat.of (E x)) ({0}ᶜ : Set (E x))).twistedHomologyCoefficientMap
        (fiberThomPairSignLocalSystemIso F E R hι x o).inv n ≫
      TopPair.twistedHomologyMap (fiberThomPairMap F E x) (thomPairSignLocalSystem F E R hι) n := by
  rw [thomPairOverTwistedHomologyUnivIso_hom, TopPair.twistedHomologyMap_naturality_assoc,
    TopPair.twistedHomologyMap_comp_of_comp_eq (fiberThomPairOverMap F E (mem_univ x))
      (TopCat.restrictPreimagePairMap (X := TopCat.of (TotalSpace F E)) (π F E)
        (zeroSectionCompl F E) univ) (thomPairSignLocalSystem F E R hι)
      (fiberThomPairOverMap_comp_restrictPreimagePairMap F E (mem_univ x)),
    ← TopPair.twistedHomologyCoefficientMap_comp_assoc,
    ← TopPair.twistedHomologyCoefficientMap_comp_assoc]
  congr 2
  exact fiberThomPairOverSignLocalSystemIso_inv_comp_eqToHom hι (mem_univ x) o

/-! ### Local trivializations over a subset of a trivializing base set -/

variable (F E R) in
/-- Over a subset `W` of the base set of a linear trivialization `e`, the pulled-back orientation
system is trivialized by evaluating at the orientation read as `ω` by `e`. -/
def thomPairOverSignLocalSystemIso (e : Trivialization F (π F E)) [e.IsLinear ℝ] {W : Set B}
    (hW : W ⊆ e.baseSet) (ω : Orientation ℝ F ι) :
    thomPairOverSignLocalSystem F E R hι W ≅
      (constantFunctor _).obj (ModuleCat.of R R) :=
  (LocalCoefficientSystem.pullback (X := TopCat.of ↥(π F E ⁻¹' W))
      (ContinuousMap.subtypeVal (π F E ⁻¹' W))).mapIso
      (eqToIso (thomPairSignLocalSystem_def hι)) ≪≫
    ((LocalCoefficientSystem.pullbackCompIso (X := (thomPairOver F E W).fst)
      (Y := TopCat.of (TotalSpace F E)) (Z := TopCat.of B)
      (ContinuousMap.subtypeVal (π F E ⁻¹' W))
      ⟨π F E, FiberBundle.continuous_proj F E⟩).app (signLocalSystem F E R hι)).symm ≪≫
    VectorBundleOrientationCover.pullbackSignLocalSystemIso R hι e ω
      (Y := (thomPairOver F E W).fst)
      ((⟨π F E, FiberBundle.continuous_proj F E⟩ : C(TotalSpace F E, B)).comp
        (ContinuousMap.subtypeVal (π F E ⁻¹' W)))
      fun v ↦ hW v.property

/-- Evaluating `TauCeti.thomPairOverSignLocalSystemIso` at a point `v` of `E|_W` evaluates the
fibre of `o(E)` over `π v` at the orientation which `e` reads as `ω`. -/
@[simp]
theorem thomPairOverSignLocalSystemIso_hom_app_apply (e : Trivialization F (π F E)) [e.IsLinear ℝ]
    {W : Set B} (hW : W ⊆ e.baseSet) (ω : Orientation ℝ F ι)
    (v : FundamentalGroupoid (thomPairOver F E W).fst)
    (f : (thomPairOverSignLocalSystem F E R hι W).obj v) :
    (ConcreteCategory.hom (Y := ModuleCat.of R R)
        ((thomPairOverSignLocalSystemIso F E R hι e hW ω).hom.app v)) f =
      VectorBundleOrientationCover.signLocalSystemFiberEquiv hι
        ((e.mapOrientation ι (hW v.as.property)).symm ω)
        (eqToHom (congrArg (fun L ↦ ((LocalCoefficientSystem.pullback
            (X := TopCat.of ↥(π F E ⁻¹' W))
            (ContinuousMap.subtypeVal (π F E ⁻¹' W))).obj L).obj v)
          (thomPairSignLocalSystem_def (F := F) (E := E) (R := R) hι)) f) := by
  unfold thomPairOverSignLocalSystemIso
  -- `erw`: unfold the two prefix transports and apply `pullbackSignLocalSystemIso_hom_app_apply`.
  erw [Iso.trans_hom, Iso.trans_hom, NatTrans.comp_app, NatTrans.comp_app, Functor.mapIso_hom,
    eqToIso.hom, Iso.symm_hom, Iso.app_inv, LocalCoefficientSystem.pullbackCompIso_inv_app_app,
    LocalCoefficientSystem.pullback_map_app, eqToHom_app, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, ConcreteCategory.id_apply,
    VectorBundleOrientationCover.pullbackSignLocalSystemIso_hom_app_apply]
  -- Both sides apply `signLocalSystemFiberEquiv` to the same transported fibre element.
  rfl

/-- The trivialization over the base set, restricted to a fibre, is the trivialization of the
fibre by the orientation it reads as `ω`. -/
theorem pullback_map_thomPairOverSignLocalSystemIso_hom (e : Trivialization F (π F E))
    [e.IsLinear ℝ] {W : Set B} (hW : W ⊆ e.baseSet) (ω : Orientation ℝ F ι) {x : B}
    (hxW : x ∈ W) :
    (LocalCoefficientSystem.pullback (TopPair.Hom.fst (fiberThomPairOverMap F E hxW)).hom).map
        (thomPairOverSignLocalSystemIso F E R hι e hW ω).hom ≫
      (LocalCoefficientSystem.pullbackConstantIso _ (ModuleCat.of R R)).hom =
    (fiberThomPairOverSignLocalSystemIso F E R hι hxW
      ((e.mapOrientation ι (hW hxW)).symm ω)).hom := by
  ext v : 2
  refine ModuleCat.hom_ext (LinearMap.ext fun f ↦ ?_)
  have hbL : (TopPair.Hom.fst (fiberThomPairOverMap F E hxW) v.as).val.proj = x :=
    congrArg (fun p : ↥(π F E ⁻¹' W) ↦ p.val.proj) (fiberThomPairOverMap_fst_apply F E hxW v.as)
  have hbR : (TopPair.Hom.fst (fiberThomPairMap F E x) v.as).proj = x :=
    congrArg TotalSpace.proj (fiberThomPairMap_fst_apply F E x v.as)
  have hcover : ∀ {b b' : B} (_ : b = b') (h₁ : b ∈ e.baseSet) (h₂ : b' ∈ e.baseSet),
      (⟨b, (e.mapOrientation ι h₁).symm ω⟩ : VectorBundleOrientationCover F E ι) =
        ⟨b', (e.mapOrientation ι h₂).symm ω⟩ := fun hb _ _ ↦ by subst hb; rfl
  have hfib : ∀ {b : B} (o : Orientation ℝ (E b) ι) (z),
      VectorBundleOrientationCover.signLocalSystemFiberEquiv (R := R) hι o z =
        VectorBundleOrientationCover.liftFiberEquiv (R := R) hι ⟨b, o⟩ rfl z := fun o z ↦ by
    rw [VectorBundleOrientationCover.signLocalSystemFiberEquiv_apply,
      VectorBundleOrientationCover.liftFiberEquiv_apply]
  -- Normalize both sides using the component evaluation lemmas for the two trivializations.
  simp only [NatTrans.comp_app, LocalCoefficientSystem.pullbackConstantIso_hom_app,
    LocalCoefficientSystem.pullback_map_app]
  erw [Category.comp_id, thomPairOverSignLocalSystemIso_hom_app_apply,
    fiberThomPairOverSignLocalSystemIso_hom_app_apply, hfib]
  refine (VectorBundleOrientationCover.liftFiberEquiv_eqToHom_apply (R := R) hι
    (hbL.trans hbR.symm)
    (congrArg (fun b ↦ (signLocalSystem F E R hι).obj (FundamentalGroupoid.mk b))
      (hbL.trans hbR.symm))
    (hcover hbL (hW (TopPair.Hom.fst (fiberThomPairOverMap F E hxW) v.as).property) (hW hxW))
    rfl hbR.symm _).symm.trans ?_
  -- `erw`: merge the two `eqToHom` transports into the single `eqToHom` on the right-hand side.
  erw [← ConcreteCategory.comp_apply, eqToHom_trans]

/-- Over a subset of the base set of a linear trivialization `e`, the fibre inclusion over `x`,
read through the trivializations of the coefficient systems by the orientation that `e` reads as
`ω`, is the fibre inclusion in ordinary homology. -/
@[reassoc]
theorem fiberThomPairOverSign_comp_twistedHomologyMap_comp_iso (e : Trivialization F (π F E))
    [e.IsLinear ℝ] {W : Set B} (hW : W ⊆ e.baseSet) (ω : Orientation ℝ F ι) {x : B}
    (hxW : x ∈ W) (n : ℕ) :
    ((TopPair.ofSubset (X := TopCat.of (E x)) ({0}ᶜ : Set (E x))).twistedHomologyConstantIso
        (ModuleCat.of R R) n).inv ≫
      (TopPair.ofSubset (X := TopCat.of (E x)) ({0}ᶜ : Set (E x))).twistedHomologyCoefficientMap
        (fiberThomPairOverSignLocalSystemIso F E R hι hxW
          ((e.mapOrientation ι (hW hxW)).symm ω)).inv n ≫
      TopPair.twistedHomologyMap (fiberThomPairOverMap F E hxW)
        (thomPairOverSignLocalSystem F E R hι W) n ≫
      (thomPairOver F E W).twistedHomologyCoefficientMap
        (thomPairOverSignLocalSystemIso F E R hι e hW ω).hom n ≫
      ((thomPairOver F E W).twistedHomologyConstantIso (ModuleCat.of R R) n).hom =
    TopPair.singularHomologyMap (fiberThomPairOverMap F E hxW) (ModuleCat.of R R) n := by
  -- Move the change of coefficients over `W` past the fibre inclusion, then compare the two
  -- trivializations of the coefficients on the fibre.
  rw [TopPair.twistedHomologyMap_naturality_assoc,
    TopPair.twistedHomologyConstantIso_hom_pair_naturality,
    ← TopPair.twistedHomologyCoefficientMap_comp_assoc,
    ← TopPair.twistedHomologyCoefficientMap_comp_assoc, Category.assoc,
    pullback_map_thomPairOverSignLocalSystemIso_hom, Iso.inv_hom_id,
    TopPair.twistedHomologyCoefficientMap_id, Category.id_comp, Iso.inv_hom_id_assoc]

end TauCeti
