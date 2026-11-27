/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.Functoriality
public import TauCeti.Topology.VectorBundle.EulerClass
public import TauCeti.Topology.VectorBundle.Orientation.LocalSystem
import TauCeti.AlgebraicTopology.Singular.Twisted.Coefficients

/-!
# The orientation local system on the Thom pair and its fibre trivializations

Let `E → B` be a real vector bundle of rank `r` with Thom pair `(E, E₀)`, `E₀` the complement of
the zero section, and let `R` be a ring. Pulling back the orientation local system `o(E)`
(`TauCeti.VectorBundleOrientationCover.signLocalSystem`) along the bundle projection `π` gives the
local coefficient system `π^*o(E)` on the total space (`TauCeti.thomPairSignLocalSystem`), whose
fibres are projective (`TauCeti.projective_thomPairSignLocalSystem_obj`), and its restriction to
`E|_W` for any `W : Set B` (`TauCeti.thomPairOverSignLocalSystem`).

Over a single fibre `E_b`, the projection to `B` is constant at `b`, so any orientation `o` of
`E_b` provides a constant lift to the orientation double cover and hence a canonical trivialization
of `π^*o(E)` restricted to the fibre pair `(E_b, E_b ∖ {0})`
(`TauCeti.fiberThomPairSignLocalSystemIso`). Composing its inverse with the fibre inclusion yields,
in every degree `n`, the map
`Hₙ(E_b, E_b ∖ {0}; R) ⟶ Hₙ(E, E₀; π^*o(E))` (`TauCeti.thomPairSignFiberMap`); reversing `o`
negates both the trivialization and the induced map
(`TauCeti.fiberThomPairSignLocalSystemIso_neg_inv`, `TauCeti.thomPairSignFiberMap_neg`).

## Main definitions and results

* `TauCeti.thomPairSignLocalSystem`: the orientation local system pulled back to the total space.
* `TauCeti.projective_thomPairSignLocalSystem_obj`: every fibre of `π^*o(E)` is projective.
* `TauCeti.thomPairOverSignLocalSystem`: the restriction of `π^*o(E)` to `E|_W`.
* `TauCeti.fiberThomPairSignLocalSystemIso`: the trivialization of `π^*o(E)` over the fibre pair
  `(E_b, E_b ∖ {0})` induced by an orientation `o` of `E_b`, with its forward and inverse
  evaluation lemmas (`TauCeti.fiberThomPairSignLocalSystemIso_hom_app_apply`,
  `TauCeti.liftFiberEquiv_fiberThomPairSignLocalSystemIso_inv_app_apply`) and sign law
  (`TauCeti.fiberThomPairSignLocalSystemIso_neg_inv`).
* `TauCeti.thomPairSignFiberMap`: the all-degree map `Hₙ(E_b, E_b ∖ {0}; R) ⟶ Hₙ(E, E₀; π^*o(E))`
  determined by an orientation `o` of `E_b`, with sign law `TauCeti.thomPairSignFiberMap_neg`.
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

/-! ### The orientation system on the total space -/

variable (F E R) in
/-- The orientation local system `o(E)` of a real vector bundle, pulled back to its total space
along the projection: its fibre over a vector `v` is the fibre of `o(E)` over `π v`. -/
def thomPairSignLocalSystem : LocalCoefficientSystem R (TopCat.of (TotalSpace F E)) :=
  (LocalCoefficientSystem.pullback (X := TopCat.of (TotalSpace F E)) (Y := TopCat.of B)
    ⟨π F E, FiberBundle.continuous_proj F E⟩).obj
      (signLocalSystem F E R hι)

/-- Unfolding lemma for `TauCeti.thomPairSignLocalSystem`. -/
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
abbrev thomPairOverSignLocalSystem (W : Set B) :
    LocalCoefficientSystem R (thomPairOver F E W).fst :=
  (LocalCoefficientSystem.pullback (X := TopCat.of ↥(π F E ⁻¹' W))
    (ContinuousMap.subtypeVal (π F E ⁻¹' W))).obj (thomPairSignLocalSystem F E R hι)

/-! ### Fibre trivializations and the all-degree fibre map -/

omit [Fintype ι] in
/-- The constant lift `⟨b, o⟩` lies over the projection of the fibre over `b`. -/
private theorem proj_const_eq_proj_fiberThomPairMap (b : B) (o : Orientation ℝ (E b) ι)
    (x : (TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).fst) :
    (ContinuousMap.const _ (⟨b, o⟩ : VectorBundleOrientationCover F E ι) x).proj =
      ((⟨π F E, FiberBundle.continuous_proj F E⟩ : C(TotalSpace F E, B)).comp
        (TopPair.Hom.fst (fiberThomPairMap F E b)).hom) x :=
  (congrArg TotalSpace.proj (fiberThomPairMap_fst_apply F E b x)).symm

variable (F E R) in
/-- Over the fibre pair `(E_b, E_b ∖ {0})`, an orientation `o` of `E_b` trivializes `π^*o(E)` by
evaluating at `o`: the bundle projection is constant at `b` on the fibre, so `o` defines a constant
lift into the orientation double cover. -/
def fiberThomPairSignLocalSystemIso (b : B) (o : Orientation ℝ (E b) ι) :
    (LocalCoefficientSystem.pullback (TopPair.Hom.fst (fiberThomPairMap F E b)).hom).obj
        (thomPairSignLocalSystem F E R hι) ≅
      (constantFunctor _).obj (ModuleCat.of R R) :=
  (LocalCoefficientSystem.pullback (TopPair.Hom.fst (fiberThomPairMap F E b)).hom).mapIso
      (eqToIso (thomPairSignLocalSystem_def hι)) ≪≫
    ((LocalCoefficientSystem.pullbackCompIso
      (Y := TopCat.of (TotalSpace F E)) (Z := TopCat.of B)
      (TopPair.Hom.fst (fiberThomPairMap F E b)).hom
      (⟨π F E, FiberBundle.continuous_proj F E⟩ : C(TotalSpace F E, B))).app
      (signLocalSystem F E R hι)).symm ≪≫
    VectorBundleOrientationCover.pullbackSignLocalSystemIsoOfLift R hι
      ((⟨π F E, FiberBundle.continuous_proj F E⟩ : C(TotalSpace F E, B)).comp
        (TopPair.Hom.fst (fiberThomPairMap F E b)).hom)
      (ContinuousMap.const _ ⟨b, o⟩) (proj_const_eq_proj_fiberThomPairMap b o)

/-- Evaluating `TauCeti.fiberThomPairSignLocalSystemIso` at a point `v` of the fibre pair evaluates
the fibre of `o(E)` at the orientation `o` (after rewriting along
`TauCeti.thomPairSignLocalSystem_def`). -/
@[simp]
theorem fiberThomPairSignLocalSystemIso_hom_app_apply (b : B) (o : Orientation ℝ (E b) ι)
    (v : FundamentalGroupoid
      (TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).fst)
    (f : ((LocalCoefficientSystem.pullback (TopPair.Hom.fst (fiberThomPairMap F E b)).hom).obj
      (thomPairSignLocalSystem F E R hι)).obj v) :
    (ConcreteCategory.hom (Y := ModuleCat.of R R)
        ((fiberThomPairSignLocalSystemIso F E R hι b o).hom.app v)) f =
      VectorBundleOrientationCover.liftFiberEquiv hι ⟨b, o⟩
        (congrArg TotalSpace.proj (fiberThomPairMap_fst_apply F E b v.as)).symm
        (((LocalCoefficientSystem.pullback (TopPair.Hom.fst (fiberThomPairMap F E b)).hom).map
          (eqToHom (thomPairSignLocalSystem_def (F := F) (E := E) (R := R) hι))).app v f) := by
  unfold fiberThomPairSignLocalSystemIso
  -- `erw`: unfold the components of the composite natural isomorphism across `pullback`.
  erw [Iso.trans_hom, Iso.trans_hom, NatTrans.comp_app, NatTrans.comp_app, Functor.mapIso_hom,
    eqToIso.hom, Iso.symm_hom, Iso.app_inv, LocalCoefficientSystem.pullbackCompIso_inv_app_app,
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ConcreteCategory.id_apply,
    VectorBundleOrientationCover.pullbackSignLocalSystemIsoOfLift_hom_app_apply]
  exact (VectorBundleOrientationCover.liftFiberEquiv_apply (R := R) hι _ _ _).symm

/-- Reversing the orientation of `E_b` negates the inverse of the fibre trivialization
`TauCeti.fiberThomPairSignLocalSystemIso`. -/
@[simp]
theorem fiberThomPairSignLocalSystemIso_neg_inv (b : B) (o : Orientation ℝ (E b) ι) :
    (fiberThomPairSignLocalSystemIso F E R hι b (-o)).inv =
      -(fiberThomPairSignLocalSystemIso F E R hι b o).inv := by
  unfold fiberThomPairSignLocalSystemIso
  -- `erw`: `(thomPair F E).fst` matches `TopCat.of (TotalSpace F E)` after unfolding `thomPair`.
  erw [Iso.trans_inv, Iso.trans_inv, Iso.trans_inv, Iso.trans_inv,
    VectorBundleOrientationCover.pullbackSignLocalSystemIsoOfLift_inv_of_eq_deck hι _
      (proj_const_eq_proj_fiberThomPairMap b o) (proj_const_eq_proj_fiberThomPairMap b (-o))
      (fun _ ↦ (VectorBundleOrientationCover.deck_apply ⟨b, o⟩).symm),
    Preadditive.neg_comp, Preadditive.neg_comp]

/-- Evaluating the inverse of `TauCeti.fiberThomPairSignLocalSystemIso` at the orientation `o`
recovers the scalar `r`. -/
theorem liftFiberEquiv_fiberThomPairSignLocalSystemIso_inv_app_apply (x : B)
    (o : Orientation ℝ (E x) ι)
    (v : FundamentalGroupoid (TopPair.ofSubset (X := TopCat.of (E x)) ({0}ᶜ : Set (E x))).fst)
    (r : R) :
    VectorBundleOrientationCover.liftFiberEquiv hι ⟨x, o⟩
        (congrArg TotalSpace.proj (fiberThomPairMap_fst_apply F E x v.as)).symm
        (((LocalCoefficientSystem.pullback (TopPair.Hom.fst (fiberThomPairMap F E x)).hom).map
          (eqToHom (thomPairSignLocalSystem_def (F := F) (E := E) (R := R) hι))).app v
          ((fiberThomPairSignLocalSystemIso F E R hι x o).inv.app v r)) = r := by
  -- `erw`: `(thomPair F E).fst` matches `TopCat.of (TotalSpace F E)` after unfolding `thomPair`.
  erw [← fiberThomPairSignLocalSystemIso_hom_app_apply, ← ConcreteCategory.comp_apply,
    ← NatTrans.comp_app, Iso.inv_hom_id, NatTrans.id_app, ConcreteCategory.id_apply]

variable (F E R) in
/-- **The fibre map into the orientation-twisted homology of the Thom pair**: for an orientation
`o` of `E_b`, the map `Hₙ(E_b, E_b ∖ {0}; R) ⟶ Hₙ(E, E₀; π^*o(E))` induced by the inclusion of the
fibre pair over `b` with `π^*o(E)` trivialized by `o`
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

/-- Unfolding lemma for `TauCeti.thomPairSignFiberMap`. -/
theorem thomPairSignFiberMap_def (b : B) (o : Orientation ℝ (E b) ι) (n : ℕ) :
    thomPairSignFiberMap F E R hι b o n =
      ((TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).twistedHomologyConstantIso
          (ModuleCat.of R R) n).inv ≫
        (TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).twistedHomologyCoefficientMap
          (fiberThomPairSignLocalSystemIso F E R hι b o).inv n ≫
        TopPair.twistedHomologyMap (fiberThomPairMap F E b) (thomPairSignLocalSystem F E R hι) n :=
  (rfl)

/-- Reversing the orientation of `E_b` negates `TauCeti.thomPairSignFiberMap`. -/
@[simp]
theorem thomPairSignFiberMap_neg (b : B) (o : Orientation ℝ (E b) ι) (n : ℕ) :
    thomPairSignFiberMap F E R hι b (-o) n = -thomPairSignFiberMap F E R hι b o n := by
  rw [thomPairSignFiberMap, thomPairSignFiberMap, fiberThomPairSignLocalSystemIso_neg_inv,
    TopPair.twistedHomologyCoefficientMap_neg, Preadditive.neg_comp, Preadditive.comp_neg]

end TauCeti
