/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient.Sign.Tensor
public import TauCeti.Topology.Homotopy.Monodromy.Basic
public import TauCeti.Topology.IsLocalHomeomorph
public import TauCeti.Topology.VectorBundle.Orientation.Cover

import Mathlib.Algebra.Category.ModuleCat.Projective
import TauCeti.Topology.Homotopy.Covering

/-!
# The orientation local system of a real vector bundle

The orientation local system `o(E)` of a real vector bundle `E → B` of rank `card ι` is the sign
local system of its orientation double cover with respect to the deck involution reversing
orientations (`TauCeti.VectorBundleOrientationCover.signLocalSystem`). Its fibre over `b` consists
of the `R`-valued functions `f` on the orientations of `E_b` with `f (-o) = -f o`, and transport
along a path precomposes with path lifting in the cover. With `R = ℤ` this is the integral sign
local system whose fibre over `b` is a copy of `ℤ` with the two orientations of `E_b` as its
generators: evaluation at any orientation `o` of `E_b` identifies the fibre with `R`
(`TauCeti.VectorBundleOrientationCover.signLocalSystemFiberEquiv`), and the opposite orientation
gives the opposite identification.

An orientation of the bundle is a continuous section of the orientation double cover, so it
trivializes the orientation local system
(`TauCeti.VectorBundleOrientation.signLocalSystemIso`), by evaluation at the chosen orientation of
each fibre. Reversing the orientation negates the trivialization. This is the coefficient system
in which Thom and Euler classes of bundles without a chosen orientation live; a chosen orientation
identifies cohomology twisted by it with ordinary cohomology. Independently of orientability,
`TauCeti.VectorBundleOrientationCover.signLocalSystemTensorIso` identifies its tensor square
with the constant coefficient system: evaluate both factors at either orientation and multiply.
If `2 = 0` in `R`, as for `R = 𝔽₂`, the system itself is constant without any orientation
(`TauCeti.VectorBundleOrientationCover.signLocalSystemIsoOfTwoEqZero`): evaluation at either
orientation of a fibre gives the same value, since `-1 = 1` in `R`.

Over the base set of a trivialization of the atlas the system is trivialized without a global
orientation: transport along a path in the base set carries the element with value `r` at the
orientation read as a fixed orientation `ω` of the model fibre to the element with value `r` at the
orientation read as `ω` at the end of the path
(`TauCeti.VectorBundleOrientationCover.signLocalSystem_map_mk_signLocalSystemFiberEquiv_symm`),
since these orientations form a continuous section of the orientation double cover over the base
set, which lifts the path. Transport is read through any path lifting by evaluation at its ends
(`TauCeti.VectorBundleOrientationCover.signLocalSystemFiberEquiv_map`).

Every loop acts on a fibre of `o(E)` by `1` or by `-1`
(`VectorBundleOrientationCover.monodromyRepresentation_signLocalSystem_eq_one_or_eq_neg_one`).
Over a connected, locally path-connected base, a non-orientable bundle has a loop acting by `-1`
(`VectorBundleOrientationCover.exists_monodromyRepresentation_signLocalSystem_eq_neg_one`):
its orientation double cover is connected, hence path-connected, so a path in the cover joins the
two orientations of a fibre, and it projects to a loop whose monodromy exchanges them.

## Main definitions

* `TauCeti.VectorBundleOrientationCover.signLocalSystem`: the orientation local system `o(E)`.
* `TauCeti.VectorBundleOrientationCover.signLocalSystemObjEquiv`: its fibres as modules of
  functions on orientations.
* `TauCeti.VectorBundleOrientationCover.signLocalSystemFiberEquiv`: evaluation at an orientation
  of the fibre.
* `TauCeti.VectorBundleOrientation.signLocalSystemIso`: the trivialization given by an
  orientation.
* `TauCeti.VectorBundleOrientationCover.pullbackSignLocalSystemIso`: the trivialization of the
  orientation system pulled back along a map into the base set of a trivialization, by evaluation
  at the orientations which it reads as a fixed orientation of the model fibre.
* `TauCeti.VectorBundleOrientationCover.signLocalSystemIsoOfTwoEqZero`: the trivialization when
  `2 = 0` in the coefficients.

## Main results

* `TauCeti.VectorBundleOrientationCover.exists_monodromyRepresentation_signLocalSystem_eq_neg_one`:
  a non-orientable bundle over a connected, locally path-connected base has an
  orientation-reversing loop.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §12 (the orientation double cover and twisted coefficients).
* A. Hatcher, *Algebraic Topology*, Section 3.H (local coefficient systems and the orientation
  system).
-/

public section

noncomputable section

open Bundle CategoryTheory Module

universe u uB uE uι

variable {B : Type uB} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type uE} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {ι : Type uι}

namespace TauCeti

namespace VectorBundleOrientationCover

variable [Fintype ι] (R : Type u) [Ring R]

variable (F E) in
/-- The orientation local system `o(E)` of a real vector bundle of rank `card ι`: the sign local
system of its orientation double cover with respect to the deck involution. Its fibre over `b` is
the module `TauCeti.signFiber` of functions on the orientations of `E_b` that change sign under
reversal (`TauCeti.VectorBundleOrientationCover.signLocalSystemObjEquiv`), and transport along a
path precomposes with path lifting in the cover. -/
@[expose] def signLocalSystem (hι : Fintype.card ι = finrank ℝ F) :
    LocalCoefficientSystem.{u, uB, max uB uE uι u} R (TopCat.of B) :=
  (isCoveringMap_proj (F := F) (E := E) hι).signLocalSystem R _ proj_comp_deck

variable {R} (hι : Fintype.card ι = finrank ℝ F)

/-- The orientation local system is the sign local system of the orientation double cover with
respect to its deck involution. -/
theorem signLocalSystem_def :
    signLocalSystem F E R hι =
      (isCoveringMap_proj (F := F) (E := E) hι).signLocalSystem R _ proj_comp_deck :=
  (rfl)

/-- The fibre of the orientation local system over `x` is the module of functions on the
orientations over `x` that change sign under reversal. -/
def signLocalSystemObjEquiv (x : FundamentalGroupoid (TopCat.of B)) :
    (signLocalSystem F E R hι).obj x ≃ₗ[R]
      signFiber R (p := proj) (deck (F := F) (E := E) (ι := ι)) (funext proj_deck) x.as :=
  (isCoveringMap_proj (F := F) (E := E) hι).signLocalSystemObjEquiv _ proj_comp_deck x

/-- Read through `TauCeti.VectorBundleOrientationCover.signLocalSystem_def`, the fibre of the
orientation local system is identified with the module of sign functions as by
`TauCeti.VectorBundleOrientationCover.signLocalSystemObjEquiv`. -/
theorem signLocalSystemObjEquiv_eqToIso_signLocalSystem_def_hom_app
    (x : FundamentalGroupoid (TopCat.of B)) (g : (signLocalSystem F E R hι).obj x) :
    (isCoveringMap_proj (F := F) (E := E) hι).signLocalSystemObjEquiv _ proj_comp_deck x
        ((eqToIso (signLocalSystem_def hι)).hom.app x g) =
      signLocalSystemObjEquiv hι x g :=
  (rfl)

/-- The inverse form of
`TauCeti.VectorBundleOrientationCover.signLocalSystemObjEquiv_eqToIso_signLocalSystem_def_hom_app`.
-/
theorem signLocalSystemObjEquiv_eqToIso_signLocalSystem_def_inv_app
    (x : FundamentalGroupoid (TopCat.of B))
    (g : ((isCoveringMap_proj (F := F) (E := E) hι).signLocalSystem R _ proj_comp_deck).obj x) :
    signLocalSystemObjEquiv hι x ((eqToIso (signLocalSystem_def hι)).inv.app x g) =
      (isCoveringMap_proj (F := F) (E := E) hι).signLocalSystemObjEquiv _ proj_comp_deck x g :=
  (rfl)

/-- Transport in the orientation local system precomposes with path lifting along the inverse
path in the orientation double cover. -/
@[simp]
theorem signLocalSystemObjEquiv_map_apply {x y : FundamentalGroupoid (TopCat.of B)} (γ : x ⟶ y)
    (f : (signLocalSystem F E R hι).obj x)
    (e : (proj ⁻¹' {y.as} : Set (VectorBundleOrientationCover F E ι))) :
    (signLocalSystemObjEquiv hι y (((signLocalSystem F E R hι).map γ).hom f) :
      (proj ⁻¹' {y.as} : Set (VectorBundleOrientationCover F E ι)) → R) e =
      (signLocalSystemObjEquiv hι x f :
        (proj ⁻¹' {x.as} : Set (VectorBundleOrientationCover F E ι)) → R)
        ((isCoveringMap_proj hι).monodromy (inv γ) e) :=
  (isCoveringMap_proj hι).signLocalSystemObjEquiv_map_apply _ proj_comp_deck γ f e

/-- Evaluation at an orientation `o` of the fibre `E_b` identifies the fibre of the orientation
local system over `b` with `R`. -/
def signLocalSystemFiberEquiv {b : B} (o : Orientation ℝ (E b) ι) :
    (signLocalSystem F E R hι).obj (FundamentalGroupoid.mk b) ≃ₗ[R] R :=
  signLocalSystemObjEquiv hι (FundamentalGroupoid.mk b) ≪≫ₗ
    signFiberEquiv deck_ne_self (fun _ _ h ↦ eq_or_eq_deck hι h) ⟨⟨b, o⟩, rfl⟩

@[simp]
theorem signLocalSystemFiberEquiv_apply {b : B} (o : Orientation ℝ (E b) ι)
    (f : (signLocalSystem F E R hι).obj (FundamentalGroupoid.mk b)) :
    signLocalSystemFiberEquiv hι o f =
      (signLocalSystemObjEquiv hι (FundamentalGroupoid.mk b) f :
        (proj ⁻¹' {b} : Set (VectorBundleOrientationCover F E ι)) → R) ⟨⟨b, o⟩, rfl⟩ :=
  signFiberEquiv_apply deck_ne_self (fun _ _ h ↦ eq_or_eq_deck hι h) ⟨⟨b, o⟩, rfl⟩ _

/-- Evaluation at the opposite orientation is the negative of evaluation at `o`. It has high
priority so that `simp` applies it before unfolding the evaluation by
`signLocalSystemFiberEquiv_apply`. -/
@[simp high]
theorem signLocalSystemFiberEquiv_neg {b : B} (o : Orientation ℝ (E b) ι)
    (f : (signLocalSystem F E R hι).obj (FundamentalGroupoid.mk b)) :
    signLocalSystemFiberEquiv hι (-o) f = -signLocalSystemFiberEquiv hι o f := by
  -- The deck involution sends the point `⟨b, o⟩` of the fibre to `⟨b, -o⟩`.
  have h : Function.fiberMap _ proj_comp_deck b ⟨⟨b, o⟩, rfl⟩ =
      (⟨⟨b, -o⟩, rfl⟩ : (proj ⁻¹' {b} : Set (VectorBundleOrientationCover F E ι))) :=
    Subtype.ext (by simp [deck_apply])
  rw [signLocalSystemFiberEquiv_apply, signLocalSystemFiberEquiv_apply, ← h]
  exact mem_signFiber_iff.1 (signLocalSystemObjEquiv hι _ f).property _

/-- Evaluation at the opposite orientation is the negative of evaluation at `o`, stated for the
inverse equivalences. -/
theorem signLocalSystemFiberEquiv_neg_symm {b : B} (o : Orientation ℝ (E b) ι) :
    (signLocalSystemFiberEquiv (R := R) hι (-o)).symm.toLinearMap =
      -(signLocalSystemFiberEquiv (R := R) hι o).symm.toLinearMap := by
  refine LinearMap.ext fun r ↦ (signLocalSystemFiberEquiv hι o).injective ?_
  have h := signLocalSystemFiberEquiv_neg hι o ((signLocalSystemFiberEquiv hι (-o)).symm r)
  rw [LinearEquiv.apply_symm_apply] at h
  rw [LinearMap.neg_apply, map_neg, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  exact (neg_eq_iff_eq_neg.2 h).symm

/-- Transport in the orientation local system along a path which lifts, in the orientation double
cover, from the orientation `o` at its start to the orientation `o'` at its end carries the value at
`o` to the value at `o'`. -/
theorem signLocalSystemFiberEquiv_map {b b' : B}
    (p : FundamentalGroupoid.mk b ⟶ FundamentalGroupoid.mk b') {o : Orientation ℝ (E b) ι}
    {o' : Orientation ℝ (E b') ι}
    (h : (isCoveringMap_proj (F := F) (E := E) hι).monodromy p ⟨⟨b, o⟩, rfl⟩ = ⟨⟨b', o'⟩, rfl⟩)
    (f : (signLocalSystem F E R hι).obj (FundamentalGroupoid.mk b)) :
    signLocalSystemFiberEquiv hι o' ((signLocalSystem F E R hι).map p f) =
      signLocalSystemFiberEquiv hι o f := by
  rw [signLocalSystemFiberEquiv_apply, signLocalSystemFiberEquiv_apply,
    signLocalSystemObjEquiv_map_apply, ← h, ← IsCoveringMap.monodromy_trans_apply]
  -- Monodromy along `p` followed by its inverse is the identity of the fibre.
  have h' := congrArg (fun a ↦ (isCoveringMap_proj (F := F) (E := E) hι).monodromy a
    (⟨⟨b, o⟩, rfl⟩ : (proj ⁻¹' {b} : Set (VectorBundleOrientationCover F E ι))))
    (IsIso.hom_inv_id p)
  exact congrArg _ (h'.trans (congrFun (isCoveringMap_proj (F := F) (E := E) hι).monodromy_refl _))

/-- **Transport over a trivializing set**: along a path in the base set of a trivialization `e` of
the atlas, transport in the orientation local system carries the element with value `r` at the
orientation read as `ω` at the start to the element with value `r` at the orientation read as `ω`
at the end. -/
theorem signLocalSystem_map_mk_signLocalSystemFiberEquiv_symm (e : Trivialization F (π F E))
    [MemTrivializationAtlas e] (ω : Orientation ℝ F ι) {x y : B} (γ : Path x y)
    (hγ : ∀ t, γ t ∈ e.baseSet) (hx : x ∈ e.baseSet) (hy : y ∈ e.baseSet) (r : R) :
    ((signLocalSystem F E R hι).map (Path.Homotopic.Quotient.mk γ)).hom
        ((signLocalSystemFiberEquiv hι ((e.mapOrientation ι hx).symm ω)).symm r) =
      (signLocalSystemFiberEquiv hι ((e.mapOrientation ι hy).symm ω)).symm r := by
  -- The orientations read as `ω` form a continuous section of the cover over the base set, which
  -- lifts `γ`, so the monodromy along `γ` carries the one at `x` to the one at `y`.
  let Γ : C(unitInterval, VectorBundleOrientationCover F E ι) :=
    ⟨fun t ↦ ⟨γ t, (e.mapOrientation ι (hγ t)).symm ω⟩,
      (continuous_mk_mapOrientation_symm hι e ω).comp (γ.continuous.subtype_mk hγ)⟩
  have hmk {x y : B} (h : x = y) (hx : x ∈ e.baseSet) (hy : y ∈ e.baseSet) :
      (⟨x, (e.mapOrientation ι hx).symm ω⟩ : VectorBundleOrientationCover F E ι) =
        ⟨y, (e.mapOrientation ι hy).symm ω⟩ := by
    subst h
    rfl
  have hm : (isCoveringMap_proj hι).monodromy (Path.Homotopic.Quotient.mk γ)
      ⟨⟨x, (e.mapOrientation ι hx).symm ω⟩, rfl⟩ = ⟨⟨y, (e.mapOrientation ι hy).symm ω⟩, rfl⟩ :=
    Subtype.ext (((isCoveringMap_proj hι).monodromy_eq_apply_one (Γ := Γ) rfl
      (hmk γ.source _ _)).trans (hmk γ.target _ _))
  apply (signLocalSystemFiberEquiv hι ((e.mapOrientation ι hy).symm ω)).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (signLocalSystemFiberEquiv_map hι _ hm _).trans
    (LinearEquiv.apply_symm_apply _ _)

/-- Every loop at `b` acts by `1` or by `-1` on the fibre of the orientation local system over
`b`. -/
theorem monodromyRepresentation_signLocalSystem_eq_one_or_eq_neg_one (b : B)
    (g : FundamentalGroup (TopCat.of B) b) :
    LocalCoefficientSystem.monodromyRepresentation (signLocalSystem F E R hι) b g = 1 ∨
      LocalCoefficientSystem.monodromyRepresentation (signLocalSystem F E R hι) b g = -1 := by
  rw [signLocalSystem_def]
  exact (isCoveringMap_proj hι).monodromyRepresentation_signLocalSystem_eq_one_or_eq_neg_one
    (hσ := proj_comp_deck) deck_ne_self (fun _ _ h ↦ eq_or_eq_deck hι h) g

variable [FiniteDimensional ℝ F]

/-- The fibres of the orientation local system are free of rank one, hence projective: evaluation
at either orientation of the fibre identifies each of them with `R`. -/
instance projective_signLocalSystem_obj (x : FundamentalGroupoid (TopCat.of B)) :
    Projective ((signLocalSystem F E R hι).obj x) := by
  obtain ⟨b⟩ := x
  obtain ⟨p, rfl⟩ := surjective_proj (F := F) (E := E) hι b
  exact ModuleCat.projective_of_free
    ((Basis.singleton Unit R).map (signLocalSystemFiberEquiv hι p.orientation).symm)

/-- **A non-orientable bundle has an orientation-reversing loop.** Over a connected, locally
path-connected base, if `E` is not orientable, some loop at `b` acts by `-1` on the fibre of the
orientation local system over `b`. -/
theorem exists_monodromyRepresentation_signLocalSystem_eq_neg_one [ConnectedSpace B]
    [LocallyPathConnectedSpace B] (h : IsEmpty (VectorBundleOrientation F E ι)) (b : B) :
    ∃ g : FundamentalGroup (TopCat.of B) b,
      LocalCoefficientSystem.monodromyRepresentation (signLocalSystem F E R hι) b g = -1 := by
  have hp := isCoveringMap_proj (F := F) (E := E) hι
  have : ConnectedSpace (VectorBundleOrientationCover F E ι) :=
    not_not.1 fun hc ↦
      h.false ((VectorBundleOrientation.nonempty_iff_not_connectedSpace hι).2 hc).some
  have : LocallyPathConnectedSpace (VectorBundleOrientationCover F E ι) :=
    hp.isLocalHomeomorph.locallyPathConnectedSpace
  have : PathConnectedSpace (VectorBundleOrientationCover F E ι) :=
    PathConnectedSpace.of_locallyPathConnectedSpace
  -- A path in the cover from a point `q` over `b` to `deck q` projects to a loop at `b` whose
  -- monodromy carries `q` to `deck q`.
  obtain ⟨q, hq⟩ := surjective_proj (F := F) (E := E) hι b
  obtain ⟨g, hg⟩ := hp.exists_monodromy_eq_of_joined (X := TopCat.of B) (e := ⟨q, hq⟩)
    (e' := ⟨deck q, (proj_deck q).trans hq⟩) (PathConnectedSpace.joined _ _)
  rw [signLocalSystem_def]
  refine ⟨g, hp.monodromyRepresentation_signLocalSystem_eq_neg_one (hσ := proj_comp_deck)
    deck_ne_self (fun _ _ h ↦ eq_or_eq_deck hι h) (e := ⟨q, hq⟩) (hg.trans (Subtype.ext ?_))⟩
  exact (Function.fiberMap_apply_coe _ proj_comp_deck b ⟨q, hq⟩).symm

section TwoEqZero

variable (h2 : (2 : R) = 0)

/-- **The orientation local system in characteristic two.** If `2 = 0` in `R`, the orientation
local system is constant, without any orientation of the bundle: over `b`, the isomorphism with
the constant system evaluates at either orientation of `E_b`
(`TauCeti.VectorBundleOrientationCover.signLocalSystemIsoOfTwoEqZero_hom_app_apply`), the two
values agreeing since `-1 = 1` in `R`. -/
def signLocalSystemIsoOfTwoEqZero :
    signLocalSystem F E R hι ≅
      (LocalCoefficientSystem.constantFunctor (TopCat.of B)).obj
        (ModuleCat.of R (ULift.{max uB uE uι} R)) :=
  (isCoveringMap_proj hι).signLocalSystemIsoOfTwoEqZero (hσ := proj_comp_deck) deck_ne_self
    (fun _ _ h ↦ eq_or_eq_deck hι h) (surjective_proj hι) h2

-- Not `simp`: the orientation `o` appears only on the right-hand side.
/-- The trivialization of the orientation local system in characteristic two evaluates at any
orientation `o` of the fibre. -/
theorem signLocalSystemIsoOfTwoEqZero_hom_app_apply {b : B} (o : Orientation ℝ (E b) ι)
    (f : (signLocalSystem F E R hι).obj (FundamentalGroupoid.mk b)) :
    (ModuleCat.Hom.hom (B := ModuleCat.of R (ULift.{max uB uE uι} R))
        ((signLocalSystemIsoOfTwoEqZero hι h2).hom.app (FundamentalGroupoid.mk b))) f =
      ULift.up (signLocalSystemFiberEquiv hι o f) := by
  rw [signLocalSystemFiberEquiv_apply]
  exact (isCoveringMap_proj hι).signLocalSystemIsoOfTwoEqZero_hom_app_apply (X := TopCat.of B)
    (hσ := proj_comp_deck) deck_ne_self (fun _ _ h ↦ eq_or_eq_deck hι h) (surjective_proj hι) h2
    (FundamentalGroupoid.mk b) f ⟨⟨b, o⟩, rfl⟩

/-- The inverse of the trivialization of the orientation local system in characteristic two
sends `r` over `b` to the element of the fibre whose value at any orientation `o` of `E_b` is
`r`. -/
theorem signLocalSystemIsoOfTwoEqZero_inv_app_apply {b : B} (o : Orientation ℝ (E b) ι) (r : R) :
    (ModuleCat.Hom.hom (A := ModuleCat.of R (ULift.{max uB uE uι} R))
        ((signLocalSystemIsoOfTwoEqZero hι h2).inv.app (FundamentalGroupoid.mk b)))
        (ULift.up r) =
      (signLocalSystemFiberEquiv hι o).symm r := by
  apply (signLocalSystemFiberEquiv hι o).injective
  rw [LinearEquiv.apply_symm_apply, signLocalSystemFiberEquiv_apply]
  exact (isCoveringMap_proj hι).signLocalSystemIsoOfTwoEqZero_inv_app_apply (X := TopCat.of B)
    (hσ := proj_comp_deck) deck_ne_self (fun _ _ h ↦ eq_or_eq_deck hι h) (surjective_proj hι) h2
    (FundamentalGroupoid.mk b) r ⟨⟨b, o⟩, rfl⟩

end TwoEqZero

section Tensor

open MonoidalCategory
open scoped TensorProduct

-- The pointwise monoidal structure on `ModuleCat` requires the coefficient ring and
-- the module fibres to live in the same universe.
variable {S : Type (max uB uE uι)} [CommRing S]

/-- The tensor square of the orientation local system is canonically constant, without a
chosen bundle orientation. The pairing multiplies evaluations at either orientation of a fibre.
This includes rank zero and coefficient rings of characteristic two. -/
def signLocalSystemTensorIso :
    signLocalSystem F E S hι ⊗ signLocalSystem F E S hι ≅
      (LocalCoefficientSystem.constantFunctor (TopCat.of B)).obj
        (ModuleCat.of S (ULift.{max uB uE uι} S)) :=
  (isCoveringMap_proj hι).signLocalSystemTensorIso deck_ne_self
    (fun _ _ h ↦ eq_or_eq_deck hι h) (surjective_proj hι)

/-- At a fibre orientation, the canonical pairing is multiplication of the two evaluation
coordinates; choosing the opposite orientation gives the same result. -/
theorem signLocalSystemTensorIso_hom_app_tmul {b : B} (o : Orientation ℝ (E b) ι)
    (f g : (signLocalSystem F E S hι).obj (FundamentalGroupoid.mk b)) :
    ((signLocalSystemTensorIso (S := S) hι).hom.app (FundamentalGroupoid.mk b)).hom
      (f ⊗ₜ[S] g) = ULift.up
        (signLocalSystemFiberEquiv hι o f * signLocalSystemFiberEquiv hι o g) := by
  rw [signLocalSystemFiberEquiv_apply hι o f, signLocalSystemFiberEquiv_apply hι o g]
  -- Convert between the bundle-specific accessors and the covering-space accessors;
  -- these wrappers are not exposed to rewriting across modules.
  convert IsCoveringMap.signLocalSystemTensorIso_hom_app_tmul (R := S) (X := TopCat.of B)
    (p := proj (F := F) (E := E) (ι := ι)) (isCoveringMap_proj hι)
    (hσ := proj_comp_deck) deck_ne_self
    (fun _ _ h ↦ eq_or_eq_deck hι h) (surjective_proj hι)
    (FundamentalGroupoid.mk b)
    (⟨⟨b, o⟩, rfl⟩ : (proj ⁻¹' {b} : Set (VectorBundleOrientationCover F E ι))) f g using 1
  rfl

/-- In either orientation coordinate, the inverse pairing sends `a * b` to the tensor of the
corresponding fibre elements. In particular, either orientation generator has tensor square `1`.
The scalars need no chosen orientation on the rest of the bundle. -/
theorem signLocalSystemTensorIso_inv_app_mul {x : B} (o : Orientation ℝ (E x) ι) (a b : S) :
    ((signLocalSystemTensorIso (S := S) hι).inv.app (FundamentalGroupoid.mk x)).hom
      (ULift.up (a * b)) =
      (signLocalSystemFiberEquiv hι o).symm a ⊗ₜ[S]
        (signLocalSystemFiberEquiv hι o).symm b :=
  IsCoveringMap.signLocalSystemTensorIso_inv_app_mul (R := S) (X := TopCat.of B)
    (p := proj (F := F) (E := E) (ι := ι)) (isCoveringMap_proj hι)
    (hσ := proj_comp_deck) deck_ne_self
    (fun _ _ h ↦ eq_or_eq_deck hι h) (surjective_proj hι)
    (FundamentalGroupoid.mk x)
    (⟨⟨x, o⟩, rfl⟩ : (proj ⁻¹' {x} : Set (VectorBundleOrientationCover F E ι))) a b

end Tensor

end VectorBundleOrientationCover

namespace VectorBundleOrientation

variable [Fintype ι] {R : Type u} [Ring R]
  (hι : Fintype.card ι = finrank ℝ F)

/-- An orientation `o` of the bundle trivializes the orientation local system: over `b`, the
isomorphism with the constant system evaluates at the orientation `o b` of `E_b`. -/
def signLocalSystemIso (o : VectorBundleOrientation F E ι) :
    VectorBundleOrientationCover.signLocalSystem F E R hι ≅
      (LocalCoefficientSystem.constantFunctor (TopCat.of B)).obj
        (ModuleCat.of R (ULift.{max uB uE uι} R)) :=
  IsCoveringMap.signLocalSystemIsoOfSection _ (hσ := VectorBundleOrientationCover.proj_comp_deck)
    VectorBundleOrientationCover.deck_ne_self
    (fun _ _ h ↦ VectorBundleOrientationCover.eq_or_eq_deck hι h)
    (o.coverSection hι) (o.proj_coverSection hι)

/-- The trivialization of the orientation local system given by `o` is the trivialization of the
sign local system given by the section `b ↦ (b, o b)` of the orientation double cover. -/
theorem signLocalSystemIso_def (o : VectorBundleOrientation F E ι) :
    signLocalSystemIso (R := R) hι o =
      (VectorBundleOrientationCover.isCoveringMap_proj hι).signLocalSystemIsoOfSection
        (hσ := VectorBundleOrientationCover.proj_comp_deck)
        VectorBundleOrientationCover.deck_ne_self
        (fun _ _ h ↦ VectorBundleOrientationCover.eq_or_eq_deck hι h)
        (o.coverSection hι) (o.proj_coverSection hι) :=
  (rfl)

@[simp]
theorem signLocalSystemIso_hom_app_apply (o : VectorBundleOrientation F E ι) (b : B)
    (f : (VectorBundleOrientationCover.signLocalSystem F E R hι).obj
      (FundamentalGroupoid.mk b)) :
    (ModuleCat.Hom.hom (B := ModuleCat.of R (ULift.{max uB uE uι} R))
        ((signLocalSystemIso hι o).hom.app (FundamentalGroupoid.mk b))) f =
      ULift.up (VectorBundleOrientationCover.signLocalSystemFiberEquiv hι (o b) f) := by
  rw [VectorBundleOrientationCover.signLocalSystemFiberEquiv_apply]
  refine (IsCoveringMap.signLocalSystemIsoOfSection_hom_app_apply (X := TopCat.of B) _
    (hσ := VectorBundleOrientationCover.proj_comp_deck) VectorBundleOrientationCover.deck_ne_self
    (fun _ _ h ↦ VectorBundleOrientationCover.eq_or_eq_deck hι h)
    (o.coverSection hι) (o.proj_coverSection hι) (FundamentalGroupoid.mk b) f).trans ?_
  -- `signLocalSystemObjEquiv` of the orientation cover is by definition that of the covering.
  simp only [coverSection_apply]
  rfl

/-- The inverse of the trivialization given by `o` sends `r` over `b` to the element of the fibre
whose evaluation at the orientation `o b` is `r`. -/
@[simp]
theorem signLocalSystemIso_inv_app_apply (o : VectorBundleOrientation F E ι) (b : B) (r : R) :
    (ModuleCat.Hom.hom (A := ModuleCat.of R (ULift.{max uB uE uι} R))
        ((signLocalSystemIso (R := R) hι o).inv.app (FundamentalGroupoid.mk b))) (ULift.up r) =
      (VectorBundleOrientationCover.signLocalSystemFiberEquiv hι (o b)).symm r := by
  apply (VectorBundleOrientationCover.signLocalSystemFiberEquiv hι (o b)).injective
  rw [LinearEquiv.apply_symm_apply, VectorBundleOrientationCover.signLocalSystemFiberEquiv_apply]
  refine Eq.trans ?_ (IsCoveringMap.signLocalSystemIsoOfSection_inv_app_apply (X := TopCat.of B)
    (VectorBundleOrientationCover.isCoveringMap_proj hι)
    (hσ := VectorBundleOrientationCover.proj_comp_deck) VectorBundleOrientationCover.deck_ne_self
    (fun _ _ h ↦ VectorBundleOrientationCover.eq_or_eq_deck hι h)
    (o.coverSection hι) (o.proj_coverSection hι) (FundamentalGroupoid.mk b) r)
  -- `signLocalSystemObjEquiv` of the orientation cover is by definition that of the covering.
  simp only [coverSection_apply]
  rfl

/-- The trivialization of the orientation local system given by the opposite orientation is the
negative of the one given by `o`. -/
@[simp]
theorem signLocalSystemIso_neg_hom (o : VectorBundleOrientation F E ι) :
    (signLocalSystemIso (R := R) hι (-o)).hom = -(signLocalSystemIso hι o).hom := by
  ext ⟨b⟩ f
  rw [NatTrans.app_neg, ModuleCat.hom_neg, LinearMap.neg_apply]
  have h : VectorBundleOrientationCover.signLocalSystemFiberEquiv hι ((-o) b) f =
      -VectorBundleOrientationCover.signLocalSystemFiberEquiv hι (o b) f := by
    rw [neg_apply, VectorBundleOrientationCover.signLocalSystemFiberEquiv_neg]
  -- The negation in the fibre of the constant system is the negation of `ULift R`, which
  -- `ULift.up` commutes with by definition; `rw` cannot see through the fibre of the constant
  -- system at reducible transparency.
  exact (signLocalSystemIso_hom_app_apply hι (-o) b f).trans ((congrArg ULift.up h).trans
    (congrArg Neg.neg (signLocalSystemIso_hom_app_apply hι o b f)).symm)

/-- The inverse of the trivialization given by the opposite orientation is the negative of the
inverse of the one given by `o`. -/
@[simp]
theorem signLocalSystemIso_neg_inv (o : VectorBundleOrientation F E ι) :
    (signLocalSystemIso (R := R) hι (-o)).inv = -(signLocalSystemIso hι o).inv :=
  Iso.inv_ext (by rw [signLocalSystemIso_neg_hom, Preadditive.neg_comp_neg, Iso.hom_inv_id])

end VectorBundleOrientation

end TauCeti

end

/-! ### The trivializations of the orientation local system over a trivializing set

The pulled-back orientation local system and the constant system with fibre `R` must have their
fibres in the same universe, so the base, the fibres and the ring share a universe here. -/

noncomputable section

open Bundle CategoryTheory Module

namespace TauCeti.VectorBundleOrientationCover

variable {R : Type u} [Ring R] {B : Type u} [TopologicalSpace B] {F : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] {E : B → Type u} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E] {ι : Type} [Fintype ι]
  (hι : Fintype.card ι = finrank ℝ F)

variable (R) in
/-- Over a map `g : Y → B` with values in the base set of a trivialization `e` of the atlas, the
pulled-back orientation local system is trivialized by evaluating, over each point `y`, at the
orientation of `E_{g y}` which `e` reads as a fixed orientation `ω` of the model fibre. -/
def pullbackSignLocalSystemIso (e : Trivialization F (π F E)) [MemTrivializationAtlas e]
    (ω : Orientation ℝ F ι) {Y : TopCat.{uB}} (g : C(Y, TopCat.of B))
    (hg : ∀ y, g y ∈ e.baseSet) :
    (LocalCoefficientSystem.pullback g).obj (signLocalSystem F E R hι) ≅
      (LocalCoefficientSystem.constantFunctor Y).obj (ModuleCat.of R R) :=
  NatIso.ofComponents
    (fun y ↦ (signLocalSystemFiberEquiv hι ((e.mapOrientation ι (hg y.as)).symm ω)).toModuleIso)
    fun {y y'} p ↦ by
      refine ModuleCat.hom_ext (LinearMap.ext fun
        (f : (signLocalSystem F E R hι).obj (FundamentalGroupoid.mk (g y.as))) ↦ ?_)
      -- The constant system transports by the identity, and the pulled-back system by transport
      -- along the image path, which stays in the base set of `e`.
      induction p using Quotient.ind with | _ δ => ?_
      have h := signLocalSystem_map_mk_signLocalSystemFiberEquiv_symm hι e ω (δ.map g.continuous)
        (fun t ↦ hg (δ t)) (hg y.as) (hg y'.as)
        (signLocalSystemFiberEquiv hι ((e.mapOrientation ι (hg y.as)).symm ω) f)
      rw [LinearEquiv.symm_apply_apply] at h
      exact ((congrArg (signLocalSystemFiberEquiv hι _) h).trans
        (LinearEquiv.apply_symm_apply _ _)).trans rfl

/-- Over `y`, the trivialization evaluates at the orientation of `E_{g y}` which `e` reads as
`ω`. -/
@[simp]
theorem pullbackSignLocalSystemIso_hom_app_apply (e : Trivialization F (π F E))
    [MemTrivializationAtlas e] (ω : Orientation ℝ F ι) {Y : TopCat.{uB}} (g : C(Y, TopCat.of B))
    (hg : ∀ y, g y ∈ e.baseSet) (y : Y)
    (f : (signLocalSystem F E R hι).obj (FundamentalGroupoid.mk (g y))) :
    (ModuleCat.Hom.hom (A := (signLocalSystem F E R hι).obj (FundamentalGroupoid.mk (g y)))
        (B := ModuleCat.of R R)
        ((pullbackSignLocalSystemIso R hι e ω g hg).hom.app (FundamentalGroupoid.mk y))) f =
      signLocalSystemFiberEquiv hι ((e.mapOrientation ι (hg y)).symm ω) f :=
  (rfl)

/-- Over `y`, the inverse of the trivialization sends `r` to the element of the fibre whose
evaluation at the orientation of `E_{g y}` which `e` reads as `ω` is `r`. -/
@[simp]
theorem pullbackSignLocalSystemIso_inv_app_apply (e : Trivialization F (π F E))
    [MemTrivializationAtlas e] (ω : Orientation ℝ F ι) {Y : TopCat.{uB}} (g : C(Y, TopCat.of B))
    (hg : ∀ y, g y ∈ e.baseSet) (y : Y) (r : R) :
    (ModuleCat.Hom.hom (A := ModuleCat.of R R)
        (B := (signLocalSystem F E R hι).obj (FundamentalGroupoid.mk (g y)))
        ((pullbackSignLocalSystemIso R hι e ω g hg).inv.app (FundamentalGroupoid.mk y))) r =
      (signLocalSystemFiberEquiv hι ((e.mapOrientation ι (hg y)).symm ω)).symm r :=
  (rfl)

/-- Two trivializations and orientations of the model fibre which pull back to the same
orientations of the fibres over `g` give the same trivialization of the pulled-back orientation
local system. -/
theorem pullbackSignLocalSystemIso_congr {e e' : Trivialization F (π F E)}
    [MemTrivializationAtlas e] [MemTrivializationAtlas e'] {ω ω' : Orientation ℝ F ι}
    {Y : TopCat.{uB}} (g : C(Y, TopCat.of B)) (hg : ∀ y, g y ∈ e.baseSet)
    (hg' : ∀ y, g y ∈ e'.baseSet)
    (h : ∀ y, (e'.mapOrientation ι (hg' y)).symm ω' = (e.mapOrientation ι (hg y)).symm ω) :
    pullbackSignLocalSystemIso R hι e' ω' g hg' = pullbackSignLocalSystemIso R hι e ω g hg := by
  refine Iso.ext (NatTrans.ext (funext fun ⟨y⟩ ↦ ModuleCat.hom_ext (LinearMap.ext fun
    (f : (signLocalSystem F E R hι).obj (FundamentalGroupoid.mk (g y))) ↦ ?_)))
  refine (pullbackSignLocalSystemIso_hom_app_apply hι e' ω' g hg' y f).trans ?_
  rw [h y]
  exact (pullbackSignLocalSystemIso_hom_app_apply hι e ω g hg y f).symm

/-- Reversing the orientation of the model fibre negates the trivialization of the pulled-back
orientation local system. -/
@[simp]
theorem pullbackSignLocalSystemIso_neg_hom (e : Trivialization F (π F E))
    [MemTrivializationAtlas e] (ω : Orientation ℝ F ι) {Y : TopCat.{uB}} (g : C(Y, TopCat.of B))
    (hg : ∀ y, g y ∈ e.baseSet) :
    (pullbackSignLocalSystemIso R hι e (-ω) g hg).hom =
      -(pullbackSignLocalSystemIso R hι e ω g hg).hom := by
  refine NatTrans.ext (funext fun ⟨y⟩ ↦ ModuleCat.hom_ext (LinearMap.ext fun
    (f : (signLocalSystem F E R hι).obj (FundamentalGroupoid.mk (g y))) ↦ ?_))
  have h : (e.mapOrientation ι (hg y)).symm (-ω) = -(e.mapOrientation ι (hg y)).symm ω :=
    (e.mapOrientation ι (hg y)).symm_apply_eq.2 (by
      rw [Trivialization.mapOrientation_neg, Equiv.apply_symm_apply])
  rw [NatTrans.app_neg, ModuleCat.hom_neg]
  refine (pullbackSignLocalSystemIso_hom_app_apply hι e (-ω) g hg y f).trans ?_
  rw [h, signLocalSystemFiberEquiv_neg]
  exact congrArg Neg.neg (pullbackSignLocalSystemIso_hom_app_apply hι e ω g hg y f).symm

/-- Reversing the orientation of the model fibre negates the inverse of the trivialization of the
pulled-back orientation local system. -/
@[simp]
theorem pullbackSignLocalSystemIso_neg_inv (e : Trivialization F (π F E))
    [MemTrivializationAtlas e] (ω : Orientation ℝ F ι) {Y : TopCat.{uB}} (g : C(Y, TopCat.of B))
    (hg : ∀ y, g y ∈ e.baseSet) :
    (pullbackSignLocalSystemIso R hι e (-ω) g hg).inv =
      -(pullbackSignLocalSystemIso R hι e ω g hg).inv :=
  Iso.inv_ext (by rw [pullbackSignLocalSystemIso_neg_hom, Preadditive.neg_comp_neg, Iso.hom_inv_id])

end TauCeti.VectorBundleOrientationCover
