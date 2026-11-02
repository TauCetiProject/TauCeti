/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient.Sign
public import TauCeti.Topology.VectorBundle.Orientation.Cover

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
identifies cohomology twisted by it with ordinary cohomology.

## Main definitions

* `TauCeti.VectorBundleOrientationCover.signLocalSystem`: the orientation local system `o(E)`.
* `TauCeti.VectorBundleOrientationCover.signLocalSystemObjEquiv`: its fibres as modules of
  functions on orientations.
* `TauCeti.VectorBundleOrientationCover.signLocalSystemFiberEquiv`: evaluation at an orientation
  of the fibre.
* `TauCeti.VectorBundleOrientation.signLocalSystemIso`: the trivialization given by an
  orientation.

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

variable [FiniteDimensional ℝ F] [Fintype ι] (R : Type u) [Ring R]

variable (F E) in
/-- The orientation local system `o(E)` of a real vector bundle of rank `card ι`: the sign local
system of its orientation double cover with respect to the deck involution. Its fibre over `b` is
the module `TauCeti.signFiber` of functions on the orientations of `E_b` that change sign under
reversal (`TauCeti.VectorBundleOrientationCover.signLocalSystemObjEquiv`), and transport along a
path precomposes with path lifting in the cover. -/
def signLocalSystem (hι : Fintype.card ι = finrank ℝ F) :
    LocalCoefficientSystem.{u, uB, max uB uE uι u} R (TopCat.of B) :=
  (isCoveringMap_proj (F := F) (E := E) hι).signLocalSystem R _ proj_comp_deck

variable {R} (hι : Fintype.card ι = finrank ℝ F)

/-- The fibre of the orientation local system over `x` is the module of functions on the
orientations over `x` that change sign under reversal. -/
def signLocalSystemObjEquiv (x : FundamentalGroupoid (TopCat.of B)) :
    (signLocalSystem F E R hι).obj x ≃ₗ[R]
      signFiber R (p := proj) (deck (F := F) (E := E) (ι := ι)) (funext proj_deck) x.as :=
  (isCoveringMap_proj (F := F) (E := E) hι).signLocalSystemObjEquiv _ proj_comp_deck x

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
  exact mem_signFiber_iff.1 (signLocalSystemObjEquiv hι _ f).2 _

end VectorBundleOrientationCover

namespace VectorBundleOrientation

variable [FiniteDimensional ℝ F] [Fintype ι] {R : Type u} [Ring R]
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
    ⟨fun b ↦ ⟨b, o b⟩, o.continuous_mk_cover hι⟩ fun _ ↦ rfl

@[simp]
theorem signLocalSystemIso_hom_app_apply (o : VectorBundleOrientation F E ι) (b : B)
    (f : (VectorBundleOrientationCover.signLocalSystem F E R hι).obj
      (FundamentalGroupoid.mk b)) :
    (ModuleCat.Hom.hom (B := ModuleCat.of R (ULift.{max uB uE uι} R))
        ((signLocalSystemIso hι o).hom.app (FundamentalGroupoid.mk b))) f =
      ULift.up (VectorBundleOrientationCover.signLocalSystemFiberEquiv hι (o b) f) := by
  rw [VectorBundleOrientationCover.signLocalSystemFiberEquiv_apply]
  exact IsCoveringMap.signLocalSystemIsoOfSection_hom_app_apply (X := TopCat.of B) _
    (hσ := VectorBundleOrientationCover.proj_comp_deck) VectorBundleOrientationCover.deck_ne_self
    (fun _ _ h ↦ VectorBundleOrientationCover.eq_or_eq_deck hι h)
    ⟨fun b ↦ ⟨b, o b⟩, o.continuous_mk_cover hι⟩ (fun _ ↦ rfl) (FundamentalGroupoid.mk b) f

/-- The inverse of the trivialization given by `o` sends `r` over `b` to the element of the fibre
whose evaluation at the orientation `o b` is `r`. -/
@[simp]
theorem signLocalSystemIso_inv_app_apply (o : VectorBundleOrientation F E ι) (b : B) (r : R) :
    (ModuleCat.Hom.hom (A := ModuleCat.of R (ULift.{max uB uE uι} R))
        ((signLocalSystemIso (R := R) hι o).inv.app (FundamentalGroupoid.mk b))) (ULift.up r) =
      (VectorBundleOrientationCover.signLocalSystemFiberEquiv hι (o b)).symm r := by
  apply (VectorBundleOrientationCover.signLocalSystemFiberEquiv hι (o b)).injective
  rw [LinearEquiv.apply_symm_apply, VectorBundleOrientationCover.signLocalSystemFiberEquiv_apply]
  exact IsCoveringMap.signLocalSystemIsoOfSection_inv_app_apply (X := TopCat.of B) _
    (hσ := VectorBundleOrientationCover.proj_comp_deck) VectorBundleOrientationCover.deck_ne_self
    (fun _ _ h ↦ VectorBundleOrientationCover.eq_or_eq_deck hι h)
    ⟨fun b ↦ ⟨b, o b⟩, o.continuous_mk_cover hι⟩ (fun _ ↦ rfl) (FundamentalGroupoid.mk b) r

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
