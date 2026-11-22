/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient.Sign.Tensor
public import TauCeti.Topology.Homotopy.Monodromy.Basic
public import TauCeti.Topology.IsLocalHomeomorph
public import TauCeti.Topology.VectorBundle.Orientation.Cover.Fiberwise

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

Over the base set of a trivialization of the atlas the system is trivialized without a global
orientation: transport along a path in the base set carries the element with value `r` at the
orientation read as a fixed orientation `ω` of the model fibre to the element with value `r` at the
orientation read as `ω` at the end of the path
(`TauCeti.VectorBundleOrientationCover.signLocalSystem_map_mk_signLocalSystemFiberEquiv_symm`).

Isomorphic bundles have isomorphic orientation local systems. A fibrewise isomorphism
`φ b : E'_b ≃ E_b` with continuous total-space map induces a map of orientation double covers
(`TauCeti.VectorBundleOrientationCover.map`) which commutes with the deck involutions and is
bijective on every fibre, so pulling functions on orientations back along it is an isomorphism
`o(E) ≅ o(E')` (`TauCeti.VectorBundleOrientationCover.signLocalSystemIsoOfFiberwise`, by
`IsCoveringMap.isIso_signLocalSystemMap`). Hence homology and cohomology twisted by the
orientation local system depend only on the isomorphism class of the bundle.

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
* `TauCeti.VectorBundleOrientationCover.signLocalSystemIsoOfFiberwise`: the isomorphism of
  orientation local systems induced by a fibrewise isomorphism of bundles.

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
  set cov := isCoveringMap_proj (F := F) (E := E) hι
  -- Lift the reversed path through the orientation read as `ω` at `y`; it stays in that sheet.
  let c₀ : (proj ⁻¹' {y} : Set (VectorBundleOrientationCover F E ι)) :=
    ⟨⟨y, (e.mapOrientation ι hy).symm ω⟩, rfl⟩
  have hc₀ : γ.symm 0 = proj c₀.val := by simp [c₀]
  let Γ := cov.liftPath γ.symm c₀.val hc₀
  have hΓ (t : unitInterval) : (Γ t).proj ∈ e.baseSet := by
    rw [show (Γ t).proj = γ.symm t from congrFun (cov.liftPath_lifts γ.symm c₀.val hc₀) t]
    exact hγ _
  have h₀ : Γ 0 ∈ sheet e ω := by
    rw [cov.liftPath_zero]
    exact mem_sheet_iff.2 ⟨hy, Equiv.apply_symm_apply _ _⟩
  let q : FundamentalGroupoid.mk (X := TopCat.of B) x ⟶ FundamentalGroupoid.mk y :=
    Path.Homotopic.Quotient.mk γ
  -- Transport along `q` evaluates at the endpoint of the lift of the reversed path.
  have hm : cov.monodromy (inv q) c₀ = ⟨⟨x, (e.mapOrientation ι hx).symm ω⟩, rfl⟩ := by
    have hmon : ((cov.monodromy (inv q) c₀ : _) : VectorBundleOrientationCover F E ι) = Γ 1 :=
      cov.coe_monodromy_inv_mk γ c₀
    have hsheet := mem_sheet_of_forall_proj_mem_baseSet hι e ω hΓ h₀ 1
    rw [← hmon] at hsheet
    obtain ⟨hm, hω⟩ := mem_sheet_iff.1 hsheet
    generalize cov.monodromy (inv q) c₀ = m at hm hω ⊢
    obtain ⟨⟨x', o'⟩, hx'⟩ := m
    obtain rfl : x' = x := hx'
    exact Subtype.ext (VectorBundleOrientationCover.ext rfl
      (heq_of_eq ((Equiv.eq_symm_apply _).2 hω)))
  apply (signLocalSystemFiberEquiv hι ((e.mapOrientation ι hy).symm ω)).injective
  rw [LinearEquiv.apply_symm_apply, signLocalSystemFiberEquiv_apply,
    signLocalSystemObjEquiv_map_apply, hm, ← signLocalSystemFiberEquiv_apply,
    LinearEquiv.apply_symm_apply]

section Fiberwise

/-! ### Isomorphic bundles -/

variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
  {E' : B → Type uE} [TopologicalSpace (TotalSpace F' E')] [∀ b, AddCommMonoid (E' b)]
  [∀ b, Module ℝ (E' b)] [∀ b, TopologicalSpace (E' b)] [FiberBundle F' E'] [VectorBundle ℝ F' E']
  {φ : ∀ b, E' b ≃L[ℝ] E b} (hι' : Fintype.card ι = finrank ℝ F')
  (hφ : Continuous fun v : TotalSpace F' E' ↦ TotalSpace.mk' F v.proj (φ v.proj v.snd))

omit [FiniteDimensional ℝ F] [FiniteDimensional ℝ F'] in
/-- Over the identity of the base, the map of orientation double covers induced by `φ` lies over
the base. -/
private theorem proj_comp_map :
    proj ∘ ⇑(map (g := ContinuousMap.id B) (φ := φ) hι' hφ) = proj :=
  funext (proj_map hι' hφ)

omit [FiniteDimensional ℝ F] [FiniteDimensional ℝ F'] in
/-- Over the identity of the base, the map of orientation double covers induced by `φ` commutes
with the deck involutions, as maps of the total spaces. -/
private theorem map_comp_deck :
    ⇑(map (g := ContinuousMap.id B) (φ := φ) hι' hφ) ∘
        ⇑(deck (F := F') (E := E') (ι := ι) : C(_, _)) =
      ⇑(deck (F := F) (E := E) (ι := ι) : C(_, _)) ∘ ⇑(map (g := ContinuousMap.id B) hι' hφ) :=
  funext (map_deck hι' hφ)

omit [FiniteDimensional ℝ F] in
include hι in
/-- Over the identity of the base, the map of orientation double covers induced by `φ` is
bijective on each fibre: each fibre is a pair of opposite orientations, and the map commutes with
reversing them. -/
private theorem bijective_fiberMap_map (b : B) :
    Function.Bijective (Function.fiberMap _ (proj_comp_map hι' hφ) b) := by
  refine ⟨fun p q hpq ↦ ?_, fun q ↦ ?_⟩
  · rcases eq_or_eq_deck hι' (p.property.trans q.property.symm) with h | h
    · exact Subtype.ext h
    · -- The images of `q` and of its opposite `deck q` cannot agree.
      have hpq' := congrArg Subtype.val hpq
      simp only [Function.fiberMap_apply_coe, h] at hpq'
      exact (deck_ne_self _ ((map_deck hι' hφ q.val).symm.trans hpq')).elim
  · obtain ⟨p, hp⟩ := surjective_proj hι' (F := F') (E := E') b
    have hmap : (map (g := ContinuousMap.id B) (φ := φ) hι' hφ p).proj = q.val.proj :=
      (proj_map hι' hφ p).trans (hp.trans q.property.symm)
    rcases eq_or_eq_deck hι hmap.symm with h | h
    · exact ⟨⟨p, hp⟩, Subtype.ext ((Function.fiberMap_apply_coe _ _ _ _).trans h.symm)⟩
    · refine ⟨⟨deck p, (proj_deck p).trans hp⟩, Subtype.ext ?_⟩
      exact (Function.fiberMap_apply_coe _ _ _ _).trans ((map_deck hι' hφ p).trans h.symm)

omit [FiniteDimensional ℝ F] in
variable (R) in
/-- **Isomorphic bundles have isomorphic orientation local systems.** A fibrewise isomorphism
`φ b : E'_b ≃ E_b` with continuous total-space map induces the isomorphism `o(E) ≅ o(E')` of
orientation local systems that pulls a function on the orientations of `E_b` back along the
transport of orientations by `φ b` (`TauCeti.VectorBundleOrientationCover.map`). -/
def signLocalSystemIsoOfFiberwise : signLocalSystem F E R hι ≅ signLocalSystem F' E' R hι' :=
  let α : signLocalSystem F E R hι ⟶ signLocalSystem F' E' R hι' :=
    (isCoveringMap_proj hι').signLocalSystemMap (isCoveringMap_proj hι) _ (proj_comp_map hι' hφ)
      (map_comp_deck hι' hφ)
  haveI : IsIso α := (isCoveringMap_proj hι').isIso_signLocalSystemMap (isCoveringMap_proj hι) _
    (proj_comp_map hι' hφ) (map_comp_deck hι' hφ) (bijective_fiberMap_map hι hι' hφ)
  asIso α

omit [FiniteDimensional ℝ F] in
/-- The isomorphism of orientation local systems induced by `φ` evaluates a function on the
orientations of `E_b` at the image under `φ b` of an orientation of `E'_b`. -/
@[simp]
theorem signLocalSystemObjEquiv_signLocalSystemIsoOfFiberwise_hom_app_apply
    (x : FundamentalGroupoid (TopCat.of B)) (f : (signLocalSystem F E R hι).obj x)
    (o : Orientation ℝ (E' x.as) ι) :
    (signLocalSystemObjEquiv hι' x
        (((signLocalSystemIsoOfFiberwise R hι hι' hφ).hom.app x).hom f) :
        (proj ⁻¹' {x.as} : Set (VectorBundleOrientationCover F' E' ι)) → R) ⟨⟨x.as, o⟩, rfl⟩ =
      (signLocalSystemObjEquiv hι x f :
        (proj ⁻¹' {x.as} : Set (VectorBundleOrientationCover F E ι)) → R)
        ⟨⟨x.as, Orientation.map ι (φ x.as).toLinearEquiv o⟩, rfl⟩ := by
  refine ((isCoveringMap_proj hι').signLocalSystemObjEquiv_signLocalSystemMap_app_apply
    (isCoveringMap_proj hι) _ (proj_comp_map hι' hφ) (map_comp_deck hι' hφ) x f _).trans ?_
  -- The fibres of `o(E)` are by definition those of the sign local system of the cover.
  refine congrArg ((isCoveringMap_proj hι).signLocalSystemObjEquiv _ proj_comp_deck x f).val
    (Subtype.ext ?_)
  rw [Function.fiberMap_apply_coe]
  exact map_mk (g := ContinuousMap.id B) (φ := φ) hι' hφ x.as o

omit [FiniteDimensional ℝ F] in
/-- The inverse of the isomorphism of orientation local systems induced by `φ` pushes a function
on the orientations of `E'_b` forward along the transport of orientations by `φ b`: its value at
the image under `φ b` of an orientation of `E'_b` is the original value there. -/
@[simp]
theorem signLocalSystemObjEquiv_signLocalSystemIsoOfFiberwise_inv_app_apply
    (x : FundamentalGroupoid (TopCat.of B)) (f : (signLocalSystem F' E' R hι').obj x)
    (o : Orientation ℝ (E' x.as) ι) :
    (signLocalSystemObjEquiv hι x
        (((signLocalSystemIsoOfFiberwise R hι hι' hφ).inv.app x).hom f) :
        (proj ⁻¹' {x.as} : Set (VectorBundleOrientationCover F E ι)) → R)
        ⟨⟨x.as, Orientation.map ι (φ x.as).toLinearEquiv o⟩, rfl⟩ =
      (signLocalSystemObjEquiv hι' x f :
        (proj ⁻¹' {x.as} : Set (VectorBundleOrientationCover F' E' ι)) → R) ⟨⟨x.as, o⟩, rfl⟩ := by
  rw [← signLocalSystemObjEquiv_signLocalSystemIsoOfFiberwise_hom_app_apply (hφ := hφ) (o := o),
    ← ModuleCat.comp_apply, Iso.inv_hom_id_app, ModuleCat.id_apply]

end Fiberwise

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
