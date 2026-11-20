/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CWComplex.Classical.Pushout
public import TauCeti.Topology.CWComplex.Classical.ULift
public import TauCeti.Topology.VectorBundle.SphereBundle.CWComplex
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.Topology.Category.TopCat.ULift
import TauCeti.Topology.Category.TopCat.ClosedEmbedding
import TauCeti.Topology.CWComplex.Classical.Basic
import TauCeti.Topology.FiberBundle.Separation
import TauCeti.Topology.Homotopy.HomotopyEquiv

/-!
# Relative CW models of disc-bundle attachments

Let `E → X` be a continuous Riemannian vector bundle of rank `r` over a Hausdorff space `X` carrying
a classical CW structure, and let `g : S(E) → Z` be a continuous attaching map from the unit sphere
bundle of `E` into an arbitrary topological space `Z`. Gluing the unit disc bundle `D(E)` to `Z`
along `g` produces the adjunction space `Z ∪_g D(E)` (`TauCeti.bundleDiskAttachmentSpace`), the
geometric building block of negative-disc bundle attachments in Morse–Bott theory and of Thom spaces
when `Z` is a point.

This file puts a classical relative CW structure `TauCeti.bundleDiskAttachmentCWModel` on
`Z ∪_g D(E)` relative to the embedded image of `Z`, without assuming any CW structure on `Z`:

* `TauCeti.bundleSphereRelCWBaseHomeomorph` and `TauCeti.bundleSphereBaseAttachingMap`: the
  canonical homeomorphism from the `A = ∅` relative base subtype
  `↥(Subtype.val ⁻¹' S(E) ∪ π_D ⁻¹' ∅)` in `D(E)` onto `S(E)`, together with the transport of
  attaching maps `g : S(E) → Z` along it;
* `TauCeti.bundleDiskSphereRelCWUlift`: universe-polymorphic lift of `TauCeti.bundleDiskSphereRelCW`
  to `ULift.{v, u} (discBundle F E)` so that `D(E) : Type u` and `Z : Type v` can live in
  independent universes;
* `TauCeti.bundleDiskRelAttachmentSpace` and `TauCeti.bundleDiskRelAttachmentCWModel`: the general
  relative attachment `Z ∪_g D(E)` along a map `g` defined on `S(E) ∪ D(E)|_A` over a relative CW
  pair `(X, A)`, together with its universe-polymorphic pushout universal property
  (`TauCeti.bundleDiskRelAttachmentDesc`, `TauCeti.bundleDiskRelAttachmentSpace_continuousMap_ext`,
  `TauCeti.isClosed_iff_bundleDiskRelAttachmentSpace`), closed base embedding
  `TauCeti.isClosedEmbedding_bundleDiskRelAttachmentInr`, Hausdorffness over Hausdorff `Z`,
  `(q + r)`-cell correspondence (`TauCeti.bundleDiskRelAttachmentCellEquiv`), cell-set formulas,
  finiteness preservation, and universe-polymorphic homotopy invariance in `Z`
  (`TauCeti.exists_homotopyEquiv_bundleDiskRelAttachmentSpace`);
* `TauCeti.bundleDiskAttachmentSpace` and `TauCeti.bundleDiskAttachmentCWModel`: the `A = ∅`
  specialization for a continuous map `g : S(E) → Z` over a Hausdorff CW complex `X`, with its
  pushout universal property (`TauCeti.bundleDiskAttachmentDesc`,
  `TauCeti.bundleDiskAttachmentSpace_continuousMap_ext`,
  `TauCeti.isClosed_iff_bundleDiskAttachmentSpace`), cell equivalence
  (`TauCeti.bundleDiskAttachmentCellEquiv`), characteristic-map and cell-set formulas, finiteness
  preservation, and universe-polymorphic homotopy invariance in `Z`
  (`TauCeti.exists_homotopyEquiv_bundleDiskAttachmentSpace`).

## References

* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §18.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Chapter 0 and
  §4.D.
* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics **60** (1954), 248–261.
-/

public section

noncomputable section

open Bundle CategoryTheory ContinuousMap Limits Metric Set Topology Topology.RelCWComplex

universe u v w

namespace TauCeti

/-! ### Homeomorphism between the `A = ∅` relative base subtype and `S(E)` -/

section BaseHomeomorph

variable {X : Type u} [TopologicalSpace X]
  (F : Type*) [TopologicalSpace F]
  (E : X → Type u) [TopologicalSpace (TotalSpace F E)]
  [∀ x, NormedAddCommGroup (E x)] [FiberBundle F E]

/-- **Homeomorphism from the `A = ∅` relative base of `D(E)` to `S(E)`.** The forward map forgets
the unit-disc bound `‖v‖ ≤ 1`; the inverse uses `‖v‖ = 1 ⇒ ‖v‖ ≤ 1` and injects into the sphere
summand of `Subtype.val ⁻¹' S(E) ∪ π_D ⁻¹' ∅`. -/
def bundleSphereRelCWBaseHomeomorph :
    ↥(Subtype.val ⁻¹' sphereBundle F E ∪ discBundleProj F E ⁻¹' (∅ : Set X)) ≃ₜ
      sphereBundle F E where
  toFun x := ⟨x.val.val, x.property.elim id False.elim⟩
  invFun s := ⟨⟨s.val, mem_discBundle.2 (mem_sphereBundle.1 s.property).le⟩, Or.inl s.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtypeVal.comp continuous_subtypeVal).subtype_mk _
  continuous_invFun := (continuous_subtypeVal.subtype_mk _).subtype_mk _

theorem coe_bundleSphereRelCWBaseHomeomorph_apply
    (x : ↥(Subtype.val ⁻¹' sphereBundle F E ∪ discBundleProj F E ⁻¹' (∅ : Set X))) :
    (bundleSphereRelCWBaseHomeomorph F E x : TotalSpace F E) = x.val.val :=
  (rfl)

theorem coe_bundleSphereRelCWBaseHomeomorph_symm_apply (s : sphereBundle F E) :
    ((bundleSphereRelCWBaseHomeomorph F E).symm s : discBundle F E) =
      ⟨s.val, mem_discBundle.2 (mem_sphereBundle.1 s.property).le⟩ :=
  (rfl)

/-- Transport an attaching map `g : S(E) → Z` along `bundleSphereRelCWBaseHomeomorph` to the
literal `A = ∅` relative base `Subtype.val ⁻¹' S(E) ∪ π_D ⁻¹' ∅` of `bundleDiskSphereRelCW`. -/
def bundleSphereBaseAttachingMap {Z : Type v} [TopologicalSpace Z]
    (g : C(sphereBundle F E, Z)) :
    C(↥(Subtype.val ⁻¹' sphereBundle F E ∪ discBundleProj F E ⁻¹' (∅ : Set X)), Z) :=
  g.comp (bundleSphereRelCWBaseHomeomorph F E)

theorem bundleSphereBaseAttachingMap_apply {Z : Type v} [TopologicalSpace Z]
    (g : C(sphereBundle F E, Z))
    (x : ↥(Subtype.val ⁻¹' sphereBundle F E ∪ discBundleProj F E ⁻¹' (∅ : Set X))) :
    bundleSphereBaseAttachingMap F E g x = g (bundleSphereRelCWBaseHomeomorph F E x) :=
  (rfl)

end BaseHomeomorph

/-! ### Relative disc-bundle attachment along `S(E) ∪ D(E)|_A` -/

section RelAttachment

variable {X : Type u} [TopologicalSpace X] [T2Space X]
  (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  (E : X → Type u) [TopologicalSpace (TotalSpace F E)]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E]
  (A : Set X) [RelCWComplex (univ : Set X) A] {r : ℕ} (hr : Module.finrank ℝ F = r)

/-- **Universe lift of `bundleDiskSphereRelCW`.** Lifting `discBundle F E : Type u` to
`ULift.{v, u} (discBundle F E) : Type (max u v)` transports `bundleDiskSphereRelCW` with unchanged
cell dimensions and characteristic maps composed with `ULift.up`. -/
abbrev bundleDiskSphereRelCWUlift :
    RelCWComplex (univ : Set (ULift.{v, u} (discBundle F E)))
      (ULift.down ⁻¹' (Subtype.val ⁻¹' sphereBundle F E ∪ discBundleProj F E ⁻¹' A)) :=
  @Topology.RelCWComplex.ulift.{v, u} (discBundle F E) _ univ _ (bundleDiskSphereRelCW F E A hr)

private def liftedRelAttachingMap {Z : Type v} [TopologicalSpace Z]
    (g : C(↥(Subtype.val ⁻¹' sphereBundle F E ∪ discBundleProj F E ⁻¹' A), Z)) :
    C(↥(ULift.down ⁻¹' (Subtype.val ⁻¹' sphereBundle F E ∪ discBundleProj F E ⁻¹' A) :
        Set (ULift.{v, u} (discBundle F E))),
      ULift.{u, v} Z) :=
  ⟨fun x ↦ ULift.up (g ⟨x.val.down, x.property⟩),
    continuous_uliftUp.comp
      (g.continuous.comp ((continuous_uliftDown.comp continuous_subtypeVal).subtype_mk _))⟩

variable {Z : Type v} [TopologicalSpace Z]
  (g : C(↥(Subtype.val ⁻¹' sphereBundle F E ∪ discBundleProj F E ⁻¹' A), Z))

/-- The adjunction space `Z ∪_g D(E)` obtained by attaching `D(E)` to `Z` along a continuous map
`g : S(E) ∪ D(E)|_A → Z`, constructed in the common universe `max u v`. -/
def bundleDiskRelAttachmentSpace : TopCat.{max u v} :=
  letI := bundleDiskSphereRelCWUlift.{u, v} F E A hr
  relCWAdjunctionSpace (univ : Set (ULift.{v, u} (discBundle F E)))
    (liftedRelAttachingMap F E A g)

/-- The canonical inclusion `Z → Z ∪_g D(E)` into the relative disc-bundle attachment. -/
def bundleDiskRelAttachmentInr : C(Z, bundleDiskRelAttachmentSpace F E A hr g) :=
  letI := bundleDiskSphereRelCWUlift.{u, v} F E A hr
  (pushout.inr
    (relCWBaseInclusion (univ : Set (ULift.{v, u} (discBundle F E))))
    (TopCat.ofHom (liftedRelAttachingMap F E A g))).hom.comp
    ⟨ULift.up, continuous_uliftUp⟩

/-- The canonical characteristic-side map `D(E) → Z ∪_g D(E)` into the relative disc-bundle
attachment. -/
def bundleDiskRelAttachmentInl : C(discBundle F E, bundleDiskRelAttachmentSpace F E A hr g) :=
  letI := bundleDiskSphereRelCWUlift.{u, v} F E A hr
  (pushout.inl
    (relCWBaseInclusion (univ : Set (ULift.{v, u} (discBundle F E))))
    (TopCat.ofHom (liftedRelAttachingMap F E A g))).hom.comp
    ⟨fun v ↦ ⟨ULift.up v, mem_univ _⟩, continuous_uliftUp.subtype_mk _⟩

private lemma bundleDiskRelAttachmentInl_apply (v : discBundle F E) :
    bundleDiskRelAttachmentInl F E A hr g v =
      letI := bundleDiskSphereRelCWUlift.{u, v} F E A hr
      pushout.inl (relCWBaseInclusion (univ : Set (ULift.{v, u} (discBundle F E))))
        (TopCat.ofHom (liftedRelAttachingMap F E A g)) ⟨ULift.up v, mem_univ _⟩ :=
  rfl

/-- On the relative base `S(E) ∪ D(E)|_A`, `bundleDiskRelAttachmentInl` agrees with
`bundleDiskRelAttachmentInr ∘ g`. -/
theorem bundleDiskRelAttachmentInl_eq_inr
    (b : ↥(Subtype.val ⁻¹' sphereBundle F E ∪ discBundleProj F E ⁻¹' A)) :
    bundleDiskRelAttachmentInl F E A hr g b.val =
      bundleDiskRelAttachmentInr F E A hr g (g b) :=
  letI := bundleDiskSphereRelCWUlift.{u, v} F E A hr
  ConcreteCategory.congr_hom
    (pushout.condition
      (f := relCWBaseInclusion (univ : Set (ULift.{v, u} (discBundle F E))))
      (g := TopCat.ofHom (liftedRelAttachingMap F E A g)))
    ⟨ULift.up b.val, b.property⟩

private def bundleDiskRelAttachmentDescLeft {W : Type w} [TopologicalSpace W]
    (f : C(discBundle F E, W)) :
    TopCat.uliftFunctor.{w, max u v}.obj
        (TopCat.of (univ : Set (ULift.{v, u} (discBundle F E)))) ⟶
      TopCat.of (ULift.{max u v, w} W) :=
  TopCat.ofHom ⟨fun x ↦ ULift.up (f ((TopCat.uliftFunctorObjHomeo _).symm x).val.down),
    continuous_uliftUp.comp (f.continuous.comp
      (continuous_uliftDown.comp
        (continuous_subtypeVal.comp (TopCat.uliftFunctorObjHomeo _).symm.continuous)))⟩

private def bundleDiskRelAttachmentDescRight {W : Type w} [TopologicalSpace W] (h : C(Z, W)) :
    TopCat.uliftFunctor.{w, max u v}.obj (TopCat.of (ULift.{u, v} Z)) ⟶
      TopCat.of (ULift.{max u v, w} W) :=
  TopCat.ofHom ⟨fun x ↦ ULift.up (h ((TopCat.uliftFunctorObjHomeo _).symm x).down),
    continuous_uliftUp.comp (h.continuous.comp
      (continuous_uliftDown.comp (TopCat.uliftFunctorObjHomeo _).symm.continuous))⟩

private lemma bundleDiskRelAttachmentDesc_compat {W : Type w} [TopologicalSpace W]
    (f : C(discBundle F E, W)) (h : C(Z, W)) (hfg : ∀ b, f b.val = h (g b)) :
    letI := bundleDiskSphereRelCWUlift.{u, v} F E A hr
    TopCat.uliftFunctor.{w, max u v}.map
        (relCWBaseInclusion (univ : Set (ULift.{v, u} (discBundle F E)))) ≫
        bundleDiskRelAttachmentDescLeft.{u, v, w} F E f =
      TopCat.uliftFunctor.{w, max u v}.map (TopCat.ofHom (liftedRelAttachingMap F E A g)) ≫
        bundleDiskRelAttachmentDescRight.{u, v, w} h := by
  let _ := bundleDiskSphereRelCWUlift.{u, v} F E A hr
  ext x
  let y := (TopCat.uliftFunctorObjHomeo.{w} _).symm x
  have h1 := TopCat.uliftFunctorObjHomeo_symm_naturality_apply.{w}
    (relCWBaseInclusion (univ : Set (ULift.{v, u} (discBundle F E)))) x
  have h2 := TopCat.uliftFunctorObjHomeo_symm_naturality_apply.{w}
    (TopCat.ofHom (liftedRelAttachingMap F E A g)) x
  have hL :
      (TopCat.uliftFunctor.{w, max u v}.map
          (relCWBaseInclusion (univ : Set (ULift.{v, u} (discBundle F E)))) ≫
          bundleDiskRelAttachmentDescLeft.{u, v, w} F E f) x =
        ULift.up (f y.val.down) := by
    rw [ConcreteCategory.comp_apply]
    exact congrArg (fun p : (univ : Set (ULift.{v, u} (discBundle F E))) ↦ ULift.up (f p.val.down))
      h1
  have hR :
      (TopCat.uliftFunctor.{w, max u v}.map (TopCat.ofHom (liftedRelAttachingMap F E A g)) ≫
          bundleDiskRelAttachmentDescRight.{u, v, w} h) x =
        ULift.up (h (g ⟨y.val.down, y.property⟩)) := by
    rw [ConcreteCategory.comp_apply]
    exact congrArg (fun z : ULift.{u, v} Z ↦ ULift.up (h z.down)) h2
  exact congrArg ULift.down
    (hL.trans <| (congrArg ULift.up (hfg ⟨y.val.down, y.property⟩)).trans hR.symm)

/-- **Pushout eliminator for `bundleDiskRelAttachmentSpace`.** Compatible continuous maps out of
`D(E)` and `Z` into a space `W` in an arbitrary universe descend uniquely to a continuous map
`Z ∪_g D(E) → W`. -/
def bundleDiskRelAttachmentDesc {W : Type w} [TopologicalSpace W]
    (f : C(discBundle F E, W)) (h : C(Z, W)) (hfg : ∀ b, f b.val = h (g b)) :
    C(bundleDiskRelAttachmentSpace F E A hr g, W) :=
  letI := bundleDiskSphereRelCWUlift.{u, v} F E A hr
  let sq := IsPushout.of_hasPushout
    (relCWBaseInclusion (univ : Set (ULift.{v, u} (discBundle F E))))
    (TopCat.ofHom (liftedRelAttachingMap F E A g))
  let dW := (sq.map TopCat.uliftFunctor.{w, max u v}).desc
    (bundleDiskRelAttachmentDescLeft.{u, v, w} F E f)
    (bundleDiskRelAttachmentDescRight.{u, v, w} h)
    (bundleDiskRelAttachmentDesc_compat.{u, v, w} F E A hr g f h hfg)
  let eP := TopCat.uliftFunctorObjHomeo.{w}
    (pushout (relCWBaseInclusion (univ : Set (ULift.{v, u} (discBundle F E))))
      (TopCat.ofHom (liftedRelAttachingMap F E A g)))
  (⟨ULift.down, continuous_uliftDown⟩ : C(ULift.{max u v, w} W, W)).comp <|
    dW.hom.comp ⟨eP, eP.continuous⟩

@[simp]
theorem bundleDiskRelAttachmentDesc_inl {W : Type w} [TopologicalSpace W]
    (f : C(discBundle F E, W)) (h : C(Z, W)) (hfg : ∀ b, f b.val = h (g b)) (v : discBundle F E) :
    bundleDiskRelAttachmentDesc F E A hr g f h hfg (bundleDiskRelAttachmentInl F E A hr g v) =
      f v := by
  let _ := bundleDiskSphereRelCWUlift.{u, v} F E A hr
  let sq := IsPushout.of_hasPushout
    (relCWBaseInclusion (univ : Set (ULift.{v, u} (discBundle F E))))
    (TopCat.ofHom (liftedRelAttachingMap F E A g))
  have hcomp := ConcreteCategory.congr_hom
    ((sq.map TopCat.uliftFunctor.{w, max u v}).inl_desc
      (bundleDiskRelAttachmentDescLeft.{u, v, w} F E f)
      (bundleDiskRelAttachmentDescRight.{u, v, w} h)
      (bundleDiskRelAttachmentDesc_compat.{u, v, w} F E A hr g f h hfg))
    (TopCat.uliftFunctorObjHomeo.{w} (TopCat.of (univ : Set (ULift.{v, u} (discBundle F E))))
      ⟨ULift.up v, mem_univ _⟩)
  have hnat := TopCat.uliftFunctorObjHomeo_naturality_apply.{w}
    (pushout.inl (relCWBaseInclusion (univ : Set (ULift.{v, u} (discBundle F E))))
      (TopCat.ofHom (liftedRelAttachingMap F E A g)))
    ⟨ULift.up v, mem_univ _⟩
  rw [ConcreteCategory.comp_apply, hnat] at hcomp
  have hval :
      bundleDiskRelAttachmentDesc F E A hr g f h hfg (bundleDiskRelAttachmentInl F E A hr g v) =
        f ((TopCat.uliftFunctorObjHomeo.{w}
            (TopCat.of (univ : Set (ULift.{v, u} (discBundle F E))))).symm
          (TopCat.uliftFunctorObjHomeo.{w}
            (TopCat.of (univ : Set (ULift.{v, u} (discBundle F E))))
            ⟨ULift.up v, mem_univ _⟩)).val.down :=
    congrArg ULift.down hcomp
  rwa [Homeomorph.symm_apply_apply] at hval

@[simp]
theorem bundleDiskRelAttachmentDesc_inr {W : Type w} [TopologicalSpace W]
    (f : C(discBundle F E, W)) (h : C(Z, W)) (hfg : ∀ b, f b.val = h (g b)) (z : Z) :
    bundleDiskRelAttachmentDesc F E A hr g f h hfg (bundleDiskRelAttachmentInr F E A hr g z) =
      h z := by
  let _ := bundleDiskSphereRelCWUlift.{u, v} F E A hr
  let sq := IsPushout.of_hasPushout
    (relCWBaseInclusion (univ : Set (ULift.{v, u} (discBundle F E))))
    (TopCat.ofHom (liftedRelAttachingMap F E A g))
  have hcomp := ConcreteCategory.congr_hom
    ((sq.map TopCat.uliftFunctor.{w, max u v}).inr_desc
      (bundleDiskRelAttachmentDescLeft.{u, v, w} F E f)
      (bundleDiskRelAttachmentDescRight.{u, v, w} h)
      (bundleDiskRelAttachmentDesc_compat.{u, v, w} F E A hr g f h hfg))
    (TopCat.uliftFunctorObjHomeo.{w} (TopCat.of (ULift.{u, v} Z)) (ULift.up z))
  have hnat := TopCat.uliftFunctorObjHomeo_naturality_apply.{w}
    (pushout.inr (relCWBaseInclusion (univ : Set (ULift.{v, u} (discBundle F E))))
      (TopCat.ofHom (liftedRelAttachingMap F E A g)))
    (ULift.up z)
  rw [ConcreteCategory.comp_apply, hnat] at hcomp
  have hval :
      bundleDiskRelAttachmentDesc F E A hr g f h hfg (bundleDiskRelAttachmentInr F E A hr g z) =
        h ((TopCat.uliftFunctorObjHomeo.{w} (TopCat.of (ULift.{u, v} Z))).symm
          (TopCat.uliftFunctorObjHomeo.{w} (TopCat.of (ULift.{u, v} Z)) (ULift.up z))).down :=
    congrArg ULift.down hcomp
  rwa [Homeomorph.symm_apply_apply] at hval

@[simp]
theorem bundleDiskRelAttachmentDesc_comp_inl {W : Type w} [TopologicalSpace W]
    (f : C(discBundle F E, W)) (h : C(Z, W)) (hfg : ∀ b, f b.val = h (g b)) :
    (bundleDiskRelAttachmentDesc F E A hr g f h hfg).comp
      (bundleDiskRelAttachmentInl F E A hr g) = f :=
  ContinuousMap.ext (bundleDiskRelAttachmentDesc_inl F E A hr g f h hfg)

@[simp]
theorem bundleDiskRelAttachmentDesc_comp_inr {W : Type w} [TopologicalSpace W]
    (f : C(discBundle F E, W)) (h : C(Z, W)) (hfg : ∀ b, f b.val = h (g b)) :
    (bundleDiskRelAttachmentDesc F E A hr g f h hfg).comp
      (bundleDiskRelAttachmentInr F E A hr g) = h :=
  ContinuousMap.ext (bundleDiskRelAttachmentDesc_inr F E A hr g f h hfg)

/-- Every point of `Z ∪_g D(E)` lies in the image of `D(E)` or in the image of `Z`. -/
theorem exists_bundleDiskRelAttachmentInl_or_inr (p : bundleDiskRelAttachmentSpace F E A hr g) :
    (∃ v : discBundle F E, bundleDiskRelAttachmentInl F E A hr g v = p) ∨
      ∃ z : Z, bundleDiskRelAttachmentInr F E A hr g z = p := by
  let _ := bundleDiskSphereRelCWUlift.{u, v} F E A hr
  have h := Types.eq_or_eq_of_isPushout
    ((forget TopCat).map_isPushout
      (IsPushout.of_hasPushout
        (relCWBaseInclusion (univ : Set (ULift.{v, u} (discBundle F E))))
        (TopCat.ofHom (liftedRelAttachingMap F E A g)))) p
  rcases h with ⟨⟨⟨v⟩, _⟩, rfl⟩ | ⟨⟨z⟩, rfl⟩
  · exact Or.inl ⟨v, rfl⟩
  · exact Or.inr ⟨z, rfl⟩

/-- Induction principle on points of `Z ∪_g D(E)` by splitting into the images of `D(E)` and
`Z`. -/
@[elab_as_elim]
theorem bundleDiskRelAttachmentSpace_induction_on
    {P : bundleDiskRelAttachmentSpace F E A hr g → Prop}
    (p : bundleDiskRelAttachmentSpace F E A hr g)
    (hl : ∀ v, P (bundleDiskRelAttachmentInl F E A hr g v))
    (hr' : ∀ z, P (bundleDiskRelAttachmentInr F E A hr g z)) : P p := by
  rcases exists_bundleDiskRelAttachmentInl_or_inr F E A hr g p with ⟨v, rfl⟩ | ⟨z, rfl⟩
  · exact hl v
  · exact hr' z

/-- The ranges of `bundleDiskRelAttachmentInl` and `bundleDiskRelAttachmentInr` cover
`Z ∪_g D(E)`. -/
theorem range_bundleDiskRelAttachmentInl_union_range_inr :
    range (bundleDiskRelAttachmentInl F E A hr g) ∪
      range (bundleDiskRelAttachmentInr F E A hr g) = univ :=
  eq_univ_of_forall fun p ↦ exists_bundleDiskRelAttachmentInl_or_inr F E A hr g p

/-- Two continuous maps out of `Z ∪_g D(E)` agree as soon as they agree on the images of `D(E)`
and `Z`. -/
theorem bundleDiskRelAttachmentSpace_continuousMap_ext {W : Type w} [TopologicalSpace W]
    {f₁ f₂ : C(bundleDiskRelAttachmentSpace F E A hr g, W)}
    (hl : ∀ v, f₁ (bundleDiskRelAttachmentInl F E A hr g v) =
      f₂ (bundleDiskRelAttachmentInl F E A hr g v))
    (hr' : ∀ z, f₁ (bundleDiskRelAttachmentInr F E A hr g z) =
      f₂ (bundleDiskRelAttachmentInr F E A hr g z)) : f₁ = f₂ :=
  ContinuousMap.ext fun p ↦ bundleDiskRelAttachmentSpace_induction_on F E A hr g p hl hr'

/-- A subset of `Z ∪_g D(E)` is closed if and only if its preimages in `D(E)` and in `Z` are both
closed. -/
theorem isClosed_iff_bundleDiskRelAttachmentSpace
    (s : Set (bundleDiskRelAttachmentSpace F E A hr g)) :
    IsClosed s ↔
      IsClosed (bundleDiskRelAttachmentInl F E A hr g ⁻¹' s) ∧
        IsClosed (bundleDiskRelAttachmentInr F E A hr g ⁻¹' s) := by
  let _ := bundleDiskSphereRelCWUlift.{u, v} F E A hr
  let sq := IsPushout.of_hasPushout
    (relCWBaseInclusion (univ : Set (ULift.{v, u} (discBundle F E))))
    (TopCat.ofHom (liftedRelAttachingMap F E A g))
  let eL : discBundle F E ≃ₜ (univ : Set (ULift.{v, u} (discBundle F E))) :=
    (Homeomorph.ulift.{v, u}).symm.trans (Homeomorph.Set.univ _).symm
  let eR : Z ≃ₜ ULift.{u, v} Z := (Homeomorph.ulift.{u, v}).symm
  exact (TauCeti.TopCat.isClosed_iff_of_isPushout sq s).trans <| by
    rw [← eL.isClosed_preimage, ← eR.isClosed_preimage]
    rfl

/-- The canonical map `Z → Z ∪_g D(E)` is a closed embedding. -/
theorem isClosedEmbedding_bundleDiskRelAttachmentInr :
    IsClosedEmbedding (bundleDiskRelAttachmentInr F E A hr g) :=
  letI := bundleDiskSphereRelCWUlift.{u, v} F E A hr
  (isClosedEmbedding_pushout_inr_relCWBaseInclusion
    (C := (univ : Set (ULift.{v, u} (discBundle F E))))
    (liftedRelAttachingMap F E A g)).comp (Homeomorph.ulift.{u, v} (X := Z)).symm.isClosedEmbedding

/-- When `Z` is Hausdorff, the relative disc-bundle attachment `Z ∪_g D(E)` is Hausdorff. -/
instance t2Space_bundleDiskRelAttachmentSpace [T2Space Z] :
    T2Space (bundleDiskRelAttachmentSpace F E A hr g) :=
  letI := bundleDiskSphereRelCWUlift.{u, v} F E A hr
  t2Space_relCWAdjunctionSpace (C := (univ : Set (ULift.{v, u} (discBundle F E))))
    (liftedRelAttachingMap F E A g)

private lemma range_bundleDiskRelAttachmentInr :
    letI := bundleDiskSphereRelCWUlift.{u, v} F E A hr
    range (pushout.inr
        (relCWBaseInclusion (univ : Set (ULift.{v, u} (discBundle F E))))
        (TopCat.ofHom (liftedRelAttachingMap F E A g))) =
      range (bundleDiskRelAttachmentInr F E A hr g) := by
  ext p
  simp only [mem_range, bundleDiskRelAttachmentInr, ULift.exists]
  rfl

/-- **Classical relative CW model of a relative disc-bundle attachment.** Attaching `D(E)` to `Z`
along `g : S(E) ∪ D(E)|_A → Z` equips `Z ∪_g D(E)` with a classical relative CW structure relative
to the image of `Z`, with one `(q + r)`-cell for each relative `q`-cell of `(X, A)`. -/
@[instance_reducible]
def bundleDiskRelAttachmentCWModel :
    RelCWComplex (univ : Set (bundleDiskRelAttachmentSpace F E A hr g))
      (range (bundleDiskRelAttachmentInr F E A hr g)) :=
  letI := bundleDiskSphereRelCWUlift.{u, v} F E A hr
  (relativeCWPushout (univ : Set (ULift.{v, u} (discBundle F E)))
    (liftedRelAttachingMap F E A g)).copy univ
    (range (bundleDiskRelAttachmentInr F E A hr g)) rfl
    (range_bundleDiskRelAttachmentInr F E A hr g)

/-- Raw cell equivalence in every dimension `n` between `bundleDiskRelAttachmentCWModel` and
`bundleDiskSphereRelCW`. -/
private def bundleDiskRelAttachmentRawCellEquiv (n : ℕ) :
    @RelCWComplex.cell _ _ _ _ (bundleDiskRelAttachmentCWModel F E A hr g) n ≃
      @RelCWComplex.cell _ _ _ _ (bundleDiskSphereRelCW F E A hr) n :=
  letI := bundleDiskSphereRelCWUlift.{u, v} F E A hr
  (((relativeCWPushout (univ : Set (ULift.{v, u} (discBundle F E)))
    (liftedRelAttachingMap F E A g)).copyCellEquiv univ
      (range (bundleDiskRelAttachmentInr F E A hr g)) rfl
      (range_bundleDiskRelAttachmentInr F E A hr g) n).trans
    (relativeCWPushoutCellEquiv (univ : Set (ULift.{v, u} (discBundle F E)))
      (liftedRelAttachingMap F E A g) n)).trans
    (@uliftCellEquiv.{v, u} (discBundle F E) _ univ _ (bundleDiskSphereRelCW F E A hr) n)

/-- The `(q + r)`-cells of `Z ∪_g D(E)` correspond bijectively to the relative `q`-cells of
`(X, A)`. -/
def bundleDiskRelAttachmentCellEquiv (q : ℕ) :
    @RelCWComplex.cell _ _ _ _ (bundleDiskRelAttachmentCWModel F E A hr g)
        (thomCellDimension r q) ≃
      cell (univ : Set X) q :=
  (bundleDiskRelAttachmentRawCellEquiv F E A hr g (thomCellDimension r q)).trans
    (bundleDiskSphereCellEquiv F E A hr q)

/-- Below the fibre rank `r`, `bundleDiskRelAttachmentCWModel` has no `n`-cells. -/
theorem isEmpty_cell_bundleDiskRelAttachmentCWModel_of_lt {n : ℕ} (hn : n < r) :
    IsEmpty (@RelCWComplex.cell _ _ _ _ (bundleDiskRelAttachmentCWModel F E A hr g) n) :=
  have := isEmpty_cell_bundleDiskSphereRelCW_of_lt F E A hr hn
  (bundleDiskRelAttachmentRawCellEquiv F E A hr g n).isEmpty_congr.2 inferInstance

/-- Each characteristic map of `bundleDiskRelAttachmentCWModel` is the corresponding characteristic
map of `bundleDiskSphereRelCW` in `D(E)` followed by `bundleDiskRelAttachmentInl`. -/
theorem bundleDiskRelAttachmentCWModel_map_apply (q : ℕ)
    (i : @RelCWComplex.cell _ _ _ _ (bundleDiskRelAttachmentCWModel F E A hr g)
      (thomCellDimension r q))
    {x : Fin (thomCellDimension r q) → ℝ} (hx : x ∈ closedBall 0 1) :
    @RelCWComplex.map _ _ _ _ (bundleDiskRelAttachmentCWModel F E A hr g)
        (thomCellDimension r q) i x =
      bundleDiskRelAttachmentInl F E A hr g
        (@RelCWComplex.map _ _ _ _ (bundleDiskSphereRelCW F E A hr) (thomCellDimension r q)
          ((bundleDiskSphereCellEquiv F E A hr q).symm
            (bundleDiskRelAttachmentCellEquiv F E A hr g q i)) x) := by
  let _ := bundleDiskSphereRelCWUlift.{u, v} F E A hr
  let _ := relativeCWPushout (univ : Set (ULift.{v, u} (discBundle F E)))
    (liftedRelAttachingMap F E A g)
  have hcopy := (relativeCWPushout (univ : Set (ULift.{v, u} (discBundle F E)))
    (liftedRelAttachingMap F E A g)).map_copy univ
      (range (bundleDiskRelAttachmentInr F E A hr g)) rfl
      (range_bundleDiskRelAttachmentInr F E A hr g) (thomCellDimension r q) i
  refine (congrArg (fun f : PartialEquiv _ _ ↦ f x) hcopy).trans ?_
  refine (relativeCWPushout_map_apply
    (C := (univ : Set (ULift.{v, u} (discBundle F E))))
    (a := liftedRelAttachingMap F E A g) (thomCellDimension r q) _ ⟨x, hx⟩).trans ?_
  rw [bundleDiskRelAttachmentInl_apply]
  congr 1
  apply Subtype.ext
  refine (congrFun (@coe_map_ulift.{v, u} (discBundle F E) _ univ _
    (bundleDiskSphereRelCW F E A hr) (thomCellDimension r q) _) x).trans ?_
  exact congrArg
    (fun c ↦ ULift.up
      (@RelCWComplex.map _ _ _ _ (bundleDiskSphereRelCW F E A hr) (thomCellDimension r q) c x))
    ((bundleDiskSphereCellEquiv F E A hr q).symm_apply_apply
      (bundleDiskRelAttachmentRawCellEquiv F E A hr g (thomCellDimension r q) i)).symm

/-- The open `(q + r)`-cell of `bundleDiskRelAttachmentCWModel` is the image under
`bundleDiskRelAttachmentInl` of the corresponding open bundle cell in `D(E)`. -/
@[simp]
theorem openCell_bundleDiskRelAttachmentCWModel (q : ℕ)
    (i : @RelCWComplex.cell _ _ _ _ (bundleDiskRelAttachmentCWModel F E A hr g)
      (thomCellDimension r q)) :
    @RelCWComplex.openCell _ _ _ _ (bundleDiskRelAttachmentCWModel F E A hr g)
        (thomCellDimension r q) i =
      bundleDiskRelAttachmentInl F E A hr g ''
        {v : discBundle F E |
          v.val.proj ∈ openCell q (bundleDiskRelAttachmentCellEquiv F E A hr g q i) ∧
            ‖v.val.snd‖ < 1} := by
  let _ := bundleDiskRelAttachmentCWModel F E A hr g
  let _ := bundleDiskSphereRelCW F E A hr
  have heq : EqOn
      (@RelCWComplex.map _ _ _ _ (bundleDiskRelAttachmentCWModel F E A hr g)
        (thomCellDimension r q) i)
      (bundleDiskRelAttachmentInl F E A hr g ∘
        @RelCWComplex.map _ _ _ _ (bundleDiskSphereRelCW F E A hr) (thomCellDimension r q)
          ((bundleDiskSphereCellEquiv F E A hr q).symm
            (bundleDiskRelAttachmentCellEquiv F E A hr g q i)))
      (ball 0 1) :=
    fun _ hx ↦ bundleDiskRelAttachmentCWModel_map_apply F E A hr g q i (ball_subset_closedBall hx)
  rw [RelCWComplex.openCell, heq.image_eq, image_comp, ← RelCWComplex.openCell,
    openCell_bundleDiskSphereRelCW, Equiv.apply_symm_apply]

/-- The closed `(q + r)`-cell of `bundleDiskRelAttachmentCWModel` is the image under
`bundleDiskRelAttachmentInl` of `D(E)` over the corresponding base closed cell. -/
@[simp]
theorem closedCell_bundleDiskRelAttachmentCWModel (q : ℕ)
    (i : @RelCWComplex.cell _ _ _ _ (bundleDiskRelAttachmentCWModel F E A hr g)
      (thomCellDimension r q)) :
    @RelCWComplex.closedCell _ _ _ _ (bundleDiskRelAttachmentCWModel F E A hr g)
        (thomCellDimension r q) i =
      bundleDiskRelAttachmentInl F E A hr g ''
        (discBundleProj F E ⁻¹'
          closedCell q (bundleDiskRelAttachmentCellEquiv F E A hr g q i)) := by
  let _ := bundleDiskRelAttachmentCWModel F E A hr g
  let _ := bundleDiskSphereRelCW F E A hr
  have heq : EqOn
      (@RelCWComplex.map _ _ _ _ (bundleDiskRelAttachmentCWModel F E A hr g)
        (thomCellDimension r q) i)
      (bundleDiskRelAttachmentInl F E A hr g ∘
        @RelCWComplex.map _ _ _ _ (bundleDiskSphereRelCW F E A hr) (thomCellDimension r q)
          ((bundleDiskSphereCellEquiv F E A hr q).symm
            (bundleDiskRelAttachmentCellEquiv F E A hr g q i)))
      (closedBall 0 1) :=
    fun _ hx ↦ bundleDiskRelAttachmentCWModel_map_apply F E A hr g q i hx
  rw [RelCWComplex.closedCell, heq.image_eq, image_comp, ← RelCWComplex.closedCell,
    closedCell_bundleDiskSphereRelCW, Equiv.apply_symm_apply]

/-- The cell frontier of a `(q + r)`-cell of `bundleDiskRelAttachmentCWModel` is the image under
`bundleDiskRelAttachmentInl` of the corresponding bundle cell frontier in `D(E)`. -/
@[simp]
theorem cellFrontier_bundleDiskRelAttachmentCWModel (q : ℕ)
    (i : @RelCWComplex.cell _ _ _ _ (bundleDiskRelAttachmentCWModel F E A hr g)
      (thomCellDimension r q)) :
    @RelCWComplex.cellFrontier _ _ _ _ (bundleDiskRelAttachmentCWModel F E A hr g)
        (thomCellDimension r q) i =
      bundleDiskRelAttachmentInl F E A hr g ''
        (discBundleProj F E ⁻¹'
            cellFrontier q (bundleDiskRelAttachmentCellEquiv F E A hr g q i) ∪
          (Subtype.val ⁻¹' sphereBundle F E ∩
            discBundleProj F E ⁻¹'
              closedCell q (bundleDiskRelAttachmentCellEquiv F E A hr g q i))) := by
  let _ := bundleDiskRelAttachmentCWModel F E A hr g
  let _ := bundleDiskSphereRelCW F E A hr
  have heq : EqOn
      (@RelCWComplex.map _ _ _ _ (bundleDiskRelAttachmentCWModel F E A hr g)
        (thomCellDimension r q) i)
      (bundleDiskRelAttachmentInl F E A hr g ∘
        @RelCWComplex.map _ _ _ _ (bundleDiskSphereRelCW F E A hr) (thomCellDimension r q)
          ((bundleDiskSphereCellEquiv F E A hr q).symm
            (bundleDiskRelAttachmentCellEquiv F E A hr g q i)))
      (sphere 0 1) :=
    fun _ hx ↦ bundleDiskRelAttachmentCWModel_map_apply F E A hr g q i (sphere_subset_closedBall hx)
  rw [RelCWComplex.cellFrontier, heq.image_eq, image_comp, ← RelCWComplex.cellFrontier,
    cellFrontier_bundleDiskSphereRelCW, Equiv.apply_symm_apply]

/-- `bundleDiskRelAttachmentCWModel` is finite-dimensional when `(X, A)` is finite-dimensional. -/
theorem finiteDimensional_bundleDiskRelAttachmentCWModel
    [RelCWComplex.FiniteDimensional (univ : Set X)] :
    @RelCWComplex.FiniteDimensional _ _ _ _ (bundleDiskRelAttachmentCWModel F E A hr g) := by
  have hfd := finiteDimensional_bundleDiskSphereRelCW F E A hr
  refine @RelCWComplex.FiniteDimensional.mk _ _ _ _ (bundleDiskRelAttachmentCWModel F E A hr g) ?_
  filter_upwards [hfd.eventually_isEmpty_cell] with n hn
  exact (bundleDiskRelAttachmentRawCellEquiv F E A hr g n).isEmpty_congr.2 hn

/-- `bundleDiskRelAttachmentCWModel` has finite type when `(X, A)` has finite type. -/
theorem finiteType_bundleDiskRelAttachmentCWModel [RelCWComplex.FiniteType (univ : Set X)] :
    @RelCWComplex.FiniteType _ _ _ _ (bundleDiskRelAttachmentCWModel F E A hr g) := by
  have hft := finiteType_bundleDiskSphereRelCW F E A hr
  refine @RelCWComplex.FiniteType.mk _ _ _ _ (bundleDiskRelAttachmentCWModel F E A hr g) fun n ↦ ?_
  have := hft.finite_cell n
  exact (bundleDiskRelAttachmentRawCellEquiv F E A hr g n).finite_iff.2 inferInstance

/-- `bundleDiskRelAttachmentCWModel` is finite when `(X, A)` is finite. -/
theorem finite_bundleDiskRelAttachmentCWModel [RelCWComplex.Finite (univ : Set X)] :
    @RelCWComplex.Finite _ _ _ _ (bundleDiskRelAttachmentCWModel F E A hr g) :=
  @RelCWComplex.Finite.mk _ _ _ _ (bundleDiskRelAttachmentCWModel F E A hr g)
    (finiteDimensional_bundleDiskRelAttachmentCWModel F E A hr g)
    (finiteType_bundleDiskRelAttachmentCWModel F E A hr g)

private def liftedRelAttachingMapUlift
    (g : C(↥(Subtype.val ⁻¹' sphereBundle F E ∪ discBundleProj F E ⁻¹' A), Z)) :
    C(↥(ULift.down ⁻¹' (Subtype.val ⁻¹' sphereBundle F E ∪ discBundleProj F E ⁻¹' A) :
        Set (ULift.{max v w, u} (discBundle F E))),
      ULift.{max u w, v} Z) :=
  ⟨fun x ↦ ULift.up (g ⟨x.val.down, x.property⟩),
    continuous_uliftUp.comp
      (g.continuous.comp ((continuous_uliftDown.comp continuous_subtypeVal).subtype_mk _))⟩

private lemma exists_homeomorph_bundleDiskRelAttachmentSpace_ulift
    (a : C(↥(ULift.down ⁻¹' (Subtype.val ⁻¹' sphereBundle F E ∪ discBundleProj F E ⁻¹' A) :
        Set (ULift.{max v w, u} (discBundle F E))),
      ULift.{max u w, v} Z))
    (ha : ∀ x, a x = ULift.up (g ⟨x.val.down, x.property⟩)) :
    letI := bundleDiskSphereRelCWUlift.{u, max v w} F E A hr
    ∃ Φ : bundleDiskRelAttachmentSpace.{u, v} F E A hr g ≃ₜ
        relCWAdjunctionSpace (univ : Set (ULift.{max v w, u} (discBundle F E))) a,
      (∀ z, Φ (bundleDiskRelAttachmentInr F E A hr g z) =
        pushout.inr (relCWBaseInclusion (univ : Set (ULift.{max v w, u} (discBundle F E))))
          (TopCat.ofHom a) (ULift.up z)) ∧
      ∀ z, Φ.symm (pushout.inr
          (relCWBaseInclusion (univ : Set (ULift.{max v w, u} (discBundle F E))))
          (TopCat.ofHom a) (ULift.up z)) =
        bundleDiskRelAttachmentInr F E A hr g z := by
  let _ := bundleDiskSphereRelCWUlift.{u, max v w} F E A hr
  let ι := relCWBaseInclusion (univ : Set (ULift.{max v w, u} (discBundle F E)))
  let inlBig : C(discBundle F E, relCWAdjunctionSpace
      (univ : Set (ULift.{max v w, u} (discBundle F E))) a) :=
    (pushout.inl ι (TopCat.ofHom a)).hom.comp
      ⟨fun v ↦ ⟨ULift.up v, mem_univ _⟩, continuous_uliftUp.subtype_mk _⟩
  let inrBig : C(Z, relCWAdjunctionSpace
      (univ : Set (ULift.{max v w, u} (discBundle F E))) a) :=
    (pushout.inr ι (TopCat.ofHom a)).hom.comp ⟨ULift.up, continuous_uliftUp⟩
  have hcompat : ∀ b, inlBig b.val = inrBig (g b) := fun b ↦ by
    have hc := ConcreteCategory.congr_hom (pushout.condition (f := ι) (g := TopCat.ofHom a))
      ⟨ULift.up b.val, b.property⟩
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hc
    exact hc.trans (congrArg (pushout.inr ι (TopCat.ofHom a)) (ha ⟨ULift.up b.val, b.property⟩))
  let toF : C(bundleDiskRelAttachmentSpace.{u, v} F E A hr g,
      relCWAdjunctionSpace (univ : Set (ULift.{max v w, u} (discBundle F E))) a) :=
    bundleDiskRelAttachmentDesc F E A hr g inlBig inrBig hcompat
  let invL : TopCat.of (univ : Set (ULift.{max v w, u} (discBundle F E))) ⟶
      TopCat.of (ULift.{w, max u v} (bundleDiskRelAttachmentSpace.{u, v} F E A hr g)) :=
    TopCat.ofHom ⟨fun x ↦ ULift.up (bundleDiskRelAttachmentInl F E A hr g x.val.down),
      continuous_uliftUp.comp ((bundleDiskRelAttachmentInl F E A hr g).continuous.comp
        (continuous_uliftDown.comp continuous_subtypeVal))⟩
  let invR : TopCat.of (ULift.{max u w, v} Z) ⟶
      TopCat.of (ULift.{w, max u v} (bundleDiskRelAttachmentSpace.{u, v} F E A hr g)) :=
    TopCat.ofHom ⟨fun z ↦ ULift.up (bundleDiskRelAttachmentInr F E A hr g z.down),
      continuous_uliftUp.comp ((bundleDiskRelAttachmentInr F E A hr g).continuous.comp
        continuous_uliftDown)⟩
  have hinv : ι ≫ invL = TopCat.ofHom a ≫ invR := by
    ext x
    simp only [ConcreteCategory.comp_apply, TopCat.hom_ofHom, ContinuousMap.coe_mk, invL, invR, ha]
    exact bundleDiskRelAttachmentInl_eq_inr F E A hr g ⟨x.val.down, x.property⟩
  let invUp : relCWAdjunctionSpace (univ : Set (ULift.{max v w, u} (discBundle F E))) a ⟶
      TopCat.of (ULift.{w, max u v} (bundleDiskRelAttachmentSpace.{u, v} F E A hr g)) :=
    pushout.desc invL invR hinv
  let invF : C(relCWAdjunctionSpace (univ : Set (ULift.{max v w, u} (discBundle F E))) a,
      bundleDiskRelAttachmentSpace.{u, v} F E A hr g) :=
    (⟨ULift.down, continuous_uliftDown⟩ :
      C(ULift.{w, max u v} (bundleDiskRelAttachmentSpace.{u, v} F E A hr g), _)).comp invUp.hom
  have hinv_inl : ∀ v : discBundle F E,
      invF (pushout.inl ι (TopCat.ofHom a) ⟨ULift.up v, mem_univ _⟩) =
        bundleDiskRelAttachmentInl F E A hr g v := fun v ↦ by
    have h := ConcreteCategory.congr_hom (pushout.inl_desc invL invR hinv) ⟨ULift.up v, mem_univ _⟩
    simpa only [invF, invUp, invL, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
      TopCat.hom_ofHom, ConcreteCategory.comp_apply] using congrArg ULift.down h
  have hinv_inr : ∀ z : Z,
      invF (pushout.inr ι (TopCat.ofHom a) (ULift.up z)) =
        bundleDiskRelAttachmentInr F E A hr g z := fun z ↦ by
    have h := ConcreteCategory.congr_hom (pushout.inr_desc invL invR hinv) (ULift.up z)
    simpa only [invF, invUp, invR, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
      TopCat.hom_ofHom, ConcreteCategory.comp_apply] using congrArg ULift.down h
  refine ⟨{
    toFun := toF
    invFun := invF
    left_inv := fun p ↦ bundleDiskRelAttachmentSpace_induction_on F E A hr g p
      (fun v ↦ by
        rw [show toF (bundleDiskRelAttachmentInl F E A hr g v) =
          pushout.inl ι (TopCat.ofHom a) ⟨ULift.up v, mem_univ _⟩ from
            bundleDiskRelAttachmentDesc_inl F E A hr g inlBig inrBig hcompat v]
        exact hinv_inl v)
      (fun z ↦ by
        rw [show toF (bundleDiskRelAttachmentInr F E A hr g z) =
          pushout.inr ι (TopCat.ofHom a) (ULift.up z) from
            bundleDiskRelAttachmentDesc_inr F E A hr g inlBig inrBig hcompat z]
        exact hinv_inr z)
    right_inv := fun q ↦ by
      rcases Types.eq_or_eq_of_isPushout
        ((forget TopCat).map_isPushout (IsPushout.of_hasPushout ι (TopCat.ofHom a))) q with
        ⟨⟨⟨v⟩, _⟩, rfl⟩ | ⟨⟨z⟩, rfl⟩
      · exact (congrArg toF (hinv_inl v)).trans
          (bundleDiskRelAttachmentDesc_inl F E A hr g inlBig inrBig hcompat v)
      · exact (congrArg toF (hinv_inr z)).trans
          (bundleDiskRelAttachmentDesc_inr F E A hr g inlBig inrBig hcompat z)
    continuous_toFun := toF.continuous
    continuous_invFun := invF.continuous },
    fun z ↦ bundleDiskRelAttachmentDesc_inr F E A hr g inlBig inrBig hcompat z,
    hinv_inr⟩

/-- **Base homotopy invariance of relative disc-bundle attachments.** A homotopy equivalence
`e : Z ≃ₕ Z'` (with `Z` and `Z'` in independent universes) induces a homotopy equivalence
`Z ∪_g D(E) ≃ₕ Z' ∪_{e ∘ g} D(E)` compatible with the inclusions of `Z` and `Z'`. -/
theorem exists_homotopyEquiv_bundleDiskRelAttachmentSpace {Z' : Type w} [TopologicalSpace Z']
    (e : Z ≃ₕ Z') :
    ∃ H : bundleDiskRelAttachmentSpace.{u, v} F E A hr g ≃ₕ
        bundleDiskRelAttachmentSpace.{u, w} F E A hr (e.toFun.comp g),
      (∀ z, H (bundleDiskRelAttachmentInr F E A hr g z) =
        bundleDiskRelAttachmentInr F E A hr (e.toFun.comp g) (e z)) ∧
      ∀ z', H.symm (bundleDiskRelAttachmentInr F E A hr (e.toFun.comp g) z') =
        bundleDiskRelAttachmentInr F E A hr g (e.symm z') := by
  let _ := bundleDiskSphereRelCWUlift.{u, max v w} F E A hr
  have hgW : ∀ x,
      liftedRelAttachingMapUlift.{u, v, w} F E A g x = ULift.up (g ⟨x.val.down, x.property⟩) :=
    fun _ ↦ rfl
  have hegW : ∀ x,
      ((e.uliftCongr.{max u w, max u v}).toFun.comp
          (liftedRelAttachingMapUlift.{u, v, w} F E A g)) x =
        ULift.up ((e.toFun.comp g) ⟨x.val.down, x.property⟩) :=
    fun x ↦ e.uliftCongr_apply.{max u w, max u v} _
  obtain ⟨Hw, hHw, hHwsymm⟩ :=
    (e.uliftCongr.{max u w, max u v}).exists_homotopyEquiv_relCWAdjunctionSpace
      (univ : Set (ULift.{max v w, u} (discBundle F E)))
      (liftedRelAttachingMapUlift.{u, v, w} F E A g)
  obtain ⟨Φ₁, hΦ₁, hΦ₁s⟩ :=
    exists_homeomorph_bundleDiskRelAttachmentSpace_ulift.{u, v, w} F E A hr g
      (liftedRelAttachingMapUlift.{u, v, w} F E A g) hgW
  obtain ⟨Φ₂, hΦ₂, hΦ₂s⟩ :=
    exists_homeomorph_bundleDiskRelAttachmentSpace_ulift.{u, w, v} F E A hr (e.toFun.comp g)
      ((e.uliftCongr.{max u w, max u v}).toFun.comp (liftedRelAttachingMapUlift.{u, v, w} F E A g))
      hegW
  refine ⟨(Φ₁.toHomotopyEquiv.trans Hw).trans Φ₂.symm.toHomotopyEquiv, fun z ↦ ?_, fun z' ↦ ?_⟩
  · simp only [ContinuousMap.HomotopyEquiv.trans_apply, Homeomorph.coe_toHomotopyEquiv,
      hΦ₁, hHw, ContinuousMap.HomotopyEquiv.uliftCongr_apply, hΦ₂s]
  · simp only [ContinuousMap.HomotopyEquiv.trans_symm_apply, ← Homeomorph.symm_toHomotopyEquiv,
      Homeomorph.symm_symm, Homeomorph.coe_toHomotopyEquiv,
      hΦ₂, hHwsymm, ContinuousMap.HomotopyEquiv.uliftCongr_symm_apply, hΦ₁s]

end RelAttachment

/-! ### Disc-bundle attachment `Z ∪_g D(E)` along `g : S(E) → Z` (`A = ∅`) -/

section SphereAttachment

variable {X : Type u} [TopologicalSpace X] [T2Space X] [Topology.CWComplex (univ : Set X)]
  (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  (E : X → Type u) [TopologicalSpace (TotalSpace F E)]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E]
  {r : ℕ} (hr : Module.finrank ℝ F = r)
  {Z : Type v} [TopologicalSpace Z] (g : C(sphereBundle F E, Z))

/-- **Disc-bundle attachment space `Z ∪_g D(E)`.** The adjunction space obtained by attaching the
unit disc bundle `D(E)` to `Z` along `g : S(E) → Z`. -/
def bundleDiskAttachmentSpace : TopCat.{max u v} :=
  bundleDiskRelAttachmentSpace F E (∅ : Set X) hr (bundleSphereBaseAttachingMap F E g)

/-- The canonical closed embedding `Z → Z ∪_g D(E)`. -/
def bundleDiskAttachmentInr : C(Z, bundleDiskAttachmentSpace F E hr g) :=
  bundleDiskRelAttachmentInr F E (∅ : Set X) hr (bundleSphereBaseAttachingMap F E g)

/-- The canonical map `D(E) → Z ∪_g D(E)`. -/
def bundleDiskAttachmentInl : C(discBundle F E, bundleDiskAttachmentSpace F E hr g) :=
  bundleDiskRelAttachmentInl F E (∅ : Set X) hr (bundleSphereBaseAttachingMap F E g)

/-- On the unit sphere bundle `S(E)`, `bundleDiskAttachmentInl` glues each vector `s` to `g s` in
`Z`. -/
theorem bundleDiskAttachmentInl_sphere (s : sphereBundle F E) :
    bundleDiskAttachmentInl F E hr g ⟨s.val, mem_discBundle.2 (mem_sphereBundle.1 s.property).le⟩ =
      bundleDiskAttachmentInr F E hr g (g s) :=
  bundleDiskRelAttachmentInl_eq_inr F E (∅ : Set X) hr (bundleSphereBaseAttachingMap F E g)
    ((bundleSphereRelCWBaseHomeomorph F E).symm s)

/-- **Pushout eliminator for `bundleDiskAttachmentSpace`.** Continuous maps `f : D(E) → W` and
`h : Z → W` into a space `W` in an arbitrary universe that agree along `g : S(E) → Z` descend
uniquely to a continuous map `Z ∪_g D(E) → W`. -/
def bundleDiskAttachmentDesc {W : Type w} [TopologicalSpace W]
    (f : C(discBundle F E, W)) (h : C(Z, W))
    (hfg : ∀ s : sphereBundle F E,
      f ⟨s.val, mem_discBundle.2 (mem_sphereBundle.1 s.property).le⟩ = h (g s)) :
    C(bundleDiskAttachmentSpace F E hr g, W) :=
  bundleDiskRelAttachmentDesc F E (∅ : Set X) hr (bundleSphereBaseAttachingMap F E g) f h fun b ↦
    hfg (bundleSphereRelCWBaseHomeomorph F E b)

@[simp]
theorem bundleDiskAttachmentDesc_inl {W : Type w} [TopologicalSpace W]
    (f : C(discBundle F E, W)) (h : C(Z, W))
    (hfg : ∀ s : sphereBundle F E,
      f ⟨s.val, mem_discBundle.2 (mem_sphereBundle.1 s.property).le⟩ = h (g s))
    (v : discBundle F E) :
    bundleDiskAttachmentDesc F E hr g f h hfg (bundleDiskAttachmentInl F E hr g v) = f v :=
  bundleDiskRelAttachmentDesc_inl F E (∅ : Set X) hr (bundleSphereBaseAttachingMap F E g) f h _ v

@[simp]
theorem bundleDiskAttachmentDesc_inr {W : Type w} [TopologicalSpace W]
    (f : C(discBundle F E, W)) (h : C(Z, W))
    (hfg : ∀ s : sphereBundle F E,
      f ⟨s.val, mem_discBundle.2 (mem_sphereBundle.1 s.property).le⟩ = h (g s))
    (z : Z) :
    bundleDiskAttachmentDesc F E hr g f h hfg (bundleDiskAttachmentInr F E hr g z) = h z :=
  bundleDiskRelAttachmentDesc_inr F E (∅ : Set X) hr (bundleSphereBaseAttachingMap F E g) f h _ z

@[simp]
theorem bundleDiskAttachmentDesc_comp_inl {W : Type w} [TopologicalSpace W]
    (f : C(discBundle F E, W)) (h : C(Z, W))
    (hfg : ∀ s : sphereBundle F E,
      f ⟨s.val, mem_discBundle.2 (mem_sphereBundle.1 s.property).le⟩ = h (g s)) :
    (bundleDiskAttachmentDesc F E hr g f h hfg).comp (bundleDiskAttachmentInl F E hr g) = f :=
  ContinuousMap.ext (bundleDiskAttachmentDesc_inl F E hr g f h hfg)

@[simp]
theorem bundleDiskAttachmentDesc_comp_inr {W : Type w} [TopologicalSpace W]
    (f : C(discBundle F E, W)) (h : C(Z, W))
    (hfg : ∀ s : sphereBundle F E,
      f ⟨s.val, mem_discBundle.2 (mem_sphereBundle.1 s.property).le⟩ = h (g s)) :
    (bundleDiskAttachmentDesc F E hr g f h hfg).comp (bundleDiskAttachmentInr F E hr g) = h :=
  ContinuousMap.ext (bundleDiskAttachmentDesc_inr F E hr g f h hfg)

/-- Every point of `Z ∪_g D(E)` lies in the image of `D(E)` or in the image of `Z`. -/
theorem exists_bundleDiskAttachmentInl_or_inr (p : bundleDiskAttachmentSpace F E hr g) :
    (∃ v : discBundle F E, bundleDiskAttachmentInl F E hr g v = p) ∨
      ∃ z : Z, bundleDiskAttachmentInr F E hr g z = p :=
  exists_bundleDiskRelAttachmentInl_or_inr F E (∅ : Set X) hr
    (bundleSphereBaseAttachingMap F E g) p

/-- Induction principle on points of `Z ∪_g D(E)` by splitting into the images of `D(E)` and
`Z`. -/
@[elab_as_elim]
theorem bundleDiskAttachmentSpace_induction_on
    {P : bundleDiskAttachmentSpace F E hr g → Prop}
    (p : bundleDiskAttachmentSpace F E hr g)
    (hl : ∀ v, P (bundleDiskAttachmentInl F E hr g v))
    (hr' : ∀ z, P (bundleDiskAttachmentInr F E hr g z)) : P p :=
  bundleDiskRelAttachmentSpace_induction_on F E (∅ : Set X) hr
    (bundleSphereBaseAttachingMap F E g) p hl hr'

/-- The ranges of `bundleDiskAttachmentInl` and `bundleDiskAttachmentInr` cover `Z ∪_g D(E)`. -/
theorem range_bundleDiskAttachmentInl_union_range_inr :
    range (bundleDiskAttachmentInl F E hr g) ∪ range (bundleDiskAttachmentInr F E hr g) = univ :=
  range_bundleDiskRelAttachmentInl_union_range_inr F E (∅ : Set X) hr
    (bundleSphereBaseAttachingMap F E g)

/-- Two continuous maps out of `Z ∪_g D(E)` agree as soon as they agree on the images of `D(E)`
and `Z`. -/
theorem bundleDiskAttachmentSpace_continuousMap_ext {W : Type w} [TopologicalSpace W]
    {f₁ f₂ : C(bundleDiskAttachmentSpace F E hr g, W)}
    (hl : ∀ v, f₁ (bundleDiskAttachmentInl F E hr g v) = f₂ (bundleDiskAttachmentInl F E hr g v))
    (hr' : ∀ z, f₁ (bundleDiskAttachmentInr F E hr g z) = f₂ (bundleDiskAttachmentInr F E hr g z)) :
    f₁ = f₂ :=
  bundleDiskRelAttachmentSpace_continuousMap_ext F E (∅ : Set X) hr
    (bundleSphereBaseAttachingMap F E g) hl hr'

/-- A subset of `Z ∪_g D(E)` is closed if and only if its preimages in `D(E)` and in `Z` are both
closed. -/
theorem isClosed_iff_bundleDiskAttachmentSpace (s : Set (bundleDiskAttachmentSpace F E hr g)) :
    IsClosed s ↔
      IsClosed (bundleDiskAttachmentInl F E hr g ⁻¹' s) ∧
        IsClosed (bundleDiskAttachmentInr F E hr g ⁻¹' s) :=
  isClosed_iff_bundleDiskRelAttachmentSpace F E (∅ : Set X) hr
    (bundleSphereBaseAttachingMap F E g) s

/-- The inclusion `Z → Z ∪_g D(E)` is a closed embedding. -/
theorem isClosedEmbedding_bundleDiskAttachmentInr :
    IsClosedEmbedding (bundleDiskAttachmentInr F E hr g) :=
  isClosedEmbedding_bundleDiskRelAttachmentInr F E (∅ : Set X) hr
    (bundleSphereBaseAttachingMap F E g)

/-- When `Z` is Hausdorff, the disc-bundle attachment `Z ∪_g D(E)` is Hausdorff. -/
instance t2Space_bundleDiskAttachmentSpace [T2Space Z] :
    T2Space (bundleDiskAttachmentSpace F E hr g) :=
  t2Space_bundleDiskRelAttachmentSpace F E (∅ : Set X) hr (bundleSphereBaseAttachingMap F E g)

/-- **Classical relative CW model of a disc-bundle attachment `Z ∪_g D(E)`.** For a continuous
Riemannian rank-`r` vector bundle `E → X` over a Hausdorff CW complex `X` and any continuous
attaching map `g : S(E) → Z`, the adjunction space `Z ∪_g D(E)` carries a classical relative CW
structure relative to `range (bundleDiskAttachmentInr F E hr g)`, whose `(q + r)`-cells correspond
to the `q`-cells of `X`. -/
@[instance_reducible]
def bundleDiskAttachmentCWModel :
    RelCWComplex (univ : Set (bundleDiskAttachmentSpace F E hr g))
      (range (bundleDiskAttachmentInr F E hr g)) :=
  bundleDiskRelAttachmentCWModel F E (∅ : Set X) hr (bundleSphereBaseAttachingMap F E g)

/-- The `(q + r)`-cells of `bundleDiskAttachmentCWModel` correspond bijectively to the `q`-cells of
`X`. -/
def bundleDiskAttachmentCellEquiv (q : ℕ) :
    @RelCWComplex.cell _ _ _ _ (bundleDiskAttachmentCWModel F E hr g) (thomCellDimension r q) ≃
      Topology.CWComplex.cell (univ : Set X) q :=
  bundleDiskRelAttachmentCellEquiv F E (∅ : Set X) hr (bundleSphereBaseAttachingMap F E g) q

/-- Below the fibre rank `r`, `bundleDiskAttachmentCWModel` has no `n`-cells. -/
theorem isEmpty_cell_bundleDiskAttachmentCWModel_of_lt {n : ℕ} (hn : n < r) :
    IsEmpty (@RelCWComplex.cell _ _ _ _ (bundleDiskAttachmentCWModel F E hr g) n) :=
  isEmpty_cell_bundleDiskRelAttachmentCWModel_of_lt F E (∅ : Set X) hr
    (bundleSphereBaseAttachingMap F E g) hn

/-- Each characteristic map of `bundleDiskAttachmentCWModel` is the characteristic map of the
corresponding `(q + r)`-cell of `bundleDiskSphereRelCW` in `D(E)` followed by
`bundleDiskAttachmentInl`. -/
theorem bundleDiskAttachmentCWModel_map_apply (q : ℕ)
    (i : @RelCWComplex.cell _ _ _ _ (bundleDiskAttachmentCWModel F E hr g)
      (thomCellDimension r q))
    {x : Fin (thomCellDimension r q) → ℝ} (hx : x ∈ closedBall 0 1) :
    @RelCWComplex.map _ _ _ _ (bundleDiskAttachmentCWModel F E hr g)
        (thomCellDimension r q) i x =
      bundleDiskAttachmentInl F E hr g
        (@RelCWComplex.map _ _ _ _ (bundleDiskSphereRelCW F E (∅ : Set X) hr)
          (thomCellDimension r q)
          ((bundleDiskSphereCellEquiv F E (∅ : Set X) hr q).symm
            (bundleDiskAttachmentCellEquiv F E hr g q i)) x) :=
  bundleDiskRelAttachmentCWModel_map_apply F E (∅ : Set X) hr
    (bundleSphereBaseAttachingMap F E g) q i hx

/-- The open `(q + r)`-cell of `bundleDiskAttachmentCWModel` is the image under
`bundleDiskAttachmentInl` of the corresponding open bundle cell in `D(E)`. -/
@[simp]
theorem openCell_bundleDiskAttachmentCWModel (q : ℕ)
    (i : @RelCWComplex.cell _ _ _ _ (bundleDiskAttachmentCWModel F E hr g)
      (thomCellDimension r q)) :
    @RelCWComplex.openCell _ _ _ _ (bundleDiskAttachmentCWModel F E hr g)
        (thomCellDimension r q) i =
      bundleDiskAttachmentInl F E hr g ''
        {v : discBundle F E |
          v.val.proj ∈
              openCell (C := (univ : Set X)) q (bundleDiskAttachmentCellEquiv F E hr g q i) ∧
            ‖v.val.snd‖ < 1} :=
  openCell_bundleDiskRelAttachmentCWModel F E (∅ : Set X) hr
    (bundleSphereBaseAttachingMap F E g) q i

/-- The closed `(q + r)`-cell of `bundleDiskAttachmentCWModel` is the image under
`bundleDiskAttachmentInl` of `D(E)` over the corresponding base closed cell. -/
@[simp]
theorem closedCell_bundleDiskAttachmentCWModel (q : ℕ)
    (i : @RelCWComplex.cell _ _ _ _ (bundleDiskAttachmentCWModel F E hr g)
      (thomCellDimension r q)) :
    @RelCWComplex.closedCell _ _ _ _ (bundleDiskAttachmentCWModel F E hr g)
        (thomCellDimension r q) i =
      bundleDiskAttachmentInl F E hr g ''
        (discBundleProj F E ⁻¹'
          closedCell (C := (univ : Set X)) q (bundleDiskAttachmentCellEquiv F E hr g q i)) :=
  closedCell_bundleDiskRelAttachmentCWModel F E (∅ : Set X) hr
    (bundleSphereBaseAttachingMap F E g) q i

/-- The cell frontier of a `(q + r)`-cell of `bundleDiskAttachmentCWModel` is the image under
`bundleDiskAttachmentInl` of the corresponding bundle cell frontier in `D(E)`. -/
@[simp]
theorem cellFrontier_bundleDiskAttachmentCWModel (q : ℕ)
    (i : @RelCWComplex.cell _ _ _ _ (bundleDiskAttachmentCWModel F E hr g)
      (thomCellDimension r q)) :
    @RelCWComplex.cellFrontier _ _ _ _ (bundleDiskAttachmentCWModel F E hr g)
        (thomCellDimension r q) i =
      bundleDiskAttachmentInl F E hr g ''
        (discBundleProj F E ⁻¹'
            cellFrontier (C := (univ : Set X)) q (bundleDiskAttachmentCellEquiv F E hr g q i) ∪
          (Subtype.val ⁻¹' sphereBundle F E ∩
            discBundleProj F E ⁻¹'
              closedCell (C := (univ : Set X)) q (bundleDiskAttachmentCellEquiv F E hr g q i))) :=
  cellFrontier_bundleDiskRelAttachmentCWModel F E (∅ : Set X) hr
    (bundleSphereBaseAttachingMap F E g) q i

/-- `bundleDiskAttachmentCWModel` is finite-dimensional when `X` is finite-dimensional. -/
theorem finiteDimensional_bundleDiskAttachmentCWModel
    [RelCWComplex.FiniteDimensional (univ : Set X)] :
    @RelCWComplex.FiniteDimensional _ _ _ _ (bundleDiskAttachmentCWModel F E hr g) :=
  finiteDimensional_bundleDiskRelAttachmentCWModel F E (∅ : Set X) hr
    (bundleSphereBaseAttachingMap F E g)

/-- `bundleDiskAttachmentCWModel` has finite type when `X` has finite type. -/
theorem finiteType_bundleDiskAttachmentCWModel [RelCWComplex.FiniteType (univ : Set X)] :
    @RelCWComplex.FiniteType _ _ _ _ (bundleDiskAttachmentCWModel F E hr g) :=
  finiteType_bundleDiskRelAttachmentCWModel F E (∅ : Set X) hr
    (bundleSphereBaseAttachingMap F E g)

/-- `bundleDiskAttachmentCWModel` is finite when `X` is finite. -/
theorem finite_bundleDiskAttachmentCWModel [RelCWComplex.Finite (univ : Set X)] :
    @RelCWComplex.Finite _ _ _ _ (bundleDiskAttachmentCWModel F E hr g) :=
  finite_bundleDiskRelAttachmentCWModel F E (∅ : Set X) hr
    (bundleSphereBaseAttachingMap F E g)

/-- **Base homotopy invariance of disc-bundle attachments.** A homotopy equivalence `e : Z ≃ₕ Z'`
(with `Z` and `Z'` in independent universes) induces a homotopy equivalence
`Z ∪_g D(E) ≃ₕ Z' ∪_{e ∘ g} D(E)` restricting to `e` on `Z` and to `e.symm` on `Z'`. -/
theorem exists_homotopyEquiv_bundleDiskAttachmentSpace {Z' : Type w} [TopologicalSpace Z']
    (e : Z ≃ₕ Z') :
    ∃ H : bundleDiskAttachmentSpace.{u, v} F E hr g ≃ₕ
        bundleDiskAttachmentSpace.{u, w} F E hr (e.toFun.comp g),
      (∀ z, H (bundleDiskAttachmentInr F E hr g z) =
        bundleDiskAttachmentInr F E hr (e.toFun.comp g) (e z)) ∧
      ∀ z', H.symm (bundleDiskAttachmentInr F E hr (e.toFun.comp g) z') =
        bundleDiskAttachmentInr F E hr g (e.symm z') :=
  exists_homotopyEquiv_bundleDiskRelAttachmentSpace F E (∅ : Set X) hr
    (bundleSphereBaseAttachingMap F E g) e

end SphereAttachment

end TauCeti
