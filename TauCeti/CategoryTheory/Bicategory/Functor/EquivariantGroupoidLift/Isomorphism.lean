/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.Bicategory

/-!
# Invertibility of compatible modifications of lifts

The prescribed-fiber comparison of a lift is an equivalence. Consequently, the component
functors of a morphism of lifts are equivalences too. Moreover, compatibility with the
fiber comparisons determines every component of a modification: after applying the target
fiber equivalence it is the first fiber isomorphism followed by the inverse of the second.
Thus compatible modifications are unique when they exist, and are automatically invertible.
The hom categories of lifts are therefore thin groupoids. In particular, restricting to
invertible modifications loses no 2-morphisms; no invertibility hypothesis is needed when
constructing comparisons of normalized transport.

This does not assert that a modification exists between arbitrary parallel lift morphisms.
Its naturality along parameter arrows is still a genuine condition.

## References

* Niles Johnson and Donald Yau, *2-Dimensional Categories*, Chapter 4, for strong
  transformations and modifications.
* The fiber comparisons and compatible modifications used here are those of
  `EquivariantGroupoidLift.Hom`.
-/

public section

universe w v u₂ v₁ u₁

namespace TauCeti.EquivariantGroupoidLift.Hom

open CategoryTheory Bicategory Pseudofunctor.StrongTrans

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  {actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}}
  {L L' : EquivariantGroupoidLift Γ actions}

/-- The component functor of a lift morphism is an equivalence, since its composite with
the target fiber equivalence is isomorphic to the source fiber equivalence. -/
instance isEquivalence_jointFunctor (φ : L.Hom L') (p : Γ) :
    (φ.jointFunctor p).IsEquivalence := by
  have : (φ.jointFunctor p ⋙ (L'.fiberEquivalence p).functor).IsEquivalence :=
    Functor.isEquivalence_of_iso (φ.fiberFunctorIso p).symm
  exact Functor.isEquivalence_of_comp_right (φ.jointFunctor p) (L'.fiberEquivalence p).functor

/-- The fiber compatibility determines a modification component after applying the target
fiber equivalence. Both factors on the right are isomorphisms. -/
@[simp]
lemma map_modification_app {φ ψ : L.Hom L'} (Θ : φ ⟶ ψ) (p : Γ) (Y : L.jointFiber p) :
    (L'.fiberEquivalence p).functor.map
        ((Θ.joint.as.app ⟨(p, SingleObj.star H)⟩).toNatTrans.app Y) =
      (φ.fiberFunctorIso p).hom.app Y ≫ (ψ.fiberFunctorIso p).inv.app Y := by
  have h := congrArg (fun m => m.toNatTrans.app Y) (Θ.comm p ⟨SingleObj.star H⟩)
  apply (cancel_mono ((ψ.fiberFunctorIso p).hom.app Y)).mp
  rw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  -- Normalize the restricted/joint fiber endpoints before simplifying the Cat component laws.
  simpa only [fiberEquivalence_functor, fiberFunctorIso_hom_app, Cat.Hom.toNatTrans_comp,
    NatTrans.comp_app, Cat.whiskerRight_app] using! h

/-- Compatible modifications between two fixed lift morphisms are unique. -/
instance subsingleton_hom₂ (φ ψ : L.Hom L') : Subsingleton (φ ⟶ ψ) where
  allEq Θ Ξ := by
    apply hom₂_ext
    apply homCategory.ext
    rintro ⟨p, a⟩
    cases a
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext Y
    apply (L'.fiberEquivalence p).functor.map_injective
    exact (map_modification_app Θ p Y).trans (map_modification_app Ξ p Y).symm

/-- Each component of the joint modification is invertible. -/
instance isIso_modification_app {φ ψ : L.Hom L'} (Θ : φ ⟶ ψ) (p : Γ) :
    IsIso (Θ.joint.as.app ⟨(p, SingleObj.star H)⟩) := by
  have h (Y : L.jointFiber p) :
      IsIso ((Θ.joint.as.app ⟨(p, SingleObj.star H)⟩).toNatTrans.app Y) := by
    have : IsIso ((L'.fiberEquivalence p).functor.map
        ((Θ.joint.as.app ⟨(p, SingleObj.star H)⟩).toNatTrans.app Y)) := by
      rw [map_modification_app]
      infer_instance
    exact isIso_of_reflects_iso _ (L'.fiberEquivalence p).functor
  let e := NatIso.ofComponents (fun Y => asIso
    ((Θ.joint.as.app ⟨(p, SingleObj.star H)⟩).toNatTrans.app Y))
    (fun f => (Θ.joint.as.app ⟨(p, SingleObj.star H)⟩).toNatTrans.naturality f)
  have he : (Cat.Hom.isoMk e).hom = Θ.joint.as.app ⟨(p, SingleObj.star H)⟩ := by
    ext Y
    rfl
  rw [← he]
  infer_instance

/-- Every compatible modification is invertible as a modification of joint pseudofunctors. -/
instance isIso_joint {φ ψ : L.Hom L'} (Θ : φ ⟶ ψ) : IsIso Θ.joint := by
  let e : φ.joint ≅ ψ.joint := Pseudofunctor.StrongTrans.isoMk
    (fun x => by
      obtain ⟨p, a⟩ := x
      cases a
      letI := isIso_modification_app Θ p
      exact asIso (Θ.joint.as.app ⟨(p, SingleObj.star H)⟩))
    (fun f => Θ.joint.as.naturality f)
  have he : e.hom = Θ.joint := by
    apply homCategory.ext
    rintro ⟨p, a⟩
    cases a
    rfl
  rw [← he]
  infer_instance

/-- The hom categories of coherent lifts are groupoids, without restricting their
modifications. Together with `subsingleton_hom₂`, they are thin groupoids. -/
instance isGroupoid : IsGroupoid (L.Hom L') where
  all_isIso {φ ψ} Θ := by
    let e : φ ≅ ψ := isoMk (asIso Θ.joint) Θ.comm
    have he : e.hom = Θ := hom₂_ext (by simp [e])
    rw [← he]
    infer_instance

end TauCeti.EquivariantGroupoidLift.Hom

namespace TauCeti.EquivariantGroupoidLift

open CategoryTheory Bicategory

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  {actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}}
  {L L' : EquivariantGroupoidLift Γ actions}

-- The native bicategory hom-category projection is not reducible to the standalone
-- Hom category during instance search. These instances also support native 1-/2-morphism notation.
/-- Compatible modifications are unique also in the native bicategory hom categories. -/
instance subsingleton₂ (φ ψ : L ⟶ L') : Subsingleton (φ ⟶ ψ) :=
  Hom.subsingleton_hom₂ φ ψ

/-- The native bicategory hom categories of lifts are groupoids. -/
instance isGroupoid_hom : IsGroupoid (L ⟶ L') :=
  Hom.isGroupoid

end TauCeti.EquivariantGroupoidLift
