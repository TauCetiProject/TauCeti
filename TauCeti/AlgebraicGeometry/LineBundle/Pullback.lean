/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback
public import TauCeti.AlgebraicGeometry.LineBundle.Basic
public import TauCeti.AlgebraicGeometry.LineBundle.Class

/-!
# Pullback of line bundles

Let `f : X ⟶ Y` be a morphism of schemes. The inverse image `f^* L` of a line bundle `L` on `Y`
is a line bundle on `X`, so pulling back makes line bundles, and their isomorphism classes,
contravariantly functorial in the scheme. This is the functoriality in `T` of the line-bundle
classes on `X_T` that the relative Picard functor `T ↦ Pic(X_T)/Pic(T)` is built from.
The generic restriction compatibility used to establish this result is provided by
`TauCeti.AlgebraicGeometry.Modules.Pullback`.

The map on classes is a function of sets. Compatibility with tensor products, needed to make it
a monoid homomorphism, requires a pullback–tensor comparison for sheaves of modules.

## Main declarations

* `TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible_pullback`: the pullback of an invertible
  sheaf is invertible;
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.pullback`: the pullback functor on line bundles;
* `TauCeti.AlgebraicGeometry.LineBundleClass.pullback`: the induced map on isomorphism classes of
  line bundles, which preserves the trivial class (`LineBundleClass.pullback_one`) and is
  functorial (`LineBundleClass.pullback_id`, `LineBundleClass.pullback_comp`).

## References

* R. Hartshorne, *Algebraic Geometry*, Section II.5 and Section II.6 (the Picard group).
* The Stacks Project, *Sheaves of Modules*, section *Invertible modules*.
-/

public section

open CategoryTheory TopologicalSpace

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

namespace SheafOfModules

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The pullback of an invertible sheaf along a morphism of schemes is invertible. -/
instance isInvertible_pullback (M : Y.Modules) [hM : isInvertible Y M] :
    isInvertible X ((Scheme.Modules.pullback f).obj M) := by
  obtain ⟨ι, V, hV, e⟩ :=
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible_iff_exists_isOpenCover.mp hM
  refine TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible_iff_exists_isOpenCover.mpr
    ⟨ι, fun i ↦ f ⁻¹ᵁ V i, ?_, fun i ↦ by
    let : (SheafOfModules.pushforward.{u} (f ∣_ V i).toRingCatSheafHom).IsRightAdjoint :=
      inferInstanceAs (Scheme.Modules.pushforward (f ∣_ V i)).IsRightAdjoint
    have : IsIso (SheafOfModules.pullbackObjUnitToUnit (f ∣_ V i).toRingCatSheafHom) :=
      SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal _
    exact ⟨(asIso (SheafOfModules.pullbackObjUnitToUnit (f ∣_ V i).toRingCatSheafHom)).symm ≪≫
      (Scheme.Modules.pullback (f ∣_ V i)).mapIso (e i).some ≪≫
      (Scheme.Modules.restrictPullbackObjIso f (V i) M).symm⟩⟩
  rw [IsOpenCover, ← Scheme.Hom.preimage_iSup, hV.iSup_eq_top, Scheme.Hom.preimage_top]

end SheafOfModules

namespace InvertibleSheaf

variable {X Y : Scheme.{u}}

/-- The pullback of line bundles along a morphism of schemes `f : X ⟶ Y`, as a functor from line
bundles on `Y` to line bundles on `X`. -/
def pullback (f : X ⟶ Y) : InvertibleSheaf Y ⥤ InvertibleSheaf X :=
  (SheafOfModules.isInvertible X).lift
    ((SheafOfModules.isInvertible Y).ι ⋙ Scheme.Modules.pullback f)
    fun L ↦ SheafOfModules.isInvertible_pullback f L.obj

/-- The underlying sheaf of the pullback of a line bundle is its pullback as a sheaf of
modules. -/
@[simp]
lemma pullback_obj_obj (f : X ⟶ Y) (L : InvertibleSheaf Y) :
    ((pullback f).obj L).obj = (Scheme.Modules.pullback f).obj L.obj :=
  (rfl)

/-- Pullback acts on a morphism of line bundles by the underlying module pullback. -/
@[simp]
lemma pullback_map (f : X ⟶ Y) {L K : InvertibleSheaf Y} (φ : L ⟶ K) :
    ((pullback f).map φ).hom =
      eqToHom (pullback_obj_obj f L) ≫ (Scheme.Modules.pullback f).map φ.hom ≫
        eqToHom (pullback_obj_obj f K).symm := by
  cases pullback_obj_obj f L
  cases pullback_obj_obj f K
  unfold pullback
  simp

end InvertibleSheaf

namespace LineBundleClass

variable {X Y Z : Scheme.{u}}

/-- The pullback of isomorphism classes of line bundles along a morphism of schemes
`f : X ⟶ Y`, as a function of sets. -/
def pullback (f : X ⟶ Y) : LineBundleClass Y → LineBundleClass X :=
  lift (fun L ↦ mk ((InvertibleSheaf.pullback f).obj L)) fun _ _ ⟨e⟩ ↦
    mk_eq_mk_iff.mpr ⟨(Scheme.Modules.pullback f).mapIso e⟩

/-- The pullback of the class of a line bundle is the class of its pullback. -/
@[simp]
lemma pullback_mk (f : X ⟶ Y) (L : InvertibleSheaf Y) :
    pullback f (mk L) = mk ((InvertibleSheaf.pullback f).obj L) :=
  lift_mk L

/-- The pullback of the trivial line bundle class is trivial. -/
@[simp]
lemma pullback_one (f : X ⟶ Y) : pullback f 1 = 1 := by
  rw [← mk_trivial, ← mk_trivial, pullback_mk, mk_eq_mk_iff, InvertibleSheaf.pullback_obj_obj,
    InvertibleSheaf.trivial_obj, InvertibleSheaf.trivial_obj]
  let : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  exact ⟨SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom PUnit⟩

/-- Pulling back along the identity is the identity on line-bundle classes. -/
@[simp]
lemma pullback_id (a : LineBundleClass X) : pullback (𝟙 X) a = a := by
  obtain ⟨L, rfl⟩ := mk_surjective a
  rw [pullback_mk, mk_eq_mk_iff]
  exact ⟨(Scheme.Modules.pullbackId X).app L.obj⟩

/-- Pulling back line-bundle classes along a composite is the composite of the pullbacks. -/
@[simp]
lemma pullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) (a : LineBundleClass Z) :
    pullback (f ≫ g) a = pullback f (pullback g a) := by
  obtain ⟨L, rfl⟩ := mk_surjective a
  rw [pullback_mk, pullback_mk, pullback_mk, mk_eq_mk_iff]
  exact ⟨((Scheme.Modules.pullbackComp f g).app L.obj).symm⟩

end LineBundleClass

end

end AlgebraicGeometry

end TauCeti
