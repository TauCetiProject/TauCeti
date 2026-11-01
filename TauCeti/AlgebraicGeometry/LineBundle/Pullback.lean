/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic
public import TauCeti.AlgebraicGeometry.LineBundle.Basic

/-!
# Pullback of line bundles

Let `f : X ⟶ Y` be a morphism of schemes. The inverse image `f^* L` of a line bundle `L` on `Y`
is a line bundle on `X`, giving a pullback functor on line bundles.
The generic restriction compatibility used to establish this result is provided by
`TauCeti.AlgebraicGeometry.Modules.Pullback.Basic`.

## Main declarations

* `TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible_pullback`: the pullback of an invertible
  sheaf is invertible;
* `TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible_iff_forall_restrict`: a sheaf of modules
  is invertible exactly when its restrictions to the members of an open cover are invertible;
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.pullback`: the pullback functor on line bundles.

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
    ⟨ι, fun i ↦ f ⁻¹ᵁ V i, ?_, fun i ↦
      ⟨(Scheme.Modules.pullbackObjUnitIso (f ∣_ V i)).symm ≪≫
        (Scheme.Modules.pullback (f ∣_ V i)).mapIso (e i).some ≪≫
        (Scheme.Modules.restrictPullbackObjIso f (V i) M).symm⟩⟩
  rw [IsOpenCover, ← Scheme.Hom.preimage_iSup, hV.iSup_eq_top, Scheme.Hom.preimage_top]

/-- **Invertibility is local**: a sheaf of modules on a scheme is invertible exactly when its
restriction to every member of an open cover is invertible. -/
theorem isInvertible_iff_forall_restrict (𝒰 : X.OpenCover) (M : X.Modules) :
    isInvertible X M ↔ ∀ i, isInvertible (𝒰.X i) (M.restrict (𝒰.f i)) := by
  refine ⟨fun _ i ↦ (isInvertible _).prop_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback (𝒰.f i)).app M).symm inferInstance, fun h ↦ ?_⟩
  -- Trivialize the restriction to each member `𝒰.X i` on an open cover `W i` of `𝒰.X i`, and
  -- pick for every point of `X` a trivializing open `W i k` whose image contains it.
  choose ι W hW e using fun i ↦ isInvertible_iff_exists_isOpenCover.mp (h i)
  have hx (x : X) : ∃ i k, x ∈ 𝒰.f i ''ᵁ W i k := by
    obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
    obtain ⟨k, hk⟩ := Opens.mem_iSup.mp ((hW i).iSup_eq_top.ge (Set.mem_univ y))
    exact ⟨i, k, y, hk, rfl⟩
  choose i k hk using hx
  refine isInvertible_iff_exists_isOpenCover.mpr ⟨X, fun x ↦ 𝒰.f (i x) ''ᵁ W (i x) (k x),
    IsOpenCover.mk (top_unique fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hk x⟩), fun x ↦ ⟨?_⟩⟩
  -- Transport the trivialization over `W i k` to its image along the isomorphism
  -- `(𝒰.f i).isoImage (W i k)` of open subschemes.
  set g := 𝒰.f (i x)
  set V := W (i x) (k x)
  exact (Scheme.Modules.restrictUnitIso (g.isoImage V).inv).symm ≪≫
    (Scheme.Modules.restrictFunctor (g.isoImage V).inv).mapIso
      ((e (i x) (k x)).some ≪≫ ((Scheme.Modules.restrictFunctorComp V.ι g).app M).symm) ≪≫
    ((Scheme.Modules.restrictFunctorComp (g.isoImage V).inv (V.ι ≫ g)).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorCongr (g.isoImage_inv_ι V)).app M

end SheafOfModules

namespace InvertibleSheaf

variable {X Y : Scheme.{u}}

/-- The pullback of line bundles along a morphism of schemes `f : X ⟶ Y`, as a functor from line
bundles on `Y` to line bundles on `X`. -/
-- Expose the underlying module so rigidified pullbacks can use this functor directly.
@[expose]
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

end

end AlgebraicGeometry

end TauCeti
