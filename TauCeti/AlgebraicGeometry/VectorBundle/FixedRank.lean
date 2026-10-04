/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.VectorBundle.Rank

/-!
# Finite locally free sheaves of fixed rank

A finite locally free sheaf has a locally constant rank, which need not be constant on a
disconnected scheme. This file packages the sheaves whose rank is constantly `r` as the full
subcategory `FiniteLocallyFreeSheaf.FixedRank X r`. The package is stable under arbitrary
pullback, and the free sheaf on a universe lift of `Fin r` gives its standard object.

In rank one, fixed-rank finite locally free sheaves are exactly invertible sheaves. The
equivalence `InvertibleSheaf.fixedRankOneEquiv` is the identity on underlying sheaves and
morphisms; it only changes which equivalent rank-one condition is bundled with the object.

## Main declarations

* `FiniteLocallyFreeSheaf.isConstantRank`: the property that the rank is constantly `r`;
* `FiniteLocallyFreeSheaf.FixedRank X r`: finite locally free sheaves of fixed rank `r`;
* `FiniteLocallyFreeSheaf.FixedRank.pullback`: pullback of fixed-rank sheaves;
* `InvertibleSheaf.fixedRankOneEquiv`: the equivalence between invertible sheaves and finite
  locally free sheaves of fixed rank one.
-/

public section

open CategoryTheory

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X : Scheme.{u}}

namespace FiniteLocallyFreeSheaf

/-- The property that a finite locally free sheaf has rank `r` at every point. -/
def isConstantRank (X : Scheme.{u}) (r : ℕ) : ObjectProperty (FiniteLocallyFreeSheaf X) :=
  fun E ↦ ∀ x, E.rank x = r

/-- A finite locally free sheaf has constant rank `r` exactly when its rank is `r` at every
point. -/
@[simp]
theorem isConstantRank_iff (E : FiniteLocallyFreeSheaf X) (r : ℕ) :
    isConstantRank X r E ↔ ∀ x, E.rank x = r :=
  Iff.rfl

/-- Constant rank is preserved by isomorphisms of finite locally free sheaves. -/
instance (X : Scheme.{u}) (r : ℕ) : (isConstantRank X r).IsClosedUnderIsomorphisms where
  of_iso {E F} e hE := by
    intro x
    rw [← hE x]
    exact (congrArg (fun q : LocallyConstant X ℕ ↦ q x) (rank_eq_of_iso
      ((Scheme.Modules.isFiniteLocallyFree X).ι.mapIso e))).symm

/-- The full category of finite locally free sheaves of rank `r` at every point of `X`. -/
abbrev FixedRank (X : Scheme.{u}) (r : ℕ) : Type _ :=
  (isConstantRank X r).FullSubcategory

namespace FixedRank

variable (X : Scheme.{u}) (r : ℕ)

/-- Forget that a finite locally free sheaf has fixed rank. -/
abbrev toFiniteLocallyFree : FixedRank X r ⥤ FiniteLocallyFreeSheaf X :=
  ObjectProperty.ι _

variable {X} {r}

/-- The rank of a fixed-rank finite locally free sheaf is its bundled rank at every point. -/
@[simp]
theorem rank_apply (E : FixedRank X r) (x : X) : E.obj.rank x = r :=
  E.property x

variable (X) (r)

/-- The free sheaf on a universe lift of `Fin r`, as a finite locally free sheaf of fixed rank
`r`. -/
def free : FixedRank X r :=
  ⟨FiniteLocallyFreeSheaf.free X (ULift.{u} (Fin r)), fun x ↦ by simp⟩

/-- Forgetting the fixed rank of the standard free sheaf gives the free finite locally free
sheaf on a universe lift of `Fin r`. -/
@[simp]
theorem free_obj :
    (free X r).obj = FiniteLocallyFreeSheaf.free X (ULift.{u} (Fin r)) :=
  (rfl)

variable {X} {r}

/-- Pullback of finite locally free sheaves of fixed rank. -/
def pullback {Y : Scheme.{u}} (f : X ⟶ Y) : FixedRank Y r ⥤ FixedRank X r :=
  (isConstantRank X r).lift
    ((isConstantRank Y r).ι ⋙ FiniteLocallyFreeSheaf.pullback f)
    fun E x ↦ by simp

/-- The underlying finite locally free sheaf of a fixed-rank pullback is the ordinary pullback. -/
@[simp]
theorem pullback_obj_obj {Y : Scheme.{u}} (f : X ⟶ Y) (E : FixedRank Y r) :
    ((pullback f).obj E).obj = (FiniteLocallyFreeSheaf.pullback f).obj E.obj :=
  (rfl)

/-- Pullback acts on morphisms of fixed-rank sheaves by the ordinary pullback functor. -/
@[simp]
theorem pullback_map_hom {Y : Scheme.{u}} (f : X ⟶ Y) {E F : FixedRank Y r}
    (g : E ⟶ F) :
    ((pullback f).map g).hom =
      eqToHom (pullback_obj_obj f E) ≫ (FiniteLocallyFreeSheaf.pullback f).map g.hom ≫
        eqToHom (pullback_obj_obj f F).symm :=
  (rfl)

end FixedRank

end FiniteLocallyFreeSheaf

namespace InvertibleSheaf

/-- Regard an invertible sheaf as a finite locally free sheaf of fixed rank one. -/
def toFixedRankOne (X : Scheme.{u}) :
    InvertibleSheaf X ⥤ FiniteLocallyFreeSheaf.FixedRank X 1 :=
  (FiniteLocallyFreeSheaf.isConstantRank X 1).lift (toFiniteLocallyFree X)
    fun L x ↦ rank_toFiniteLocallyFree_apply L x

/-- The underlying finite locally free sheaf of an invertible sheaf regarded as a fixed-rank
object is the existing inclusion into finite locally free sheaves. -/
@[simp]
theorem toFixedRankOne_obj_obj (X : Scheme.{u}) (L : InvertibleSheaf X) :
    ((toFixedRankOne X).obj L).obj = (toFiniteLocallyFree X).obj L :=
  (rfl)

/-- The fixed-rank-one functor acts on morphisms through the existing inclusion of invertible
sheaves into finite locally free sheaves. -/
@[simp]
theorem toFixedRankOne_map_hom (X : Scheme.{u}) {L M : InvertibleSheaf X} (f : L ⟶ M) :
    ((toFixedRankOne X).map f).hom =
      eqToHom (toFixedRankOne_obj_obj X L) ≫ (toFiniteLocallyFree X).map f ≫
        eqToHom (toFixedRankOne_obj_obj X M).symm :=
  (rfl)

end InvertibleSheaf

namespace FiniteLocallyFreeSheaf.FixedRank

/-- Regard a finite locally free sheaf of fixed rank one as an invertible sheaf. -/
def toInvertible (X : Scheme.{u}) :
    FiniteLocallyFreeSheaf.FixedRank X 1 ⥤ InvertibleSheaf X :=
  (SheafOfModules.isInvertible X).lift
    ((FiniteLocallyFreeSheaf.isConstantRank X 1).ι ⋙
      (Scheme.Modules.isFiniteLocallyFree X).ι)
    fun E ↦ (FiniteLocallyFreeSheaf.isInvertible_iff_forall_rank_eq_one E.obj).mpr E.property

/-- The underlying sheaf of a fixed-rank-one object regarded as invertible is unchanged. -/
@[simp]
theorem toInvertible_obj_obj (X : Scheme.{u}) (E : FiniteLocallyFreeSheaf.FixedRank X 1) :
    ((toInvertible X).obj E).obj = E.obj.obj :=
  (rfl)

/-- The inverse rank-one functor is the identity on underlying module morphisms. -/
@[simp]
theorem toInvertible_map_hom (X : Scheme.{u})
    {E F : FiniteLocallyFreeSheaf.FixedRank X 1} (f : E ⟶ F) :
    ((toInvertible X).map f).hom =
      eqToHom (toInvertible_obj_obj X E) ≫ f.hom.hom ≫
        eqToHom (toInvertible_obj_obj X F).symm :=
  (rfl)

end FiniteLocallyFreeSheaf.FixedRank

namespace InvertibleSheaf

/-- Invertible sheaves on `X` are equivalent to finite locally free sheaves of fixed rank one.
Both functors preserve the underlying sheaves and module morphisms. -/
def fixedRankOneEquiv (X : Scheme.{u}) :
    InvertibleSheaf X ≌ FiniteLocallyFreeSheaf.FixedRank X 1 where
  functor := toFixedRankOne X
  inverse := FiniteLocallyFreeSheaf.FixedRank.toInvertible X
  unitIso := NatIso.ofComponents (fun L ↦ ObjectProperty.isoMk _ (Iso.refl L.obj))
  counitIso := NatIso.ofComponents (fun E ↦ ObjectProperty.isoMk _
    (ObjectProperty.isoMk _ (Iso.refl E.obj.obj)))

/-- The forward functor of the rank-one equivalence is the canonical inclusion of invertible
sheaves into fixed-rank finite locally free sheaves. -/
theorem fixedRankOneEquiv_functor (X : Scheme.{u}) :
    (fixedRankOneEquiv X).functor = toFixedRankOne X :=
  (rfl)

/-- The inverse functor of the rank-one equivalence only changes the bundled rank-one witness. -/
theorem fixedRankOneEquiv_inverse (X : Scheme.{u}) :
    (fixedRankOneEquiv X).inverse = FiniteLocallyFreeSheaf.FixedRank.toInvertible X :=
  (rfl)

/-- The forward rank-one equivalence leaves the underlying sheaf unchanged. -/
@[simp]
theorem fixedRankOneEquiv_functor_obj_obj (X : Scheme.{u}) (L : InvertibleSheaf X) :
    ((fixedRankOneEquiv X).functor.obj L).obj.obj = L.obj :=
  (rfl)

/-- The inverse rank-one equivalence leaves the underlying sheaf unchanged. -/
@[simp]
theorem fixedRankOneEquiv_inverse_obj_obj (X : Scheme.{u})
    (E : FiniteLocallyFreeSheaf.FixedRank X 1) :
    ((fixedRankOneEquiv X).inverse.obj E).obj = E.obj.obj :=
  (rfl)

/-- The composite underlying sheaf appearing in the unit of the rank-one equivalence is the
original sheaf. This equality supplies the transport in the unit's characteristic equation. -/
theorem fixedRankOneEquiv_unit_obj (X : Scheme.{u}) (L : InvertibleSheaf X) :
    (((fixedRankOneEquiv X).functor ⋙ (fixedRankOneEquiv X).inverse).obj L).obj = L.obj :=
  (rfl)

/-- The unit of the rank-one equivalence is the identity map after identifying its target with
the original underlying sheaf. -/
@[simp]
theorem fixedRankOneEquiv_unitIso_hom_app_hom (X : Scheme.{u}) (L : InvertibleSheaf X) :
    ((fixedRankOneEquiv X).unitIso.hom.app L).hom =
      eqToHom (fixedRankOneEquiv_unit_obj X L).symm :=
  (rfl)

/-- The composite underlying sheaf appearing in the counit of the rank-one equivalence is the
original sheaf. This equality supplies the transport in the counit's characteristic equation. -/
theorem fixedRankOneEquiv_counit_obj (X : Scheme.{u})
    (E : FiniteLocallyFreeSheaf.FixedRank X 1) :
    (((fixedRankOneEquiv X).inverse ⋙ (fixedRankOneEquiv X).functor).obj E).obj.obj = E.obj.obj :=
  (rfl)

/-- The counit of the rank-one equivalence is the identity map after identifying its source with
the original underlying sheaf. -/
@[simp]
theorem fixedRankOneEquiv_counitIso_hom_app_hom_hom (X : Scheme.{u})
    (E : FiniteLocallyFreeSheaf.FixedRank X 1) :
    ((fixedRankOneEquiv X).counitIso.hom.app E).hom.hom =
      eqToHom (fixedRankOneEquiv_counit_obj X E) :=
  (rfl)

end InvertibleSheaf

end

end AlgebraicGeometry

end TauCeti
