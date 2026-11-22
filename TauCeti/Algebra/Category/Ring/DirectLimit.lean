/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import TauCeti.Order.Interval.Set.Directed

/-!
# Directed colimits in `CommRingCat` as direct limits of algebras

Let `F : I ⥤ CommRingCat` be a diagram over a preorder `I`, and `i₀ : I` a stage. On the tail
`Set.Ici i₀` above `i₀`, each stage `F.obj i` is an `F.obj i₀`-algebra through
`F.map (homOfLE _)`, and so is `colimit F` through `colimit.ι F i₀`. The maps of `F` between the
stages of the tail are then `F.obj i₀`-algebra maps forming a directed system, and so are the
colimit injections from these stages. When `I` is directed, Mathlib's generic direct limit of this
system is the categorical colimit: the map out of it induced by the colimit injections is an
`F.obj i₀`-algebra isomorphism onto `colimit F`. Results about direct limits of algebras, such as
base change along them, thereby apply to colimits of directed diagrams in `CommRingCat`.

The index type may live in a smaller universe than the rings, as in
`Mathlib/Algebra/Category/Ring/FilteredColimits.lean`.

## Main declarations

* `CategoryTheory.Functor.tailAlgebra`, `CategoryTheory.Functor.colimitAlgebra`: the
  `F.obj i₀`-algebra structures on the stages above `i₀` and on `colimit F`.
* `CategoryTheory.Functor.tailTransition`: the maps of `F` between the stages above `i₀`, as
  `F.obj i₀`-algebra maps; they form a directed system.
* `CategoryTheory.Functor.tailToColimit`: the colimit injections from the stages above `i₀`, as
  `F.obj i₀`-algebra maps.
* `CategoryTheory.Functor.directLimitTailToColimit`: the induced map from the direct limit of the
  tail to `colimit F`.
* `CategoryTheory.Functor.directLimitTailAlgEquivColimit`: for directed `I`, this map is an
  `F.obj i₀`-algebra isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe v u

section Algebra

variable {I : Type v} [Preorder I] (F : I ⥤ CommRingCat.{u}) (i₀ : I)

/-- A stage `F.obj i` of the tail `Set.Ici i₀` is an `F.obj i₀`-algebra through the map of `F`
from `i₀` to `i`. -/
abbrev tailAlgebra (i : Set.Ici i₀) : Algebra (F.obj i₀) (F.obj i) :=
  (F.map (homOfLE i.property)).hom.toAlgebra

/-- The colimit of `F` is an `F.obj i₀`-algebra through the colimit injection `colimit.ι F i₀`. -/
noncomputable abbrev colimitAlgebra [HasColimit F] :
    Algebra (F.obj i₀) (colimit F : CommRingCat.{u}) :=
  (colimit.ι F i₀).hom.toAlgebra

end Algebra

attribute [local instance] tailAlgebra colimitAlgebra

section Tail

variable {I : Type v} [Preorder I] (F : I ⥤ CommRingCat.{u}) (i₀ : I)

/-- The transition maps of the tail of `F` above `i₀`: the maps of `F` between stages in
`Set.Ici i₀`, as `F.obj i₀`-algebra maps. -/
def tailTransition (i j : Set.Ici i₀) (h : i ≤ j) : F.obj i →ₐ[F.obj i₀] F.obj j :=
  { (F.map (homOfLE h)).hom with
    commutes' a :=
      (ConcreteCategory.congr_hom (F.map_comp (homOfLE i.property) (homOfLE h)) a).symm }

@[simp]
theorem tailTransition_apply (i j : Set.Ici i₀) (h : i ≤ j) (x : F.obj i) :
    F.tailTransition i₀ i j h x = (F.map (homOfLE h)).hom x :=
  rfl

/-- The maps of `F` between the stages above `i₀` form a directed system. -/
instance instDirectedSystemTailTransition :
    DirectedSystem (fun i : Set.Ici i₀ ↦ F.obj i) (F.tailTransition i₀ · · ·) where
  map_self i x := by simp
  map_map _ _ _ hij hjk x :=
    (ConcreteCategory.congr_hom (F.map_comp (homOfLE hij) (homOfLE hjk)) x).symm

variable [HasColimit F]

/-- The colimit injections from the stages of the tail of `F` above `i₀`, as `F.obj i₀`-algebra
maps. -/
noncomputable def tailToColimit (i : Set.Ici i₀) : F.obj i →ₐ[F.obj i₀] (colimit F : CommRingCat) :=
  { (colimit.ι F i).hom with
    commutes' a := ConcreteCategory.congr_hom (colimit.w F (homOfLE i.property)) a }

@[simp]
theorem tailToColimit_apply (i : Set.Ici i₀) (x : F.obj i) :
    F.tailToColimit i₀ i x = (colimit.ι F i).hom x :=
  rfl

variable [IsDirectedOrder (Set.Ici i₀)]

/-- The `F.obj i₀`-algebra map from the direct limit of the tail of `F` above `i₀` to
`colimit F` induced by the colimit injections. Only the tail needs to be directed; it is when `I`
is (`Set.Ici.isDirectedOrder`). -/
noncomputable def directLimitTailToColimit :
    DirectLimit (fun i : Set.Ici i₀ ↦ F.obj i) (F.tailTransition i₀) →ₐ[F.obj i₀]
      (colimit F : CommRingCat) :=
  DirectLimit.Algebra.lift _ _ _ (F.tailToColimit i₀) fun _ _ h x ↦
    ConcreteCategory.congr_hom (colimit.w F (homOfLE h)) x

@[simp]
theorem directLimitTailToColimit_mk (i : Set.Ici i₀) (x : F.obj i) :
    F.directLimitTailToColimit i₀ ⟦⟨i, x⟩⟧ = (colimit.ι F i).hom x :=
  rfl

theorem directLimitTailToColimit_of (i : Set.Ici i₀) (x : F.obj i) :
    F.directLimitTailToColimit i₀ (DirectLimit.Algebra.of _ (F.tailTransition i₀) i x) =
      (colimit.ι F i).hom x :=
  DirectLimit.Algebra.lift_of ..

end Tail

section Colimit

variable {I : Type v} [Preorder I] [IsDirectedOrder I] (F : I ⥤ CommRingCat.{max v u}) (i₀ : I)
  [HasColimit F]

/-- The map from the direct limit of the tail of `F` above `i₀` to `colimit F` is bijective. -/
theorem bijective_directLimitTailToColimit :
    Function.Bijective (F.directLimitTailToColimit i₀) := by
  -- The directed preorder `I` is filtered, and the forgetful functor preserves filtered colimits
  -- indexed by `I`, as `Concrete.colimit_exists_rep` and `colimit_exists_of_rep_eq` need.
  have : Nonempty I := ⟨i₀⟩
  have := preservesFilteredColimitsOfSize_shrink.{v, u, v, u} (forget CommRingCat.{max v u})
  refine ⟨(injective_iff_map_eq_zero _).mpr fun z hz ↦ ?_, fun r ↦ ?_⟩
  · obtain ⟨i, x, rfl⟩ := DirectLimit.exists_eq_mk _ z
    rw [← DirectLimit.Algebra.of_apply, directLimitTailToColimit_of] at hz
    rw [← DirectLimit.Algebra.of_apply]
    obtain ⟨k, f, _, hk⟩ :=
      Concrete.colimit_exists_of_rep_eq F x 0 (hz.trans (map_zero (colimit.ι F i).hom).symm)
    let k' : Set.Ici i₀ := ⟨k, i.property.trans (leOfHom f)⟩
    rw [← DirectLimit.Algebra.of_f (G := fun i : Set.Ici i₀ ↦ F.obj i) (leOfHom f : i ≤ k') x,
      tailTransition_apply]
    exact (congrArg _ (hk.trans (map_zero _))).trans (map_zero _)
  · obtain ⟨i, x, rfl⟩ := Concrete.colimit_exists_rep F r
    obtain ⟨j, h₀j, hij⟩ := exists_ge_ge i₀ i
    exact ⟨DirectLimit.Algebra.of _ (F.tailTransition i₀) ⟨j, h₀j⟩ ((F.map (homOfLE hij)).hom x),
      (directLimitTailToColimit_of ..).trans (ConcreteCategory.congr_hom (colimit.w F _) x)⟩

/-- The direct limit of the tail of `F` above the stage `i₀` is the colimit of `F`, as an
`F.obj i₀`-algebra: the map induced by the colimit injections is an isomorphism. -/
noncomputable def directLimitTailAlgEquivColimit :
    DirectLimit (fun i : Set.Ici i₀ ↦ F.obj i) (F.tailTransition i₀) ≃ₐ[F.obj i₀]
      (colimit F : CommRingCat) :=
  AlgEquiv.ofBijective _ (F.bijective_directLimitTailToColimit i₀)

@[simp]
theorem directLimitTailAlgEquivColimit_mk (i : Set.Ici i₀) (x : F.obj i) :
    F.directLimitTailAlgEquivColimit i₀ ⟦⟨i, x⟩⟧ = (colimit.ι F i).hom x :=
  (AlgEquiv.ofBijective_apply ..).trans (directLimitTailToColimit_mk ..)

theorem directLimitTailAlgEquivColimit_of (i : Set.Ici i₀) (x : F.obj i) :
    F.directLimitTailAlgEquivColimit i₀ (DirectLimit.Algebra.of _ (F.tailTransition i₀) i x) =
      (colimit.ι F i).hom x :=
  (AlgEquiv.ofBijective_apply ..).trans (directLimitTailToColimit_of ..)

end Colimit

end CategoryTheory.Functor
