/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# Homology of systems of complexes which are functorial up to homotopy

Let `ι` be a preordered set and `K i` a homological complex for each `i : ι`, with morphisms
`f hij : K i ⟶ K j` for `i ≤ j`. Suppose that `f (le_refl i)` is homotopic to the identity and
that `f (hij.trans hjk)` is homotopic to `f hij ≫ f hjk`. The maps `f` need not compose on the
nose, but homotopic morphisms induce the same maps on homology, so in each degree `n` the
homology groups of the `K i` and the maps induced by `f` form a functor `ι ⥤ V`
(`HomologicalComplex.homologyFunctorOfHomotopy`).

This is how a system of Floer complexes, indexed by the slopes of the Hamiltonians and connected
by continuation maps which compose only up to homotopy, has a direct limit of homology groups.

## Main definitions

* `HomologicalComplex.homologyFunctorOfHomotopy`: the homology functor `ι ⥤ V` of a system of
  complexes which is functorial up to homotopy.
-/

public section

open CategoryTheory

namespace HomologicalComplex

universe w v u u'

variable {ι : Type w} [Preorder ι] {V : Type u} [Category.{v} V] [Preadditive V]
  [CategoryWithHomology V] {β : Type u'} {c : ComplexShape β}
  (K : ι → HomologicalComplex V c) (f : ∀ ⦃i j : ι⦄, i ≤ j → (K i ⟶ K j))
  (hid : ∀ i, Nonempty (Homotopy (f (le_refl i)) (𝟙 (K i))))
  (hcomp : ∀ ⦃i j k : ι⦄ (hij : i ≤ j) (hjk : j ≤ k),
    Nonempty (Homotopy (f (hij.trans hjk)) (f hij ≫ f hjk)))
  (n : β)

/-- The **homology functor of a system of complexes which is functorial up to homotopy**: for
morphisms `f hij : K i ⟶ K j`, `i ≤ j`, with `f (le_refl i)` homotopic to the identity and
`f (hij.trans hjk)` homotopic to `f hij ≫ f hjk`, the homology groups `H_n(K i)` and the maps
induced by the `f hij`.

The body is exposed so that the maps of the functor can be stated between the homology groups
of the `K i`. -/
@[expose]
noncomputable def homologyFunctorOfHomotopy : ι ⥤ V where
  obj i := (K i).homology n
  map g := homologyMap (f (leOfHom g)) n
  map_id i := by
    obtain ⟨H⟩ := hid i
    exact H.homologyMap_eq n |>.trans (homologyMap_id _ n)
  map_comp g g' := by
    obtain ⟨H⟩ := hcomp (leOfHom g) (leOfHom g')
    exact H.homologyMap_eq n |>.trans (homologyMap_comp _ _ n)

@[simp]
theorem homologyFunctorOfHomotopy_obj (i : ι) :
    (homologyFunctorOfHomotopy K f hid hcomp n).obj i = (K i).homology n :=
  (rfl)

@[simp]
theorem homologyFunctorOfHomotopy_map {i j : ι} (g : i ⟶ j) :
    (homologyFunctorOfHomotopy K f hid hcomp n).map g = homologyMap (f (leOfHom g)) n :=
  (rfl)

end HomologicalComplex
