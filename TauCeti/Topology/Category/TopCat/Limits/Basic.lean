/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.UnitInterval
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# Basic facts about colimits in `TopCat`

The initial object of `TopCat` is empty, through Mathlib's isomorphism `TopCat.initialIsoPEmpty`.
As an instance, this makes the separation properties of the empty space, such as being Hausdorff,
available for it by instance search. It is the base of every CW complex in Mathlib's categorical
sense, `TopCat.CWComplex X`, which is a relative CW complex over the map out of `⊥_ TopCat`.

A directed colimit in `TopCat` along injective transition maps has injective colimit maps
(`TauCeti.TopCat.injective_ι_of_isColimit`), since the forgetful functor to types preserves it.

Every point of a coproduct `⨆ᵢ D i` in `TopCat` lies in one of the summands
(`TauCeti.TopCat.exists_sigma_ι_eq`). Since the unit interval `I` is locally compact, maps out of
the cylinder `I × ⨆ᵢ D i` are glued from maps out of the cylinders `I × D i`
(`TauCeti.TopCat.sigmaCylinderDesc`), as the uncurried form of the map `⨆ᵢ D i → C(I, W)` glued
from the curried ones.
-/

public section

open CategoryTheory Limits unitInterval

universe w u

namespace TopCat

/-- The initial topological space is empty. -/
instance initial_isEmpty : IsEmpty (⊥_ TopCat.{u}) :=
  Function.isEmpty initialIsoPEmpty.hom

end TopCat

namespace TauCeti.TopCat

/-- If all transition maps of a directed diagram in `TopCat` are injective, then so are the maps
from the objects of the diagram to its colimit. -/
theorem injective_ι_of_isColimit {J : Type w} [Preorder J] [IsDirectedOrder J]
    {F : J ⥤ TopCat.{u}} (hF : ∀ ⦃i j : J⦄ (hij : i ≤ j), Function.Injective (F.map (homOfLE hij)))
    {c : Cocone F} (hc : IsColimit c) (i : J) : Function.Injective (c.ι.app i) := fun x y h ↦ by
  have : Nonempty J := ⟨i⟩
  obtain ⟨k, g, hk⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' (isColimitOfPreserves (forget TopCat) hc) x y).1 h
  exact hF (leOfHom g) hk

/-- Every point of a coproduct `⨆ᵢ D i` in `TopCat` lies in one of the summands. -/
theorem exists_sigma_ι_eq {ι : Type u} {D : ι → TopCat.{u}} (z : (∐ D : TopCat.{u})) :
    ∃ i x, Sigma.ι D i x = z :=
  let ⟨⟨i⟩, x, hx⟩ := Concrete.colimit_exists_rep (Discrete.functor D) z
  ⟨i, x, hx⟩

/-- The map `I × ⨆ᵢ D i → W` out of the cylinder over a coproduct in `TopCat` which is `F i` on
the cylinder over the `i`-th summand. -/
noncomputable def sigmaCylinderDesc {ι : Type u} {D : ι → TopCat.{u}} {W : TopCat.{u}}
    (F : ∀ i, C(I × D i, W)) : C(I × (∐ D : TopCat.{u}), W) :=
  (Sigma.desc fun i ↦ TopCat.ofHom ((F i).comp ContinuousMap.prodSwap).curry :
    (∐ D) ⟶ TopCat.of C(I, W)).hom.uncurry.comp ContinuousMap.prodSwap

/-- `TauCeti.TopCat.sigmaCylinderDesc F` is `F i` on the cylinder over the `i`-th summand. -/
@[simp]
theorem sigmaCylinderDesc_ι {ι : Type u} {D : ι → TopCat.{u}} {W : TopCat.{u}}
    (F : ∀ i, C(I × D i, W)) (t : I) (i : ι) (x : D i) :
    sigmaCylinderDesc F (t, Sigma.ι D i x) = F i (t, x) := by
  have hx : (Sigma.desc fun i ↦ TopCat.ofHom ((F i).comp ContinuousMap.prodSwap).curry :
      (∐ D) ⟶ TopCat.of C(I, W)) (Sigma.ι D i x) =
        ((F i).comp ContinuousMap.prodSwap).curry x :=
    ConcreteCategory.congr_hom (Sigma.ι_comp_desc
      (fun i ↦ TopCat.ofHom ((F i).comp ContinuousMap.prodSwap).curry) i) x
  exact congrArg (fun g : C(I, W) ↦ g t) hx

end TauCeti.TopCat
