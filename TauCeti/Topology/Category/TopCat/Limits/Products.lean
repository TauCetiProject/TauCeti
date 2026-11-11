/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.UnitInterval
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# Maps out of coproducts in `TopCat`

Every point of a coproduct `∐ⱼ F j` in `TopCat` lies in the image of one of the coprojections
(`TopCat.exists_sigma_ι_eq`). Since the unit interval `I` is locally compact, maps out of the
cylinder `I × ∐ⱼ F j` are glued from maps out of the cylinders `I × F j`, as the uncurried form of
the map `∐ⱼ F j → C(I, W)` glued from the curried ones (`TopCat.sigmaCylinderDesc`).
-/

public section

noncomputable section

open CategoryTheory Limits unitInterval

universe u

namespace TopCat

variable {J : Type u} (F : J → TopCat.{u})

/-- Every point of a coproduct in `TopCat` lies in the image of one of the coprojections. -/
theorem exists_sigma_ι_eq (z : (∐ F : TopCat.{u})) : ∃ j x, Sigma.ι F j x = z :=
  let ⟨⟨j⟩, x, hx⟩ := Concrete.colimit_exists_rep _ z; ⟨j, x, hx⟩

variable {W : Type u} [TopologicalSpace W] {F}

/-- The map `I × ∐ⱼ F j → W` which is `C j` on the cylinder `I × F j`: the uncurried form of the
map `∐ⱼ F j → C(I, W)` glued from the curried maps. -/
def sigmaCylinderDesc (C : ∀ j, C(I × F j, W)) : C(I × (∐ F : TopCat.{u}), W) :=
  (Sigma.desc fun j ↦ TopCat.ofHom ((C j).comp ContinuousMap.prodSwap).curry :
    (∐ F) ⟶ TopCat.of C(I, W)).hom.uncurry.comp ContinuousMap.prodSwap

@[simp]
theorem sigmaCylinderDesc_ι (C : ∀ j, C(I × F j, W)) (t : I) (j : J) (x : F j) :
    sigmaCylinderDesc C (t, Sigma.ι F j x) = C j (t, x) := by
  have hx := ConcreteCategory.congr_hom
    (Sigma.ι_comp_desc (fun j ↦ TopCat.ofHom ((C j).comp ContinuousMap.prodSwap).curry :
      ∀ j, F j ⟶ TopCat.of C(I, W)) j) x
  exact congrArg (fun g : C(I, W) ↦ g t) hx

end TopCat
