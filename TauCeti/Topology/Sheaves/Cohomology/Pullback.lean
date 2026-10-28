/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Topology.Sheaves.Functors

/-!
# Inverse image on the cohomology of abelian sheaves

Let `f : X ⟶ Y` be a continuous map and `F` a sheaf of abelian groups on `Y`. The inverse image
functor `f⁻¹` from abelian sheaves on `Y` to abelian sheaves on `X` is exact, and it carries the
constant sheaf `ℤ` on `Y` to the constant sheaf `ℤ` on `X`. Since `Hⁿ(Y, F)` is
`Extⁿ(ℤ, F)` (Mathlib's `CategoryTheory.Sheaf.H`), applying `f⁻¹` to extensions gives the
canonical map

`TauCeti.Topology.cohomologyPullback f F n : Hⁿ(Y, F) →+ Hⁿ(X, f⁻¹ F)`.

It is natural in `F`, commutes with the connecting maps of short exact sequences, and in degree
zero it is the map on global sections given by the unit `F ⟶ f_* f⁻¹ F` of the adjunction. These
three properties make it a morphism of cohomological δ-functors. Composed with a comparison map
`f⁻¹ F ⟶ G`, it gives the pullback maps on the cohomology of sheaves of modules on schemes.

## Main declarations

* `TauCeti.Topology.pullbackConstantSheafIso`: `f⁻¹` of a constant sheaf is constant;
* `TauCeti.Topology.cohomologyPullback`: the map `Hⁿ(Y, F) →+ Hⁿ(X, f⁻¹ F)`;
* `TauCeti.Topology.cohomologyPullback_map`: its naturality in `F`;
* `TauCeti.Topology.cohomologyPullback_δ`: its compatibility with connecting maps;
* `TauCeti.Topology.cohomologyPullback_zero`: its description in degree zero.

## References

* R. Hartshorne, *Algebraic Geometry*, Section III.1 (universal δ-functors) and Exercise III.8.1.
-/

public section

open CategoryTheory Limits TopologicalSpace Opposite Abelian

namespace TauCeti.Topology

universe u

noncomputable section

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/-- The inverse image of abelian sheaves along a continuous map is left exact. -/
instance : PreservesFiniteLimits ((Opens.map f).sheafPullback AddCommGrpCat.{u}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)) :=
  have : RepresentablyFlat (Opens.map f) := flat_of_preservesFiniteLimits _
  Functor.sheafPullbackConstruction.preservesFiniteLimits (Opens.map f) AddCommGrpCat.{u} _ _

/-- The inverse image of abelian sheaves along a continuous map is right exact, being a left
adjoint. -/
instance : PreservesFiniteColimits ((Opens.map f).sheafPullback AddCommGrpCat.{u}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)) :=
  have := ((Opens.map f).sheafAdjunctionContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).isLeftAdjoint
  inferInstance

/-- The inverse image of abelian sheaves along a continuous map is additive. -/
instance : ((Opens.map f).sheafPullback AddCommGrpCat.{u}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The inverse image of the constant sheaf with value `A` is the constant sheaf with value `A`.
Both functors `A ↦ f⁻¹ A_Y` and `A ↦ A_X` are left adjoint to taking global sections, because
global sections of `f_* G` are global sections of `G`. -/
def pullbackConstantSheafIso (A : AddCommGrpCat.{u}) :
    ((Opens.map f).sheafPullback AddCommGrpCat.{u} (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X)).obj
        ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj A) ≅
      (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj A :=
  (((constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{u} isTerminalTop).comp
    ((Opens.map f).sheafAdjunctionContinuous AddCommGrpCat.{u} _ _)).leftAdjointUniq
      (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop)).app A

/-- Under the adjunctions between constant sheaves and global sections, precomposing with the
inverse of `pullbackConstantSheafIso` corresponds to composing with the unit `F ⟶ f_* f⁻¹ F` on
global sections. -/
lemma constantSheafAdj_homEquiv_pullbackConstantSheafIso_inv
    {A : AddCommGrpCat.{u}} {F : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}}
    (a : (constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj A ⟶ F) :
    (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop).homEquiv _ _
        ((pullbackConstantSheafIso f A).inv ≫
          ((Opens.map f).sheafPullback AddCommGrpCat.{u} _ _).map a) =
      (constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{u} isTerminalTop).homEquiv _ _
        a ≫ (((Opens.map f).sheafAdjunctionContinuous AddCommGrpCat.{u}
          (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).unit.app F).hom.app
            (op ⊤) := by
  let adj₁ := (constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
    isTerminalTop).comp ((Opens.map f).sheafAdjunctionContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X))
  let adj₂ := constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop
  have e : (pullbackConstantSheafIso f A).inv = (adj₂.leftAdjointUniq adj₁).hom.app A := rfl
  rw [e, Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  -- The two adjunctions have definitionally equal right adjoints, but not syntactically equal ones.
  erw [Adjunction.unit_leftAdjointUniq_hom_app adj₂ adj₁ A]
  -- The left side is the unit form of `adj₁.homEquiv`; `adj₁`'s right adjoint is only
  -- definitionally the one of `adj₂`, so `Adjunction.homEquiv_unit` cannot fold it back.
  change adj₁.homEquiv _ _ (((Opens.map f).sheafPullback AddCommGrpCat.{u}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).map a) = _
  rw [Adjunction.comp_homEquiv]
  dsimp only [Equiv.trans_apply]
  -- `(unit.app F).hom.app (op ⊤)` is the map on global sections of the unit, written as the
  -- image of the unit under the global sections functor so that `homEquiv_naturality_right`
  -- applies.
  change _ = _ ≫ ((sheafSections (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj (op ⊤)).map
    (((Opens.map f).sheafAdjunctionContinuous AddCommGrpCat.{u} (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X)).unit.app F)
  rw [← Adjunction.homEquiv_naturality_right]
  congr 1
  rw [Adjunction.homEquiv_unit, Adjunction.unit_naturality]

/-- The inverse image map `Hⁿ(Y, F) →+ Hⁿ(X, f⁻¹ F)` on sheaf cohomology along a continuous map
`f : X ⟶ Y`: the exact functor `f⁻¹` applied to `Extⁿ(ℤ, F)`, followed by the identification
`f⁻¹ ℤ ≅ ℤ` of `pullbackConstantSheafIso`. -/
def cohomologyPullback (F : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H.{u} F n →+ Sheaf.H.{u} (((Opens.map f).sheafPullback AddCommGrpCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj F) n where
  toFun x := (Ext.mk₀ (pullbackConstantSheafIso f _).inv).comp
    (x.mapExactFunctor ((Opens.map f).sheafPullback AddCommGrpCat.{u} _ _)) (zero_add n)
  map_zero' := by rw [Ext.mapExactFunctor_zero]; exact Ext.comp_zero _ _ _ _ _
  map_add' x y := by rw [Ext.mapExactFunctor_add]; exact Ext.comp_add _ _ _ _

/-- The defining formula of `cohomologyPullback`. -/
lemma cohomologyPullback_apply (F : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
    {n : ℕ} (x : Sheaf.H.{u} F n) :
    cohomologyPullback f F n x = (Ext.mk₀ (pullbackConstantSheafIso f _).inv).comp
      (x.mapExactFunctor ((Opens.map f).sheafPullback AddCommGrpCat.{u} _ _)) (zero_add n) :=
  (rfl)

/-- The inverse image map on cohomology is natural in the coefficient sheaf. -/
lemma cohomologyPullback_map {F G : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}}
    (α : F ⟶ G) {n : ℕ} (x : Sheaf.H.{u} F n) :
    cohomologyPullback f G n (Sheaf.H.map α n x) =
      Sheaf.H.map (((Opens.map f).sheafPullback AddCommGrpCat.{u} _ _).map α) n
        (cohomologyPullback f F n x) := by
  rw [cohomologyPullback_apply, cohomologyPullback_apply, Sheaf.H.map_apply, Sheaf.H.map_apply,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_third_deg_zero]

/-- The inverse image map on cohomology commutes with the connecting maps of a short exact
sequence of sheaves and of its (exact) inverse image. -/
lemma cohomologyPullback_δ
    {S : ShortComplex (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})}
    (hS : S.ShortExact) {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) (x : Sheaf.H.{u} S.X₃ n₀) :
    cohomologyPullback f S.X₁ n₁ (Sheaf.H.δ hS n₀ n₁ h x) =
      Sheaf.H.δ (hS.map_of_exact ((Opens.map f).sheafPullback AddCommGrpCat.{u} _ _)) n₀ n₁ h
        (cohomologyPullback f S.X₃ n₀ x) := by
  simp only [cohomologyPullback_apply, Sheaf.H.δ, AddMonoidHom.flip_apply,
    Ext.bilinearComp_apply_apply]
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
  exact (Ext.comp_assoc _ _ _ (zero_add n₀) h (by omega)).symm

/-- In degree zero, under the identifications of `H⁰` with global sections, the inverse image map
on cohomology is the unit `F ⟶ f_* f⁻¹ F` on global sections. -/
lemma cohomologyPullback_zero (F : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
    (x : Sheaf.H.{u} F 0) :
    Sheaf.H.equiv₀ _ isTerminalTop (cohomologyPullback f F 0 x) =
      (((Opens.map f).sheafAdjunctionContinuous AddCommGrpCat.{u} (Opens.grothendieckTopology Y)
          (Opens.grothendieckTopology X)).unit.app F).hom.app (op ⊤)
        (Sheaf.H.equiv₀ F isTerminalTop x) := by
  obtain ⟨a, rfl⟩ : ∃ a, Ext.mk₀ a = x := ⟨Ext.addEquiv₀ x, Ext.mk₀_addEquiv₀_apply x⟩
  rw [cohomologyPullback_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]
  simp only [Sheaf.H.equiv₀, AddEquiv.trans_apply, ← Ext.addEquiv₀_symm_apply,
    AddEquiv.apply_symm_apply, Adjunction.homAddEquiv_apply,
    constantSheafAdj_homEquiv_pullbackConstantSheafIso_inv]
  rfl

end

end TauCeti.Topology
