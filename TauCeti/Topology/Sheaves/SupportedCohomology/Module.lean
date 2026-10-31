/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Module
public import TauCeti.Topology.Sheaves.SupportedCohomology
import TauCeti.Algebra.Homology.Ext.Basic

/-!
# Cohomology with closed supports for sheaves of modules

Let `R` be a commutative ring, `F` a sheaf of `R`-modules on a topological space `X`, `W` an open
subset and `S` a closed subset. The sections of `F` over `W` supported in `S` form the
`R`-submodule `Γ_S(W, F)` of `F(W)` of sections whose restriction to `W ∖ S` vanishes.

Write `R_O` for the free sheaf of `R`-modules on an open `O`
(`TauCeti.CategoryTheory.freeModuleYonedaSheafFunctor`) and `Q_S(W)` for the cokernel of
`R_{W ∖ S} ⟶ R_W`. Morphisms `Q_S(W) ⟶ F` are `R`-linearly the supported sections `Γ_S(W, F)`, and
the cohomology of `F` on `W` with supports in `S` is defined as `H_Sⁿ(W, F) = Extⁿ(Q_S(W), F)`, an
`R`-module. This is the `R`-linear counterpart of `CategoryTheory.Sheaf.supportedH`, which treats
sheaves of abelian groups with the free abelian sheaves in place of `R_O`.

For opens `W' ≤ W` the inclusion of pairs `(W', W' ∖ S) ⟶ (W, W ∖ S)` induces a morphism
`Q_S(W') ⟶ Q_S(W)`; this makes `W ↦ Q_S(W)` a functor, and applying `R`-linear `Ext` makes
`W ↦ H_Sⁿ(W, F)` a presheaf of `R`-modules, functorial in `F`. In degree zero it is `Γ_S(W, F)`
with the restriction of sections. On an open disjoint from `S` the cohomology with supports
in `S` vanishes.

## Main declarations

* `CategoryTheory.Sheaf.supportedSubmodule F S W`: the `R`-submodule `Γ_S(W, F)`;
* `TopologicalSpace.Closeds.supportedFreeModuleSheafFunctor R S`: the functor `W ↦ Q_S(W)`, and
  `TopologicalSpace.Closeds.supportedFreeModuleSheafHomEquiv`, the `R`-linear equivalence
  `(Q_S(W) ⟶ F) ≃ₗ[R] Γ_S(W, F)`, natural in `F` and compatible with restriction;
* `CategoryTheory.Sheaf.supportedModuleH F S W n`: the `R`-module `H_Sⁿ(W, F)`, and
  `CategoryTheory.Sheaf.supportedModuleHPresheaf F S n`, the presheaf of `R`-modules
  `W ↦ H_Sⁿ(W, F)`;
* `CategoryTheory.Sheaf.supportedModuleHZeroEquiv`: `H_S⁰(W, F) ≃ₗ[R] Γ_S(W, F)`, natural in `F`
  and compatible with restriction;
* `CategoryTheory.Sheaf.subsingleton_supportedModuleH_of_le_compl`: `H_Sⁿ(W, F) = 0` when `W` is
  disjoint from `S`.

## References

* A. Grothendieck, *Local cohomology*, Lecture Notes in Mathematics 41, §1.
* M. Kashiwara and P. Schapira, *Sheaves on Manifolds*, §2.3 and §2.6.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace Abelian TauCeti.CategoryTheory

universe u

variable {X : TopCat.{u}} (R : Type u) [CommRing R]

noncomputable section

namespace TopologicalSpace.Closeds

/-- The sheaf of `R`-modules `Q_S(W)`: the cokernel of the map `R_{W ∖ S} ⟶ R_W` of free sheaves of
`R`-modules induced by the inclusion `W ∖ S ⟶ W`. Its functoriality in `W` is induced by the
inclusions of pairs `(W', W' ∖ S) ⟶ (W, W ∖ S)`. -/
@[expose]
def supportedFreeModuleSheafFunctor (S : Closeds X) :
    Opens X ⥤ Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R) where
  obj W := relativeFreeModuleYonedaSheaf _ R (S.complInclusion W)
  map {W' W} h := relativeFreeModuleYonedaSheafMap _ R (S.complInclusion W')
    (S.complInclusion W) (homOfLE (inf_le_inf_right S.compl (leOfHom h))) h rfl
  map_id _ := relativeFreeModuleYonedaSheafMap_id _ R _
  map_comp _ _ := (relativeFreeModuleYonedaSheafMap_comp _ R _ _ _ _ _ _ _ _ _).symm

@[simp]
lemma supportedFreeModuleSheafFunctor_obj (S : Closeds X) (W : Opens X) :
    (supportedFreeModuleSheafFunctor R S).obj W =
      relativeFreeModuleYonedaSheaf _ R (S.complInclusion W) :=
  (rfl)

@[simp]
lemma supportedFreeModuleSheafFunctor_map (S : Closeds X) {W' W : Opens X} (h : W' ⟶ W) :
    (supportedFreeModuleSheafFunctor R S).map h =
      relativeFreeModuleYonedaSheafMap _ R (S.complInclusion W') (S.complInclusion W)
        (homOfLE (inf_le_inf_right S.compl (leOfHom h))) h rfl :=
  (rfl)

end TopologicalSpace.Closeds

namespace CategoryTheory.Sheaf

variable {R} (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))

/-- The `R`-submodule `Γ_S(W, F)` of sections of `F` over `W` supported in the closed subset `S`,
that is, whose restriction to `W ∖ S` vanishes. -/
def supportedSubmodule (S : Closeds X) (W : Opens X) : Submodule R (F.obj.obj (op W)) :=
  LinearMap.ker (F.obj.map (S.complInclusion W).op).hom

@[simp]
lemma mem_supportedSubmodule_iff {S : Closeds X} {W : Opens X} {s : F.obj.obj (op W)} :
    s ∈ F.supportedSubmodule S W ↔ F.obj.map (S.complInclusion W).op s = 0 :=
  Iff.rfl

/-- A morphism of sheaves of modules maps sections supported in `S` to sections supported
in `S`. -/
lemma map_mem_supportedSubmodule {F G : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)}
    (f : F ⟶ G) {S : Closeds X} {W : Opens X} {s : F.obj.obj (op W)}
    (hs : s ∈ F.supportedSubmodule S W) : f.hom.app (op W) s ∈ G.supportedSubmodule S W := by
  rw [mem_supportedSubmodule_iff] at hs ⊢
  simp [← NatTrans.naturality_apply, hs]

/-- The restriction of a section supported in `S` to a smaller open is supported in `S`. -/
lemma map_mem_supportedSubmodule_of_le {S : Closeds X} {W' W : Opens X} (h : W' ≤ W)
    {s : F.obj.obj (op W)} (hs : s ∈ F.supportedSubmodule S W) :
    F.obj.map (homOfLE h).op s ∈ F.supportedSubmodule S W' := by
  rw [mem_supportedSubmodule_iff] at hs ⊢
  -- both composites are the inclusion `W' ∖ S ⟶ W`
  simpa [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp] using
    congr(F.obj.map (homOfLE (inf_le_inf_right S.compl h)).op $hs)

end CategoryTheory.Sheaf

namespace TopologicalSpace.Closeds

/-- Morphisms `Q_S(W) ⟶ F` are `R`-linearly equivalent to the sections of `F` over `W` supported
in `S`. -/
def supportedFreeModuleSheafHomEquiv (S : Closeds X) (W : Opens X)
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) :
    ((supportedFreeModuleSheafFunctor R S).obj W ⟶ F) ≃ₗ[R] F.supportedSubmodule S W :=
  relativeFreeModuleYonedaSheafHomEquiv _ R (S.complInclusion W) F

@[simp]
lemma coe_supportedFreeModuleSheafHomEquiv_apply (S : Closeds X) (W : Opens X)
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))
    (g : (supportedFreeModuleSheafFunctor R S).obj W ⟶ F) :
    (supportedFreeModuleSheafHomEquiv R S W F g : F.obj.obj (op W)) =
      relativeFreeModuleYonedaSheafHomEquiv _ R (S.complInclusion W) F g :=
  (rfl)

/-- The equivalence `supportedFreeModuleSheafHomEquiv` is natural in the coefficient sheaf. -/
lemma coe_supportedFreeModuleSheafHomEquiv_comp (S : Closeds X) (W : Opens X)
    {F G : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)}
    (g : (supportedFreeModuleSheafFunctor R S).obj W ⟶ F) (f : F ⟶ G) :
    (supportedFreeModuleSheafHomEquiv R S W G (g ≫ f) : G.obj.obj (op W)) =
      f.hom.app (op W) (supportedFreeModuleSheafHomEquiv R S W F g) :=
  relativeFreeModuleYonedaSheafHomEquiv_naturality_right _ R _ g f

/-- Under `supportedFreeModuleSheafHomEquiv`, precomposition with `Q_S(W') ⟶ Q_S(W)` is the
restriction of supported sections from `W` to `W'`. -/
lemma coe_supportedFreeModuleSheafHomEquiv_map_comp (S : Closeds X) {W' W : Opens X}
    (h : W' ⟶ W) (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))
    (g : (supportedFreeModuleSheafFunctor R S).obj W ⟶ F) :
    (supportedFreeModuleSheafHomEquiv R S W' F ((supportedFreeModuleSheafFunctor R S).map h ≫ g) :
        F.obj.obj (op W')) =
      F.obj.map h.op (supportedFreeModuleSheafHomEquiv R S W F g) :=
  coe_relativeFreeModuleYonedaSheafHomEquiv_map_comp _ R _ _ _ _ _ F g

/-- On an open `W` disjoint from `S`, the sheaf `Q_S(W)` is zero. -/
lemma isZero_supportedFreeModuleSheafFunctor_obj (S : Closeds X) {W : Opens X}
    (hW : W ≤ S.compl) : IsZero ((supportedFreeModuleSheafFunctor R S).obj W) :=
  haveI : IsIso (S.complInclusion W) :=
    ⟨homOfLE (le_inf le_rfl hW), Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  isZero_relativeFreeModuleYonedaSheaf _ R _

end TopologicalSpace.Closeds

namespace CategoryTheory.Sheaf

variable {R} (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))

/-- The cohomology `H_Sⁿ(W, F)` of a sheaf of `R`-modules `F` on `W` with supports in the closed
subset `S`: the `R`-module `Extⁿ(Q_S(W), F)`. -/
abbrev supportedModuleH (S : Closeds X) (W : Opens X) (n : ℕ) : Type u :=
  Ext.{u} ((S.supportedFreeModuleSheafFunctor R).obj W) F n

/-- The presheaf of `R`-modules `W ↦ H_Sⁿ(W, F)`, whose restriction maps are induced by the maps
`Q_S(W') ⟶ Q_S(W)` for `W' ≤ W`. -/
@[expose]
def supportedModuleHPresheaf (S : Closeds X) (n : ℕ) : TopCat.Presheaf (ModuleCat.{u} R) X :=
  (S.supportedFreeModuleSheafFunctor R).op ⋙ (linearExtFunctor.{u} R _ n).flip.obj F

@[simp]
lemma supportedModuleHPresheaf_obj (S : Closeds X) (n : ℕ) (W : (Opens X)ᵒᵖ) :
    (F.supportedModuleHPresheaf S n).obj W = ModuleCat.of R (F.supportedModuleH S W.unop n) :=
  (rfl)

/-- The restriction maps of `supportedModuleHPresheaf` are precomposition with the maps
`Q_S(W') ⟶ Q_S(W)`. -/
@[simp]
lemma supportedModuleHPresheaf_map_apply (S : Closeds X) (n : ℕ) {W W' : (Opens X)ᵒᵖ}
    (h : W ⟶ W') (x : F.supportedModuleH S W.unop n) :
    (F.supportedModuleHPresheaf S n).map h x =
      (Ext.mk₀ ((S.supportedFreeModuleSheafFunctor R).map h.unop)).comp x (zero_add n) :=
  (rfl)

/-- The functor `F ↦ (W ↦ H_Sⁿ(W, F))` from sheaves of `R`-modules to presheaves of
`R`-modules. -/
@[expose]
def supportedModuleHPresheafFunctor (S : Closeds X) (n : ℕ) :
    Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R) ⥤ TopCat.Presheaf (ModuleCat.{u} R) X :=
  (linearExtFunctor.{u} R _ n).flip ⋙
    (Functor.whiskeringLeft _ _ _).obj (S.supportedFreeModuleSheafFunctor R).op

@[simp]
lemma supportedModuleHPresheafFunctor_obj (S : Closeds X) (n : ℕ) :
    (supportedModuleHPresheafFunctor S n).obj F = F.supportedModuleHPresheaf S n :=
  (rfl)

/-- The maps of presheaves `H_Sⁿ(-, F) ⟶ H_Sⁿ(-, G)` induced by a morphism `f : F ⟶ G` are
postcomposition with `f`. -/
@[simp]
lemma supportedModuleHPresheafFunctor_map_app_apply (S : Closeds X) (n : ℕ)
    {F G : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)} (f : F ⟶ G) (W : (Opens X)ᵒᵖ)
    (x : F.supportedModuleH S W.unop n) :
    ((supportedModuleHPresheafFunctor S n).map f).app W x = x.comp (Ext.mk₀ f) (add_zero n) :=
  (rfl)

/-- Cohomology with supports in `S` vanishes on an open `W` disjoint from `S`. -/
theorem subsingleton_supportedModuleH_of_le_compl (S : Closeds X) {W : Opens X}
    (hW : W ≤ S.compl) (n : ℕ) : Subsingleton (F.supportedModuleH S W n) :=
  TauCeti.subsingleton_ext_of_isZero_left (S.isZero_supportedFreeModuleSheafFunctor_obj R hW) F n

/-- Degree-zero cohomology with supports in `S` is the module `Γ_S(W, F)` of sections supported
in `S`. -/
def supportedModuleHZeroEquiv (S : Closeds X) (W : Opens X) :
    F.supportedModuleH S W 0 ≃ₗ[R] F.supportedSubmodule S W :=
  relativeFreeModuleYonedaExtZeroEquiv _ R (S.complInclusion W) F

@[simp]
lemma coe_supportedModuleHZeroEquiv_apply (S : Closeds X) (W : Opens X)
    (x : F.supportedModuleH S W 0) :
    (F.supportedModuleHZeroEquiv S W x : F.obj.obj (op W)) =
      relativeFreeModuleYonedaExtZeroEquiv _ R (S.complInclusion W) F x :=
  (rfl)

/-- The identification of degree-zero cohomology with supported sections is natural in the
coefficient sheaf. -/
lemma coe_supportedModuleHZeroEquiv_naturality_right (S : Closeds X) (W : Opens X)
    {F G : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)} (f : F ⟶ G)
    (x : F.supportedModuleH S W 0) :
    (G.supportedModuleHZeroEquiv S W (x.comp (Ext.mk₀ f) (add_zero 0)) : G.obj.obj (op W)) =
      f.hom.app (op W) (F.supportedModuleHZeroEquiv S W x) :=
  coe_relativeFreeModuleYonedaExtZeroEquiv_comp_mk₀ _ R _ x f

/-- The identification of degree-zero cohomology with supported sections commutes with
restriction. -/
lemma coe_supportedModuleHZeroEquiv_map (S : Closeds X) {W W' : (Opens X)ᵒᵖ} (h : W ⟶ W')
    (x : F.supportedModuleH S W.unop 0) :
    (F.supportedModuleHZeroEquiv S W'.unop ((F.supportedModuleHPresheaf S 0).map h x) :
        F.obj.obj W') =
      F.obj.map h (F.supportedModuleHZeroEquiv S W.unop x) :=
  coe_relativeFreeModuleYonedaExtZeroEquiv_mk₀_comp _ R (S.complInclusion W'.unop)
    (S.complInclusion W.unop) _ h.unop rfl F x

end CategoryTheory.Sheaf
