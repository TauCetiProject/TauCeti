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
import TauCeti.CategoryTheory.Abelian.DiagramLemmas.CokernelComp

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

*Excision* says that cohomology with supports in `S` only depends on a neighbourhood of `S`: if
`W' ≤ W` and `S ∩ W ⊆ W'`, the map `Q_S(W') ⟶ Q_S(W)` is an isomorphism, because a section over
`W'` supported in `S` glues with zero on `W ∖ S` to a unique section over `W` supported in `S`.
Hence restriction is an `R`-linear isomorphism `H_Sⁿ(W, F) ≃ₗ[R] H_Sⁿ(W', F)`.

For closed subsets `Z ≤ S` the inclusions of pairs `(W, W ∖ S) ⟶ (W, W ∖ Z)` give maps
`Q_S(W) ⟶ Q_Z(W)`, and since `(W ∖ Z) ∖ S = W ∖ S` the sequence
`0 ⟶ Q_S(W ∖ Z) ⟶ Q_S(W) ⟶ Q_Z(W) ⟶ 0` is short exact. Its long exact `Ext` sequence is the long
exact sequence of supports

`⋯ ⟶ H_Zⁿ(W, F) ⟶ H_Sⁿ(W, F) ⟶ H_Sⁿ(W ∖ Z, F) ⟶ H_Zⁿ⁺¹(W, F) ⟶ ⋯`,

whose first map enlarges the support and whose second map is restriction to `W ∖ Z`.

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
  disjoint from `S`;
* `CategoryTheory.Sheaf.existsUnique_mem_supportedSubmodule_map_eq`: excision for sections
  supported in `S`;
* `TopologicalSpace.Closeds.isIso_supportedFreeModuleSheafFunctor_map`: excision for the sheaves
  `Q_S(W)`;
* `CategoryTheory.Sheaf.supportedModuleHExcisionEquiv`: excision
  `H_Sⁿ(W, F) ≃ₗ[R] H_Sⁿ(W', F)` when `S ∩ W ⊆ W'`;
* `TopologicalSpace.Closeds.supportedFreeModuleSheafSequence_shortExact`: for `Z ≤ S`, the sequence
  `0 ⟶ Q_S(W ∖ Z) ⟶ Q_S(W) ⟶ Q_Z(W) ⟶ 0` is short exact;
* `CategoryTheory.Sheaf.supportedModuleHPresheafMap` and `CategoryTheory.Sheaf.supportedModuleHδ`:
  for `Z ≤ S`, the morphism of presheaves `H_Zⁿ(-, F) ⟶ H_Sⁿ(-, F)` and the connecting map
  `H_Sⁿ(W ∖ Z, F) ⟶ H_Zⁿ⁺¹(W, F)` of the long exact sequence of supports, whose exactness is
  `CategoryTheory.Sheaf.exact_supportedModuleHPresheafMap_app_supportedModuleHPresheaf_map`,
  `CategoryTheory.Sheaf.exact_supportedModuleHPresheaf_map_supportedModuleHδ` and
  `CategoryTheory.Sheaf.exact_supportedModuleHδ_supportedModuleHPresheafMap_app`.

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

/-! ### Excision -/

namespace CategoryTheory.Sheaf

variable {R} (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))

/-- Excision for sections with supports: if `W' ≤ W` and `S ∩ W ⊆ W'` (that is,
`W ≤ W' ⊔ (X ∖ S)`), then every section over `W'` supported in `S` is the restriction of a unique
section over `W` supported in `S`, namely the one gluing it with zero on `W ∖ S`. -/
theorem existsUnique_mem_supportedSubmodule_map_eq {S : Closeds X} {W' W : Opens X} (h : W' ≤ W)
    (hW : W ≤ W' ⊔ S.compl) {s : F.obj.obj (op W')} (hs : s ∈ F.supportedSubmodule S W') :
    ∃! t : F.obj.obj (op W), t ∈ F.supportedSubmodule S W ∧ F.obj.map (homOfLE h).op t = s := by
  -- The statement only involves the underlying sheaf of abelian groups `G`, whose sections and
  -- restriction maps are definitionally those of `F`, so it is the abelian excision for `G`.
  let G := (sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F
  have hmem {V : Opens X} {t : F.obj.obj (op V)} :
      t ∈ F.supportedSubmodule S V ↔ t ∈ G.supportedSections S V :=
    F.mem_supportedSubmodule_iff.trans G.mem_supportedSections_iff.symm
  obtain ⟨t, ⟨ht, hts⟩, hu⟩ := G.existsUnique_mem_supportedSections_map_eq h hW (hmem.1 hs)
  exact ⟨t, ⟨hmem.2 ht, hts⟩, fun t' ⟨ht', hts'⟩ ↦ hu t' ⟨hmem.1 ht', hts'⟩⟩

end CategoryTheory.Sheaf

namespace TopologicalSpace.Closeds

/-- Precomposing the map `Q_S(W') ⟶ Q_S(W)` with the quotient map `R_W' ⟶ Q_S(W')` is the
quotient map `R_W ⟶ Q_S(W)` precomposed with the map `R_W' ⟶ R_W`. -/
@[reassoc]
lemma cokernel_π_supportedFreeModuleSheafFunctor_map (S : Closeds X) {W' W : Opens X}
    (h : W' ⟶ W) :
    cokernel.π _ ≫ (S.supportedFreeModuleSheafFunctor R).map h =
      (freeModuleYonedaSheafFunctor _ R).map h ≫ cokernel.π _ :=
  cokernel_π_relativeFreeModuleYonedaSheafMap _ R _ _ _ _ _

/-- Excision for the sheaves `Q_S(W)`: if `W' ≤ W` and `S ∩ W ⊆ W'` (that is,
`W ≤ W' ⊔ (X ∖ S)`), the map `Q_S(W') ⟶ Q_S(W)` is an isomorphism. -/
theorem isIso_supportedFreeModuleSheafFunctor_map (S : Closeds X) {W' W : Opens X} (h : W' ≤ W)
    (hW : W ≤ W' ⊔ S.compl) : IsIso ((S.supportedFreeModuleSheafFunctor R).map (homOfLE h)) :=
  (isIso_relativeFreeModuleYonedaSheafMap_iff _ R _ _ _ _ _).2 fun F _ hs ↦
    F.existsUnique_mem_supportedSubmodule_map_eq h hW hs

end TopologicalSpace.Closeds

namespace CategoryTheory.Sheaf

variable {R} (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))

/-- Excision for cohomology with supports: if `W' ≤ W` and `S ∩ W ⊆ W'` (that is,
`W ≤ W' ⊔ (X ∖ S)`), restriction is an `R`-linear isomorphism
`H_Sⁿ(W, F) ≃ₗ[R] H_Sⁿ(W', F)`. -/
def supportedModuleHExcisionEquiv (S : Closeds X) {W' W : Opens X} (h : W' ≤ W)
    (hW : W ≤ W' ⊔ S.compl) (n : ℕ) :
    F.supportedModuleH S W n ≃ₗ[R] F.supportedModuleH S W' n :=
  have := S.isIso_supportedFreeModuleSheafFunctor_map R h hW
  TauCeti.extLinearEquivOfIso R
    (asIso ((S.supportedFreeModuleSheafFunctor R).map (homOfLE h))).symm (Iso.refl F) n

@[simp]
lemma supportedModuleHExcisionEquiv_apply (S : Closeds X) {W' W : Opens X} (h : W' ≤ W)
    (hW : W ≤ W' ⊔ S.compl) {n : ℕ} (x : F.supportedModuleH S W n) :
    F.supportedModuleHExcisionEquiv S h hW n x =
      (F.supportedModuleHPresheaf S n).map (homOfLE h).op x := by
  -- Keep the map `Q_S(W') ⟶ Q_S(W)` folded, so that `asIso_hom` applies.
  simp [supportedModuleHExcisionEquiv, supportedModuleHPresheaf_map_apply,
    -Closeds.supportedFreeModuleSheafFunctor_map]

end CategoryTheory.Sheaf

/-! ### The long exact sequence of supports -/

namespace TopologicalSpace.Closeds

variable {R} {Z S : Closeds X}

variable (R) in
/-- For closed subsets `Z ≤ S`, the natural map `Q_S(W) ⟶ Q_Z(W)` induced by the inclusions of
pairs `(W, W ∖ S) ⟶ (W, W ∖ Z)`. -/
def supportedFreeModuleSheafFunctorMap (hZS : Z ≤ S) :
    S.supportedFreeModuleSheafFunctor R ⟶ Z.supportedFreeModuleSheafFunctor R where
  app W := relativeFreeModuleYonedaSheafMap _ R (S.complInclusion W) (Z.complInclusion W)
    (homOfLE (inf_le_inf_left W ((Closeds.complOrderIso X).monotone hZS))) (𝟙 W) rfl
  -- both composites are induced by morphisms of pairs `(W', W' ∖ S) ⟶ (W, W ∖ Z)`, which agree
  -- because `Opens X` is a thin category
  naturality W' W h :=
    (relativeFreeModuleYonedaSheafMap_comp _ R (S.complInclusion W) (Z.complInclusion W) _ (𝟙 W)
      rfl (S.complInclusion W') _ h _).trans
    (relativeFreeModuleYonedaSheafMap_comp _ R (Z.complInclusion W') (Z.complInclusion W) _ h _
      (S.complInclusion W') _ (𝟙 W') rfl).symm

@[simp, reassoc]
lemma cokernel_π_supportedFreeModuleSheafFunctorMap_app (hZS : Z ≤ S) (W : Opens X) :
    cokernel.π _ ≫ (supportedFreeModuleSheafFunctorMap R hZS).app W = cokernel.π _ := by
  refine (cokernel_π_relativeFreeModuleYonedaSheafMap _ R _ _ _ _ _).trans ?_
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

@[simp]
lemma supportedFreeModuleSheafFunctorMap_refl (Z : Closeds X) :
    supportedFreeModuleSheafFunctorMap R (le_refl Z) = 𝟙 _ :=
  NatTrans.ext <| funext fun W ↦ relativeFreeModuleYonedaSheafMap_id _ R (Z.complInclusion W)

@[reassoc (attr := simp)]
lemma supportedFreeModuleSheafFunctorMap_comp {T : Closeds X} (hZS : Z ≤ S) (hST : S ≤ T) :
    supportedFreeModuleSheafFunctorMap R hST ≫ supportedFreeModuleSheafFunctorMap R hZS =
      supportedFreeModuleSheafFunctorMap R (hZS.trans hST) :=
  -- the composite morphism of pairs is the one for `Z ≤ T`, as `Opens X` is a thin category
  NatTrans.ext <| funext fun W ↦ relativeFreeModuleYonedaSheafMap_comp _ R (S.complInclusion W)
    (Z.complInclusion W) _ (𝟙 W) rfl (T.complInclusion W) _ (𝟙 W) rfl

/-- For closed subsets `Z ≤ S` and an open `W`, the composite `Q_S(W ∖ Z) ⟶ Q_S(W) ⟶ Q_Z(W)`
vanishes. -/
@[reassoc]
lemma supportedFreeModuleSheafFunctor_map_comp_supportedFreeModuleSheafFunctorMap_app
    (hZS : Z ≤ S) (W : Opens X) :
    (S.supportedFreeModuleSheafFunctor R).map (Z.complInclusion W) ≫
      (supportedFreeModuleSheafFunctorMap R hZS).app W = 0 :=
  TauCeti.comp_eq_zero_of_epi (π₁ := cokernel.π ((freeModuleYonedaSheafFunctor _ R).map
    (S.complInclusion (W ⊓ Z.compl)))) inferInstance (cokernel.condition _)
    (cokernel_π_supportedFreeModuleSheafFunctor_map R S _)
    (cokernel_π_supportedFreeModuleSheafFunctorMap_app hZS W)

variable (R) in
/-- For closed subsets `Z ≤ S` and an open `W`, the sequence `Q_S(W ∖ Z) ⟶ Q_S(W) ⟶ Q_Z(W)`, whose
first map comes from the inclusion `W ∖ Z ⟶ W` and whose second map compares the supports. -/
abbrev supportedFreeModuleSheafSequence (hZS : Z ≤ S) (W : Opens X) :
    ShortComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) :=
  ShortComplex.mk ((S.supportedFreeModuleSheafFunctor R).map (Z.complInclusion W))
    ((supportedFreeModuleSheafFunctorMap R hZS).app W)
    (supportedFreeModuleSheafFunctor_map_comp_supportedFreeModuleSheafFunctorMap_app hZS W)

variable (R) in
/-- For closed subsets `Z ≤ S` and an open `W`, the sequence
`0 ⟶ Q_S(W ∖ Z) ⟶ Q_S(W) ⟶ Q_Z(W) ⟶ 0` is short exact. It is the sequence of relative free
sheaves of the triple `(W ∖ Z) ∖ S ⟶ W ∖ Z ⟶ W`, as `(W ∖ Z) ∖ S = W ∖ S`. -/
lemma supportedFreeModuleSheafSequence_shortExact (hZS : Z ≤ S) (W : Opens X) :
    (supportedFreeModuleSheafSequence R hZS W).ShortExact := by
  let P := freeModuleYonedaSheafFunctor (Opens.grothendieckTopology X) R
  -- the inclusion `(W ∖ Z) ∖ S ⟶ W ∖ S` is an isomorphism of opens
  let e : W ⊓ Z.compl ⊓ S.compl ⟶ W ⊓ S.compl := homOfLE (inf_le_inf_right S.compl inf_le_left)
  have : IsIso e := homOfLE_isIso_of_eq _ (by rw [inf_assoc,
    inf_eq_right.2 (show S.compl ≤ Z.compl from (Closeds.complOrderIso X).monotone hZS)])
  -- the two composites `(W ∖ Z) ∖ S ⟶ W` agree in the thin category `Opens X`
  have hk : P.map (S.complInclusion (W ⊓ Z.compl) ≫ Z.complInclusion W) =
      P.map e ≫ P.map (S.complInclusion W) := by
    rw [← P.map_comp]
    rfl
  exact TauCeti.shortExact_of_isColimit_cokernelCofork (P.map_comp _ _).symm inferInstance
    (cokernelIsCokernel _) (isCokernelEpiComp (cokernelIsCokernel _) _ hk) (cokernelIsCokernel _)
    (cokernel_π_supportedFreeModuleSheafFunctor_map R S _)
    (cokernel_π_supportedFreeModuleSheafFunctorMap_app hZS W)

end TopologicalSpace.Closeds

namespace CategoryTheory.Sheaf

variable {R} (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) {Z S : Closeds X}

/-- For closed subsets `Z ≤ S`, the morphism of presheaves `H_Zⁿ(-, F) ⟶ H_Sⁿ(-, F)` enlarging
the support, induced by the maps `Q_S(W) ⟶ Q_Z(W)`. -/
def supportedModuleHPresheafMap (hZS : Z ≤ S) (n : ℕ) :
    F.supportedModuleHPresheaf Z n ⟶ F.supportedModuleHPresheaf S n :=
  Functor.whiskerRight (NatTrans.op (Closeds.supportedFreeModuleSheafFunctorMap R hZS))
    ((linearExtFunctor.{u} R _ n).flip.obj F)

@[simp]
lemma supportedModuleHPresheafMap_app_apply (hZS : Z ≤ S) (n : ℕ) (W : (Opens X)ᵒᵖ)
    (x : F.supportedModuleH Z W.unop n) :
    (F.supportedModuleHPresheafMap hZS n).app W x =
      (Ext.mk₀ ((Closeds.supportedFreeModuleSheafFunctorMap R hZS).app W.unop)).comp x
        (zero_add n) :=
  (rfl)

lemma supportedModuleHPresheafMap_refl_app_apply (Z : Closeds X) (n : ℕ) (W : (Opens X)ᵒᵖ)
    (x : F.supportedModuleH Z W.unop n) :
    (F.supportedModuleHPresheafMap (le_refl Z) n).app W x = x := by
  rw [supportedModuleHPresheafMap_app_apply, Closeds.supportedFreeModuleSheafFunctorMap_refl,
    NatTrans.id_app, Ext.mk₀_id_comp]

lemma supportedModuleHPresheafMap_app_supportedModuleHPresheafMap_app {T : Closeds X}
    (hZS : Z ≤ S) (hST : S ≤ T) (n : ℕ) (W : (Opens X)ᵒᵖ) (x : F.supportedModuleH Z W.unop n) :
    (F.supportedModuleHPresheafMap hST n).app W ((F.supportedModuleHPresheafMap hZS n).app W x) =
      (F.supportedModuleHPresheafMap (hZS.trans hST) n).app W x := by
  simp only [supportedModuleHPresheafMap_app_apply]
  rw [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, ← NatTrans.comp_app,
    Closeds.supportedFreeModuleSheafFunctorMap_comp]

@[simp]
lemma supportedModuleHPresheafMap_refl (Z : Closeds X) (n : ℕ) :
    F.supportedModuleHPresheafMap (le_refl Z) n = 𝟙 _ := by
  ext W x
  exact F.supportedModuleHPresheafMap_refl_app_apply Z n (op W) x

@[reassoc (attr := simp)]
lemma supportedModuleHPresheafMap_comp {T : Closeds X} (hZS : Z ≤ S) (hST : S ≤ T) (n : ℕ) :
    F.supportedModuleHPresheafMap hZS n ≫ F.supportedModuleHPresheafMap hST n =
      F.supportedModuleHPresheafMap (hZS.trans hST) n := by
  ext W x
  exact F.supportedModuleHPresheafMap_app_supportedModuleHPresheafMap_app hZS hST n (op W) x

/-- Under `supportedModuleHZeroEquiv`, enlarging the support in degree zero is the inclusion of
`Γ_Z(W, F)` in `Γ_S(W, F)`. -/
lemma coe_supportedModuleHZeroEquiv_supportedModuleHPresheafMap_app (hZS : Z ≤ S) (W : Opens X)
    (x : F.supportedModuleH Z W 0) :
    (F.supportedModuleHZeroEquiv S W ((F.supportedModuleHPresheafMap hZS 0).app (op W) x) :
        F.obj.obj (op W)) =
      F.supportedModuleHZeroEquiv Z W x :=
  (coe_relativeFreeModuleYonedaExtZeroEquiv_mk₀_comp _ R (S.complInclusion W)
    (Z.complInclusion W) _ (𝟙 W) rfl F x).trans <| by
    rw [op_id, F.obj.map_id, ModuleCat.id_apply, coe_supportedModuleHZeroEquiv_apply]

/-- The connecting map `H_Sⁿ(W ∖ Z, F) ⟶ H_Zⁿ⁺¹(W, F)` of the long exact sequence of supports for
closed subsets `Z ≤ S`: the Yoneda product with the extension class of the short exact sequence
`0 ⟶ Q_S(W ∖ Z) ⟶ Q_S(W) ⟶ Q_Z(W) ⟶ 0`. -/
def supportedModuleHδ (hZS : Z ≤ S) (W : Opens X) {n₀ n₁ : ℕ} (h : 1 + n₀ = n₁) :
    F.supportedModuleH S (W ⊓ Z.compl) n₀ →ₗ[R] F.supportedModuleH Z W n₁ :=
  Ext.precompOfLinear (Closeds.supportedFreeModuleSheafSequence_shortExact R hZS W).extClass R F h

lemma supportedModuleHδ_apply (hZS : Z ≤ S) (W : Opens X) {n₀ n₁ : ℕ} (h : 1 + n₀ = n₁)
    (x : F.supportedModuleH S (W ⊓ Z.compl) n₀) :
    F.supportedModuleHδ hZS W h x =
      (Closeds.supportedFreeModuleSheafSequence_shortExact R hZS W).extClass.comp x h :=
  (rfl)

/-- The long exact sequence of supports
`⋯ ⟶ H_Zⁿ(W, F) ⟶ H_Sⁿ(W, F) ⟶ H_Sⁿ(W ∖ Z, F) ⟶ H_Zⁿ⁺¹(W, F) ⟶ ⋯` for closed subsets `Z ≤ S` is
exact at `H_Sⁿ(W, F)`: a class with supports in `S` comes from a class with supports in `Z`
exactly when it restricts to zero on `W ∖ Z`. -/
theorem exact_supportedModuleHPresheafMap_app_supportedModuleHPresheaf_map (hZS : Z ≤ S)
    (W : Opens X) (n : ℕ) :
    Function.Exact ((F.supportedModuleHPresheafMap hZS n).app (op W))
      ((F.supportedModuleHPresheaf S n).map (Z.complInclusion W).op) :=
  TauCeti.exact_precomp (Closeds.supportedFreeModuleSheafSequence_shortExact R hZS W) F n

/-- The long exact sequence of supports for closed subsets `Z ≤ S` is exact at
`H_Sⁿ(W ∖ Z, F)`: the kernel of the connecting map consists of the restrictions of classes on `W`
with supports in `S`. -/
theorem exact_supportedModuleHPresheaf_map_supportedModuleHδ (hZS : Z ≤ S) (W : Opens X)
    {n₀ n₁ : ℕ} (h : 1 + n₀ = n₁) :
    Function.Exact ((F.supportedModuleHPresheaf S n₀).map (Z.complInclusion W).op)
      (F.supportedModuleHδ hZS W h) :=
  TauCeti.exact_precomp₁ (Closeds.supportedFreeModuleSheafSequence_shortExact R hZS W) F n₀ n₁ h

/-- The long exact sequence of supports for closed subsets `Z ≤ S` is exact at
`H_Zⁿ⁺¹(W, F)`: a class with supports in `Z` becomes zero with supports in `S` exactly when it
comes from `H_Sⁿ(W ∖ Z, F)` under the connecting map. -/
theorem exact_supportedModuleHδ_supportedModuleHPresheafMap_app (hZS : Z ≤ S) (W : Opens X)
    {n₀ n₁ : ℕ} (h : 1 + n₀ = n₁) :
    Function.Exact (F.supportedModuleHδ hZS W h)
      ((F.supportedModuleHPresheafMap hZS n₁).app (op W)) :=
  TauCeti.exact_precomp₃ (Closeds.supportedFreeModuleSheafSequence_shortExact R hZS W) F n₀ n₁ h

end CategoryTheory.Sheaf
