/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Exactness
public import TauCeti.Topology.Sheaves.SupportedCohomology.Module

/-!
# Flasque sheaves of modules are acyclic, also with supports

Let `R` be a commutative ring and `F` a flasque sheaf of `R`-modules on a topological space `X`,
that is, a sheaf all of whose restriction maps are surjective. This file proves that `F` has no
cohomology in positive degrees, in the three forms used for sheaves of `R`-modules in this
library:

* over an open `U`, `Extⁿ⁺¹(R_U, F) = 0`, where `R_U` is the free sheaf of `R`-modules on `U`;
* relative to an inclusion of opens `U ≤ V`, `Extⁿ⁺¹(R_{V,U}, F) = 0`, where `R_{V,U}` is the
  cokernel of `R_U ⟶ R_V`;
* with supports in a closed subset `S`, `H_Sⁿ⁺¹(W, F) = 0` for every open `W`.

This is the acyclicity input for computing the cohomology with supports `H_S^*(W, F)` of a sheaf
of `R`-modules (`CategoryTheory.Sheaf.supportedModuleH`) by flasque resolutions, the counterpart
of `CategoryTheory.Sheaf.relativeH'.subsingleton_succ_of_isFlasque` for sheaves of abelian
groups.

The proof is the classical dimension shift. Injective sheaves of `R`-modules are flasque, because
`Hom(-, I)` turns the monomorphism `R_U ⟶ R_V` of free sheaves into the restriction map of `I`.
Embedding a flasque `F` into an injective `I` gives a short exact sequence `0 ⟶ F ⟶ I ⟶ Q ⟶ 0`
whose sections over every open are short exact and whose cokernel `Q` is again flasque. Both
facts are Mathlib's theorems for flasque sheaves of abelian groups,
`TopCat.Sheaf.IsFlasque.epi_of_shortExact` and
`TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂`, applied to the underlying abelian sheaves.
The relative statement then follows from the long exact `Ext` sequence of
`0 ⟶ R_U ⟶ R_V ⟶ R_{V,U} ⟶ 0`: in degree one because sections of `F` over `U` extend to `V`,
and in higher degrees because `Extⁿ⁺¹(R_U, F)` and `Extⁿ⁺²(R_V, F)` vanish.

## Main declarations

* `CategoryTheory.Sheaf.isFlasque_of_injective_moduleCat`: injective sheaves of `R`-modules are
  flasque;
* `CategoryTheory.ShortComplex.ShortExact.surjective_app_of_isFlasque` and
  `CategoryTheory.ShortComplex.ShortExact.isFlasque_X₃_of_isFlasque`: in a short exact sequence
  `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` of sheaves of `R`-modules with `F₁` flasque, sections of `F₃` lift to
  `F₂`, and `F₃` is flasque when `F₂` is;
* `CategoryTheory.Sheaf.subsingleton_ext_freeModuleYonedaSheaf_succ_of_isFlasque`:
  `Extⁿ⁺¹(R_U, F) = 0` for flasque `F`;
* `CategoryTheory.Sheaf.subsingleton_ext_relativeFreeModuleYonedaSheaf_succ_of_isFlasque`:
  `Extⁿ⁺¹(R_{V,U}, F) = 0` for flasque `F`;
* `CategoryTheory.Sheaf.subsingleton_supportedModuleH_succ_of_isFlasque`: `H_Sⁿ⁺¹(W, F) = 0`
  for flasque `F`.

## References

* R. Hartshorne, *Algebraic Geometry*, III.2.4–2.5.
* A. Grothendieck, *Local cohomology*, Lecture Notes in Mathematics 41, §1.
* The Stacks Project, tag 09SY, Lemma 20.12.3, *Flasque sheaves*.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace Abelian
open TauCeti.CategoryTheory

universe u

namespace CategoryTheory.ShortComplex.ShortExact

variable {X : TopCat.{u}} {R : Type u} [Ring R]
  {S : ShortComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))} (hS : S.ShortExact)
include hS

/-- If `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` is a short exact sequence of sheaves of `R`-modules with `F₁`
flasque, then every section of `F₃` lifts to a section of `F₂`. -/
theorem surjective_app_of_isFlasque [TopCat.Presheaf.IsFlasque S.X₁.obj] (U : (Opens X)ᵒᵖ) :
    Function.Surjective (S.g.hom.app U) :=
  have : TopCat.Presheaf.IsFlasque
      (S.map (sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}))).X₁.obj :=
    TopCat.Presheaf.isFlasque_comp S.X₁.obj _
  (AddCommGrpCat.epi_iff_surjective _).1 <| TopCat.Sheaf.IsFlasque.epi_of_shortExact
    (Sheaf.shortExact_map_sheafCompose_forget₂_moduleCat hS) (U := U.unop)

/-- If `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` is a short exact sequence of sheaves of `R`-modules with `F₁` and
`F₂` flasque, then `F₃` is flasque. -/
theorem isFlasque_X₃_of_isFlasque [TopCat.Presheaf.IsFlasque S.X₁.obj]
    [TopCat.Presheaf.IsFlasque S.X₂.obj] : TopCat.Presheaf.IsFlasque S.X₃.obj :=
  have : TopCat.Presheaf.IsFlasque
      (S.map (sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}))).X₁.obj :=
    TopCat.Presheaf.isFlasque_comp S.X₁.obj _
  have : TopCat.Presheaf.IsFlasque
      (S.map (sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}))).X₂.obj :=
    TopCat.Presheaf.isFlasque_comp S.X₂.obj _
  (TopCat.Presheaf.isFlasque_comp_iff S.X₃.obj _).1
    (TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂
      (Sheaf.shortExact_map_sheafCompose_forget₂_moduleCat hS))

end CategoryTheory.ShortComplex.ShortExact

namespace CategoryTheory.Sheaf

variable {X : TopCat.{u}} {R : Type u} [CommRing R]

/-- An injective sheaf of `R`-modules is flasque. -/
instance isFlasque_of_injective_moduleCat
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) [Injective F] :
    TopCat.Presheaf.IsFlasque F.obj where
  -- Given `s : I(V)` and `V ≤ U`, represent `s` by `R_V ⟶ I`, extend it along the monomorphism
  -- `R_V ⟶ R_U` using injectivity, and translate the extension back to a section.
  epi {U V} i := by
    rw [ModuleCat.epi_iff_surjective]
    intro s
    refine ⟨freeModuleYonedaSheafSectionsEquiv _ R U.unop F
      (Injective.factorThru ((freeModuleYonedaSheafSectionsEquiv _ R V.unop F).symm s)
        ((freeModuleYonedaSheafFunctor _ R).map i.unop)), ?_⟩
    have h := freeModuleYonedaSheafSectionsEquiv_naturality_left _ R i.unop F
      (Injective.factorThru ((freeModuleYonedaSheafSectionsEquiv _ R V.unop F).symm s)
        ((freeModuleYonedaSheafFunctor _ R).map i.unop))
    rw [Injective.comp_factorThru, LinearEquiv.apply_symm_apply] at h
    exact h.symm

/-- A flasque sheaf of `R`-modules has no cohomology in positive degrees over any open subset:
`Extⁿ⁺¹(R_U, F) = 0`. -/
instance subsingleton_ext_freeModuleYonedaSheaf_succ_of_isFlasque
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) [TopCat.Presheaf.IsFlasque F.obj]
    (U : Opens X) (n : ℕ) :
    Subsingleton (Ext.{u} ((freeModuleYonedaSheafFunctor _ R).obj U) F (n + 1)) := by
  -- dimension shift along `0 ⟶ F ⟶ I ⟶ Q ⟶ 0` with `I` injective
  induction n generalizing F with
  | zero =>
    have hS := TauCeti.injectiveCokernelSequence_shortExact F
    refine TauCeti.subsingleton_ext_succ_of_injectiveCokernelSequence _ F 0 fun x₃ ↦ ?_
    -- the morphism `R_U ⟶ Q` underlying `x₃` lifts to `I`, because `F` is flasque
    obtain ⟨t, ht⟩ := hS.surjective_app_of_isFlasque (op U)
      (freeModuleYonedaSheafSectionsEquiv _ R U _ (Ext.addEquiv₀ x₃))
    have hx : x₃ = (Ext.mk₀ ((freeModuleYonedaSheafSectionsEquiv _ R U _).symm t)).comp
        (Ext.mk₀ (TauCeti.injectiveCokernelSequence F).g) (add_zero 0) := by
      rw [Ext.mk₀_comp_mk₀, ← Ext.mk₀_addEquiv₀_apply x₃]
      congr 1
      apply (freeModuleYonedaSheafSectionsEquiv _ R U _).injective
      rw [freeModuleYonedaSheafSectionsEquiv_naturality_right, LinearEquiv.apply_symm_apply, ht]
    rw [hx, Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]
  | succ n ih =>
    have hS := TauCeti.injectiveCokernelSequence_shortExact F
    refine TauCeti.subsingleton_ext_succ_of_injectiveCokernelSequence _ F (n + 1) fun x₃ ↦ ?_
    have : TopCat.Presheaf.IsFlasque (TauCeti.injectiveCokernelSequence F).X₁.obj := ‹_›
    have : TopCat.Presheaf.IsFlasque (TauCeti.injectiveCokernelSequence F).X₂.obj :=
      isFlasque_of_injective_moduleCat _
    -- `Q` is flasque, as a quotient of flasque sheaves
    have := @ih _ hS.isFlasque_X₃_of_isFlasque
    rw [Subsingleton.elim x₃ 0, Ext.zero_comp]

/-- A flasque sheaf of `R`-modules has no relative cohomology in positive degrees for an inclusion
of opens `U ≤ V`: `Extⁿ⁺¹(R_{V,U}, F) = 0`. -/
instance subsingleton_ext_relativeFreeModuleYonedaSheaf_succ_of_isFlasque
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) [TopCat.Presheaf.IsFlasque F.obj]
    {U V : Opens X} (i : U ⟶ V) (n : ℕ) :
    Subsingleton (Ext.{u} (relativeFreeModuleYonedaSheaf _ R i) F (n + 1)) := by
  -- the long exact sequence of `0 ⟶ R_U ⟶ R_V ⟶ R_{V,U} ⟶ 0` in the first variable
  have hS := relativeFreeModuleYonedaSequence_shortExact (Opens.grothendieckTopology X) R i
  -- state everything in terms of the objects of this sequence, so that the rewrites below see
  -- syntactically matching `Ext` groups
  refine subsingleton_of_forall_eq (0 : Ext (relativeFreeModuleYonedaSequence _ R i).X₃ F (n + 1))
    fun x ↦ ?_
  obtain ⟨y, rfl⟩ := Ext.contravariant_sequence_exact₃ hS F x
    ((subsingleton_ext_freeModuleYonedaSheaf_succ_of_isFlasque F V n).elim _ _) (add_comm 1 n)
  cases n with
  | zero =>
    -- the morphism `R_U ⟶ F` underlying `y` extends to `R_V`, because `F` is flasque
    obtain ⟨t, ht⟩ := (ModuleCat.epi_iff_surjective (F.obj.map i.op)).1 inferInstance
      (freeModuleYonedaSheafSectionsEquiv _ R U F (Ext.addEquiv₀ y))
    obtain ⟨g, hg⟩ : ∃ g : (relativeFreeModuleYonedaSequence _ R i).X₂ ⟶ F,
        (relativeFreeModuleYonedaSequence _ R i).f ≫ g = Ext.addEquiv₀ y :=
      ⟨(freeModuleYonedaSheafSectionsEquiv _ R V F).symm t,
        (freeModuleYonedaSheafSectionsEquiv _ R U F).injective <|
          (freeModuleYonedaSheafSectionsEquiv_naturality_left _ R i F _).trans <| by
            rw [LinearEquiv.apply_symm_apply]
            exact ht⟩
    rw [← Ext.mk₀_addEquiv₀_apply y, ← hg, ← Ext.mk₀_comp_mk₀,
      ← Ext.comp_assoc_of_second_deg_zero, hS.extClass_comp, Ext.zero_comp]
  | succ n =>
    have : Subsingleton (Ext.{u} (relativeFreeModuleYonedaSequence _ R i).X₁ F (n + 1)) :=
      subsingleton_ext_freeModuleYonedaSheaf_succ_of_isFlasque F U n
    rw [Subsingleton.elim y 0, Ext.comp_zero]

/-- A flasque sheaf of `R`-modules has no cohomology with supports in positive degrees:
`H_Sⁿ⁺¹(W, F) = 0` for every closed `S` and open `W`. -/
instance subsingleton_supportedModuleH_succ_of_isFlasque
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) [TopCat.Presheaf.IsFlasque F.obj]
    (S : Closeds X) (W : Opens X) (n : ℕ) : Subsingleton (F.supportedModuleH S W (n + 1)) :=
  subsingleton_ext_relativeFreeModuleYonedaSheaf_succ_of_isFlasque F (S.complInclusion W) n

end CategoryTheory.Sheaf
