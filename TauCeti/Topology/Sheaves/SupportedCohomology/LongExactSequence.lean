/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sheaves.Flasque.Module
public import TauCeti.Topology.Sheaves.SupportedCohomology.Sections
import TauCeti.Algebra.Homology.ShortComplex.FunctorCategory
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The coefficient sequence for module-valued supported cohomology

A short exact sequence `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` of sheaves of `R`-modules gives a
connecting morphism `H_Sⁿ(-, F₃) ⟶ H_Sⁿ⁺¹(-, F₁)` of supported cohomology
presheaves (`CategoryTheory.Sheaf.supportedModuleHPresheafδ`), defined as Yoneda
postcomposition (`CategoryTheory.Sheaf.supportedModuleHPresheafPostcomp`, from
`TauCeti.Topology.Sheaves.SupportedCohomology.Module`) with its extension class.
This is the `R`-linear counterpart of the abelian-group connecting-morphism and
flasque-isomorphism API (`CategoryTheory.Sheaf.supportedHPresheafδ`,
`CategoryTheory.Sheaf.isIso_supportedHPresheafPostcomp_extClass`,
`CategoryTheory.Sheaf.isIso_supportedHPresheafPostcomp_mk₀_g`, and
`CategoryTheory.Sheaf.relativeH'.mk₀_g_postcomp_bijective_of_isFlasque`) in
`TauCeti.Topology.Sheaves.SupportedCohomology`.

These maps commute with enlarging the closed support and with morphisms of short
exact sequences, and give an exact coefficient sequence. A flasque middle term
makes the positive-degree connecting maps dimension-shift isomorphisms and all
connecting maps epimorphisms; a flasque kernel makes the positive-degree quotient
maps isomorphisms. Read through the identification of degree-zero supported
cohomology with supported sections, the degree-zero connecting map
`Γ_S(-, F₃) ⟶ H_S¹(-, F₁)` is exact after `Γ_S(-, F₂) ⟶ Γ_S(-, F₃)`, and
surjective when the middle term is flasque.

Sheafification of this sequence is treated in
`TauCeti.Topology.Sheaves.LocalCohomology.LongExactSequence`.

## References

* A. Grothendieck, *Local cohomology*, Lecture Notes in Mathematics 41, §1.
* M. Kashiwara and P. Schapira, *Sheaves on Manifolds*, §2.6.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace Abelian

universe u

namespace CategoryTheory.Sheaf

variable {X : TopCat.{u}} {R : Type u} [CommRing R] (S : Closeds X)
  {T T' : ShortComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))}

noncomputable section

/-- If `F₂` is flasque, the connecting morphism `H_Sᵃ⁺¹(-, F₃) ⟶ H_Sᵏ(-, F₁)`,
for `k = a + 2`, is an isomorphism of presheaves. -/
theorem isIso_supportedModuleHPresheafPostcomp_extClass (hT : T.ShortExact)
    [TopCat.Presheaf.IsFlasque T.X₂.obj] {a k : ℕ} (hk : a + 1 + 1 = k) :
    IsIso (supportedModuleHPresheafPostcomp S hT.extClass hk) :=
  isIso_supportedModuleHPresheafPostcomp S _ _ fun W ↦ by
    subst hk
    exact hT.extClass_postcomp_bijective _ rfl inferInstance inferInstance

/-- The connecting morphism of supported cohomology presheaves for a short exact
sequence of coefficient sheaves, given by its Yoneda extension class. -/
def supportedModuleHPresheafδ (hT : T.ShortExact) (n : ℕ) :
    T.X₃.supportedModuleHPresheaf S n ⟶ T.X₁.supportedModuleHPresheaf S (n + 1) :=
  supportedModuleHPresheafPostcomp S hT.extClass rfl

/-- For the extension class of a short exact sequence, Yoneda postcomposition is the
connecting morphism `CategoryTheory.Sheaf.supportedModuleHPresheafδ`. -/
@[simp]
lemma supportedModuleHPresheafPostcomp_extClass (hT : T.ShortExact) (n : ℕ) :
    supportedModuleHPresheafPostcomp S hT.extClass rfl = supportedModuleHPresheafδ S hT n :=
  (rfl)

@[simp]
lemma supportedModuleHPresheafδ_app_apply (hT : T.ShortExact) (n : ℕ)
    (W : (Opens X)ᵒᵖ) (x : T.X₃.supportedModuleH S W.unop n) :
    (supportedModuleHPresheafδ S hT n).app W x = x.comp hT.extClass rfl :=
  supportedModuleHPresheafPostcomp_app_apply S hT.extClass rfl W x

variable {S} in
/-- Enlarging the support from `Z` to `S` commutes with the connecting morphisms
of a short exact sequence of coefficients. -/
@[reassoc]
lemma supportedModuleHPresheafMap_δ {Z : Closeds X} (hZS : Z ≤ S) (hT : T.ShortExact) (n : ℕ) :
    T.X₃.supportedModuleHPresheafMap hZS n ≫ supportedModuleHPresheafδ S hT n =
      supportedModuleHPresheafδ Z hT n ≫ T.X₁.supportedModuleHPresheafMap hZS (n + 1) :=
  supportedModuleHPresheafMap_supportedModuleHPresheafPostcomp hZS hT.extClass rfl

/-- The connecting morphism is natural in short exact sequences of coefficients. -/
@[reassoc]
lemma supportedModuleHPresheafδ_naturality (hT : T.ShortExact) (hT' : T'.ShortExact)
    (f : T ⟶ T') (n : ℕ) :
    (supportedModuleHPresheafFunctor S n).map f.τ₃ ≫ supportedModuleHPresheafδ S hT' n =
      supportedModuleHPresheafδ S hT n ≫
        (supportedModuleHPresheafFunctor S (n + 1)).map f.τ₁ := by
  have h : supportedModuleHPresheafPostcomp S (Ext.mk₀ f.τ₃) (add_zero n) ≫
      supportedModuleHPresheafPostcomp S hT'.extClass rfl =
      supportedModuleHPresheafPostcomp S hT.extClass rfl ≫
      supportedModuleHPresheafPostcomp S (Ext.mk₀ f.τ₁) (add_zero (n + 1)) := by
    rw [supportedModuleHPresheafPostcomp_comp (hp := zero_add 1),
      supportedModuleHPresheafPostcomp_comp (hp := add_zero 1), hT.extClass_naturality hT' f]
  simp only [supportedModuleHPresheafPostcomp_mk₀, supportedModuleHPresheafPostcomp_extClass] at h
  exact h

@[simp, reassoc]
lemma supportedModuleHPresheafFunctor_map_g_δ (hT : T.ShortExact) (n : ℕ) :
    (supportedModuleHPresheafFunctor S n).map T.g ≫ supportedModuleHPresheafδ S hT n = 0 := by
  have h : supportedModuleHPresheafPostcomp S (Ext.mk₀ T.g) (add_zero n) ≫
      supportedModuleHPresheafPostcomp S hT.extClass rfl = 0 := by
    rw [supportedModuleHPresheafPostcomp_comp (hp := zero_add 1), hT.comp_extClass,
      supportedModuleHPresheafPostcomp_zero]
  simp only [supportedModuleHPresheafPostcomp_mk₀, supportedModuleHPresheafPostcomp_extClass] at h
  exact h

@[simp, reassoc]
lemma supportedModuleHPresheafδ_map_f (hT : T.ShortExact) (n : ℕ) :
    supportedModuleHPresheafδ S hT n ≫
      (supportedModuleHPresheafFunctor S (n + 1)).map T.f = 0 := by
  have h : supportedModuleHPresheafPostcomp S hT.extClass rfl ≫
      supportedModuleHPresheafPostcomp S (Ext.mk₀ T.f) (add_zero (n + 1)) = 0 := by
    rw [supportedModuleHPresheafPostcomp_comp (hp := add_zero 1), hT.extClass_comp,
      supportedModuleHPresheafPostcomp_zero]
  simp only [supportedModuleHPresheafPostcomp_mk₀, supportedModuleHPresheafPostcomp_extClass] at h
  exact h

/-- The coefficient sequence is exact at the middle supported cohomology presheaf. -/
theorem exact_map_supportedModuleHPresheafFunctor (hT : T.ShortExact) (n : ℕ) :
    (T.map (supportedModuleHPresheafFunctor S n)).Exact := by
  rw [ShortComplex.exact_iff_evaluation]
  intro W
  rw [ShortComplex.moduleCat_exact_iff]
  exact fun x hx ↦ Ext.covariant_sequence_exact₂ _ hT x hx

/-- The coefficient sequence is exact immediately before its connecting map. -/
theorem exact_supportedModuleHPresheafFunctor_map_g_δ (hT : T.ShortExact) (n : ℕ) :
    (ShortComplex.mk ((supportedModuleHPresheafFunctor S n).map T.g)
      (supportedModuleHPresheafδ S hT n)
      (supportedModuleHPresheafFunctor_map_g_δ S hT n)).Exact := by
  rw [ShortComplex.exact_iff_evaluation]
  intro W
  rw [ShortComplex.moduleCat_exact_iff]
  exact fun x hx ↦ Ext.covariant_sequence_exact₃ _ hT x rfl
    ((supportedModuleHPresheafδ_app_apply S hT n W x).symm.trans hx)

/-- The coefficient sequence is exact immediately after its connecting map. -/
theorem exact_supportedModuleHPresheafδ_map_f (hT : T.ShortExact) (n : ℕ) :
    (ShortComplex.mk (supportedModuleHPresheafδ S hT n)
      ((supportedModuleHPresheafFunctor S (n + 1)).map T.f)
      (supportedModuleHPresheafδ_map_f S hT n)).Exact := by
  rw [ShortComplex.exact_iff_evaluation]
  intro W
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ _ hT x hx rfl
  exact ⟨y, (supportedModuleHPresheafδ_app_apply S hT n W y).trans hy⟩

/-- A flasque middle term makes the positive-degree connecting morphism an
isomorphism of supported cohomology presheaves. -/
instance isIso_supportedModuleHPresheafδ_succ (hT : T.ShortExact)
    [TopCat.Presheaf.IsFlasque T.X₂.obj] (n : ℕ) :
    IsIso (supportedModuleHPresheafδ S hT (n + 1)) :=
  isIso_supportedModuleHPresheafPostcomp_extClass S hT rfl

/-- A flasque first term makes the positive-degree map `H_Sⁿ⁺¹(-, F₂) ⟶ H_Sⁿ⁺¹(-, F₃)` induced
by `F₂ ⟶ F₃` an isomorphism of supported cohomology presheaves. -/
theorem isIso_supportedModuleHPresheafFunctor_map_g (hT : T.ShortExact)
    [TopCat.Presheaf.IsFlasque T.X₁.obj] (n : ℕ) :
    IsIso ((supportedModuleHPresheafFunctor S (n + 1)).map T.g) :=
  isIso_supportedModuleHPresheafFunctor_map S (n + 1) T.g fun _ ↦
    ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ by
      obtain ⟨z, rfl⟩ := Ext.covariant_sequence_exact₂ _ hT x hx
      rw [Subsingleton.elim z 0, Ext.zero_comp],
    fun x ↦ Ext.covariant_sequence_exact₃ _ hT x rfl (Subsingleton.elim _ _)⟩

/-- The degree-zero connecting morphism `Γ_S(-, F₃) ⟶ H_S¹(-, F₁)` of a short exact sequence
`0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0`, read through the identification of degree-zero supported cohomology
with supported sections. -/
def supportedModuleHPresheafδZero (hT : T.ShortExact) :
    (T.X₃.supportedSubmoduleSheaf S).obj ⟶ T.X₁.supportedModuleHPresheaf S 1 :=
  (T.X₃.supportedModuleHPresheafZeroIso S).inv ≫ supportedModuleHPresheafδ S hT 0

/-- The degree-zero connecting morphism sends a supported section to the Yoneda product of its
degree-zero class with the extension class. -/
lemma supportedModuleHPresheafδZero_app_apply (hT : T.ShortExact) (W : (Opens X)ᵒᵖ)
    (s : T.X₃.supportedSubmodule S W.unop) :
    (supportedModuleHPresheafδZero S hT).app W s =
      ((T.X₃.supportedModuleHZeroEquiv S W.unop).symm s).comp hT.extClass (zero_add 1) :=
  (supportedModuleHPresheafδ_app_apply S hT 0 W _).trans <|
    congrArg (Ext.comp · hT.extClass _)
      (supportedModuleHPresheafZeroIso_inv_app_apply S T.X₃ W s)

/-- Under `CategoryTheory.Sheaf.supportedModuleHZeroEquiv`, the image of a supported section of
`F₂` in `F₃` corresponds to the image of its class. -/
private lemma supportedModuleHZeroEquiv_symm_map_g (W : (Opens X)ᵒᵖ)
    (s : T.X₂.supportedSubmodule S W.unop) :
    (T.X₃.supportedModuleHZeroEquiv S W.unop).symm
        (((supportedSubmoduleFunctor S).map T.g).hom.app W s) =
      ((T.X₂.supportedModuleHZeroEquiv S W.unop).symm s).comp (Ext.mk₀ T.g) (add_zero 0) := by
  refine (LinearEquiv.symm_apply_eq _).2 (Subtype.ext ?_)
  rw [coe_supportedModuleHZeroEquiv_naturality_right, LinearEquiv.apply_symm_apply]
  exact coe_supportedSubmoduleFunctor_map_hom_app_apply S T.g W s

/-- The degree-zero connecting morphism vanishes on the supported sections coming from `F₂`. -/
@[reassoc (attr := simp)]
lemma supportedSubmoduleFunctor_map_g_hom_supportedModuleHPresheafδZero (hT : T.ShortExact) :
    ((supportedSubmoduleFunctor S).map T.g).hom ≫ supportedModuleHPresheafδZero S hT = 0 := by
  ext W s
  refine (supportedModuleHPresheafδZero_app_apply S hT W _).trans <|
    (congrArg (fun z ↦ z.comp hT.extClass (zero_add 1))
      (supportedModuleHZeroEquiv_symm_map_g S W s)).trans ?_
  rw [Ext.comp_assoc_of_second_deg_zero, hT.comp_extClass, Ext.comp_zero]
  rfl

/-- The sequence `Γ_S(W, F₂) ⟶ Γ_S(W, F₃) ⟶ H_S¹(W, F₁)` of a short exact sequence
`0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` is exact. -/
theorem exact_supportedModuleHPresheafδZero_app (hT : T.ShortExact) (W : (Opens X)ᵒᵖ) :
    (ShortComplex.mk (((supportedSubmoduleFunctor S).map T.g).hom.app W)
      ((supportedModuleHPresheafδZero S hT).app W) (by
        rw [← NatTrans.comp_app, supportedSubmoduleFunctor_map_g_hom_supportedModuleHPresheafδZero,
          NatTrans.app_zero])).Exact := by
  refine (ShortComplex.moduleCat_exact_iff _).2 fun s hs ↦ ?_
  obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₃ _ hT _ (zero_add 1)
    ((supportedModuleHPresheafδZero_app_apply S hT W s).symm.trans hs)
  refine ⟨T.X₂.supportedModuleHZeroEquiv S W.unop z, ?_⟩
  apply (T.X₃.supportedModuleHZeroEquiv S W.unop).symm.injective
  refine (supportedModuleHZeroEquiv_symm_map_g S W _).trans ?_
  rw [LinearEquiv.symm_apply_apply]
  exact hz

/-- A flasque middle term makes the degree-zero connecting morphism
`Γ_S(W, F₃) ⟶ H_S¹(W, F₁)` surjective. -/
instance epi_supportedModuleHPresheafδZero_app (hT : T.ShortExact)
    [TopCat.Presheaf.IsFlasque T.X₂.obj] (W : (Opens X)ᵒᵖ) :
    Epi ((supportedModuleHPresheafδZero S hT).app W) := by
  refine (ModuleCat.epi_iff_surjective _).2 fun c ↦ ?_
  obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₁ _ hT c
    ((subsingleton_supportedModuleH_succ_of_isFlasque T.X₂ S W.unop 0).elim _ _) (zero_add 1)
  refine ⟨T.X₃.supportedModuleHZeroEquiv S W.unop y, ?_⟩
  exact (supportedModuleHPresheafδZero_app_apply S hT W _).trans
    (by rw [LinearEquiv.symm_apply_apply])

/-- A flasque middle term makes the connecting morphism
`H_Sⁿ(-, F₃) ⟶ H_Sⁿ⁺¹(-, F₁)` an epimorphism of presheaves in every degree `n`. -/
instance epi_supportedModuleHPresheafδ (hT : T.ShortExact)
    [TopCat.Presheaf.IsFlasque T.X₂.obj] (n : ℕ) :
    Epi (supportedModuleHPresheafδ S hT n) := by
  rcases n with _ | n
  · have : Epi ((T.X₃.supportedModuleHPresheafZeroIso S).hom ≫
        supportedModuleHPresheafδZero S hT) := by
      have : Epi (supportedModuleHPresheafδZero S hT) := NatTrans.epi_of_epi_app _
      exact epi_comp _ _
    rwa [supportedModuleHPresheafδZero, Iso.hom_inv_id_assoc] at this
  · infer_instance

end

end CategoryTheory.Sheaf
