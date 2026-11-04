/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sheaves.Flasque.Module
import TauCeti.Algebra.Homology.ShortComplex.FunctorCategory
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The coefficient sequence for module-valued supported cohomology

For a short exact sequence of sheaves of modules, the Yoneda product with its
extension class defines connecting maps on the supported cohomology presheaves.
These maps commute with open restriction and with morphisms of short exact
sequences, and give an exact coefficient sequence. A flasque middle term makes
its positive-degree connecting maps dimension-shift isomorphisms.

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

/-- The connecting morphism of supported cohomology presheaves for a short exact
sequence of coefficient sheaves, given by its Yoneda extension class. -/
def supportedModuleHPresheafδ (hT : T.ShortExact) (n : ℕ) :
    T.X₃.supportedModuleHPresheaf S n ⟶ T.X₁.supportedModuleHPresheaf S (n + 1) where
  app W := ModuleCat.ofHom (Ext.postcompOfLinear hT.extClass R
    ((S.supportedFreeModuleSheafFunctor R).obj W.unop) rfl)
  naturality W W' f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    -- Normalize the source before introducing a class, so rewriting sees Ext
    -- rather than the opaque presheaf object's carrier.
    change ∀ x : T.X₃.supportedModuleH S W.unop n,
      ((Ext.mk₀ ((S.supportedFreeModuleSheafFunctor R).map f.unop)).comp x
          (zero_add n)).comp hT.extClass rfl =
        (Ext.mk₀ ((S.supportedFreeModuleSheafFunctor R).map f.unop)).comp
          (x.comp hT.extClass rfl) (zero_add (n + 1))
    intro x
    exact Ext.comp_assoc _ x hT.extClass (zero_add n) rfl (by omega)

@[simp]
lemma supportedModuleHPresheafδ_app_apply (hT : T.ShortExact) (n : ℕ)
    (W : (Opens X)ᵒᵖ) (x : T.X₃.supportedModuleH S W.unop n) :
    (supportedModuleHPresheafδ S hT n).app W x = x.comp hT.extClass rfl :=
  (rfl)

/-- The connecting morphism is natural in short exact sequences of coefficients. -/
@[reassoc]
lemma supportedModuleHPresheafδ_naturality (hT : T.ShortExact) (hT' : T'.ShortExact)
    (f : T ⟶ T') (n : ℕ) :
    (supportedModuleHPresheafFunctor S n).map f.τ₃ ≫ supportedModuleHPresheafδ S hT' n =
      supportedModuleHPresheafδ S hT n ≫
        (supportedModuleHPresheafFunctor S (n + 1)).map f.τ₁ := by
  apply NatTrans.ext
  funext W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  -- Normalize the domain before introducing its Ext class, as in the definition.
  change ∀ x : T.X₃.supportedModuleH S W.unop n,
    (x.comp (Ext.mk₀ f.τ₃) (add_zero n)).comp hT'.extClass rfl =
      (x.comp hT.extClass rfl).comp (Ext.mk₀ f.τ₁) (add_zero (n + 1))
  intro x
  exact (Ext.comp_assoc_of_second_deg_zero x _ _ rfl).trans
    ((congrArg (fun a : Ext.{u} T.X₃ T'.X₁ 1 ↦ x.comp a rfl)
      (hT.extClass_naturality hT' f).symm).trans
        (Ext.comp_assoc_of_third_deg_zero x _ _ rfl).symm)

@[simp, reassoc]
lemma supportedModuleHPresheafFunctor_map_g_δ (hT : T.ShortExact) (n : ℕ) :
    (supportedModuleHPresheafFunctor S n).map T.g ≫ supportedModuleHPresheafδ S hT n = 0 := by
  apply NatTrans.ext
  funext W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  -- Expose the Ext domain before introducing a section of the composite functor.
  change ∀ x : T.X₂.supportedModuleH S W.unop n,
    (x.comp (Ext.mk₀ T.g) (add_zero n)).comp hT.extClass rfl = 0
  intro x
  exact (Ext.comp_assoc_of_second_deg_zero x _ _ rfl).trans
    ((congrArg (fun a : Ext.{u} T.X₂ T.X₁ 1 ↦ x.comp a rfl) hT.comp_extClass).trans
      (Ext.comp_zero x _ _ _ rfl))

@[simp, reassoc]
lemma supportedModuleHPresheafδ_map_f (hT : T.ShortExact) (n : ℕ) :
    supportedModuleHPresheafδ S hT n ≫
      (supportedModuleHPresheafFunctor S (n + 1)).map T.f = 0 := by
  apply NatTrans.ext
  funext W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  -- Expose the Ext domain before introducing a section of the composite functor.
  change ∀ x : T.X₃.supportedModuleH S W.unop n,
    (x.comp hT.extClass rfl).comp (Ext.mk₀ T.f) (add_zero (n + 1)) = 0
  intro x
  exact (Ext.comp_assoc_of_third_deg_zero x _ _ rfl).trans
    ((congrArg (fun a : Ext.{u} T.X₃ T.X₂ 1 ↦ x.comp a rfl) hT.extClass_comp).trans
      (Ext.comp_zero x _ _ _ rfl))

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
  exact fun x hx ↦ Ext.covariant_sequence_exact₃ _ hT x rfl hx

/-- The coefficient sequence is exact immediately after its connecting map. -/
theorem exact_supportedModuleHPresheafδ_map_f (hT : T.ShortExact) (n : ℕ) :
    (ShortComplex.mk (supportedModuleHPresheafδ S hT n)
      ((supportedModuleHPresheafFunctor S (n + 1)).map T.f)
      (supportedModuleHPresheafδ_map_f S hT n)).Exact := by
  rw [ShortComplex.exact_iff_evaluation]
  intro W
  rw [ShortComplex.moduleCat_exact_iff]
  exact fun x hx ↦ Ext.covariant_sequence_exact₁ _ hT x hx rfl

/-- A flasque middle term makes the positive-degree connecting morphism an
isomorphism of supported cohomology presheaves. -/
instance isIso_supportedModuleHPresheafδ_succ (hT : T.ShortExact)
    [TopCat.Presheaf.IsFlasque T.X₂.obj] (n : ℕ) :
    IsIso (supportedModuleHPresheafδ S hT (n + 1)) := by
  have (W : (Opens X)ᵒᵖ) : IsIso ((supportedModuleHPresheafδ S hT (n + 1)).app W) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    -- The component is the Yoneda postcomposition map, with an explicit Ext domain.
    change Function.Bijective (Ext.postcomp hT.extClass
      ((S.supportedFreeModuleSheafFunctor R).obj W.unop) (rfl : n + 1 + 1 = n + 2))
    refine ⟨(injective_iff_map_eq_zero _).2 (fun x hx ↦ ?_), fun x ↦ ?_⟩
    · obtain ⟨z, rfl⟩ := Ext.covariant_sequence_exact₃ _ hT x rfl hx
      rw [Subsingleton.elim z 0, Ext.zero_comp]
    · exact Ext.covariant_sequence_exact₁ _ hT x (Subsingleton.elim _ _) rfl
  exact NatIso.isIso_of_isIso_app _

end

end CategoryTheory.Sheaf
