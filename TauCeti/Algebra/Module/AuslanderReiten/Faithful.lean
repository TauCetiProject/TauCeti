/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.Functor
public import TauCeti.Algebra.Module.AuslanderReiten.DoubleTranspose.Naturality

/-!
# Faithfulness of the stable transpose

The Auslander–Bridger transpose detects maps factoring through projective modules:
a map between finitely presented modules vanishes in the projective stable category
if and only if its transpose does. Consequently the stable transpose functor is faithful.

The detection statement uses arbitrary finite projective presentations. It follows from
recovering the original map after two transpositions. More precisely, if a transposed map
factors through a projective, the original map factors through the degree-zero projective
of the target presentation. No commutativity, Noetherian, or minimality assumption is needed.

## References

* M. Auslander, M. Bridger, *Stable module theory*, Mem. Amer. Math. Soc. 94 (1969), Section 2.1.
-/

public section

namespace TauCeti

open CategoryTheory LinearMap

universe u v

namespace AuslanderReitenTranspose

variable {A : Type u} [Ring A]

section Factorization

variable {M : Type*} {N : Type*} {P₀ : Type*} {P₁ : Type*} {Q₀ : Type*} {Q₁ : Type*}
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  [AddCommGroup P₀] [Module A P₀] [AddCommGroup P₁] [Module A P₁]
  [AddCommGroup Q₀] [Module A Q₀] [AddCommGroup Q₁] [Module A Q₁]
  [Module.Finite A P₀] [Module.Projective A P₀]
  [Module.Finite A P₁] [Module.Projective A P₁]
  [Module.Finite A Q₀] [Module.Projective A Q₀]
  [Module.Finite A Q₁] [Module.Projective A Q₁]
  {p : P₁ →ₗ[A] P₀} {q : Q₁ →ₗ[A] Q₀} {π : P₀ →ₗ[A] M} {ρ : Q₀ →ₗ[A] N}

/-- If the transpose of a presentation lift factors through a projective right module,
the original module map factors through the target presentation's degree-zero projective. -/
theorem exists_comp_eq_of_map_factor
    (hp : Function.Exact p π) (hπ : Function.Surjective π)
    (hq : Function.Exact q ρ) (hρ : Function.Surjective ρ)
    (f : M →ₗ[A] N) (f₀ : P₀ →ₗ[A] Q₀) (f₁ : P₁ →ₗ[A] Q₁)
    (hf₀ : ρ ∘ₗ f₀ = f ∘ₗ π) (hf₁ : f₀ ∘ₗ p = q ∘ₗ f₁)
    {C : Type*} [AddCommGroup C] [Module Aᵐᵒᵖ C] [Module.Projective Aᵐᵒᵖ C]
    (i : AuslanderReitenTranspose q →ₗ[Aᵐᵒᵖ] C)
    (j : C →ₗ[Aᵐᵒᵖ] AuslanderReitenTranspose p)
    (hfactor : map f₀ f₁ hf₁ = j ∘ₗ i) :
    ∃ a : M →ₗ[A] Q₀, ρ ∘ₗ a = f := by
  have hexp : Function.Exact (p.lcomp Aᵐᵒᵖ A) (mk p) := by
    rw [LinearMap.exact_iff, ker_mk]
  have hsquare : f₁.lcomp Aᵐᵒᵖ A ∘ₗ q.lcomp Aᵐᵒᵖ A =
      p.lcomp Aᵐᵒᵖ A ∘ₗ f₀.lcomp Aᵐᵒᵖ A := by
    ext φ x
    exact congrArg φ (LinearMap.congr_fun hf₁ x).symm
  -- Apply the existing vanishing-on-projectives theorem to the dual presentation square.
  have hzero : mk q ∘ₗ q.lcomp Aᵐᵒᵖ A = 0 := by
    ext φ
    simp
  obtain ⟨h, hh⟩ := exists_map_eq_mk_comp_of_factor
    (p := q.lcomp Aᵐᵒᵖ A) (q := p.lcomp Aᵐᵒᵖ A) (π := mk q) (ρ := mk p)
    hzero hexp (mk_surjective p) i j (f₁.lcomp Aᵐᵒᵖ A) (f₀.lcomp Aᵐᵒᵖ A) hsquare
    (by rw [← map_comp_mk f₀ f₁ hf₁, hfactor, comp_assoc])
  let ep := doubleTransposePresentationEquiv A p π hp hπ
  -- Inverse evaluation identifies the intervening double dual with Q₀.
  let a : M →ₗ[A] Q₀ :=
    (opDualEvalEquiv A Q₀).symm.toLinearMap ∘ₛₗ
      (opDualCodomainEquiv A (Module.Dual A Q₀)).symm.toLinearMap ∘ₛₗ
        h ∘ₛₗ ep.symm.toLinearMap
  refine ⟨a, ?_⟩
  ext x
  have hn := doubleTransposePresentationEquiv_naturality A hp hπ hq hρ f f₀ f₁
    hf₀ hf₁ (ep.symm x)
  have he := LinearMap.congr_fun hh (ep.symm x)
  rw [he, LinearMap.comp_apply] at hn
  simpa only [a, LinearMap.comp_apply, doubleTransposePresentationEquiv_mk,
    ep, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using hn

end Factorization

variable {M N P₀ P₁ Q₀ Q₁ : Type v}
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  [AddCommGroup P₀] [Module A P₀] [AddCommGroup P₁] [Module A P₁]
  [AddCommGroup Q₀] [Module A Q₀] [AddCommGroup Q₁] [Module A Q₁]
  [Module.Finite A P₀] [Module.Projective A P₀]
  [Module.Finite A P₁] [Module.Projective A P₁]
  [Module.Finite A Q₀] [Module.Projective A Q₀]
  [Module.Finite A Q₁] [Module.Projective A Q₁]
  {p : P₁ →ₗ[A] P₀} {q : Q₁ →ₗ[A] Q₀} {π : P₀ →ₗ[A] M} {ρ : Q₀ →ₗ[A] N}

variable [Small.{v} A]

local notation "S" => ExactStructure.projectiveStableFunctor (ExactStructure.abelian (ModuleCat A))

/-- Stable transposition reflects zero morphisms between finite projective presentations. -/
@[simp]
theorem stableMap_eq_zero_iff
    (hp : Function.Exact p π) (hπ : Function.Surjective π)
    (hq : Function.Exact q ρ) (hρ : Function.Surjective ρ)
    (f : (S).obj (ModuleCat.of A M) ⟶ (S).obj (ModuleCat.of A N)) :
    stableMap hp.linearMap_comp_eq_zero hq hρ f = 0 ↔ f = 0 := by
  constructor
  · obtain ⟨f, rfl⟩ := (S).map_surjective f
    obtain ⟨f₀, f₁, hf₀, hf₁⟩ :=
      exists_lift_projective_presentation hp.linearMap_comp_eq_zero hq hρ f.hom
    rw [← ModuleCat.ofHom_hom f,
      stableMap_quotient_map hp.linearMap_comp_eq_zero hq hρ f.hom f₀ f₁ hf₀ hf₁,
      ExactStructure.projectiveStableFunctor_map_eq_zero_iff]
    intro hf
    obtain ⟨C, hC, i, j, hij⟩ := (ObjectProperty.factorsThrough_iff _ _).mp hf
    have : Projective C := (ExactStructure.abelian_isProjective_iff C).mp hC
    have : Module.Projective Aᵐᵒᵖ C := inferInstance
    obtain ⟨a, ha⟩ := exists_comp_eq_of_map_factor hp hπ hq hρ f.hom f₀ f₁ hf₀ hf₁
      i.hom j.hom (by
        simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom] using
          congrArg (fun h ↦ h.hom) hij)
    rw [ExactStructure.projectiveStableFunctor_map_eq_zero_iff]
    have hQ := (ExactStructure.abelian_isProjective_iff (ModuleCat.of A Q₀)).mpr
      inferInstance
    have heq : f = ModuleCat.ofHom a ≫ ModuleCat.ofHom ρ := ModuleCat.hom_ext ha.symm
    rw [heq]
    exact ObjectProperty.factorsThrough_comp _ hQ (ModuleCat.ofHom a) (ModuleCat.ofHom ρ)
  · rintro rfl
    exact (stableMap hp.linearMap_comp_eq_zero hq hρ).map_zero

/-- Stable transposition is injective on stable Hom groups. -/
theorem stableMap_injective
    (hp : Function.Exact p π) (hπ : Function.Surjective π)
    (hq : Function.Exact q ρ) (hρ : Function.Surjective ρ) :
    Function.Injective (stableMap hp.linearMap_comp_eq_zero hq hρ) :=
  (injective_iff_map_eq_zero' _).mpr (stableMap_eq_zero_iff hp hπ hq hρ)

end AuslanderReitenTranspose

variable {A : Type u} [Ring A]

/-- The transpose attached to any family of finite projective presentations is faithful. -/
instance stableTransposeFunctor_faithful
    (P : ∀ M : FinitelyPresentedStableModule.{u, max u v} A,
      FiniteProjectivePresentation M.obj.as) :
    (stableTransposeFunctor P).Faithful where
  map_injective {M N} f g hfg := by
    apply ObjectProperty.hom_ext
    apply AuslanderReitenTranspose.stableMap_injective (P M).exact (P M).surjective
      (P N).exact (P N).surjective
    simp only [stableTransposeFunctor_map, ← Category.assoc, cancel_mono, cancel_epi] at hfg
    exact congrArg (fun h ↦ h.unop.hom) hfg

/-- The Auslander–Bridger stable transpose on finitely presented modules is faithful. -/
instance stableTranspose_faithful : (stableTranspose.{u, v} A).Faithful := by
  rw [stableTranspose_def]
  infer_instance

end TauCeti
