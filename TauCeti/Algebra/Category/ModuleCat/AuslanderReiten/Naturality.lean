/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.Basic
public import TauCeti.Algebra.Module.AuslanderReiten.PairingNaturality

/-!
# Auslander–Reiten duality is natural in the presented module

A square between finite projective presentations induces a map on their
Auslander–Reiten translates. Postcomposition by its injective stable class is
dual to pullback of `Ext¹` along the induced cokernel map. Together with the
coefficient naturality of `LinearMap.auslanderReitenExtEquiv`, this supplies
both variables of Auslander–Reiten duality.

The statements allow nonminimal presentations, presenting arrows with nonzero
kernel, and arbitrary algebras and coefficient modules over a field.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section IV.2.
-/

public section

namespace LinearMap

open TauCeti CategoryTheory
open scoped ModuleCat.Algebra

universe u v w

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A]
  {P₀ P₁ Q₀ Q₁ : Type max u v w}
  [AddCommGroup P₀] [Module A P₀] [Module.Finite A P₀] [Module.Projective A P₀]
  [AddCommGroup P₁] [Module A P₁] [Module.Finite A P₁] [Module.Projective A P₁]
  [AddCommGroup Q₀] [Module A Q₀] [Module.Finite A Q₀] [Module.Projective A Q₀]
  [AddCommGroup Q₁] [Module A Q₁] [Module.Finite A Q₁] [Module.Projective A Q₁]
  {p : P₁ →ₗ[A] P₀} {q : Q₁ →ₗ[A] Q₀}

/-- Postcomposition by a translated presentation square in injective stable Hom
is dual to precomposition on Hom cocycle classes. -/
theorem auslanderReitenStableHomEquiv_presentation_naturality
    (f₀ : P₀ →ₗ[A] Q₀) (f₁ : P₁ →ₗ[A] Q₁) (hf : f₀.comp p = q.comp f₁)
    (N : ModuleCat.{max u v w} A)
    (h : (ExactStructure.abelian (ModuleCat.{max u v w} A)).injectiveStableFunctor.obj N ⟶
      (ExactStructure.abelian (ModuleCat.{max u v w} A)).injectiveStableFunctor.obj
        (ModuleCat.of A (AuslanderReitenTranslate k p))) :
    auslanderReitenStableHomEquiv q N
        (h ≫ (ExactStructure.abelian (ModuleCat.{max u v w} A)).injectiveStableFunctor.map
          (ModuleCat.ofHom (auslanderReitenTranslateMap f₀ f₁ hf))) =
      (homCocycleQuotientPrecomp f₀ f₁ hf).dualMap (auslanderReitenStableHomEquiv p N h) := by
  obtain ⟨h, rfl⟩ :=
    (ExactStructure.abelian (ModuleCat.{max u v w} A)).injectiveStableFunctor.map_surjective h
  rw [← Functor.map_comp, auslanderReitenStableHomEquiv_map,
    auslanderReitenStableHomEquiv_map]
  exact auslanderReitenCocyclePairing_presentation_naturality f₀ f₁ hf h.hom

/-- Postcomposition by the translate of a presentation square is dual to pullback
of extensions along the induced cokernel map. -/
theorem auslanderReitenExtEquiv_presentation_naturality
    (f₀ : P₀ →ₗ[A] Q₀) (f₁ : P₁ →ₗ[A] Q₁) (hf : f₀.comp p = q.comp f₁)
    (g : (P₀ ⧸ range p) →ₗ[A] (Q₀ ⧸ range q))
    (hg : g.comp (range p).mkQ = (range q).mkQ.comp f₀)
    (N : ModuleCat.{max u v w} A)
    (h : (ExactStructure.abelian (ModuleCat.{max u v w} A)).injectiveStableFunctor.obj N ⟶
      (ExactStructure.abelian (ModuleCat.{max u v w} A)).injectiveStableFunctor.obj
        (ModuleCat.of A (AuslanderReitenTranslate k p)))
    (α : Abelian.Ext (ModuleCat.of A (Q₀ ⧸ range q)) N 1) :
    auslanderReitenExtEquiv q N
        (h ≫ (ExactStructure.abelian (ModuleCat.{max u v w} A)).injectiveStableFunctor.map
          (ModuleCat.ofHom (auslanderReitenTranslateMap f₀ f₁ hf))) α =
      auslanderReitenExtEquiv p N h
        ((Abelian.Ext.mk₀ (ModuleCat.ofHom g)).comp α (zero_add 1)) := by
  obtain ⟨x, rfl⟩ := (homCocycleQuotientEquivExt (k := k) q N).surjective α
  rw [← homCocycleQuotientEquivExt_precomp f₀ f₁ hf g hg,
    auslanderReitenExtEquiv_apply, auslanderReitenExtEquiv_apply,
    auslanderReitenStableHomEquiv_presentation_naturality]
  rfl

end LinearMap
