/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.FinitePresentation

/-!
# Finite projective presentations

A finite projective presentation of a module is a right exact diagram
`P₁ → P₀ → M → 0` with both `P₀` and `P₁` finitely generated projective.
Every finitely presented module admits such a diagram, even over a non-Noetherian ring.
Keeping the diagram explicit allows constructions such as the Auslander–Bridger transpose
to compare different choices of presentation.

## References

* M. Auslander, M. Bridger, *Stable module theory*, Section 2.1.
-/

public section

namespace TauCeti

universe u v

variable {A : Type u} [Ring A]

/-- A right exact presentation by two finitely generated projective modules. -/
structure FiniteProjectivePresentation (M : ModuleCat.{v} A) where
  /-- The module of generators. -/
  P₀ : ModuleCat.{v} A
  /-- The module of relations. -/
  P₁ : ModuleCat.{v} A
  /-- The generators form a finite module. -/
  [finite₀ : Module.Finite A P₀]
  /-- The relations form a finite module. -/
  [finite₁ : Module.Finite A P₁]
  /-- The generators form a projective module. -/
  [projective₀ : Module.Projective A P₀]
  /-- The relations form a projective module. -/
  [projective₁ : Module.Projective A P₁]
  /-- The presenting map. -/
  p : P₁ →ₗ[A] P₀
  /-- The augmentation to the presented module. -/
  π : P₀ →ₗ[A] M
  /-- The relations are exactly the kernel of the augmentation. -/
  exact : Function.Exact p π
  /-- The generators cover the module. -/
  surjective : Function.Surjective π

namespace FiniteProjectivePresentation

attribute [instance] finite₀ finite₁ projective₀ projective₁

/-- Every finitely presented module has a finite projective presentation.
The ring need only be small in the universe of the module. -/
noncomputable def ofFinitePresentation {M : ModuleCat.{v} A}
    [Module.FinitePresentation A M] [Small.{v} A] : FiniteProjectivePresentation M := by
  classical
  apply Classical.choice
  obtain ⟨n, m, f, g, hf, hg⟩ := Module.FinitePresentation.exists_fin' A M
  let e₀ := Shrink.linearEquiv A (Fin n → A)
  let e₁ := Shrink.linearEquiv A (Fin m → A)
  have : Module.Free A (Shrink.{v} (Fin n → A)) := .of_equiv e₀.symm
  have : Module.Free A (Shrink.{v} (Fin m → A)) := .of_equiv e₁.symm
  have : Module.Finite A (Shrink.{v} (Fin n → A)) := .equiv e₀.symm
  have : Module.Finite A (Shrink.{v} (Fin m → A)) := .equiv e₁.symm
  refine ⟨⟨ModuleCat.of A (Shrink.{v} (Fin n → A)),
    ModuleCat.of A (Shrink.{v} (Fin m → A)),
    e₀.symm.toLinearMap ∘ₗ g ∘ₗ e₁.toLinearMap, f ∘ₗ e₀.toLinearMap, ?_,
    hf.comp e₀.surjective⟩⟩
  simpa only [LinearMap.comp_assoc] using
    (LinearEquiv.conj_symm_exact_iff_exact (g ∘ₗ e₁.toLinearMap) f e₀).mpr
      (LinearEquiv.precomp_exact_iff_exact.mpr hg)

end FiniteProjectivePresentation

end TauCeti
