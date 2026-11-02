/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import TauCeti.AlgebraicGeometry.Scheme.Normal

/-!
# Finite morphisms into normal integral schemes

Let `f : X ⟶ Y` be a finite morphism of integral schemes with `Y` normal, and let `V` be an
affine open of `Y`. If `f` is an isomorphism on sections over some nonempty open `W ⊆ V`, then
`f` is bijective on sections over `V`
(`AlgebraicGeometry.Scheme.Hom.bijective_app_of_isFinite_of_isIso_app`). Indeed, restricting to
`f ⁻¹ W ≅ W` and taking germs at the generic point embeds `Γ(X, f ⁻¹ V)` into the function field
of `Y`, the fraction field of `Γ(Y, V)`, as an integral extension of the integrally closed domain
`Γ(Y, V)`, and such an extension is trivial.

This is the affine step in the proof that a finite modification of a normal integral scheme is an
isomorphism (Stacks, Lemma 29.54.8 (0AB1)).

## References

* [Stacks Project, Lemma 29.54.8](https://stacks.math.columbia.edu/tag/0AB1).
-/

public section

open CategoryTheory TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

/-- If `f` is finite between integral schemes with `Y` normal, and `f` is an isomorphism on
sections over a nonempty open `W` of an affine open `V`, then `f` is bijective on sections over
`V`. -/
theorem Scheme.Hom.bijective_app_of_isFinite_of_isIso_app [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme Y] (f : X ⟶ Y) [IsFinite f] {V W : Y.Opens} (hV : IsAffineOpen V)
    (hWV : W ≤ V) [Nonempty W] [IsIso (f.app W)] :
    Function.Bijective (f.app V) := by
  have : Nonempty V := ⟨⟨_, hWV (Classical.choice ‹Nonempty W›).2⟩⟩
  -- An empty preimage would make `f.app W` identify the nonzero ring `Γ(Y, W)` with zero.
  have : Nonempty (f ⁻¹ᵁ W) := by
    by_contra h
    have : Subsingleton Γ(X, f ⁻¹ᵁ W) := CommRingCat.subsingleton_of_isTerminal
      (X.sheaf.isTerminalOfEqEmpty (SetLike.ext' (Set.not_nonempty_iff_eq_empty'.mp h)))
    exact not_subsingleton Γ(Y, W) (ConcreteCategory.bijective_of_isIso (f.app W)).1.subsingleton
  have : Nonempty (f ⁻¹ᵁ V) :=
    ⟨⟨_, f.preimage_mono hWV (Classical.choice ‹Nonempty (f ⁻¹ᵁ W)›).2⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen Y V hV
  have := IsNormalScheme.isIntegrallyClosed_of_isAffineOpen hV
  let σ := X.presheaf.map (homOfLE (f.preimage_mono hWV)).op ≫ inv (f.app W) ≫
    Y.germToFunctionField W
  have hσ : Function.Injective σ :=
    (Y.germToFunctionField_injective _).comp
      ((ConcreteCategory.bijective_of_isIso (inv (f.app W))).1.comp
        (map_injective_of_isIntegral X _))
  -- `σ` extends the inclusion of `Γ(Y, V)` into its fraction field `k(Y)`.
  have hσφ (a : Γ(Y, V)) : σ (f.app V a) = algebraMap Γ(Y, V) Y.functionField a := by
    have hnat : f.app V ≫ X.presheaf.map (homOfLE (f.preimage_mono hWV)).op =
        Y.presheaf.map (homOfLE hWV).op ≫ f.app W :=
      (f.naturality _).symm
    have : f.app V ≫ σ = Y.germToFunctionField V := by
      rw [reassoc_of% hnat, IsIso.hom_inv_id_assoc]
      exact TopCat.Presheaf.germ_res _ _ _ _
    exact congr($this a)
  refine ⟨fun a b hab ↦ IsFractionRing.injective Γ(Y, V) Y.functionField ?_, fun b ↦ ?_⟩
  · rw [← hσφ, ← hσφ, hab]
  · -- `σ b` is integral over the integrally closed domain `Γ(Y, V)`, so it comes from `Γ(Y, V)`.
    obtain ⟨p, hp, hpb⟩ := (f.finite_app V hV).to_isIntegral b
    have : _root_.IsIntegral Γ(Y, V) (σ b) := by
      refine ⟨p, hp, ?_⟩
      rw [← RingHom.ext (f := σ.hom.comp (f.app V).hom) hσφ, ← Polynomial.hom_eval₂, hpb,
        map_zero]
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp this
    exact ⟨a, hσ (by rw [hσφ, ha])⟩

end AlgebraicGeometry
