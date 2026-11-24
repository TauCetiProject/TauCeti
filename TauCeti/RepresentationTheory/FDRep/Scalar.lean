/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.FDRep

/-!
# Comparing intertwiners when endomorphisms are scalar

Two invertible operators intertwining the same representations differ by a unit scalar
if the source has only scalar equivariant endomorphisms. The scalar-endomorphism hypothesis
is explicit, so the result applies over nonsplitting fields as well as algebraically closed
ones. It is used to construct scalar factor sets for projective extensions.

The result is stated for a plain `Representation`, with no finiteness assumption
(`Representation.exists_unit_smul_of_intertwines`), and for `FDRep`
(`FDRep.exists_unit_smul_of_intertwines`), where it follows from the first.

For a simple object over an algebraically closed field, Mathlib's
`CategoryTheory.endomorphism_simple_eq_smul_id` supplies the hypothesis.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Chapter 11.
-/

public section

namespace Representation

variable {k G V W : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] {ρ : Representation k G V} {σ : Representation k G W}

/-- If the equivariant endomorphisms of a nonzero representation `ρ` are scalar, two invertible
intertwiners from `ρ` to the same target `σ` differ by a unit scalar. Neither an algebraic closure
nor finite dimensionality is needed. -/
theorem exists_unit_smul_of_intertwines [Nontrivial V]
    (hscalar : ∀ f : Module.End k V, (∀ g, Commute f (ρ g)) →
      ∃ c : k, f = algebraMap k (Module.End k V) c)
    (a b : V ≃ₗ[k] W) (ha : ∀ g x, a (ρ g x) = σ g (a x))
    (hb : ∀ g x, b (ρ g x) = σ g (b x)) :
    ∃ c : kˣ, ∀ x, a x = (c : k) • b x := by
  obtain ⟨c, hc⟩ := hscalar ((b.symm : W →ₗ[k] V) ∘ₗ (a : V →ₗ[k] W)) fun g ↦ by
    refine (commute_iff_eq _ _).2 (LinearMap.ext fun x ↦ ?_)
    simp only [mul_apply_eq_comp, LinearMap.comp_apply, LinearEquiv.coe_coe, ha]
    rw [LinearEquiv.symm_apply_eq, hb, LinearEquiv.apply_symm_apply]
  have hx (x : V) : a x = c • b x := by
    have := LinearMap.congr_fun hc x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.algebraMap_end_apply] at this
    rw [← map_smul, ← this, LinearEquiv.apply_symm_apply]
  have hc₀ : c ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx₀⟩ := exists_ne (0 : V)
    exact hx₀ (a.injective (by simp [hx]))
  exact ⟨Units.mk0 c hc₀, hx⟩

end Representation

namespace FDRep

open CategoryTheory

universe u v w

variable {k : Type u} {G : Type v} [Field k] [Monoid G]

/-- If the equivariant endomorphisms of a nonzero representation are scalar, two invertible
intertwiners to the same target differ by a unit scalar. No algebraic closure is needed. This is
`Representation.exists_unit_smul_of_intertwines` for `FDRep`. -/
theorem exists_unit_smul_of_intertwines (A : FDRep k G) [Nontrivial A]
    (hScalar : ∀ f : A ⟶ A, ∃ c : k, c • 𝟙 A = f)
    {W : Type w} [AddCommGroup W] [Module k W] {σ : Representation k G W}
    (a b : A ≃ₗ[k] W)
    (ha : ∀ g x, a (A.ρ g x) = σ g (a x))
    (hb : ∀ g x, b (A.ρ g x) = σ g (b x)) :
    ∃ c : kˣ, ∀ x, a x = (c : k) • b x := by
  refine Representation.exists_unit_smul_of_intertwines (ρ := A.ρ) (fun f hf ↦ ?_) a b ha hb
  let f' : A ⟶ A :=
    { hom := FGModuleCat.ofHom f
      comm := fun g => by
        apply FGModuleCat.hom_ext
        ext x
        -- The constructor bundles a linear map in two category wrappers; expose its
        -- evaluation to check equivariance on the original carrier.
        change f (A.ρ g x) = A.ρ g (f x)
        exact LinearMap.congr_fun (hf g) x }
  obtain ⟨c, hc⟩ := hScalar f'
  exact ⟨c, LinearMap.ext fun x ↦ (congrArg (fun t : A ⟶ A => t.hom.hom.hom x) hc).symm⟩

end FDRep
