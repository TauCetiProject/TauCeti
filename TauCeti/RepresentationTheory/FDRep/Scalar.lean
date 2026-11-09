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

For a simple object over an algebraically closed field, Mathlib's
`CategoryTheory.endomorphism_simple_eq_smul_id` supplies the hypothesis.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Chapter 11.
-/

public section

namespace FDRep

open CategoryTheory

universe u v w

variable {k : Type u} {G : Type v} [Field k] [Monoid G]

/-- If the equivariant endomorphisms of a nonzero representation are scalar, two invertible
intertwiners to the same target differ by a unit scalar. No algebraic closure is needed. -/
theorem exists_unit_smul_of_intertwines (A : FDRep k G) [Nontrivial A]
    (hScalar : ∀ f : A ⟶ A, ∃ c : k, c • 𝟙 A = f)
    {W : Type w} [AddCommGroup W] [Module k W] {σ : Representation k G W}
    (a b : A ≃ₗ[k] W)
    (ha : ∀ g x, a (A.ρ g x) = σ g (a x))
    (hb : ∀ g x, b (A.ρ g x) = σ g (b x)) :
    ∃ c : kˣ, ∀ x, a x = (c : k) • b x := by
  let f : A ⟶ A :=
    { hom := FGModuleCat.ofHom (a.trans b.symm).toLinearMap
      comm := fun g => by
        apply FGModuleCat.hom_ext
        ext x
        -- The constructor bundles a linear map in two category wrappers; expose its
        -- evaluation to check equivariance on the original carrier.
        change b.symm (a (A.ρ g x)) = A.ρ g (b.symm (a x))
        exact b.injective (by simp [ha, hb]) }
  obtain ⟨c, hc⟩ := hScalar f
  have hcx (x : A) : b.symm (a x) = c • x := by
    exact (congrArg (fun t : A ⟶ A => t.hom.hom.hom x) hc).symm
  have hne : c ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx⟩ := exists_ne (0 : A)
    exact hx ((a.trans b.symm).injective (by simpa using hcx x))
  exact ⟨Units.mk0 c hne, fun x => by simpa using congrArg b (hcx x)⟩

end FDRep
