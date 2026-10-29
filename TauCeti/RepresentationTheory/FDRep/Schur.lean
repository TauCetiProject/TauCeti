/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.FDRep
public import TauCeti.RepresentationTheory.Intertwining

/-!
# Scalar comparison of intertwiners

When every endomorphism of a nonzero finite-dimensional representation is scalar, two invertible
intertwiners from it to the same representation differ by a unit scalar. The scalar-endomorphism
hypothesis is explicit, so the comparison applies over splitting fields that are not algebraically
closed. It is used to construct factor sets for projective extensions.

This is a categorical adapter for `Representation.exists_unit_smul_of_intertwines`, which
generalizes the former irreducible-case argument by taking the scalar-Schur hypothesis explicitly.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Chapter 11.
-/

public section

open CategoryTheory

namespace FDRep

variable {k G : Type*} [Field k] [Monoid G] (A : FDRep k G) [Nontrivial A]

/-- Two invertible intertwiners out of a representation with scalar endomorphisms differ by a
unit scalar, without an algebraic-closure hypothesis. -/
theorem exists_unit_smul_of_intertwines
    (hScalar : ∀ f : A ⟶ A, ∃ c : k, f = c • 𝟙 A)
    {W : Type*} [AddCommGroup W] [Module k W] {σ : Representation k G W}
    (a b : A ≃ₗ[k] W)
    (ha : ∀ g v, a (A.ρ g v) = σ g (a v))
    (hb : ∀ g v, b (A.ρ g v) = σ g (b v)) :
    ∃ c : kˣ, ∀ v, a v = (c : k) • b v := by
  refine Representation.exists_unit_smul_of_intertwines A.ρ ?_ a b ha hb
  intro f hf
  obtain ⟨c, hc⟩ := hScalar (FDRep.forget₂HomLinearEquiv A A <|
    Rep.ofHom (f.intertwiningMap_of_isIntertwiningMap A.ρ A.ρ hf))
  refine ⟨c, fun v => ?_⟩
  -- These constructors only bundle the given linear map: the intertwining-map constructor and
  -- Rep.ofHom preserve it, and forget₂HomLinearEquiv rewraps it with InducedCategory.homMk and
  -- ModuleCat.ofHom. Thus evaluation is definitionally f v; scalar identity evaluates to c • v.
  exact congrArg (fun f : A ⟶ A => f.hom.hom v) hc

end FDRep
