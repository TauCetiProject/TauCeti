/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.FDRep

/-!
# Scalar comparison of intertwiners

When every endomorphism of a nonzero finite-dimensional representation is scalar, two invertible
intertwiners from it to the same representation differ by a unit scalar. The scalar-endomorphism
hypothesis is explicit, so the comparison applies over splitting fields that are not algebraically
closed. It is used to construct factor sets for projective extensions.

This is the categorical scalar-Schur variant of
`Representation.IsIrreducible.exists_unit_smul_of_intertwines`, with the endomorphism hypothesis
supplied rather than deduced from algebraic closure.

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
  let f : A ⟶ A := FDRep.forget₂HomLinearEquiv A A <| Rep.ofHom
    ((a.trans b.symm).toLinearMap.intertwiningMap_of_isIntertwiningMap A.ρ A.ρ
      (fun g v => b.injective (by simp [ha, hb])))
  obtain ⟨c, hc⟩ := hScalar f
  have hcv (v : A) : b.symm (a v) = c • v := by
    exact congrArg (fun f : A ⟶ A => f.hom.hom v) hc
  have hne : c ≠ 0 := by
    rintro rfl
    obtain ⟨v, hv⟩ := exists_ne (0 : A)
    exact hv ((a.trans b.symm).injective (by simpa using hcv v))
  refine ⟨Units.mk0 c hne, fun v => ?_⟩
  simpa using congrArg b (hcv v)

end FDRep
