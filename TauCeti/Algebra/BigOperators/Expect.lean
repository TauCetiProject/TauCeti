/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.GroupTheory.Coset.Card

/-!
# Means along surjective homomorphisms

For a surjective homomorphism `f : G →+ H` of finite additive groups, all fibres of `f` are cosets
of its kernel and have the same size. So the mean of `φ ∘ f` over `G` is the mean of `φ` over `H`
(`AddMonoidHom.expect_comp_of_surjective`).

## References

* This is the `Finset.expect` form of `New.finMean_comp_surjective` of
  `src/Lib/General/Groups/CharacterTheory.lean` in grh-lean (https://github.com/lsernau/grh-lean,
  Apache 2.0, Copyright 2026 Anthropic PBC).
-/

public section

open scoped BigOperators

/-- The mean of `φ ∘ f` over `G`, for a surjective additive homomorphism `f : G →+ H` of finite
groups, is the mean of `φ` over `H`. -/
theorem AddMonoidHom.expect_comp_of_surjective {G H M : Type*} [AddGroup G] [AddGroup H]
    [Fintype G] [Fintype H] [AddCommMonoid M] [Module ℚ≥0 M] (f : G →+ H)
    (hf : Function.Surjective f) (φ : H → M) : 𝔼 g, φ (f g) = 𝔼 h, φ h := by
  classical
  -- `G` is in bijection with `H × ker f`, and `f` becomes the first projection.
  let e : G ≃ H × f.ker :=
    (Equiv.sigmaFiberEquiv f).symm.trans (.sigmaEquivProdOfEquiv (f.fiberEquivKerOfSurjective hf))
  -- The first component of `e g` is `f g` by the construction of `e` from the fibres of `f`.
  refine (Fintype.expect_equiv e _ (fun p ↦ φ p.1) fun g ↦ (rfl)).trans ?_
  rw [← Finset.univ_product_univ, Finset.expect_product]
  simp
