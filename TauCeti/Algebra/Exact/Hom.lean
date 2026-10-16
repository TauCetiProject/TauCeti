/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic

/-!
# Exactness of additive Hom from an extension property

For an exact pair `X → Y → Z`, an additive homomorphism on `Y` vanishing on the image of
`X` descends to `Y ⧸ ker g`. If every such homomorphism extends along the embedding
`Y ⧸ ker g → Z`, then precomposition gives an exact pair
`Hom(Z, W) → Hom(Y, W) → Hom(X, W)`.

The groups `Y` and `Z` need not be commutative, and `X` only needs addition and an additive
identity. This criterion separates the quotient argument from the hypotheses used to obtain
extensions, such as injectivity of the target or splitting of the embedding.
-/

public section

/-- If every additive homomorphism `Y ⧸ ker g →+ W` extends along the embedding induced by
`g`, then `Hom(-, W)` sends the exact pair `X → Y → Z` to an exact pair
`Hom(Z, W) → Hom(Y, W) → Hom(X, W)`. The additive groups `Y` and `Z` need not be commutative,
and `X` only needs addition and an additive identity. -/
theorem Function.Exact.compHom'_of_forall_exists_comp_eq {X Y Z W : Type*} [AddZeroClass X]
    [AddGroup Y] [AddGroup Z] [AddCommMonoid W] {f : X →+ Y} {g : Y →+ Z}
    (h : Function.Exact f g)
    (hext : ∀ φ : Y ⧸ g.ker →+ W, ∃ ψ : Z →+ W, ψ.comp (QuotientAddGroup.kerLift g) = φ) :
    Function.Exact (g.compHom' (P := W)) (f.compHom') := by
  intro ψ
  constructor
  · intro hψ
    have hker : g.ker ≤ ψ.ker := fun y hy => by
      obtain ⟨x, rfl⟩ := (h y).1 hy
      simpa using DFunLike.congr_fun hψ x
    obtain ⟨χ, hχ⟩ := hext (QuotientAddGroup.lift g.ker ψ hker)
    exact ⟨χ, AddMonoidHom.ext fun y => by
      simpa using DFunLike.congr_fun hχ (QuotientAddGroup.mk y)⟩
  · rintro ⟨χ, rfl⟩
    ext x
    simp [h.apply_apply_eq_zero]
