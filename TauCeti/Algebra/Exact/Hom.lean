/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic

/-!
# Exactness of additive Hom and the extension property

For an exact pair `X → Y → Z`, an additive homomorphism on `Y` vanishing on the image of
`X` descends to `Y ⧸ ker g`. Precomposition gives an exact pair
`Hom(Z, W) → Hom(Y, W) → Hom(X, W)` if and only if every additive homomorphism
`Y ⧸ ker g →+ W` extends along the embedding `Y ⧸ ker g → Z`.

The groups `Y` and `Z` need not be commutative, and `X` only needs addition and an additive
identity. This criterion separates the quotient argument from the hypotheses used to obtain
extensions, such as injectivity of the target or splitting of the embedding.
-/

public section

/-- For an exact pair `X → Y → Z`, `Hom(-, W)` gives an exact pair
`Hom(Z, W) → Hom(Y, W) → Hom(X, W)` if and only if every additive homomorphism
`Y ⧸ ker g →+ W` extends along the embedding `Y ⧸ ker g → Z` induced by `g`. The additive
groups `Y` and `Z` need not be commutative, and `X` only needs addition and an additive
identity. -/
theorem Function.Exact.exact_compHom'_iff_forall_exists_comp_eq {X Y Z W : Type*}
    [AddZeroClass X] [AddGroup Y] [AddGroup Z] [AddCommMonoid W] {f : X →+ Y} {g : Y →+ Z}
    (h : Function.Exact f g) :
    Function.Exact (g.compHom' (P := W)) f.compHom' ↔
      ∀ φ : Y ⧸ g.ker →+ W, ∃ ψ : Z →+ W, ψ.comp (QuotientAddGroup.kerLift g) = φ := by
  refine ⟨fun hW φ => ?_, fun hext ψ => ⟨fun hψ => ?_, ?_⟩⟩
  · obtain ⟨χ, hχ⟩ := (hW (φ.comp (QuotientAddGroup.mk' g.ker))).1 <| by
      ext x
      simp [(QuotientAddGroup.eq_zero_iff (f x)).2 (g.mem_ker.2 (h.apply_apply_eq_zero x))]
    exact ⟨χ, by ext y; simpa using DFunLike.congr_fun hχ y⟩
  · have hker : g.ker ≤ ψ.ker := fun y hy => by
      obtain ⟨x, rfl⟩ := (h y).1 hy
      simpa using DFunLike.congr_fun hψ x
    obtain ⟨χ, hχ⟩ := hext (QuotientAddGroup.lift g.ker ψ hker)
    exact ⟨χ, AddMonoidHom.ext fun y => by
      simpa using DFunLike.congr_fun hχ (QuotientAddGroup.mk y)⟩
  · rintro ⟨χ, rfl⟩
    ext x
    simp [h.apply_apply_eq_zero]
