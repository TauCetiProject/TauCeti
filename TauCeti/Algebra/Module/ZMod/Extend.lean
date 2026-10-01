/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Extending additive homomorphisms between groups killed by a prime

An additive commutative group killed by a prime `p` is an `𝔽_p`-vector space, through
`AddCommGroup.zmodModule`, and every additive homomorphism between two such groups is `𝔽_p`-linear.
Since an injective linear map of vector spaces has a linear left inverse, an injective additive
homomorphism into a group killed by `p` has an additive left inverse, and so an additive
homomorphism out of its source, with values in an arbitrary additive monoid `N`, extends along it.
In other words, `Hom(-, N)` is exact on the additive groups killed by `p` for every `N`; this is the
algebraic input to the duality statements for finite `𝔽_p[G]`-modules.

Primality is essential: with `p = 4`, the identity of `2ℤ/4ℤ ≅ ℤ/2ℤ` does not extend along the
inclusion `2ℤ/4ℤ ⊆ ℤ/4ℤ` to a homomorphism `ℤ/4ℤ → ℤ/2ℤ`, since every such homomorphism kills
`2ℤ/4ℤ`.

## Main results

* `AddMonoidHom.exists_comp_eq_of_injective`: for `p` prime and `B` killed by `p`, every additive
  homomorphism `A →+ N` is the restriction along an injective `f : A →+ B` of an additive
  homomorphism `B →+ N`.
* `Function.Exact.compHom'`: `Hom(-, W)` is exact on the groups killed by `p`: an exact pair
  `X → Y → Z` with `Z` killed by `p` dualises to an exact pair `Hom(Z, W) → Hom(Y, W) → Hom(X, W)`.
-/

public section

namespace TauCeti

variable {p : ℕ} [Fact p.Prime] {A B N : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommMonoid N]

/-- **Extension along an injection into a group killed by a prime.** If `p` is prime and `B` is
killed by `p`, every additive homomorphism `φ : A →+ N` extends along an injective additive
homomorphism `f : A →+ B` to a homomorphism `ψ : B →+ N` with `ψ ∘ f = φ`. No hypothesis is
needed on `N`: the extension is `φ` composed with an additive left inverse of `f`. -/
theorem _root_.AddMonoidHom.exists_comp_eq_of_injective (hB : ∀ b : B, p • b = 0)
    {f : A →+ B} (hf : Function.Injective f) (φ : A →+ N) :
    ∃ ψ : B →+ N, ψ.comp f = φ := by
  have hA : ∀ a : A, p • a = 0 := fun a => hf (by rw [map_nsmul, hB, map_zero])
  let := AddCommGroup.zmodModule hA
  let := AddCommGroup.zmodModule hB
  obtain ⟨g, hg⟩ := (f.toZModLinearMap p).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hf)
  refine ⟨φ.comp g.toAddMonoidHom, AddMonoidHom.ext fun a => ?_⟩
  have h := LinearMap.congr_fun hg a
  simp only [LinearMap.comp_apply, AddMonoidHom.coe_toZModLinearMap,
    LinearMap.id_apply] at h
  simp [h]

/-- **`Hom(-, W)` is exact on groups killed by a prime.** If `X → Y → Z` is an exact pair of
additive homomorphisms with `Z` killed by `p`, then for every additive commutative monoid `W` the
pair `Hom(Z, W) → Hom(Y, W) → Hom(X, W)` obtained by precomposition is exact. A homomorphism on `Y`
killing the range of `f`, which is the kernel of `g`, descends to `Y ⧸ ker g`, and extends from
there along the embedding of `Y ⧸ ker g` into `Z`. -/
theorem _root_.Function.Exact.compHom' {X Y Z W : Type*} [AddCommGroup X] [AddCommGroup Y]
    [AddCommGroup Z] [AddCommMonoid W] {f : X →+ Y} {g : Y →+ Z} (h : Function.Exact f g)
    (hZ : ∀ z : Z, p • z = 0) :
    Function.Exact (g.compHom' (P := W)) (f.compHom') := by
  intro ψ
  constructor
  · intro hψ
    have hker : g.ker ≤ ψ.ker := fun y hy => by
      obtain ⟨x, rfl⟩ := (h y).1 hy
      simpa using DFunLike.congr_fun hψ x
    obtain ⟨χ, hχ⟩ := AddMonoidHom.exists_comp_eq_of_injective hZ
      (QuotientAddGroup.kerLift_injective g) (QuotientAddGroup.lift g.ker ψ hker)
    exact ⟨χ, AddMonoidHom.ext fun y => by
      simpa using DFunLike.congr_fun hχ (QuotientAddGroup.mk y)⟩
  · rintro ⟨χ, rfl⟩
    ext x
    simp [h.apply_apply_eq_zero]

end TauCeti
