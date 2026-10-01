/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Algebra.Group.Hom.Instances

/-!
# Pre- and postcomposition with homomorphisms, as bijections on homomorphisms

For a homomorphism `f : M →* N` and a commutative monoid `P`, Mathlib's `MonoidHom.compHom' f` is
precomposition with `f`, as a homomorphism `(N →* P) →* M →* P`. This file records that it is
bijective as soon as `f` is: `Hom(-, P)` takes isomorphisms to isomorphisms. The bundled form of
this fact is Mathlib's `MulEquiv.monoidHomCongrLeft`; the statement here is the one to use when
the isomorphism is given as a homomorphism known to be bijective, and the precomposition map is
the unbundled `compHom'`.

Dually, for `f : N →* P` between commutative monoids, `MonoidHom.compHom f` is postcomposition with
`f`, as a homomorphism `(M →* N) →* M →* P`. It is bijective as soon as `f` is injective and its
range contains every `n`-th root of unity of `P`, provided every element of `M` satisfies
`a ^ n = 1`: a homomorphism out of `M` takes values in the `n`-th roots of unity, so `Hom(M, -)`
sees such an `f` as an isomorphism. This is the form in which an injection of coefficient groups
whose image is the `n`-torsion induces bijections on duals.

## Main results

* `MonoidHom.compHom'_bijective`, `AddMonoidHom.compHom'_bijective`: precomposition with a bijective
  homomorphism is bijective on homomorphisms into a commutative monoid.
* `MonoidHom.compHom_bijective_of_forall_pow_eq_one`,
  `AddMonoidHom.compHom_bijective_of_forall_nsmul_eq_zero`: postcomposition with an injective
  homomorphism onto the `n`-th roots of unity is bijective on homomorphisms out of a monoid killed
  by `n`.
-/

public section

namespace TauCeti

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [CommMonoid P]

/-- Precomposition with a bijective homomorphism is bijective on homomorphisms into a commutative
monoid: `Hom(-, P)` takes isomorphisms to isomorphisms. The inverse is precomposition with the
inverse bijection. -/
@[to_additive /-- Precomposition with a bijective homomorphism is bijective on homomorphisms into
a commutative additive monoid: `Hom(-, P)` takes isomorphisms to isomorphisms. The inverse is
precomposition with the inverse bijection. -/]
theorem _root_.MonoidHom.compHom'_bijective {f : M →* N} (hf : Function.Bijective f) :
    Function.Bijective (MonoidHom.compHom' f : (N →* P) →* M →* P) :=
  ⟨fun φ ψ h => MonoidHom.ext fun n => by
      obtain ⟨m, rfl⟩ := hf.2 n
      exact DFunLike.congr_fun h m,
    fun χ => ⟨χ.comp (MulEquiv.ofBijective f hf).symm.toMonoidHom, MonoidHom.ext fun m =>
      congrArg χ ((MulEquiv.ofBijective f hf).symm_apply_apply m)⟩⟩

/-- Postcomposition with an injective homomorphism `f : N →* P` is bijective on homomorphisms out
of a monoid `M` all of whose elements satisfy `a ^ n = 1`, provided the range of `f` contains every
`n`-th root of unity of `P`: every homomorphism `M →* P` takes values in the `n`-th roots of unity,
hence in the range of `f`, and so lifts uniquely through `f`. -/
@[to_additive /-- Postcomposition with an injective homomorphism `f : N →+ P` is bijective on
homomorphisms out of an additive monoid `M` all of whose elements satisfy `n • a = 0`, provided the
range of `f` contains every element of `P` killed by `n`: every homomorphism `M →+ P` takes values
in the `n`-torsion, hence in the range of `f`, and so lifts uniquely through `f`. -/]
theorem _root_.MonoidHom.compHom_bijective_of_forall_pow_eq_one {M N P : Type*} [Monoid M]
    [CommMonoid N] [CommMonoid P] {f : N →* P} (hf : Function.Injective f) {n : ℕ}
    (hM : ∀ a : M, a ^ n = 1) (hf' : ∀ y : P, y ^ n = 1 → ∃ x, f x = y) :
    Function.Bijective (MonoidHom.compHom f : (M →* N) →* M →* P) := by
  refine ⟨fun φ ψ h => MonoidHom.ext fun a => hf ?_, fun ψ => ?_⟩
  · simpa only [MonoidHom.compHom_apply_apply, MonoidHom.comp_apply] using DFunLike.congr_fun h a
  · have hψ : ∀ a : M, ∃ x, f x = ψ a := fun a => hf' (ψ a) (by rw [← map_pow, hM, map_one])
    let φ : M → N := fun a => Classical.choose (hψ a)
    have hφ : ∀ a, f (φ a) = ψ a := fun a => Classical.choose_spec (hψ a)
    refine ⟨{ toFun := φ, map_one' := hf ?_, map_mul' := fun a b => hf ?_ },
      MonoidHom.ext fun a => ?_⟩
    · rw [hφ, map_one, map_one]
    · rw [hφ, map_mul, map_mul, hφ, hφ]
    · simpa only [MonoidHom.compHom_apply_apply, MonoidHom.comp_apply, MonoidHom.coe_mk,
        OneHom.coe_mk] using hφ a

end TauCeti
