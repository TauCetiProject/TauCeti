/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.ExponentialGroup.Completion
public import TauCeti.GroupTheory.ExponentialGroup.Polynomial.Basic

/-!
# Completions with exponents in `ℤ[t]`

A `ℤ[t]`-group structure is determined by its `t`-th power, which can be any map that commutes with
conjugation and is multiplicative on commuting elements
(`TauCeti.IsExponentialGroup.isExponentialGroup_polynomialPow`). So a `ℤ[t]`-completion
`μ : G →* K` of a group `G` is universal among the groups `H` with such a map, in the universe `w`
of its universal property: every homomorphism `φ : G →* H` extends uniquely along `μ` to a
homomorphism `K →* H` that takes the `t`-th power of `K` to a given such map `T : H → H`.

## Main definitions

* `TauCeti.IsExponentialGroup.IsCompletion.liftMapPowX`: that extension, for `H` in the universe
  `w`. It takes `x ^ p` to the power of its image for the exponentiation determined by `T`
  (`liftMapPowX_pow`).

## Main results

* `TauCeti.IsExponentialGroup.IsCompletion.existsUnique_lift_map_pow_X`: the universal property
  of a `ℤ[t]`-completion in terms of the `t`-th power. For the tensor completion, apply it to
  `TauCeti.ExponentialGroup.Completion.isCompletion_of`.

## References

* A. G. Myasnikov, V. N. Remeslennikov, *Exponential groups. II. Extensions of centralizers and
  tensor completion of CSA-groups*, Internat. J. Algebra Comput. 6 (1996), Definition 1 and §2.
* A. G. Myasnikov, V. N. Remeslennikov, D. E. Serbin, *Regular free length functions on Lyndon's
  free `ℤ[t]`-group `F^{ℤ[t]}`*, §2.1.
-/

public section

open Polynomial

universe w

namespace TauCeti.IsExponentialGroup.IsCompletion

variable {G K : Type*} [Group G] [Group K] [Pow K ℤ[X]] [IsExponentialGroup ℤ[X] K] {μ : G →* K}
  (hμ : IsCompletion.{w} ℤ[X] μ) {H : Type w} [Group H] {T : H → H}
  (hconj : ∀ g h : H, T (g * h * g⁻¹) = g * T h * g⁻¹)
  (hmul : ∀ g h : H, Commute g h → T (g * h) = T g * T h)

/-- For a `ℤ[t]`-completion `μ : G →* K`, a group `H` in the universe `w` of its universal property
and a map `T : H → H` that commutes with conjugation and is multiplicative on commuting elements,
the homomorphism `K →* H` extending `φ : G →* H` along `μ` and taking the `t`-th power to `T`. -/
noncomputable def liftMapPowX (φ : G →* H) : K →* H :=
  letI := polynomialPow T
  haveI := isExponentialGroup_polynomialPow hconj hmul
  (hμ.lift φ).toMonoidHom

@[simp]
theorem liftMapPowX_comp (φ : G →* H) : (hμ.liftMapPowX hconj hmul φ).comp μ = φ :=
  letI := polynomialPow T
  haveI := isExponentialGroup_polynomialPow hconj hmul
  hμ.lift_comp φ

@[simp]
theorem liftMapPowX_eq (φ : G →* H) (g : G) : hμ.liftMapPowX hconj hmul φ (μ g) = φ g :=
  DFunLike.congr_fun (hμ.liftMapPowX_comp hconj hmul φ) g

/-- The extension `liftMapPowX` takes the power `x ^ p` to the power of its image for the
exponentiation determined by `T`. -/
@[simp]
theorem liftMapPowX_pow (φ : G →* H) (x : K) (p : ℤ[X]) :
    hμ.liftMapPowX hconj hmul φ (x ^ p) =
      (letI := polynomialPow T; hμ.liftMapPowX hconj hmul φ x ^ p) :=
  letI := polynomialPow T
  haveI := isExponentialGroup_polynomialPow hconj hmul
  (hμ.lift φ).map_pow x p

/-- The extension `liftMapPowX` takes the `t`-th power to `T`. -/
theorem liftMapPowX_pow_X (φ : G →* H) (x : K) :
    hμ.liftMapPowX hconj hmul φ (x ^ (X : ℤ[X])) = T (hμ.liftMapPowX hconj hmul φ x) :=
  (hμ.liftMapPowX_pow hconj hmul φ x X).trans (polynomialPow_X T _)

/-- The extension `liftMapPowX` is the only homomorphism extending `φ` along `μ` that takes the
`t`-th power to `T`. -/
theorem eq_liftMapPowX {φ : G →* H} {ψ : K →* H} (hψ : ψ.comp μ = φ)
    (hT : ∀ x : K, ψ (x ^ (X : ℤ[X])) = T (ψ x)) : ψ = hμ.liftMapPowX hconj hmul φ := by
  let := polynomialPow T
  have := isExponentialGroup_polynomialPow hconj hmul
  have hpow := ψ.map_pow_of_map_pow_X fun x => by rw [hT, polynomialPow_X]
  exact congrArg ExponentialHom.toMonoidHom (hμ.eq_lift (ψ := ⟨ψ, hpow⟩) hψ)

include hμ hconj hmul in
/-- **The universal property of a `ℤ[t]`-completion in terms of the `t`-th power.** For a
`ℤ[t]`-completion `μ : G →* K`, a group `H` in the universe `w` of its universal property and a map
`T : H → H` that commutes with conjugation and is multiplicative on commuting elements, every
homomorphism `φ : G →* H` extends uniquely along `μ` to a homomorphism `ψ : K →* H` with
`ψ (x ^ t) = T (ψ x)`. -/
theorem existsUnique_lift_map_pow_X (φ : G →* H) :
    ∃! ψ : K →* H, ψ.comp μ = φ ∧ ∀ x : K, ψ (x ^ (X : ℤ[X])) = T (ψ x) :=
  ⟨hμ.liftMapPowX hconj hmul φ,
    ⟨hμ.liftMapPowX_comp hconj hmul φ, hμ.liftMapPowX_pow_X hconj hmul φ⟩,
    fun _ hψ => hμ.eq_liftMapPowX hconj hmul hψ.1 hψ.2⟩

end TauCeti.IsExponentialGroup.IsCompletion
