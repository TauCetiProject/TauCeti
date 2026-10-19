/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CrossedProduct.BrauerClass
public import TauCeti.Algebra.CrossedProduct.Quadratic
public import TauCeti.Algebra.Quaternion.BrauerClass

/-!
# Quaternion algebras as crossed products

Let `L/K` be a Galois extension of degree two with nontrivial automorphism `σ`, and let `α ∈ L`
with `α² = a ∈ Kˣ` and `α ∉ K`, so that `L = K(√a)` and `σ α = -α`. For `b ∈ Kˣ`, the crossed
product of the quadratic cocycle `TauCeti.TwoCocycle.quadratic h b`, whose only nontrivial value is
`c(σ, σ) = b`, is generated over `K` by `i = α` and `j = u_σ` with

`i² = a`, `j² = b`, `j i = σ(α) j = -i j`,

which are the relations of the quaternion algebra `ℍ[K, a, b]`. Both algebras have dimension four,
and the quaternion algebra is simple, so the resulting homomorphism `ℍ[K, a, b] → (L, σ, b)` is an
isomorphism (`TauCeti.CrossedProduct.nonempty_quaternionAlgebra_algEquiv_quadratic`). In the
Brauer group, the class of the quadratic cocycle of `b` is therefore the quaternion symbol
`[(a, b)]` (`TauCeti.BrauerGroup.crossedProductClass_quadratic`).

This is the step at which a cocycle meets an algebra in the computation `ι [(a, b)] = (a) ∪ (b)`
of the quaternion symbol as a cup product.

## Main results

* `TauCeti.CrossedProduct.nonempty_quaternionAlgebra_algEquiv_quadratic`: the crossed product of
  the quadratic cocycle of `b` over `K(√a)` is isomorphic to `ℍ[K, a, b]`.
* `TauCeti.BrauerGroup.crossedProductClass_quadratic`: its Brauer class is `[(a, b)]`.

## References

* J.-P. Serre, *Local Fields*, Graduate Texts in Mathematics 67, Springer (1979), Chapter XIV,
  §2.
* P. Gille and T. Szamuely, *Central Simple Algebras and Galois Cohomology* (2006), §2.5 and §4.7.
-/

public section

open scoped Quaternion

universe u v

namespace TauCeti

namespace CrossedProduct

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [IsGalois K L] (h : Nat.card (L ≃ₐ[K] L) = 2) {a : Kˣ} {α : L}

omit [FiniteDimensional K L] [IsGalois K L] in
include h in
/-- In an automorphism group of order two, the nontrivial automorphism is an involution. -/
private theorem mul_self_eq_one (σ : L ≃ₐ[K] L) : σ * σ = 1 := by
  rw [← sq, ← h, pow_card_eq_one']

include h in
/-- If `α ∉ K` squares into `K`, the nontrivial automorphism of a quadratic Galois extension sends
`α` to `-α`. -/
private theorem apply_eq_neg (hα : α ^ 2 = algebraMap K L a)
    (hαK : α ∉ Set.range (algebraMap K L)) {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) : σ α = -α := by
  obtain ⟨ρ, -, hρ⟩ := (Nat.card_eq_two_iff' (1 : L ≃ₐ[K] L)).1 h
  refine (sq_eq_sq_iff_eq_or_eq_neg.1 (by rw [← map_pow, hα, AlgEquiv.commutes])).resolve_left
    fun hσα ↦ hαK ?_
  refine (IsGalois.mem_range_algebraMap_iff_fixed α).2 fun τ ↦ ?_
  rcases eq_or_ne τ 1 with rfl | hτ
  · rfl
  · rwa [hρ τ hτ, ← hρ σ hσ]

/-- The quaternion basis `i = α`, `j = u_σ` of the crossed product of the quadratic cocycle of
`b`. -/
private noncomputable def quadraticQuaternionBasis (hα : α ^ 2 = algebraMap K L a)
    (hαK : α ∉ Set.range (algebraMap K L)) (b : Kˣ) {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) :
    QuaternionAlgebra.Basis (CrossedProduct (TwoCocycle.quadratic h b)) (a : K) 0 (b : K) where
  i := inc _ α
  j := basis _ σ
  k := inc _ α * basis _ σ
  i_mul_i := by
    rw [← map_mul, ← sq, hα]
    simp [Algebra.algebraMap_eq_smul_one]
  j_mul_j := by
    rw [basis_mul_basis, mul_self_eq_one h, basis_one,
      TwoCocycle.quadratic_toFun_of_ne_one_of_ne_one h b hσ hσ]
    simp [Algebra.algebraMap_eq_smul_one]
  i_mul_j := rfl
  j_mul_i := by
    rw [basis_mul_inc, apply_eq_neg h hα hαK hσ]
    simp

/-- **The quaternion algebra `(a, b)` is the crossed product of the quadratic cocycle of `b` over
`K(√a)`.** If `L/K` is Galois with automorphism group of order two and `α ∈ L ∖ K` has
`α² = a`, the crossed product of `TauCeti.TwoCocycle.quadratic h b` is isomorphic to
`ℍ[K, a, b]`, by `i ↦ α` and `j ↦ u_σ` for the nontrivial automorphism `σ`. -/
theorem nonempty_quaternionAlgebra_algEquiv_quadratic [Invertible (2 : K)]
    (hα : α ^ 2 = algebraMap K L a) (hαK : α ∉ Set.range (algebraMap K L)) (b : Kˣ) :
    Nonempty (ℍ[K,(a : K),(b : K)] ≃ₐ[K] CrossedProduct (TwoCocycle.quadratic h b)) := by
  obtain ⟨σ, hσ, -⟩ := (Nat.card_eq_two_iff' (1 : L ≃ₐ[K] L)).1 h
  let f := (quadraticQuaternionBasis h hα hαK b hσ).liftHom
  -- `ℍ[K, a, b]` is simple, so `f` is injective, and both sides have dimension four
  have hinj : Function.Injective f := f.toRingHom.injective
  have hdim : Module.finrank K ℍ[K,(a : K),(b : K)] =
      Module.finrank K (CrossedProduct (TwoCocycle.quadratic h b)) := by
    rw [QuaternionAlgebra.finrank_eq_four, finrank_eq_finrank_sq, ← IsGalois.card_aut_eq_finrank,
      h]
    norm_num
  exact ⟨AlgEquiv.ofBijective f ⟨hinj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim (f := f.toLinearMap)).1 hinj⟩⟩

end CrossedProduct

namespace BrauerGroup

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (h : Nat.card (L ≃ₐ[K] L) = 2) {a : Kˣ} {α : L}

/-- **The Brauer class of the quadratic cocycle of `b` over `K(√a)` is the quaternion symbol
`[(a, b)]`.** -/
theorem crossedProductClass_quadratic [Invertible (2 : K)] (hα : α ^ 2 = algebraMap K L a)
    (hαK : α ∉ Set.range (algebraMap K L)) (b : Kˣ) :
    crossedProductClass (TwoCocycle.quadratic h b) = quaternionClass a b := by
  obtain ⟨e⟩ := CrossedProduct.nonempty_quaternionAlgebra_algEquiv_quadratic h hα hαK b
  rw [crossedProductClass_def, quaternionClass_def]
  exact (mk_eq_mk_of_algEquiv (A := CSA.of K ℍ[K,(a : K),(b : K)])
    (B := CSA.of K (CrossedProduct (TwoCocycle.quadratic h b))) e).symm

end BrauerGroup

end TauCeti
