/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Exp.ExponentialPolynomial

import TauCeti.Algebra.CharZero.RatCast
import TauCeti.LinearAlgebra.Vandermonde
import TauCeti.NumberTheory.Transcendental.GelfondSchneider.SchneiderAuxiliary

/-!
# The first nonvanishing derivative of Gelfond's auxiliary function

Let `K` be a field of characteristic zero with an embedding `σ : K →+* ℂ`, let `λ ∈ ℂ` and let
`α, β, γ ∈ K` with `σ α = exp λ`, `σ γ = exp (σ β λ)` and `β` irrational. In Gelfond's proof of
the Gelfond–Schneider theorem the auxiliary function is the exponential sum

`R(z) = ∑_{a, b = 1}^{q} η_{ab} exp ((a + b σ β) λ z)`

with coefficients `η_{ab} ∈ K` (written `σ η_{ab}` once embedded in `ℂ`). Its derivatives at the
natural numbers lie in `σ(K)` after factoring out a power of `λ`: since `exp ((a + b σ β) λ t)` is
`σ (α ^ (a t) γ ^ (b t))`,

`R⁽ᵏ⁾(t) = λ ^ k σ (y_k(t))`, where `y_k(t) = ∑_{a, b} η_{ab} (a + b β) ^ k α ^ (a t) γ ^ (b t)`.

In the application, `K` is a number field containing the algebraic numbers `α, β, γ`, and the
coefficients `η` are algebraic integers chosen by Siegel's lemma so that `R` vanishes to a high
order `n` at the points `t = 1, …, m`. Gelfond's argument then uses the first derivative order `r`
at which `R` fails to vanish at one of these points, say at `t₀`: the number `ρ = y_r(t₀) ∈ K` is
nonzero, so in that number-field setting (after clearing the denominators of `α, β, γ`) it
satisfies Liouville's lower bound, while the vanishing of all lower derivatives gives an analytic
upper bound for `|R⁽ʳ⁾(t₀)| = |λ| ^ r |σ ρ|`.

This file makes no arithmetic assumption on `K`: it proves that such `r` and `t₀` exist, with
`n ≤ r < q ^ 2`, as soon as `λ ≠ 0` and `η ≠ 0`. For each fixed `t`, the values `y_k(t)` are the
power sums `∑ w_{ab} θ_{ab} ^ k` with weights `w_{ab} = η_{ab} α ^ (a t) γ ^ (b t)` and nodes
`θ_{ab} = a + b β`. The nodes are pairwise distinct because `β` is irrational, so the Vandermonde
matrix of the nodes is invertible and one of the first `q ^ 2` power sums is nonzero. In Lean the
indices `a, b` run over `Fin q`, and the frequencies are written `(a + 1) + (b + 1) β`.

## Main results

* `TauCeti.exists_gelfond_value_ne_zero`: for `η ≠ 0` and a nonempty finite set `T ⊆ ℕ`, there
  are `r < q ^ 2` and `t₀ ∈ T` with `y_k(t) = 0` for all `k < r` and `t ∈ T`, and `y_r(t₀) ≠ 0`.
* `RingHom.iteratedDeriv_gelfond_auxiliary_natCast`: `R⁽ᵏ⁾(t) = λ ^ k σ (y_k(t))`.
* `RingHom.exists_iteratedDeriv_gelfond_auxiliary_ne_zero`: if `λ ≠ 0`, `η ≠ 0` and `R` vanishes
  to order `n` on `T`, then there are `r` with `n ≤ r < q ^ 2` and `t₀ ∈ T` such that `R`
  vanishes to order `r` on `T` and `R⁽ʳ⁾(t₀) ≠ 0`.

## References

* M. Karatarakis and F. Wiedijk, *A formalization of the Gelfond–Schneider theorem*,
  arXiv:2603.24823 (2026), §3.
* K. Soundararajan (notes by I. Petrow), *Transcendental number theory*, Stanford Math 249A
  course notes (2011).
-/

public section

open Finset

namespace TauCeti

variable {K : Type*} [Field K] [CharZero K]

/-- **The first nonvanishing derivative of Gelfond's auxiliary function, algebraic form.** Let
`K` be a field of characteristic zero, let `α, γ ∈ K` be nonzero and `β ∈ K` irrational, and let
`η : Fin q → Fin q → K` be nonzero. Put
`y_k(t) = ∑_{a, b} η_{ab} ((a + 1) + (b + 1) β) ^ k α ^ ((a + 1) t) γ ^ ((b + 1) t)`. Then for every
nonempty finite set `T` of natural numbers there are `r < q ^ 2` and `t₀ ∈ T` such that
`y_k(t) = 0` for all `k < r` and `t ∈ T`, and `y_r(t₀) ≠ 0`. -/
theorem exists_gelfond_value_ne_zero {α β γ : K} (hα : α ≠ 0) (hγ : γ ≠ 0)
    (hβ : ∀ r : ℚ, (r : K) ≠ β) {q : ℕ} {η : Fin q → Fin q → K} (hη : η ≠ 0) {T : Finset ℕ}
    (hT : T.Nonempty) :
    ∃ r < q ^ 2, ∃ t₀ ∈ T,
      (∀ k < r, ∀ t ∈ T, ∑ a, ∑ b, η a b * (((a + 1 : ℕ) : K) + (b + 1 : ℕ) * β) ^ k *
          (α ^ ((a + 1 : ℕ) * t) * γ ^ ((b + 1 : ℕ) * t)) = 0) ∧
        ∑ a, ∑ b, η a b * (((a + 1 : ℕ) : K) + (b + 1 : ℕ) * β) ^ r *
          (α ^ ((a + 1 : ℕ) * t₀) * γ ^ ((b + 1 : ℕ) * t₀)) ≠ 0 := by
  classical
  obtain ⟨y, hy⟩ : ∃ y : ℕ → ℕ → K, ∀ k t, y k t = ∑ a, ∑ b, η a b *
      (((a + 1 : ℕ) : K) + (b + 1 : ℕ) * β) ^ k * (α ^ ((a + 1 : ℕ) * t) * γ ^ ((b + 1 : ℕ) * t)) :=
    ⟨_, fun _ _ ↦ rfl⟩
  simp only [← hy]
  obtain ⟨t₁, ht₁⟩ := hT
  obtain ⟨a, b, hab⟩ : ∃ a b, η a b ≠ 0 := by
    by_contra! h
    exact hη (funext fun a ↦ funext (h a))
  -- At `t₁`, the values `y_k(t₁)` are power sums with distinct nodes and weights not all zero.
  obtain ⟨k, hk, hne⟩ := exists_lt_card_sum_mul_pow_ne_zero (s := univ)
    (θ := fun p : Fin q × Fin q ↦ ((p.1 + 1 : ℕ) : K) + (p.2 + 1 : ℕ) * β)
    (w := fun p ↦ η p.1 p.2 * (α ^ ((p.1 + 1 : ℕ) * t₁) * γ ^ ((p.2 + 1 : ℕ) * t₁)))
    (by
      rintro ⟨a, b⟩ - ⟨a', b'⟩ - h
      simpa [Fin.val_inj] using ratCast_add_ratCast_mul_injective hβ
        (a₁ := ((a + 1 : ℕ), (b + 1 : ℕ)))
        (a₂ := ((a' + 1 : ℕ), (b' + 1 : ℕ))) (by simpa using h))
    ⟨(a, b), mem_univ _, mul_ne_zero hab (mul_ne_zero (pow_ne_zero _ hα) (pow_ne_zero _ hγ))⟩
  have hk' : y k t₁ ≠ 0 := by
    rw [Fintype.sum_prod_type] at hne
    rw [hy]
    exact ne_of_eq_of_ne (sum_congr rfl fun a _ ↦ sum_congr rfl fun b _ ↦ by ring) hne
  have hex : ∃ k, ∃ t ∈ T, y k t ≠ 0 := ⟨k, t₁, ht₁, hk'⟩
  obtain ⟨t₀, ht₀, hr⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, ?_, t₀, ht₀, fun k' hk' t ht ↦ ?_, hr⟩
  · calc Nat.find hex ≤ k := Nat.find_min' hex ⟨t₁, ht₁, hk'⟩
      _ < q ^ 2 := by simpa [sq] using hk
  · by_contra h
    exact Nat.find_min hex hk' ⟨t, ht, h⟩

end TauCeti

namespace RingHom

/-- If `σ α = exp λ` and `σ γ = exp (σ β λ)`, then the `k`-th derivative of Gelfond's auxiliary
function `R(z) = ∑_{a, b} σ η_{ab} exp (((a + 1) + (b + 1) σ β) λ z)` at a natural number `t` is
`λ ^ k` times the image under `σ` of
`y_k(t) = ∑_{a, b} η_{ab} ((a + 1) + (b + 1) β) ^ k α ^ ((a + 1) t) γ ^ ((b + 1) t)`. -/
theorem iteratedDeriv_gelfond_auxiliary_natCast {R : Type*} [Ring R] (σ : R →+* ℂ) {l : ℂ}
    {α β γ : R} (hα : σ α = Complex.exp l) (hγ : σ γ = Complex.exp (σ β * l)) {q : ℕ}
    (η : Fin q → Fin q → R) (k t : ℕ) :
    iteratedDeriv k (fun z ↦ ∑ a, ∑ b, σ (η a b) *
        Complex.exp ((((a + 1 : ℕ) : ℂ) + (b + 1 : ℕ) * σ β) * l * z)) t =
      l ^ k * σ (∑ a, ∑ b, η a b * (((a + 1 : ℕ) : R) + (b + 1 : ℕ) * β) ^ k *
        (α ^ ((a + 1 : ℕ) * t) * γ ^ ((b + 1 : ℕ) * t))) := by
  have hR : (fun z ↦ ∑ a, ∑ b, σ (η a b) *
      Complex.exp ((((a + 1 : ℕ) : ℂ) + (b + 1 : ℕ) * σ β) * l * z)) =
      fun z ↦ ∑ p : Fin q × Fin q, σ (η p.1 p.2) *
        Complex.exp ((((p.1 + 1 : ℕ) : ℂ) + (p.2 + 1 : ℕ) * σ β) * l * z) := by
    funext z
    rw [Fintype.sum_prod_type]
  rw [hR, Finset.iteratedDeriv_sum_mul_cexp]
  dsimp only
  rw [Fintype.sum_prod_type, map_sum, mul_sum]
  refine sum_congr rfl fun a _ ↦ ?_
  rw [map_sum, mul_sum]
  refine sum_congr rfl fun b _ ↦ ?_
  rw [map_mul, σ.map_pow_mul_pow_eq_exp hα hγ]
  simp only [map_mul, map_pow, map_add, map_natCast, mul_pow]
  rw [mul_comm ((t : ℂ) * l), mul_comm (t : ℂ) l, ← mul_assoc _ l]
  ring

/-- **The first nonvanishing derivative of Gelfond's auxiliary function.** Let `K` be a field with
an embedding `σ : K →+* ℂ`, let `λ ≠ 0`, and let `α, β, γ ∈ K` with `β` irrational,
`σ α = exp λ` and `σ γ = exp (σ β λ)`. Let `η : Fin q → Fin q → K` be nonzero, and suppose that
`R(z) = ∑_{a, b} σ η_{ab} exp (((a + 1) + (b + 1) σ β) λ z)` vanishes to order `n` at every point
of a nonempty finite set `T` of natural numbers. Then there are `r` with `n ≤ r < q ^ 2` and
`t₀ ∈ T` such that `R` vanishes to order `r` at every point of `T` and `R⁽ʳ⁾(t₀) ≠ 0`. -/
theorem exists_iteratedDeriv_gelfond_auxiliary_ne_zero {K : Type*} [Field K] (σ : K →+* ℂ)
    {l : ℂ} (hl : l ≠ 0) {α β γ : K} (hα : σ α = Complex.exp l)
    (hγ : σ γ = Complex.exp (σ β * l)) (hβ : ∀ r : ℚ, (r : K) ≠ β) {q : ℕ}
    {η : Fin q → Fin q → K} (hη : η ≠ 0) {T : Finset ℕ} (hT : T.Nonempty) {n : ℕ}
    (hn : ∀ k < n, ∀ t ∈ T, iteratedDeriv k (fun z ↦ ∑ a, ∑ b, σ (η a b) *
      Complex.exp ((((a + 1 : ℕ) : ℂ) + (b + 1 : ℕ) * σ β) * l * z)) t = 0) :
    ∃ r, n ≤ r ∧ r < q ^ 2 ∧ ∃ t₀ ∈ T,
      (∀ k < r, ∀ t ∈ T, iteratedDeriv k (fun z ↦ ∑ a, ∑ b, σ (η a b) *
        Complex.exp ((((a + 1 : ℕ) : ℂ) + (b + 1 : ℕ) * σ β) * l * z)) t = 0) ∧
      iteratedDeriv r (fun z ↦ ∑ a, ∑ b, σ (η a b) *
        Complex.exp ((((a + 1 : ℕ) : ℂ) + (b + 1 : ℕ) * σ β) * l * z)) t₀ ≠ 0 := by
  have := σ.charZero
  have hα₀ : α ≠ 0 := fun h ↦ Complex.exp_ne_zero l (by rw [← hα, h, map_zero])
  have hγ₀ : γ ≠ 0 := fun h ↦ Complex.exp_ne_zero (σ β * l) (by rw [← hγ, h, map_zero])
  obtain ⟨r, hrq, t₀, ht₀, hzero, hr⟩ := TauCeti.exists_gelfond_value_ne_zero hα₀ hγ₀ hβ hη hT
  have hr' : iteratedDeriv r (fun z ↦ ∑ a, ∑ b, σ (η a b) *
      Complex.exp ((((a + 1 : ℕ) : ℂ) + (b + 1 : ℕ) * σ β) * l * z)) t₀ ≠ 0 := by
    rw [σ.iteratedDeriv_gelfond_auxiliary_natCast hα hγ]
    exact mul_ne_zero (pow_ne_zero _ hl) ((map_ne_zero σ).2 hr)
  refine ⟨r, ?_, hrq, t₀, ht₀, fun k hk t ht ↦ ?_, hr'⟩
  · by_contra! h
    exact hr' (hn r h t₀ ht₀)
  · rw [σ.iteratedDeriv_gelfond_auxiliary_natCast hα hγ, hzero k hk t ht, map_zero, mul_zero]

end RingHom
