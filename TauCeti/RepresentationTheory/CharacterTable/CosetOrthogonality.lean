/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Table

/-!
# Orthogonality of characters on a coset of a subgroup

Let `N` be a finite subgroup of a group `G`, and let `χ` and `χ'` be the characters of
representations `ρ` and `ρ'` of `G` over a field of characteristic zero. If the restrictions of `χ`
and `χ'` to `N` are orthogonal, `∑ n ∈ N, χ(n) χ'(n⁻¹) = 0`, then `χ` and `χ'` are orthogonal on
every coset of `N`: `∑ n ∈ N, χ(g n) χ'((g n)⁻¹) = 0` for every `g ∈ G`; the converse is the case
`g = 1` (`Representation.forall_sum_character_mul_mul_character_mul_inv_eq_zero_iff`). In
particular, over a field of characteristic zero, characters whose restrictions to `N` are distinct
irreducible characters of `N` are orthogonal on every coset of `N`
(`Representation.sum_character_mul_mul_character_mul_inv_eq_zero`). This is the companion of
`Representation.sum_character_mul_mul_character_mul_inv_eq_card` (in
`TauCeti.RepresentationTheory.CharacterTable.Gallagher`), which says that over an algebraically
closed field of characteristic zero a character restricting to an irreducible character of `N` has
unnormalized self-pairing `∑ n ∈ N, χ(g n) χ((g n)⁻¹) = |N|` on every coset of `N`. Together they
say that, over such a field, characters of `G` restricting to distinct irreducible characters of
`N` are orthonormal on every coset of `N` for the normalized pairing
`|N|⁻¹ ∑ n ∈ N, χ(g n) χ'((g n)⁻¹)`. The self-pairing statement needs algebraic closure: over `ℝ`
the two-dimensional irreducible character `(2, -1, -1)` of the cyclic group of order `3` has
unnormalized self-pairing `6`, not `3`, on `N = G`, that is normalized self-pairing `2`, not `1`.
The orthogonality proved here does not need it. For instance, for a normal
subgroup `N` of prime index, `χ` and `χ'` may be extensions to `G` of distinct `G`-stable
irreducible characters of `N`.

The proof computes a trace. Let `σ` be the action of `G` on `Hom(W, V)` by conjugation, where `ρ`
acts on `V` and `ρ'` on `W`. The left side is the trace of `σ g ∘ S`, with `S = ∑ n ∈ N, σ n`,
Mathlib's group sum `Representation.norm` of the restriction of `σ` to `N`
(`Representation.sum_character_mul_mul_character_mul_inv_eq_trace`, which needs no finiteness of
`V` or `W`). If `Hom(W, V)` is not finite-dimensional, every trace on it is `0`. Otherwise the
values of `S` are `N`-invariant, that is `N`-equivariant maps `W → V`, and the character of `σ`
at `x` is `χ(x) χ'(x⁻¹)` (`Representation.character_linHom`), so `∑ n ∈ N, χ(n) χ'(n⁻¹)` is the
sum over `N` of the character of `σ`. Since `|N|` is
invertible in `k`, the normalized sum `|N|⁻¹ ∑ n ∈ N, χ(n) χ'(n⁻¹)` is then the dimension of that
space of invariants as an element of `k` (`Representation.card_inv_mul_sum_char_eq_finrank`), and
characteristic zero lets one recover the integer dimension from it. So orthogonality on `N` makes
that space `0`, and then `S` is `0` (`Representation.self_norm_apply`). Distinct irreducible
characters of `N` are orthogonal over any field, by Schur's lemma when `|N|` is nonzero in it
(`TauCeti.sum_mul_inv_eq_zero_of_mem_irreducibleCharacters`); the field need not be algebraically
closed.

## Main results

* `Representation.forall_sum_character_mul_mul_character_mul_inv_eq_zero_iff`: over a field of
  characteristic zero, two characters are orthogonal on every coset of `N` if and only if their
  restrictions to `N` are orthogonal.
* `Representation.sum_character_mul_mul_character_mul_inv_eq_zero`: over a field of characteristic
  zero, characters restricting to distinct irreducible characters of `N` are orthogonal on every
  coset of `N`.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Chapter 6.
* The statement of `Representation.sum_character_mul_mul_character_mul_inv_eq_zero` is that of
  `GlobalTheory.T.finsum_semidirect_coset_character_orth_zero` in the Lean formalization of the
  Riemann hypothesis for Dirichlet L-functions by L. Alpöge,
  <https://github.com/leanprover-community/riemann-hypothesis>, which states it for a semidirect
  product with a cyclic complement.
-/

public section

namespace Representation

open Module

variable {k G V W : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] [CharZero k]

/-- The core of the trace computation of the module docstring: if the restrictions of the
characters to `N` are orthogonal and `W →ₗ[k] V` is finite-dimensional, the group sum `S` over `N`
of the conjugation action on `W →ₗ[k] V` is `0`. -/
private theorem norm_comp_subtype_linHom_eq_zero [FiniteDimensional k (W →ₗ[k] V)]
    (ρ : Representation k G V) (ρ' : Representation k G W) (N : Subgroup G) [Fintype N]
    (hpair : ∑ n : N, ρ.character n * ρ'.character ↑n⁻¹ = 0) :
    norm ((linHom ρ' ρ).comp N.subtype) = 0 := by
  have hN : (Nat.card N : k) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  let : Invertible (Nat.card N : k) := invertibleOfNonzero hN
  -- `σN` is the action of `N` on `W →ₗ[k] V` by conjugation.
  let σN : Representation k N (W →ₗ[k] V) := (linHom ρ' ρ).comp N.subtype
  -- The restrictions to `N` are orthogonal, so `σN` has no nonzero invariants: the character of
  -- `σN` at `n` is `χ'(n⁻¹) χ(n)` (`Representation.character_linHom`).
  have hinv : σN.invariants = ⊥ := by
    have h := card_inv_mul_sum_char_eq_finrank σN
    have h0 : ∑ n : N, σN.character n = 0 := by
      simpa only [σN, character_comp, Function.comp_apply, Subgroup.subtype_apply,
        character_linHom, mul_comm (ρ'.character _), Subgroup.coe_inv] using hpair
    rw [h0, mul_zero, eq_comm, Nat.cast_eq_zero] at h
    exact Submodule.finrank_eq_zero.mp h
  -- So the group sum `S` of `σN`, whose values are `N`-invariant, vanishes.
  refine LinearMap.ext fun f => ?_
  have hf : σN.norm f ∈ σN.invariants := (mem_invariants σN _).mpr fun n => σN.self_norm_apply n f
  simpa only [hinv, Submodule.mem_bot, LinearMap.zero_apply] using hf

/-- **Orthogonality on `N` is orthogonality on every coset of `N`**: over a field of
characteristic zero, `∑ n ∈ N, χ(g n) χ'((g n)⁻¹) = 0` for every `g ∈ G` if and only if
`∑ n ∈ N, χ(n) χ'(n⁻¹) = 0`, where `χ` and `χ'` are the characters of `ρ` and `ρ'`. The subgroup
`N` need not be normal and the spaces `V` and `W` need not be finite-dimensional. -/
theorem forall_sum_character_mul_mul_character_mul_inv_eq_zero_iff (ρ : Representation k G V)
    (ρ' : Representation k G W) (N : Subgroup G) [Fintype N] :
    (∀ g : G, ∑ n : N, ρ.character (g * n) * ρ'.character (g * n)⁻¹ = 0) ↔
      ∑ n : N, ρ.character n * ρ'.character ↑n⁻¹ = 0 := by
  refine ⟨fun h => by simpa only [one_mul, Subgroup.coe_inv] using h 1, fun hpair g => ?_⟩
  -- The coset sum is the trace of `σ g ∘ S`, with `S = 0` when `W →ₗ[k] V` is
  -- finite-dimensional; otherwise every trace on `W →ₗ[k] V` is `0`.
  have htr := ρ.sum_character_mul_mul_character_mul_inv_eq_trace ρ' N.subtype g
  simp only [Subgroup.subtype_apply] at htr
  rw [htr]
  by_cases hHom : Module.Finite k (W →ₗ[k] V)
  · rw [norm_comp_subtype_linHom_eq_zero ρ ρ' N hpair, mul_zero, map_zero]
  · rw [TauCeti.LinearMap.trace_eq_zero_of_not_finite hHom, LinearMap.zero_apply]

/-- **Characters restricting to distinct irreducible characters of `N` are orthogonal on every
coset of `N`**: over a field of characteristic zero, if the restrictions to `N` of the characters
`χ` and `χ'` of `ρ` and `ρ'` are distinct irreducible characters of `N`, then
`∑ n ∈ N, χ(g n) χ'((g n)⁻¹) = 0` for every `g ∈ G`. The field `k` need not be algebraically
closed, and the spaces `V` and `W` need not be assumed finite-dimensional. -/
theorem sum_character_mul_mul_character_mul_inv_eq_zero (ρ : Representation k G V)
    (ρ' : Representation k G W) (N : Subgroup G) [Fintype N]
    (hθ : (fun n : N => ρ.character n) ∈ TauCeti.irreducibleCharacters k N)
    (hθ' : (fun n : N => ρ'.character n) ∈ TauCeti.irreducibleCharacters k N)
    (hne : (fun n : N => ρ.character n) ≠ fun n : N => ρ'.character n) (g : G) :
    ∑ n : N, ρ.character (g * n) * ρ'.character (g * n)⁻¹ = 0 :=
  (forall_sum_character_mul_mul_character_mul_inv_eq_zero_iff ρ ρ' N).mpr
    (TauCeti.sum_mul_inv_eq_zero_of_mem_irreducibleCharacters hθ hθ' hne) g

end Representation
