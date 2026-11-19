/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import TauCeti.RingTheory.FormalGroup.LazardRing.Hurewicz
-- Proof-only: renaming variables, weights and leading monomials.
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import TauCeti.RingTheory.MvPolynomial.MonomialOrder

/-!
# The generators of the Lazard ring are algebraically independent

The generators `xₙ ∈ L₂ₙ` of the indecomposables of the Lazard ring `L`
(`TauCeti.LazardRing.generator`) are algebraically independent over `ℤ`: the homomorphism
`ℤ[x₁, x₂, …] → L` sending `xₙ` to the generator `xₙ` is injective. This is the integral
independence half of Lazard's theorem that `L` is the polynomial ring `ℤ[x₁, x₂, …]`.

The proof maps `L` to `ℤ[b₁, b₂, …]` by the Hurewicz homomorphism `TauCeti.LazardRing.hurewicz`,
which classifies the additive formal group law transported along the strict coordinate
`X + ∑ bᵢ X^(i + 1)`. Giving `bᵢ` the degree `2i`, it is graded, and the image of `xₙ` has
coefficient `d_{n+1} ≠ 0` at `bₙ` (`TauCeti.LazardRing.coeff_single_hurewicz_generator`).

A polynomial of degree `2n` is a combination of `bₙ` and of monomials in `b₁, …, bₙ₋₁`, so for the
lexicographic order in which variables of larger index are more significant the leading monomial
of the image of `xₙ` is `bₙ`. Polynomials with distinct leading variables are algebraically
independent (`MonomialOrder.algebraicIndependent_of_degree_eq_single`), hence so are the images of
the `xₙ`, and the `xₙ` themselves.

## Main results

* `TauCeti.LazardRing.algebraicIndependent_hurewicz_generator`: the images of the generators `xₙ`
  under the Hurewicz homomorphism are algebraically independent over `ℤ`.
* `TauCeti.LazardRing.algebraicIndependent_generator`: the generators `xₙ` of the Lazard ring are
  algebraically independent over `ℤ`.

## References

* M. Lazard, *Sur les groupes de Lie formels à un paramètre*, Bull. Soc. Math. France 83 (1955).
* J. F. Adams, *Stable Homotopy and Generalised Homology*, Part II, §7.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A2.1
  (Lazard's theorem A2.1.8).
-/

public section

noncomputable section

open Finsupp OrderDual

namespace TauCeti.LazardRing

/-- The Hurewicz homomorphism `L →+* ℤ[b₁, b₂, …]` with its variables indexed by `ℕ+ᵒᵈ`, so that
the lexicographic monomial order makes the variables of larger index more significant. -/
private abbrev ρ : LazardRing →+* MvPolynomial ℕ+ᵒᵈ ℤ :=
  (MvPolynomial.rename toDual).toRingHom.comp hurewicz

/-- The degree `2i` of the variable `bᵢ`. -/
private abbrev weight : ℕ+ᵒᵈ → ℕ := fun i ↦ 2 * ((ofDual i : ℕ+) : ℕ)

/-! ### The leading monomial of `ρ(xₙ)` -/

/-- A monomial of degree `2n` is `bₙ` or lexicographically smaller than `bₙ`: it only involves
the variables `bᵢ` with `i ≤ n`, and `bₙ` only as the monomial `bₙ` itself. -/
private theorem toLex_le_single_of_weight_eq {n : ℕ+} {d : ℕ+ᵒᵈ →₀ ℕ}
    (hd : Finsupp.weight weight d = 2 * n) : toLex d ≤ toLex (single (toDual n) 1) := by
  by_cases hn : d (toDual n) = 0
  · -- `d` does not involve `bₙ`, nor any `bᵢ` with `i > n`, which would have degree `> 2n`.
    refine le_of_lt (Finsupp.Lex.lt_iff.2 ⟨toDual n, fun j hj ↦ ?_, ?_⟩)
    · have hj' : n < ofDual j := hj
      have hdj : d j = 0 := by
        by_contra hdj
        have := le_weight_of_ne_zero' weight hdj
        simp only [weight] at this
        have : (n : ℕ) < ofDual j := hj'
        omega
      simp [hdj, hj.ne']
    · simp [hn]
  · -- `d - bₙ` has degree `0`, so it is `0`.
    have hsub : d - single (toDual n) 1 = 0 := by
      ext j
      by_contra hj
      have h1 := le_weight_of_ne_zero' weight hj
      have h2 := weight_sub_single_add (w := weight) hn
      simp only [weight, ofDual_toDual] at h1 h2
      have := (ofDual j).pos
      simp only [coe_zero, Pi.zero_apply] at hj
      omega
    rw [← sub_add_single_one_cancel hn, hsub, zero_add]

/-- The leading monomial of `ρ(xₙ)` is `bₙ`. -/
private theorem degree_ρ_generator (n : ℕ+) :
    MonomialOrder.lex.degree (ρ (generator n)) = single (toDual n) 1 := by
  classical
  have hp := isWeightedHomogeneous_hurewicz (generator_mem_grading n)
  -- The coefficient of `bₙ` in `ρ(xₙ)` is `d_{n+1} ≠ 0`.
  have hc : (ρ (generator n)).coeff (single (toDual n) 1) ≠ 0 := by
    rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← Finsupp.mapDomain_single,
      MvPolynomial.coeff_rename_mapDomain _ toDual.injective, coeff_single_hurewicz_generator,
      ite_eq_left rfl]
    exact Nat.cast_ne_zero.2 (lazardGcd_succ_ne_zero n.ne_zero)
  refine MonomialOrder.lex.toSyn.injective (le_antisymm ?_ ?_)
  · -- Every monomial of `ρ(xₙ)` is the renaming of a monomial of degree `2n`.
    refine MonomialOrder.lex.degree_le_iff.2 fun d hd ↦ ?_
    rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      MvPolynomial.support_rename_of_injective toDual.injective, Finset.mem_image] at hd
    obtain ⟨e, he, rfl⟩ := hd
    refine MonomialOrder.lex_le_iff.2 (toLex_le_single_of_weight_eq ?_)
    rw [← hp (MvPolynomial.mem_support_iff.1 he), Finsupp.weight_apply, Finsupp.weight_apply,
      Finsupp.sum_mapDomain_index (h := fun i c ↦ c • weight i) (fun _ ↦ zero_smul ℕ _)
        fun _ _ _ ↦ add_smul _ _ _]
    simp [weight]
  · exact MonomialOrder.lex.le_degree (MvPolynomial.mem_support_iff.2 hc)

/-- The images `hurewicz xₙ ∈ ℤ[b₁, b₂, …]` of the generators of the Lazard ring are algebraically
independent over `ℤ`. -/
theorem algebraicIndependent_hurewicz_generator :
    AlgebraicIndependent ℤ (hurewicz ∘ generator) := by
  have h : AlgebraicIndependent ℤ fun i : ℕ+ᵒᵈ ↦ ρ (generator (ofDual i)) :=
    MonomialOrder.lex.algebraicIndependent_of_degree_eq_single fun i ↦ degree_ρ_generator _
  -- Undo the renaming of the variables.
  have h' := h.map' (f := MvPolynomial.rename ofDual)
    (MvPolynomial.rename_injective _ ofDual.injective)
  have hcomp : ⇑(MvPolynomial.rename (R := ℤ) ofDual) ∘
      (fun i : ℕ+ᵒᵈ ↦ ρ (generator (ofDual i))) = (hurewicz ∘ generator) ∘ ofDual := by
    funext i
    simp [MvPolynomial.rename_rename]
  rw [hcomp] at h'
  exact (algebraicIndependent_equiv ofDual).1 h'

/-- **Lazard's theorem, integral independence**: the generators `xₙ ∈ L₂ₙ` of the Lazard ring are
algebraically independent over `ℤ`, that is, the homomorphism `ℤ[x₁, x₂, …] → L` sending `xₙ` to
`TauCeti.LazardRing.generator n` is injective. -/
theorem algebraicIndependent_generator : AlgebraicIndependent ℤ generator :=
  algebraicIndependent_hurewicz_generator.of_comp hurewicz.toIntAlgHom

end TauCeti.LazardRing
