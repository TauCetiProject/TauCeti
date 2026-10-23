/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Symmetric.Complete.Basic
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.HsymmPart
import TauCeti.RingTheory.MvPolynomial.Homogeneous

/-!
# The Cauchy identity for Schur polynomials

For two finite alphabets `x = (xᵢ)_{i ∈ σ}` and `y = (yⱼ)_{j ∈ τ}`, the **Cauchy identity**

`∏_{i,j} (1 - xᵢ yⱼ t)⁻¹ = ∑_λ s_λ(x) s_λ(y) t^{|λ|}`

expands the product of the geometric series over all pairs of letters in the products of the
Schur polynomials of the two alphabets, the sum running over all partitions `λ`.  Its coefficient
of `tⁿ` says that the complete homogeneous symmetric polynomial `hₙ` in the products `xᵢ yⱼ` is
`∑_{λ ⊢ n} s_λ(x) s_λ(y)`.

Both forms are stated for the values of the Schur polynomials at arbitrary families `f : σ → S`
and `g : τ → S` in a commutative `R`-algebra `S`.  Taking for `S` the polynomial ring
`MvPolynomial (σ ⊕ τ) R`, with `f = X ∘ Sum.inl` and `g = X ∘ Sum.inr`, gives the identity of
polynomials in the two alphabets.

## The argument

Grouping the pairs `(i, j)` by their first letter, `hₙ(xy) = ∑_l ∏ᵢ xᵢ^{lᵢ} h_{lᵢ}(y)`, the sum
running over the exponent vectors `l` on `σ` of total degree `n`
(`TauCeti.aeval_hsymm_prod_eq_sum_finsuppAntidiag`).  The product `∏ᵢ h_{lᵢ}(y)` expands in the
Schur polynomials as `∑_λ K_{λ l} s_λ(y)`, and the Kostka number `K_{λ l}` is the coefficient of
`x^l` in `s_λ(x)` (`TauCeti.prod_hsymm_eq_sum_coeff_schurPoly_smul_schurPoly`).  Exchanging the two
sums leaves `∑_l K_{λ l} x^l` as the cofactor of `s_λ(y)`, and that is `s_λ(x)`, `s_λ` being
homogeneous of
degree `n` (`MvPolynomial.IsHomogeneous.aeval_eq_sum_finsuppAntidiag`).  Bijectively, the identity
is the Robinson--Schensted--Knuth correspondence between matrices of natural numbers and pairs of
semistandard tableaux of the same shape.

## Main results

* `TauCeti.sum_aeval_schurPoly_mul_aeval_schurPoly`: **the Cauchy identity in degree `n`**,
  `∑_{λ ⊢ n} s_λ(x) s_λ(y) = hₙ(xᵢ yⱼ)`.
* `TauCeti.mk_sum_aeval_schurPoly_mul_aeval_schurPoly`: **the Cauchy identity** as an identity of
  power series, `∑_λ s_λ(x) s_λ(y) t^{|λ|} = ∏_{i,j} ∑ₘ (xᵢ yⱼ)ᵐ tᵐ`.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 4, (4.3).
* R. P. Stanley, *Enumerative Combinatorics, Vol. 2*, Theorem 7.12.1.
-/

public section

namespace TauCeti

open MvPolynomial Finset

variable {σ τ R S : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
  [CommSemiring R] [CommSemiring S] [Algebra R S]

/-- **The Cauchy identity in degree `n`**: for families `f : σ → S` and `g : τ → S`,

`∑_{λ ⊢ n} s_λ(f) s_λ(g) = hₙ(fᵢ gⱼ)`,

the complete homogeneous symmetric polynomial `hₙ` in the alphabet `σ × τ` being evaluated at the
products `fᵢ gⱼ`.  This is the coefficient of `tⁿ` in `∏_{i,j} (1 - fᵢ gⱼ t)⁻¹`. -/
theorem sum_aeval_schurPoly_mul_aeval_schurPoly (f : σ → S) (g : τ → S) (n : ℕ) :
    ∑ μ : n.Partition, aeval f (schurPoly σ R μ) * aeval g (schurPoly τ R μ) =
      aeval (fun p : σ × τ => f p.1 * g p.2) (hsymm (σ × τ) R n) := by
  rw [aeval_hsymm_prod_eq_sum_finsuppAntidiag]
  have h (l : σ →₀ ℕ) (hl : l ∈ finsuppAntidiag univ n) :
      ∏ i, f i ^ l i * aeval g (hsymm τ R (l i)) = ∑ μ : n.Partition,
        algebraMap R S ((schurPoly σ R μ).coeff l) * (∏ i, f i ^ l i) *
          aeval g (schurPoly τ R μ) := by
    rw [prod_mul_distrib, ← map_prod, prod_hsymm_eq_sum_coeff_schurPoly_smul_schurPoly τ
      (by rw [Finsupp.degree_eq_sum, (mem_finsuppAntidiag.mp hl).1]),
      map_sum, mul_sum]
    refine sum_congr rfl fun μ _ => ?_
    rw [map_smul, Algebra.smul_def]
    ring
  simp only [sum_congr rfl h, (isHomogeneous_schurPoly _).aeval_eq_sum_finsuppAntidiag, sum_mul]
  exact sum_comm

omit [DecidableEq σ] [DecidableEq τ] in
/-- **The Cauchy identity**: for families `f : σ → S` and `g : τ → S`,

`∑_λ s_λ(f) s_λ(g) t^{|λ|} = ∏_{i,j} (1 - fᵢ gⱼ t)⁻¹`,

as power series over `S`, the coefficient of `tⁿ` on the left summing over the partitions `λ` of
`n`, and the factor `(1 - fᵢ gⱼ t)⁻¹` on the right written as the geometric series
`∑ₘ (fᵢ gⱼ)ᵐ tᵐ`. -/
theorem mk_sum_aeval_schurPoly_mul_aeval_schurPoly (f : σ → S) (g : τ → S) :
    PowerSeries.mk (fun n => ∑ μ : n.Partition,
        aeval f (schurPoly σ R μ) * aeval g (schurPoly τ R μ)) =
      ∏ i, ∏ j, PowerSeries.mk fun m => (f i * g j) ^ m := by
  classical
  simp only [sum_aeval_schurPoly_mul_aeval_schurPoly, mk_aeval_hsymm_eq_prod_mk_pow,
    Fintype.prod_prod_type]

end TauCeti
