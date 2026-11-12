/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Regular.QuasiRegular
public import TauCeti.RingTheory.RegularLocalRing.Basic
import Mathlib.RingTheory.Polynomial.Basic
import TauCeti.Algebra.Module.SpanRank
import TauCeti.RingTheory.Regular.RegularSequence
import TauCeti.RingTheory.RegularLocalRing.CohenMacaulay

/-!
# The associated graded ring of a regular local ring

Let `(R, 𝔪)` be a regular local ring with residue field `κ = R ⧸ 𝔪`, and let `x₁, …, x_d` be a
regular system of parameters: `d = spanFinrank 𝔪` elements generating `𝔪`. The `κ`-algebra
homomorphism `κ[X₁, …, X_d] → gr_𝔪 R = ⨁ₙ 𝔪ⁿ ⧸ 𝔪ⁿ⁺¹` sending `X i` to the class of `xᵢ` in degree
one is an isomorphism; it sends the class of a homogeneous polynomial `F` of degree `n` with
coefficients in `R` to the class of `F(x₁, …, x_d)` in degree `n`
(`Ideal.AssociatedGraded.ofMvPolynomial_map_of_isHomogeneous`). Hence `gr_𝔪 R` is a domain, and
initial forms multiply: if `f ∈ 𝔪ᵃ \ 𝔪ᵃ⁺¹` and `g ∈ 𝔪ᵇ \ 𝔪ᵇ⁺¹`, then `f g ∉ 𝔪ᵃ⁺ᵇ⁺¹`. This is
the input for the additivity of the `𝔪`-adic order on a regular local ring.

No equicharacteristic hypothesis and no coefficient field are needed: for `R = ℤ_(p)` the
associated graded ring is `𝔽_p[T]`, with `T` the class of `p` in degree one.

## Main results

* `TauCeti.IsRegularLocalRing.associatedGradedEquiv`: `κ[X₁, …, X_d] ≃ₐ[κ] gr_𝔪 R` for a regular
  system of parameters `x₁, …, x_d`.
* `TauCeti.IsRegularLocalRing.isDomain_associatedGraded`: `gr_𝔪 R` is a domain.
* `TauCeti.IsRegularLocalRing.mul_notMem_maximalIdeal_pow_succ`: initial forms multiply.

## Implementation notes

A regular system of parameters is a regular sequence
(`TauCeti.IsRegularLocalRing.isRegular_of_ofList_eq_maximalIdeal`), and regular sequences are
quasi-regular (`RingTheory.Sequence.IsWeaklyRegular.coeff_mem_of_eval_mem_pow_succ`). This avoids
Hilbert–Samuel polynomials.

## References

* H. Matsumura, *Commutative Ring Theory*, Theorem 14.4.
* [The Stacks Project, Lemma 00NO](https://stacks.math.columbia.edu/tag/00NO)
-/

public section

open IsLocalRing Ideal

namespace TauCeti.IsRegularLocalRing

variable {R : Type*} [CommRing R] [IsRegularLocalRing R]

/-- **The associated graded ring of a regular local ring is a polynomial ring.** For a regular
system of parameters `x₁, …, x_d` of a regular local ring `(R, 𝔪)`, the residue-field algebra
isomorphism `(R ⧸ 𝔪)[X₁, …, X_d] ≃ gr_𝔪 R` sending `X i` to the class of `xᵢ` in degree one. -/
noncomputable def associatedGradedEquiv {n : ℕ} {x : Fin n → R}
    (hx : span (Set.range x) = maximalIdeal R) (hn : n ≤ (maximalIdeal R).spanFinrank) :
    MvPolynomial (Fin n) (R ⧸ maximalIdeal R) ≃ₐ[R ⧸ maximalIdeal R]
      (maximalIdeal R).AssociatedGraded :=
  AssociatedGraded.ofMvPolynomialEquiv
    (isRegular_of_ofList_eq_maximalIdeal (by rwa [ofList_ofFn]) (by simpa using hn)).1
    (fun i ↦ hx ▸ subset_span ⟨i, rfl⟩) hx.ge

/-- `associatedGradedEquiv` sends `X i` to the class of the parameter `xᵢ` in degree one. -/
@[simp]
theorem associatedGradedEquiv_X {n : ℕ} {x : Fin n → R}
    (hx : span (Set.range x) = maximalIdeal R) (hn : n ≤ (maximalIdeal R).spanFinrank)
    (i : Fin n) :
    associatedGradedEquiv hx hn (MvPolynomial.X i) =
      AssociatedGraded.mk (maximalIdeal R) 1
        ⟨x i, by rw [pow_one, ← hx]; exact subset_span ⟨i, rfl⟩⟩ := by
  rw [associatedGradedEquiv, AssociatedGraded.coe_ofMvPolynomialEquiv,
    AssociatedGraded.ofMvPolynomial_X]

/-- The associated graded ring `gr_𝔪 R` of a regular local ring is a domain. -/
instance isDomain_associatedGraded : IsDomain (maximalIdeal R).AssociatedGraded := by
  obtain ⟨x, hx⟩ := (Submodule.FG.spanFinrank_le_iff_exists_fin_generating_family
    (IsNoetherian.noetherian (maximalIdeal R)) _).1 le_rfl
  exact MulEquiv.isDomain _ (associatedGradedEquiv hx le_rfl).symm.toMulEquiv

/-- **Initial forms multiply in a regular local ring.** If `f ∈ 𝔪ᵃ \ 𝔪ᵃ⁺¹` and
`g ∈ 𝔪ᵇ \ 𝔪ᵇ⁺¹`, then `f g ∉ 𝔪ᵃ⁺ᵇ⁺¹`. -/
theorem mul_notMem_maximalIdeal_pow_succ {f g : R} {a b : ℕ} (hf : f ∈ maximalIdeal R ^ a)
    (hf' : f ∉ maximalIdeal R ^ (a + 1)) (hg : g ∈ maximalIdeal R ^ b)
    (hg' : g ∉ maximalIdeal R ^ (b + 1)) :
    f * g ∉ maximalIdeal R ^ (a + b + 1) := by
  have hfg := mul_ne_zero ((AssociatedGraded.mk_eq_zero_iff ⟨f, hf⟩).not.2 hf')
    ((AssociatedGraded.mk_eq_zero_iff ⟨g, hg⟩).not.2 hg')
  rwa [AssociatedGraded.mk_mul_mk, Ne, AssociatedGraded.mk_eq_zero_iff] at hfg

end TauCeti.IsRegularLocalRing
