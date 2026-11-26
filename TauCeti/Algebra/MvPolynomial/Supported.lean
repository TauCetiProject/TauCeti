/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Supported
import Mathlib.RingTheory.Adjoin.Basic

/-!
# Multivariate polynomials supported on a set of variables

A polynomial in `MvPolynomial.supported R s` is a linear combination of the monomials in the
variables of `s`, so two linear maps agree on it once they agree on these monomials
(`MvPolynomial.linearMap_eqOn_supported`). This is the linear analogue of
`MvPolynomial.derivation_eqOn_supported`.

For an `R`-algebra `B`, `MvPolynomial σ B` is also generated as an `R`-algebra by the base
constants `C b` and the polynomial variables `X i`
(`TauCeti.MvPolynomial.adjoin_range_C_union_range_X`).

## Main results

* `MvPolynomial.linearMap_eqOn_supported`: linear maps agreeing on monomials in `s` agree on
  `MvPolynomial.supported R s`.
* `TauCeti.MvPolynomial.adjoin_range_C_union_range_X`: `MvPolynomial σ B` is generated as an
  `R`-algebra by base constants and variables.
-/

public section

namespace MvPolynomial

variable {σ R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- Two linear maps out of `MvPolynomial σ R` agree on the polynomials in the variables of `s`
once they agree on the monomials with coefficient `1` in these variables. -/
theorem linearMap_eqOn_supported {s : Set σ} {f g : MvPolynomial σ R →ₗ[R] M}
    (h : ∀ m : σ →₀ ℕ, ↑m.support ⊆ s → f (monomial m 1) = g (monomial m 1)) :
    Set.EqOn f g (supported R s) := by
  intro p hp
  rw [SetLike.mem_coe, mem_supported] at hp
  rw [p.as_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [← mul_one (p.coeff m), ← smul_eq_mul, ← smul_monomial, map_smul, map_smul,
    h m fun i hi ↦ hp (support_subset_vars_of_mem_support hm hi)]

end MvPolynomial

namespace TauCeti.MvPolynomial

/-- `MvPolynomial σ B` is generated as an `R`-algebra by base constants `C b` and polynomial
variables `X i`. -/
theorem adjoin_range_C_union_range_X (R B σ : Type*) [CommSemiring R] [CommSemiring B]
    [Algebra R B] :
    Algebra.adjoin R
        (Set.range (_root_.MvPolynomial.C : B → _root_.MvPolynomial σ B) ∪
          Set.range _root_.MvPolynomial.X) =
      ⊤ := by
  ext p
  simp only [Algebra.mem_top, iff_true]
  induction p using _root_.MvPolynomial.induction_on with
  | C b => exact Algebra.subset_adjoin (Or.inl ⟨b, rfl⟩)
  | add p q hp hq => exact add_mem hp hq
  | mul_X p i hp => exact mul_mem hp (Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩))

end TauCeti.MvPolynomial
