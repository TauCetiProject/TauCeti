/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Coefficient vectors under variable embeddings

The embedding `Polynomial.toMvPolynomial i` reindexes the native coefficient vector
by sending an exponent `n` to the multivariate exponent `Finsupp.single i n`.
This description lets coefficient constructions commute with placement in one coordinate.
Injective variable renaming similarly reindexes the multivariate coefficient vector.
-/

public section

namespace Polynomial

variable {R σ : Type*} [CommSemiring R]

/-- Placement in one coordinate reindexes the native coefficient vector by the
corresponding single-coordinate exponent embedding. -/
theorem coeff_toMvPolynomial_eq_embDomain (p : Polynomial R) (i : σ) :
    AddMonoidAlgebra.coeff (p.toMvPolynomial i) =
      p.toFinsupp.coeff.embDomain ⟨Finsupp.single i, Finsupp.single_injective i⟩ := by
  classical
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [_root_.map_add, AddMonoidAlgebra.coeff_add, Polynomial.toFinsupp_add,
      Finsupp.embDomain_add, hp, hq]
  | monomial n c =>
    simp [← Polynomial.C_mul_X_pow_eq_monomial, MvPolynomial.C_mul_X_pow_eq_monomial,
      ← MvPolynomial.single_eq_monomial,
      AddMonoidAlgebra.coeff_single, Finsupp.embDomain_single]

end Polynomial

namespace MvPolynomial

variable {R σ τ : Type*} [CommSemiring R]

/-- Injective variable renaming reindexes the native coefficient vector by the induced
embedding of exponent vectors. -/
theorem coeff_rename_eq_embDomain (p : MvPolynomial σ R) {f : σ → τ}
    (hf : Function.Injective f) :
    AddMonoidAlgebra.coeff (rename f p) =
      (AddMonoidAlgebra.coeff p).embDomain
        ⟨Finsupp.mapDomain f, Finsupp.mapDomain_injective hf⟩ := by
  classical
  let e : (σ →₀ ℕ) ↪ (τ →₀ ℕ) :=
    ⟨Finsupp.mapDomain f, Finsupp.mapDomain_injective hf⟩
  ext d
  by_cases hd : ∃ a, e a = d
  · obtain ⟨a, rfl⟩ := hd
    rw [Finsupp.embDomain_apply_self]
    -- Since `MvPolynomial` abbreviates `AddMonoidAlgebra`, `.coeff` is its native coefficient
    -- evaluation, and `e a` reduces to `a.mapDomain f`. Expose this form to apply
    -- `coeff_rename_embDomain`.
    change (rename f p).coeff (a.mapDomain f) = p.coeff a
    simpa only [Finsupp.embDomain_eq_mapDomain, Function.Embedding.coeFn_mk] using
      coeff_rename_embDomain ⟨f, hf⟩ p a
  · rw [Finsupp.embDomain_of_notMem_range e _ d hd]
    exact coeff_rename_eq_zero f p d (fun a ha ↦ (hd ⟨a, ha⟩).elim)

end MvPolynomial
