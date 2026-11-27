/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.TraceFunctional.Radical
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.LinearAlgebra.Matrix.Trace
public import TauCeti.RingTheory.MvPolynomial.Symmetric.PowerSum.IntegralNewton
import TauCeti.LinearAlgebra.Matrix.Charpoly.IntegralNewton
import TauCeti.LinearAlgebra.LinearIndependent.Evaluation
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Finite-dimensional trace quotients from polynomial trace identities

If a tracial linear form on an algebra satisfies every polynomial identity among traces of
algebra maps to matrices of a fixed finite size, its trace quotient is finite-dimensional.
Evaluation determinants detect independence in the quotient without requiring the original
algebra to be finite-dimensional. Over any commutative scalar ring, the integral Newton
identity also descends to every element of the trace quotient.

## Provenance

`LinearMap.finite_quotient_traceRadical_of_trace_identities` and
`LinearMap.eval_integralNewtonPolynomial_quotientTrace_eq_zero` adapt
`New.finite_quotient_pairingKernel` and the quotient Newton-vanishing step of
`New.exists_rep_of_trace_identities` in
`src/Lib/GaloisRep/Pseudocharacter/Pseudorepresentations.lean` in grh-lean
(https://github.com/lsernau/grh-lean, commit `72fead1`, Apache 2.0,
Copyright 2026 Anthropic, PBC). The formulation for arbitrary algebras is new here.

## References

* R. Taylor, *Galois representations associated to Siegel modular forms of low weight*,
  Duke Math. J. 63 (1991), Theorem 1.
* R. Rouquier, *Caractérisation des caractères et pseudo-caractères*, J. Algebra 180 (1996),
  571–586. https://www.math.ucla.edu/~rouquier/papers.html
-/

public section

open Matrix LinearMap Module Submodule Ideal.Quotient MvPolynomial

namespace LinearMap

/-- An algebra's quotient by the trace radical is finite-dimensional if the trace satisfies
all polynomial trace identities of matrices of a fixed finite size. -/
theorem finite_quotient_traceRadical_of_trace_identities
    {k A n : Type*} [Field k] [Ring A] [Algebra k A] [Fintype n] [DecidableEq n]
    (t : A →ₗ[k] k) (t_comm : ∀ x y, t (x * y) = t (y * x))
    (h_alg : ∀ B : MvPolynomial A k,
      (∀ ρ : A →ₐ[k] Matrix n n k, eval (fun x ↦ (ρ x).trace) B = 0) → eval t B = 0) :
    Module.Finite k (A ⧸ t.traceRadical t_comm) := by
  let N : ℕ := Fintype.card n * Fintype.card n + 1
  refine rank_lt_aleph0_iff.mp (not_le.mp fun h_inf ↦ ?_)
  obtain ⟨s, hs⟩ : ∃ s : Fin N → A,
      LinearIndependent k (Ideal.Quotient.mk (t.traceRadical t_comm) ∘ s) :=
    mk_surjective.comp_left.exists.mp (le_rank_iff.mp (Cardinal.aleph0_le.mp h_inf N))
  have h_ltoFun : LinearMap.ker (ltoFun k A k k) = ⊥ := by aesop
  have h_indep : LinearIndependent k fun (i : Fin N) (y : A) ↦ t (s i * y) :=
    (hs.map' _ (ker_liftQ_eq_bot' _ _ (t.traceRadical_restrictScalars_eq_ker t_comm))).map'
      (ltoFun k A k k) h_ltoFun
  have h_dep (ρ : A →ₐ[k] Matrix n n k) :
      ¬LinearIndependent k fun (i : Fin N) (A : Matrix n n k) ↦ (ρ (s i) * A).trace := by
    intro h
    have hle := (LinearIndependent.of_comp (v := fun i ↦ ρ (s i))
      (pi fun A ↦ traceLinearMap n k k ∘ₗ mulRight k A) h).fintype_card_le_finrank
    simp only [finrank_matrix, Module.finrank_self, mul_one, Fintype.card_fin] at hle
    omega
  refine TauCeti.det_eval_eq_zero_iff_not_linearIndependent.mp (fun b ↦ ?_) h_indep
  -- the minor `det (t (s i * b j))` is `t` at a polynomial that vanishes on traces
  have h_det_zero : eval t (of fun i j ↦ X (s i * b j) : Matrix (Fin N) (Fin N) _)ᵀ.det = 0 := by
    refine h_alg _ fun ρ ↦ ?_
    simpa [det_apply, Function.flip_def] using
      TauCeti.det_eval_eq_zero_iff_not_linearIndependent.mpr (h_dep ρ) (ρ ∘ b)
  simpa [det_apply, Function.flip_def] using h_det_zero

/-- Every element of the trace quotient satisfies the integral Newton identity of the given
matrix size when the original trace satisfies all polynomial trace identities of that size. -/
theorem eval_integralNewtonPolynomial_quotientTrace_eq_zero
    {k A n : Type*} [CommRing k] [Ring A] [Algebra k A] [Fintype n] [DecidableEq n]
    (t : A →ₗ[k] k) (t_comm : ∀ x y, t (x * y) = t (y * x))
    (h_alg : ∀ B : MvPolynomial A k,
      (∀ ρ : A →ₐ[k] Matrix n n k, eval (fun x ↦ (ρ x).trace) B = 0) → eval t B = 0)
    (x : A ⧸ t.traceRadical t_comm) :
    eval (fun i : ℕ ↦ t.quotientTrace t_comm (x ^ i))
      (TauCeti.integralNewtonPolynomial (Fintype.card n + 1) 1) = 0 := by
  obtain ⟨x, rfl⟩ := mk_surjective x
  have hz : eval t (rename (fun i : ℕ ↦ x ^ i)
      (TauCeti.integralNewtonPolynomial (Fintype.card n + 1) 1)) = 0 := by
    refine h_alg _ fun ρ ↦ ?_
    simpa [eval_rename, Function.comp_def] using
      (ρ x).eval_integralNewtonPolynomial_trace_pow_eq_zero
  simpa only [eval_rename, Function.comp_def, ← map_pow, quotientTrace_mk] using hz

end LinearMap
