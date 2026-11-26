/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.IsIntegral
public import TauCeti.FieldTheory.Minpoly.AlgHom

/-!
# Testing integrality on characters

Let `B` be a commutative integral algebra over an algebraically closed field `K`, and let
`R → K → B` be a scalar tower. An element `y : B` is integral over `R` exactly when every
`K`-algebra homomorphism `χ : B →ₐ[K] K` takes it to an element integral over `R`. If `R` is
integrally closed in `K`, this is equivalent to every `χ y` lying in the image of `R`.
The first criterion requires neither injectivity of `R → K` nor integral closedness.

Finite-dimensional algebras satisfy the integrality hypothesis by instance search. Reducedness
is unnecessary: the minimal polynomial retains the multiplicities that account for nilpotents.
Integrality of `y` alone over `K` would not suffice: `K(t)` has no `K`-valued characters.

For the resulting finite generation of powers, use Mathlib's `IsIntegral.fg_adjoin_singleton`:
`(Algebra.adjoin R {y}).toSubmodule` is finitely generated and contains every `y ^ n` by
`Subalgebra.pow_mem` and `Algebra.subset_adjoin`. More explicitly,
`Submodule.span_range_natDegree_eq_adjoin` identifies it with the span of the first
`(minpoly R y).natDegree` powers. The finite-span assertion is already in Mathlib.

The forward implications use only that homomorphisms preserve integrality
(`IsIntegral.map`), and, for the image criterion, that `R` is integrally closed in `K`.
They require neither algebraic closedness of `K` nor integrality of the whole algebra.

## References

* The Stacks Project, [Tag 00H6](https://stacks.math.columbia.edu/tag/00H6), for integrality of
  coefficients obtained from integral roots.
* L. Alpöge's formal Lean proof of the Riemann hypothesis for Dirichlet L-functions (2026),
  https://github.com/leanprover-community/riemann-hypothesis, uses this criterion to bound the
  powers of a functional on a finite Hopf algebra by its values at points. The criterion is
  standard, and the formalization here is independent of that source.
-/

public section

namespace TauCeti

open Polynomial

variable {R K B : Type*} [CommRing R] [Field K] [CommRing B]
  [Algebra R K] [Algebra K B] [Algebra R B] [IsScalarTower R K B]
  [IsAlgClosed K] [Algebra.IsIntegral K B]

/-- Integrality over a base ring can be tested on all scalar-valued characters of a commutative
integral algebra over an algebraically closed field. No injectivity of the base map is needed. -/
theorem isIntegral_iff_forall_isIntegral_algHom {y : B} :
    IsIntegral R y ↔ ∀ χ : B →ₐ[K] K, IsIntegral R (χ y) := by
  constructor
  · exact fun hy χ ↦ hy.map χ
  · intro h
    nontriviality B
    have hy := Algebra.IsIntegral.isIntegral (R := K) y
    have hc : ∀ i, IsIntegral R ((minpoly K y).coeff i) :=
      (minpoly K y).isIntegral_coeff_of_factors
        (by rw [(minpoly.monic hy).leadingCoeff]; exact isIntegral_one)
        (IsAlgClosed.splits _) (fun r hr ↦ by
          obtain ⟨χ, rfl⟩ := isRoot_minpoly_iff_exists_algHom.mp hr
          exact h χ)
    apply IsIntegral.of_aeval_monic_of_isIntegral_coeff
      ((minpoly.monic hy).map (algebraMap K B))
    · rw [natDegree_map]
      exact (minpoly.natDegree_pos hy).ne'
    · rw [eval_map_algebraMap, minpoly.aeval]
      exact isIntegral_zero
    · intro i
      rw [coeff_map]
      exact (hc i).map (IsScalarTower.toAlgHom R K B)

/-- Over a ring integrally closed in an algebraically closed field, an element of a commutative
integral algebra is integral exactly when every scalar-valued character takes it into the base
image. -/
theorem isIntegral_iff_forall_algHom_mem_range [IsIntegrallyClosedIn R K] {y : B} :
    IsIntegral R y ↔ ∀ χ : B →ₐ[K] K, χ y ∈ Set.range (algebraMap R K) := by
  rw [isIntegral_iff_forall_isIntegral_algHom (K := K)]
  exact forall_congr' fun χ ↦ IsIntegrallyClosedIn.isIntegral_iff

end TauCeti
