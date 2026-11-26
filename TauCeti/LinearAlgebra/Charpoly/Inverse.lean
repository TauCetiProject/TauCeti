/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic.ComputeDegree
import TauCeti.Algebra.Polynomial.Reverse
import TauCeti.LinearAlgebra.Charpoly.FinrankTwo

/-!
# The characteristic polynomial of an inverse endomorphism

Let `f` and `g` be endomorphisms of a finite free module `M` of rank `d` over a commutative ring
with `g * f = 1`, so that `g` is the inverse of `f`. The characteristic polynomial of `g` is, up
to the unit `(-1) ^ d * det g`, the reverse `det (1 - X f)` of that of `f`:

  `det (X - g) = (-1) ^ d * det g * X ^ d * det (X⁻¹ - f)`.

This is the basis-free form of Mathlib's `Matrix.charpoly_inv`. Consequently, in any field `S`
over the ring of coefficients, the characteristic roots of `g` are the inverses of those of `f`,
counted with algebraic multiplicity; no splitting hypothesis is needed, and `0` is a root of
neither polynomial because `f` and `g` are invertible. In rank two, the inverse of an
endomorphism with characteristic polynomial `X ^ 2 - a X + q` has characteristic polynomial
`X ^ 2 - (a / q) X + 1 / q`.

These are the statements relating an arithmetic Frobenius and its inverse, the geometric
Frobenius: their eigenvalues are inverse to each other, with multiplicities.

## Main results

* `LinearMap.charpoly_of_mul_eq_one`: if `g * f = 1`, then
  `g.charpoly = (-1) ^ d * C (det g) * f.charpoly.reverse`.
* `LinearMap.isUnit_coeff_zero_charpoly_iff`: the constant coefficient of the characteristic
  polynomial is a unit if and only if the determinant is.
* `LinearMap.aroots_charpoly_of_mul_eq_one`: if `g * f = 1`, then the characteristic roots of `g`
  in a field `S` are the inverses of those of `f`.
* `LinearMap.charpoly_of_mul_eq_one_of_finrank_eq_two`,
  `LinearMap.charpoly_of_mul_eq_one_of_charpoly_eq`: the rank-two formula.

## References

* P. Deligne, *La conjecture de Weil. I*, Publ. Math. IHÉS 43 (1974), (1.5.1).
-/

public section

open Module Polynomial

namespace LinearMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M]
  [Module.Finite R M] {f g : Module.End R M}

/-- The characteristic polynomial of the inverse `g` of an endomorphism `f` of a finite free
module of rank `d` is `(-1) ^ d * det g` times the reverse `det (1 - X f)` of the characteristic
polynomial of `f`. -/
theorem charpoly_of_mul_eq_one (h : g * f = 1) :
    g.charpoly = (-1) ^ finrank R M * C (LinearMap.det g) * f.charpoly.reverse := by
  nontriviality R
  let b := Module.Free.chooseBasis R M
  have hgf : toMatrix b b g * toMatrix b b f = 1 := by
    rw [← toMatrix_mul, h, toMatrix_one]
  have hinv : (toMatrix b b f)⁻¹ = toMatrix b b g := Matrix.inv_eq_left_inv hgf
  rw [← charpoly_toMatrix g b, ← charpoly_toMatrix f b, ← hinv,
    Matrix.charpoly_inv _ (.of_mul_eq_one_right _ hgf),
    ← Matrix.det_nonsing_inv, hinv, det_toMatrix, Matrix.reverse_charpoly,
    finrank_eq_card_chooseBasisIndex]

/-- The constant coefficient of the characteristic polynomial of an endomorphism of a finite free
module is a unit exactly when its determinant is: they differ by the sign `(-1) ^ finrank`. -/
theorem isUnit_coeff_zero_charpoly_iff :
    IsUnit (f.charpoly.coeff 0) ↔ IsUnit (LinearMap.det f) := by
  nontriviality R
  rw [det_eq_sign_charpoly_coeff, IsUnit.mul_iff, and_iff_right (isUnit_neg_one.pow _)]

/-- **The characteristic roots of an inverse.** If `g * f = 1` for endomorphisms of a finite free
module, then the characteristic roots of `g` in a field `S` are the inverses of those of `f`,
counted with algebraic multiplicity. -/
theorem aroots_charpoly_of_mul_eq_one {S : Type*} [Field S] [Algebra R S] (h : g * f = 1) :
    g.charpoly.aroots S = (f.charpoly.aroots S).map (·⁻¹) := by
  have hdet : LinearMap.det g * LinearMap.det f = 1 := by rw [← map_mul, h, map_one]
  have hc : algebraMap R S ((-1) ^ finrank R M * LinearMap.det g) ≠ 0 :=
    (((isUnit_neg_one.pow _).mul (.of_mul_eq_one _ hdet)).map _).ne_zero
  -- Over `S`, the characteristic polynomial of `g` is a nonzero constant times the reverse of
  -- that of `f`, and reversal turns each nonzero root into its inverse.
  have hg : g.charpoly.aroots S = (f.charpoly.reverse.map (algebraMap R S)).roots := by
    rw [aroots, charpoly_of_mul_eq_one h, ← C_1, ← C_neg, ← C_pow, ← C_mul, Polynomial.map_mul,
      map_C, roots_C_mul _ hc]
  classical
  refine Multiset.ext' fun a ↦ ?_
  obtain ⟨a, rfl⟩ : ∃ b : S, a = b⁻¹ := ⟨a⁻¹, (inv_inv a).symm⟩
  rw [hg, Multiset.count_map_eq_count' _ _ inv_injective, aroots, count_roots, count_roots]
  rcases eq_or_ne a 0 with rfl | ha
  · -- `0` is a root of neither polynomial: `f` is invertible and its characteristic polynomial
    -- is monic.
    have hmonic := (charpoly_monic f).map (algebraMap R S)
    rw [inv_zero, rootMultiplicity_map_reverse_zero _ _ hmonic.ne_zero,
      (charpoly_monic f).natDegree_map, Nat.sub_self]
    refine (rootMultiplicity_eq_zero ?_).symm
    rw [IsRoot.def, ← coeff_zero_eq_eval_zero, coeff_map]
    exact ((isUnit_coeff_zero_charpoly_iff.2 (.of_mul_eq_one_right _ hdet)).map _).ne_zero
  · simpa using rootMultiplicity_map_reverse f.charpoly (algebraMap R S) (Units.mk0 a ha)

/-- **The inverse in rank two.** If `g` is the inverse of an endomorphism `f` of a free module of
rank two, then `g` has characteristic polynomial `X ^ 2 - tr(f) det(g) X + det(g)`. -/
theorem charpoly_of_mul_eq_one_of_finrank_eq_two (h2 : finrank R M = 2) (h : g * f = 1) :
    g.charpoly = X ^ 2 - C (trace R M f * LinearMap.det g) * X + C (LinearMap.det g) := by
  nontriviality R
  have hdet : LinearMap.det g * LinearMap.det f = 1 := by rw [← map_mul, h, map_one]
  -- Multiplying the Cayley–Hamilton identity `f ^ 2 - tr(f) f + det(f) = 0` by `g` gives
  -- `f - tr(f) + det(f) g = 0`, so `g = det(g) (tr(f) - f)`.
  have hCH := aeval_self_charpoly f
  rw [charpoly_of_finrank_eq_two h2] at hCH
  simp only [map_add, map_sub, map_pow, map_mul, aeval_X, aeval_C,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] at hCH
  have hg : g = LinearMap.det g • (trace R M f • 1 - f) := by
    have := congrArg (fun x ↦ LinearMap.det g • (g * x)) hCH
    simp only [mul_add, mul_sub, mul_smul_comm, pow_two, ← mul_assoc, h, one_mul, mul_one,
      smul_add, smul_sub, smul_smul, hdet, one_smul, mul_zero, smul_zero] at this
    rw [smul_sub, smul_smul, eq_sub_iff_add_eq, ← sub_eq_zero, ← this]
    abel
  have htr : trace R M g = trace R M f * LinearMap.det g := by
    conv_lhs => rw [hg]
    rw [map_smul, map_sub, map_smul, trace_one, h2, smul_eq_mul, smul_eq_mul]
    ring
  rw [charpoly_of_finrank_eq_two h2 g, htr]

/-- **The inverse in rank two.** If an endomorphism `f` of a vector space has characteristic
polynomial `X ^ 2 - a X + q`, then its inverse has characteristic polynomial
`X ^ 2 - (a / q) X + 1 / q`. -/
theorem charpoly_of_mul_eq_one_of_charpoly_eq {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {f g : Module.End K V} {a q : K}
    (hf : f.charpoly = X ^ 2 - C a * X + C q) (h : g * f = 1) :
    g.charpoly = X ^ 2 - C (a / q) * X + C q⁻¹ := by
  have h2 : finrank K V = 2 := by
    rw [← charpoly_natDegree, hf]
    compute_degree!
  have hf' := hf
  rw [charpoly_of_finrank_eq_two h2] at hf'
  have ha : trace K V f = a := by simpa using congrArg (fun p : K[X] ↦ p.coeff 1) hf'
  have hq : LinearMap.det f = q := by simpa using congrArg (fun p : K[X] ↦ p.coeff 0) hf'
  have hdet : LinearMap.det g = q⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← hq, ← map_mul, h, map_one])
  rw [charpoly_of_mul_eq_one_of_finrank_eq_two h2 h, ha, hdet, div_eq_mul_inv]

end LinearMap
