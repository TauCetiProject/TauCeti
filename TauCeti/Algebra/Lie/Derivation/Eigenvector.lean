/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Derivation.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.RingTheory.Algebraic.Basic

/-!
# Algebraic eigenvectors of associative derivations

Over a characteristic-zero domain, an algebraic element of a torsion-free associative algebra
that is an eigenvector of a derivation with nonzero eigenvalue is nilpotent. Commutativity of
the algebra is not required. Indeed, its powers have eigenvalues `n * c`; if none vanishes,
their distinct eigenvalues make them linearly independent, contradicting a polynomial relation.

Applied to inner derivations of endomorphism algebras, this gives the nilpotence of the
operator representing `x` whenever `⁅y, x⁆ = c • x` with `c ≠ 0`. In particular it converts
a bracket relation into nilpotence without extending the coefficient field.

## Main results

* `TauCeti.derivationLieAlgebra.apply_pow_of_apply_eq_smul`: powers of an eigenvector of a
  derivation have eigenvalues multiplied by their exponents.
* `TauCeti.derivationLieAlgebra.isNilpotent_of_isAlgebraic_of_apply_eq_smul`: an algebraic
  eigenvector with nonzero eigenvalue is nilpotent in characteristic zero.

## References

* G. Hochschild, *An Addition to Ado's Theorem*, Proc. Amer. Math. Soc. **17** (1966), 531–533,
  for the use of bracket relations to prove nilpotence in finite-dimensional representations.
-/

public section

namespace TauCeti.derivationLieAlgebra

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- If a derivation acts on `x` by the scalar `c`, it acts on `xⁿ` by `n * c`. -/
theorem apply_pow_of_apply_eq_smul (D : derivationLieAlgebra R A) {x : A} {c : R}
    (hx : (D : Module.End R A) x = c • x) (n : ℕ) :
    (D : Module.End R A) (x ^ n) = (n * c) • x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, leibniz, ih, hx, smul_mul_assoc, mul_smul_comm, ← add_smul]
    congr 1
    simp [add_mul]

/-- Over a characteristic-zero domain, an algebraic eigenvector of a derivation with nonzero
eigenvalue in a torsion-free algebra is nilpotent. Only the element needs to be algebraic;
the ambient algebra may be infinite dimensional. -/
theorem isNilpotent_of_isAlgebraic_of_apply_eq_smul [IsDomain R] [CharZero R]
    [Module.IsTorsionFree R A] (D : derivationLieAlgebra R A) {x : A} {c : R}
    (hx : IsAlgebraic R x) (hc : c ≠ 0) (hDx : (D : Module.End R A) x = c • x) :
    IsNilpotent x := by
  classical
  by_contra hnil
  have hpowers : LinearIndependent R (fun n : ℕ => x ^ n) :=
    (D : Module.End R A).eigenvectors_linearIndependent' (fun n : ℕ => n * c)
      (fun i j hij => Nat.cast_injective (mul_right_cancel₀ hc hij)) _ fun n =>
        ⟨Module.End.mem_eigenspace_iff.mpr (apply_pow_of_apply_eq_smul D hDx n),
          fun hn => hnil ⟨n, hn⟩⟩
  obtain ⟨p, hp, hpx⟩ := hx
  rw [Polynomial.aeval_eq_sum_range] at hpx
  have hcoeff := linearIndependent_iff'.mp hpowers (Finset.range (p.natDegree + 1))
    (fun n => p.coeff n) hpx
  apply hp
  ext n
  by_cases hn : n < p.natDegree + 1
  · simpa using hcoeff n (Finset.mem_range.mpr hn)
  · exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).trans (by simp)

end TauCeti.derivationLieAlgebra
