/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.Symmetrizer
public import TauCeti.GroupTheory.Perm.Poincare

/-!
# The quantum-factorial normalization of the full Hecke symmetrizer

For the symmetric group on all `n` letters, the row q-symmetrizer has
quasi-idempotence scalar `∏ d ∈ Icc 1 n, (1 + q² + ⋯ + q^(2*(d-1)))`.
This formula also holds when this quantum factorial vanishes: no invertibility
or genericity hypothesis is imposed.

## References

* R. Dipper and G. James, *Representations of Hecke algebras of general linear groups*,
  Proc. London Math. Soc. (3) 52 (1986), 20–52, Section 3.
-/

public section

namespace TauCeti.TypeAHeckeAlgebra

/-- The full row q-symmetrizer squares to the quantum factorial times itself,
including at parameters for which the quantum factorial is zero. -/
theorem parabolicEigenSum_univ_q_mul_self {R : Type*} [CommRing R] (q : Rˣ) (n : ℕ) :
    parabolicEigenSum (permCoxeterSystem n) Set.univ (q : R) *
        parabolicEigenSum (permCoxeterSystem n) Set.univ (q : R) =
      (∏ d ∈ Finset.Icc 1 n, ∑ j ∈ Finset.range d, (q : R) ^ (2 * j)) •
        parabolicEigenSum (q := q) (permCoxeterSystem n) Set.univ (q : R) := by
  classical
  let _ := Fintype.ofFinite ((permCoxeterSystem n).parabolic Set.univ)
  rw [parabolicEigenSum_q_mul_self]
  congr 1
  calc
    (∑ w : (permCoxeterSystem n).parabolic Set.univ,
        (q : R) ^ (2 * (permCoxeterSystem n).length w)) =
        ∑ w : Equiv.Perm (Fin n), (q : R) ^ (2 * (permCoxeterSystem n).length w) := by
      exact Fintype.sum_equiv (Equiv.subtypeUnivEquiv (fun w => by
        rw [CoxeterSystem.parabolic_univ]; exact Subgroup.mem_top w)) _ _ (fun _ => rfl)
    _ = ∏ d ∈ Finset.Icc 1 n, ∑ j ∈ Finset.range d, (q : R) ^ (2 * j) := by
      simpa only [pow_mul] using sum_pow_permCoxeterSystem_length ((q : R) ^ 2) n

end TauCeti.TypeAHeckeAlgebra
