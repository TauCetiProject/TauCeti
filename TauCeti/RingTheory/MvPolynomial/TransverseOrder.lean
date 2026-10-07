/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.DirectionalOrder

/-!
# Transverse plane slices preserving ambient order

Keep coordinate zero as a free root coordinate and restrict the remaining coordinates
to an affine line. One base direction can be chosen so that these plane restrictions
preserve ambient order for finitely many polynomial–point pairs. The points and
polynomials need not be distinct, and zero polynomials are included.

This permits ambient order along polynomial root sections to be calculated using
two-variable slices, while retaining the distinguished root coordinate. In particular,
one direction can test a discriminant at a base point and the original polynomial at
each of its finitely many roots above that point. Preservation at those points is a
conclusion; preservation at other points is not asserted.

The plane coordinates are `(line parameter, root coordinate)`, so that the slice is
centered at `![0, a 0]` and evaluates to `p(z, Fin.tail a + y • v)` at `![y, z]`.

## References

* S. McCallum, *An improved projection operation for cylindrical algebraic
  decomposition*, Springer (1998), Sections 2–3 (ambient order and delineability).
-/

public section

namespace MvPolynomial

variable {R : Type*} {n : ℕ}

/-- Evaluation of a transverse plane restriction keeps the root coordinate free and
moves the base along an affine line. -/
-- Kept as an explicit rewrite: `map_aeval` simplifies the left-hand side to `eval₂`,
-- so adding `@[simp]` here fails the `simpNF` linter.
theorem eval_aeval_finCons_C_add_C_mul_X [CommSemiring R]
    (p : MvPolynomial (Fin (n + 1)) R) (a v : Fin n → R) (y z : R) :
    eval ![y, z]
      (aeval (Fin.cons (X 1) (fun j ↦ C (a j) + C (v j) * X 0)) p) =
      eval (Fin.cons z (a + y • v)) p := by
  simp only [← aeval_eq_eval]
  rw [comp_aeval_apply]
  congr 1
  ext i
  cases i using Fin.cases <;> simp [mul_comm]

/-- If an affine line detects ambient order, the plane containing that line and the
distinguished coordinate also detects it. This statement allows infinite order. -/
theorem orderAt_aeval_finCons_C_add_C_mul_X_eq [CommRing R]
    (p : MvPolynomial (Fin (n + 1)) R) (a v : Fin (n + 1) → R)
    (hv : (aeval (fun j ↦ Polynomial.C (a j) + Polynomial.C (v j) * Polynomial.X)
      p).trailingDegree = p.orderAt a) :
    (aeval (Fin.cons (X 1) (fun j ↦ C (a j.succ) + C (v j.succ) * X 0))
      p).orderAt ![0, a 0] = p.orderAt a := by
  let g : Fin (n + 1) → MvPolynomial (Fin 2) R :=
    Fin.cons (X 1) (fun j ↦ C (a j.succ) + C (v j.succ) * X 0)
  have hcenter : (fun j ↦ eval ![0, a 0] (g j)) = a := by
    ext i
    cases i using Fin.cases <;> simp [g]
  have hlower := p.orderAt_le_orderAt_aeval g ![0, a 0]
  rw [hcenter] at hlower
  have hupper := (aeval g p).orderAt_le_trailingDegree_aeval_C_add_C_mul_X
    ![0, a 0] ![1, v 0]
  have hline :
      aeval (fun j ↦ Polynomial.C (![0, a 0] j) +
        Polynomial.C (![1, v 0] j) * Polynomial.X) (aeval g p) =
      aeval (fun j ↦ Polynomial.C (a j) + Polynomial.C (v j) * Polynomial.X) p := by
    rw [comp_aeval_apply]
    congr 1
    ext i
    cases i using Fin.cases <;> simp [g]
  rw [hline, hv] at hupper
  exact le_antisymm hupper hlower

/-- A single base direction gives transverse plane restrictions preserving ambient order
for finitely many polynomial–point pairs over an infinite domain. Coordinate zero remains
free. Zero polynomials retain infinite order, and an empty family is allowed. -/
theorem exists_forall_orderAt_aeval_finCons_C_add_C_mul_X_eq
    [CommRing R] [IsDomain R] [Infinite R] {ι : Type*}
    (s : Finset ι) (p : ι → MvPolynomial (Fin (n + 1)) R)
    (a : ι → Fin (n + 1) → R) :
    ∃ v : Fin n → R, ∀ i ∈ s,
      (aeval (Fin.cons (X 1) (fun j ↦ C (a i j.succ) + C (v j) * X 0))
        (p i)).orderAt ![0, a i 0] = (p i).orderAt (a i) := by
  obtain ⟨v, hv⟩ := exists_forall_trailingDegree_aeval_C_add_C_mul_X_eq s p a
  exact ⟨Fin.tail v, fun i hi ↦
    (p i).orderAt_aeval_finCons_C_add_C_mul_X_eq (a i) v (hv i hi)⟩

end MvPolynomial
