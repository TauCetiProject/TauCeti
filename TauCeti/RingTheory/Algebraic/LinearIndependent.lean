/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Algebraic.Basic
-- Proof-only: the rank of the span of a linearly independent family.
import Mathlib.LinearAlgebra.Dimension.Constructions
-- Proof-only: products of linearly independent families in a tower, and powers below the degree.
import Mathlib.RingTheory.AlgebraTower
import Mathlib.RingTheory.PowerBasis
-- Proof-only: a nontrivial commutative ring satisfies the strong rank condition.
import Mathlib.RingTheory.FiniteType

/-!
# Linear independence from transcendence

The powers of a transcendental element of an algebra are linearly independent over the base ring.
Consequently, the first `n` powers span a submodule of rank `n` over a nontrivial commutative ring,
and in a tower `R → K → A` with `K` a field, the products `x ^ i y ^ j` of the powers of `x ∈ K`
transcendental over `R` with the powers `y ^ j`, `j < (minpoly K y).natDegree`, of `y ∈ A` are
linearly independent over `R`.

## Main results

* `Transcendental.linearIndependent_pow`: the powers of a transcendental element are
  linearly independent over the base ring.
* `Transcendental.finrank_span_range_pow`: over a nontrivial commutative ring, the span of the
  first `n` powers of a transcendental element has rank `n`.
* `Transcendental.linearIndepOn_pow_mul_pow`: in a tower `R → K → A`, the products `x ^ i y ^ j`
  with `x ∈ K` transcendental over `R` and `j < (minpoly K y).natDegree` are linearly independent
  over `R`.
-/

public section

namespace TauCeti

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- The powers of a transcendental element are linearly independent over the base ring. -/
theorem _root_.Transcendental.linearIndependent_pow {x : A} (hx : Transcendental R x) :
    LinearIndependent R fun n : ℕ ↦ x ^ n := by
  simpa [Function.comp_def] using (Polynomial.basisMonomials R).linearIndependent.map_injOn
    (Polynomial.aeval x).toLinearMap (transcendental_iff_injective.mp hx).injOn

/-- The first `n` powers of a transcendental element span a submodule of rank `n` over a
nontrivial commutative ring. -/
theorem _root_.Transcendental.finrank_span_range_pow {K B : Type*} [CommRing K] [Nontrivial K]
    [Ring B] [Algebra K B] {x : B} (hx : Transcendental K x) (n : ℕ) :
    Module.finrank K (Submodule.span K (Set.range fun i : Fin n ↦ x ^ (i : ℕ))) = n :=
  (finrank_span_eq_card (hx.linearIndependent_pow.comp _ Fin.val_injective)).trans
    (Fintype.card_fin n)

/-- **The products `x ^ i y ^ j` are linearly independent**: in a tower `R → K → A` with `K` a
field, if `x ∈ K` is transcendental over `R` and `y ∈ A`, then the products `x ^ i y ^ j` with
`j < (minpoly K y).natDegree` are linearly independent over `R`. The bound is the degree of `y`
over `K` when `y` is integral over `K`; otherwise `minpoly K y = 0` and the statement is vacuous. -/
theorem _root_.Transcendental.linearIndepOn_pow_mul_pow {K : Type*} [Field K] [Algebra R K]
    [Algebra K A] [IsScalarTower R K A] {x : K} (hx : Transcendental R x) (y : A) :
    LinearIndepOn R (fun p : ℕ × ℕ ↦ algebraMap K A x ^ p.1 * y ^ p.2)
      {p | p.2 < (minpoly K y).natDegree} := by
  -- The powers of `x` are independent over `R`, those of `y` below `(minpoly K y).natDegree`
  -- over `K`.
  have h := linearIndependent_smul (R := R) hx.linearIndependent_pow (linearIndependent_pow y)
  have hinj : Function.Injective fun p : {p : ℕ × ℕ | p.2 < (minpoly K y).natDegree} ↦
      ((p : ℕ × ℕ).1, (⟨(p : ℕ × ℕ).2, p.2⟩ : Fin (minpoly K y).natDegree)) :=
    fun p q hpq ↦ by
      simp only [Prod.mk.injEq, Fin.mk.injEq] at hpq
      exact Subtype.ext (Prod.ext hpq.1 hpq.2)
  rw [← linearIndependent_set_coe_iff]
  convert h.comp _ hinj using 1
  ext p
  simp [Algebra.smul_def]

end TauCeti
