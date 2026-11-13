/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.RingTheory.RingHom.Flat

/-!
# A basis for polynomial power substitution

For a positive integer `n`, substitution `t ↦ x ^ n` makes `R[x]` a finite free module over
`R[t]`, with basis `1, x, …, x ^ (n - 1)`. This file constructs that basis and computes its
coordinates: the coefficient polynomial in position `i` collects the coefficients in degrees
congruent to `i` modulo `n`.

In particular the power substitution is flat over every commutative ring, including in
characteristic dividing `n`. This supplies the flat potential map for polynomial matrix
factorizations of `x ^ n`.

The basis construction works over a commutative semiring. Its scalar action is restriction
along Mathlib's `Polynomial.expand R n`, stated using `RingHom.toAlgebra` locally, so the usual
scalar action on polynomials is unchanged. The construction reuses `Module.Basis.mk`; the
coefficient calculation supplies linear independence and the coordinate formula.

## References

* D. Orlov, *Triangulated categories of singularities and D-branes in Landau–Ginzburg models*,
  Proceedings of the Steklov Institute of Mathematics **246** (2004), Section 3.
-/

public section

noncomputable section

open Polynomial Module

namespace TauCeti.Polynomial

universe u

variable (R : Type u) [CommSemiring R] {n : ℕ}

private theorem coeff_expand_mul_X_pow (f : R[X]) (i j : Fin n) (k : ℕ) :
    (expand R n f * X ^ (i : ℕ)).coeff (k * n + j) =
      if i = j then f.coeff k else 0 := by
  split_ifs with hij
  · subst j
    simp [coeff_mul_X_pow, i.pos]
  · rw [coeff_mul_X_pow', coeff_expand i.pos]
    split_ifs with hle hdvd
    · -- `i ≡ k * n + j [MOD n]` with `i, j < n` forces `i = j`.
      have hmod := (Nat.modEq_iff_dvd' hle).mpr hdvd
      simp [Nat.ModEq, Nat.mod_eq_of_lt, Fin.val_inj, hij] at hmod
    all_goals rfl

private theorem coeff_sum_expand (f : Fin n → R[X]) (i : Fin n) (k : ℕ) :
    (∑ j, expand R n (f j) * (X ^ (j : ℕ) : R[X])).coeff (k * n + i) = (f i).coeff k := by
  simp [coeff_expand_mul_X_pow]

private theorem expand_powers_linearIndependent :
    letI : Module R[X] R[X] := (expand R n).toRingHom.toAlgebra.toModule
    LinearIndependent R[X] (fun i : Fin n => (X ^ (i : ℕ) : R[X])) := by
  let : Module R[X] R[X] := (expand R n).toRingHom.toAlgebra.toModule
  rw [Fintype.linearIndependent_iffₛ]
  intro f g hfg i
  ext k
  -- The restricted action multiplies by the expanded scalar.
  exact (coeff_sum_expand R f i k).symm.trans
    ((congrArg (fun p : R[X] => p.coeff (k * n + i)) hfg).trans (coeff_sum_expand R g i k))

private theorem expand_powers_span (hn : 0 < n) :
    letI : Module R[X] R[X] := (expand R n).toRingHom.toAlgebra.toModule
    ⊤ ≤ Submodule.span R[X] (Set.range (fun i : Fin n => (X ^ (i : ℕ) : R[X]))) := by
  let : Module R[X] R[X] := (expand R n).toRingHom.toAlgebra.toModule
  rintro p -
  induction p using Polynomial.induction_on' with
  | add p q hp hq => exact Submodule.add_mem _ hp hq
  | monomial k a =>
    -- The scalar action is multiplication by the expanded polynomial.
    have heq : expand R n (monomial (k / n) a) * X ^ (k % n) = monomial k a := by
      rw [expand_monomial, monomial_mul_X_pow, Nat.div_add_mod']
    exact heq ▸ Submodule.smul_mem _ (monomial (k / n) a)
      (Submodule.subset_span ⟨⟨k % n, Nat.mod_lt k hn⟩, rfl⟩)

/-- The basis `1, x, …, x ^ (n - 1)` of `R[x]` over `R[t]` for `t ↦ x ^ n`. -/
def expandBasis (hn : 0 < n) :
    letI : Module R[X] R[X] := (expand R n).toRingHom.toAlgebra.toModule
    Basis (Fin n) R[X] R[X] :=
  letI : Module R[X] R[X] := (expand R n).toRingHom.toAlgebra.toModule
  Basis.mk (expand_powers_linearIndependent R) (expand_powers_span R hn)

/-- The `i`th basis vector for power substitution is `x ^ i`. -/
@[simp]
theorem expandBasis_apply (hn : 0 < n) (i : Fin n) :
    expandBasis R hn i = (X ^ (i : ℕ) : R[X]) := by
  let : Module R[X] R[X] := (expand R n).toRingHom.toAlgebra.toModule
  exact Basis.mk_apply _ _ _

/-- The coordinates collect coefficients by residue class modulo `n`. -/
@[simp]
theorem expandBasis_repr_coeff (hn : 0 < n) (p : R[X]) (i : Fin n) (k : ℕ) :
    letI : Module R[X] R[X] := (expand R n).toRingHom.toAlgebra.toModule
    ((expandBasis R hn).repr p i).coeff k = p.coeff (k * n + i) := by
  let : Module R[X] R[X] := (expand R n).toRingHom.toAlgebra.toModule
  have h := (expandBasis R hn).sum_repr p
  simp only [expandBasis_apply] at h
  -- The restricted action multiplies by the expanded scalar.
  exact (coeff_sum_expand R (fun j => (expandBasis R hn).repr p j) i k).symm.trans
    (congrArg (fun p : R[X] => p.coeff (k * n + i)) h)

/-- Polynomial power substitution with positive exponent is flat, in every characteristic. -/
theorem flat_expand (S : Type u) [CommRing S] {n : ℕ} (hn : 0 < n) :
    (expand S n).toRingHom.Flat :=
  letI : Module S[X] S[X] := (expand S n).toRingHom.toAlgebra.toModule
  haveI : Module.Free S[X] S[X] := Module.Free.of_basis (expandBasis S hn)
  Module.Flat.of_free

end TauCeti.Polynomial
