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

private theorem coeff_expand_mul_X_pow (hn : 0 < n) (f : R[X]) (i j : Fin n) (k : ℕ) :
    (expand R n f * X ^ (i : ℕ)).coeff (k * n + j) =
      if i = j then f.coeff k else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    simp [coeff_mul_X_pow, hn]
  · rw [ite_eq_right hij, coeff_mul_X_pow']
    split_ifs with hle
    · rw [coeff_expand hn]
      have hndvd : ¬ n ∣ k * n + j - i := by
        intro hdvd
        have hz := Nat.mod_eq_zero_of_dvd hdvd
        have heq : k * n + j = (k * n + j - i) + i := by omega
        have hm := congrArg (fun a : ℕ => a % n) heq
        have hjmod : (k * n + j) % n = (j : ℕ) := by
          rw [Nat.add_mod, Nat.mul_mod_left]
          simp [Nat.mod_eq_of_lt j.isLt]
        have himod : ((k * n + j - i) + i) % n = (i : ℕ) := by
          rw [Nat.add_mod, hz]
          simp [Nat.mod_eq_of_lt i.isLt]
        exact hij (Fin.ext (by omega))
      simp [hndvd]
    · rfl

private theorem coeff_sum_expand (hn : 0 < n) (f : Fin n → R[X]) (i : Fin n)
    (k : ℕ) : (∑ j, expand R n (f j) * (X ^ (j : ℕ) : R[X])).coeff (k * n + i) =
      (f i).coeff k := by
  classical
  simp only [finsetSum_coeff, coeff_expand_mul_X_pow R hn]
  simp

private theorem expand_powers_linearIndependent (hn : 0 < n) :
    let : Module R[X] R[X] := (expand R n).toRingHom.toAlgebra.toModule
    LinearIndependent R[X] (fun i : Fin n => (X ^ (i : ℕ) : R[X])) := by
  let : Module R[X] R[X] := (expand R n).toRingHom.toAlgebra.toModule
  let : SMul R[X] R[X] := (expand R n).toRingHom.toAlgebra.toSMul
  classical
  rw [Fintype.linearIndependent_iffₛ]
  intro f g hfg i
  ext k
  have h := congrArg (fun p : R[X] => p.coeff (k * n + i)) hfg
  -- The restricted action multiplies by the expanded scalar.
  exact (coeff_sum_expand R hn f i k).symm.trans
    (h.trans (coeff_sum_expand R hn g i k))

private theorem expand_powers_span (hn : 0 < n) :
    let : Module R[X] R[X] := (expand R n).toRingHom.toAlgebra.toModule
    ⊤ ≤ Submodule.span R[X] (Set.range (fun i : Fin n => (X ^ (i : ℕ) : R[X]))) := by
  let : Module R[X] R[X] := (expand R n).toRingHom.toAlgebra.toModule
  let : SMul R[X] R[X] := (expand R n).toRingHom.toAlgebra.toSMul
  suffices ∀ p : R[X], p ∈ Submodule.span R[X]
      (Set.range (fun i : Fin n => (X ^ (i : ℕ) : R[X]))) from fun p _ => this p
  intro p
  induction p using Polynomial.induction_on' with
  | add p q hp hq => exact Submodule.add_mem _ hp hq
  | monomial k a =>
    let i : Fin n := ⟨k % n, Nat.mod_lt k hn⟩
    have hi : (X ^ (i : ℕ) : R[X]) ∈
        Submodule.span R[X] (Set.range (fun i : Fin n => (X ^ (i : ℕ) : R[X]))) :=
      Submodule.subset_span ⟨i, rfl⟩
    have heq : monomial (k / n) a • (X ^ (i : ℕ) : R[X]) = monomial k a := by
      -- The scalar action is multiplication by the expanded polynomial.
      have h := expand_monomial (R := R) n (k / n) a
      have h' := congrArg (fun p => p * X ^ (i : ℕ)) h
      rw [monomial_mul_X_pow] at h'
      have hexp : k / n * n + (i : ℕ) = k := by
        simpa only [i, Nat.mul_comm] using Nat.div_add_mod k n
      rw [hexp] at h'
      exact h'
    rw [← heq]
    exact Submodule.smul_mem _ _ hi

/-- The basis `1, x, …, x ^ (n - 1)` of `R[x]` over `R[t]` for `t ↦ x ^ n`. -/
def expandBasis (hn : 0 < n) :
    letI : Module R[X] R[X] := (expand R n).toRingHom.toAlgebra.toModule
    Basis (Fin n) R[X] R[X] := by
  letI : Module R[X] R[X] := (expand R n).toRingHom.toAlgebra.toModule
  letI : SMul R[X] R[X] := (expand R n).toRingHom.toAlgebra.toSMul
  exact Basis.mk (expand_powers_linearIndependent R hn) (expand_powers_span R hn)

/-- The `i`th basis vector for power substitution is `x ^ i`. -/
@[simp]
theorem expandBasis_apply (hn : 0 < n) (i : Fin n) :
    expandBasis R hn i = (X ^ (i : ℕ) : R[X]) := by
  let : Module R[X] R[X] := (expand R n).toRingHom.toAlgebra.toModule
  exact Basis.mk_apply _ _ _

/-- The coordinates collect coefficients by residue class modulo `n`. -/
@[simp]
theorem expandBasis_repr_coeff (hn : 0 < n) (p : R[X]) (i : Fin n) (k : ℕ) :
    let : Module R[X] R[X] := (expand R n).toRingHom.toAlgebra.toModule
    ((expandBasis R hn).repr p i).coeff k = p.coeff (k * n + i) := by
  let : Module R[X] R[X] := (expand R n).toRingHom.toAlgebra.toModule
  let : SMul R[X] R[X] := (expand R n).toRingHom.toAlgebra.toSMul
  have h := congrArg (fun q : R[X] => q.coeff (k * n + i))
    ((expandBasis R hn).sum_repr p)
  simp only [expandBasis_apply] at h
  have hs : (∑ j, (expandBasis R hn).repr p j • (X ^ (j : ℕ) : R[X])) =
      ∑ j, expand R n ((expandBasis R hn).repr p j) * (X ^ (j : ℕ) : R[X]) := by
    apply Finset.sum_congr rfl
    intro j _
    exact @Algebra.smul_def R[X] R[X] _ _ (expand R n).toRingHom.toAlgebra _ _
  rw [hs] at h
  exact (coeff_sum_expand R hn (fun j => (expandBasis R hn).repr p j) i k).symm.trans h

/-- Polynomial power substitution with positive exponent is flat, in every characteristic. -/
theorem flat_expand (S : Type u) [CommRing S] {n : ℕ} (hn : 0 < n) :
    (expand S n).toRingHom.Flat := by
  let : Module S[X] S[X] := (expand S n).toRingHom.toAlgebra.toModule
  let : Module.Free S[X] S[X] := Module.Free.of_basis (expandBasis S hn)
  exact Module.Flat.of_free

end TauCeti.Polynomial
