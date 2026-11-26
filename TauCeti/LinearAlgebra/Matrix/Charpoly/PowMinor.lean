/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.PowerBasis
import TauCeti.LinearAlgebra.Matrix.Rank

/-!
# Linear dependence of the first powers of a matrix

For a square matrix `y` with entries in a commutative ring `R` and a natural number `m`,
`Matrix.powMinor y m a` is the `m × m` minor, at the rows `a 0, …, a (m - 1)`, of the matrix with
rows indexed by `N × N` whose column `j < m` lists the entries of `y ^ j`. The vanishing of all
these minors is a polynomial condition on the entries of `y`.

## Main results

* `Matrix.powMinor_map`: the minors commute with ring homomorphisms applied to the entries.
* `Matrix.forall_powMinor_eq_zero_iff`: over an integral domain, all minors `powMinor y m a`
  vanish if and only if `1, y, …, y ^ (m - 1)` are linearly dependent.
* `Matrix.exists_monic_dvd_charpoly_of_not_linearIndependent`: over an integrally closed domain,
  if `1, y, …, y ^ (m - 1)` are linearly dependent, then a monic factor of `y.charpoly` of degree
  less than `m` has `y` as a root.

## Provenance

`Matrix.powMinor`, `Matrix.powMinor_map` and
`Matrix.exists_monic_dvd_charpoly_of_not_linearIndependent` are adapted from `New.powMinor`,
`New.map_powMinor` and `New.exists_factor_charpoly` in `grh/src/Lib/GaloisRep/KillingPolynomials`
of `grh-lean` (<https://github.com/lsernau/grh-lean>, Apache 2.0, Copyright 2026 Anthropic, PBC).
There the factor is not stated to be monic and the hypothesis is the vanishing of the minors. The
passage between minors and linear dependence uses
`New.det_eval_eq_zero_iff_not_linearIndependent` over a field there; here it uses
`Matrix.linearIndependent_row_iff_exists_det_submatrix_ne_zero` over an integral domain.
-/

public section

open Polynomial

namespace Matrix

variable {N R S : Type*} [Fintype N] [DecidableEq N] [CommRing R] [CommRing S]

/-- The `m × m` minor, at the rows `a 0, …, a (m - 1)`, of the matrix with rows indexed by
`N × N` whose column `j < m` lists the entries of `y ^ j`: its entry at `(i, j)` is the entry of
`y ^ j` at the position `a i`. -/
noncomputable def powMinor (y : Matrix N N R) (m : ℕ) (a : Fin m → N × N) : R :=
  (of fun i j : Fin m ↦ (y ^ (j : ℕ)) (a i).1 (a i).2).det

/-- The minors `powMinor` commute with a ring homomorphism applied to the entries. -/
@[simp]
theorem powMinor_map (y : Matrix N N R) (f : R →+* S) (m : ℕ) (a : Fin m → N × N) :
    (y.map f).powMinor m a = f (y.powMinor m a) := by
  have h_pow (j : ℕ) : y.map f ^ j = (y ^ j).map f := (map_pow f.mapMatrix y j).symm
  rw [powMinor, powMinor, RingHom.map_det]
  congr 1
  ext i j
  simp [h_pow]

/-- The matrix whose row `j` lists the entries of `y ^ j`, so that its maximal minors are the
minors `powMinor y m a` for injective `a`. -/
private noncomputable def powRows (y : Matrix N N R) (m : ℕ) : Matrix (Fin m) (N × N) R :=
  of fun j p ↦ (y ^ (j : ℕ)) p.1 p.2

/-- The minor `powMinor y m a` is the minor of `powRows y m` in the columns `a`. -/
private theorem powMinor_eq_det_submatrix (y : Matrix N N R) (m : ℕ) (a : Fin m → N × N) :
    y.powMinor m a = ((powRows y m).submatrix id a).det := by
  rw [powMinor, ← det_transpose]
  rfl

/-- The rows of `powRows y m` are linearly independent if and only if the matrices `y ^ j` for
`j < m` are. -/
private theorem linearIndependent_powRows_row_iff (y : Matrix N N R) (m : ℕ) :
    LinearIndependent R (powRows y m).row ↔ LinearIndependent R fun j : Fin m ↦ y ^ (j : ℕ) :=
  (LinearEquiv.curry R R N N).symm.toLinearMap.linearIndependent_iff_of_injOn
    (LinearEquiv.injective _).injOn

/-- Over an integral domain, all minors `powMinor y m a` vanish if and only if the matrices
`y ^ j` for `j < m` are linearly dependent. -/
theorem forall_powMinor_eq_zero_iff [IsDomain R] {y : Matrix N N R} {m : ℕ} :
    (∀ a : Fin m → N × N, y.powMinor m a = 0) ↔
      ¬LinearIndependent R fun j : Fin m ↦ y ^ (j : ℕ) := by
  rw [← linearIndependent_powRows_row_iff, linearIndependent_row_iff_exists_det_submatrix_ne_zero]
  push Not
  refine ⟨fun h e ↦ (powMinor_eq_det_submatrix y m e).symm.trans (h e), fun h a ↦ ?_⟩
  rw [powMinor_eq_det_submatrix]
  by_cases ha : Function.Injective a
  · exact h ⟨a, ha⟩
  · obtain ⟨i, j, hij, hne⟩ : ∃ i j, a i = a j ∧ i ≠ j := by
      simpa [Function.Injective] using ha
    exact det_zero_of_column_eq hne fun k ↦ by simp [hij]

/-- Over an integrally closed domain, if the matrices `y ^ j` for `j < m` are linearly dependent,
then `y.charpoly = p * q` for a monic polynomial `p` of degree less than `m` with `p(y) = 0`. -/
theorem exists_monic_dvd_charpoly_of_not_linearIndependent [IsDomain R] [IsIntegrallyClosed R]
    {y : Matrix N N R} {m : ℕ} (hy : ¬LinearIndependent R fun j : Fin m ↦ y ^ (j : ℕ)) :
    ∃ p q : R[X], y.charpoly = p * q ∧ p.Monic ∧ p.natDegree < m ∧ aeval y p = 0 := by
  let F := FractionRing R
  let z : Matrix N N F := y.map (algebraMap R F)
  -- Over the fraction field the matrices `z ^ j`, `j < m`, are linearly dependent.
  have h_lt : (minpoly F z).natDegree < m := by
    by_contra! h_le
    refine (forall_powMinor_eq_zero_iff.mp fun a ↦ ?_) <|
      (linearIndependent_pow z).comp (Fin.castLE h_le) (Fin.castLE_injective h_le)
    rw [powMinor_map, forall_powMinor_eq_zero_iff.mpr hy a, map_zero]
  -- By Gauss's lemma the minimal polynomial of `z` lifts to a monic factor `p` of `y.charpoly`.
  have h_monic : (minpoly F z).Monic := minpoly.monic z.isIntegral
  have h_dvd : minpoly F z ∣ y.charpoly.map (algebraMap R F) :=
    z.minpoly_dvd_charpoly.trans (charpoly_map y (algebraMap R F)).dvd
  have h_lifts : minpoly F z ∈ lifts (algebraMap R F) := by
    obtain ⟨g, hg⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd F y.charpoly_monic h_dvd
    exact (mem_lifts _).mpr ⟨g, by simpa [h_monic.leadingCoeff] using hg⟩
  obtain ⟨p, hp, hp_deg, hp_monic⟩ := lifts_and_natDegree_eq_and_monic h_lifts h_monic
  obtain ⟨q, hq⟩ : p ∣ y.charpoly :=
    (map_dvd_map (algebraMap R F) (IsFractionRing.injective R F) hp_monic).mp (by rwa [hp])
  -- The image of `p(y)` over `F` is `p(z) = 0`.
  have hz_root : (Algebra.ofId R F).mapMatrix (aeval y p) = 0 := by
    rw [← aeval_algHom_apply,
      ← aeval_map_algebraMap F, hp]
    exact minpoly.aeval F z
  exact ⟨p, q, hq, hp_monic, hp_deg ▸ h_lt,
    map_injective (IsFractionRing.injective R F) (by simpa [Algebra.ofId] using hz_root)⟩

end Matrix
