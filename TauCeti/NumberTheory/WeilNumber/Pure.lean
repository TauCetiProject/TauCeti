/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import TauCeti.NumberTheory.WeilNumber.Basic
public import TauCeti.LinearAlgebra.Charpoly.Roots

import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Semisimple

/-!
# Pure endomorphisms

Let `V` be a finite-dimensional vector space over a field `K` of characteristic zero, `F` an
endomorphism of `V`, `q` a real number and `n` an integer. Following Deligne, `F` is *pure of
weight `n` relative to `q`* if every eigenvalue of `F`, that is every root of the characteristic
polynomial of `F` in an algebraic closure of `K`, is a Weil `q`-number of weight `n`. For the
geometric Frobenius acting on the `ℓ`-adic cohomology `Hⁱ` of a smooth projective variety over a
finite field with `q` elements this is Deligne's purity theorem, with `n = i`.

Purity is a condition on the characteristic roots only: it does not see Jordan blocks, so a pure
endomorphism need not be semisimple. Since Weil numbers are nonzero, a pure endomorphism is
invertible. The zero space is pure of every weight. Because being a Weil number is preserved and
reflected by field homomorphisms, purity can be tested in any algebraically closed field over
`K`, and it is preserved and reflected by extension of scalars to any field over `K`.

## Main definitions

* `TauCeti.IsPure q n F`: `F` is pure of weight `n` relative to `q`.

## Main results

* `TauCeti.isPure_iff_forall_mem_aroots`: purity may be tested on the characteristic roots in
  any algebraically closed field over `K`.
* `TauCeti.IsPure.isWeilNumber_of_mem_aroots`: every characteristic root of a pure endomorphism
  in any field over `K` is a Weil number of its weight.
* `TauCeti.IsPure.isWeilNumber_of_hasEigenvalue`: every eigenvalue in `K` of a pure endomorphism
  is a Weil number of its weight.
* `TauCeti.isPure_baseChange_iff`: purity is preserved and reflected by extension of scalars.
* `TauCeti.isPure_conj_iff`: purity is invariant under conjugation by a linear equivalence.
* `TauCeti.IsPure.isUnit`: a pure endomorphism is invertible.
* `TauCeti.IsPure.unique`: a pure endomorphism of a nonzero space has a unique weight.
* `TauCeti.isPure_of_subsingleton`: every endomorphism of the zero space is pure of every weight.

The file closes with examples: a Jordan block `[[q, 1], [0, q]]` is pure of weight `2` without
being semisimple, the matrix `[[0, -q], [1, 0]]` is pure of weight `1` although it has no
eigenvalue in `ℚ`, and `diag(1, q)` is pure of no weight.

## References

* P. Deligne, *La conjecture de Weil. I*, Publ. Math. IHÉS 43 (1974), §2, (2.6).
* P. Deligne, *La conjecture de Weil. II*, Publ. Math. IHÉS 52 (1980), §1.2, (1.2.1) and
  Variante (1.2.4).
-/

public section

open Module Polynomial

namespace TauCeti

variable {K V : Type*} [Field K] [Algebra ℚ K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {q : ℝ} {n m : ℤ} {F : End K V}

/-- An endomorphism `F` of a finite-dimensional vector space over a field `K` of characteristic
zero is *pure of weight `n` relative to `q`* if every root of its characteristic polynomial in an
algebraic closure of `K` is a Weil `q`-number of weight `n`. See
`TauCeti.isPure_iff_forall_mem_aroots` for the independence of the algebraic closure. -/
def IsPure (q : ℝ) (n : ℤ) (F : End K V) : Prop :=
  ∀ α ∈ F.charpoly.aroots (AlgebraicClosure K), IsWeilNumber q n α

/-- Purity may be tested on the characteristic roots in any algebraically closed field `Ω`
over `K`. -/
theorem isPure_iff_forall_mem_aroots (Ω : Type*) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    [Algebra ℚ Ω] : IsPure q n F ↔ ∀ α ∈ F.charpoly.aroots Ω, IsWeilNumber q n α := by
  let φ : AlgebraicClosure K →ₐ[K] Ω := IsAlgClosed.lift
  have hroots : F.charpoly.aroots Ω = (F.charpoly.aroots (AlgebraicClosure K)).map φ := by
    rw [aroots_def, aroots_def, ← φ.comp_algebraMap, ← map_map]
    exact (IsAlgClosed.splits _).roots_map_of_injective φ.injective
  rw [IsPure, hroots, Multiset.forall_mem_map_iff]
  simp only [isWeilNumber_map_iff]

/-- Purity is preserved and reflected by extension of scalars to any field `L` over `K`. -/
@[simp]
theorem isPure_baseChange_iff (L : Type*) [Field L] [Algebra K L] [Algebra ℚ L] :
    IsPure q n (F.baseChange L) ↔ IsPure q n F := by
  rw [isPure_iff_forall_mem_aroots (AlgebraicClosure L),
    isPure_iff_forall_mem_aroots (AlgebraicClosure L), LinearMap.charpoly_baseChange, aroots_map]

/-- Purity is invariant under conjugation by a linear equivalence. -/
@[simp]
theorem isPure_conj_iff {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (e : V ≃ₗ[K] W) : IsPure q n (e.conj F) ↔ IsPure q n F := by
  rw [IsPure, IsPure, LinearEquiv.charpoly_conj]

/-- Every endomorphism of the zero space is pure of every weight, relative to every `q`. -/
@[simp]
theorem isPure_of_subsingleton [Subsingleton V] : IsPure q n F := by
  intro α hα
  have hcard := F.card_aroots_charpoly (AlgebraicClosure K)
  rw [finrank_zero_of_subsingleton, Multiset.card_eq_zero] at hcard
  simp [hcard] at hα

namespace IsPure

/-- Every root of the characteristic polynomial of a pure endomorphism in a field `L` over `K`
is a Weil number of the weight of the endomorphism. -/
theorem isWeilNumber_of_mem_aroots {L : Type*} [Field L] [Algebra K L] [Algebra ℚ L]
    (h : IsPure q n F) {α : L} (hα : α ∈ F.charpoly.aroots L) : IsWeilNumber q n α := by
  rw [← isWeilNumber_map_iff (algebraMap L (AlgebraicClosure L))]
  refine (isPure_iff_forall_mem_aroots (AlgebraicClosure L)).mp h _ ?_
  rw [LinearMap.mem_aroots_charpoly_iff] at hα ⊢
  rw [aeval_algebraMap_apply, hα, map_zero]

/-- Every eigenvalue in `K` of a pure endomorphism is a Weil number of its weight. -/
theorem isWeilNumber_of_hasEigenvalue (h : IsPure q n F) {α : K} (hα : F.HasEigenvalue α) :
    IsWeilNumber q n α :=
  h.isWeilNumber_of_mem_aroots <| by
    rw [LinearMap.mem_aroots_charpoly_iff, ← eval_map_algebraMap, Algebra.algebraMap_self,
      map_id]
    exact (Module.End.hasEigenvalue_iff_isRoot_charpoly F α).mp hα

/-- A pure endomorphism is invertible: its characteristic roots are Weil numbers, hence
nonzero. -/
theorem isUnit (h : IsPure q n F) : IsUnit F := by
  rw [LinearMap.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  exact ((LinearMap.not_hasEigenvalue_zero_tfae F).out 1 4).mp fun h0 ↦
    not_isWeilNumber_zero (h.isWeilNumber_of_hasEigenvalue h0)

/-- The weight of a pure endomorphism of a nonzero space is unique. -/
theorem unique [Nontrivial V] (h : IsPure q n F) (h' : IsPure q m F) : n = m := by
  obtain ⟨α, hα⟩ := Multiset.card_pos_iff_exists_mem.mp
    ((F.card_aroots_charpoly (AlgebraicClosure K)).symm ▸ finrank_pos)
  exact (h α hα).unique (h' α hα)

end IsPure

/-! ### Examples -/

/- A Jordan block `[[q, 1], [0, q]]` with `1 < q` rational is pure of weight `2` relative to `q`
and is not semisimple: purity does not see Jordan blocks. -/
example {q : ℚ} (hq : 1 < q) :
    IsPure (q : ℝ) 2 (Matrix.toLin' !![(q : K), 1; 0, q]) ∧
      ¬Module.End.IsSemisimple (Matrix.toLin' !![(q : K), 1; 0, q]) := by
  refine ⟨fun α hα ↦ ?_, fun hs ↦ ?_⟩
  · have hpoly : (Matrix.toLin' !![(q : K), 1; 0, q]).charpoly = (X - C (q : K)) ^ 2 := by
      rw [Matrix.charpoly_toLin', Matrix.charpoly_fin_two]
      simp only [Matrix.trace_fin_two_of, map_add, Matrix.det_fin_two_of, mul_zero, sub_zero,
        map_mul]
      ring
    rw [hpoly, aroots_pow, aroots_X_sub_C, Multiset.mem_nsmul_of_ne_zero two_ne_zero,
      Multiset.mem_singleton] at hα
    rw [hα, map_ratCast]
    exact isWeilNumber_ratCast hq
  · have hN : Matrix.toLin' !![(q : K), 1; 0, q] - algebraMap K (End K (Fin 2 → K)) q =
        Matrix.toLin' !![0, 1; 0, 0] := by
      ext v i
      fin_cases v <;> fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have hnil : IsNilpotent (Matrix.toLin' !![(0 : K), 1; 0, 0]) := by
      refine ⟨2, ?_⟩
      ext v i
      fin_cases v <;> fin_cases i <;> simp [sq, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have h0 := Module.End.eq_zero_of_isNilpotent_isSemisimple hnil
      (hN ▸ (Module.End.isSemisimple_sub_algebraMap_iff.mpr hs))
    have := congrArg (fun f ↦ f (Pi.single 1 1) 0) h0
    simp at this

/- The matrix `[[0, -q], [1, 0]]` on `ℚ²`, for rational `q > 1`, has characteristic polynomial
`X² + q`. Its characteristic roots `± i √q` lie in an algebraic closure of `ℚ`, not in `ℚ`, and
are Weil `q`-numbers of weight `1`, so it is pure of weight `1`. -/
example {q : ℚ} (hq : 1 < q) : IsPure (q : ℝ) 1 (Matrix.toLin' !![0, -q; 1, 0]) := by
  have hpoly : (Matrix.toLin' !![0, -q; 1, 0]).charpoly = X ^ 2 + C q := by
    rw [Matrix.charpoly_toLin', Matrix.charpoly_fin_two]
    simp
  intro α hα
  rw [hpoly, mem_aroots'] at hα
  have hα2 : α ^ 2 = ((-q : ℚ) : AlgebraicClosure ℚ) := by
    have := hα.2
    simp only [map_add, map_pow, aeval_X, aeval_C, eq_ratCast] at this
    push_cast
    linear_combination this
  have hq0 : (0 : ℝ) ≤ q := by exact_mod_cast (zero_lt_one.trans hq).le
  rw [← isWeilNumber_pow_iff two_ne_zero hq0, hα2]
  refine IsWeilNumber.of_aeval_eq_zero (P := X - C (-q)) ?_ (X_sub_C_ne_zero _) (by simp)
    fun z hz ↦ ?_
  · exact one_lt_pow₀ (by exact_mod_cast hq) two_ne_zero
  · rw [aroots_X_sub_C, Multiset.mem_singleton] at hz
    rw [hz, eq_ratCast, Complex.norm_ratCast, ← Real.rpow_natCast, ← Real.rpow_mul hq0]
    norm_num [abs_of_pos (zero_lt_one.trans hq), (zero_lt_one.trans hq).le]

/- `diag(1, q)`, for rational `q > 1`, is pure of no weight relative to `q`: its eigenvalues `1`
and `q` have weights `0` and `2`. -/
example {q : ℚ} (hq : 1 < q) (n : ℤ) : ¬IsPure (q : ℝ) n (Matrix.toLin' !![(1 : K), 0; 0, q]) := by
  intro h
  have hroot (a : K) (ha : a = 1 ∨ a = q) :
      a ∈ (Matrix.toLin' !![(1 : K), 0; 0, q]).charpoly.aroots K := by
    rw [LinearMap.mem_aroots_charpoly_iff, Matrix.charpoly_toLin', Matrix.charpoly_fin_two]
    rcases ha with rfl | rfl
    · simp
    · simp only [Matrix.trace_fin_two_of, map_add, map_one, Matrix.det_fin_two_of, one_mul,
        mul_zero, sub_zero, coe_aeval_eq_eval, eval_add, eval_sub, eval_pow, eval_X, eval_mul,
        eval_one, eval_C]
      ring
  have h1 := (h.isWeilNumber_of_mem_aroots (hroot 1 (.inl rfl))).unique
    (isWeilNumber_one (by exact_mod_cast hq))
  have h2 := (h.isWeilNumber_of_mem_aroots (hroot q (.inr rfl))).unique
    (isWeilNumber_ratCast hq)
  omega

/- The zero space is pure of every weight. -/
example : IsPure q n (0 : End K (Fin 0 → K)) := isPure_of_subsingleton

end TauCeti
