/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.LinearAlgebra.Matrix.Block
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer

/-!
# Cartan diagonalization for `GL_n` over a valuation subring

Let `O : ValuationSubring F` be a valuation subring of a field `F`. Every square matrix
`y : Matrix n n F` admits a Cartan factorization
`y = k * diagonal d * k'` with `k, k' : GL n O` mapped into `GL n F` via
`GeneralLinearGroup.map (algebraMap O F)` (`ValuationSubring.exists_mul_diagonal_mul`).

The proof proceeds by induction on `Fintype.card n` via pivot elimination over `O`:
1. `ValuationSubring.exists_pivot_dvd` chooses an entry of maximal valuation, which `O`-divides
   every entry of `y`.
2. `Matrix.exists_eq_mul_diagonal_mul_of_pivot_dvd` lifts a diagonalization of the Schur-complement
   block `(M - w · M p).toBlock (· ≠ p) (· ≠ p)` to a diagonalization of `M` via block-triangular
   matrices in `GL n O`.

## References

* J. Tits, *Reductive groups over local fields*, Automorphic Forms, Representations and
  L-Functions, Proc. Sympos. Pure Math. 33 (1979), §3.3.3.
* T. Tamagawa, *On the ζ-functions of a division algebra*, Ann. of Math. **77** (1963), 387–405.
* Adapted from `src/Lib/General/LinearAlgebra/IntegralLattices.lean` in `grh-lean`
  (<https://github.com/lsernau/grh-lean>, Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

noncomputable section

open Matrix Matrix.GeneralLinearGroup

universe u

namespace Matrix

/-- One pivot elimination step over a `CommRing` homomorphism `algebraMap R A`: if every entry
`M i j` is an `R`-multiple `algebraMap R A (w i j) * M p p` of the `(p, p)` entry and the
remaining block diagonalizes over `R`, then `M` diagonalizes over `R`. -/
theorem exists_eq_mul_diagonal_mul_of_pivot_dvd {n : Type u} [Fintype n] [DecidableEq n]
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (M : Matrix n n A) {p : n} {w : n → n → R}
    (hw : ∀ i j : n, algebraMap R A (w i j) * M p p = M i j)
    {k l : GL {i : n // i ≠ p} R} {d : {i : n // i ≠ p} → A}
    (h_block : (M - of fun i : n ↦ algebraMap R A (w i p) • M p).toBlock (· ≠ p) (· ≠ p) =
      (GeneralLinearGroup.map (algebraMap R A) k).val * diagonal d *
        (GeneralLinearGroup.map (algebraMap R A) l).val) :
    ∃ (lower upper : GL n R) (D : n → A),
      M = (GeneralLinearGroup.map (algebraMap R A) lower).val * diagonal D *
        (GeneralLinearGroup.map (algebraMap R A) upper).val := by
  let e : {i : n // i = p} ⊕ {i : n // i ≠ p} ≃ n := Equiv.sumCompl (· = p)
  let lower : GL n R :=
    GeneralLinearGroup.mk'' (reindex e e (fromBlocks 1 0 (of fun i j ↦ w i j) k)) (by simp)
  let upper : GL n R :=
    GeneralLinearGroup.mk'' (reindex e e (fromBlocks 1 (of fun i j ↦ w i j) 0 l)) (by simp)
  let D : n → A := Sum.elim (fun _ ↦ M p p) d ∘ e.symm
  have block_entry (i j : {i : n // i ≠ p}) :
      M i j - algebraMap R A (w i p) * M p j =
        ∑ s : {i : n // i ≠ p}, algebraMap R A (k.val i s) * d s * algebraMap R A (l.val s j) := by
    have h := congrFun (congrFun h_block i) j
    simpa [Matrix.mul_apply, Matrix.diagonal_apply, GeneralLinearGroup.map,
      Algebra.smul_def] using h
  have default_val : ((default : {i : n // i = p}) : n) = p := (default : {i : n // i = p}).property
  refine ⟨lower, upper, D, (reindex e.symm e.symm).injective ?_⟩
  suffices M.submatrix e e =
      fromBlocks 1 0 ((of fun i j ↦ w i.val j.val).map (algebraMap R A))
          (GeneralLinearGroup.map (algebraMap R A) k).val *
        diagonal (Sum.elim (fun _ : {i : n // i = p} ↦ M p p) d) *
        fromBlocks 1 ((of fun i j ↦ w i.val j.val).map (algebraMap R A)) 0
          (GeneralLinearGroup.map (algebraMap R A) l).val by
    simp [this, lower, upper, D, ← submatrix_mul_equiv _ _ _ e, fromBlocks_map, submatrix_map,
      Function.comp_assoc, GeneralLinearGroup.map]
  rw [← fromBlocks_diagonal, fromBlocks_multiply, fromBlocks_multiply]
  ext (i | i) (j | j)
  · simp [e, Unique.eq_default, default_val]
  · simp [e, mul_comm (M p p), Unique.eq_default i, default_val, hw]
  · simp [e, Unique.eq_default j, default_val, hw]
  · suffices M i j = algebraMap R A (w i p) * M p p * algebraMap R A (w p j) +
        ∑ s : {i : n // i ≠ p}, algebraMap R A (k.val i s) * d s * algebraMap R A (l.val s j) by
      simpa [e, Matrix.mul_apply, Matrix.diagonal_apply, default_val, GeneralLinearGroup.map]
    rw [← block_entry, ← hw p j]
    ring

end Matrix

namespace ValuationSubring

/-- Every nonempty finite matrix over a field `F` has an entry that `O`-divides all other entries
for any valuation subring `O : ValuationSubring F`. -/
theorem exists_pivot_dvd {m : Type u} [Finite m] [Nonempty m] {F : Type*} [Field F]
    (O : ValuationSubring F) (y : Matrix m m F) :
    ∃ ij₀ : m × m, ∀ ij : m × m, ∃ w : O, algebraMap O F w * y ij₀.1 ij₀.2 = y ij.1 ij.2 := by
  classical
  let : Fintype m := Fintype.ofFinite m
  obtain ⟨p⟩ := ‹Nonempty m›
  obtain ⟨ij₀, -, hij₀⟩ := Finset.exists_max_image Finset.univ
    (fun ij : m × m ↦ O.valuation (y ij.1 ij.2)) ⟨(p, p), Finset.mem_univ _⟩
  exact ⟨ij₀, fun ij ↦ (O.valuation_le_iff _ _).1 (hij₀ ij (Finset.mem_univ _))⟩

/-- **Diagonalization over a valuation subring.** For a valuation subring `O` of a field `F`,
every square matrix `y : Matrix n n F` factors as `k * diagonal d * k'` with `k, k' : GL n O`
mapped into `GL n F`. -/
theorem exists_mul_diagonal_mul {n : Type u} [Fintype n] [DecidableEq n] {F : Type*} [Field F]
    (O : ValuationSubring F) (y : Matrix n n F) :
    ∃ (k k' : GL n O) (d : n → F),
      y = (GeneralLinearGroup.map (algebraMap O F) k).val * diagonal d *
        (GeneralLinearGroup.map (algebraMap O F) k').val := by
  induction h : Fintype.card n generalizing n with
  | zero =>
    have : IsEmpty n := Fintype.card_eq_zero_iff.1 h
    exact ⟨1, 1, 0, Matrix.ext fun i ↦ IsEmpty.elim inferInstance i⟩
  | succ r ih =>
    have : Nonempty n := Fintype.card_pos_iff.1 (by omega)
    obtain ⟨p⟩ := ‹Nonempty n›
    obtain ⟨⟨i₀, j₀⟩, hij₀⟩ := O.exists_pivot_dvd y
    let a : GL n O := TauCeti.permutationGL (Equiv.swap p i₀)
    let b : GL n O := TauCeti.permutationGL (Equiv.swap p j₀)
    set M : Matrix n n F :=
      (GeneralLinearGroup.map (algebraMap O F) a).val * y *
        (GeneralLinearGroup.map (algebraMap O F) b).val with hM
    have hM_entry (i j : n) : M i j = y (Equiv.swap p i₀ i) (Equiv.swap p j₀ j) := by
      simp [hM, a, b, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, Matrix.mul_apply,
        Equiv.swap_apply_eq_iff]
    have hpivot (i j : n) : ∃ w : O, algebraMap O F w * M p p = M i j := by
      simpa only [hM_entry, Equiv.swap_apply_left] using hij₀ (Equiv.swap p i₀ i, Equiv.swap p j₀ j)
    choose w hw using hpivot
    obtain ⟨k, l, d, h_block⟩ :=
      ih ((M - of fun i : n ↦ algebraMap O F (w i p) • M p).toBlock (· ≠ p) (· ≠ p)) (by simp [h])
    obtain ⟨lower, upper, D, factor⟩ := M.exists_eq_mul_diagonal_mul_of_pivot_dvd hw h_block
    refine ⟨a⁻¹ * lower, upper * b⁻¹, D, ?_⟩
    simp only [map_mul, map_inv, Units.val_mul, Matrix.mul_assoc, Units.eq_inv_mul_iff_mul_eq]
    simpa only [← Matrix.mul_assoc, Units.eq_mul_inv_iff_mul_eq, hM] using factor

end ValuationSubring

end
