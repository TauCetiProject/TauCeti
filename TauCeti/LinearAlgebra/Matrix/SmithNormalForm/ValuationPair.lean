/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Data.Fintype.Order
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Diagonalization of square matrices over valuation pairs and valuation subrings

A subring `R` of a commutative ring `A` is a *valuation pair* (`Subring.IsValuationPair R`) if
for all `a b : A` there exists an idempotent `e : R` such that both `a` and `b` are `R`-multiples
of `a - e * (a - b) = (1 - e) * a + e * b`. Every `ValuationSubring F` of a field `F` satisfies
this property (`ValuationSubring.isValuationPair_toSubring`), as does a ring of integral adeles
inside the finite adeles.

Over any valuation pair `R ⊆ A`, every square matrix `y : Matrix n n A` factors as
`y = (map R.subtype k).val * diagonal d * (map R.subtype k').val` for some `k, k' : GL n R` and
`d : n → A` (`Subring.IsValuationPair.exists_eq_mul_diagonal_mul`). No divisibility chain among
the entries of `d` is asserted. In particular, every square matrix over a (not necessarily
discrete) valuation subring `O` of a field `F`, or over `F` itself, is diagonalized by two-sided
multiplication by `GL n O` (`ValuationSubring.exists_eq_mul_diagonal_mul` and
`ValuationSubring.exists_eq_mul_diagonal_mul_self`).

## Main definitions and results

* `Subring.IsValuationPair`: valuation-pair condition on a subring `R` of a commutative ring `A`.
* `Subring.IsValuationPair.top`: if `R ⊆ A` is a valuation pair, then `⊤ : Subring R` is a
  valuation pair.
* `IsIdempotentElem.cutGL`: the endomorphism `g ↦ e • g + (1 - e) • 1` of `GL n A` attached to an
  idempotent `e : A`, with characterizing lemma `IsIdempotentElem.val_cutGL`.
* `Subring.IsValuationPair.exists_eq_mul_diagonal_mul`: two-sided `GL n R`-diagonalization of any
  square matrix over `A`.
* `ValuationSubring.isValuationPair_toSubring`: every valuation subring of a field is a valuation
  pair.
* `ValuationSubring.exists_eq_mul_diagonal_mul` and
  `ValuationSubring.exists_eq_mul_diagonal_mul_self`: two-sided `GL n O`-diagonalization of square
  matrices over `F` and over `O`.

## References

* L. Alpöge and L. Sernau, Lean formalization of the generalized Riemann hypothesis for Dirichlet
  `L`-functions (`Lib/General/LinearAlgebra/IntegralLattices.lean`,
  `New.IsValuationPair.smith_normal_form`), <https://github.com/lsernau/grh-lean> (Apache 2.0).
* N. Bourbaki, *Commutative Algebra*, Chapter VI (valuation rings and finitely generated ideals).
-/

public section

open Matrix Submodule Fintype GeneralLinearGroup

namespace IsIdempotentElem

variable {A n : Type*} [CommRing A] [Fintype n] [DecidableEq n] {e : A}

/-- For an idempotent `e` of a commutative ring `A`, the endomorphism `g ↦ e • g + (1 - e) • 1`
of `GL n A`. -/
def cutGL (he : IsIdempotentElem e) : GL n A →* GL n A :=
  Units.map
    { toFun g := e • g + (1 - e) • 1
      map_one' := by simp
      map_mul' := by simp [he.eq, mul_add, add_mul, smul_smul, mul_sub, sub_mul] }

/-- Characterizing formula for the underlying matrix of `he.cutGL g`. -/
@[simp]
theorem val_cutGL (he : IsIdempotentElem e) (g : GL n A) :
    (he.cutGL g).val = e • g.val + (1 - e) • 1 := by
  rfl

/-- Patching two invertible matrices `c` and `d` along an idempotent `e` gives
`e • d + (1 - e) • c`. -/
theorem val_mul_cutGL_inv_mul (he : IsIdempotentElem e) (c d : GL n A) :
    (c * he.cutGL (c⁻¹ * d)).val = e • d.val + (1 - e) • c.val := by
  rw [Units.val_mul, val_cutGL]
  simp [mul_add, -Matrix.coe_units_inv]

end IsIdempotentElem

namespace Subring

section ValuationPair

variable {A : Type*} [CommRing A] (R : Subring A)

/-- A subring `R` of a commutative ring `A` is a valuation pair if for all `a b : A` there exists
an idempotent `e : R` such that `a` and `b` are `R`-multiples of `a - e * (a - b)`. -/
abbrev IsValuationPair : Prop :=
  ∀ a b : A, ∃ e : R, e.val * e = e ∧ R ∙ a ⊔ R ∙ b ≤ R ∙ (a - e * (a - b))

/-- If `R ⊆ A` is a valuation pair, then `R` is a valuation pair inside itself. -/
theorem IsValuationPair.top {R : Subring A} (hR : R.IsValuationPair) :
    (⊤ : Subring R).IsValuationPair := by
  intro a b
  obtain ⟨e, he, hle⟩ := hR a.val b.val
  refine ⟨⟨e, trivial⟩, Subtype.ext he, sup_le ((span_singleton_le_iff_mem _ _).2 ?_)
    ((span_singleton_le_iff_mem _ _).2 ?_)⟩
  · obtain ⟨r, hr⟩ := mem_span_singleton.1 (le_sup_left.trans hle (mem_span_singleton_self _))
    exact mem_span_singleton.2 ⟨⟨r, trivial⟩, Subtype.ext (by simpa [Subring.smul_def] using hr)⟩
  · obtain ⟨r, hr⟩ := mem_span_singleton.1 (le_sup_right.trans hle (mem_span_singleton_self _))
    exact mem_span_singleton.2 ⟨⟨r, trivial⟩, Subtype.ext (by simpa [Subring.smul_def] using hr)⟩

end ValuationPair

section Diagonalization

variable {A n : Type*} [CommRing A] {R : Subring A} [Fintype n] [DecidableEq n]

/-- For a valuation pair `R ⊆ A`, the `R`-submodules generated by the `(p, p)` entry of `a * y * b`
as `a, b` range over `GL n R` form a directed family. -/
private lemma IsValuationPair.directed_span_pivot (hR : R.IsValuationPair) (y : Matrix n n A)
    (p : n) :
    Directed (· ≤ ·) fun c : GL n R × GL n R ↦
      R ∙ ((GeneralLinearGroup.map R.subtype c.fst).val * y *
        (GeneralLinearGroup.map R.subtype c.snd).val) p p := by
  rintro ⟨c, c'⟩ ⟨d, d'⟩
  let B (a b : GL n R) : A :=
    ((GeneralLinearGroup.map R.subtype a).val * y * (GeneralLinearGroup.map R.subtype b).val) p p
  obtain ⟨e, he, h_le⟩ : ∃ e : R, e.val * e = e ∧
      R ∙ B c c' ⊔ R ∙ B d d' ≤ R ∙ (B c c' - e * (B c c' - B d d')) := hR _ _
  have he_idem : IsIdempotentElem e := Subtype.ext he
  let patch (a b : GL n R) : GL n R := a * he_idem.cutGL (a⁻¹ * b)
  have patch_val (a b : GL n R) : (GeneralLinearGroup.map R.subtype (patch a b)).val =
      e.val • (GeneralLinearGroup.map R.subtype b).val +
        (1 - e.val) • (GeneralLinearGroup.map R.subtype a).val := by
    change (patch a b).val.map R.subtype = _
    rw [show (patch a b).val = e • b.val + (1 - e) • a.val from he_idem.val_mul_cutGL_inv_mul a b]
    ext i j
    simp
  have patch_entry : B (patch c d) (patch c' d') = B c c' - e * (B c c' - B d d') := by
    simp only [B, patch_val, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul]
    linear_combination (B c c' - B c d' - B d c' + B d d') * he
  rw [← patch_entry, sup_le_iff] at h_le
  exact ⟨(patch c d, patch c' d'), h_le⟩

/-- Existence of a pivot: for a valuation pair `R ⊆ A`, every square matrix `y` can be transformed
by `GL n R` on both sides so that every entry is an `R`-multiple of the `(p, p)` entry. -/
private lemma IsValuationPair.exists_pivot_dvd (hR : R.IsValuationPair) (y : Matrix n n A)
    (p : n) :
    ∃ a b : GL n R, ∀ i j : n, ∃ w : R,
      w * ((GeneralLinearGroup.map R.subtype a).val * y *
          (GeneralLinearGroup.map R.subtype b).val) p p =
        ((GeneralLinearGroup.map R.subtype a).val * y *
          (GeneralLinearGroup.map R.subtype b).val) i j := by
  let swapGL (q : n) : GL n R :=
    ⟨(Equiv.swap p q).permMatrix R, (Equiv.swap p q).permMatrix R,
      by rw [← permMatrix_mul, Equiv.swap_mul_self, permMatrix_one],
      by rw [← permMatrix_mul, Equiv.swap_mul_self, permMatrix_one]⟩
  let B (c : GL n R × GL n R) : Matrix n n A :=
    (GeneralLinearGroup.map R.subtype c.fst).val * y * (GeneralLinearGroup.map R.subtype c.snd).val
  obtain ⟨c, hc⟩ : ∃ c : GL n R × GL n R,
      ∀ ij : n × n, R ∙ B (swapGL ij.fst, swapGL ij.snd) p p ≤ R ∙ B c p p :=
    (hR.directed_span_pivot y p).finite_le fun ij : n × n ↦ (swapGL ij.fst, swapGL ij.snd)
  have hswap (i j : n) : B (swapGL i, swapGL j) p p = y i j := by
    simp [B, swapGL, Equiv.Perm.permMatrix, Matrix.mul_apply,
      ← Equiv.eq_symm_apply, apply_ite Subtype.val]
  have y_mem (i j : n) : y i j ∈ R ∙ B c p p := by
    rw [← hswap i j]
    exact hc (i, j) (mem_span_singleton_self _)
  refine ⟨c.fst, c.snd, fun i j ↦ mem_span_singleton.1 ?_⟩
  change B c i j ∈ R ∙ B c p p
  rw [show B c i j = ∑ s : n, c.snd.val s j • ∑ r : n, c.fst.val i r • y r s by
    simp [B, Matrix.mul_apply, Subring.smul_def, mul_comm, Finset.mul_sum]]
  exact sum_smul_mem _ _ fun s _ ↦ sum_smul_mem _ _ fun r _ ↦ y_mem r s

/-- One elimination step: if every entry of `M` is an `R`-multiple of the pivot `M p p` and the
complementary block after clearing column `p` is diagonalized over `GL _ R`, then so is `M`. -/
private lemma exists_eq_mul_diagonal_mul_of_pivot_dvd {M : Matrix n n A} {p : n} {w : n → n → R}
    (hw : ∀ i j : n, w i j * M p p = M i j) {k l : GL {i : n // i ≠ p} R} {d : {i : n // i ≠ p} → A}
    (h_block : (M - of fun i : n ↦ w i p • M p).toBlock (· ≠ p) (· ≠ p) =
      (GeneralLinearGroup.map R.subtype k).val * diagonal d *
        (GeneralLinearGroup.map R.subtype l).val) :
    ∃ (lower upper : GL n R) (D : n → A),
      M = (GeneralLinearGroup.map R.subtype lower).val * diagonal D *
        (GeneralLinearGroup.map R.subtype upper).val := by
  let e : {i : n // i = p} ⊕ {i : n // i ≠ p} ≃ n := Equiv.sumCompl (· = p)
  let lower : GL n R := .mk'' (reindex e e (fromBlocks 1 0 (of fun i j ↦ w i j) k)) (by simp)
  let upper : GL n R := .mk'' (reindex e e (fromBlocks 1 (of fun i j ↦ w i j) 0 l)) (by simp)
  let D : n → A := Sum.elim (fun _ ↦ M p p) d ∘ e.symm
  have block_entry (i j : {i : n // i ≠ p}) :
      M i j - w i p * M p j = ∑ s : {i : n // i ≠ p}, k.val i s * d s * l.val s j := by
    simpa [↓mul_diagonal, Matrix.mul_apply, Subring.smul_def, GeneralLinearGroup.map_apply] using
      congrFun (congrFun h_block i) j
  have default_val : ((default : {i : n // i = p}) : n) = p := rfl
  refine ⟨lower, upper, D, (reindex e.symm e.symm).injective ?_⟩
  suffices M.submatrix e e =
      fromBlocks 1 0 ((of fun i j ↦ w i.val j.val).map R.subtype)
          (GeneralLinearGroup.map R.subtype k).val *
        diagonal (Sum.elim (fun _ : {i : n // i = p} ↦ M p p) d) *
        fromBlocks 1 ((of fun i j ↦ w i.val j.val).map R.subtype) 0
          (GeneralLinearGroup.map R.subtype l).val by
    simp [this, lower, upper, D, ← submatrix_mul_equiv _ _ _ e, fromBlocks_map, submatrix_map,
      Function.comp_assoc]
  rw [← fromBlocks_diagonal, fromBlocks_multiply, fromBlocks_multiply]
  ext (i | i) (j | j)
  · simp [e, Unique.eq_default, default_val]
  · simp [e, mul_comm (M p p), Unique.eq_default i, default_val, hw]
  · simp [e, Unique.eq_default j, default_val, hw]
  · suffices M i j = w i p * M p p * w p j +
        ∑ s : {i : n // i ≠ p}, k.val i s * d s * l.val s j by
      simpa [e, ↓mul_diagonal, Matrix.mul_apply, default_val, GeneralLinearGroup.map_apply]
    rw [← block_entry, ← hw p j]
    ring

/-- **Two-sided diagonalization over a valuation pair**: if `R ⊆ A` is a valuation pair, every
square matrix `y : Matrix n n A` factors as
`(GeneralLinearGroup.map R.subtype k).val * diagonal d * (GeneralLinearGroup.map R.subtype k').val`
for some `k, k' : GL n R` and `d : n → A`. No divisibility chain among the entries of `d` is
asserted. -/
theorem IsValuationPair.exists_eq_mul_diagonal_mul (hR : R.IsValuationPair) (y : Matrix n n A) :
    ∃ (k k' : GL n R) (d : n → A),
      y = (GeneralLinearGroup.map R.subtype k).val * diagonal d *
        (GeneralLinearGroup.map R.subtype k').val := by
  induction h : card n generalizing n with
  | zero => exact ⟨1, 1, 0, Matrix.ext fun i ↦ ((card_eq_zero_iff.1 h).false i).elim⟩
  | succ m ih =>
    obtain ⟨p⟩ : Nonempty n := card_pos_iff.1 (by omega)
    obtain ⟨a, b, pivot_dvd⟩ := hR.exists_pivot_dvd y p
    set M : Matrix n n A :=
      (GeneralLinearGroup.map R.subtype a).val * y * (GeneralLinearGroup.map R.subtype b).val
      with hM
    choose w hw using pivot_dvd
    obtain ⟨k, l, d, h_block⟩ :=
      ih ((M - of fun i : n ↦ w i p • M p).toBlock (· ≠ p) (· ≠ p)) (by simp [h])
    obtain ⟨lower, upper, D, factor⟩ := exists_eq_mul_diagonal_mul_of_pivot_dvd hw h_block
    refine ⟨a⁻¹ * lower, upper * b⁻¹, D, ?_⟩
    simp only [map_mul, map_inv, Units.val_mul, mul_assoc, Units.eq_inv_mul_iff_mul_eq]
    simpa only [← mul_assoc, Units.eq_mul_inv_iff_mul_eq, hM] using factor

end Diagonalization

end Subring

namespace ValuationSubring

variable {F n : Type*} [Field F]

/-- Every valuation subring `O` of a field `F` is a valuation pair inside `F`. -/
theorem isValuationPair_toSubring (O : ValuationSubring F) : O.toSubring.IsValuationPair := by
  intro a b
  have h_dvd : (∃ y ∈ O, a = b * y) ∨ ∃ y ∈ O, b = a * y := by
    by_cases ha : a = 0
    · exact Or.inl ⟨0, O.zero_mem, by simp [ha]⟩
    · by_cases hb : b = 0
      · exact Or.inr ⟨0, O.zero_mem, by simp [hb]⟩
      · rcases O.mem_or_inv_mem (a / b) with h | h
        · exact Or.inl ⟨a / b, h, by field_simp⟩
        · exact Or.inr ⟨(a / b)⁻¹, h, by field_simp⟩
  rcases h_dvd with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
  · refine ⟨1, by simp, sup_le ((span_singleton_le_iff_mem _ _).2 ?_)
      ((span_singleton_le_iff_mem _ _).2 ?_)⟩
    · exact mem_span_singleton.2 ⟨⟨y, hy⟩, by simp [Subring.smul_def]; ring⟩
    · exact mem_span_singleton.2 ⟨1, by simp⟩
  · refine ⟨0, by simp, sup_le ((span_singleton_le_iff_mem _ _).2 ?_)
      ((span_singleton_le_iff_mem _ _).2 ?_)⟩
    · exact mem_span_singleton.2 ⟨1, by simp⟩
    · exact mem_span_singleton.2 ⟨⟨y, hy⟩, by simp [Subring.smul_def]; ring⟩

/-- Every square matrix over a field `F` is diagonalized on both sides by `GL n O` for any
valuation subring `O` of `F`. -/
theorem exists_eq_mul_diagonal_mul [Fintype n] [DecidableEq n] (O : ValuationSubring F)
    (y : Matrix n n F) :
    ∃ (k k' : GL n O) (d : n → F),
      y = (map O.toSubring.subtype k).val * diagonal d * (map O.toSubring.subtype k').val :=
  O.isValuationPair_toSubring.exists_eq_mul_diagonal_mul y

/-- Every square matrix over a valuation subring `O` of a field `F` is diagonalized on both sides
by `GL n O`. -/
theorem exists_eq_mul_diagonal_mul_self [Fintype n] [DecidableEq n] (O : ValuationSubring F)
    (y : Matrix n n O) :
    ∃ (k k' : GL n O) (d : n → O), y = k.val * diagonal d * k'.val := by
  obtain ⟨k, k', d, h⟩ := O.isValuationPair_toSubring.top.exists_eq_mul_diagonal_mul y
  exact ⟨map (⊤ : Subring O).subtype k, map (⊤ : Subring O).subtype k', d, h⟩

end ValuationSubring
