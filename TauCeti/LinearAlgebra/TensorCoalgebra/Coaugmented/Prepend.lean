/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented.Grading
public import TauCeti.LinearAlgebra.TensorCoalgebra.Primitives
public import TauCeti.LinearAlgebra.TensorCoalgebra.Splice

/-!
# Prepending a letter to a possibly empty tensor word

`TauCeti.TensorWords.prepend` sends a letter `a` and a tensor word `y₁ ⋯ y_k`, the empty word
included, to the nonempty word `a y₁ ⋯ y_k`.  Its uncurried form is the concatenation map
`M ⊗ Tᶜ(M) → ReducedTensorWords R M` onto the reduced tensor words.  Through it, the cofree right
bar comodule `sA ⊗ Tᶜ(sA)` of an `A∞` algebra `A`, regarded as a right module over itself, is
compared with the reduced bar construction `ReducedTensorWords R A` of `A`.

On positive-length words it is `TauCeti.ReducedTensorWords.prepend`, and on the empty word it
is the single letter.  The remaining lemmas evaluate it on blocks of a tuple, as subwords or
splices, which is the form in which coderivations are expanded.

## Main definitions

* `TauCeti.TensorWords.prepend`: prepend a letter to a tensor word.

## Main results

* `TauCeti.TensorWords.prepend_of_tprod`: prepending conses the letter onto a pure tensor word.
* `TauCeti.TensorWords.prepend_one` and `TauCeti.TensorWords.prepend_reducedInclusion`: the empty
  and the positive-length cases.
* `TauCeti.TensorWords.prepend_subword` and `TauCeti.TensorWords.prepend_subword_eq_splice`:
  prepending to a block of a tuple.
* `TauCeti.TensorWords.deconcatenation_comp_reducedInclusion_comp_prepend`: deconcatenating a
  word with a prepended letter.
* `TauCeti.TensorWords.prepend_mem_gradedPiece` and
  `TauCeti.TensorWords.isHomogeneous_lift_prepend`: prepending adds total letter degrees.
* `TauCeti.TensorWords.subword_tail`: blocks of the tail of a tuple.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 4.
-/

public section

open scoped BigOperators DirectSum TensorProduct

universe uR uM

namespace TauCeti

namespace TensorWords

variable (R : Type uR) (M : Type uM) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- Prepend a letter to a tensor word: `a` and `y₁ ⋯ y_k` give the nonempty word `a y₁ ⋯ y_k`.
Uncurried, this is the concatenation map `M ⊗ Tᶜ(M) → ReducedTensorWords R M`. -/
noncomputable def prepend : M →ₗ[R] TensorWords R M →ₗ[R] ReducedTensorWords R M :=
  (DirectSum.toModule R ℕ (M →ₗ[R] ReducedTensorWords R M) fun k ↦
    ((TensorProduct.mk R (TensorPower R 1 M) (TensorPower R k M)).compr₂
        (ReducedTensorWords.of R M ⟨1 + k, by omega⟩ ∘ₗ
          (TensorPower.mulEquiv (R := R) (M := M)).toLinearMap) ∘ₗ
      (TauCeti.TensorPower.oneEquiv R M).symm.toLinearMap).flip).flip

variable {R M}

/-- A block of the tail of a tuple is the block one position further along the tuple. -/
theorem subword_tail {n : ℕ} (z : Fin (n + 1) → M) (a b : ℕ) :
    subword R (Fin.tail z) a b = subword R z (a + 1) b := by
  by_cases hab : a + b ≤ n
  · rw [subword_eq_of_tprod R _ hab, subword_eq_of_tprod R z (by omega)]
    exact of_tprod_congr R M fun j ↦ congrArg z (Fin.ext (by simp; omega))
  · rw [subword_eq_zero_of_lt_add R _ (by omega), subword_eq_zero_of_lt_add R z (by omega)]

/-- Prepending a letter to a pure tensor word conses it onto the letters. -/
theorem prepend_of_tprod (a : M) (k : ℕ) (y : Fin k → M) :
    prepend R M a (of R M k (PiTensorProduct.tprod R y)) =
      ReducedTensorWords.of R M ⟨k + 1, by omega⟩ (PiTensorProduct.tprod R (Fin.cons a y)) := by
  simp only [prepend, LinearMap.flip_apply, toModule_of, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearEquiv.coe_coe,
    TauCeti.TensorPower.oneEquiv_symm_apply, ← TensorPower.gMul_def, TensorPower.tprod_mul_tprod,
    Fin.append_left_eq_cons]
  exact ReducedTensorWords.of_tprod_congr R M _ (Nat.add_comm 1 k) fun _ ↦ rfl

/-- Prepending a letter to the empty word gives that letter as a word of length one. -/
@[simp]
theorem prepend_one (a : M) : prepend R M a 1 = ReducedTensorWords.ofLetter R M a := by
  rw [one_eq_of_zero, prepend_of_tprod, ReducedTensorWords.ofLetter_eq_of_tprod]
  exact ReducedTensorWords.of_tprod_congr R M _ rfl fun i ↦ by
    rw [Fin.fin_one_eq_zero i]
    rfl

/-- On words of positive length, prepending agrees with prepending in the reduced tensor words. -/
@[simp]
theorem prepend_reducedInclusion (a : M) (w : ReducedTensorWords R M) :
    prepend R M a (reducedInclusion R M w) = ReducedTensorWords.prepend R M a w := by
  have h : prepend R M a ∘ₗ reducedInclusion R M = ReducedTensorWords.prepend R M a := by
    refine ReducedTensorWords.linearMap_ext R M fun k y ↦ ?_
    rw [LinearMap.comp_apply, reducedInclusion_of, prepend_of_tprod,
      ReducedTensorWords.prepend_of_tprod]
  exact LinearMap.congr_fun h w

/-- Prepending the letter at position `a` to the (possibly empty) block after it extends the
block by that letter. -/
theorem prepend_subword {n : ℕ} (z : Fin n → M) {a : ℕ} (ha : a < n) (b : ℕ) :
    prepend R M (z ⟨a, ha⟩) (subword R z (a + 1) b) =
      ReducedTensorWords.subword R z a (b + 1) := by
  by_cases hab : a + 1 + b ≤ n
  · rw [subword_eq_of_tprod R z hab, prepend_of_tprod,
      ReducedTensorWords.subword_eq_of_tprod R z (Nat.succ_pos b) (by omega)]
    refine ReducedTensorWords.of_tprod_congr R M _ rfl fun i ↦ ?_
    induction i using Fin.cases with
    | zero => rfl
    | succ j =>
      simp only [Fin.cons_succ, Fin.cast_eq_self, Fin.val_succ]
      exact congrArg z (Fin.ext (by simp only; omega))
  · rw [subword_eq_zero_of_lt_add R z (by omega), map_zero,
      ReducedTensorWords.subword_eq_zero_of_lt_add R z (by omega)]

/-- Prepending a letter `e` to the block that follows the first `d` letters of a block replaces
those `d` letters by `e`. -/
theorem prepend_subword_eq_splice {n : ℕ} (z : Fin n → M) {a b d : ℕ} (hd : 0 < d)
    (hdb : d ≤ b) (hab : a + b ≤ n) (e : M) :
    prepend R M e (subword R z (a + d) (b - d)) =
      ReducedTensorWords.splice R z a b 0 d e := by
  rw [subword_eq_of_tprod R z (by omega), prepend_of_tprod,
    ReducedTensorWords.splice_eq_of_tprod R z e hd (by omega) hab]
  refine ReducedTensorWords.of_tprod_congr R M _ (by omega) fun i ↦ ?_
  induction i using Fin.cases with
  | zero => simp
  | succ j =>
    simp only [Fin.cons_succ, Fin.val_cast, Fin.val_succ]
    rw [dite_eq_right (by omega), dite_eq_right (by omega)]
    exact congrArg z (Fin.ext (by simp only; omega))

/-- Deconcatenating a word `a w` with a prepended letter cuts it either before `a`, or inside
`w` after `a`: if `Δ w = ∑ w₁ ⊗ w₂`, then `Δ (a w) = 1 ⊗ a w + ∑ a w₁ ⊗ w₂`. -/
theorem deconcatenation_comp_reducedInclusion_comp_prepend (a : M) :
    deconcatenation R M ∘ₗ reducedInclusion R M ∘ₗ prepend R M a =
      TensorProduct.mk R _ _ (1 : TensorWords R M) ∘ₗ reducedInclusion R M ∘ₗ prepend R M a +
        (reducedInclusion R M ∘ₗ prepend R M a).rTensor (TensorWords R M) ∘ₗ
          deconcatenation R M := by
  refine linearMap_ext R M fun k y ↦ ?_
  simp only [LinearMap.add_apply, LinearMap.comp_apply, TensorProduct.mk_apply]
  rw [prepend_of_tprod, reducedInclusion_of,
    of_tprod_eq_subword R (Fin.cons a y : Fin (k + 1) → M), deconcatenation_subword,
    of_tprod_eq_subword R y, deconcatenation_subword, map_sum, Finset.sum_range_succ',
    subword_length_zero R _ (Nat.zero_le _), add_comm]
  congr 1
  -- A cut after `j + 1` letters of `a y₁ ⋯ y_k` is `a` prepended to a cut after `j` letters of `y`.
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [LinearMap.rTensor_tmul, LinearMap.comp_apply, ← Fin.tail_cons (α := fun _ ↦ M) a y,
    subword_tail, subword_tail, Fin.tail_cons]
  have h := prepend_subword (R := R) (Fin.cons a y : Fin (k + 1) → M) (a := 0) (Nat.succ_pos k) j
  rw [Fin.zero_eta, Fin.cons_zero] at h
  rw [h, reducedInclusion_subword R _ (Nat.succ_pos j)]
  congr 2
  omega

end TensorWords

namespace TensorWords

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommGroup M] [Module R M]

/-- Prepending a letter of degree `p` to a word of total degree `D` gives a word of total degree
`p + D`. -/
theorem prepend_mem_gradedPiece {G : InternalGrading R M} {p D : ℤ} {a : M}
    (ha : a ∈ G.piece p) {w : TensorWords R M} (hw : w ∈ gradedPiece G D) :
    prepend R M a w ∈ ReducedTensorWords.gradedPiece G (p + D) := by
  refine gradedPiece_induction
    (motive := fun w ↦ prepend R M a w ∈ ReducedTensorWords.gradedPiece G (p + D)) hw
    ?_ (by rw [map_zero]; exact zero_mem _) ?_ ?_
  · intro k 𝒟 y hy hD
    rw [prepend_of_tprod, ← hD, ← Fin.sum_cons p 𝒟]
    refine ReducedTensorWords.mem_gradedPiece_of_tprod G _ _ _ fun i ↦ ?_
    induction i using Fin.cases with
    | zero => simpa only [Fin.cons_zero] using ha
    | succ j => simpa only [Fin.cons_succ] using hy j
  · intro u v _ _ hu hv
    rw [map_add]
    exact add_mem hu hv
  · intro c u _ hu
    rw [map_smul]
    exact Submodule.smul_mem _ _ hu

/-- Uncurried prepending preserves total degrees: it is homogeneous of degree zero from the
tensor-product grading of `M ⊗ Tᶜ(M)` to the total-letter-degree grading of the reduced words. -/
theorem isHomogeneous_lift_prepend (G : InternalGrading R M) :
    LinearMap.IsHomogeneous (TensorProduct.lift (prepend R M))
      (G.tensorProduct (grading G)).piece (ReducedTensorWords.gradedPiece G) 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro p z hz
  rw [InternalGrading.tensorProduct_piece_eq_iSup] at hz
  refine (iSup_le fun q ↦ Submodule.map₂_le.2 fun x hx w hw ↦ ?_ :
    _ ≤ (ReducedTensorWords.gradedPiece G (p + 0)).comap _) hz
  rw [TensorProduct.mk_apply, Submodule.mem_comap, TensorProduct.lift.tmul, add_zero]
  rw [grading_piece] at hw
  simpa only [add_sub_cancel] using prepend_mem_gradedPiece hx hw

end TensorWords

end TauCeti
