/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Cofree
public import TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented.Prepend

/-!
# Concatenation of tensor words

For a module `X`, `TauCeti.TensorWords.tmulConcat` sends `x : X` to the linear map
`A ⊗ Tᶜ(A) → X ⊗ Tᶜ(A)`, `y ⊗ w ↦ x ⊗ y w`, where `y w` is the word `w` with the letter `y`
prepended.  On cofree bar comodules `X ⊗ Tᶜ(A)` it is the map through which representable
`A∞` modules are compared with the underlying complex of a module.

`TauCeti.TensorWords.concatLetter` concatenates two words around a letter,
`w ⊗ x ⊗ v ↦ w x v`, using the multiplication of the tensor algebra.  It maps the cofree bar
bicomodule `Tᶜ(A) ⊗ A ⊗ Tᶜ(A)` to the nonempty words, and it is the map through which the diagonal
`A∞` bimodule of an `A∞` algebra is compared with its bar construction.  Its evaluations on blocks
of one ambient tuple are recorded in the `subword` and `splice` vocabulary of the bar
construction.

## Main definitions

* `TauCeti.TensorWords.tmulConcat`: concatenation behind a fixed first factor.
* `TauCeti.TensorWords.concatLetter`: concatenation of two words around a letter.

## Main results

* `TauCeti.TensorWords.cofreeLift_comp_tmulConcat`: the cofree lift of a linear map after
  concatenation splits into the cut before the first letter and the cofree lift of the
  concatenated map.
* `TauCeti.TensorWords.isHomogeneous_tmulConcat`: concatenation behind an element of degree `q`
  raises the total degree by `q`.
* `TauCeti.TensorWords.concatLetter_of_tprod`: concatenation around a letter appends the letter
  tuples.
* `TauCeti.TensorWords.concatLetter_subword`, `TauCeti.TensorWords.concatLetter_eq_splice`,
  `TauCeti.TensorWords.concatLetter_reducedInclusion_splice_left` and
  `TauCeti.TensorWords.concatLetter_reducedInclusion_splice_right`: concatenating consecutive
  blocks of a tuple, one of which may carry a collapsed subblock, gives the corresponding block or
  spliced block.
* `TauCeti.TensorWords.isHomogeneous_concatLetter`: concatenation around a letter preserves total
  degrees.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 4.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe uR uA uX uN

attribute [local instance] Comodule.cofree

namespace TensorWords

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]

variable (R A) in
/-- Concatenation after a fixed first factor: `x` sends `y ⊗ w` to `x ⊗ y w`, where `y w` is the
word `w` with the letter `y` prepended. -/
noncomputable def tmulConcat (X : Type uX) [AddCommGroup X] [Module R X] :
    X →ₗ[R] A ⊗[R] TensorWords R A →ₗ[R] X ⊗[R] TensorWords R A :=
  (TensorProduct.mk R X (TensorWords R A)).compl₂
    (reducedInclusion R A ∘ₗ TensorProduct.lift (prepend R A))

variable {X : Type uX} [AddCommGroup X] [Module R X]

/-- Concatenation behind `x` applies prepending, followed by the inclusion of the nonempty words,
behind `x`. -/
theorem tmulConcat_apply (x : X) (z : A ⊗[R] TensorWords R A) :
    tmulConcat R A X x z = x ⊗ₜ[R] reducedInclusion R A (TensorProduct.lift (prepend R A) z) :=
  (rfl)

/-- Concatenation behind `x` sends `y ⊗ w` to `x ⊗ y w`. -/
@[simp]
theorem tmulConcat_tmul (x : X) (y : A) (w : TensorWords R A) :
    tmulConcat R A X x (y ⊗ₜ[R] w) = x ⊗ₜ[R] reducedInclusion R A (prepend R A y w) :=
  (rfl)

/-- The cofree lift of `φ` after concatenation behind `z`: the cut before the first letter of the
concatenated word gives `φ (z ⊗ 1)` in front of the whole word, and every other cut falls inside
the concatenated word. -/
theorem cofreeLift_comp_tmulConcat {N : Type uN} [AddCommGroup N] [Module R N]
    (φ : X ⊗[R] TensorWords R A →ₗ[R] N) (z : X) :
    (Comodule.Hom.cofreeLift (C := TensorWords R A) φ).toLinearMap ∘ₗ tmulConcat R A X z =
      tmulConcat R A N (φ (z ⊗ₜ[R] 1)) +
        (Comodule.Hom.cofreeLift (C := TensorWords R A)
          (φ ∘ₗ tmulConcat R A X z)).toLinearMap := by
  refine TensorProduct.ext' fun y w ↦ ?_
  have hΔ := deconcatenation_reducedInclusion_prepend (R := R) y w
  simp only [LinearMap.comp_apply, LinearMap.add_apply, tmulConcat_tmul,
    Comodule.Hom.cofreeLift_toLinearMap, Comodule.cofree_coact_tmul, comul_eq_deconcatenation]
  rw [hΔ]
  simp only [TensorProduct.tmul_add, map_add, TensorProduct.assoc_symm_tmul,
    LinearMap.rTensor_tmul]
  congr 1
  induction deconcatenation R A w using TensorProduct.inductionOn with
  | tmul u v => simp
  | add s t hs ht => simp only [map_add, TensorProduct.tmul_add, hs, ht]

/-- Concatenation behind an element of degree `q` raises the total degree by `q`. -/
theorem isHomogeneous_tmulConcat (G : InternalGrading R A) (H : InternalGrading R X) {q : ℤ}
    {x : X} (hx : x ∈ H.piece q) :
    LinearMap.IsHomogeneous (tmulConcat R A X x) (G.tensorProduct (grading G)).piece
      (H.tensorProduct (grading G)).piece q := by
  rw [LinearMap.isHomogeneous_def]
  intro d z hz
  have hc := (isHomogeneous_lift_prepend G).map_mem hz
  rw [add_zero] at hc
  have hw : reducedInclusion R A (TensorProduct.lift (prepend R A) z) ∈ (grading G).piece d := by
    rw [grading_piece]
    exact mem_gradedPiece_of_reducedInclusion hc
  rw [add_comm]
  exact InternalGrading.tmul_mem_tensorProduct H (grading G) hx hw

end TensorWords

namespace TensorWords

section ConcatLetter

variable {R : Type uR} {A : Type uA} [CommSemiring R] [AddCommMonoid A] [Module R A]

variable (R A) in
/-- Concatenation of two words around a letter: `w ⊗ x ⊗ v ↦ w x v`, computed with the
multiplication of the tensor algebra.  The result is a nonempty word. -/
noncomputable def concatLetter :
    (TensorWords R A ⊗[R] A) ⊗[R] TensorWords R A →ₗ[R] ReducedTensorWords R A :=
  reducedProjection R A ∘ₗ LinearMap.mul' R (TensorWords R A) ∘ₗ
    TensorProduct.map LinearMap.id (reducedInclusion R A ∘ₗ TensorProduct.lift (prepend R A)) ∘ₗ
      (TensorProduct.assoc R _ _ _).toLinearMap

/-- Concatenation around a letter multiplies the first word with the second word prepended by
the letter. -/
theorem concatLetter_tmul (w : TensorWords R A) (x : A) (v : TensorWords R A) :
    concatLetter R A ((w ⊗ₜ x) ⊗ₜ v) =
      reducedProjection R A (w * reducedInclusion R A (prepend R A x v)) := by
  simp [concatLetter]

/-- Concatenation around a letter appends the letter tuples: `w ⊗ x ⊗ v` becomes the word of
`Fin.append w (Fin.cons x v)`. -/
theorem concatLetter_of_tprod {l n : ℕ} (w : Fin l → A) (x : A) (v : Fin n → A) :
    concatLetter R A ((of R A l (PiTensorProduct.tprod R w) ⊗ₜ x) ⊗ₜ
        of R A n (PiTensorProduct.tprod R v)) =
      ReducedTensorWords.of R A ⟨l + (n + 1), by omega⟩
        (PiTensorProduct.tprod R (Fin.append w (Fin.cons x v))) := by
  rw [concatLetter_tmul, prepend_of_tprod, reducedInclusion_of, of_def, of_def,
    DirectSum.lof_eq_of, DirectSum.lof_eq_of, DirectSum.of_mul_of, TensorPower.tprod_mul_tprod,
    ← DirectSum.lof_eq_of R, ← of_def, reducedProjection_of_of_pos R A (by simp)]

/-- Concatenation around a letter, with the letters of the result given by position. -/
private theorem concatLetter_of_tprod_eq {l n N : ℕ} (w : Fin l → A) (x : A) (v : Fin n → A)
    (hN : l + 1 + n = N) (u : Fin N → A)
    (hu : ∀ i : Fin N, u i =
      if h : i.1 < l then w ⟨i, h⟩ else if _ : i.1 = l then x else v ⟨i - (l + 1), by omega⟩) :
    concatLetter R A ((of R A l (PiTensorProduct.tprod R w) ⊗ₜ x) ⊗ₜ
        of R A n (PiTensorProduct.tprod R v)) =
      ReducedTensorWords.of R A ⟨N, by omega⟩ (PiTensorProduct.tprod R u) := by
  rw [concatLetter_of_tprod]
  refine ReducedTensorWords.of_tprod_congr R A _ (by omega) fun i ↦ ?_
  rw [hu]
  simp only [Fin.val_cast]
  induction i using Fin.addCases with
  | left i => simp [Fin.append_left, i.isLt]
  | right j =>
    rw [Fin.append_right]
    induction j using Fin.cases with
    | zero => simp
    | succ k =>
      simp only [Fin.cons_succ, Fin.val_natAdd, Fin.val_succ]
      rw [dite_eq_right (by omega), dite_eq_right (by omega)]
      exact congrArg v (Fin.ext (by simp; omega))

/-- Concatenating the block of length `l` at `a`, the letter after it, and the block of length
`k` after that letter gives the block of length `l + 1 + k` at `a`. -/
theorem concatLetter_subword {N : ℕ} (y : Fin N → A) {a l k : ℕ} (h : a + l + 1 + k ≤ N) :
    concatLetter R A ((subword R y a l ⊗ₜ y ⟨a + l, by omega⟩) ⊗ₜ subword R y (a + l + 1) k) =
      ReducedTensorWords.subword R y a (l + 1 + k) := by
  rw [subword_eq_of_tprod R y (by omega), subword_eq_of_tprod R y h,
    ReducedTensorWords.subword_eq_of_tprod R y (by omega) (by omega)]
  refine concatLetter_of_tprod_eq _ _ _ rfl _ fun i ↦ ?_
  split_ifs
  · rfl
  · exact congrArg y (Fin.ext (by simp only; omega))
  · exact congrArg y (Fin.ext (by simp only; omega))

/-- Concatenating the block of length `j` at `a`, a letter `e`, and the block of length `k` that
starts `d` letters after the first block ends replaces those `d` letters by `e`. -/
theorem concatLetter_eq_splice {N : ℕ} (y : Fin N → A) {a j d k : ℕ} (e : A) (hd : 0 < d)
    (h : a + j + d + k ≤ N) :
    concatLetter R A ((subword R y a j ⊗ₜ e) ⊗ₜ subword R y (a + j + d) k) =
      ReducedTensorWords.splice R y a (j + d + k) j d e := by
  rw [subword_eq_of_tprod R y (by omega), subword_eq_of_tprod R y h,
    ReducedTensorWords.splice_eq_of_tprod R y e hd (by omega) (by omega)]
  dsimp only
  refine concatLetter_of_tprod_eq _ _ _ (by omega) _ fun i ↦ ?_
  split_ifs <;>
    first | rfl | omega | exact congrArg y (Fin.ext (by simp only; omega))

/-- Concatenating a spliced block of length `l` at `a`, the letter after it, and the block of
length `k` after that letter gives the spliced block of length `l + 1 + k` at `a`, provided the
collapsed subblock lies inside the first block. -/
theorem concatLetter_reducedInclusion_splice_left {N : ℕ} (y : Fin N → A) {a l p d k : ℕ}
    (e : A) (hpd : p + d ≤ l) (h : a + l + 1 + k ≤ N) :
    concatLetter R A ((reducedInclusion R A (ReducedTensorWords.splice R y a l p d e) ⊗ₜ
        y ⟨a + l, by omega⟩) ⊗ₜ subword R y (a + l + 1) k) =
      ReducedTensorWords.splice R y a (l + 1 + k) p d e := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  rw [ReducedTensorWords.splice_eq_of_tprod R y e hd hpd (by omega), reducedInclusion_of,
    subword_eq_of_tprod R y h,
    ReducedTensorWords.splice_eq_of_tprod R y e hd (by omega) (by omega)]
  dsimp only
  refine concatLetter_of_tprod_eq _ _ _ (by omega) _ fun i ↦ ?_
  split_ifs <;>
    first | rfl | omega | exact congrArg y (Fin.ext (by simp only; omega))

/-- Concatenating the block of length `l` at `a`, the letter after it, and a spliced block of
length `k` after that letter gives the spliced block of length `l + 1 + k` at `a`, with the
collapsed subblock moved `l + 1` positions to the right. -/
theorem concatLetter_reducedInclusion_splice_right {N : ℕ} (y : Fin N → A) {a l p d k : ℕ}
    (e : A) (h : a + l + 1 + k ≤ N) :
    concatLetter R A ((subword R y a l ⊗ₜ y ⟨a + l, by omega⟩) ⊗ₜ
        reducedInclusion R A (ReducedTensorWords.splice R y (a + l + 1) k p d e)) =
      ReducedTensorWords.splice R y a (l + 1 + k) (l + 1 + p) d e := by
  by_cases hfit : 0 < d ∧ p + d ≤ k
  · obtain ⟨hd, hpd⟩ := hfit
    rw [ReducedTensorWords.splice_eq_of_tprod R y e hd hpd h, reducedInclusion_of,
      subword_eq_of_tprod R y (by omega),
      ReducedTensorWords.splice_eq_of_tprod R y e hd (by omega) (by omega)]
    dsimp only
    refine concatLetter_of_tprod_eq _ _ _ (by omega) _ fun i ↦ ?_
    dsimp only
    split_ifs <;>
      first | rfl | omega | exact congrArg y (Fin.ext (by simp only; omega))
  · rw [ReducedTensorWords.splice_eq_zero_of_not_fits R y e hfit, map_zero,
      TensorProduct.tmul_zero, map_zero,
      ReducedTensorWords.splice_eq_zero_of_not_fits R y e (by omega)]

end ConcatLetter

section Grading

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]

/-- Concatenating words of total degrees `D` and `E` around a letter of degree `p` gives a word
of total degree `D + p + E`. -/
theorem concatLetter_mem_gradedPiece {G : InternalGrading R A} {D p E : ℤ}
    {w v : TensorWords R A} {x : A} (hw : w ∈ gradedPiece G D) (hx : x ∈ G.piece p)
    (hv : v ∈ gradedPiece G E) :
    concatLetter R A ((w ⊗ₜ x) ⊗ₜ v) ∈ ReducedTensorWords.gradedPiece G (D + p + E) := by
  refine gradedPiece_induction
    (motive := fun w ↦ concatLetter R A ((w ⊗ₜ x) ⊗ₜ v) ∈
      ReducedTensorWords.gradedPiece G (D + p + E)) hw ?_ ?_ ?_ ?_
  · intro l 𝒟 w hw hD
    refine gradedPiece_induction
      (motive := fun v ↦ concatLetter R A ((of R A l (PiTensorProduct.tprod R w) ⊗ₜ x) ⊗ₜ v) ∈
        ReducedTensorWords.gradedPiece G (D + p + E)) hv ?_ ?_ ?_ ?_
    · intro n ℰ v hv hE
      have hsum : ∑ i, Fin.append 𝒟 (Fin.cons p ℰ) i = ∑ i, 𝒟 i + ∑ i, Fin.cons p ℰ i := by
        rw [Fin.sum_univ_add]
        simp only [Fin.append_left, Fin.append_right]
      rw [concatLetter_of_tprod, ← hD, ← hE, add_assoc, ← Fin.sum_cons p ℰ, ← hsum]
      refine ReducedTensorWords.mem_gradedPiece_of_tprod G _ _ _ fun i ↦ ?_
      induction i using Fin.addCases with
      | left i => simpa only [Fin.append_left] using hw i
      | right j =>
        induction j using Fin.cases with
        | zero => simpa only [Fin.append_right, Fin.cons_zero] using hx
        | succ k => simpa only [Fin.append_right, Fin.cons_succ] using hv k
    · rw [TensorProduct.tmul_zero, map_zero]
      exact zero_mem _
    · intro u u' _ _ hu hu'
      rw [TensorProduct.tmul_add, map_add]
      exact add_mem hu hu'
    · intro c u _ hu
      rw [TensorProduct.tmul_smul, map_smul]
      exact Submodule.smul_mem _ _ hu
  · rw [TensorProduct.zero_tmul, TensorProduct.zero_tmul, map_zero]
    exact zero_mem _
  · intro u u' _ _ hu hu'
    rw [TensorProduct.add_tmul, TensorProduct.add_tmul, map_add]
    exact add_mem hu hu'
  · intro c u _ hu
    rw [← TensorProduct.smul_tmul', ← TensorProduct.smul_tmul', map_smul]
    exact Submodule.smul_mem _ _ hu

/-- Concatenation around a letter preserves total degrees: it is homogeneous of degree zero from
the tensor-product grading of `Tᶜ(A) ⊗ A ⊗ Tᶜ(A)` to the total-letter-degree grading of the
reduced words. -/
theorem isHomogeneous_concatLetter (G : InternalGrading R A) :
    LinearMap.IsHomogeneous (concatLetter R A)
      (((grading G).tensorProduct G).tensorProduct (grading G)).piece
      (ReducedTensorWords.gradedPiece G) 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro d z hz
  rw [InternalGrading.tensorProduct_piece_eq_iSup] at hz
  refine (iSup_le fun q ↦ Submodule.map₂_le.2 fun y hy v hv ↦ ?_ :
    _ ≤ (ReducedTensorWords.gradedPiece G (d + 0)).comap _) hz
  rw [TensorProduct.mk_apply, Submodule.mem_comap, add_zero]
  rw [InternalGrading.tensorProduct_piece_eq_iSup] at hy
  refine (iSup_le fun r ↦ Submodule.map₂_le.2 fun w hw x hx ↦ ?_ :
    _ ≤ (ReducedTensorWords.gradedPiece G d).comap
      (concatLetter R A ∘ₗ (TensorProduct.mk R _ _).flip v)) hy
  rw [TensorProduct.mk_apply, Submodule.mem_comap, LinearMap.comp_apply, LinearMap.flip_apply,
    TensorProduct.mk_apply]
  rw [grading_piece] at hw hv
  simpa only [add_sub_cancel] using concatLetter_mem_gradedPiece hw hx hv

end Grading

end TensorWords

end TauCeti
