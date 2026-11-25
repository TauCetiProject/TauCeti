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

Its composite with the inclusion of the reduced words is the endomorphism
`TauCeti.TensorWords.cons x` of all tensor words.  Every pure tensor word is either the empty word
or a letter followed by a shorter pure word, and the pure words span the tensor words.  This gives
an induction principle and a recursor `TauCeti.TensorWords.consRec` for linear maps out of tensor
words.

## Main definitions

* `TauCeti.TensorWords.prepend`: prepend a letter to a tensor word.
* `TauCeti.TensorWords.cons`: prepend a letter, as an endomorphism of tensor words.
* `TauCeti.TensorWords.consRec`: linear maps out of tensor words by recursion on the first letter.

## Main results

* `TauCeti.TensorWords.prepend_of_tprod`: prepending conses the letter onto a pure tensor word.
* `TauCeti.TensorWords.prepend_one` and `TauCeti.TensorWords.prepend_reducedInclusion`: the empty
  and the positive-length cases.
* `TauCeti.TensorWords.prepend_subword` and `TauCeti.TensorWords.prepend_subword_eq_splice`:
  prepending to a block of a tuple.
* `TauCeti.TensorWords.prepend_mem_gradedPiece` and
  `TauCeti.TensorWords.isHomogeneous_lift_prepend`: prepending adds total letter degrees.
* `TauCeti.TensorWords.subword_tail`: blocks of the tail of a tuple.
* `TauCeti.TensorWords.cons_induction`, `TauCeti.TensorWords.linearMap_ext_cons` and
  `TauCeti.TensorWords.linearMap_ext_cons'`: induction on the first letter.
* `TauCeti.TensorWords.deconcatenation_cons` and `TauCeti.TensorWords.deconcatenation_cons_pow`:
  the cuts of a word starting with given letters.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 4.
-/

public section

open scoped BigOperators DirectSum TensorProduct

universe uR uM uN

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
    (hdb : d ≤ b) (e : M) :
    prepend R M e (subword R z (a + d) (b - d)) =
      ReducedTensorWords.splice R z a b 0 d e := by
  by_cases hab : a + b ≤ n
  swap
  · rw [subword_eq_zero_of_lt_add R z (by omega), map_zero,
      ReducedTensorWords.splice_eq_zero_of_length_lt_add R z e (by omega)]
  rw [subword_eq_of_tprod R z (by omega), prepend_of_tprod,
    ReducedTensorWords.splice_eq_of_tprod R z e hd (by omega) hab]
  refine ReducedTensorWords.of_tprod_congr R M _ (by omega) fun i ↦ ?_
  induction i using Fin.cases with
  | zero => simp
  | succ j =>
    simp only [Fin.cons_succ, Fin.val_cast, Fin.val_succ]
    rw [dite_eq_right (by omega), dite_eq_right (by omega)]
    exact congrArg z (Fin.ext (by simp only; omega))

/-! ### Prepending a letter as an endomorphism -/

variable {N : Type uN} [AddCommMonoid N] [Module R N]

variable (R M) in
/-- Prepend a letter to a tensor word, as an endomorphism of tensor words:
`cons x (y₁ ⋯ yₖ) = x y₁ ⋯ yₖ`. -/
noncomputable def cons : M →ₗ[R] TensorWords R M →ₗ[R] TensorWords R M :=
  (prepend R M).compr₂ (reducedInclusion R M)

theorem cons_apply (x : M) (w : TensorWords R M) :
    cons R M x w = reducedInclusion R M (prepend R M x w) :=
  (rfl)

/-- Prepending a letter to a pure tensor word conses it onto the letters. -/
theorem cons_of_tprod (x : M) {n : ℕ} (y : Fin n → M) :
    cons R M x (of R M n (PiTensorProduct.tprod R y)) =
      of R M (n + 1) (PiTensorProduct.tprod R (Fin.cons x y)) := by
  rw [cons_apply, prepend_of_tprod, reducedInclusion_of]

/-- Prepending a letter to the empty word gives the one-letter word. -/
theorem cons_one (x : M) :
    cons R M x 1 = reducedInclusion R M (ReducedTensorWords.ofLetter R M x) := by
  rw [cons_apply, prepend_one]

/-- The word `a ⋯ a` of length `n`. -/
theorem cons_pow_apply_one_eq_of (a : M) (n : ℕ) :
    (cons R M a ^ n) 1 = of R M n (PiTensorProduct.tprod R fun _ ↦ a) := by
  induction n with
  | zero =>
    rw [pow_zero, one_apply_eq_self, one_eq_of_zero]
    exact of_tprod_congr R M fun i ↦ i.elim0
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, ih, cons_of_tprod]
    exact of_tprod_congr R M fun i ↦ Fin.cases rfl (fun _ ↦ rfl) i

/-- The one-letter word `x`. -/
theorem cons_one_eq_of (x : M) : cons R M x 1 = of R M 1 (PiTensorProduct.tprod R ![x]) := by
  rw [one_eq_of_zero, cons_of_tprod]
  exact of_tprod_congr R M fun i ↦ Fin.cases rfl (fun j ↦ j.elim0) i

/-- A word starting with a letter has zero counit. -/
@[simp]
theorem counit_cons (x : M) (w : TensorWords R M) : counit R M (cons R M x w) = 0 :=
  counit_reducedInclusion R M _

/-- Cutting `x w` either cuts before `x` or cuts `w` and prepends `x` to the left half. -/
theorem deconcatenation_cons (x : M) (w : TensorWords R M) :
    deconcatenation R M (cons R M x w) =
      (1 : TensorWords R M) ⊗ₜ[R] cons R M x w +
        (cons R M x).rTensor (TensorWords R M) (deconcatenation R M w) := by
  have h : deconcatenation R M ∘ₗ cons R M x =
      TensorProduct.mk R _ _ (1 : TensorWords R M) ∘ₗ cons R M x +
        (cons R M x).rTensor (TensorWords R M) ∘ₗ deconcatenation R M := by
    refine linearMap_ext R M fun n y ↦ ?_
    set z : Fin (n + 1) → M := Fin.cons x y with hz
    have hy : of R M n (PiTensorProduct.tprod R y) = subword R z 1 n := by
      rw [of_tprod_eq_subword, ← subword_tail, hz, Fin.tail_cons]
    have ha : z ⟨0, Nat.succ_pos n⟩ = x := Fin.cons_zero _ _
    have hp (k : ℕ) : reducedInclusion R M (prepend R M x (subword R z 1 k)) =
        subword R z 0 (k + 1) := by
      have h := prepend_subword (R := R) z (a := 0) (Nat.succ_pos n) k
      rw [Nat.zero_add, ha] at h
      rw [h, reducedInclusion_subword R z (Nat.succ_pos k)]
    simp only [LinearMap.comp_apply, LinearMap.add_apply, TensorProduct.mk_apply, cons_apply]
    rw [hy, hp, deconcatenation_subword,
      deconcatenation_subword, map_sum, Finset.sum_range_succ', subword_length_zero R z
        (Nat.zero_le _), add_comm]
    congr 1
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [Finset.mem_range] at hk
    rw [LinearMap.rTensor_tmul, cons_apply, hp]
    congr 2 <;> omega
  exact LinearMap.congr_fun h w

/-- Mapping a word starting with `x` gives a word starting with the image of `x`. -/
@[simp]
theorem map_cons (f : M →ₗ[R] N) (x : M) (w : TensorWords R M) :
    map f (cons R M x w) = cons R N (f x) (map f w) := by
  have h : map f ∘ₗ cons R M x = cons R N (f x) ∘ₗ map f := by
    refine linearMap_ext R M fun n y ↦ ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, cons_of_tprod, map_of_tprod, map_of_tprod,
      cons_of_tprod]
    exact of_tprod_congr R N fun i ↦ Fin.cases rfl (fun _ ↦ rfl) i
  exact LinearMap.congr_fun h w

/-- Mapping the iterated prepending of a letter. -/
theorem map_cons_pow (f : M →ₗ[R] N) (x : M) (k : ℕ) (w : TensorWords R M) :
    map f ((cons R M x ^ k) w) = (cons R N (f x) ^ k) (map f w) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_apply_eq_comp, map_cons, ih, pow_succ', mul_apply_eq_comp]

/-- **Induction on the first letter.**  A property of tensor words holding for the empty word and
preserved by prepending letters holds for every pure tensor word. -/
theorem cons_induction {motive : TensorWords R M → Prop} (one : motive 1)
    (cons : ∀ x w, motive w → motive (cons R M x w)) {n : ℕ} (y : Fin n → M) :
    motive (of R M n (PiTensorProduct.tprod R y)) := by
  induction n with
  | zero =>
    rw [Subsingleton.elim y fun i ↦ i.elim0, ← one_eq_of_zero]
    exact one
  | succ n ih =>
    rw [← Fin.cons_self_tail y, ← cons_of_tprod]
    exact cons _ _ (ih _)

/-- Two families of linear maps out of tensor words agree if they agree on the empty word and
agreement on a word implies agreement after prepending any letter. -/
theorem linearMap_ext_cons {ι : Type*} {f g : ι → TensorWords R M →ₗ[R] N}
    (one : ∀ i, f i 1 = g i 1)
    (cons : ∀ x w, (∀ i, f i w = g i w) → ∀ i, f i (cons R M x w) = g i (cons R M x w)) (i : ι) :
    f i = g i :=
  linearMap_ext R M fun _ y ↦
    cons_induction (motive := fun w ↦ ∀ i, f i w = g i w) one cons y i

/-- Two linear maps out of tensor words agree if they agree on the empty word and agreement on a
word implies agreement after prepending any letter. -/
theorem linearMap_ext_cons' {f g : TensorWords R M →ₗ[R] N} (one : f 1 = g 1)
    (cons : ∀ x w, f w = g w → f (cons R M x w) = g (cons R M x w)) : f = g :=
  linearMap_ext_cons (ι := Unit) (f := fun _ ↦ f) (g := fun _ ↦ g) (fun _ ↦ one)
    (fun x w hw _ ↦ cons x w (hw ())) ()

/-! ### Recursion on the first letter -/

/-- The recursion of `consRec` on the words of a fixed length. -/
private noncomputable def consRecAux (e : N) (S : M →ₗ[R] TensorWords R M →ₗ[R] N)
    (Θ : M →ₗ[R] N →ₗ[R] N) : (n : ℕ) → TensorPower R n M →ₗ[R] N
  | 0 => PiTensorProduct.lift (MultilinearMap.constOfIsEmpty (RingHom.id R) _ e)
  | n + 1 => PiTensorProduct.lift <| LinearMap.uncurryLeft
      { toFun x := (S x ∘ₗ of R M n + Θ x ∘ₗ consRecAux e S Θ n).compMultilinearMap
          (PiTensorProduct.tprod R)
        map_add' x x' := by ext; simp only [map_add]; simp; abel
        map_smul' r x := by ext; simp }

private theorem consRecAux_zero (e : N) (S : M →ₗ[R] TensorWords R M →ₗ[R] N)
    (Θ : M →ₗ[R] N →ₗ[R] N) (y : Fin 0 → M) :
    consRecAux e S Θ 0 (PiTensorProduct.tprod R y) = e := by
  simp [consRecAux]

private theorem consRecAux_succ (e : N) (S : M →ₗ[R] TensorWords R M →ₗ[R] N)
    (Θ : M →ₗ[R] N →ₗ[R] N) {n : ℕ} (x : M) (y : Fin n → M) :
    consRecAux e S Θ (n + 1) (PiTensorProduct.tprod R (Fin.cons x y)) =
      S x (of R M n (PiTensorProduct.tprod R y)) +
        Θ x (consRecAux e S Θ n (PiTensorProduct.tprod R y)) := by
  simp [consRecAux]

/-- **Recursion on the first letter.**  The linear map out of tensor words sending the empty word
to `e` and a word `x w` to `S x w + Θ x (φ w)`, where `φ w` is its value on the shorter word `w`. -/
noncomputable def consRec (e : N) (S : M →ₗ[R] TensorWords R M →ₗ[R] N)
    (Θ : M →ₗ[R] N →ₗ[R] N) : TensorWords R M →ₗ[R] N :=
  DirectSum.toModule R ℕ N (consRecAux e S Θ)

@[simp]
theorem consRec_one (e : N) (S : M →ₗ[R] TensorWords R M →ₗ[R] N) (Θ : M →ₗ[R] N →ₗ[R] N) :
    consRec e S Θ 1 = e := by
  rw [one_eq_of_zero, consRec, toModule_of, consRecAux_zero]

@[simp]
theorem consRec_cons (e : N) (S : M →ₗ[R] TensorWords R M →ₗ[R] N) (Θ : M →ₗ[R] N →ₗ[R] N)
    (x : M) (w : TensorWords R M) :
    consRec e S Θ (cons R M x w) = S x w + Θ x (consRec e S Θ w) := by
  have h : consRec e S Θ ∘ₗ cons R M x = S x + Θ x ∘ₗ consRec e S Θ := by
    refine linearMap_ext R M fun n y ↦ ?_
    rw [LinearMap.comp_apply, cons_of_tprod, consRec, toModule_of, consRecAux_succ,
      LinearMap.add_apply, LinearMap.comp_apply, toModule_of]
  exact LinearMap.congr_fun h w

/-- Prepending a letter lengthens a word by one. -/
theorem cons_mem_range_of (x : M) {m : ℕ} {w : TensorWords R M}
    (hw : w ∈ LinearMap.range (of R M m)) : cons R M x w ∈ LinearMap.range (of R M (m + 1)) := by
  obtain ⟨z, rfl⟩ := hw
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r y =>
    rw [map_smul, map_smul, cons_of_tprod]
    exact Submodule.smul_mem _ _ ⟨_, rfl⟩
  | add z z' hz hz' =>
    rw [map_add, map_add]
    exact add_mem hz hz'

/-- Prepending `k` copies of a letter lengthens a word by `k`. -/
theorem cons_pow_mem_range_of (a : M) (k : ℕ) {m : ℕ} {w : TensorWords R M}
    (hw : w ∈ LinearMap.range (of R M m)) :
    (cons R M a ^ k) w ∈ LinearMap.range (of R M (m + k)) := by
  induction k with
  | zero => simpa using hw
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp, ← add_assoc]
    exact cons_mem_range_of a ih

/-- The deconcatenation of `a ⋯ a w`: the cuts inside the initial block of `k` letters `a`, and the
cuts of `w`. -/
theorem deconcatenation_cons_pow (a : M) (k : ℕ) (w : TensorWords R M) :
    deconcatenation R M ((cons R M a ^ k) w) =
      ∑ i ∈ Finset.range k, (cons R M a ^ i) 1 ⊗ₜ[R] (cons R M a ^ (k - i)) w +
        (cons R M a ^ k).rTensor (TensorWords R M) (deconcatenation R M w) := by
  induction k with
  | zero => simp [Module.End.one_eq_id]
  | succ k ih =>
    have h₁ : ∑ i ∈ Finset.range k, (cons R M a).rTensor (TensorWords R M)
          ((cons R M a ^ i) 1 ⊗ₜ[R] (cons R M a ^ (k - i)) w) =
        ∑ i ∈ Finset.range k,
          (cons R M a ^ (i + 1)) 1 ⊗ₜ[R] (cons R M a ^ (k + 1 - (i + 1))) w := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [LinearMap.rTensor_tmul, pow_succ' _ i, mul_apply_eq_comp, Nat.add_sub_add_right]
    have h₂ : (1 : TensorWords R M) ⊗ₜ[R] cons R M a ((cons R M a ^ k) w) =
        (cons R M a ^ 0) 1 ⊗ₜ[R] (cons R M a ^ (k + 1 - 0)) w := by
      rw [pow_zero, one_apply_eq_self, Nat.sub_zero, pow_succ', mul_apply_eq_comp]
    have h₃ : (cons R M a).rTensor (TensorWords R M)
          ((cons R M a ^ k).rTensor (TensorWords R M) (deconcatenation R M w)) =
        (cons R M a * cons R M a ^ k).rTensor (TensorWords R M) (deconcatenation R M w) := by
      rw [← LinearMap.rTensor_comp_apply, Module.End.mul_eq_comp]
    rw [pow_succ', mul_apply_eq_comp, deconcatenation_cons, ih, map_add, map_sum, h₁, h₂, h₃,
      Finset.sum_range_succ' _ k]
    abel

/-- The letter component of a word starting with `x` is `x` times the counit of the rest. -/
@[simp]
theorem letter_reducedProjection_cons (x : M) (w : TensorWords R M) :
    ReducedTensorWords.letter R M (reducedProjection R M (cons R M x w)) = counit R M w • x := by
  conv_lhs => rw [← reducedInclusion_reducedProjection_add_algebraMap_counit R M w]
  simp [cons_apply, Algebra.algebraMap_eq_smul_one]

/-- The word `x y` of length two. -/
theorem reducedProjection_cons_cons_one (x y : M) :
    reducedProjection R M (cons R M x (cons R M y 1)) =
      ReducedTensorWords.of R M (2 : ℕ+) (PiTensorProduct.tprod R ![x, y]) := by
  rw [cons_one_eq_of, cons_of_tprod, reducedProjection_of_of_pos R M (n := 1 + 1) (by omega)]
  exact ReducedTensorWords.of_tprod_congr R M _ rfl
    fun i ↦ Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ k.elim0) j) i

end TensorWords

namespace TensorWords

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommGroup M] [Module R M]

/-- Prepending a letter of degree `p` to a word of total degree `D` gives a word of total degree
`p + D`. -/
theorem prepend_mem_gradedPiece {G : InternalGrading R M ℤ} {p D : ℤ} {a : M}
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

/-- Prepending a letter of degree `p` raises the total degree by `p`. -/
theorem cons_mem_gradedPiece {G : InternalGrading R M ℤ} {p D : ℤ} {x : M} (hx : x ∈ G.piece p)
    {w : TensorWords R M} (hw : w ∈ gradedPiece G D) : cons R M x w ∈ gradedPiece G (p + D) :=
  mem_gradedPiece_of_reducedInclusion (prepend_mem_gradedPiece hx hw)

/-- Prepending `k` copies of a letter of degree `p` raises the total degree by `k * p`. -/
theorem cons_pow_mem_gradedPiece {G : InternalGrading R M ℤ} {p D : ℤ} {x : M}
    (hx : x ∈ G.piece p) (k : ℕ) {w : TensorWords R M} (hw : w ∈ gradedPiece G D) :
    (cons R M x ^ k) w ∈ gradedPiece G (D + k * p) := by
  induction k with
  | zero => simpa using hw
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp]
    convert cons_mem_gradedPiece hx ih using 2
    push_cast
    ring

/-- Uncurried prepending preserves total degrees: it is homogeneous of degree zero from the
tensor-product grading of `M ⊗ Tᶜ(M)` to the total-letter-degree grading of the reduced words. -/
theorem isHomogeneous_lift_prepend (G : InternalGrading R M ℤ) :
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
