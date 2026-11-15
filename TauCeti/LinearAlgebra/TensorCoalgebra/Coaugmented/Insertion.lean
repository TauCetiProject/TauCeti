/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BigOperators.NatAntidiagonal
public import TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented.Prepend
public import TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented.Taylor
public import TauCeti.LinearAlgebra.TensorProduct.Basic

/-!
# Inserting letters into tensor words

Every tensor word is either the empty word or a letter `x` followed by a shorter word `w`, written
`TauCeti.TensorWords.cons x w`.  This file uses that recursion to build two operations on the
coaugmented tensor coalgebra `Tᶜ(M)`, and computes their deconcatenations.

* `TauCeti.TensorWords.insertions a t` sends a word to the sum of all the words obtained from it by
  inserting `t` copies of the letter `a`, each of the `n + 1` gaps of a word of length `n` receiving
  any number of them:

  `insertions a t (x₁ ⋯ xₙ) = ∑_{k₀ + ⋯ + kₙ = t} a^{k₀} x₁ a^{k₁} ⋯ xₙ a^{kₙ}`.

  The family is a graded coalgebra morphism:
  `Δ ∘ insertions a t = ∑_{i + j = t} (insertions a i ⊗ insertions a j) ∘ Δ`.  Summed over all
  `t`, the insertions would form the coalgebra automorphism of a completed tensor coalgebra with
  linear part the identity and constant part `a`; keeping the number of inserted letters as a
  grading keeps every identity finite, and no completion is formed here.
* `TauCeti.TensorWords.twistedInsert τ c` inserts the single letter `c` into every gap, applying
  `τ` to the letters before it:
  `twistedInsert τ c (x₁ ⋯ xₙ) = ∑ᵢ τx₁ ⋯ τxᵢ c xᵢ₊₁ ⋯ xₙ`.  For `τ` a Koszul twist it is the
  graded coderivation with constant Taylor coefficient `c`, the curvature term of a curved bar
  differential.

The main result, `TauCeti.TensorWords.IsGradedCoderivation.comp_insertions`, says how a graded
coderivation `D` passes through the insertions: if the coderivations `E v` have Taylor maps
`(letter ∘ D) ∘ insertions a v`, then `D ∘ insertions a t = ∑_{u + v = t} insertions a u ∘ E v`.
This is the identity behind twisting an `A∞` structure by a Maurer--Cartan element `a`: the
difference of the two sides is a graded coderivation with zero Taylor map, hence zero by
`TauCeti.TensorWords.IsGradedCoderivation.eq_zero_of_letter_reducedProjection_eq_zero`.

## Main definitions

* `TauCeti.TensorWords.cons`: prepend a letter, as an endomorphism of tensor words.
* `TauCeti.TensorWords.consRec`: linear maps out of tensor words by recursion on the first letter.
* `TauCeti.TensorWords.insertions`: insert `t` copies of a letter in all possible ways.
* `TauCeti.TensorWords.twistedInsert`: insert a letter once, twisting the letters before it.

## Main results

* `TauCeti.TensorWords.deconcatenation_insertions`: the insertions form a graded coalgebra
  morphism.
* `TauCeti.TensorWords.map_insertions` and `TauCeti.TensorWords.isHomogeneous_insertions`: the
  insertions commute with letterwise maps fixing the inserted letter, and preserve total degrees
  when it has degree zero.
* `TauCeti.TensorWords.deconcatenation_twistedInsert` and
  `TauCeti.TensorWords.isGradedCoderivation_twistedInsert`: the twisted insertion of a letter is a
  graded coderivation.
* `TauCeti.TensorWords.IsGradedCoderivation.comp_insertions`: graded coderivations pass through
  the insertions.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 7.6.
-/

public section

open scoped TensorProduct

universe uR uM uN

namespace TauCeti

namespace TensorWords

section Semiring

variable {R : Type uR} {M : Type uM} {N : Type uN} [CommSemiring R] [AddCommMonoid M]
  [Module R M] [AddCommMonoid N] [Module R N]

/-! ### Prepending a letter -/

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
theorem cons_pow_one (a : M) (n : ℕ) :
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
        (cons R M x).rTensor (TensorWords R M) (deconcatenation R M w) :=
  deconcatenation_reducedInclusion_prepend x w

/-- Mapping a word starting with `x` gives a word starting with the image of `x`. -/
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

/-! ### Inserting copies of a letter -/

/-- The recursion step of `insertions`, acting on the family of its values for all numbers of
inserted letters: before a letter `x`, insert `k` copies of `a`, and insert the remaining copies
into the rest of the word. -/
private noncomputable def insertionsStep (a : M) :
    M →ₗ[R] (ℕ → TensorWords R M) →ₗ[R] (ℕ → TensorWords R M) :=
  LinearMap.mk₂ R
    (fun x φ t ↦ ∑ p ∈ Finset.antidiagonal t, (cons R M a ^ p.1) (cons R M x (φ p.2)))
    (fun x x' φ ↦ by funext t; simp [Finset.sum_add_distrib])
    (fun r x φ ↦ by funext t; simp [Finset.smul_sum])
    (fun x φ φ' ↦ by funext t; simp [Finset.sum_add_distrib])
    (fun r x φ ↦ by funext t; simp [Finset.smul_sum])

/-- The family of all `insertions a t`, indexed by the number `t` of inserted letters. -/
private noncomputable def insertionsFamily (a : M) :
    TensorWords R M →ₗ[R] (ℕ → TensorWords R M) :=
  consRec (fun t ↦ (cons R M a ^ t) 1) 0 (insertionsStep a)

variable (R) in
/-- **Insertion of `t` copies of a letter.**  The sum of all the words obtained from a word by
inserting `t` copies of `a`, each gap receiving any number of them:
`insertions a t (x₁ ⋯ xₙ) = ∑_{k₀ + ⋯ + kₙ = t} a^{k₀} x₁ a^{k₁} ⋯ xₙ a^{kₙ}`. -/
noncomputable def insertions (a : M) (t : ℕ) : TensorWords R M →ₗ[R] TensorWords R M :=
  LinearMap.proj t ∘ₗ insertionsFamily a

/-- Inserting `t` copies of `a` into the empty word gives the word `a ⋯ a` of length `t`. -/
@[simp]
theorem insertions_one (a : M) (t : ℕ) : insertions R a t 1 = (cons R M a ^ t) 1 := by
  simp [insertions, insertionsFamily]

/-- Inserting `t` copies of `a` into `x w`: some `k` of them go before `x`, and the others into
`w`. -/
theorem insertions_cons (a : M) (t : ℕ) (x : M) (w : TensorWords R M) :
    insertions R a t (cons R M x w) =
      ∑ p ∈ Finset.antidiagonal t, (cons R M a ^ p.1) (cons R M x (insertions R a p.2 w)) := by
  simp [insertions, insertionsFamily, insertionsStep]

/-- Inserting no letters is the identity. -/
@[simp]
theorem insertions_zero (a : M) : insertions R a 0 = LinearMap.id := by
  refine linearMap_ext_cons (ι := Unit) (f := fun _ ↦ insertions R a 0) (g := fun _ ↦ .id)
    (fun _ ↦ by simp) (fun x w hw _ ↦ ?_) ()
  simp [insertions_cons, hw ()]

/-- Inserting at least one copy of the zero letter gives zero. -/
theorem zero_insertions {t : ℕ} (ht : t ≠ 0) : insertions R (0 : M) t = 0 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht
  refine linearMap_ext_cons (ι := ℕ) (f := fun t ↦ insertions R (0 : M) (t + 1)) (g := fun _ ↦ 0)
    (fun t ↦ ?_) (fun x w hw t ↦ ?_) t
  · simp [pow_succ']
  · simp only [LinearMap.zero_apply] at hw ⊢
    rw [insertions_cons, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ']
    simp [pow_succ', hw]

/-- Iterated prepending of a letter to a word with zero counit gives a word with zero counit. -/
private theorem counit_cons_pow_cons (a x : M) (k : ℕ) (w : TensorWords R M) :
    counit R M ((cons R M a ^ k) (cons R M x w)) = 0 := by
  rcases k with _ | k
  · simp
  · rw [pow_succ', mul_apply_eq_comp, counit_cons]

/-- A word into which at least one letter has been inserted has zero counit. -/
@[simp]
theorem counit_insertions_succ (a : M) (t : ℕ) (w : TensorWords R M) :
    counit R M (insertions R a (t + 1) w) = 0 := by
  refine LinearMap.congr_fun (linearMap_ext_cons (ι := Unit)
    (f := fun _ ↦ counit R M ∘ₗ insertions R a (t + 1)) (g := fun _ ↦ 0)
    (fun _ ↦ ?_) (fun x w _ _ ↦ ?_) ()) w
  · simp [pow_succ', mul_apply_eq_comp]
  · simp [insertions_cons, counit_cons_pow_cons]

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

/-- **The insertions form a graded coalgebra morphism**: inserting `t` letters and cutting is the
same as cutting and inserting `i` letters on the left and `j` on the right, for all
`i + j = t`. -/
theorem deconcatenation_comp_insertions (a : M) (t : ℕ) :
    deconcatenation R M ∘ₗ insertions R a t =
      ∑ p ∈ Finset.antidiagonal t,
        TensorProduct.map (insertions R a p.1) (insertions R a p.2) ∘ₗ deconcatenation R M := by
  refine linearMap_ext_cons (ι := ℕ)
    (f := fun t ↦ deconcatenation R M ∘ₗ insertions R a t)
    (g := fun t ↦ ∑ p ∈ Finset.antidiagonal t,
      TensorProduct.map (insertions R a p.1) (insertions R a p.2) ∘ₗ deconcatenation R M)
    (fun t ↦ ?_) (fun x w hw t ↦ ?_) t
  · simp only [LinearMap.comp_apply, LinearMap.sum_apply, insertions_one,
      deconcatenation_one, TensorProduct.map_tmul, deconcatenation_cons_pow,
      LinearMap.rTensor_tmul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, one_apply_eq_self]
  · have hw' (l : ℕ) := hw l
    simp only [LinearMap.comp_apply, LinearMap.sum_apply] at hw' ⊢
    -- The cuts with an empty or a pure-`a` left half, and the cuts inside the rest of the word.
    set T₁ : ℕ → ℕ → ℕ → TensorWords R M ⊗[R] TensorWords R M := fun i j l ↦
      (cons R M a ^ i) 1 ⊗ₜ[R] (cons R M a ^ j) (cons R M x (insertions R a l w)) with hT₁
    set T₂ : ℕ → ℕ → ℕ → TensorWords R M ⊗[R] TensorWords R M := fun k i j ↦
      TensorProduct.map ((cons R M a ^ k) ∘ₗ cons R M x ∘ₗ insertions R a i) (insertions R a j)
        (deconcatenation R M w) with hT₂
    have hleft (k l : ℕ) :
        deconcatenation R M ((cons R M a ^ k) (cons R M x (insertions R a l w))) =
        ∑ r ∈ Finset.antidiagonal k, T₁ r.1 r.2 l +
          ∑ q ∈ Finset.antidiagonal l, T₂ k q.1 q.2 := by
      rw [deconcatenation_cons_pow, deconcatenation_cons, map_add, LinearMap.rTensor_tmul, hw',
        map_sum, map_sum, ← add_assoc]
      congr 1
      · rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]
        simp [hT₁]
      · refine Finset.sum_congr rfl fun q _ ↦ ?_
        simp [hT₂]
    have hcomp (k : ℕ) : insertions R a k ∘ₗ cons R M x =
        ∑ r ∈ Finset.antidiagonal k, (cons R M a ^ r.1) ∘ₗ cons R M x ∘ₗ insertions R a r.2 := by
      refine LinearMap.ext fun v ↦ ?_
      simp [insertions_cons, LinearMap.sum_apply]
    have hright (p : ℕ × ℕ) : TensorProduct.map (insertions R a p.1) (insertions R a p.2)
        (deconcatenation R M (cons R M x w)) =
          ∑ r ∈ Finset.antidiagonal p.2, T₁ p.1 r.1 r.2 +
            ∑ r ∈ Finset.antidiagonal p.1, T₂ r.1 r.2 p.2 := by
      rw [deconcatenation_cons, map_add, TensorProduct.map_tmul, insertions_one, insertions_cons,
        TensorProduct.tmul_sum, LinearMap.map_rTensor, hcomp, TensorProduct.map_sum_left,
        LinearMap.sum_apply]
    rw [insertions_cons, map_sum]
    simp only [hleft, hright, Finset.sum_add_distrib]
    rw [Finset.Nat.sum_antidiagonal_sum_antidiagonal_fst t T₁,
      Finset.Nat.sum_antidiagonal_sum_antidiagonal_fst t T₂]

/-- **The insertions form a graded coalgebra morphism**, applied to a word. -/
theorem deconcatenation_insertions (a : M) (t : ℕ) (w : TensorWords R M) :
    deconcatenation R M (insertions R a t w) =
      ∑ p ∈ Finset.antidiagonal t,
        TensorProduct.map (insertions R a p.1) (insertions R a p.2) (deconcatenation R M w) := by
  simpa using LinearMap.congr_fun (deconcatenation_comp_insertions a t) w

/-- The counit of the insertions: inserting at least one letter leaves no empty word. -/
theorem counit_insertions (a : M) (t : ℕ) (w : TensorWords R M) :
    counit R M (insertions R a t w) = if t = 0 then counit R M w else 0 := by
  rcases t with _ | t
  · simp
  · simp

/-- The letter component of a word starting with `x` is `x` times the counit of the rest. -/
theorem letter_reducedProjection_cons (x : M) (w : TensorWords R M) :
    ReducedTensorWords.letter R M (reducedProjection R M (cons R M x w)) = counit R M w • x := by
  conv_lhs => rw [← reducedInclusion_reducedProjection_add_algebraMap_counit R M w]
  rw [cons_apply, reducedProjection_reducedInclusion, map_add, prepend_reducedInclusion,
    Algebra.algebraMap_eq_smul_one, map_smul, prepend_one, map_add, map_smul,
    ReducedTensorWords.letter_prepend, ReducedTensorWords.letter_ofLetter, zero_add]

/-- The letter component of the insertions: inserting no letters keeps it, inserting one letter
into the empty word gives that letter, and every other insertion has no letter component. -/
theorem letter_reducedProjection_insertions (a : M) (t : ℕ) (w : TensorWords R M) :
    ReducedTensorWords.letter R M (reducedProjection R M (insertions R a t w)) =
      if t = 0 then ReducedTensorWords.letter R M (reducedProjection R M w)
      else if t = 1 then counit R M w • a else 0 := by
  refine LinearMap.congr_fun (linearMap_ext_cons (ι := ℕ)
    (f := fun t ↦ ReducedTensorWords.letter R M ∘ₗ reducedProjection R M ∘ₗ insertions R a t)
    (g := fun t ↦ if t = 0 then ReducedTensorWords.letter R M ∘ₗ reducedProjection R M
      else if t = 1 then (counit R M).smulRight a else 0)
    (fun t ↦ ?_) (fun x w _ t ↦ ?_) t) w |>.trans (by split_ifs <;> rfl)
  · rcases t with _ | _ | t
    · simp
    · simp [letter_reducedProjection_cons]
    · simp [pow_succ', mul_apply_eq_comp, letter_reducedProjection_cons]
  · have hterm (i l : ℕ) : ReducedTensorWords.letter R M (reducedProjection R M
        ((cons R M a ^ (i + 1)) (cons R M x (insertions R a l w)))) = 0 := by
      rw [pow_succ', mul_apply_eq_comp, letter_reducedProjection_cons, counit_cons_pow_cons,
        zero_smul]
    rcases t with _ | _ | t <;>
      simp [insertions_cons, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        Finset.sum_range_succ', hterm, letter_reducedProjection_cons]

/-- Inserting letters commutes with applying a linear map to every letter. -/
theorem map_insertions (f : M →ₗ[R] N) (a : M) (t : ℕ) (w : TensorWords R M) :
    map f (insertions R a t w) = insertions R (f a) t (map f w) := by
  refine LinearMap.congr_fun (linearMap_ext_cons (ι := ℕ)
    (f := fun t ↦ map f ∘ₗ insertions R a t) (g := fun t ↦ insertions R (f a) t ∘ₗ map f)
    (fun t ↦ ?_) (fun x w hw t ↦ ?_) t) w
  · simp [map_cons_pow, map_one]
  · simp only [LinearMap.comp_apply] at hw ⊢
    simp [insertions_cons, map_cons_pow, map_cons, hw]

/-- Inserting `t` letters into a word of length `n` gives a word of length `n + t`. -/
theorem insertions_of_mem_range (a : M) (t : ℕ) {n : ℕ} (z : TensorPower R n M) :
    insertions R a t (of R M n z) ∈ LinearMap.range (of R M (n + t)) := by
  -- Prepending a letter lengthens a word by one.
  have hcons (x : M) {m : ℕ} {v : TensorWords R M} (hv : v ∈ LinearMap.range (of R M m)) :
      cons R M x v ∈ LinearMap.range (of R M (m + 1)) := by
    obtain ⟨z, rfl⟩ := hv
    induction z using PiTensorProduct.induction_on with
    | smul_tprod r y =>
      rw [map_smul, map_smul, cons_of_tprod]
      exact Submodule.smul_mem _ _ ⟨_, rfl⟩
    | add z z' hz hz' =>
      rw [map_add, map_add]
      exact add_mem hz hz'
  have hpow (k : ℕ) {m : ℕ} {v : TensorWords R M} (hv : v ∈ LinearMap.range (of R M m)) :
      (cons R M a ^ k) v ∈ LinearMap.range (of R M (m + k)) := by
    induction k with
    | zero => simpa using hv
    | succ k ih =>
      rw [pow_succ', mul_apply_eq_comp, ← add_assoc]
      exact hcons a ih
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r y =>
    rw [map_smul, map_smul]
    refine Submodule.smul_mem _ _ ?_
    induction n generalizing t with
    | zero =>
      rw [Subsingleton.elim y fun i ↦ i.elim0, ← one_eq_of_zero, insertions_one]
      exact hpow t (v := 1) ⟨_, (one_eq_of_zero R M).symm⟩
    | succ n ih =>
      rw [← Fin.cons_self_tail y, ← cons_of_tprod, insertions_cons]
      refine Submodule.sum_mem _ fun p hp ↦ ?_
      rw [Finset.mem_antidiagonal] at hp
      have h := hpow p.1 (hcons (y 0) (ih p.2 (Fin.tail y)))
      rwa [show n + p.2 + 1 + p.1 = n + 1 + t by omega] at h
  | add z z' hz hz' =>
    rw [map_add, map_add]
    exact add_mem hz hz'

/-! ### Inserting a single letter -/

/-- The underlying function of `twistedInsert`, before linearity in the inserted letter. -/
private noncomputable def twistedInsertAux (τ : M →ₗ[R] M) (c : M) :
    TensorWords R M →ₗ[R] TensorWords R M :=
  consRec (cons R M c 1) ((cons R M).compr₂ (cons R M c)) (cons R M ∘ₗ τ)

private theorem twistedInsertAux_one (τ : M →ₗ[R] M) (c : M) :
    twistedInsertAux τ c 1 = cons R M c 1 :=
  consRec_one _ _ _

private theorem twistedInsertAux_cons (τ : M →ₗ[R] M) (c x : M) (w : TensorWords R M) :
    twistedInsertAux τ c (cons R M x w) =
      cons R M c (cons R M x w) + cons R M (τ x) (twistedInsertAux τ c w) := by
  simp [twistedInsertAux]

variable (R) in
/-- **Twisted insertion of a letter.**  Insert the letter `c` once into every gap of a word,
applying `τ` to each letter before it:
`twistedInsert τ c (x₁ ⋯ xₙ) = ∑_{i = 0}^{n} τx₁ ⋯ τxᵢ c xᵢ₊₁ ⋯ xₙ`. -/
noncomputable def twistedInsert (τ : M →ₗ[R] M) :
    M →ₗ[R] TensorWords R M →ₗ[R] TensorWords R M where
  toFun := twistedInsertAux τ
  map_add' c c' := linearMap_ext_cons (ι := Unit) (f := fun _ ↦ twistedInsertAux τ (c + c'))
    (g := fun _ ↦ twistedInsertAux τ c + twistedInsertAux τ c')
    (fun _ ↦ by simp [twistedInsertAux_one])
    (fun x w hw _ ↦ by
      simp only [LinearMap.add_apply] at hw ⊢
      rw [twistedInsertAux_cons, twistedInsertAux_cons, twistedInsertAux_cons, hw (), map_add,
        map_add, LinearMap.add_apply]
      abel) ()
  map_smul' r c := linearMap_ext_cons (ι := Unit) (f := fun _ ↦ twistedInsertAux τ (r • c))
    (g := fun _ ↦ r • twistedInsertAux τ c)
    (fun _ ↦ by simp [twistedInsertAux_one])
    (fun x w hw _ ↦ by
      simp only [LinearMap.smul_apply] at hw ⊢
      rw [twistedInsertAux_cons, twistedInsertAux_cons, hw (), map_smul, map_smul, smul_add,
        LinearMap.smul_apply]) ()

/-- Inserting a letter into the empty word gives that letter. -/
@[simp]
theorem twistedInsert_one (τ : M →ₗ[R] M) (c : M) : twistedInsert R τ c 1 = cons R M c 1 :=
  twistedInsertAux_one τ c

/-- Inserting a letter into `x w`: before `x`, or after the twisted letter `τ x`. -/
theorem twistedInsert_cons (τ : M →ₗ[R] M) (c x : M) (w : TensorWords R M) :
    twistedInsert R τ c (cons R M x w) =
      cons R M c (cons R M x w) + cons R M (τ x) (twistedInsert R τ c w) :=
  twistedInsertAux_cons τ c x w

/-- Twisted insertion leaves no empty word. -/
@[simp]
theorem counit_twistedInsert (τ : M →ₗ[R] M) (c : M) (w : TensorWords R M) :
    counit R M (twistedInsert R τ c w) = 0 := by
  refine LinearMap.congr_fun (linearMap_ext_cons (ι := Unit)
    (f := fun _ ↦ counit R M ∘ₗ twistedInsert R τ c) (g := fun _ ↦ 0)
    (fun _ ↦ by simp) (fun x w _ _ ↦ by simp [twistedInsert_cons]) ()) w

/-- The letter component of a twisted insertion is the inserted letter times the counit. -/
theorem letter_reducedProjection_twistedInsert (τ : M →ₗ[R] M) (c : M) (w : TensorWords R M) :
    ReducedTensorWords.letter R M (reducedProjection R M (twistedInsert R τ c w)) =
      counit R M w • c := by
  refine LinearMap.congr_fun (linearMap_ext_cons (ι := Unit)
    (f := fun _ ↦ ReducedTensorWords.letter R M ∘ₗ reducedProjection R M ∘ₗ twistedInsert R τ c)
    (g := fun _ ↦ (counit R M).smulRight c)
    (fun _ ↦ by simp [letter_reducedProjection_cons])
    (fun x w _ _ ↦ by simp [twistedInsert_cons, letter_reducedProjection_cons]) ()) w

/-- **The co-Leibniz rule of twisted insertion**: cutting `τx₁ ⋯ τxᵢ c xᵢ₊₁ ⋯ xₙ` puts `c` in
the left half, or in the right half after the twisted left half. -/
theorem deconcatenation_twistedInsert (τ : M →ₗ[R] M) (c : M) (w : TensorWords R M) :
    deconcatenation R M (twistedInsert R τ c w) =
      (twistedInsert R τ c).rTensor (TensorWords R M) (deconcatenation R M w) +
        (twistedInsert R τ c).lTensor (TensorWords R M)
          ((map τ).rTensor (TensorWords R M) (deconcatenation R M w)) := by
  refine LinearMap.congr_fun (linearMap_ext_cons (ι := Unit)
    (f := fun _ ↦ deconcatenation R M ∘ₗ twistedInsert R τ c)
    (g := fun _ ↦ (twistedInsert R τ c).rTensor (TensorWords R M) ∘ₗ deconcatenation R M +
      (twistedInsert R τ c).lTensor (TensorWords R M) ∘ₗ
        (map τ).rTensor (TensorWords R M) ∘ₗ deconcatenation R M)
    (fun _ ↦ ?_) (fun x w hw _ ↦ ?_) ()) w
  · simp [deconcatenation_cons, map_one, add_comm]
  · have hw' := hw ()
    simp only [LinearMap.comp_apply, LinearMap.add_apply] at hw' ⊢
    have hC : twistedInsert R τ c ∘ₗ cons R M x =
        cons R M c ∘ₗ cons R M x + cons R M (τ x) ∘ₗ twistedInsert R τ c := by
      refine LinearMap.ext fun v ↦ ?_
      simp [twistedInsert_cons]
    have hτ : map τ ∘ₗ cons R M x = cons R M (τ x) ∘ₗ map τ := by
      refine LinearMap.ext fun v ↦ ?_
      simp [map_cons]
    rw [twistedInsert_cons, map_add, deconcatenation_cons c, deconcatenation_cons (τ x), hw',
      deconcatenation_cons x]
    have hcomm (z : TensorWords R M ⊗[R] TensorWords R M) :
        (cons R M (τ x)).rTensor (TensorWords R M) ((twistedInsert R τ c).lTensor _ z) =
          (twistedInsert R τ c).lTensor _ ((cons R M (τ x)).rTensor (TensorWords R M) z) := by
      exact (LinearMap.congr_fun (LinearMap.rTensor_comp_lTensor (f := cons R M (τ x))
        (g := twistedInsert R τ c)) z).trans (LinearMap.congr_fun
          (LinearMap.lTensor_comp_rTensor (f := cons R M (τ x)) (g := twistedInsert R τ c)) z).symm
    simp only [map_add, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, twistedInsert_one,
      map_one, ← LinearMap.rTensor_comp_apply, hC, hτ, LinearMap.rTensor_add, LinearMap.add_apply]
    rw [twistedInsert_cons, TensorProduct.tmul_add]
    simp only [hcomm, LinearMap.rTensor_comp_apply]
    abel

end Semiring

section Ring

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommGroup M] [Module R M]
  {G : InternalGrading R M ℤ} {q : ℤ}

/-! ### Graded structure -/

/-- The twisted insertion of a letter along the Koszul twist is a graded coderivation. -/
theorem isGradedCoderivation_twistedInsert (G : InternalGrading R M ℤ) (q : ℤ) (c : M) :
    IsGradedCoderivation G q (twistedInsert R (G.koszulTwist q) c) := by
  rw [isGradedCoderivation_iff]
  refine LinearMap.ext fun w ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.add_apply, deconcatenation_twistedInsert]

/-- Prepending a letter of degree `p` raises the total degree by `p`. -/
theorem cons_mem_gradedPiece {p D : ℤ} {x : M} (hx : x ∈ G.piece p) {w : TensorWords R M}
    (hw : w ∈ gradedPiece G D) : cons R M x w ∈ gradedPiece G (p + D) :=
  mem_gradedPiece_of_reducedInclusion (prepend_mem_gradedPiece hx hw)

/-- Inserting copies of a letter of degree zero preserves total degrees. -/
theorem insertions_mem_gradedPiece {a : M} (ha : a ∈ G.piece 0) (t : ℕ) {D : ℤ}
    {w : TensorWords R M} (hw : w ∈ gradedPiece G D) : insertions R a t w ∈ gradedPiece G D := by
  have hpow (k : ℕ) {E : ℤ} {v : TensorWords R M} (hv : v ∈ gradedPiece G E) :
      (cons R M a ^ k) v ∈ gradedPiece G E := by
    induction k with
    | zero => simpa using hv
    | succ k ih => simpa [pow_succ', mul_apply_eq_comp] using cons_mem_gradedPiece ha ih
  have h₁ : (1 : TensorWords R M) ∈ gradedPiece G 0 := by
    simpa [← one_eq_of_zero] using
      mem_gradedPiece_of_tprod G (fun i : Fin 0 ↦ (i.elim0 : M)) (fun i ↦ i.elim0) (fun i ↦ i.elim0)
  have key (n : ℕ) : ∀ (𝒟 : Fin n → ℤ) (x : Fin n → M), (∀ i, x i ∈ G.piece (𝒟 i)) → ∀ t,
      insertions R a t (of R M n (PiTensorProduct.tprod R x)) ∈ gradedPiece G (∑ i, 𝒟 i) := by
    induction n with
    | zero =>
      intro 𝒟 x _ t
      rw [Subsingleton.elim x fun i ↦ i.elim0, ← one_eq_of_zero, insertions_one,
        Finset.univ_eq_empty, Finset.sum_empty]
      exact hpow t h₁
    | succ n ih =>
      intro 𝒟 x hx t
      rw [← Fin.cons_self_tail x, ← cons_of_tprod, insertions_cons, Fin.sum_univ_succ]
      exact Submodule.sum_mem _ fun p _ ↦ hpow p.1 (cons_mem_gradedPiece (hx 0)
        (ih (Fin.tail 𝒟) (Fin.tail x) (fun i ↦ hx i.succ) p.2))
  refine gradedPiece_induction (motive := fun w ↦ insertions R a t w ∈ gradedPiece G D) hw
    (fun n 𝒟 x hx hD ↦ hD ▸ key n 𝒟 x hx t) (by simp)
    (fun u v _ _ hu hv ↦ by simpa using add_mem hu hv)
    (fun r u _ hu ↦ by simpa using Submodule.smul_mem _ r hu)

/-- Inserting copies of a letter of degree zero is homogeneous of degree zero. -/
theorem isHomogeneous_insertions {a : M} (ha : a ∈ G.piece 0) (t : ℕ) :
    LinearMap.IsHomogeneous (insertions R a t) (gradedPiece G) (gradedPiece G) 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro D w hw
  rw [add_zero]
  exact insertions_mem_gradedPiece ha t hw

/-! ### Coderivations through the insertions -/

/-- A sum over the triples `a + b + c = n`, bracketed as `(a + b) + c`, is unchanged by swapping
the roles of `b` and `c`. -/
private theorem sum_antidiagonal_sum_antidiagonal_fst_swap {X : Type*} [AddCommMonoid X] (n : ℕ)
    (g : ℕ → ℕ → ℕ → X) :
    ∑ p ∈ Finset.antidiagonal n, ∑ q ∈ Finset.antidiagonal p.1, g q.1 q.2 p.2 =
      ∑ p ∈ Finset.antidiagonal n, ∑ q ∈ Finset.antidiagonal p.1, g q.1 p.2 q.2 := by
  rw [Finset.Nat.sum_antidiagonal_sum_antidiagonal_fst n g,
    Finset.Nat.sum_antidiagonal_sum_antidiagonal_fst n fun a b c ↦ g a c b]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  exact (Finset.Nat.sum_antidiagonal_swap (f := fun q ↦ g p.1 q.1 q.2)).symm

/-- The tensor product of maps is subtractive in its left factor.  The difference is written with
`(-1 : R) •`, since `TensorWords R M ⊗[R] TensorWords R M` is used with its additive monoid
structure. -/
private theorem map_sub_left_apply (f₁ f₂ g : TensorWords R M →ₗ[R] TensorWords R M)
    (z : TensorWords R M ⊗[R] TensorWords R M) :
    TensorProduct.map (f₁ - f₂) g z =
      TensorProduct.map f₁ g z + (-1 : R) • TensorProduct.map f₂ g z := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    rw [TensorProduct.map_tmul, TensorProduct.map_tmul, TensorProduct.map_tmul, LinearMap.sub_apply,
      sub_eq_add_neg, ← neg_one_smul R (f₂ x), TensorProduct.add_tmul, TensorProduct.smul_tmul']
  | add z z' hz hz' => rw [map_add, map_add, map_add, hz, hz', smul_add]; abel

/-- The tensor product of maps is subtractive in its right factor. -/
private theorem map_sub_right_apply (f g₁ g₂ : TensorWords R M →ₗ[R] TensorWords R M)
    (z : TensorWords R M ⊗[R] TensorWords R M) :
    TensorProduct.map f (g₁ - g₂) z =
      TensorProduct.map f g₁ z + (-1 : R) • TensorProduct.map f g₂ z := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    rw [TensorProduct.map_tmul, TensorProduct.map_tmul, TensorProduct.map_tmul, LinearMap.sub_apply,
      sub_eq_add_neg, ← neg_one_smul R (g₂ y), TensorProduct.tmul_add, TensorProduct.tmul_smul]
  | add z z' hz hz' => rw [map_add, map_add, map_add, hz, hz', smul_add]; abel

/-- A graded coderivation after the insertions is a coderivation along the insertions. -/
private theorem IsGradedCoderivation.deconcatenation_comp_insertions_apply {a : M}
    {D : TensorWords R M →ₗ[R] TensorWords R M} (hD : IsGradedCoderivation G q D) (i : ℕ)
    (w : TensorWords R M) :
    deconcatenation R M (D (insertions R a i w)) =
      ∑ p ∈ Finset.antidiagonal i,
        (TensorProduct.map (D ∘ₗ insertions R a p.1) (insertions R a p.2) (deconcatenation R M w) +
          TensorProduct.map (map (G.koszulTwist q) ∘ₗ insertions R a p.1) (D ∘ₗ insertions R a p.2)
            (deconcatenation R M w)) := by
  simp only [hD.deconcatenation_apply, deconcatenation_insertions, map_sum, LinearMap.rTensor_map,
    LinearMap.lTensor_map, Finset.sum_add_distrib]

/-- Graded coderivations followed by insertions, summed over the number of inserted letters, form
a coderivation along the insertions. -/
private theorem deconcatenation_sum_insertions_comp_apply {a : M}
    (ha : G.koszulTwist q a = a) {E : ℕ → TensorWords R M →ₗ[R] TensorWords R M}
    (hE : ∀ v, IsGradedCoderivation G q (E v)) (i : ℕ) (w : TensorWords R M) :
    deconcatenation R M ((∑ p ∈ Finset.antidiagonal i, insertions R a p.1 ∘ₗ E p.2) w) =
      ∑ p ∈ Finset.antidiagonal i,
        (TensorProduct.map (∑ r ∈ Finset.antidiagonal p.1, insertions R a r.1 ∘ₗ E r.2)
            (insertions R a p.2) (deconcatenation R M w) +
          TensorProduct.map (map (G.koszulTwist q) ∘ₗ insertions R a p.1)
            (∑ r ∈ Finset.antidiagonal p.2, insertions R a r.1 ∘ₗ E r.2)
            (deconcatenation R M w)) := by
  have hτ (j : ℕ) : map (G.koszulTwist q) ∘ₗ insertions R a j =
      insertions R a j ∘ₗ map (G.koszulTwist q) :=
    LinearMap.ext fun w ↦ by simp only [LinearMap.comp_apply, map_insertions, ha]
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum, deconcatenation_insertions,
    (hE _).deconcatenation_apply, map_add, LinearMap.map_rTensor, LinearMap.map_lTensor,
    Finset.sum_add_distrib, TensorProduct.map_sum_left, TensorProduct.map_sum_right, hτ]
  congr 1
  · exact sum_antidiagonal_sum_antidiagonal_fst_swap i fun i' j' v ↦
      TensorProduct.map (insertions R a i' ∘ₗ E v) (insertions R a j') (deconcatenation R M w)
  · exact Finset.Nat.sum_antidiagonal_sum_antidiagonal_fst i fun i' j' v ↦
      TensorProduct.map (insertions R a i' ∘ₗ map (G.koszulTwist q)) (insertions R a j' ∘ₗ E v)
        (deconcatenation R M w)

/-- Two coderivations along the insertions which agree for fewer than `t` inserted letters differ by
a graded coderivation for `t` inserted letters. -/
private theorem isGradedCoderivation_sub_of_deconcatenation {a : M}
    {L K : ℕ → TensorWords R M →ₗ[R] TensorWords R M} {t : ℕ}
    (hL : ∀ w, deconcatenation R M (L t w) = ∑ p ∈ Finset.antidiagonal t,
      (TensorProduct.map (L p.1) (insertions R a p.2) (deconcatenation R M w) +
        TensorProduct.map (map (G.koszulTwist q) ∘ₗ insertions R a p.1) (L p.2)
          (deconcatenation R M w)))
    (hK : ∀ w, deconcatenation R M (K t w) = ∑ p ∈ Finset.antidiagonal t,
      (TensorProduct.map (K p.1) (insertions R a p.2) (deconcatenation R M w) +
        TensorProduct.map (map (G.koszulTwist q) ∘ₗ insertions R a p.1) (K p.2)
          (deconcatenation R M w)))
    (hLK : ∀ i < t, L i - K i = 0) :
    IsGradedCoderivation G q (L t - K t) := by
  rw [isGradedCoderivation_iff]
  refine LinearMap.ext fun w ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.add_apply]
  have hsub : deconcatenation R M ((L t - K t) w) =
      ∑ p ∈ Finset.antidiagonal t,
        TensorProduct.map (L p.1 - K p.1) (insertions R a p.2) (deconcatenation R M w) +
      ∑ p ∈ Finset.antidiagonal t,
        TensorProduct.map (map (G.koszulTwist q) ∘ₗ insertions R a p.1) (L p.2 - K p.2)
          (deconcatenation R M w) := by
    rw [LinearMap.sub_apply, sub_eq_add_neg, ← neg_one_smul R (K t w)]
    simp only [map_add, map_smul, hL, hK, map_sub_left_apply, map_sub_right_apply,
      Finset.sum_add_distrib, Finset.smul_sum, smul_add]
    abel
  -- Only the summands with all `t` letters on one side survive.
  rw [hsub, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Finset.sum_range_succ']
  rw [Finset.sum_eq_zero fun i hi ↦ by
      rw [hLK i (Finset.mem_range.1 hi), TensorProduct.map_zero_left, LinearMap.zero_apply],
    Finset.sum_eq_zero fun i hi ↦ by
      rw [hLK (t - (i + 1)) (by have := Finset.mem_range.1 hi; omega),
        TensorProduct.map_zero_right, LinearMap.zero_apply]]
  simp [LinearMap.rTensor, LinearMap.lTensor, TensorProduct.map_map]

/-- **Graded coderivations pass through the insertions.**  Let `D` and the `E v` be graded
coderivations, and suppose that the Taylor map of `E v` is the Taylor map of `D` after inserting
`v` copies of a letter `a` fixed by the Koszul twist.  Then inserting `t` copies of `a` and applying
`D` is the sum, over `u + v = t`, of applying `E v` and inserting `u` copies of `a`.  The
coderivations need not vanish on the empty word: the constant Taylor coefficient of `E v` is the
value of the Taylor map of `D` on the word `a ⋯ a` of length `v`. -/
theorem IsGradedCoderivation.comp_insertions {a : M} (ha : G.koszulTwist q a = a)
    {D : TensorWords R M →ₗ[R] TensorWords R M} {E : ℕ → TensorWords R M →ₗ[R] TensorWords R M}
    (hD : IsGradedCoderivation G q D) (hE : ∀ v, IsGradedCoderivation G q (E v))
    (hEt : ∀ v w, ReducedTensorWords.letter R M (reducedProjection R M (E v w)) =
      ReducedTensorWords.letter R M (reducedProjection R M (D (insertions R a v w))))
    (t : ℕ) :
    D ∘ₗ insertions R a t = ∑ p ∈ Finset.antidiagonal t, insertions R a p.1 ∘ₗ E p.2 := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  -- The difference of the two sides is a graded coderivation with vanishing Taylor map.
  refine sub_eq_zero.1 <| IsGradedCoderivation.eq_zero_of_letter_reducedProjection_eq_zero
    (isGradedCoderivation_sub_of_deconcatenation
      (L := fun i ↦ D ∘ₗ insertions R a i)
      (K := fun i ↦ ∑ p ∈ Finset.antidiagonal i, insertions R a p.1 ∘ₗ E p.2)
      (hD.deconcatenation_comp_insertions_apply t)
      (deconcatenation_sum_insertions_comp_apply ha hE t) fun i hi ↦ sub_eq_zero.2 (ih i hi))
    fun w ↦ ?_
  simp only [LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.comp_apply, map_sub, map_sum]
  simp only [letter_reducedProjection_insertions, (hE _).counit_apply, zero_smul, ite_self,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ',
    Nat.add_one_ne_zero, ↓reduceIte, Finset.sum_const_zero, zero_add, Nat.sub_zero, hEt,
    sub_self]

end Ring

end TensorWords

end TauCeti
