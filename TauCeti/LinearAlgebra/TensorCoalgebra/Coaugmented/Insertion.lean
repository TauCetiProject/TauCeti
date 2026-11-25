/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BigOperators.NatAntidiagonal
public import TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented.Prepend
public import TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented.Taylor

/-!
# Inserting letters into tensor words

Every pure tensor word is either the empty word or a letter `x` followed by a shorter pure
word `w`, written `TauCeti.TensorWords.cons x w`, and the pure words span `Tᶜ(M)`.  This file uses
the recursion `TauCeti.TensorWords.consRec` on the first letter to build two operations on the
coaugmented tensor coalgebra `Tᶜ(M)`, and computes their deconcatenations.

* `TauCeti.TensorWords.insertions a t` sends a word to the sum of all the words obtained from it by
  inserting `t` copies of the letter `a`, each of the `n + 1` gaps of a word of length `n` receiving
  any number of them:

  `insertions a t (x₁ ⋯ xₙ) = ∑_{k₀ + ⋯ + kₙ = t} a^{k₀} x₁ a^{k₁} ⋯ xₙ a^{kₙ}`.

  The family satisfies the coefficientwise coproduct identity
  `Δ ∘ insertions a t = ∑_{i + j = t} (insertions a i ⊗ insertions a j) ∘ Δ`; this is a property
  of the family, not of the individual maps.  Summed over all
  `t`, the insertions would form the coalgebra automorphism of a completed tensor coalgebra with
  linear part the identity and constant part `a`; keeping the number of inserted letters as a
  grading keeps every identity finite, and no completion is formed here.
* `TauCeti.TensorWords.twistedInsert τ c` inserts the single letter `c` into every gap, applying
  `τ` to the letters before it:
  `twistedInsert τ c (x₁ ⋯ xₙ) = ∑ᵢ τx₁ ⋯ τxᵢ c xᵢ₊₁ ⋯ xₙ`.  For `τ` a Koszul twist it is the
  graded coderivation with constant Taylor coefficient `c`, the curvature term of a curved bar
  differential.

The main result, `TauCeti.TensorWords.IsGradedCoderivation.comp_insertions`, says how a graded
coderivation `D` passes through the insertions of a letter `a` fixed by the Koszul twist: if the
coderivations `E v` have Taylor maps `(letter ∘ D) ∘ insertions a v`, then
`D ∘ insertions a t = ∑_{u + v = t} insertions a u ∘ E v`.  A suspended Maurer--Cartan element has
degree zero, so the Koszul twist fixes it.  This is the identity behind twisting an `A∞`
structure by a Maurer--Cartan element `a`: the difference of the two sides is a graded
coderivation with zero Taylor map, hence zero by
`TauCeti.TensorWords.IsGradedCoderivation.eq_zero_of_letter_reducedProjection_eq_zero`.

## Main definitions

* `TauCeti.TensorWords.insertions`: insert `t` copies of a letter in all possible ways.
* `TauCeti.TensorWords.twistedInsert`: insert a letter once, twisting the letters before it.

## Main results

* `TauCeti.TensorWords.deconcatenation_insertions`: the coefficientwise coproduct identity for the
  family of insertions.
* `TauCeti.TensorWords.map_insertions` and `TauCeti.TensorWords.isHomogeneous_insertions`: the
  insertions commute with letterwise maps fixing the inserted letter, and inserting `t` copies of
  a letter of degree `p` raises total degrees by `t * p`.
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
theorem insertions_apply_one (a : M) (t : ℕ) : insertions R a t 1 = (cons R M a ^ t) 1 := by
  simp [insertions, insertionsFamily]

/-- Inserting `t` copies of `a` into `x w`: some `k` of them go before `x`, and the others into
`w`. -/
@[simp]
theorem insertions_cons (a : M) (t : ℕ) (x : M) (w : TensorWords R M) :
    insertions R a t (cons R M x w) =
      ∑ p ∈ Finset.antidiagonal t, (cons R M a ^ p.1) (cons R M x (insertions R a p.2 w)) := by
  simp [insertions, insertionsFamily, insertionsStep]

/-- Inserting no letters is the identity. -/
@[simp]
theorem insertions_zero (a : M) : insertions R a 0 = LinearMap.id := by
  refine linearMap_ext_cons' (by simp) fun x w hw ↦ ?_
  simp [insertions_cons, hw]

/-- Inserting at least one copy of the zero letter gives zero. -/
@[simp]
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
  refine LinearMap.congr_fun (linearMap_ext_cons'
    (f := counit R M ∘ₗ insertions R a (t + 1)) (g := 0) ?_ fun x w _ ↦ ?_) w
  · simp [pow_succ', mul_apply_eq_comp]
  · simp [insertions_cons, counit_cons_pow_cons]

/-- **The coproduct identity for the insertions**, coefficientwise in the number of inserted
letters: inserting `t` letters and cutting is the same as cutting and inserting `i` letters on the
left and `j` on the right, summed over all `i + j = t`. -/
theorem deconcatenation_comp_insertions (a : M) (t : ℕ) :
    deconcatenation R M ∘ₗ insertions R a t =
      ∑ p ∈ Finset.antidiagonal t,
        TensorProduct.map (insertions R a p.1) (insertions R a p.2) ∘ₗ deconcatenation R M := by
  refine linearMap_ext_cons (ι := ℕ)
    (f := fun t ↦ deconcatenation R M ∘ₗ insertions R a t)
    (g := fun t ↦ ∑ p ∈ Finset.antidiagonal t,
      TensorProduct.map (insertions R a p.1) (insertions R a p.2) ∘ₗ deconcatenation R M)
    (fun t ↦ ?_) (fun x w hw t ↦ ?_) t
  · simp only [LinearMap.comp_apply, LinearMap.sum_apply, insertions_apply_one,
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
      rw [deconcatenation_cons, map_add, TensorProduct.map_tmul, insertions_apply_one,
        insertions_cons, TensorProduct.tmul_sum, LinearMap.map_rTensor, hcomp,
        TensorProduct.map_sum_left, LinearMap.sum_apply]
    rw [insertions_cons, map_sum]
    simp only [hleft, hright, Finset.sum_add_distrib]
    rw [Finset.Nat.sum_antidiagonal_sum_antidiagonal_fst t T₁,
      Finset.Nat.sum_antidiagonal_sum_antidiagonal_fst t T₂]

/-- **The coproduct identity for the insertions**, applied to a word. -/
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
    (fun t ↦ ?_) (fun x w _ t ↦ ?_) t) w |>.trans (by split_ifs <;> simp)
  · rcases t with _ | _ | t
    · simp
    · simp
    · simp [pow_succ', mul_apply_eq_comp]
  · have hterm (i l : ℕ) : ReducedTensorWords.letter R M (reducedProjection R M
        ((cons R M a ^ (i + 1)) (cons R M x (insertions R a l w)))) = 0 := by
      rw [pow_succ', mul_apply_eq_comp, letter_reducedProjection_cons, counit_cons_pow_cons,
        zero_smul]
    rcases t with _ | _ | t <;>
      simp [insertions_cons, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        Finset.sum_range_succ', hterm]

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
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r y =>
    rw [map_smul, map_smul]
    refine Submodule.smul_mem _ _ ?_
    induction n generalizing t with
    | zero =>
      rw [Subsingleton.elim y fun i ↦ i.elim0, ← one_eq_of_zero, insertions_apply_one]
      exact cons_pow_mem_range_of a t (w := 1) ⟨_, (one_eq_of_zero R M).symm⟩
    | succ n ih =>
      rw [← Fin.cons_self_tail y, ← cons_of_tprod, insertions_cons]
      refine Submodule.sum_mem _ fun p hp ↦ ?_
      rw [Finset.mem_antidiagonal] at hp
      have h := cons_pow_mem_range_of a p.1 (cons_mem_range_of (y 0) (ih p.2 (Fin.tail y)))
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
  map_add' c c' := linearMap_ext_cons' (by simp [twistedInsertAux_one]) fun x w hw ↦ by
    simp only [LinearMap.add_apply] at hw ⊢
    rw [twistedInsertAux_cons, twistedInsertAux_cons, twistedInsertAux_cons, hw, map_add,
      map_add, LinearMap.add_apply]
    abel
  map_smul' r c := linearMap_ext_cons' (by simp [twistedInsertAux_one]) fun x w hw ↦ by
    simp only [LinearMap.smul_apply, RingHom.id_apply] at hw ⊢
    rw [twistedInsertAux_cons, twistedInsertAux_cons, hw, map_smul, map_smul, smul_add,
      LinearMap.smul_apply]

/-- Inserting a letter into the empty word gives that letter. -/
@[simp]
theorem twistedInsert_one (τ : M →ₗ[R] M) (c : M) : twistedInsert R τ c 1 = cons R M c 1 :=
  twistedInsertAux_one τ c

/-- Inserting a letter into `x w`: before `x`, or after the twisted letter `τ x`. -/
@[simp]
theorem twistedInsert_cons (τ : M →ₗ[R] M) (c x : M) (w : TensorWords R M) :
    twistedInsert R τ c (cons R M x w) =
      cons R M c (cons R M x w) + cons R M (τ x) (twistedInsert R τ c w) :=
  twistedInsertAux_cons τ c x w

/-- Twisted insertion leaves no empty word. -/
@[simp]
theorem counit_twistedInsert (τ : M →ₗ[R] M) (c : M) (w : TensorWords R M) :
    counit R M (twistedInsert R τ c w) = 0 := by
  refine LinearMap.congr_fun (linearMap_ext_cons' (f := counit R M ∘ₗ twistedInsert R τ c) (g := 0)
    (by simp) fun x w _ ↦ by simp [twistedInsert_cons]) w

/-- The letter component of a twisted insertion is the inserted letter times the counit. -/
@[simp]
theorem letter_reducedProjection_twistedInsert (τ : M →ₗ[R] M) (c : M) (w : TensorWords R M) :
    ReducedTensorWords.letter R M (reducedProjection R M (twistedInsert R τ c w)) =
      counit R M w • c := by
  refine LinearMap.congr_fun (linearMap_ext_cons'
    (f := ReducedTensorWords.letter R M ∘ₗ reducedProjection R M ∘ₗ twistedInsert R τ c)
    (g := (counit R M).smulRight c) (by simp) fun x w _ ↦ by simp [twistedInsert_cons]) w

/-- **The co-Leibniz rule of twisted insertion**: cutting `τx₁ ⋯ τxᵢ c xᵢ₊₁ ⋯ xₙ` puts `c` in
the left half, or in the right half after the twisted left half. -/
theorem deconcatenation_twistedInsert (τ : M →ₗ[R] M) (c : M) (w : TensorWords R M) :
    deconcatenation R M (twistedInsert R τ c w) =
      (twistedInsert R τ c).rTensor (TensorWords R M) (deconcatenation R M w) +
        (twistedInsert R τ c).lTensor (TensorWords R M)
          ((map τ).rTensor (TensorWords R M) (deconcatenation R M w)) := by
  refine LinearMap.congr_fun (linearMap_ext_cons'
    (f := deconcatenation R M ∘ₗ twistedInsert R τ c)
    (g := (twistedInsert R τ c).rTensor (TensorWords R M) ∘ₗ deconcatenation R M +
      (twistedInsert R τ c).lTensor (TensorWords R M) ∘ₗ
        (map τ).rTensor (TensorWords R M) ∘ₗ deconcatenation R M) ?_ fun x w hw' ↦ ?_) w
  · simp [deconcatenation_cons, map_one, add_comm]
  · simp only [LinearMap.comp_apply, LinearMap.add_apply] at hw' ⊢
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

/-- Inserting `t` copies of a letter of degree `p` raises total degrees by `t * p`. -/
theorem insertions_mem_gradedPiece {a : M} {p : ℤ} (ha : a ∈ G.piece p) (t : ℕ) {D : ℤ}
    {w : TensorWords R M} (hw : w ∈ gradedPiece G D) :
    insertions R a t w ∈ gradedPiece G (D + t * p) := by
  have hdeg {E E' : ℤ} {v : TensorWords R M} (h : E = E') (hv : v ∈ gradedPiece G E) :
      v ∈ gradedPiece G E' := h ▸ hv
  have key (n : ℕ) : ∀ (𝒟 : Fin n → ℤ) (x : Fin n → M), (∀ i, x i ∈ G.piece (𝒟 i)) →
      ∀ t : ℕ, insertions R a t (of R M n (PiTensorProduct.tprod R x)) ∈
        gradedPiece G (∑ i, 𝒟 i + t * p) := by
    induction n with
    | zero =>
      intro 𝒟 x _ t
      rw [Subsingleton.elim x fun i ↦ i.elim0, ← one_eq_of_zero, insertions_apply_one,
        Finset.univ_eq_empty, Finset.sum_empty]
      simpa using cons_pow_mem_gradedPiece ha t (one_mem_gradedPiece G)
    | succ n ih =>
      intro 𝒟 x hx t
      rw [← Fin.cons_self_tail x, ← cons_of_tprod, insertions_cons, Fin.sum_univ_succ]
      refine Submodule.sum_mem _ fun k hk ↦ hdeg ?_ (cons_pow_mem_gradedPiece ha k.1
        (cons_mem_gradedPiece (hx 0) (ih (Fin.tail 𝒟) (Fin.tail x) (fun i ↦ hx i.succ) k.2)))
      rw [← Finset.mem_antidiagonal.1 hk]
      push_cast
      simp only [Fin.tail]
      ring
  refine gradedPiece_induction
    (motive := fun w ↦ insertions R a t w ∈ gradedPiece G (D + t * p)) hw
    (fun n 𝒟 x hx hD ↦ hD ▸ key n 𝒟 x hx t) (by simp)
    (fun u v _ _ hu hv ↦ by simpa using add_mem hu hv)
    (fun r u _ hu ↦ by simpa using Submodule.smul_mem _ r hu)

/-- Inserting `t` copies of a letter of degree `p` is homogeneous of degree `t * p`. -/
theorem isHomogeneous_insertions {a : M} {p : ℤ} (ha : a ∈ G.piece p) (t : ℕ) :
    LinearMap.IsHomogeneous (insertions R a t) (gradedPiece G) (gradedPiece G) (t * p) :=
  LinearMap.isHomogeneous_def.2 fun _ _ hw ↦ insertions_mem_gradedPiece ha t hw

/-! ### Coderivations through the insertions -/

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
  · exact Finset.Nat.sum_antidiagonal_sum_antidiagonal_fst_swap i fun i' j' v ↦
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
    rw [LinearMap.sub_apply, map_sub, hL, hK, ← Finset.sum_add_distrib]
    -- `Finset.sum_sub_distrib` does not unify with the subtraction of this tensor square, so the
    -- sums are compared through `eq_sub_of_add_eq`.
    symm
    refine eq_sub_of_add_eq ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [TensorProduct.map_sub_left_apply, TensorProduct.map_sub_right_apply]
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
  simp [LinearMap.rTensor_def, LinearMap.lTensor_def, TensorProduct.map_map]

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
