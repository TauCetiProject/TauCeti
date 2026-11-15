/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorCoalgebra.GradedCoalgHom

/-!
# Taylor expansion of graded coderivations along coalgebra morphisms

Let `M` and `N` carry internal integer gradings `G` and `H`, and let `F F' : Tᶜ(M) ⟶ Tᶜ(N)` be
coalgebra morphisms between their reduced tensor coalgebras.  A coderivation `D` along `F` and `F'`
with twist parameter `q` (`TauCeti.ReducedTensorWords.IsGradedCoderivationAlong`) is determined by
its letter component `h = π ∘ D : Tᶜ(M) ⟶ N`
(`TauCeti.ReducedTensorWords.IsGradedCoderivationAlong.eq_of_letter_comp_eq`).  This file
constructs the inverse correspondence: every family of Taylor components `h : Tᶜ(M) ⟶ N` extends
to a unique `(F, F')`-coderivation `gradedCoderivAlong G q F F' h`.

On a word `x₁ ⋯ xₙ`, the Taylor expansion sends a cut into consecutive nonempty blocks
`B₁ ⋯ B_k` and a distinguished index `1 ≤ i ≤ k` to
`(π ∘ F)(τ B₁) ⋯ (π ∘ F)(τ B_{i-1}) · h(B_i) · F'(B_{i+1} ⋯ B_k)`, where `τ` is the
letterwise Koszul twist of parameter `q`.  Splitting off the first block gives the recursion

`D(x₁ ⋯ xₙ) = h(x₁ ⋯ xₙ) + ∑_{0 < d < n} (h(x₁ ⋯ x_d) · F'(x_{d+1} ⋯ xₙ) +`
`  (π ∘ F)(τ(x₁ ⋯ x_d)) · D(x_{d+1} ⋯ xₙ))`.

Deconcatenating either separates the prepended letter or cuts the remaining suffix; using the
coalgebra-morphism identities of `F` and `F'` together with the induction hypothesis on the shorter
suffix yields the `(F, F')`-co-Leibniz rule.

The second half of the file records the conilpotence-filtration bounds for relative coderivations
used in arity-by-arity obstruction arguments for `A∞` homotopies: a relative coderivation is
determined on `filtration n` by `F` and `F'` on `filtration (n - 1)` together with its letter
component on `filtration n`; if two relative coderivations agree up to filtration `n`, their
difference on `filtration (n + 1)` takes primitive values; and the graded commutator of an odd
`(F, F')`-coderivation with odd coderivations intertwined up to filtration `n` satisfies the
relative co-Leibniz rule on `filtration (n + 1)`.

## Main definitions

* `TauCeti.ReducedTensorWords.gradedCoderivAlong`: the `(F, F')`-coderivation with prescribed
  Taylor components.
* `TauCeti.ReducedTensorWords.gradedCoderivAlongEquivTaylor`: `(F, F')`-coderivations are in
  bijection with their Taylor components when `F` and `F'` are coalgebra morphisms.

## Main results

* `TauCeti.ReducedTensorWords.gradedCoderivAlong_subword`: the recursive evaluation rule on blocks.
* `TauCeti.ReducedTensorWords.isGradedCoderivationAlong_gradedCoderivAlong` and
  `TauCeti.ReducedTensorWords.letter_comp_gradedCoderivAlong`: `gradedCoderivAlong G q F F' h` is an
  `(F, F')`-coderivation with letter component `h`.
* `TauCeti.ReducedTensorWords.isHomogeneous_gradedCoderivAlong`: if `π ∘ F` and `F'` have degree
  zero and `h` has degree `r`, then `gradedCoderivAlong G q F F' h` has degree `r`.
* `TauCeti.ReducedTensorWords.IsGradedCoderivationAlong.apply_eq_of_mem_filtration` and
  `TauCeti.ReducedTensorWords.IsGradedCoderivationAlong.sub_apply_eq_ofLetter_of_mem_filtration`:
  filtration determination and top-arity primitive difference for relative coderivations.
* `TauCeti.ReducedTensorWords.IsGradedCoderivationAlong.sub_comp_add_comp_of_mem_filtration`:
  primitive top-arity homotopy residual when `F` and `F'` intertwine odd coderivations up to
  filtration `n`.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.6--3.7.
* K. Lefèvre-Hasegawa, *Sur les A-infini catégories*, Chapter 1, Section 1.2.
-/

public section

open scoped BigOperators DirectSum TensorProduct

universe uR uM uN

namespace TauCeti.ReducedTensorWords

section TaylorExpansion

variable {R : Type uR} {M : Type uM} {N : Type uN} [CommRing R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- The length-`n` component of `gradedCoderivAlong G q F F' h`, defined by strong recursion on
word length by splitting off the first nonempty block. -/
private noncomputable def gradedCoderivAlongComponent (G : InternalGrading R M ℤ) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (h : ReducedTensorWords R M →ₗ[R] N) :
    (n : ℕ) → TensorPower R n M →ₗ[R] ReducedTensorWords R N
  | n =>
    (if hn : 0 < n then ofLetter R N ∘ₗ h ∘ₗ of R M ⟨n, hn⟩ else 0) +
      ∑ d : Fin n, if hd : 0 < d.1 then
        (TensorProduct.lift ((prepend R N).compl₁₂ (h ∘ₗ of R M ⟨d.1, hd⟩)
          (F' ∘ₗ of R M ⟨n - d.1, by have := d.isLt; omega⟩)) +
        TensorProduct.lift ((prepend R N).compl₁₂
          ((letter R N ∘ₗ F) ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist q) ∘ₗ
            of R M ⟨d.1, hd⟩)
          (gradedCoderivAlongComponent G q F F' h (n - d.1)))) ∘ₗ
          TensorPower.splitAt R M n d.1 d.2.le
        else 0
termination_by n => n
decreasing_by have := d.isLt; omega

/-- The `(F, F')`-coderivation of twist parameter `q` with prescribed Taylor components `h`: on a
word `x₁ ⋯ xₙ`, either the whole word is collapsed by `h`, or a nonempty first block of `d`
letters is collapsed by `h` (with `F'` applied to the remaining suffix) or by `(π ∘ F) ∘ τ`
(with the coderivation applied recursively to the remaining suffix). -/
noncomputable def gradedCoderivAlong (G : InternalGrading R M ℤ) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (h : ReducedTensorWords R M →ₗ[R] N) :
    ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N :=
  DirectSum.toModule R {n : ℕ // 0 < n} _ fun n ↦ gradedCoderivAlongComponent G q F F' h n.1

/-- The recursive evaluation rule of `gradedCoderivAlong` on a pure tensor word. -/
private theorem gradedCoderivAlong_of_tprod (G : InternalGrading R M ℤ) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (h : ReducedTensorWords R M →ₗ[R] N) {n : ℕ} (hn : 0 < n) (x : Fin n → M) :
    gradedCoderivAlong G q F F' h (of R M ⟨n, hn⟩ (PiTensorProduct.tprod R x)) =
      ofLetter R N (h (subword R x 0 n)) +
        ∑ d ∈ Finset.range n,
          (prepend R N (h (subword R x 0 d)) (F' (subword R x d (n - d))) +
            prepend R N ((letter R N ∘ₗ F)
              (ReducedTensorWords.map (R := R) (G.koszulTwist q) (subword R x 0 d)))
              (gradedCoderivAlong G q F F' h (subword R x d (n - d)))) := by
  rw [gradedCoderivAlong, toModule_of, gradedCoderivAlongComponent, dite_eq_left hn,
    ← of_tprod_eq_subword R hn x]
  simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.sum_apply]
  congr 1
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rcases Nat.eq_zero_or_pos d.1 with hd | hd
  · simp [hd, subword_length_zero]
  · have _ := d.isLt
    have hx₀ :
        of R M ⟨d.1, hd⟩ (PiTensorProduct.tprod R fun i : Fin d.1 ↦ x (Fin.castLE d.2.le i)) =
          subword R x 0 d.1 := by
      rw [subword_eq_of_tprod R x hd (by omega)]
      exact of_tprod_congr R M hd rfl fun i ↦ congrArg x (Fin.ext (by simp))
    rw [dite_eq_left hd, subword_eq_of_tprod R x (a := d.1) (b := n - d.1) (by omega) (by omega),
      toModule_of]
    simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
      TensorPower.splitAt_tprod, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply]
    rw [hx₀]

/-- The recursive evaluation rule of `gradedCoderivAlong` on a block of a tensor word. -/
theorem gradedCoderivAlong_subword (G : InternalGrading R M ℤ) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (h : ReducedTensorWords R M →ₗ[R] N) {n : ℕ} (x : Fin n → M) (a b : ℕ) :
    gradedCoderivAlong G q F F' h (subword R x a b) =
      ofLetter R N (h (subword R x a b)) +
        ∑ d ∈ Finset.range b,
          (prepend R N (h (subword R x a d)) (F' (subword R x (a + d) (b - d))) +
            prepend R N ((letter R N ∘ₗ F)
              (ReducedTensorWords.map (R := R) (G.koszulTwist q) (subword R x a d)))
              (gradedCoderivAlong G q F F' h (subword R x (a + d) (b - d)))) := by
  by_cases hb : 0 < b ∧ a + b ≤ n
  · obtain ⟨hb₀, hab⟩ := hb
    have hy : ∀ c d : ℕ, c + d ≤ b →
        subword R (fun j : Fin b ↦ x ⟨a + j.1, by omega⟩) c d = subword R x (a + c) d :=
      fun c d hcd ↦
        subword_congr R _ x hcd (by omega) fun j _ ↦ congrArg x (Fin.ext (by simp only; omega))
    have hx := congrArg (gradedCoderivAlong G q F F' h) (subword_eq_of_tprod R x hb₀ hab)
    rw [hx, gradedCoderivAlong_of_tprod G q F F' h hb₀, hy 0 b (by omega), Nat.add_zero]
    congr 1
    refine Finset.sum_congr rfl fun d hd ↦ ?_
    rw [Finset.mem_range] at hd
    rw [hy 0 d (by omega), hy d (b - d) (by omega), Nat.add_zero]
  · have hzero : subword R x a b = 0 := by
      rcases not_and_or.1 hb with hb₀ | hab
      · have hb0 : b = 0 := by omega
        rw [hb0, subword_length_zero]
      · exact subword_eq_zero_of_lt_add R x (by omega)
    rw [hzero, map_zero, map_zero, map_zero, zero_add]
    refine (Finset.sum_eq_zero fun d hd ↦ ?_).symm
    rw [Finset.mem_range] at hd
    rcases not_and_or.1 hb with hb₀ | hab
    · omega
    · rw [subword_eq_zero_of_lt_add R x (a := a + d) (by omega), map_zero, map_zero, map_zero,
        map_zero, add_zero]

/-- The letter component of `gradedCoderivAlong G q F F' h` is `h`. -/
@[simp]
theorem letter_comp_gradedCoderivAlong (G : InternalGrading R M ℤ) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (h : ReducedTensorWords R M →ₗ[R] N) :
    letter R N ∘ₗ gradedCoderivAlong G q F F' h = h := by
  refine linearMap_ext R M fun n x ↦ ?_
  rw [LinearMap.comp_apply, of_tprod_eq_subword R n.2, gradedCoderivAlong_subword, map_add,
    map_sum, letter_ofLetter]
  simp only [map_add, letter_prepend, add_zero, Finset.sum_const_zero]

/-- On a single letter, `gradedCoderivAlong` applies the arity-one component of `h`. -/
@[simp]
theorem gradedCoderivAlong_ofLetter (G : InternalGrading R M ℤ) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (h : ReducedTensorWords R M →ₗ[R] N) (a : M) :
    gradedCoderivAlong G q F F' h (ofLetter R M a) = ofLetter R N (h (ofLetter R M a)) := by
  have h₁ := gradedCoderivAlong_subword G q F F' h (fun _ : Fin 1 ↦ a) 0 1
  simpa only [subword_one R M _ Nat.one_pos, Finset.sum_range_one, subword_length_zero, map_zero,
    LinearMap.zero_apply, add_zero] using h₁

/-- Flip a triangular double sum of prepended blocks tensored with a suffix into a sum over the
cut position `e = d + c`. -/
private theorem sum_range_prepend_tmul_flip {n : ℕ} (x : Fin n → M) (a b : ℕ) (u : ℕ → N)
    (L R' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) :
    (∑ d ∈ Finset.range b, ∑ c ∈ Finset.range (b - d),
      prepend R N (u d) (L (subword R x (a + d) c)) ⊗ₜ[R]
        R' (subword R x (a + d + c) (b - d - c))) =
      ∑ e ∈ Finset.range b,
        (∑ d ∈ Finset.range e, prepend R N (u d) (L (subword R x (a + d) (e - d)))) ⊗ₜ[R]
          R' (subword R x (a + e) (b - e)) := by
  rw [← Finset.sum_range_diag_flip]
  refine Finset.sum_congr rfl fun e he ↦ ?_
  rw [Finset.mem_range] at he
  rw [Finset.sum_range_succ, Nat.sub_self, subword_length_zero, map_zero, map_zero,
    TensorProduct.zero_tmul, add_zero, TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [Finset.mem_range] at hd
  have had : a + d + (e - d) = a + e := by omega
  have hbd : b - d - (e - d) = b - e := by omega
  rw [had, hbd]

/-- Recursive expansion of `F (τ (subword R x a e))` for a coalgebra morphism `F`. -/
private theorem coalgHom_twist_subword_eq (G : InternalGrading R M ℤ) (q : ℤ)
    {F : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} (hF : IsCoalgHom R F) {n : ℕ}
    (x : Fin n → M) (a e : ℕ) :
    F (ReducedTensorWords.map (R := R) (G.koszulTwist q) (subword R x a e)) =
      ofLetter R N ((letter R N ∘ₗ F)
        (ReducedTensorWords.map (R := R) (G.koszulTwist q) (subword R x a e))) +
        ∑ d ∈ Finset.range e,
          prepend R N ((letter R N ∘ₗ F)
            (ReducedTensorWords.map (R := R) (G.koszulTwist q) (subword R x a d)))
            (F (ReducedTensorWords.map (R := R) (G.koszulTwist q)
              (subword R x (a + d) (e - d)))) := by
  nth_rw 1 [hF.eq_coalgHom]
  rw [map_subword, coalgHom_subword, ← map_subword]
  congr 1
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [← map_subword, ← map_subword, ← hF.eq_coalgHom]

/-- Expand the left factor `gradedCoderivAlong` in a sum over cuts of `subword R x a b`. -/
private theorem sum_gradedCoderivAlong_tmul_eq (G : InternalGrading R M ℤ) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (h : ReducedTensorWords R M →ₗ[R] N) {n : ℕ} (x : Fin n → M) (a b : ℕ) :
    ∑ c ∈ Finset.range b,
        gradedCoderivAlong G q F F' h (subword R x a c) ⊗ₜ[R]
          F' (subword R x (a + c) (b - c)) =
      (∑ c ∈ Finset.range b,
        ofLetter R N (h (subword R x a c)) ⊗ₜ[R] F' (subword R x (a + c) (b - c))) +
      ((∑ c ∈ Finset.range b,
        (∑ d ∈ Finset.range c,
          prepend R N (h (subword R x a d)) (F' (subword R x (a + d) (c - d)))) ⊗ₜ[R]
            F' (subword R x (a + c) (b - c))) +
      ∑ c ∈ Finset.range b,
        (∑ d ∈ Finset.range c,
          prepend R N ((letter R N ∘ₗ F)
            (ReducedTensorWords.map (R := R) (G.koszulTwist q) (subword R x a d)))
            (gradedCoderivAlong G q F F' h (subword R x (a + d) (c - d)))) ⊗ₜ[R]
            F' (subword R x (a + c) (b - c))) := by
  simp only [← Finset.sum_add_distrib, ← TensorProduct.add_tmul]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [gradedCoderivAlong_subword, Finset.sum_add_distrib]

/-- Expand the left factor `F ∘ τ` in a sum over cuts of `subword R x a b`. -/
private theorem sum_coalgHom_twist_tmul_eq (G : InternalGrading R M ℤ) (q : ℤ)
    {F : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} (hF : IsCoalgHom R F)
    (D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) {n : ℕ} (x : Fin n → M)
    (a b : ℕ) :
    ∑ c ∈ Finset.range b,
        (F ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist q)) (subword R x a c) ⊗ₜ[R]
          D (subword R x (a + c) (b - c)) =
      (∑ c ∈ Finset.range b,
        ofLetter R N ((letter R N ∘ₗ F)
          (ReducedTensorWords.map (R := R) (G.koszulTwist q) (subword R x a c))) ⊗ₜ[R]
          D (subword R x (a + c) (b - c))) +
      ∑ c ∈ Finset.range b,
        (∑ d ∈ Finset.range c,
          prepend R N ((letter R N ∘ₗ F)
            (ReducedTensorWords.map (R := R) (G.koszulTwist q) (subword R x a d)))
            ((F ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist q))
              (subword R x (a + d) (c - d)))) ⊗ₜ[R]
          D (subword R x (a + c) (b - c)) := by
  simp only [← Finset.sum_add_distrib, ← TensorProduct.add_tmul]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  simp only [LinearMap.comp_apply]
  nth_rw 1 [coalgHom_twist_subword_eq G q hF x a c]
  simp only [LinearMap.comp_apply]

/-- **The Taylor expansion `gradedCoderivAlong` is a coderivation along `F` and `F'`** whenever
`F` and `F'` are coalgebra morphisms. -/
theorem isGradedCoderivationAlong_gradedCoderivAlong (G : InternalGrading R M ℤ) (q : ℤ)
    {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} (hF : IsCoalgHom R F)
    (hF' : IsCoalgHom R F') (h : ReducedTensorWords R M →ₗ[R] N) :
    IsGradedCoderivationAlong G q F F' (gradedCoderivAlong G q F F' h) := by
  set D := gradedCoderivAlong G q F F' h with hD_def
  set τ := ReducedTensorWords.map (R := R) (G.koszulTwist q)
  have key : ∀ {n : ℕ} (x : Fin n → M) (b a : ℕ), deconcatenation R N (D (subword R x a b)) =
      TensorProduct.map D F' (deconcatenation R M (subword R x a b)) +
        TensorProduct.map (F ∘ₗ τ) D (deconcatenation R M (subword R x a b)) := by
    intro n x b
    induction b using Nat.strong_induction_on with
    | _ b ih =>
      intro a
      have hF'cut : ∀ d ∈ Finset.range b,
          LinearMap.rTensor _ (prepend R N (h (subword R x a d)))
              (deconcatenation R N (F' (subword R x (a + d) (b - d)))) =
            ∑ c ∈ Finset.range (b - d), prepend R N (h (subword R x a d))
              (F' (subword R x (a + d) c)) ⊗ₜ[R] F' (subword R x (a + d + c) (b - d - c)) :=
        fun d _ ↦ by
          rw [hF'.deconcatenation_apply, map_deconcatenation_subword, map_sum]
          simp only [LinearMap.rTensor_tmul]
      have hDcut : ∀ d ∈ Finset.range b,
          LinearMap.rTensor _ (prepend R N ((letter R N ∘ₗ F) (τ (subword R x a d))))
              (deconcatenation R N (D (subword R x (a + d) (b - d)))) =
            (∑ c ∈ Finset.range (b - d), prepend R N ((letter R N ∘ₗ F) (τ (subword R x a d)))
              (D (subword R x (a + d) c)) ⊗ₜ[R] F' (subword R x (a + d + c) (b - d - c))) +
            ∑ c ∈ Finset.range (b - d), prepend R N ((letter R N ∘ₗ F) (τ (subword R x a d)))
              ((F ∘ₗ τ) (subword R x (a + d) c)) ⊗ₜ[R] D (subword R x (a + d + c) (b - d - c)) :=
        fun d hd ↦ by
          rcases Nat.eq_zero_or_pos d with rfl | _
          · simp only [subword_length_zero, map_zero, LinearMap.rTensor_zero, LinearMap.zero_apply,
              TensorProduct.zero_tmul, Finset.sum_const_zero, add_zero]
          · rw [ih (b - d) (by rw [Finset.mem_range] at hd; omega) (a + d),
              map_deconcatenation_subword, map_deconcatenation_subword, map_add, map_sum, map_sum]
            simp only [LinearMap.rTensor_tmul]
      rw [hD_def, gradedCoderivAlong_subword, ← hD_def, map_add, deconcatenation_ofLetter, zero_add,
        map_sum, map_deconcatenation_subword, map_deconcatenation_subword]
      simp only [map_add, deconcatenation_prepend, Finset.sum_add_distrib]
      rw [Finset.sum_congr rfl hF'cut, Finset.sum_congr rfl hDcut, Finset.sum_add_distrib,
        sum_range_prepend_tmul_flip, sum_range_prepend_tmul_flip, sum_range_prepend_tmul_flip,
        hD_def, sum_gradedCoderivAlong_tmul_eq, sum_coalgHom_twist_tmul_eq G q hF]
      abel
  rw [isGradedCoderivationAlong_iff, LinearMap.rTensor_def, ← LinearMap.comp_assoc,
    ← TensorProduct.map_comp, LinearMap.comp_id]
  refine linearMap_ext R M fun n x ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    of_tprod_eq_subword R n.2]
  exact key x n.1 0

/-- Every `(F, F')`-coderivation along coalgebra morphisms `F` and `F'` is the Taylor expansion of
its own letter component. -/
theorem IsGradedCoderivationAlong.eq_gradedCoderivAlong {G : InternalGrading R M ℤ} {q : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} (hF : IsCoalgHom R F)
    (hF' : IsCoalgHom R F') (hD : IsGradedCoderivationAlong G q F F' D) :
    D = gradedCoderivAlong G q F F' (letter R N ∘ₗ D) :=
  hD.eq_of_letter_comp_eq (isGradedCoderivationAlong_gradedCoderivAlong G q hF hF' _)
    (letter_comp_gradedCoderivAlong G q F F' _).symm

/-- Coderivations along coalgebra morphisms `F` and `F'` are in bijection with their Taylor
components, the linear maps from reduced tensor words to letters.

Its body is sealed; reason about it through
`TauCeti.ReducedTensorWords.gradedCoderivAlongEquivTaylor_apply` and
`TauCeti.ReducedTensorWords.gradedCoderivAlongEquivTaylor_symm_apply`. -/
noncomputable def gradedCoderivAlongEquivTaylor (G : InternalGrading R M ℤ) (q : ℤ)
    {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} (hF : IsCoalgHom R F)
    (hF' : IsCoalgHom R F') :
    {D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N //
      IsGradedCoderivationAlong G q F F' D} ≃ (ReducedTensorWords R M →ₗ[R] N) where
  toFun D := letter R N ∘ₗ D.1
  invFun h :=
    ⟨gradedCoderivAlong G q F F' h, isGradedCoderivationAlong_gradedCoderivAlong G q hF hF' h⟩
  left_inv D := Subtype.ext (D.2.eq_gradedCoderivAlong hF hF').symm
  right_inv h := letter_comp_gradedCoderivAlong G q F F' h

@[simp]
theorem gradedCoderivAlongEquivTaylor_apply (G : InternalGrading R M ℤ) (q : ℤ)
    {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} (hF : IsCoalgHom R F)
    (hF' : IsCoalgHom R F')
    (D : {D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N //
      IsGradedCoderivationAlong G q F F' D}) :
    gradedCoderivAlongEquivTaylor G q hF hF' D = letter R N ∘ₗ D.1 :=
  (rfl)

@[simp]
theorem gradedCoderivAlongEquivTaylor_symm_apply (G : InternalGrading R M ℤ) (q : ℤ)
    {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} (hF : IsCoalgHom R F)
    (hF' : IsCoalgHom R F') (h : ReducedTensorWords R M →ₗ[R] N) :
    ((gradedCoderivAlongEquivTaylor G q hF hF').symm h).1 = gradedCoderivAlong G q F F' h :=
  (rfl)

/-- `gradedCoderivAlong` sends the zero Taylor map to zero. -/
@[simp]
theorem gradedCoderivAlong_zero (G : InternalGrading R M ℤ) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) :
    gradedCoderivAlong G q F F' 0 = 0 := by
  have key : ∀ {n : ℕ} (x : Fin n → M) (b a : ℕ),
      gradedCoderivAlong G q F F' 0 (subword R x a b) = 0 := by
    intro n x b
    induction b using Nat.strong_induction_on with
    | _ b ih =>
      intro a
      rw [gradedCoderivAlong_subword, LinearMap.zero_apply, map_zero, zero_add]
      refine Finset.sum_eq_zero fun d hd ↦ ?_
      rw [Finset.mem_range] at hd
      rcases Nat.eq_zero_or_pos d with rfl | hd0
      · simp only [subword_length_zero, map_zero, LinearMap.zero_apply, add_zero]
      · rw [LinearMap.zero_apply, map_zero, LinearMap.zero_apply, ih (b - d) (by omega) (a + d),
          map_zero, add_zero]
  refine linearMap_ext R M fun n x ↦ ?_
  rw [LinearMap.zero_apply, of_tprod_eq_subword R n.2]
  exact key x n.1 0

/-- `gradedCoderivAlong` is additive in the Taylor map. -/
theorem gradedCoderivAlong_add (G : InternalGrading R M ℤ) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (h₁ h₂ : ReducedTensorWords R M →ₗ[R] N) :
    gradedCoderivAlong G q F F' (h₁ + h₂) =
      gradedCoderivAlong G q F F' h₁ + gradedCoderivAlong G q F F' h₂ := by
  have key : ∀ {n : ℕ} (x : Fin n → M) (b a : ℕ),
      gradedCoderivAlong G q F F' (h₁ + h₂) (subword R x a b) =
        gradedCoderivAlong G q F F' h₁ (subword R x a b) +
          gradedCoderivAlong G q F F' h₂ (subword R x a b) := by
    intro n x b
    induction b using Nat.strong_induction_on with
    | _ b ih =>
      intro a
      rw [gradedCoderivAlong_subword, gradedCoderivAlong_subword, gradedCoderivAlong_subword,
        LinearMap.add_apply, map_add, add_add_add_comm]
      congr 1
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun d hd ↦ ?_
      rw [Finset.mem_range] at hd
      rcases Nat.eq_zero_or_pos d with rfl | hd0
      · simp only [subword_length_zero, map_zero, LinearMap.zero_apply, add_zero]
      · rw [LinearMap.add_apply, map_add, LinearMap.add_apply, ih (b - d) (by omega) (a + d),
          map_add]
        abel
  refine linearMap_ext R M fun n x ↦ ?_
  rw [LinearMap.add_apply, of_tprod_eq_subword R n.2]
  exact key x n.1 0

/-- `gradedCoderivAlong` is `R`-linear in the Taylor map. -/
theorem gradedCoderivAlong_smul (G : InternalGrading R M ℤ) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (c : R) (h : ReducedTensorWords R M →ₗ[R] N) :
    gradedCoderivAlong G q F F' (c • h) = c • gradedCoderivAlong G q F F' h := by
  have key : ∀ {n : ℕ} (x : Fin n → M) (b a : ℕ),
      gradedCoderivAlong G q F F' (c • h) (subword R x a b) =
        c • gradedCoderivAlong G q F F' h (subword R x a b) := by
    intro n x b
    induction b using Nat.strong_induction_on with
    | _ b ih =>
      intro a
      rw [gradedCoderivAlong_subword, gradedCoderivAlong_subword, LinearMap.smul_apply, map_smul,
        smul_add, Finset.smul_sum]
      congr 1
      refine Finset.sum_congr rfl fun d hd ↦ ?_
      rw [Finset.mem_range] at hd
      rcases Nat.eq_zero_or_pos d with rfl | hd0
      · simp only [subword_length_zero, map_zero, LinearMap.zero_apply, add_zero, smul_zero]
      · rw [LinearMap.smul_apply, map_smul, LinearMap.smul_apply, ih (b - d) (by omega) (a + d),
          map_smul, smul_add]
  refine linearMap_ext R M fun n x ↦ ?_
  rw [LinearMap.smul_apply, of_tprod_eq_subword R n.2]
  exact key x n.1 0

/-- **Homogeneity of `gradedCoderivAlong`.**  If `π ∘ F` and `F'` have degree zero and `h` has
degree `r`, then `gradedCoderivAlong G q F F' h` has degree `r` for every twist parameter `q`. -/
theorem isHomogeneous_gradedCoderivAlong {G : InternalGrading R M ℤ} {H : InternalGrading R N ℤ}
    {q r : ℤ} {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    {h : ReducedTensorWords R M →ₗ[R] N}
    (hf : LinearMap.IsHomogeneous (letter R N ∘ₗ F) (gradedPiece G) H.piece 0)
    (hF' : LinearMap.IsHomogeneous F' (gradedPiece G) (gradedPiece H) 0)
    (hh : LinearMap.IsHomogeneous h (gradedPiece G) H.piece r) :
    LinearMap.IsHomogeneous (gradedCoderivAlong G q F F' h) (gradedPiece G) (gradedPiece H) r := by
  rw [LinearMap.isHomogeneous_def]
  intro D z hz
  refine gradedPiece_induction
    (motive := fun w ↦ gradedCoderivAlong G q F F' h w ∈ gradedPiece H (D + r)) hz ?_ ?_ ?_
  · intro n hn 𝒟 x hx hD
    set g : ℕ → ℤ := fun k ↦ if hk : k < n then 𝒟 ⟨k, hk⟩ else 0 with hg
    have hxg : ∀ i : Fin n, x i ∈ G.piece (g i) := fun i ↦ by simpa [hg] using hx i
    have key : ∀ b a : ℕ, a + b ≤ n →
        gradedCoderivAlong G q F F' h (subword R x a b) ∈
          gradedPiece H ((∑ j ∈ Finset.range b, g (a + j)) + r) := by
      intro b
      induction b using Nat.strong_induction_on with
      | _ b ih =>
        intro a hab
        rw [gradedCoderivAlong_subword]
        refine add_mem
          (ofLetter_mem_gradedPiece H (hh.map_mem (subword_mem_gradedPiece x g hxg a b)))
          (Submodule.sum_mem _ fun d hd ↦ ?_)
        rw [Finset.mem_range] at hd
        rcases Nat.eq_zero_or_pos d with rfl | hd0
        · simp only [subword_length_zero, map_zero, LinearMap.zero_apply, add_zero, zero_mem]
        · have hsum : ∑ j ∈ Finset.range b, g (a + j) =
              (∑ j ∈ Finset.range d, g (a + j)) +
                ∑ j ∈ Finset.range (b - d), g (a + d + j) := by
            rw [← Nat.add_sub_cancel' hd.le, Finset.sum_range_add, Nat.add_sub_cancel_left]
            simp only [Nat.add_assoc]
          have hsub₁ := subword_mem_gradedPiece x g hxg a d
          have hτ₁ : ReducedTensorWords.map (R := R) (G.koszulTwist q) (subword R x a d) ∈
              gradedPiece G (∑ j ∈ Finset.range d, g (a + j)) := by
            rw [map_koszulTwist_apply_of_mem G hsub₁ q]
            exact Submodule.smul_mem _ _ hsub₁
          refine add_mem ?_ ?_
          · rw [hsum, add_right_comm]
            exact prepend_mem_gradedPiece (hh.map_mem hsub₁)
              (by simpa only [add_zero] using
                hF'.map_mem (subword_mem_gradedPiece x g hxg (a + d) (b - d)))
          · rw [hsum, add_assoc]
            exact prepend_mem_gradedPiece (by simpa only [add_zero] using hf.map_mem hτ₁)
              (ih (b - d) (by omega) (a + d) (by omega))
    have hsum : ∑ j ∈ Finset.range n, g (0 + j) = D := by
      rw [← hD, ← Fin.sum_univ_eq_sum_range (fun j ↦ g (0 + j)) n]
      exact Finset.sum_congr rfl fun i _ ↦ by simp [hg]
    rw [of_tprod_eq_subword R hn, ← hsum]
    exact key n 0 (by omega)
  · intro u v _ _ hu hv; rw [map_add]; exact add_mem hu hv
  · intro c u _ hu; rw [map_smul]; exact Submodule.smul_mem _ _ hu

/-- If `F'` preserves the conilpotence filtration, then `gradedCoderivAlong G q F F' h` preserves
the conilpotence filtration. -/
theorem gradedCoderivAlong_mem_filtration (G : InternalGrading R M ℤ) (q : ℤ)
    {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF' : ∀ {k : ℕ} {w : ReducedTensorWords R M},
      w ∈ filtration R M k → F' w ∈ filtration R N k)
    (h : ReducedTensorWords R M →ₗ[R] N) {n : ℕ} {z : ReducedTensorWords R M}
    (hz : z ∈ filtration R M n) :
    gradedCoderivAlong G q F F' h z ∈ filtration R N n := by
  have hsub : ∀ {l : ℕ} (x : Fin l → M) (b a : ℕ),
      gradedCoderivAlong G q F F' h (subword R x a b) ∈ filtration R N b := by
    intro l x b
    induction b using Nat.strong_induction_on with
    | _ b ih =>
      intro a
      rcases Nat.eq_zero_or_pos b with rfl | hb
      · rw [subword_length_zero, map_zero]
        exact Submodule.zero_mem _
      rw [gradedCoderivAlong_subword]
      refine Submodule.add_mem _ (filtration_monotone R N hb (ofLetter_mem_filtration R N _))
        (Submodule.sum_mem _ fun d hd ↦ ?_)
      rw [Finset.mem_range] at hd
      rcases Nat.eq_zero_or_pos d with rfl | hd0
      · simp only [subword_length_zero, map_zero, LinearMap.zero_apply, add_zero]
        exact Submodule.zero_mem _
      · refine Submodule.add_mem _ ?_ ?_
        · exact filtration_monotone R N (by omega)
            (prepend_mem_filtration R N _
              (hF' (subword_mem_filtration R M x (a + d) le_rfl)))
        · exact filtration_monotone R N (by omega)
            (prepend_mem_filtration R N _ (ih (b - d) (by omega) (a + d)))
  have hle : filtration R M n ≤ (filtration R N n).comap (gradedCoderivAlong G q F F' h) := by
    rw [filtration_le_iff]
    rintro k hk _ ⟨x, rfl⟩
    simp only [Submodule.mem_comap]
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r y =>
        rw [map_smul, map_smul, of_tprod_eq_subword R k.2]
        exact Submodule.smul_mem _ _ (filtration_monotone R N hk (hsub y k.1 0))
    | add u v hu hv =>
        rw [map_add, map_add]
        exact Submodule.add_mem _ hu hv
  exact hle hz

/-- **Filtration determination of relative coderivations.**  If `D₁` is an
`(F₁, F₁')`-coderivation and `D₂` is an `(F₂, F₂')`-coderivation with the same twist parameter
`q`, such that `F₁` and `F₂` agree on `filtration (n - 1)`, `F₁'` and `F₂'` agree on
`filtration (n - 1)`, and the letter components of `D₁` and `D₂` agree on `filtration n`, then
`D₁` and `D₂` agree on `filtration n`. -/
theorem IsGradedCoderivationAlong.apply_eq_of_mem_filtration {G : InternalGrading R M ℤ} {q : ℤ}
    {F₁ F₁' D₁ F₂ F₂' D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (h₁ : IsGradedCoderivationAlong G q F₁ F₁' D₁)
    (h₂ : IsGradedCoderivationAlong G q F₂ F₂' D₂) {n : ℕ}
    (hF : ∀ w ∈ filtration R M (n - 1), F₁ w = F₂ w)
    (hF' : ∀ w ∈ filtration R M (n - 1), F₁' w = F₂' w)
    (hl : ∀ w ∈ filtration R M n, letter R N (D₁ w) = letter R N (D₂ w))
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M n) : D₁ z = D₂ z := by
  induction n generalizing z with
  | zero =>
      rw [filtration_zero] at hz
      rw [(Submodule.mem_bot R).1 hz, map_zero, map_zero]
  | succ n ih =>
      rw [Nat.add_sub_cancel] at hF hF'
      have ih' : ∀ u ∈ filtration R M n, D₁ u = D₂ u := fun u hu ↦
        ih (fun w hw ↦ hF w (filtration_monotone R M (Nat.sub_le n 1) hw))
          (fun w hw ↦ hF' w (filtration_monotone R M (Nat.sub_le n 1) hw))
          (fun w hw ↦ hl w (filtration_monotone R M n.le_succ hw)) hu
      refine eq_of_deconcatenation_eq_of_letter_eq R N ?_ (hl z hz)
      obtain ⟨w, hw⟩ := map_deconcatenation_filtration_succ_le R M n ⟨z, hz, rfl⟩
      rw [h₁.deconcatenation_apply, h₂.deconcatenation_apply, ← hw]
      clear hw
      induction w using TensorProduct.inductionOn with
      | tmul u v =>
          simp only [TensorProduct.mapIncl, TensorProduct.map_tmul, Submodule.coe_subtype,
            LinearMap.rTensor_tmul]
          rw [ih' _ u.2, ih' _ v.2, hF' _ v.2,
            hF _ ((isCoalgHom_map (G.koszulTwist q)).mem_filtration u.2)]
      | add u v hu hv =>
          simp only [map_add] at hu hv ⊢
          rw [add_add_add_comm, hu, hv, add_add_add_comm]

end TaylorExpansion

/-! ### Differences, negation, and top-arity filtration bounds -/

section Group

variable {R : Type uR} {M : Type uM} {N : Type uN} [CommRing R] [AddCommMonoid M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- The negation of a coderivation along a pair of maps is a coderivation along them. -/
theorem IsGradedCoderivationAlong.neg {G : InternalGrading R M ℤ} {q : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G q F F' D) :
    IsGradedCoderivationAlong G q F F' (-D) := by
  have h : -D = (-1 : R) • D := LinearMap.ext fun z ↦ by simp
  rw [h]
  exact hD.smul (-1 : R)

/-- The difference of two coderivations along the same pair of maps is a coderivation along
them. -/
theorem IsGradedCoderivationAlong.sub {G : InternalGrading R M ℤ} {q : ℤ}
    {F F' D D' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G q F F' D) (hD' : IsGradedCoderivationAlong G q F F' D') :
    IsGradedCoderivationAlong G q F F' (D - D') := by
  have h : D - D' = D + (-1 : R) • D' := LinearMap.ext fun z ↦ by simp [sub_eq_add_neg]
  rw [h]
  exact hD.add (hD'.smul (-1 : R))

/-- `gradedCoderivAlong` commutes with negation of the Taylor map. -/
theorem gradedCoderivAlong_neg (G : InternalGrading R M ℤ) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (h : ReducedTensorWords R M →ₗ[R] N) :
    gradedCoderivAlong G q F F' (-h) = -gradedCoderivAlong G q F F' h := by
  have hh : -h = (-1 : R) • h := LinearMap.ext fun w ↦ by simp
  rw [hh, gradedCoderivAlong_smul]
  exact LinearMap.ext fun z ↦ by simp

/-- `gradedCoderivAlong` commutes with subtraction of Taylor maps. -/
theorem gradedCoderivAlong_sub (G : InternalGrading R M ℤ) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (h₁ h₂ : ReducedTensorWords R M →ₗ[R] N) :
    gradedCoderivAlong G q F F' (h₁ - h₂) =
      gradedCoderivAlong G q F F' h₁ - gradedCoderivAlong G q F F' h₂ := by
  have hh : h₁ - h₂ = h₁ + (-1 : R) • h₂ := LinearMap.ext fun w ↦ by simp [sub_eq_add_neg]
  rw [hh, gradedCoderivAlong_add, gradedCoderivAlong_smul]
  exact LinearMap.ext fun z ↦ by simp [sub_eq_add_neg]

/-- **Top-arity primitive difference of relative coderivations.**  If `D₁` is an
`(F₁, F₁')`-coderivation and `D₂` is an `(F₂, F₂')`-coderivation with the same twist parameter
`q`, and `F₁ = F₂`, `F₁' = F₂'`, and `π ∘ D₁ = π ∘ D₂` on `filtration n`, then on
`filtration (n + 1)` their difference takes single-letter values: every proper cut involves only
words in `filtration n`, where all maps agree. -/
theorem IsGradedCoderivationAlong.sub_apply_eq_ofLetter_of_mem_filtration
    {G : InternalGrading R M ℤ} {q : ℤ}
    {F₁ F₁' D₁ F₂ F₂' D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (h₁ : IsGradedCoderivationAlong G q F₁ F₁' D₁)
    (h₂ : IsGradedCoderivationAlong G q F₂ F₂' D₂) {n : ℕ}
    (hF : ∀ w ∈ filtration R M n, F₁ w = F₂ w)
    (hF' : ∀ w ∈ filtration R M n, F₁' w = F₂' w)
    (hl : ∀ w ∈ filtration R M n, letter R N (D₁ w) = letter R N (D₂ w))
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M (n + 1)) :
    D₁ z - D₂ z = ofLetter R N (letter R N (D₁ z) - letter R N (D₂ z)) := by
  have hD : ∀ u ∈ filtration R M n, D₁ u = D₂ u := fun u hu ↦
    h₁.apply_eq_of_mem_filtration h₂
      (fun w hw ↦ hF w (filtration_monotone R M (Nat.sub_le n 1) hw))
      (fun w hw ↦ hF' w (filtration_monotone R M (Nat.sub_le n 1) hw)) hl hu
  have hdec : deconcatenation R N (D₁ z - D₂ z) = 0 := by
    obtain ⟨w, hw⟩ := map_deconcatenation_filtration_succ_le R M n ⟨z, hz, rfl⟩
    rw [map_sub, h₁.deconcatenation_apply, h₂.deconcatenation_apply, ← hw, sub_eq_zero]
    clear hw
    induction w using TensorProduct.inductionOn with
    | tmul u v =>
        simp only [TensorProduct.mapIncl, TensorProduct.map_tmul, Submodule.coe_subtype,
          LinearMap.rTensor_tmul]
        rw [hD _ u.2, hD _ v.2, hF' _ v.2,
          hF _ ((isCoalgHom_map (G.koszulTwist q)).mem_filtration u.2)]
    | add u v hu hv =>
        simp only [map_add] at hu hv ⊢
        rw [add_add_add_comm, hu, hv, add_add_add_comm]
  refine eq_of_deconcatenation_eq_of_letter_eq R N ?_ ?_
  · rw [hdec, deconcatenation_ofLetter]
  · rw [map_sub, letter_ofLetter]

/-- A coderivation along `F` and `F'` whose letter component vanishes on `filtration n` takes
single-letter values on `filtration (n + 1)`. -/
theorem IsGradedCoderivationAlong.apply_eq_ofLetter_of_mem_filtration
    {G : InternalGrading R M ℤ} {q : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G q F F' D) {n : ℕ}
    (hl : ∀ w ∈ filtration R M n, letter R N (D w) = 0)
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M (n + 1)) :
    D z = ofLetter R N (letter R N (D z)) := by
  simpa only [LinearMap.zero_apply, map_zero, sub_zero] using
    hD.sub_apply_eq_ofLetter_of_mem_filtration (isGradedCoderivationAlong_zero G q F F')
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      (fun w hw ↦ by rw [hl w hw, LinearMap.zero_apply, map_zero]) hz

/-- Filtered version of `IsGradedCoderivationAlong.comp_sub_negOnePow_smul_comp`: when `F` and `F'`
intertwine `bM` and `bN` on `filtration n`, the graded commutator `bN ∘ D - (-1)^(q r) D ∘ bM`
satisfies the `(F, F')`-co-Leibniz rule on every word in `filtration (n + 1)`. -/
theorem IsGradedCoderivationAlong.deconcatenation_comp_sub_negOnePow_smul_comp_of_mem_filtration
    {G : InternalGrading R M ℤ} {H : InternalGrading R N ℤ} {t q r s : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G t F F' D)
    (hD₁ : LinearMap.IsHomogeneous D (gradedPiece G) (gradedPiece H) r)
    (hbM : IsGradedCoderivation G q bM)
    (hbM₁ : LinearMap.IsHomogeneous bM (gradedPiece G) (gradedPiece G) s)
    (hs : (t * s).negOnePow = (q * r).negOnePow)
    (hbN : IsGradedCoderivation H q bN)
    (hF₀ : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0) {n : ℕ}
    (hF : ∀ w ∈ filtration R M n, bN (F w) = F (bM w))
    (hF' : ∀ w ∈ filtration R M n, bN (F' w) = F' (bM w))
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M (n + 1)) :
    deconcatenation R N ((bN ∘ₗ D - ((((q * r).negOnePow : ℤ) : R)) • (D ∘ₗ bM)) z) =
      TensorProduct.map (bN ∘ₗ D - ((((q * r).negOnePow : ℤ) : R)) • (D ∘ₗ bM)) F'
          (deconcatenation R M z) +
        TensorProduct.map F (bN ∘ₗ D - ((((q * r).negOnePow : ℤ) : R)) • (D ∘ₗ bM))
          (LinearMap.rTensor (ReducedTensorWords R M)
            (ReducedTensorWords.map (R := R) (G.koszulTwist (t + q)))
            (deconcatenation R M z)) := by
  set c : R := (((q * r).negOnePow : ℤ) : R) with hc
  have hτF (w) : ReducedTensorWords.map (R := R) (H.koszulTwist q) (F w) =
      F (ReducedTensorWords.map (R := R) (G.koszulTwist q) w) := by
    simpa only [mul_zero, Int.negOnePow_zero, Units.val_one, Int.cast_one, one_smul,
      LinearMap.comp_apply] using LinearMap.congr_fun (hF₀.map_koszulTwist_comp q) w
  have hτD (w) : ReducedTensorWords.map (R := R) (H.koszulTwist q) (D w) =
      c • D (ReducedTensorWords.map (R := R) (G.koszulTwist q) w) := by
    simpa only [LinearMap.comp_apply, LinearMap.smul_apply] using
      LinearMap.congr_fun (hD₁.map_koszulTwist_comp q) w
  have hτb (w) : ReducedTensorWords.map (R := R) (G.koszulTwist t) (bM w) =
      c • bM (ReducedTensorWords.map (R := R) (G.koszulTwist t) w) := by
    simpa only [hs, LinearMap.comp_apply, LinearMap.smul_apply] using
      LinearMap.congr_fun (hbM₁.map_koszulTwist_comp t) w
  have hττ (a b : ℤ) (w) : ReducedTensorWords.map (R := R) (G.koszulTwist a)
      (ReducedTensorWords.map (R := R) (G.koszulTwist b) w) =
        ReducedTensorWords.map (R := R) (G.koszulTwist (b + a)) w := by
    rw [← LinearMap.comp_apply, ← ReducedTensorWords.map_comp,
      InternalGrading.koszulTwist_comp, add_comm]
  have hcc (x : ReducedTensorWords R N ⊗[R] ReducedTensorWords R N) : c • c • x = x := by
    rw [smul_smul, hc, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one,
      Int.cast_one, one_smul]
  obtain ⟨w, hw⟩ := map_deconcatenation_filtration_succ_le R M n ⟨z, hz, rfl⟩
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sub, map_smul]
  rw [hbN.deconcatenation_apply, hD.deconcatenation_apply, hD.deconcatenation_apply,
    hbM.deconcatenation_apply, ← hw]
  clear hw
  induction w using TensorProduct.inductionOn with
  | tmul u v =>
      have huτ : ReducedTensorWords.map (R := R) (G.koszulTwist t) u.1 ∈ filtration R M n :=
        (isCoalgHom_map (G.koszulTwist t)).mem_filtration u.2
      simp only [TensorProduct.mapIncl, Submodule.coe_subtype, map_add, map_smul,
        TensorProduct.map_tmul, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
        LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, hτF, hτD, hτb, hττ,
        add_comm q t, hF _ huτ, hF' _ v.2, TensorProduct.tmul_sub, TensorProduct.sub_tmul,
        TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', smul_add, hcc]
      abel
  | add u v hu hv =>
      simp only [map_add, smul_add] at hu hv ⊢
      convert congrArg₂ (· + ·) hu hv using 1 <;> abel

/-- Filtered version of `IsGradedCoderivationAlong.comp_add_comp` for an odd relative coderivation
and odd coderivations intertwined on `filtration n`. -/
theorem IsGradedCoderivationAlong.deconcatenation_comp_add_comp_of_mem_filtration
    {G : InternalGrading R M ℤ} {H : InternalGrading R N ℤ} {q r s : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G q F F' D)
    (hD₁ : LinearMap.IsHomogeneous D (gradedPiece G) (gradedPiece H) r)
    (hr : (q * r).negOnePow = -1)
    (hbM : IsGradedCoderivation G q bM)
    (hbM₁ : LinearMap.IsHomogeneous bM (gradedPiece G) (gradedPiece G) s)
    (hs : (q * s).negOnePow = -1) (hbN : IsGradedCoderivation H q bN)
    (hF₀ : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0) {n : ℕ}
    (hF : ∀ w ∈ filtration R M n, bN (F w) = F (bM w))
    (hF' : ∀ w ∈ filtration R M n, bN (F' w) = F' (bM w))
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M (n + 1)) :
    deconcatenation R N ((bN ∘ₗ D + D ∘ₗ bM) z) =
      TensorProduct.map (bN ∘ₗ D + D ∘ₗ bM) F' (deconcatenation R M z) +
        TensorProduct.map F (bN ∘ₗ D + D ∘ₗ bM) (deconcatenation R M z) := by
  have h := hD.deconcatenation_comp_sub_negOnePow_smul_comp_of_mem_filtration hD₁ hbM hbM₁
    (hs.trans hr.symm) hbN hF₀ hF hF' hz
  have he : bN ∘ₗ D - ((((q * r).negOnePow : ℤ) : R)) • (D ∘ₗ bM) = bN ∘ₗ D + D ∘ₗ bM :=
    LinearMap.ext fun w ↦ by
      rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.add_apply, hr, Units.val_neg,
        Units.val_one, Int.cast_neg, Int.cast_one, neg_one_smul R, sub_neg_eq_add]
  have hτ : G.koszulTwist (q + q) = LinearMap.id := by
    rw [← InternalGrading.koszulTwist_comp, InternalGrading.koszulTwist_comp_self]
  simpa only [he, hτ, ReducedTensorWords.map_id, LinearMap.rTensor_id, LinearMap.id_apply] using h

/-- **Top-arity primitive homotopy residual.**  Under the hypotheses of
`deconcatenation_comp_add_comp_of_mem_filtration`, if `F` and `F'` are coalgebra morphisms and the
homotopy residual `R_D = (F - F') - (bN ∘ D + D ∘ bM)` vanishes on `filtration n`, then on
`filtration (n + 1)` it takes single-letter values. -/
theorem IsGradedCoderivationAlong.sub_comp_add_comp_of_mem_filtration
    {G : InternalGrading R M ℤ} {H : InternalGrading R N ℤ} {q r s : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G q F F' D)
    (hD₁ : LinearMap.IsHomogeneous D (gradedPiece G) (gradedPiece H) r)
    (hr : (q * r).negOnePow = -1)
    (hbM : IsGradedCoderivation G q bM)
    (hbM₁ : LinearMap.IsHomogeneous bM (gradedPiece G) (gradedPiece G) s)
    (hs : (q * s).negOnePow = -1) (hbN : IsGradedCoderivation H q bN)
    (hFc : IsCoalgHom R F) (hF'c : IsCoalgHom R F')
    (hF₀ : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0) {n : ℕ}
    (hF : ∀ w ∈ filtration R M n, bN (F w) = F (bM w))
    (hF' : ∀ w ∈ filtration R M n, bN (F' w) = F' (bM w))
    (hR : ∀ w ∈ filtration R M n, ((F - F') - (bN ∘ₗ D + D ∘ₗ bM)) w = 0)
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M (n + 1)) :
    ((F - F') - (bN ∘ₗ D + D ∘ₗ bM)) z =
      ofLetter R N (letter R N (((F - F') - (bN ∘ₗ D + D ∘ₗ bM)) z)) := by
  set E := (F - F') - (bN ∘ₗ D + D ∘ₗ bM)
  have hdec : deconcatenation R N (E z) = 0 := by
    have h₂ := hD.deconcatenation_comp_add_comp_of_mem_filtration hD₁ hr hbM hbM₁ hs hbN hF₀
      hF hF' hz
    have hsub : deconcatenation R N (E z) =
        TensorProduct.map E F' (deconcatenation R M z) +
          TensorProduct.map F E (deconcatenation R M z) := by
      rw [LinearMap.sub_apply, map_sub, LinearMap.sub_apply, map_sub, hFc.deconcatenation_apply,
        hF'c.deconcatenation_apply, h₂]
      induction deconcatenation R M z using TensorProduct.inductionOn with
      | tmul u v =>
          simp only [E, TensorProduct.map_tmul, LinearMap.sub_apply, TensorProduct.sub_tmul,
            TensorProduct.tmul_sub]
          abel
      | add u v hu hv =>
          simp only [map_add] at hu hv ⊢
          convert congrArg₂ (· + ·) hu hv using 1 <;> abel
    rw [hsub, map_deconcatenation_eq_zero_of_mem_filtration R M hR
      (apply_eq_zero_of_mem_filtration_zero R M _) (by simpa using hz),
      map_deconcatenation_eq_zero_of_mem_filtration R M
        (apply_eq_zero_of_mem_filtration_zero R M _) hR (by simpa using hz), add_zero]
  refine eq_of_deconcatenation_eq_of_letter_eq R N ?_ (letter_ofLetter R N _).symm
  rw [hdec, deconcatenation_ofLetter]

end Group

end TauCeti.ReducedTensorWords
