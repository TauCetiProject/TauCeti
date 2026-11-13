/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.FreeProbability.Circular
public import TauCeti.Probability.FreeProbability.Cumulant.JointSeries

/-!
# R-diagonal elements and their determining sequences

An element is R-diagonal when its joint cumulants with its adjoint vanish except on
nonempty even alternating words. There are two possible starting letters, and hence two
sequences of possibly nonzero cumulants. These sequences determine the entire star
distribution, without a positivity or trace assumption. The sequences here are indexed
by `n : ℕ`, with entry `n` having order `2 * (n + 1)`; no unused order-zero entry is stored.

We prove stability under adjoints and scalar multiplication and show that circular
elements are R-diagonal. The two determining sequences need not agree: their equality
is an additional property, not part of R-diagonality.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 15.
-/

public section

noncomputable section

open Finset

namespace TauCeti

variable {R A B : Type*} [CommRing R]
  [Semiring A] [Algebra R A] [StarRing A]
  [Semiring B] [Algebra R B] [StarRing B]
  {φ : A →ₗ[R] R} {ψ : B →ₗ[R] R} {a : A} {b : B}

/-- The alternating Boolean word of length `n` starting with `c`, used to index
R-diagonal cumulants. -/
def rDiagonalWord (c : Bool) (n : ℕ) (i : Fin n) : Bool :=
  if Even (i : ℕ) then c else !c

/-- The letters of the alternating word are selected by parity. -/
theorem rDiagonalWord_apply (c : Bool) (n : ℕ) (i : Fin n) :
    rDiagonalWord c n i = if Even (i : ℕ) then c else !c := (rfl)

/-- Complementing every letter exchanges the two alternating words. -/
@[simp]
theorem not_rDiagonalWord (c : Bool) (n : ℕ) (i : Fin n) :
    (!rDiagonalWord c n i) = rDiagonalWord (!c) n i := by
  unfold rDiagonalWord
  split <;> simp

/-- An R-diagonal element has a normalized functional and zero cumulants outside even
alternating words in the element and its adjoint. `false` labels the element and `true`
its adjoint. The even alternating words are parametrized by their half-length and their
starting label. -/
structure IsRDiagonal (φ : A →ₗ[R] R) (a : A) : Prop where
  /-- The functional is normalized. -/
  apply_one : φ 1 = 1
  /-- Only nonempty even alternating cumulants may be nonzero. -/
  freeCumulant_eq_zero {n : ℕ} (hn : n ≠ 0) (w : Fin n → Bool)
    (hw : ¬ ∃ k c, n = 2 * (k + 1) ∧
      ∀ i, w i = rDiagonalWord c n i) :
    freeCumulant φ (fun i => if w i then star a else a) univ = 0

/-- The two determining sequences of an element: entry `n` is its alternating cumulant
of order `2 * (n + 1)`, starting with the element for `c = false` and its adjoint for
`c = true`. This definition is meaningful without assuming R-diagonality. -/
def rDiagonalDeterminingSequence (φ : A →ₗ[R] R) (a : A) (c : Bool) (n : ℕ) : R :=
  freeCumulant φ (fun i : Fin (2 * (n + 1)) =>
    if rDiagonalWord c (2 * (n + 1)) i then star a else a) univ

/-- The determining sequences are alternating free cumulants. -/
theorem rDiagonalDeterminingSequence_def (φ : A →ₗ[R] R) (a : A) (c : Bool) (n : ℕ) :
    rDiagonalDeterminingSequence φ a c n =
      freeCumulant φ (fun i : Fin (2 * (n + 1)) =>
        if rDiagonalWord c (2 * (n + 1)) i then star a else a) univ := (rfl)

/-- Taking the adjoint exchanges the two determining sequences. -/
@[simp]
theorem rDiagonalDeterminingSequence_star (φ : A →ₗ[R] R) (a : A) (c : Bool) (n : ℕ) :
    rDiagonalDeterminingSequence φ (star a) c n =
      rDiagonalDeterminingSequence φ a (!c) n := by
  unfold rDiagonalDeterminingSequence
  congr 1
  funext i
  conv_rhs => rw [← not_rDiagonalWord]
  generalize rDiagonalWord c (2 * (n + 1)) i = d
  cases d <;> simp

/-- Scaling multiplies the order-`2 * (n + 1)` determining cumulant by
`(z * star z) ^ (n + 1)`, independently of the starting letter. -/
@[simp]
theorem rDiagonalDeterminingSequence_smul [StarRing R] [StarModule R A]
    (φ : A →ₗ[R] R) (a : A) (z : R) (c : Bool) (n : ℕ) :
    rDiagonalDeterminingSequence φ (z • a) c n =
      (z * star z) ^ (n + 1) * rDiagonalDeterminingSequence φ a c n := by
  have hp (m : ℕ) :
      (∏ i : Fin (2 * m), if rDiagonalWord c (2 * m) i then star z else z) =
        (z * star z) ^ m := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.mul_succ, Fin.prod_univ_succ, Fin.prod_univ_succ]
      simp only [rDiagonalWord, Fin.val_zero, Fin.val_succ, Nat.add_assoc,
        Nat.even_add] at *
      cases c <;> simp_all [pow_succ, mul_comm, mul_left_comm, mul_assoc]
  have he : (fun i : Fin (2 * (n + 1)) =>
      if rDiagonalWord c (2 * (n + 1)) i then star (z • a) else z • a) =
      fun i => (if rDiagonalWord c (2 * (n + 1)) i then star z else z) •
        (if rDiagonalWord c (2 * (n + 1)) i then star a else a) := by
    funext i
    cases rDiagonalWord c (2 * (n + 1)) i <;> simp [star_smul]
  rw [rDiagonalDeterminingSequence_def, he, freeCumulant_smul, hp,
    rDiagonalDeterminingSequence_def]

namespace IsRDiagonal

/-- R-diagonal elements are centered. -/
theorem apply_eq_zero (h : IsRDiagonal φ a) : φ a = 0 := by
  have hz := h.freeCumulant_eq_zero one_ne_zero (fun _ => false) (by
    rintro ⟨k, c, hk, _⟩
    omega)
  simpa [univ_unique] using hz

/-- Adjoint preserves R-diagonality. -/
theorem star (h : IsRDiagonal φ a) : IsRDiagonal φ (star a) where
  apply_one := h.apply_one
  freeCumulant_eq_zero := by
    intro n hn w hw
    have hw' : ¬ ∃ k c, n = 2 * (k + 1) ∧
        ∀ i, (!w i) = rDiagonalWord c n i := by
      rintro ⟨k, c, hk, hc⟩
      apply hw
      refine ⟨k, !c, hk, fun i => ?_⟩
      have hi := congrArg Bool.not (hc i)
      simpa only [not_rDiagonalWord, Bool.not_not] using hi
    convert h.freeCumulant_eq_zero hn (fun i => !w i) hw' using 1
    congr 1
    funext i
    cases w i <;> simp

/-- Scalar multiplication preserves R-diagonality, including multiplication by zero. -/
theorem smul [StarRing R] [StarModule R A] (h : IsRDiagonal φ a) (z : R) :
    IsRDiagonal φ (z • a) where
  apply_one := h.apply_one
  freeCumulant_eq_zero hn w hw := by
    have he : (fun i => if w i then Star.star (z • a) else z • a) =
        fun i => (if w i then Star.star z else z) • (if w i then Star.star a else a) := by
      funext i
      cases w i <;> simp [star_smul]
    rw [he, freeCumulant_smul, h.freeCumulant_eq_zero hn w hw, mul_zero]

/-- The determining sequences give every joint cumulant of an R-diagonal element. In
particular, matching determining sequences gives matching cumulants in every star word. -/
theorem freeCumulant_eq (h : IsRDiagonal φ a) (h' : IsRDiagonal ψ b)
    (hc : ∀ c n, rDiagonalDeterminingSequence φ a c n =
      rDiagonalDeterminingSequence ψ b c n) {n : ℕ} (w : Fin n → Bool) :
    freeCumulant φ (fun i => if w i then Star.star a else a) univ =
      freeCumulant ψ (fun i => if w i then Star.star b else b) univ := by
  by_cases hn : n = 0
  · subst n
    simp [freeCumulant_empty]
  by_cases hw : ∃ k c, n = 2 * (k + 1) ∧
      ∀ i, w i = rDiagonalWord c n i
  · obtain ⟨k, c, rfl, hw⟩ := hw
    simpa only [hw, rDiagonalDeterminingSequence_def] using hc c k
  · rw [h.freeCumulant_eq_zero hn w hw, h'.freeCumulant_eq_zero hn w hw]

/-- The two determining sequences reconstruct the full star distribution, even for
realizations in different algebras. -/
theorem starDistribution_eq [StarRing R] [StarModule R A] [StarModule R B]
    (h : IsRDiagonal φ a) (h' : IsRDiagonal ψ b)
    (hc : ∀ c n, rDiagonalDeterminingSequence φ a c n =
      rDiagonalDeterminingSequence ψ b c n) :
    starDistribution φ (fun _ : Unit => a) = starDistribution ψ (fun _ : Unit => b) := by
  apply starDistribution_eq_iff_jointDistribution_withStar_eq.2
  apply (jointRSeries_eq_iff_jointDistribution_eq (h.apply_one.trans h'.apply_one.symm)).1
  ext w
  by_cases hw : w.toList.length = 0
  · have he : w = 1 := FreeMonoid.ext (List.length_eq_zero_iff.mp hw)
    simp only [he, ← WordSeries.constantCoeff_apply, constantCoeff_jointRSeries]
  rw [coeff_jointRSeries _ _ _ hw, coeff_jointRSeries _ _ _ hw]
  simpa only [StarPolynomial.withStar_def, Function.comp_def] using
    h.freeCumulant_eq h' hc (fun i => (w.toList.get i).2)

end IsRDiagonal

/-- An element is R-diagonal exactly when its adjoint is. -/
@[simp]
theorem isRDiagonal_star_iff : IsRDiagonal φ (star a) ↔ IsRDiagonal φ a :=
  ⟨fun h => by simpa only [star_star] using h.star, IsRDiagonal.star⟩

/-- Equal star distributions have equal determining sequences; no R-diagonal hypothesis
is needed for this direction. -/
theorem rDiagonalDeterminingSequence_eq_of_starDistribution_eq
    [StarRing R] [StarModule R A] [StarModule R B]
    (h : starDistribution φ (fun _ : Unit => a) =
      starDistribution ψ (fun _ : Unit => b)) (c : Bool) (n : ℕ) :
    rDiagonalDeterminingSequence φ a c n = rDiagonalDeterminingSequence ψ b c n := by
  have hj := starDistribution_eq_iff_jointDistribution_withStar_eq.1 h
  have hR := (jointRSeries_eq_iff_jointDistribution_eq
    (by simpa using LinearMap.congr_fun h 1)).2 hj
  have he := congrArg (WordSeries.coeff (FreeMonoid.ofList (List.ofFn
    (fun i : Fin (2 * (n + 1)) => ((), rDiagonalWord c (2 * (n + 1)) i))))) hR
  rw [coeff_jointRSeries_ofFn _ _ _ (by omega : 2 * (n + 1) ≠ 0),
    coeff_jointRSeries_ofFn _ _ _ (by omega : 2 * (n + 1) ≠ 0)] at he
  simpa only [Function.comp_def, StarPolynomial.withStar_def,
    rDiagonalDeterminingSequence_def] using he

/-- For R-diagonal elements, equality of the two determining sequences is equivalent to
equality of star distributions. -/
theorem IsRDiagonal.starDistribution_eq_iff [StarRing R] [StarModule R A] [StarModule R B]
    (h : IsRDiagonal φ a) (h' : IsRDiagonal ψ b) :
    starDistribution φ (fun _ : Unit => a) = starDistribution ψ (fun _ : Unit => b) ↔
      ∀ c n, rDiagonalDeterminingSequence φ a c n =
        rDiagonalDeterminingSequence ψ b c n :=
  ⟨fun he => rDiagonalDeterminingSequence_eq_of_starDistribution_eq he,
    h.starDistribution_eq h'⟩

private theorem freeCumulant_boolWord {n : ℕ} (w : Fin n → Bool) :
    freeCumulant φ ((![a, star a] : Fin 2 → A) ∘
      (fun i => if w i then 1 else 0)) univ =
      freeCumulant φ (fun i => if w i then star a else a) univ := by
  simp [Function.comp_def, apply_ite]

/-- Circular elements are R-diagonal: their only nonzero cumulants are the two alternating
second cumulants. -/
theorem IsCircular.isRDiagonal {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A]
    {φ : A →ₗ[ℂ] ℂ} {a : A} (h : IsCircular φ a) : IsRDiagonal φ a where
  apply_one := h.apply_one
  freeCumulant_eq_zero := by
    intro n hn w hw
    by_cases hn₂ : n = 2
    · subst hn₂
      have heq : w 0 = w 1 := by
        by_contra hne
        apply hw
        refine ⟨0, w 0, by omega, fun i => ?_⟩
        fin_cases i <;> cases h0 : w 0 <;> cases h1 : w 1 <;>
          simp_all [rDiagonalWord]
      have hc := h.freeCumulant_two (fun i => if w i then (1 : Fin 2) else 0)
      rw [freeCumulant_boolWord] at hc
      simpa [heq] using hc
    · have hc := h.freeCumulant_eq_zero hn hn₂
        (fun i => if w i then (1 : Fin 2) else 0)
      simpa only [freeCumulant_boolWord] using hc

/-- Both determining sequences of a standard circular element are `1, 0, 0, …`. -/
@[simp]
theorem IsCircular.rDiagonalDeterminingSequence {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A]
    {φ : A →ₗ[ℂ] ℂ} {a : A} (h : IsCircular φ a) (c : Bool) (n : ℕ) :
    rDiagonalDeterminingSequence φ a c n = if n = 0 then 1 else 0 := by
  rw [rDiagonalDeterminingSequence_def, ← freeCumulant_boolWord]
  by_cases hn : n = 0
  · subst n
    rw [IsCircular.freeCumulant_two h]
    cases c <;> simp [rDiagonalWord]
  · rw [h.freeCumulant_eq_zero (by omega) (by omega), ite_eq_right hn]

end TauCeti
