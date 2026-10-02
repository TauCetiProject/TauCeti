/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.MuTwo.CupNorm
public import TauCeti.FieldTheory.QuadraticForm.StiefelWhitney.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Chain.Induction
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Descent

/-!
# The Stiefel–Whitney classes of an isometry class of regular forms

Let `K` be a field in which `2` is invertible. The Stiefel–Whitney classes `w₁ = ∑ᵢ (aᵢ)` and
`w₂ = ∑_{i<j} (aᵢ) ∪ (aⱼ)` of a diagonal form `⟨a₁, …, aₙ⟩` (`TauCeti.sw1`, `TauCeti.sw2`) depend
only on the isometry class of the form. In rank at least two, Witt's chain theorem reduces this to
invariance under the two elementary steps of a diagonal chain; in rank one, where there is no
binary step, it instead requires invariance when the single coefficient is multiplied by a square.
The latter holds for `w₁` because the Kummer class only depends on the square class, and for `w₂`
because it vanishes in rank one. Both classes are unchanged by permuting the coefficients. A
binary step replaces two coefficients `a, b` by the coefficients `c, d` of an isometric binary form
`⟨c, d⟩ ≅ ⟨a, b⟩`; it leaves `w₁` unchanged because the discriminants agree modulo squares, and it
leaves `w₂` unchanged because of the binary cup identity `(a) ∪ (b) = (c) ∪ (d)`
(`TauCeti.cup_kummerClass_congr`): under the comparison of `H²(G_K, 𝔽₂)` with the Brauer group
both sides are quaternion symbols, and isometric binary forms have equal quaternion symbols.

From these three invariance properties, the descent principle
`TauCeti.RegularFormClass.liftDiagonal` produces functions `TauCeti.sw1Class` and
`TauCeti.sw2Class` on `TauCeti.RegularFormClass K`, which agree with the tuple-level classes on
every diagonal presentation. Composed with `TauCeti.formClass`, they are the Stiefel–Whitney classes
`w₁(q)` and `w₂(q)` of a regular quadratic form `q`, and isometric regular
forms have the same classes.

The binary cup identity rests on the comparison of the Brauer group with Galois cohomology, which
is available for fields `K : Type`; the second class is defined in that generality.

## Main definitions

* `TauCeti.sw1Class`: the first Stiefel–Whitney class of an isometry class of regular forms.
* `TauCeti.sw2Class`: the second Stiefel–Whitney class of an isometry class of regular forms.

## Main results

* `TauCeti.BinaryStep.sw2_eq`: `w₂` is invariant under a binary step of a diagonal chain.
* `TauCeti.sw2_eq_of_equivalent`: isometric diagonal forms have the same `w₂`.
* `TauCeti.sw1Class_mk` and `TauCeti.sw2Class_mk`: the classes of `⟨a₁, …, aₙ⟩` are computed on
  that presentation.
* `TauCeti.sw1Class_formClass` and `TauCeti.sw2Class_formClass`: the classes of a regular form are
  computed on any of its diagonalizations.
* `TauCeti.sw1Class_formClass_congr` and `TauCeti.sw2Class_formClass_congr`: isometric regular
  forms have the same classes.
* `TauCeti.sw1Class_zero`, `TauCeti.sw2Class_zero`, `TauCeti.sw1Class_one`,
  `TauCeti.sw2Class_one`, `TauCeti.sw2Class_eq_zero_of_rank_le_one`,
  `TauCeti.sw1Class_mk_rankOne`, `TauCeti.sw2Class_mk_binary`, `TauCeti.sw1Class_hyperbolicClass`
  and `TauCeti.sw2Class_hyperbolicClass`: the values in rank at most two, on the unit form and on
  the hyperbolic plane.

## References

* J. Milnor, *Algebraic K-theory and quadratic forms*, Invent. Math. 9 (1970), §3.
* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Graduate Studies in Mathematics 67,
  American Mathematical Society (2005), Chapter I, Theorem 5.2, and Chapter V, Proposition 3.18.
-/

public section

noncomputable section

open Finset ContinuousCohomology QuadraticMap

namespace TauCeti

universe u

/-! ### The first class -/

section FirstClass

variable {K : Type u} [Field K] [Invertible (2 : K)]

private theorem sw1_rankOne_eq {a b : Kˣ} (h : IsSquare (a * b)) :
    sw1 (fun _ : Fin 1 => a) = sw1 (fun _ : Fin 1 => b) := by
  rw [sw1_fin_one, sw1_fin_one, ← kummerSquareClassEquiv_squareClass,
    ← kummerSquareClassEquiv_squareClass, (squareClass_eq_iff_isSquare_mul a b).2 h]

/-- **The first Stiefel–Whitney class of an isometry class of regular forms**: for a diagonal
presentation `⟨a₁, …, aₙ⟩` of the class, the sum `w₁ = ∑ᵢ (aᵢ)` of the Kummer classes of its
coefficients. It does not depend on the presentation. -/
def sw1Class : RegularFormClass K → continuousCohomology 1 (trivialF2 (AbsoluteGaloisGroup K)) :=
  RegularFormClass.liftDiagonal (fun p => sw1 p.2) PermutationStep.sw1_eq BinaryStep.sw1_eq
    fun _ _ => sw1_rankOne_eq

/-- `w₁` of the class of a diagonal presentation `⟨a₁, …, aₙ⟩` is `∑ᵢ (aᵢ)`. -/
@[simp]
theorem sw1Class_mk (p : RegularFormPresentation K) :
    sw1Class (Quotient.mk (regularFormSetoid K) p) = sw1 p.2 :=
  RegularFormClass.liftDiagonal_mk _ PermutationStep.sw1_eq BinaryStep.sw1_eq
    (fun _ _ => sw1_rankOne_eq) p

/-- `w₁` of a regular form isometric to `⟨a₁, …, aₙ⟩` is `∑ᵢ (aᵢ)`. -/
theorem sw1Class_formClass {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) {n : ℕ} (w : Fin n → Kˣ)
    (h : Q.Equivalent (weightedSumSquares K fun i => (w i : K))) :
    sw1Class (formClass Q hQ) = sw1 w := by
  rw [formClass_mk Q hQ ⟨n, w⟩ (by rwa [presentedForm_eq_weightedSumSquares_coe]), sw1Class_mk]

/-- **`w₁` is an isometry invariant of regular forms**: isometric regular forms have the same first
Stiefel–Whitney class. -/
theorem sw1Class_formClass_congr {V W : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {Q : QuadraticForm K V} (hQ : Q.Nondegenerate) {R : QuadraticForm K W} (hR : R.Nondegenerate)
    (h : Q.Equivalent R) : sw1Class (formClass Q hQ) = sw1Class (formClass R hR) := by
  rw [(formClass_eq_iff Q hQ R hR).2 h]

/-- The zero class has trivial `w₁`. -/
@[simp]
theorem sw1Class_zero : sw1Class (0 : RegularFormClass K) = 0 := by
  rw [RegularFormClass.zero_def, sw1Class_mk, sw1_fin_zero]

/-- `w₁⟨a⟩ = (a)`. -/
theorem sw1Class_mk_rankOne (a : Kˣ) :
    sw1Class (Quotient.mk (regularFormSetoid K) ⟨1, fun _ => a⟩) = kummerClass a := by
  rw [sw1Class_mk, sw1_fin_one]

/-- The unit class `⟨1⟩` has trivial `w₁`. -/
@[simp]
theorem sw1Class_one : sw1Class (1 : RegularFormClass K) = 0 := by
  rw [← RegularFormClass.mk_rankOne_one, sw1Class_mk_rankOne, kummerClass_one]

/-- `w₁` of the hyperbolic plane `⟨1, -1⟩` is `(-1)`. -/
@[simp]
theorem sw1Class_hyperbolicClass : sw1Class (hyperbolicClass K) = kummerClass (-1) := by
  rw [hyperbolicClass_def, sw1Class_mk, sw1_fin_two]
  simp

end FirstClass

/-! ### The second class -/

section SecondClass

variable {K : Type} [Field K] [Invertible (2 : K)] {n : ℕ}

/-- **A binary step of a diagonal chain does not change `w₂`**: replacing two coefficients of a
diagonal form by the coefficients of an isometric binary form leaves `∑_{i<j} (aᵢ) ∪ (aⱼ)`
unchanged. -/
theorem BinaryStep.sw2_eq {w w' : Fin n → Kˣ} (h : BinaryStep w w') : sw2 w = sw2 w' := by
  have key := h.prod_prod_Ioi_eq
    (F := fun a b => Multiplicative.ofAdd (kummerCup K (squareClass a) (squareClass b)))
    (fun a b c => by rw [squareClass_mul, map_add, AddMonoidHom.add_apply, ofAdd_add])
    (fun a b c d hab => by
      simp only [kummerCup_squareClass_squareClass, cup_kummerClass_congr hab])
  simpa only [sw2_def, ← ofAdd_sum, EmbeddingLike.apply_eq_iff_eq] using key

/-- **The second Stiefel–Whitney class of an isometry class of regular forms**: for a diagonal
presentation `⟨a₁, …, aₙ⟩` of the class, the sum `w₂ = ∑_{i<j} (aᵢ) ∪ (aⱼ)` of the cup products of
the Kummer classes of pairs of distinct coefficients. It does not depend on the presentation. -/
def sw2Class : RegularFormClass K → continuousCohomology 2 (trivialF2 (AbsoluteGaloisGroup K)) :=
  RegularFormClass.liftDiagonal (fun p => sw2 p.2) PermutationStep.sw2_eq BinaryStep.sw2_eq
    fun _ _ _ => by rw [sw2_fin_one, sw2_fin_one]

/-- `w₂` of the class of a diagonal presentation `⟨a₁, …, aₙ⟩` is `∑_{i<j} (aᵢ) ∪ (aⱼ)`. -/
@[simp]
theorem sw2Class_mk (p : RegularFormPresentation K) :
    sw2Class (Quotient.mk (regularFormSetoid K) p) = sw2 p.2 :=
  RegularFormClass.liftDiagonal_mk _ PermutationStep.sw2_eq BinaryStep.sw2_eq
    (fun _ _ _ => by rw [sw2_fin_one, sw2_fin_one]) p

/-- **`w₂` is an isometry invariant of diagonal forms**: isometric diagonal forms
`⟨a₁, …, aₙ⟩ ≅ ⟨b₁, …, bₙ⟩` have the same second Stiefel–Whitney class. -/
theorem sw2_eq_of_equivalent {p q : RegularFormPresentation K}
    (h : (presentedForm p).Equivalent (presentedForm q)) : sw2 p.2 = sw2 q.2 := by
  rw [← sw2Class_mk, ← sw2Class_mk, RegularFormClass.mk_eq_mk_iff.2 h]

/-- `w₂` of a regular form isometric to `⟨a₁, …, aₙ⟩` is `∑_{i<j} (aᵢ) ∪ (aⱼ)`. -/
theorem sw2Class_formClass {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (w : Fin n → Kˣ)
    (h : Q.Equivalent (weightedSumSquares K fun i => (w i : K))) :
    sw2Class (formClass Q hQ) = sw2 w := by
  rw [formClass_mk Q hQ ⟨n, w⟩ (by rwa [presentedForm_eq_weightedSumSquares_coe]), sw2Class_mk]

/-- **`w₂` is an isometry invariant of regular forms**: isometric regular forms have the same
second Stiefel–Whitney class. -/
theorem sw2Class_formClass_congr {V W : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {Q : QuadraticForm K V} (hQ : Q.Nondegenerate) {R : QuadraticForm K W} (hR : R.Nondegenerate)
    (h : Q.Equivalent R) : sw2Class (formClass Q hQ) = sw2Class (formClass R hR) := by
  rw [(formClass_eq_iff Q hQ R hR).2 h]

/-- `w₂` vanishes in ranks `0` and `1`, in particular on `0`, on `1` and on every `⟨a⟩`. -/
theorem sw2Class_eq_zero_of_rank_le_one {x : RegularFormClass K} (hx : x.rank ≤ 1) :
    sw2Class x = 0 := by
  induction x using Quotient.inductionOn with
  | h p =>
    rw [RegularFormClass.rank_mk] at hx
    rw [sw2Class_mk, sw2_eq_zero_of_le_one hx]

/-- The zero class has trivial `w₂`. -/
@[simp]
theorem sw2Class_zero : sw2Class (0 : RegularFormClass K) = 0 :=
  sw2Class_eq_zero_of_rank_le_one (by simp)

/-- The unit class `⟨1⟩` has trivial `w₂`. -/
@[simp]
theorem sw2Class_one : sw2Class (1 : RegularFormClass K) = 0 :=
  sw2Class_eq_zero_of_rank_le_one RegularFormClass.rank_one.le

/-- **`w₂⟨a, b⟩ = (a) ∪ (b)`**. -/
theorem sw2Class_mk_binary (a b : Kˣ) :
    sw2Class (Quotient.mk (regularFormSetoid K) ⟨2, ![a, b]⟩) =
      (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1 (kummerClass a) (kummerClass b) := by
  simp [sw2Class_mk]

/-- The hyperbolic plane `⟨1, -1⟩` has trivial `w₂`. -/
@[simp]
theorem sw2Class_hyperbolicClass : sw2Class (hyperbolicClass K) = 0 := by
  rw [hyperbolicClass_def, sw2Class_mk_binary, kummerClass_one, map_zero,
    LinearMap.zero_apply]

end SecondClass

end TauCeti
