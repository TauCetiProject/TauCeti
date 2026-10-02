/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BigOperators.Finset.Pairs
public import TauCeti.FieldTheory.GaloisCohomology.MuTwo.Cup
public import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Chain.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Discriminant

/-!
# The Stiefel–Whitney classes of a diagonal form in degrees one and two

Let `K` be a field in which `2` is invertible, and write `(a) ∈ H¹(G_K, 𝔽₂)` for the Kummer class
of a unit `a` (`TauCeti.kummerClass`). The **Stiefel–Whitney classes** of a diagonal quadratic form
`⟨a₁, …, aₙ⟩` in degrees one and two are

```text
w₁⟨a₁, …, aₙ⟩ = ∑ᵢ (aᵢ) ∈ H¹(G_K, 𝔽₂),     w₂⟨a₁, …, aₙ⟩ = ∑_{i<j} (aᵢ) ∪ (aⱼ) ∈ H²(G_K, 𝔽₂),
```

the degree-one and degree-two parts of Delzant's total class `∏ᵢ (1 + (aᵢ))`. The cup product is
the mod-two Kummer cup pairing `TauCeti.kummerCup` on square classes, so `w₂` is visibly a function
of the square classes of the coefficients.

This file defines both classes on tuples of units and computes them in low rank and on squares.
Both classes are unchanged by permuting the coefficients, `w₂` because the cup pairing is symmetric
(`TauCeti.kummerCup_comm`). The class `w₁` is the Kummer class of the plain discriminant
`a₁ ⋯ aₙ`, so it is an invariant of the isometry class of the diagonal form.

## Main definitions

* `TauCeti.sw1`: the first Stiefel–Whitney class `∑ᵢ (aᵢ)` of a tuple of units.
* `TauCeti.sw2`: the second Stiefel–Whitney class `∑_{i<j} (aᵢ) ∪ (aⱼ)` of a tuple of units.

## Main results

* `TauCeti.sw1_eq_kummerClass_prod`: `w₁⟨a₁, …, aₙ⟩ = (a₁ ⋯ aₙ)`, the Kummer class of the
  (unsigned) discriminant.
* `TauCeti.sw1_eq_of_equivalent`: isometric diagonal forms have the same `w₁`.
* `TauCeti.sw1_comp_perm`, `TauCeti.sw2_comp_perm`, `TauCeti.PermutationStep.sw1_eq` and
  `TauCeti.PermutationStep.sw2_eq`: both classes are invariant under permuting the coefficients.
* `TauCeti.sw1_fin_zero`, `TauCeti.sw1_fin_one`, `TauCeti.sw2_eq_zero_of_le_one`,
  `TauCeti.sw1_fin_two` and `TauCeti.sw2_fin_two`: both classes vanish in rank `0`,
  `w₁⟨a⟩ = (a)`, `w₂` vanishes in rank `1`, `w₁⟨a, b⟩ = (a) + (b)` and `w₂⟨a, b⟩ = (a) ∪ (b)`.
* `TauCeti.sw1_eq_zero_of_isSquare` and `TauCeti.sw2_eq_zero_of_isSquare`: both classes vanish on
  a tuple of squares, in particular on `⟨1, …, 1⟩`.

## References

* J. Milnor, *Algebraic K-theory and quadratic forms*, Invent. Math. 9 (1970), §3.
* A. Delzant, *Définition des classes de Stiefel-Whitney d'un module quadratique sur un corps de
  caractéristique différente de 2*, C. R. Acad. Sci. Paris 255 (1962), 1366–1368.
-/

public section

noncomputable section

namespace TauCeti

open Finset _root_.ContinuousCohomology

universe u

variable {K : Type u} [Field K] [Invertible (2 : K)] {n : ℕ}

/-- **The first Stiefel–Whitney class** of the diagonal form `⟨a₁, …, aₙ⟩`: the sum
`w₁ = ∑ᵢ (aᵢ)` of the Kummer classes of its coefficients, in `H¹(G_K, 𝔽₂)`. -/
def sw1 (w : Fin n → Kˣ) : continuousCohomology 1 (trivialF2 (AbsoluteGaloisGroup K)) :=
  ∑ i, kummerClass (w i)

/-- **The second Stiefel–Whitney class** of the diagonal form `⟨a₁, …, aₙ⟩`: the sum
`w₂ = ∑_{i<j} (aᵢ) ∪ (aⱼ)` of the cup products of the Kummer classes of pairs of distinct
coefficients, in `H²(G_K, 𝔽₂)`. -/
def sw2 (w : Fin n → Kˣ) : continuousCohomology 2 (trivialF2 (AbsoluteGaloisGroup K)) :=
  ∑ i, ∑ j ∈ Ioi i, kummerCup K (squareClass (w i)) (squareClass (w j))

/-- Unfolding rule for `TauCeti.sw1`. -/
theorem sw1_def (w : Fin n → Kˣ) : sw1 w = ∑ i, kummerClass (w i) :=
  (rfl)

/-- Unfolding rule for `TauCeti.sw2`. -/
theorem sw2_def (w : Fin n → Kˣ) :
    sw2 w = ∑ i, ∑ j ∈ Ioi i, kummerCup K (squareClass (w i)) (squareClass (w j)) :=
  (rfl)

/-! ### The first class is the Kummer class of the discriminant -/

/-- `w₁` read through the Kummer isomorphism on square classes: it is the image of the square
class of the discriminant `a₁ ⋯ aₙ`. -/
theorem sw1_eq_kummerSquareClassEquiv (w : Fin n → Kˣ) :
    sw1 w = kummerSquareClassEquiv K (squareClass (∏ i, w i)) := by
  simp only [sw1_def, squareClass_prod, map_sum, kummerSquareClassEquiv_squareClass]

/-- **`w₁` is the Kummer class of the discriminant**: `w₁⟨a₁, …, aₙ⟩ = (a₁ ⋯ aₙ)`, with the plain
discriminant `a₁ ⋯ aₙ` rather than the signed one. -/
theorem sw1_eq_kummerClass_prod (w : Fin n → Kˣ) : sw1 w = kummerClass (∏ i, w i) := by
  rw [sw1_eq_kummerSquareClassEquiv, kummerSquareClassEquiv_squareClass]

/-- **`w₁` is an isometry invariant**: isometric diagonal forms `⟨a₁, …, aₙ⟩ ≅ ⟨b₁, …, bₘ⟩` have
the same first Stiefel–Whitney class, because their discriminants agree modulo squares. -/
theorem sw1_eq_of_equivalent {p q : RegularFormPresentation K}
    (h : (presentedForm p).Equivalent (presentedForm q)) : sw1 p.2 = sw1 q.2 := by
  rw [sw1_eq_kummerSquareClassEquiv, sw1_eq_kummerSquareClassEquiv,
    squareClass_prod_eq_of_equivalent h]

/-! ### Invariance under permuting the coefficients -/

/-- `w₁` does not depend on the order of the coefficients. -/
@[simp]
theorem sw1_comp_perm (w : Fin n → Kˣ) (σ : Equiv.Perm (Fin n)) : sw1 (w ∘ σ) = sw1 w := by
  rw [sw1_def, sw1_def]
  exact Equiv.sum_comp σ fun i => kummerClass (w i)

/-- `w₂` does not depend on the order of the coefficients, because the cup pairing is
symmetric. -/
@[simp]
theorem sw2_comp_perm (w : Fin n → Kˣ) (σ : Equiv.Perm (Fin n)) : sw2 (w ∘ σ) = sw2 w := by
  rw [sw2_def, sw2_def]
  exact sum_sum_Ioi_comp_perm
    (fun i j => kummerCup K (squareClass (w i)) (squareClass (w j))) σ
      fun _ _ => kummerCup_comm K _ _

/-- A permutation step of a diagonal chain does not change `w₁`. -/
theorem PermutationStep.sw1_eq {w w' : Fin n → Kˣ} (h : PermutationStep w w') :
    sw1 w = sw1 w' := by
  obtain ⟨σ, hσ⟩ := h.exists_perm
  rw [funext hσ]
  exact (sw1_comp_perm w σ).symm

/-- A permutation step of a diagonal chain does not change `w₂`. -/
theorem PermutationStep.sw2_eq {w w' : Fin n → Kˣ} (h : PermutationStep w w') :
    sw2 w = sw2 w' := by
  obtain ⟨σ, hσ⟩ := h.exists_perm
  rw [funext hσ]
  exact (sw2_comp_perm w σ).symm

/-! ### Low rank -/

/-- The first Stiefel–Whitney class of the rank-zero form vanishes. -/
@[simp]
theorem sw1_fin_zero (w : Fin 0 → Kˣ) : sw1 w = 0 := by
  simp [sw1_def]

/-- The second Stiefel–Whitney class of the rank-zero form vanishes. -/
@[simp]
theorem sw2_fin_zero (w : Fin 0 → Kˣ) : sw2 w = 0 := by
  simp [sw2_def]

/-- **`w₂` vanishes in ranks `0` and `1`**: there are no pairs of distinct coefficients. -/
theorem sw2_eq_zero_of_le_one (hn : n ≤ 1) (w : Fin n → Kˣ) : sw2 w = 0 := by
  rw [sw2_def]
  exact sum_eq_zero fun i _ => sum_eq_zero fun j hj => by
    have := Fin.lt_def.mp (mem_Ioi.mp hj)
    omega

/-- `w₁⟨a⟩ = (a)`. -/
@[simp]
theorem sw1_fin_one (w : Fin 1 → Kˣ) : sw1 w = kummerClass (w 0) := by
  simp [sw1_def]

/-- `w₂⟨a⟩ = 0`. -/
@[simp]
theorem sw2_fin_one (w : Fin 1 → Kˣ) : sw2 w = 0 :=
  sw2_eq_zero_of_le_one le_rfl w

/-- `w₁⟨a, b⟩ = (a) + (b)`. -/
@[simp]
theorem sw1_fin_two (w : Fin 2 → Kˣ) : sw1 w = kummerClass (w 0) + kummerClass (w 1) := by
  simp [sw1_def, Fin.sum_univ_two]

/-- **`w₂⟨a, b⟩ = (a) ∪ (b)`**: the second Stiefel–Whitney class of a binary form is the cup
product of the Kummer classes of its two coefficients. -/
@[simp]
theorem sw2_fin_two (w : Fin 2 → Kˣ) :
    sw2 w = (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1
      (kummerClass (w 0)) (kummerClass (w 1)) := by
  have hIoi : Ioi (1 : Fin 2) = ∅ := by decide
  simp [sw2_def, Fin.sum_univ_two, hIoi]

/-! ### Tuples of squares -/

/-- `w₁` vanishes on a tuple of squares. -/
theorem sw1_eq_zero_of_isSquare {w : Fin n → Kˣ} (hw : ∀ i, IsSquare (w i)) : sw1 w = 0 := by
  rw [sw1_def]
  exact sum_eq_zero fun i _ =>
    (kummerClass_eq_zero_iff_square K).mpr (Subgroup.mem_square.mpr (hw i))

/-- `w₂` vanishes on a tuple of squares. -/
theorem sw2_eq_zero_of_isSquare {w : Fin n → Kˣ} (hw : ∀ i, IsSquare (w i)) : sw2 w = 0 := by
  rw [sw2_def]
  exact sum_eq_zero fun i _ => sum_eq_zero fun j _ => by
    rw [(squareClass_eq_zero_iff _).mpr (hw i), map_zero, AddMonoidHom.zero_apply]

/-- `w₁⟨1, …, 1⟩ = 0`. -/
@[simp]
theorem sw1_one : sw1 (1 : Fin n → Kˣ) = 0 :=
  sw1_eq_zero_of_isSquare fun _ => IsSquare.one

/-- `w₂⟨1, …, 1⟩ = 0`. -/
@[simp]
theorem sw2_one : sw2 (1 : Fin n → Kˣ) = 0 :=
  sw2_eq_zero_of_isSquare fun _ => IsSquare.one

end TauCeti
