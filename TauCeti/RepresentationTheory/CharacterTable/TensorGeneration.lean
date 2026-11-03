/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Lagrange
public import TauCeti.RepresentationTheory.CharacterTable.ClassFunction
public import TauCeti.RepresentationTheory.CharacterTable.Kernel
public import TauCeti.RepresentationTheory.Irreducible
public import TauCeti.RepresentationTheory.Simple.Basic
public import TauCeti.RepresentationTheory.Tensor.Power

/-!
# Faithful tensor generation

The Burnside–Brauer theorem bounds the tensor powers needed to contain every irreducible
complex representation of a finite group by the number of distinct values of a faithful
character. The proof interpolates the indicator of the identity fibre of that character.

`FDRep.exists_pos_finrank_hom_tensorPower` proves the slightly stronger assertion that every
nonzero finite-dimensional representation has a nonzero map into one of these tensor powers.
For an irreducible source such a map is injective, so this is occurrence in an actual tensor
power, not merely membership in a span of characters. The zero-fold tensor power is included;
no positivity or irreducibility assumption on the faithful representation is needed.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Theorem 4.3.
* B. Steinberg, *On the Burnside–Brauer–Steinberg theorem*, arXiv:1409.7632,
  Introduction.

The construction uses Mathlib's `Lagrange.basis` and the finite-order trace criterion
`Representation.char_eq_finrank_iff`.
-/

public section

open CategoryTheory

namespace FDRep

universe u v

section Values

variable {k : Type u} {G : Type v} [Field k] [Monoid G] [Finite G]

/-- The distinct values of the character, without a choice of conjugacy representatives. -/
noncomputable def characterValues (V : FDRep k G) : Finset k :=
  (Set.finite_range V.character).toFinset

@[simp]
theorem mem_characterValues (V : FDRep k G) (z : k) :
    z ∈ V.characterValues ↔ ∃ g, V.character g = z := by
  simp [characterValues]

/-- Character values are the image of the character on all group elements. -/
theorem characterValues_eq_image [Fintype G] [DecidableEq k] (V : FDRep k G) :
    V.characterValues = Finset.univ.image V.character := by
  ext z
  simp only [mem_characterValues, Finset.mem_image, Finset.mem_univ, true_and]

/-- The number of distinct values of a character. -/
noncomputable def characterValueCount (V : FDRep k G) : ℕ :=
  V.characterValues.card

@[simp]
theorem card_characterValues (V : FDRep k G) :
    V.characterValues.card = V.characterValueCount :=
  (rfl)

/-- A character has at least one value, even on the zero representation. -/
theorem characterValueCount_pos (V : FDRep k G) : 0 < V.characterValueCount :=
  Finset.card_pos.mpr ⟨V.character 1, (mem_characterValues _ _).mpr ⟨1, rfl⟩⟩

/-- Isomorphic representations have the same character values. -/
theorem characterValues_eq_of_iso (V : FDRep k G) {W : FDRep k G} (e : V ≅ W) :
    V.characterValues = W.characterValues := by
  simp only [characterValues, char_iso e]

/-- Isomorphism does not change the number of character values. -/
theorem characterValueCount_eq_of_iso (V : FDRep k G) {W : FDRep k G} (e : V ≅ W) :
    V.characterValueCount = W.characterValueCount := by
  rw [characterValueCount, characterValueCount, characterValues_eq_of_iso V e]

/-- The Lagrange polynomial isolating the character value at the identity. -/
noncomputable def characterInterpolator (V : FDRep k G) : Polynomial k := by
  classical
  exact Lagrange.basis V.characterValues id (V.character 1)

/-- The interpolator has degree one less than the number of distinct character values. -/
@[simp]
theorem natDegree_characterInterpolator (V : FDRep k G) :
    V.characterInterpolator.natDegree = V.characterValueCount - 1 := by
  classical
  exact Lagrange.natDegree_basis Function.injective_id.injOn
    ((mem_characterValues _ _).mpr ⟨1, rfl⟩)

/-- The coefficient expansion of the interpolator, including its constant term. -/
theorem eval_characterInterpolator_eq_sum (V : FDRep k G) (x : k) :
    V.characterInterpolator.eval x = ∑ n ∈ Finset.range V.characterValueCount,
      V.characterInterpolator.coeff n * x ^ n := by
  apply Polynomial.eval_eq_sum_range'
  rw [natDegree_characterInterpolator]
  exact Nat.sub_lt V.characterValueCount_pos (by decide)

/-- Evaluation of the interpolator detects the identity's character value. -/
theorem eval_characterInterpolator [DecidableEq k] (V : FDRep k G) (g : G) :
    V.characterInterpolator.eval (V.character g) =
      if V.character g = V.character 1 then 1 else 0 := by
  let := Classical.typeDecidableEq k
  by_cases h : V.character g = V.character 1
  · simp only [ite_eq_left h]
    rw [characterInterpolator, h]
    exact Lagrange.eval_basis_self Function.injective_id.injOn
      ((mem_characterValues _ _).mpr ⟨1, rfl⟩)
  · simp only [ite_eq_right h]
    rw [characterInterpolator]
    exact Lagrange.eval_basis_of_ne (v := id) (Ne.symm h)
      ((mem_characterValues _ _).mpr ⟨g, rfl⟩)

end Values

section GroupValues

variable {k : Type u} {G : Type v} [Field k] [Group G] [Finite G]

/-- Character values may equally be enumerated over conjugacy classes. -/
theorem characterValues_eq_image_toConjClasses [DecidableEq k] (V : FDRep k G)
    [Fintype (ConjClasses G)] :
    V.characterValues = Finset.univ.image
      (TauCeti.ClassFunction.toConjClasses (TauCeti.ClassFunction.ofFDRep V)) := by
  classical
  ext z
  simp only [mem_characterValues, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨ConjClasses.mk g, by simp⟩
  · rintro ⟨C, rfl⟩
    obtain ⟨g, rfl⟩ := ConjClasses.exists_rep C
    exact ⟨g, by simp⟩

/-- The number of character values is at most the number of conjugacy classes. -/
theorem characterValueCount_le_card_conjClasses (V : FDRep k G) :
    V.characterValueCount ≤ Nat.card (ConjClasses G) := by
  classical
  let := Fintype.ofFinite (ConjClasses G)
  calc
    V.characterValueCount = (Finset.univ.image
        (TauCeti.ClassFunction.toConjClasses (TauCeti.ClassFunction.ofFDRep V))).card := by
      rw [← card_characterValues, characterValues_eq_image_toConjClasses V]
    _ ≤ Fintype.card (ConjClasses G) := Finset.card_image_le.trans (by simp)
    _ = Nat.card (ConjClasses G) := Fintype.card_eq_nat_card

end GroupValues

section Complex

variable {G : Type v} [Group G] [Finite G]

/-- For a faithful complex representation the interpolator is the indicator of the identity. -/
theorem eval_characterInterpolator_of_injective [DecidableEq G] (V : FDRep ℂ G)
    (hV : Function.Injective V.ρ) (g : G) :
    V.characterInterpolator.eval (V.character g) = if g = 1 then 1 else 0 := by
  classical
  have h : V.character g = V.character 1 ↔ g = 1 := by
    rw [← V.mem_ker_iff_char_eq (isOfFinOrder_of_finite g), MonoidHom.mem_ker]
    exact ⟨fun hg ↦ hV (hg.trans (map_one V.ρ).symm), fun hg ↦ by simp [hg]⟩
  simp only [eval_characterInterpolator, h]

/-- **Burnside–Brauer faithful tensor generation.** Every nonzero finite-dimensional complex
representation has a nonzero map into a tensor power of a faithful representation, with exponent
strictly smaller than the number of its distinct character values. In particular every
irreducible occurs among these tensor powers. -/
theorem exists_pos_finrank_hom_tensorPower (V X : FDRep ℂ G)
    (hV : Function.Injective V.ρ) (hX : 0 < Module.finrank ℂ X) :
    ∃ n < V.characterValueCount, 0 < Module.finrank ℂ (X ⟶ V.tensorPower n) := by
  classical
  let := Fintype.ofFinite G
  let : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr (Nat.card_pos.ne'))
  by_contra! h
  have hzero (n : ℕ) (hn : n < V.characterValueCount) :
      ∑ g : G, V.character g ^ n * X.character g⁻¹ = 0 := by
    have hm := scalar_product_char_eq_finrank_equivariant X (V.tensorPower n)
    simp only [char_tensorPower, Nat.eq_zero_of_le_zero (h n hn), Nat.cast_zero,
      mul_eq_zero, inv_eq_zero] at hm
    exact hm.resolve_left (Invertible.ne_zero _)
  have heval : ∑ g : G,
      V.characterInterpolator.eval (V.character g) * X.character g⁻¹ = 0 := by
    simp_rw [eval_characterInterpolator_eq_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro n hn
    simp_rw [mul_assoc, ← Finset.mul_sum]
    rw [hzero n (Finset.mem_range.mp hn), mul_zero]
  simp only [eval_characterInterpolator_of_injective V hV, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, inv_one, char_one] at heval
  exact (Nat.cast_ne_zero.mpr hX.ne') heval

/-- **Burnside–Brauer, conjugacy-class bound.** Every nonzero finite-dimensional complex
representation has a nonzero map into a tensor power of a faithful representation, with exponent
strictly smaller than the number of conjugacy classes. -/
theorem exists_pos_finrank_hom_tensorPower_lt_card_conjClasses (V X : FDRep ℂ G)
    (hV : Function.Injective V.ρ) (hX : 0 < Module.finrank ℂ X) :
    ∃ n < Nat.card (ConjClasses G), 0 < Module.finrank ℂ (X ⟶ V.tensorPower n) := by
  obtain ⟨n, hn, hm⟩ := exists_pos_finrank_hom_tensorPower V X hV hX
  exact ⟨n, hn.trans_le V.characterValueCount_le_card_conjClasses, hm⟩

/-- Every irreducible complex representation embeds into one of the first tensor powers of a
faithful representation. -/
theorem exists_mono_tensorPower (V X : FDRep ℂ G) [Simple X]
    (hV : Function.Injective V.ρ) :
    ∃ n < V.characterValueCount, ∃ f : X ⟶ V.tensorPower n, Mono f := by
  obtain ⟨n, hn, hm⟩ := exists_pos_finrank_hom_tensorPower V X hV
    ((simple_iff_isIrreducible X).mp inferInstance).finrank_pos
  obtain ⟨f, hf⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hm
  exact ⟨n, hn, f, mono_of_ne_zero_from_simple hf⟩

end Complex

end FDRep
