/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.RingTheory.PowerSeries.Inverse
public import TauCeti.RepresentationTheory.CharacterTable.ClassFunction
public import TauCeti.RepresentationTheory.CharacterTable.Kernel
public import TauCeti.RepresentationTheory.Irreducible
public import TauCeti.RepresentationTheory.Simple.Basic
public import TauCeti.RepresentationTheory.Tensor.Power
import TauCeti.Algebra.Polynomial.Degree.Operations
import TauCeti.RingTheory.PowerSeries.Geometric

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

The multiplicities `mₙ = dim Hom_G(X, V^⊗n)` are collected in the formal power series
`FDRep.tensorMultiplicitySeries V X = ∑ₙ mₙ zⁿ`. Since `mₙ = |G|⁻¹ ∑_g χ_V(g)ⁿ χ_X(g⁻¹)`, it is the
finite sum of geometric series `|G|⁻¹ ∑_g χ_X(g⁻¹) (1 - χ_V(g) z)⁻¹`
(`FDRep.tensorMultiplicitySeries_eq_characterFractions`). Consequently it is a rational function:
multiplied by `Q(z) = ∏_a (1 - a z)`, the product over the distinct character values `a`, it
becomes a polynomial of degree less than the number of values, and the multiplicities satisfy the
linear recurrence whose characteristic polynomial is `∏_a (T - a)`. These identities hold over
every field in which `|G|` is invertible, with the multiplicities read in that field.

For a faithful representation of positive dimension `d`, interpolating the identity fibre after
multiplying by `Tᴮ` shows that every window `[B, B + r)` of `r` consecutive exponents, `r` the
number of character values, contains a tensor power into which a given nonzero representation
maps nontrivially (`FDRep.exists_mem_Ico_pos_finrank_hom_tensorPower`). This gives the sharp
positive-power bound `1 ≤ n ≤ r` and occurrence in arbitrarily large tensor powers, so that the
tensor-multiplicity series has infinitely many nonzero coefficients.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Theorem 4.3.
* B. Steinberg, *On the Burnside–Brauer–Steinberg theorem*, arXiv:1409.7632,
  Introduction and Remark 1.

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

/-- The polynomial `Q(z) = ∏_a (1 - a z)` over the distinct character values `a`. It clears the
denominators of the tensor-multiplicity series; a zero character value contributes the factor
`1`. -/
noncomputable def tensorMultiplicityDenominator (V : FDRep k G) : Polynomial k :=
  ∏ a ∈ V.characterValues, (1 - Polynomial.C a * Polynomial.X)

theorem tensorMultiplicityDenominator_def (V : FDRep k G) :
    V.tensorMultiplicityDenominator =
      ∏ a ∈ V.characterValues, (1 - Polynomial.C a * Polynomial.X) :=
  (rfl)

/-- The denominator has constant term one. -/
@[simp]
theorem coeff_zero_tensorMultiplicityDenominator (V : FDRep k G) :
    V.tensorMultiplicityDenominator.coeff 0 = 1 := by
  simp [tensorMultiplicityDenominator_def, Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.eval_prod]

/-- The denominator has degree at most the number of character values. -/
theorem natDegree_tensorMultiplicityDenominator_le (V : FDRep k G) :
    V.tensorMultiplicityDenominator.natDegree ≤ V.characterValueCount :=
  (Polynomial.natDegree_prod_le _ _).trans <| (Finset.sum_le_card_nsmul _ _ 1 fun a _ ↦
    Polynomial.natDegree_one_sub_C_mul_X_le a).trans (by simp)

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

section MultiplicitySeries

variable {k : Type u} {G : Type v} [Field k] [Monoid G]

/-- The generating series `∑ₙ dim Hom_G(X, V^⊗n) zⁿ` of the multiplicities of `X` in the tensor
powers of `V`, with the dimensions read in `k`. -/
noncomputable def tensorMultiplicitySeries (V X : FDRep k G) : PowerSeries k :=
  PowerSeries.mk fun n ↦ (Module.finrank k (X ⟶ V.tensorPower n) : k)

@[simp]
theorem coeff_tensorMultiplicitySeries (V X : FDRep k G) (n : ℕ) :
    PowerSeries.coeff n (V.tensorMultiplicitySeries X) =
      (Module.finrank k (X ⟶ V.tensorPower n) : k) :=
  PowerSeries.coeff_mk _ _

end MultiplicitySeries

section CharacterFractions

variable {k : Type u} {G : Type v} [Field k] [Group G]

/-- The numerator `N_X(z) = |G|⁻¹ ∑_g χ_X(g⁻¹) ∏_{a ≠ χ_V(g)} (1 - a z)` of the
tensor-multiplicity series, the products running over the distinct character values of `V`. -/
noncomputable def tensorMultiplicityNumerator [Fintype G] (V X : FDRep k G) : Polynomial k := by
  classical
  exact Polynomial.C (Nat.card G : k)⁻¹ * ∑ g : G, Polynomial.C (X.character g⁻¹) *
    ∏ a ∈ V.characterValues.erase (V.character g), (1 - Polynomial.C a * Polynomial.X)

theorem tensorMultiplicityNumerator_def [Fintype G] [DecidableEq k] (V X : FDRep k G) :
    V.tensorMultiplicityNumerator X =
      Polynomial.C (Nat.card G : k)⁻¹ * ∑ g : G, Polynomial.C (X.character g⁻¹) *
        ∏ a ∈ V.characterValues.erase (V.character g), (1 - Polynomial.C a * Polynomial.X) := by
  rw [tensorMultiplicityNumerator]
  congr!

/-- The numerator has degree less than the number of character values. -/
theorem natDegree_tensorMultiplicityNumerator_lt [Fintype G] (V X : FDRep k G) :
    (V.tensorMultiplicityNumerator X).natDegree < V.characterValueCount := by
  classical
  rw [tensorMultiplicityNumerator_def]
  refine (Nat.le_sub_one_iff_lt V.characterValueCount_pos).mp ?_
  refine (Polynomial.natDegree_C_mul_le _ _).trans <|
    Polynomial.natDegree_sum_le_of_forall_le _ _ fun g _ ↦ ?_
  refine (Polynomial.natDegree_C_mul_le _ _).trans <| (Polynomial.natDegree_prod_le _ _).trans <|
    (Finset.sum_le_card_nsmul _ _ 1 fun a _ ↦ Polynomial.natDegree_one_sub_C_mul_X_le a).trans ?_
  rw [smul_eq_mul, mul_one, Finset.card_erase_of_mem ((mem_characterValues _ _).mpr ⟨g, rfl⟩),
    card_characterValues]

variable [Fintype G] [Invertible (Nat.card G : k)]

/-- **Coefficient–pairing interchange.** Pairing `χ_Vⁿ · P(χ_V)` against `χ_X` computes the
combination `∑ⱼ P.coeff j · dim Hom_G(X, V^⊗(n + j))` of tensor multiplicities, for every
polynomial `P`. -/
theorem sum_coeff_mul_finrank_hom_tensorPower_add (V X : FDRep k G) (P : Polynomial k) (n : ℕ) :
    ∑ j ∈ Finset.range (P.natDegree + 1),
        P.coeff j * (Module.finrank k (X ⟶ V.tensorPower (n + j)) : k) =
      (Nat.card G : k)⁻¹ *
        ∑ g : G, V.character g ^ n * P.eval (V.character g) * X.character g⁻¹ := by
  simp_rw [← scalar_product_char_eq_finrank_equivariant, char_tensorPower,
    Polynomial.eval_eq_sum_range, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  ring

/-- **The character-fraction identity.** The tensor-multiplicity series is
`|G|⁻¹ ∑_g χ_X(g⁻¹) (1 - χ_V(g) z)⁻¹`, each factor inverted as a formal power series with
constant coefficient one; the `n`-th coefficient is `|G|⁻¹ ∑_g χ_V(g)ⁿ χ_X(g⁻¹)`, with
`χ_V(g)⁰ = 1` also when `χ_V(g) = 0`. -/
theorem tensorMultiplicitySeries_eq_characterFractions (V X : FDRep k G) :
    V.tensorMultiplicitySeries X =
      PowerSeries.C (Nat.card G : k)⁻¹ * ∑ g : G, PowerSeries.C (X.character g⁻¹) *
        (1 - PowerSeries.C (V.character g) * PowerSeries.X)⁻¹ := by
  have hinv (a : k) : (1 - PowerSeries.C a * PowerSeries.X)⁻¹ = PowerSeries.mk (a ^ ·) :=
    (PowerSeries.inv_eq_iff_mul_eq_one (by simp)).mpr
      (TauCeti.powerSeries_mk_pow_mul_one_sub_C_mul_X_eq_one a)
  ext n
  rw [coeff_tensorMultiplicitySeries, ← scalar_product_char_eq_finrank_equivariant]
  simp only [hinv, char_tensorPower, PowerSeries.coeff_C_mul, map_sum, PowerSeries.coeff_mk,
    mul_comm (V.character _ ^ n)]

/-- **Rationality of the tensor-multiplicity series.** `Q(z) F_X(z) = N_X(z)`. -/
theorem tensorMultiplicityDenominator_mul_tensorMultiplicitySeries (V X : FDRep k G) :
    (V.tensorMultiplicityDenominator : PowerSeries k) * V.tensorMultiplicitySeries X =
      V.tensorMultiplicityNumerator X := by
  classical
  have hcoe (s : Finset k) :
      ((∏ a ∈ s, (1 - Polynomial.C a * Polynomial.X) : Polynomial k) : PowerSeries k) =
        ∏ a ∈ s, (1 - PowerSeries.C a * PowerSeries.X) := by
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
    simp only [map_sub, map_one, map_mul, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coe_C, Polynomial.coe_X]
  rw [tensorMultiplicitySeries_eq_characterFractions, tensorMultiplicityNumerator_def,
    tensorMultiplicityDenominator_def, hcoe]
  simp only [← Polynomial.coeToPowerSeries.ringHom_apply, map_mul, map_sum]
  simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C, hcoe]
  rw [mul_left_comm, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  rw [mul_left_comm, ← Finset.mul_prod_erase _ _ ((mem_characterValues _ _).mpr ⟨g, rfl⟩),
    mul_right_comm, PowerSeries.mul_inv_cancel _ (by simp), one_mul]

end CharacterFractions

section FiniteFractions

variable {k : Type u} {G : Type v} [Field k] [Group G] [Finite G] [Invertible (Nat.card G : k)]

/-- The tensor-multiplicity series depends on `V` and `X` only up to isomorphism. -/
theorem tensorMultiplicitySeries_congr {V V' X X' : FDRep k G} (e : V ≅ V') (f : X ≅ X') :
    V.tensorMultiplicitySeries X = V'.tensorMultiplicitySeries X' := by
  let := Fintype.ofFinite G
  simp only [tensorMultiplicitySeries_eq_characterFractions, char_iso e, char_iso f]

/-- **The linear recurrence of tensor multiplicities.** If `∏_a (T - a) = ∑ⱼ cⱼ Tʲ`, the product
running over the distinct character values of `V`, then `∑ⱼ cⱼ m_{n+j} = 0` for every `n`, where
`mₙ = dim Hom_G(X, V^⊗n)`. -/
theorem sum_coeff_nodal_mul_finrank_hom_tensorPower_add_eq_zero (V X : FDRep k G) (n : ℕ) :
    ∑ j ∈ Finset.range (V.characterValueCount + 1),
        (Lagrange.nodal V.characterValues id).coeff j *
          (Module.finrank k (X ⟶ V.tensorPower (n + j)) : k) = 0 := by
  let := Fintype.ofFinite G
  have h := sum_coeff_mul_finrank_hom_tensorPower_add V X (Lagrange.nodal V.characterValues id) n
  rw [Lagrange.natDegree_nodal, card_characterValues] at h
  rw [h, Finset.sum_eq_zero fun g _ ↦ ?_, mul_zero]
  rw [Lagrange.eval_nodal, Finset.prod_eq_zero ((mem_characterValues _ _).mpr ⟨g, rfl⟩)
    (by simp), mul_zero, zero_mul]

end FiniteFractions

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

/-- Interpolating the identity fibre of a faithful character after multiplying by `Tⁿ`: if
`dim Vⁿ ≠ 0`, some exponent in `[n, n + r)` carries a nonzero map from `X`. -/
private theorem exists_lt_pos_finrank_hom_tensorPower_add (V X : FDRep ℂ G)
    (hV : Function.Injective V.ρ) (hX : 0 < Module.finrank ℂ X) (n : ℕ)
    (hn : (Module.finrank ℂ V : ℂ) ^ n ≠ 0) :
    ∃ j < V.characterValueCount, 0 < Module.finrank ℂ (X ⟶ V.tensorPower (n + j)) := by
  classical
  let := Fintype.ofFinite G
  by_contra! h
  have key := sum_coeff_mul_finrank_hom_tensorPower_add V X V.characterInterpolator n
  rw [natDegree_characterInterpolator, Nat.sub_add_cancel V.characterValueCount_pos,
    Finset.sum_eq_zero fun j hj ↦ by
      rw [Nat.eq_zero_of_le_zero (h j (Finset.mem_range.mp hj)), Nat.cast_zero, mul_zero]] at key
  simp only [eval_characterInterpolator_of_injective V hV, mul_ite, mul_one, mul_zero, ite_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, inv_one, char_one] at key
  exact (mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.mpr Nat.card_pos.ne'))
    (mul_ne_zero hn (Nat.cast_ne_zero.mpr hX.ne'))) key.symm

/-- **Burnside–Brauer faithful tensor generation.** Every nonzero finite-dimensional complex
representation has a nonzero map into a tensor power of a faithful representation, with exponent
strictly smaller than the number of its distinct character values. In particular every
irreducible occurs among these tensor powers. -/
theorem exists_pos_finrank_hom_tensorPower (V X : FDRep ℂ G)
    (hV : Function.Injective V.ρ) (hX : 0 < Module.finrank ℂ X) :
    ∃ n < V.characterValueCount, 0 < Module.finrank ℂ (X ⟶ V.tensorPower n) := by
  obtain ⟨j, hj, hm⟩ := exists_lt_pos_finrank_hom_tensorPower_add V X hV hX 0 (by simp)
  rw [zero_add] at hm
  exact ⟨j, hj, hm⟩

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

/-- **Tensor generation in every window.** For a faithful complex representation `V` of positive
dimension, every nonzero `X` has a nonzero map into `V^⊗n` for some `n` in each window
`[B, B + r)` of `r` consecutive exponents, where `r` is the number of character values of `V`. -/
theorem exists_mem_Ico_pos_finrank_hom_tensorPower (V X : FDRep ℂ G)
    (hV : Function.Injective V.ρ) (hd : 0 < Module.finrank ℂ V) (hX : 0 < Module.finrank ℂ X)
    (B : ℕ) :
    ∃ n ∈ Set.Ico B (B + V.characterValueCount), 0 < Module.finrank ℂ (X ⟶ V.tensorPower n) := by
  obtain ⟨j, hj, hm⟩ := exists_lt_pos_finrank_hom_tensorPower_add V X hV hX B
    (pow_ne_zero _ (Nat.cast_ne_zero.mpr hd.ne'))
  exact ⟨B + j, ⟨Nat.le_add_right B j, Nat.add_lt_add_left hj B⟩, hm⟩

/-- **The sharp positive-power bound.** For a faithful complex representation `V` of positive
dimension, every nonzero `X` has a nonzero map into some positive tensor power `V^⊗n` with `n` at
most the number of character values of `V`. Positivity of `dim V` is necessary: the zero
representation of the trivial group is faithful, and all its positive tensor powers vanish. -/
theorem exists_positive_tensorPower_le_valueCount (V X : FDRep ℂ G)
    (hV : Function.Injective V.ρ) (hd : 0 < Module.finrank ℂ V) (hX : 0 < Module.finrank ℂ X) :
    ∃ n, 0 < n ∧ n ≤ V.characterValueCount ∧ 0 < Module.finrank ℂ (X ⟶ V.tensorPower n) := by
  obtain ⟨n, ⟨h₁, h₂⟩, hm⟩ := exists_mem_Ico_pos_finrank_hom_tensorPower V X hV hd hX 1
  exact ⟨n, h₁, by omega, hm⟩

/-- **Arbitrarily large tensor powers.** For a faithful complex representation `V` of positive
dimension, every nonzero `X` has nonzero maps into arbitrarily large tensor powers of `V`, so the
tensor-multiplicity series of `X` has infinitely many nonzero coefficients. -/
theorem arbitrarily_large_tensorPowers (V X : FDRep ℂ G)
    (hV : Function.Injective V.ρ) (hd : 0 < Module.finrank ℂ V) (hX : 0 < Module.finrank ℂ X)
    (B : ℕ) :
    ∃ n, B ≤ n ∧ 0 < Module.finrank ℂ (X ⟶ V.tensorPower n) := by
  obtain ⟨n, ⟨h, -⟩, hm⟩ := exists_mem_Ico_pos_finrank_hom_tensorPower V X hV hd hX B
  exact ⟨n, h, hm⟩

end Complex

end FDRep
