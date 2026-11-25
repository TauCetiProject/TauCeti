/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Free.Enveloping
public import TauCeti.Algebra.Lie.UniversalEnveloping.BCH
public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Embedding
public import TauCeti.RingTheory.Nilpotent.BCH
import TauCeti.RingTheory.Ideal.Maps

/-!
# The universal Baker–Campbell–Hausdorff element

Let `𝔣` be the free Lie algebra over `ℚ` on two generators `X` and `Y`, and let `U⁺` be the
augmentation ideal of its enveloping algebra. In the truncated enveloping algebra
`U(𝔣) ⧸ (U⁺) ^ (c + 1)` the classes of `X` and `Y` are nilpotent, and the product
`exp X * exp Y` is the exponential of the image of a unique element of the free nilpotent Lie
algebra `𝔣 ⧸ lowerCentralSeries c` of class at most `c`. This element is the Baker–Campbell–
Hausdorff element `bchElement c`; equivalently, its image is the finite logarithm
`log (exp X * exp Y)`. The elements of different classes are compatible under the quotient maps
between free nilpotent Lie algebras, and through degree three `bchElement 3` is the familiar
polynomial `X + Y + ½ ⁅X, Y⁆ + 1/12 (⁅X, ⁅X, Y⁆⁆ + ⁅Y, ⁅Y, X⁆⁆)`. These elements are the universal
formulas for the group law of a nilpotent Lie algebra over a rational algebra.

Existence holds for any two Lie elements of the free Lie algebra on any set of generators
(`TauCeti.FreeLieAlgebra.exists_exp_ι_eq_exp_mul_exp`); it is the case of the word-length
grading of `TauCeti.UniversalEnvelopingAlgebra.exists_exp_ι_eq_exp_mul_exp`, whose total-degree
filtration consists of the powers of the augmentation ideal. Uniqueness comes from injectivity
of the canonical map from the free nilpotent Lie algebra into the truncated enveloping algebra.

## Main definitions

* `TauCeti.FreeLieAlgebra.bchElement`: the Baker–Campbell–Hausdorff element of class `c`.

## Main results

* `TauCeti.FreeLieAlgebra.exists_exp_ι_eq_exp_mul_exp`: in `U(F) ⧸ (U⁺) ^ (c + 1)` for a free
  Lie algebra `F` over `ℚ`, a product of exponentials of Lie elements is the exponential of a Lie
  element.
* `TauCeti.FreeLieAlgebra.exp_lowerCentralQuotientι_bchElement`: `exp` of the image of
  `bchElement c` is `exp X * exp Y`.
* `TauCeti.FreeLieAlgebra.eq_bchElement_iff`: this property characterizes `bchElement c`.
* `TauCeti.FreeLieAlgebra.lowerCentralQuotientι_bchElement`: the image of `bchElement c` is
  `log (exp X * exp Y)`.
* `TauCeti.FreeLieAlgebra.factor_bchElement`: the elements of different classes are compatible.
* `TauCeti.FreeLieAlgebra.bchElement_three`: the element of class three is the cubic
  Baker–Campbell–Hausdorff polynomial.

## References

* C. Reutenauer, *Free Lie Algebras*, Oxford University Press (1993), §3.1.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 1–3*, Springer (1989), Chapter II, §6.
-/

public section

namespace TauCeti.FreeLieAlgebra

open _root_.TauCeti.UniversalEnvelopingAlgebra

-- The canonical map `ι` is a Lie homomorphism into the commutator Lie algebra of `U(F)`.
attribute [local instance 100] LieRing.ofAssociativeRing

section Existence

variable (S : Type*)

local notation "F" => _root_.FreeLieAlgebra ℚ S
local notation "U" => _root_.UniversalEnvelopingAlgebra ℚ F
local notation "J" => HopfIdeal.toIdeal (HopfIdeal.augmentation ℚ U)
local notation "ι" => _root_.UniversalEnvelopingAlgebra.ι ℚ

/-- In the enveloping algebra of a free Lie algebra over `ℚ`, truncated at the `(c + 1)`-st
power of the augmentation ideal, a product of the exponentials of two Lie elements is the
exponential of a Lie element. -/
theorem exists_exp_ι_eq_exp_mul_exp (c : ℕ) (x y : F) :
    ∃ b : F, IsNilpotent.exp (Ideal.Quotient.mk (J ^ (c + 1)) (ι b)) =
      IsNilpotent.exp (Ideal.Quotient.mk (J ^ (c + 1)) (ι x)) *
        IsNilpotent.exp (Ideal.Quotient.mk (J ^ (c + 1)) (ι y)) := by
  -- Transport the graded statement along the equality of the word-length filtration with the
  -- augmentation powers.
  have h := degreeFiltration_eq_augmentation_pow ℚ S (c + 1)
  obtain ⟨b, hb⟩ := UniversalEnvelopingAlgebra.exists_exp_ι_eq_exp_mul_exp
    (homogeneousSubmodule ℚ S) (homogeneousSubmodule_zero ℚ S) c x y
  have he : ∀ z : F, IsNilpotent.exp (Ideal.Quotient.mk (J ^ (c + 1)) (ι z)) =
      Ideal.Quotient.factor h.le (IsNilpotent.exp (Ideal.Quotient.mk _ (ι z))) := by
    intro z
    have hz := (isNilpotent_mk_ι ℚ F c z).map (Ideal.Quotient.factor h.ge)
    rw [Ideal.Quotient.factor_mk] at hz
    rw [hz.map_exp, Ideal.Quotient.factor_mk]
  exact ⟨b, by rw [he, he, he, hb, map_mul]⟩

end Existence

local notation "𝔣" => _root_.FreeLieAlgebra ℚ (Fin 2)
local notation "J" =>
  HopfIdeal.toIdeal (HopfIdeal.augmentation ℚ (_root_.UniversalEnvelopingAlgebra ℚ 𝔣))
local notation "ι" => _root_.UniversalEnvelopingAlgebra.ι ℚ
local notation "X" => _root_.FreeLieAlgebra.of ℚ (0 : Fin 2)
local notation "Y" => _root_.FreeLieAlgebra.of ℚ (1 : Fin 2)

/-- The Baker–Campbell–Hausdorff element of class `c`: the element of the free nilpotent Lie
algebra `𝔣 ⧸ lowerCentralSeries c` on the generators `X = of 0` and `Y = of 1` whose image `b` in
`U(𝔣) ⧸ (U⁺) ^ (c + 1)` satisfies `exp b = exp X * exp Y`, so that `b = log (exp X * exp Y)`. -/
noncomputable def bchElement (c : ℕ) : 𝔣 ⧸ LieModule.lowerCentralSeries ℚ 𝔣 𝔣 c :=
  LieSubmodule.Quotient.mk (exists_exp_ι_eq_exp_mul_exp (Fin 2) c X Y).choose

/-- The defining property of the Baker–Campbell–Hausdorff element: the exponential of its image
in the truncated enveloping algebra is `exp X * exp Y`. -/
theorem exp_lowerCentralQuotientι_bchElement (c : ℕ) :
    IsNilpotent.exp (lowerCentralQuotientι ℚ 𝔣 c (bchElement c)) =
      IsNilpotent.exp (Ideal.Quotient.mk (J ^ (c + 1)) (ι X)) *
        IsNilpotent.exp (Ideal.Quotient.mk (J ^ (c + 1)) (ι Y)) := by
  rw [bchElement, lowerCentralQuotientι_mk]
  exact (exists_exp_ι_eq_exp_mul_exp (Fin 2) c X Y).choose_spec

/-- The Baker–Campbell–Hausdorff element is the unique element of the free nilpotent Lie algebra
whose image `b` in the truncated enveloping algebra satisfies `exp b = exp X * exp Y`. -/
theorem eq_bchElement_iff {c : ℕ} {z : 𝔣 ⧸ LieModule.lowerCentralSeries ℚ 𝔣 𝔣 c} :
    z = bchElement c ↔ IsNilpotent.exp (lowerCentralQuotientι ℚ 𝔣 c z) =
      IsNilpotent.exp (Ideal.Quotient.mk (J ^ (c + 1)) (ι X)) *
        IsNilpotent.exp (Ideal.Quotient.mk (J ^ (c + 1)) (ι Y)) := by
  refine ⟨fun h => h ▸ exp_lowerCentralQuotientι_bchElement c, fun h => ?_⟩
  apply lowerCentralQuotientι_injective ℚ (Fin 2) (ι_injective ℚ 𝔣) c
  rw [← IsNilpotent.log_exp (isNilpotent_lowerCentralQuotientι ℚ 𝔣 c z), h,
    ← exp_lowerCentralQuotientι_bchElement,
    IsNilpotent.log_exp (isNilpotent_lowerCentralQuotientι ℚ 𝔣 c _)]

/-- The image of the Baker–Campbell–Hausdorff element in the truncated enveloping algebra is the
finite logarithm of `exp X * exp Y`. -/
theorem lowerCentralQuotientι_bchElement (c : ℕ) :
    lowerCentralQuotientι ℚ 𝔣 c (bchElement c) =
      IsNilpotent.log (IsNilpotent.exp (Ideal.Quotient.mk (J ^ (c + 1)) (ι X)) *
        IsNilpotent.exp (Ideal.Quotient.mk (J ^ (c + 1)) (ι Y))) := by
  rw [← exp_lowerCentralQuotientι_bchElement,
    IsNilpotent.log_exp (isNilpotent_lowerCentralQuotientι ℚ 𝔣 c _)]

/-- The Baker–Campbell–Hausdorff elements of different classes are compatible: the quotient map
from class at most `d` to class at most `c ≤ d` sends `bchElement d` to `bchElement c`. -/
@[simp]
theorem factor_bchElement {c d : ℕ} (h : c ≤ d) :
    LieIdeal.factor (LieModule.antitone_lowerCentralSeries ℚ 𝔣 𝔣 h) (bchElement d) =
      bchElement c := by
  rw [eq_bchElement_iff, lowerCentralQuotientι_factor ℚ 𝔣 h,
    ← (isNilpotent_lowerCentralQuotientι ℚ 𝔣 d _).map_exp, exp_lowerCentralQuotientι_bchElement,
    map_mul, (isNilpotent_mk_ι ℚ 𝔣 d X).map_exp, (isNilpotent_mk_ι ℚ 𝔣 d Y).map_exp,
    Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk]

/-- **The Baker–Campbell–Hausdorff element through degree three**: the element of class three is
`X + Y + ½ ⁅X, Y⁆ + 1/12 (⁅X, ⁅X, Y⁆⁆ + ⁅Y, ⁅Y, X⁆⁆)`. -/
theorem bchElement_three :
    bchElement 3 = LieSubmodule.Quotient.mk (X + Y + (1 / 2 : ℚ) • ⁅X, Y⁆ +
      (1 / 12 : ℚ) • (⁅X, ⁅X, Y⁆⁆ + ⁅Y, ⁅Y, X⁆⁆)) := by
  -- The classes of the augmentation ideal form an ideal with vanishing fourth power.
  have hI : Ideal.map (Ideal.Quotient.mk (J ^ (3 + 1))) J ^ 4 = ⊥ :=
    le_bot_iff.mp ((Ideal.pow_map_le_map_pow_of_surjective Ideal.Quotient.mk_surjective J 4).trans
      (Ideal.map_quotient_self _).le)
  have hmem : ∀ z : 𝔣, Ideal.Quotient.mk (J ^ (3 + 1)) (ι z) ∈ Ideal.map (Ideal.Quotient.mk _) J :=
    fun z => Ideal.mem_map_of_mem _ (HopfIdeal.mem_toIdeal.mpr (ι_mem_augmentation ℚ 𝔣 z))
  symm
  rw [eq_bchElement_iff, lowerCentralQuotientι_mk,
    ← Ideal.exp_bch_of_pow_four_eq_bot _ hI (hmem X) (hmem Y)]
  simp only [map_add, map_smul, LieHom.map_lie, Ring.lie_def, map_add, map_sub,
    map_mul, map_rat_smul]

end TauCeti.FreeLieAlgebra
