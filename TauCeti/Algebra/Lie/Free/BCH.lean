/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Free.Enveloping
public import TauCeti.Algebra.Lie.UniversalEnveloping.BCH
public import TauCeti.Algebra.Lie.UniversalEnveloping.Completion.Exp
public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Embedding
public import TauCeti.RingTheory.Nilpotent.BCH

import TauCeti.RingTheory.Ideal.Maps
import TauCeti.RingTheory.Ideal.Quotient.Operations

/-!
# The universal Baker–Campbell–Hausdorff element

Let `𝔣` be the free Lie algebra over `ℚ` on two generators `X` and `Y`, and let `U⁺` be the
augmentation ideal of its enveloping algebra. In the truncated enveloping algebra
`U(𝔣) ⧸ (U⁺) ^ (c + 1)` the classes of `X` and `Y` are nilpotent, and the product
`exp X * exp Y` is the exponential of the image of a unique element of the free nilpotent Lie
algebra `𝔣 ⧸ lowerCentralSeries c` of class at most `c`. This element is the Baker–Campbell–
Hausdorff element `bchElement c`; equivalently, its image is the finite logarithm
`log (exp X * exp Y)`. In the word-length completion of `𝔣`, pulling back the product of the
completed exponentials of `X` and `Y` along `completedLieExpEquiv` produces the completed
Baker–Campbell–Hausdorff series `bchCompleted`, whose finite projections agree with `bchElement c`.
The elements of different classes are compatible under the quotient maps between free nilpotent
Lie algebras, and through degree three `bchElement` is given explicitly (`bchElement_zero`,
`bchElement_one`, `bchElement_two`, `bchElement_three`).

Existence holds for any two Lie elements of the free Lie algebra on any set of generators
(`TauCeti.FreeLieAlgebra.exists_exp_ι_eq_exp_mul_exp`); it is the case of the word-length
grading of `TauCeti.UniversalEnvelopingAlgebra.exists_exp_ι_eq_exp_mul_exp`, whose total-degree
filtration consists of the powers of the augmentation ideal. Uniqueness comes from injectivity
of the canonical map from the free nilpotent Lie algebra into the truncated enveloping algebra.

## Main definitions

* `TauCeti.FreeLieAlgebra.bchElement`: the Baker–Campbell–Hausdorff element of class `c`.
* `TauCeti.FreeLieAlgebra.bchCompleted`: the completed Baker–Campbell–Hausdorff series in the
  word-length completion of `𝔣`.

## Main results

* `TauCeti.FreeLieAlgebra.exists_exp_ι_eq_exp_mul_exp`: in `U(F) ⧸ (U⁺) ^ (c + 1)` for a free
  Lie algebra `F` over `ℚ`, a product of exponentials of Lie elements is the exponential of a Lie
  element.
* `TauCeti.FreeLieAlgebra.exp_lowerCentralQuotientι_bchElement`: `exp` of the image of
  `bchElement c` is `exp X * exp Y`.
* `TauCeti.FreeLieAlgebra.eq_bchElement_iff`: this property characterizes `bchElement c`.
* `TauCeti.FreeLieAlgebra.lowerCentralQuotientι_bchElement`: the image of `bchElement c` is
  `log (exp X * exp Y)`.
* `TauCeti.FreeLieAlgebra.completedExp_completedLieToU_bchCompleted`: in `completedEnveloping`,
  `completedExp` of `bchCompleted` is the product of the completed exponentials of `X` and `Y`.
* `TauCeti.FreeLieAlgebra.quotEquivOfEq_completionProjection_bchCompleted`: the finite
  projections of `bchCompleted` are `bchElement c`.
* `TauCeti.FreeLieAlgebra.factor_bchElement`: the elements of different classes are compatible.
* `TauCeti.FreeLieAlgebra.bchElement_zero`, `TauCeti.FreeLieAlgebra.bchElement_one`,
  `TauCeti.FreeLieAlgebra.bchElement_two`, `TauCeti.FreeLieAlgebra.bchElement_three`: explicit
  formulas through class three.

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

section Completed

open PositiveDegrees (naturals)

local notation "𝓛" => homogeneousSubmodule ℚ (Fin 2)
local notation "𝓕" => degreeFiltration 𝓛 naturals.degree (naturals.eq_bot_of_degree_neg 𝓛)

private noncomputable def bchGroupLikeFactor (i : Fin 2) :=
  completedLieExpEquiv naturals 𝓛
    (LieIdeal.toCompletion (naturals.degreeIdeal 𝓛) (naturals.degreeIdeal_antitone 𝓛)
      (_root_.FreeLieAlgebra.of ℚ i))

/-- The completed Baker–Campbell–Hausdorff series in the word-length completion of `𝔣`,
obtained by pulling back the product of the completed exponentials of the two free generators. -/
noncomputable def bchCompleted : naturals.completedLie 𝓛 :=
  (completedLieExpEquiv naturals 𝓛).symm ⟨(bchGroupLikeFactor 0).val * (bchGroupLikeFactor 1).val,
    (bchGroupLikeFactor 0).property.mul (bchGroupLikeFactor 1).property⟩

/-- In the completed enveloping algebra of `𝔣`, the completed exponential of `bchCompleted` is
the product of the completed exponentials of the two canonical generators. -/
theorem completedExp_completedLieToU_bchCompleted :
    (𝓕).completedExp ⟨completedLieToU naturals 𝓛 bchCompleted,
        completedLieToU_mem_completionIdeal_one naturals 𝓛 bchCompleted⟩ =
      (𝓕).completedExp ⟨(𝓕).toCompletion (ι X), toCompletion_ι_mem_completionIdeal_one
        𝓛 naturals.degree (naturals.eq_bot_of_degree_nonpos 𝓛) X⟩ *
      (𝓕).completedExp ⟨(𝓕).toCompletion (ι Y), toCompletion_ι_mem_completionIdeal_one
        𝓛 naturals.degree (naturals.eq_bot_of_degree_nonpos 𝓛) Y⟩ := by
  have happ := congrArg Subtype.val <| (completedLieExpEquiv naturals 𝓛).apply_symm_apply
    ⟨_, (bchGroupLikeFactor 0).property.mul (bchGroupLikeFactor 1).property⟩
  simp only [bchCompleted, bchGroupLikeFactor, coe_completedLieExpEquiv_apply,
    completedLieToU_toCompletion] at happ ⊢
  exact happ

private noncomputable abbrev bchEnvEquiv (c : ℕ) :=
  Ideal.quotientEquivAlgOfEq ℚ (naturals_degreeFiltration_eq_augmentation_pow ℚ (Fin 2) (c + 1))

private theorem bchEnvEquiv_projection_completedExp (c : ℕ) (x : (𝓕).completionIdeal 1) :
    bchEnvEquiv c ((𝓕).projection c ((𝓕).completedExp x)) =
      IsNilpotent.exp (bchEnvEquiv c ((𝓕).projection c x)) := by
  rw [(𝓕).projection_completedExp x c,
    ((𝓕).isNilpotent_projection x.property c).map_exp (bchEnvEquiv c)]

/-- Identifying the degree ideal with the lower central series sends the order-`c` projection of
`bchCompleted` to `bchElement c`. -/
@[simp]
theorem quotEquivOfEq_completionProjection_bchCompleted (c : ℕ) :
    ((naturals.degreeIdeal 𝓛 c).quotEquivOfEq _
        (naturals_degreeIdeal_eq_lowerCentralSeries ℚ (Fin 2) c))
      (LieIdeal.completionProjection (naturals.degreeIdeal 𝓛)
        (naturals.degreeIdeal_antitone 𝓛) c bchCompleted) = bchElement c := by
  rw [eq_bchElement_iff, ← quotientEquivAlgOfEq_truncatedLieToU ℚ (Fin 2) c,
    ← projection_completedLieToU naturals 𝓛 c bchCompleted,
    ← bchEnvEquiv_projection_completedExp c
      ⟨_, completedLieToU_mem_completionIdeal_one naturals 𝓛 bchCompleted⟩,
    completedExp_completedLieToU_bchCompleted, map_mul, map_mul,
    bchEnvEquiv_projection_completedExp c, bchEnvEquiv_projection_completedExp c]
  simp [bchEnvEquiv]

/-- The order-`c` projection of `bchCompleted` is `bchElement c` transported back along the
identification of degree ideals with lower central terms. -/
theorem completionProjection_bchCompleted (c : ℕ) :
    LieIdeal.completionProjection (naturals.degreeIdeal 𝓛)
        (naturals.degreeIdeal_antitone 𝓛) c bchCompleted =
      ((naturals.degreeIdeal 𝓛 c).quotEquivOfEq _
          (naturals_degreeIdeal_eq_lowerCentralSeries ℚ (Fin 2) c)).symm (bchElement c) := by
  rw [← quotEquivOfEq_completionProjection_bchCompleted c, LieEquiv.symm_apply_apply]

end Completed

/-! ### Explicit formulas in low nilpotency class -/

private noncomputable def quotAugmentationIdeal (c : ℕ) :
    Ideal (_root_.UniversalEnvelopingAlgebra ℚ 𝔣 ⧸ J ^ (c + 1)) :=
  Ideal.map (Ideal.Quotient.mk (J ^ (c + 1))) J

private theorem quotAugmentationIdeal_def (c : ℕ) :
    quotAugmentationIdeal c = Ideal.map (Ideal.Quotient.mk (J ^ (c + 1))) J := rfl

private theorem mk_ι_mem_quotAugmentationIdeal (c : ℕ) (x : 𝔣) :
    Ideal.Quotient.mk (J ^ (c + 1)) (ι x) ∈ quotAugmentationIdeal c :=
  Ideal.mem_map_of_mem _
    (HopfIdeal.mem_toIdeal.mpr (UniversalEnvelopingAlgebra.ι_mem_augmentation ℚ 𝔣 x))

/-- At class `0`, `bchElement 0` vanishes. -/
@[simp] theorem bchElement_zero : bchElement 0 = 0 := by
  obtain ⟨x, hx⟩ := LieIdeal.surjective_mkQ _ (bchElement 0)
  rw [← hx, LieIdeal.mkQ_eq_zero]
  simp only [LieModule.lowerCentralSeries_zero, LieSubmodule.mem_top]

/-- At class `1`, `bchElement 1` is the sum `X + Y` of the two generators. -/
theorem bchElement_one :
    bchElement 1 = LieSubmodule.Quotient.mk X + LieSubmodule.Quotient.mk Y := by
  symm
  apply lowerCentralQuotientι_injective ℚ (Fin 2) (ι_injective ℚ 𝔣) 1
  rw [lowerCentralQuotientι_bchElement,
    Ideal.log_exp_mul_exp_of_pow_three_eq_bot (quotAugmentationIdeal 1)
      (Ideal.map_mk_pow_eq_bot_of_le (Ideal.pow_le_pow_right (by decide : 1 + 1 ≤ 3)))
      (mk_ι_mem_quotAugmentationIdeal 1 X) (mk_ι_mem_quotAugmentationIdeal 1 Y)]
  have hcomm : Ideal.Quotient.mk (J ^ (1 + 1)) (ι X) * Ideal.Quotient.mk (J ^ (1 + 1)) (ι Y) -
      Ideal.Quotient.mk (J ^ (1 + 1)) (ι Y) * Ideal.Quotient.mk (J ^ (1 + 1)) (ι X) = 0 := by
    rw [← Ideal.mem_bot, ← Ideal.map_mk_pow_self J (1 + 1), ← quotAugmentationIdeal_def 1,
      Submodule.pow_succ (quotAugmentationIdeal 1), Submodule.pow_one]
    exact Submodule.sub_mem _
      (Ideal.mul_mem_mul (mk_ι_mem_quotAugmentationIdeal 1 X)
        (mk_ι_mem_quotAugmentationIdeal 1 Y))
      (Ideal.mul_mem_mul (mk_ι_mem_quotAugmentationIdeal 1 Y)
        (mk_ι_mem_quotAugmentationIdeal 1 X))
  simp only [map_add, lowerCentralQuotientι_mk, LieRing.of_associative_ring_bracket, hcomm,
    smul_zero, add_zero]

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

/-- The Baker–Campbell–Hausdorff element of class two is the class of `X + Y + ½ ⁅X, Y⁆`. -/
theorem bchElement_two :
    bchElement 2 = LieSubmodule.Quotient.mk (X + Y + (1 / 2 : ℚ) • ⁅X, Y⁆) := by
  rw [← factor_bchElement (show 2 ≤ 3 by norm_num), bchElement_three, LieIdeal.factor_apply]
  refine (Submodule.Quotient.eq _).mpr ?_
  have hmem : ∀ a b c : 𝔣, ⁅a, ⁅b, c⁆⁆ ∈ LieModule.lowerCentralSeries ℚ 𝔣 𝔣 2 := fun a b c => by
    rw [LieModule.lowerCentralSeries_succ, LieModule.lowerCentralSeries_succ,
      LieModule.lowerCentralSeries_zero]
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top a)
      (LieSubmodule.lie_mem_lie (LieSubmodule.mem_top b) (LieSubmodule.mem_top c))
  rw [add_sub_cancel_left]
  exact Submodule.smul_mem _ _ (add_mem (hmem _ _ _) (hmem _ _ _))

end TauCeti.FreeLieAlgebra
