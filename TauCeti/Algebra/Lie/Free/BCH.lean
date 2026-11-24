/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Free.Enveloping
public import TauCeti.Algebra.Lie.UniversalEnveloping.Completion.Exp

import TauCeti.RingTheory.Ideal.Quotient.Operations
import TauCeti.RingTheory.Nilpotent.BCH

/-!
# Universal Baker–Campbell–Hausdorff elements in the free Lie algebra

Let `F = FreeLieAlgebra ℚ (Fin 2)` be the free Lie algebra over `ℚ` on `X = of ℚ 0` and
`Y = of ℚ 1`, graded by word length over `PositiveDegrees.naturals`. In `completedEnveloping`,
pulling back the product of the completed exponentials of `X` and `Y` along `completedLieExpEquiv`
produces the completed BCH series `bchCompleted`, whose finite projections define the universal
BCH elements `bchElement c : F ⧸ lowerCentralSeries ℚ F F c`.

At every class `c`, `lowerCentralQuotientι ℚ F c` maps `bchElement c` to
`IsNilpotent.log (IsNilpotent.exp X * IsNilpotent.exp Y)` in `U(F) ⧸ J ^ (c + 1)`, uniquely
characterizing `bchElement c` and giving compatibility under `LieIdeal.factor`. Through degree
three, `bchElement 3` agrees with
`X + Y + (1 / 2) • ⁅X, Y⁆ + (1 / 12) • (⁅X, ⁅X, Y⁆⁆ + ⁅Y, ⁅Y, X⁆⁆)`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter II, §6.
* J.-P. Serre, *Lie Algebras and Lie Groups*, Part I, Chapter IV.
-/

public section

namespace TauCeti.FreeLieAlgebra

open _root_.UniversalEnvelopingAlgebra (ι)
open _root_.FreeLieAlgebra (of)
open LieModule (lowerCentralSeries)
open PositiveDegrees (naturals)
open _root_.TauCeti.UniversalEnvelopingAlgebra (degreeFiltration
  completedLieToU completedLieToU_mem_completionIdeal_one toCompletion_ι_mem_completionIdeal_one
  projection_completedLieToU completedLieToU_toCompletion completedLieExpEquiv
  coe_completedLieExpEquiv_apply lowerCentralQuotientι lowerCentralQuotientι_mk
  isNilpotent_lowerCentralQuotientι)

section BCH

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The free Lie algebra over `ℚ` on two generators `of ℚ 0` and `of ℚ 1`. -/
abbrev FreeLieTwo : Type := _root_.FreeLieAlgebra ℚ (Fin 2)

/-- The augmentation ideal of `U(FreeLieTwo)`. -/
noncomputable abbrev freeAugmentation : Ideal (_root_.UniversalEnvelopingAlgebra ℚ FreeLieTwo) :=
  (HopfIdeal.augmentation ℚ (_root_.UniversalEnvelopingAlgebra ℚ FreeLieTwo)).toIdeal

local notation "𝓛" => homogeneousSubmodule ℚ (Fin 2)
local notation "𝓕" => degreeFiltration 𝓛 naturals.degree (naturals.eq_bot_of_degree_neg 𝓛)

private noncomputable def bchGroupLikeFactor (i : Fin 2) :=
  completedLieExpEquiv naturals 𝓛
    (LieIdeal.toCompletion (naturals.degreeIdeal 𝓛) (naturals.degreeIdeal_antitone 𝓛) (of ℚ i))

/-- The completed Baker–Campbell–Hausdorff series in the word-length completion of `FreeLieTwo`,
obtained by pulling back the product of the completed exponentials of the two free generators. -/
noncomputable def bchCompleted : naturals.completedLie 𝓛 :=
  (completedLieExpEquiv naturals 𝓛).symm ⟨(bchGroupLikeFactor 0).val * (bchGroupLikeFactor 1).val,
    (bchGroupLikeFactor 0).property.mul (bchGroupLikeFactor 1).property⟩

/-- In the completed enveloping algebra of `FreeLieTwo`, the completed exponential of `bchCompleted`
is the product of the completed exponentials of the two canonical generators. -/
theorem completedExp_completedLieToU_bchCompleted :
    (𝓕).completedExp ⟨completedLieToU naturals 𝓛 bchCompleted,
        completedLieToU_mem_completionIdeal_one naturals 𝓛 bchCompleted⟩ =
      (𝓕).completedExp ⟨(𝓕).toCompletion (ι ℚ (of ℚ 0)), toCompletion_ι_mem_completionIdeal_one
        𝓛 naturals.degree (naturals.eq_bot_of_degree_nonpos 𝓛) (of ℚ 0)⟩ *
      (𝓕).completedExp ⟨(𝓕).toCompletion (ι ℚ (of ℚ 1)), toCompletion_ι_mem_completionIdeal_one
        𝓛 naturals.degree (naturals.eq_bot_of_degree_nonpos 𝓛) (of ℚ 1)⟩ := by
  have happ := congrArg Subtype.val <| (completedLieExpEquiv naturals 𝓛).apply_symm_apply
    ⟨_, (bchGroupLikeFactor 0).property.mul (bchGroupLikeFactor 1).property⟩
  simp only [bchCompleted, bchGroupLikeFactor, coe_completedLieExpEquiv_apply,
    completedLieToU_toCompletion] at happ ⊢; exact happ

/-- The universal Baker–Campbell–Hausdorff element of nilpotency class `c` in
`FreeLieTwo ⧸ lowerCentralSeries ℚ FreeLieTwo FreeLieTwo c`. -/
noncomputable def bchElement (c : ℕ) :
    FreeLieTwo ⧸ lowerCentralSeries ℚ FreeLieTwo FreeLieTwo c :=
  ((naturals.degreeIdeal 𝓛 c).quotEquivOfEq _
      (naturals_degreeIdeal_eq_lowerCentralSeries ℚ (Fin 2) c))
    (LieIdeal.completionProjection (naturals.degreeIdeal 𝓛)
      (naturals.degreeIdeal_antitone 𝓛) c bchCompleted)

/-- Identifying the degree ideal with the lower central series sends the order-`c` projection of
`bchCompleted` to `bchElement c`. -/
@[simp] theorem quotEquivOfEq_completionProjection_bchCompleted (c : ℕ) :
    ((naturals.degreeIdeal 𝓛 c).quotEquivOfEq _
        (naturals_degreeIdeal_eq_lowerCentralSeries ℚ (Fin 2) c))
      (LieIdeal.completionProjection (naturals.degreeIdeal 𝓛)
        (naturals.degreeIdeal_antitone 𝓛) c bchCompleted) = bchElement c := (rfl)

/-- The order-`c` projection of `bchCompleted` is `bchElement c` transported back along the
identification of degree ideals with lower central terms. -/
theorem completionProjection_bchCompleted (c : ℕ) :
    LieIdeal.completionProjection (naturals.degreeIdeal 𝓛)
        (naturals.degreeIdeal_antitone 𝓛) c bchCompleted =
      ((naturals.degreeIdeal 𝓛 c).quotEquivOfEq _
          (naturals_degreeIdeal_eq_lowerCentralSeries ℚ (Fin 2) c)).symm (bchElement c) := by
  rw [← quotEquivOfEq_completionProjection_bchCompleted c, LieEquiv.symm_apply_apply]

private noncomputable abbrev bchEnvEquiv (c : ℕ) :=
  Ideal.quotientEquivAlgOfEq ℚ (naturals_degreeFiltration_eq_augmentation_pow ℚ (Fin 2) (c + 1))

private theorem bchEnvEquiv_projection_completedExp (c : ℕ) (x : (𝓕).completionIdeal 1) :
    bchEnvEquiv c ((𝓕).projection c ((𝓕).completedExp x)) =
      IsNilpotent.exp (bchEnvEquiv c ((𝓕).projection c x)) := by
  rw [(𝓕).projection_completedExp x c,
    ((𝓕).isNilpotent_projection x.property c).map_exp (bchEnvEquiv c)]

/-- Exponentiating the image of `bchElement c` in `U(FreeLieTwo) ⧸ freeAugmentation ^ (c + 1)`
recovers `exp X * exp Y`. -/
theorem exp_lowerCentralQuotientι_bchElement (c : ℕ) :
    IsNilpotent.exp (lowerCentralQuotientι ℚ FreeLieTwo c (bchElement c)) =
      IsNilpotent.exp (Ideal.Quotient.mk (freeAugmentation ^ (c + 1)) (ι ℚ (of ℚ 0))) *
        IsNilpotent.exp (Ideal.Quotient.mk (freeAugmentation ^ (c + 1)) (ι ℚ (of ℚ 1))) := by
  rw [← quotEquivOfEq_completionProjection_bchCompleted c,
    ← quotientEquivAlgOfEq_truncatedLieToU ℚ (Fin 2) c,
    ← projection_completedLieToU naturals 𝓛 c bchCompleted,
    ← bchEnvEquiv_projection_completedExp c
      ⟨_, completedLieToU_mem_completionIdeal_one naturals 𝓛 bchCompleted⟩,
    completedExp_completedLieToU_bchCompleted, map_mul, map_mul,
    bchEnvEquiv_projection_completedExp c, bchEnvEquiv_projection_completedExp c]
  simp [bchEnvEquiv, freeAugmentation]

/-- Under `lowerCentralQuotientι`, `bchElement c` maps to the finite logarithm of `exp X * exp Y`
modulo `freeAugmentation ^ (c + 1)`. -/
theorem lowerCentralQuotientι_bchElement (c : ℕ) :
    lowerCentralQuotientι ℚ FreeLieTwo c (bchElement c) = IsNilpotent.log
      (IsNilpotent.exp (Ideal.Quotient.mk (freeAugmentation ^ (c + 1)) (ι ℚ (of ℚ 0))) *
        IsNilpotent.exp (Ideal.Quotient.mk (freeAugmentation ^ (c + 1)) (ι ℚ (of ℚ 1)))) := by
  rw [← exp_lowerCentralQuotientι_bchElement c,
    (isNilpotent_lowerCentralQuotientι ℚ FreeLieTwo c (bchElement c)).log_exp]

/-- Existence of a representative in `FreeLieTwo` whose exponential modulo
`freeAugmentation ^ (c + 1)` equals `exp X * exp Y`. -/
theorem exists_bch_exp_mul_exp (c : ℕ) :
    ∃ b : FreeLieTwo, IsNilpotent.exp (Ideal.Quotient.mk (freeAugmentation ^ (c + 1)) (ι ℚ b)) =
      IsNilpotent.exp (Ideal.Quotient.mk (freeAugmentation ^ (c + 1)) (ι ℚ (of ℚ 0))) *
        IsNilpotent.exp (Ideal.Quotient.mk (freeAugmentation ^ (c + 1)) (ι ℚ (of ℚ 1))) := by
  obtain ⟨b, hb⟩ := LieIdeal.surjective_mkQ
    (lowerCentralSeries ℚ FreeLieTwo FreeLieTwo c) (bchElement c)
  exact ⟨b, by simpa only [← hb, LieIdeal.mkQ_apply, lowerCentralQuotientι_mk] using
    exp_lowerCentralQuotientι_bchElement c⟩

/-- Any element of the class-`c` quotient whose image under `lowerCentralQuotientι` is
`log (exp X * exp Y)` equals `bchElement c`. -/
theorem eq_bchElement_of_lowerCentralQuotientι_eq {c : ℕ}
    {z : FreeLieTwo ⧸ lowerCentralSeries ℚ FreeLieTwo FreeLieTwo c}
    (hz : lowerCentralQuotientι ℚ FreeLieTwo c z = IsNilpotent.log
      (IsNilpotent.exp (Ideal.Quotient.mk (freeAugmentation ^ (c + 1)) (ι ℚ (of ℚ 0))) *
        IsNilpotent.exp (Ideal.Quotient.mk (freeAugmentation ^ (c + 1)) (ι ℚ (of ℚ 1))))) :
    z = bchElement c :=
  lowerCentralQuotientι_injective_of_algebra_rat ℚ (Fin 2) c
    (hz.trans (lowerCentralQuotientι_bchElement c).symm)

/-- Uniqueness of `bchElement c` characterized by its exponential in the truncated enveloping
algebra. -/
theorem eq_bchElement_iff_exp_lowerCentralQuotientι_eq (c : ℕ)
    (z : FreeLieTwo ⧸ lowerCentralSeries ℚ FreeLieTwo FreeLieTwo c) :
    z = bchElement c ↔ IsNilpotent.exp (lowerCentralQuotientι ℚ FreeLieTwo c z) =
      IsNilpotent.exp (Ideal.Quotient.mk (freeAugmentation ^ (c + 1)) (ι ℚ (of ℚ 0))) *
        IsNilpotent.exp (Ideal.Quotient.mk (freeAugmentation ^ (c + 1)) (ι ℚ (of ℚ 1))) := by
  refine ⟨fun h => h ▸ exp_lowerCentralQuotientι_bchElement c, fun h => ?_⟩
  apply lowerCentralQuotientι_injective_of_algebra_rat ℚ (Fin 2) c
  have hlog := congrArg IsNilpotent.log (h.trans (exp_lowerCentralQuotientι_bchElement c).symm)
  rwa [(isNilpotent_lowerCentralQuotientι ℚ FreeLieTwo c z).log_exp,
    (isNilpotent_lowerCentralQuotientι ℚ FreeLieTwo c (bchElement c)).log_exp] at hlog

/-- The universal Baker–Campbell–Hausdorff elements are compatible across nilpotency bounds. -/
@[simp]
theorem factor_bchElement {c₁ c₂ : ℕ} (h : c₁ ≤ c₂) :
    LieIdeal.factor (LieModule.antitone_lowerCentralSeries ℚ FreeLieTwo FreeLieTwo h)
        (bchElement c₂) = bchElement c₁ := by
  obtain ⟨x, hx⟩ := (naturals.degreeIdeal 𝓛 c₂).surjective_mkQ (LieIdeal.completionProjection
    (naturals.degreeIdeal 𝓛) (naturals.degreeIdeal_antitone 𝓛) c₂ bchCompleted)
  have hc₁ : LieIdeal.completionProjection (naturals.degreeIdeal 𝓛)
      (naturals.degreeIdeal_antitone 𝓛) c₁ bchCompleted = LieSubmodule.Quotient.mk x := by
    rw [← LieIdeal.factor_completionProjection (naturals.degreeIdeal 𝓛)
      (naturals.degreeIdeal_antitone 𝓛) h, ← hx, LieIdeal.mkQ_apply, LieIdeal.factor_apply]
  rw [bchElement, bchElement, ← hx, hc₁]
  simp [LieIdeal.mkQ_apply, LieIdeal.quotEquivOfEq_mk, LieIdeal.factor_apply]

/-! ### Explicit formulas in low nilpotency class -/

private noncomputable def quotAugmentationIdeal (c : ℕ) :
    Ideal (_root_.UniversalEnvelopingAlgebra ℚ FreeLieTwo ⧸ freeAugmentation ^ (c + 1)) :=
  freeAugmentation.map (Ideal.Quotient.mk (freeAugmentation ^ (c + 1)))

private theorem mk_ι_mem_quotAugmentationIdeal (c : ℕ) (x : FreeLieTwo) :
    Ideal.Quotient.mk (freeAugmentation ^ (c + 1)) (ι ℚ x) ∈ quotAugmentationIdeal c :=
  Ideal.mem_map_of_mem _
    (HopfIdeal.mem_toIdeal.mpr (UniversalEnvelopingAlgebra.ι_mem_augmentation ℚ FreeLieTwo x))

/-- At class `0`, `bchElement 0` vanishes. -/
@[simp] theorem bchElement_zero : bchElement 0 = 0 := by
  obtain ⟨x, hx⟩ := LieIdeal.surjective_mkQ _ (bchElement 0)
  rw [← hx, LieIdeal.mkQ_eq_zero]
  simp

/-- At class `1`, `bchElement 1` is the sum `X + Y` of the two generators. -/
theorem bchElement_one :
    bchElement 1 = LieSubmodule.Quotient.mk (of ℚ 0) + LieSubmodule.Quotient.mk (of ℚ 1) := by
  symm; apply eq_bchElement_of_lowerCentralQuotientι_eq
  rw [Ideal.log_exp_mul_exp_of_pow_three_eq_bot (quotAugmentationIdeal 1)
    (Ideal.map_mk_pow_eq_bot_of_le (Ideal.pow_le_pow_right (by decide : 1 + 1 ≤ 3)))
    (mk_ι_mem_quotAugmentationIdeal 1 (of ℚ 0)) (mk_ι_mem_quotAugmentationIdeal 1 (of ℚ 1))]
  simp [LieRing.of_associative_ring_bracket]

local notation "q0(" c ")" =>
  (LieSubmodule.Quotient.mk (of ℚ 0) : FreeLieTwo ⧸ lowerCentralSeries ℚ FreeLieTwo FreeLieTwo c)
local notation "q1(" c ")" =>
  (LieSubmodule.Quotient.mk (of ℚ 1) : FreeLieTwo ⧸ lowerCentralSeries ℚ FreeLieTwo FreeLieTwo c)

/-- At class `2`, `bchElement 2` is `X + Y + (1 / 2) • ⁅X, Y⁆`. -/
theorem bchElement_two : bchElement 2 = q0(2) + q1(2) + (1 / 2 : ℚ) • ⁅q0(2), q1(2)⁆ := by
  symm; apply eq_bchElement_of_lowerCentralQuotientι_eq
  rw [Ideal.log_exp_mul_exp_of_pow_three_eq_bot (quotAugmentationIdeal 2)
    (Ideal.map_mk_pow_self freeAugmentation 3)
    (mk_ι_mem_quotAugmentationIdeal 2 (of ℚ 0)) (mk_ι_mem_quotAugmentationIdeal 2 (of ℚ 1))]
  simp only [map_add, map_smul, LieHom.map_lie, lowerCentralQuotientι_mk]

/-- At class `3`, `bchElement 3` is
`X + Y + (1 / 2) • ⁅X, Y⁆ + (1 / 12) • (⁅X, ⁅X, Y⁆⁆ + ⁅Y, ⁅Y, X⁆⁆)`. -/
theorem bchElement_three :
    bchElement 3 = q0(3) + q1(3) + (1 / 2 : ℚ) • ⁅q0(3), q1(3)⁆ +
      (1 / 12 : ℚ) • (⁅q0(3), ⁅q0(3), q1(3)⁆⁆ + ⁅q1(3), ⁅q1(3), q0(3)⁆⁆) := by
  symm; apply eq_bchElement_of_lowerCentralQuotientι_eq
  rw [Ideal.log_exp_mul_exp_of_pow_four_eq_bot (quotAugmentationIdeal 3)
    (Ideal.map_mk_pow_self freeAugmentation 4)
    (mk_ι_mem_quotAugmentationIdeal 3 (of ℚ 0)) (mk_ι_mem_quotAugmentationIdeal 3 (of ℚ 1))]
  simp only [map_add, map_smul, LieHom.map_lie, lowerCentralQuotientι_mk]

end BCH

end TauCeti.FreeLieAlgebra
