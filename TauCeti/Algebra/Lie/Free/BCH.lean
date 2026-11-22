/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Free.Enveloping
public import TauCeti.Algebra.Lie.UniversalEnveloping.Completion.Primitive

import TauCeti.RingTheory.Nilpotent.BCH

/-!
# Universal Baker–Campbell–Hausdorff elements in the free Lie algebra

Let `F = FreeLieAlgebra ℚ (Fin 2)` be the free Lie algebra over `ℚ` on two generators
`X = of ℚ 0` and `Y = of ℚ 1`, graded by word length over `PositiveDegrees.naturals`. Its
word-length degree ideals coincide with the lower central series
(`naturals_degreeIdeal_eq_lowerCentralSeries`), and the associated degree filtration on `U(F)`
coincides with the powers of the augmentation ideal `J`
(`naturals_degreeFiltration_eq_augmentation_pow`).

In the completed enveloping algebra `completedEnveloping`, the completed exponentials of `X` and
`Y` are completed grouplike, so their product is also completed grouplike. Pulling that product
back along `TauCeti.UniversalEnvelopingAlgebra.completedLieExpEquiv` produces the completed
Baker–Campbell–Hausdorff series `bchCompleted`, whose finite projections define the universal
Baker–Campbell–Hausdorff elements `bchElement c` in the free nilpotent quotients
`F ⧸ lowerCentralSeries ℚ F F c`.

At every class bound `c`, the canonical Lie embedding `lowerCentralQuotientι ℚ F c` maps
`bchElement c` to `IsNilpotent.log (IsNilpotent.exp X * IsNilpotent.exp Y)` in
`U(F) ⧸ J ^ (c + 1)`, uniquely characterizing `bchElement c` and showing compatibility across all
cutoffs `c₁ ≤ c₂`. Through degree three, `bchElement 3` agrees with the classical rational Lie
polynomial
`X + Y + (1 / 2) • ⁅X, Y⁆ + (1 / 12) • (⁅X, ⁅X, Y⁆⁆ + ⁅Y, ⁅Y, X⁆⁆)`.

## Main definitions

* `TauCeti.FreeLieAlgebra.FreeLieTwo`: the free Lie algebra `FreeLieAlgebra ℚ (Fin 2)` on two
  generators.
* `TauCeti.FreeLieAlgebra.freeAugmentation`: the augmentation ideal of `U(FreeLieTwo)`.
* `TauCeti.FreeLieAlgebra.bchCompleted`: the completed Baker–Campbell–Hausdorff series in the
  word-length completion of `FreeLieTwo`.
* `TauCeti.FreeLieAlgebra.bchElement`: the universal Baker–Campbell–Hausdorff element of
  nilpotency class `c` in `FreeLieTwo ⧸ lowerCentralSeries ℚ FreeLieTwo FreeLieTwo c`.

## Main results

* `TauCeti.FreeLieAlgebra.comap_freeAugmentation_pow_ι`: the preimage of
  `freeAugmentation ^ (c + 1)` under `ι ℚ` is `lowerCentralSeries ℚ FreeLieTwo FreeLieTwo c`.
* `TauCeti.FreeLieAlgebra.completedExp_completedLieToU_bchCompleted`: in `completedEnveloping`,
  the completed exponential of `completedLieToU bchCompleted` equals the product of the completed
  exponentials of the two canonical generators.
* `TauCeti.FreeLieAlgebra.quotEquivOfEq_completionProjection_bchCompleted` and
  `TauCeti.FreeLieAlgebra.completionProjection_bchCompleted`: the order-`c` projection of
  `bchCompleted` corresponds to `bchElement c`.
* `TauCeti.FreeLieAlgebra.lowerCentralQuotientι_bchElement`: `lowerCentralQuotientι` sends
  `bchElement c` to `log (exp X * exp Y)` modulo `freeAugmentation ^ (c + 1)`.
* `TauCeti.FreeLieAlgebra.exp_lowerCentralQuotientι_bchElement` and
  `TauCeti.FreeLieAlgebra.exists_bch_exp_mul_exp`: exponentiating `bchElement c` recovers
  `exp X * exp Y` modulo `freeAugmentation ^ (c + 1)`.
* `TauCeti.FreeLieAlgebra.eq_bchElement_iff_exp_lowerCentralQuotientι_eq`: uniqueness of
  `bchElement c`.
* `TauCeti.FreeLieAlgebra.factor_bchElement`: compatibility of `bchElement` under lower-central
  quotient transitions.
* `TauCeti.FreeLieAlgebra.bchElement_zero`, `bchElement_one`, `bchElement_two`, `bchElement_three`:
  explicit universal formulas through degree three.

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
open _root_.TauCeti.UniversalEnvelopingAlgebra (degreeFiltration truncatedLieToU
  completedLieToU completedLieToU_mem_completionIdeal_one toCompletion_ι_mem_completionIdeal_one
  projection_completedLieToU completedLieToU_toCompletion completedLieExpEquiv
  coe_completedLieExpEquiv_apply lowerCentralQuotientι lowerCentralQuotientι_mk
  isNilpotent_lowerCentralQuotientι)

section Grading

variable (R : Type*) [CommRing R] (S : Type*)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- `truncatedLieToU` for `PositiveDegrees.naturals` agrees with `lowerCentralQuotientι` across the
identifications of degree ideals with lower central terms and filtration ideals with augmentation
powers. -/
theorem quotientEquivAlgOfEq_truncatedLieToU (c : ℕ)
    (z : naturals.truncatedLie (homogeneousSubmodule R S) c) :
    Ideal.quotientEquivAlgOfEq R (naturals_degreeFiltration_eq_augmentation_pow R S (c + 1))
        (truncatedLieToU naturals (homogeneousSubmodule R S) c z) =
      lowerCentralQuotientι R (_root_.FreeLieAlgebra R S) c
        (((naturals.degreeIdeal (homogeneousSubmodule R S) c).quotEquivOfEq _
          (naturals_degreeIdeal_eq_lowerCentralSeries R S c)) z) := by
  obtain ⟨x, rfl⟩ := (naturals.degreeIdeal (homogeneousSubmodule R S) c).surjective_mkQ z
  simp [LieIdeal.mkQ_apply, LieIdeal.quotEquivOfEq_mk]

end Grading

section BCH

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The free Lie algebra over `ℚ` on two generators `of ℚ 0` and `of ℚ 1`. -/
abbrev FreeLieTwo : Type := _root_.FreeLieAlgebra ℚ (Fin 2)

/-- The augmentation ideal of `U(FreeLieTwo)`. -/
noncomputable abbrev freeAugmentation : Ideal (_root_.UniversalEnvelopingAlgebra ℚ FreeLieTwo) :=
  (HopfIdeal.augmentation ℚ (_root_.UniversalEnvelopingAlgebra ℚ FreeLieTwo)).toIdeal

local notation "𝓛" => homogeneousSubmodule ℚ (Fin 2)
local notation "𝓕" =>
  degreeFiltration 𝓛 naturals.degree (naturals.eq_bot_of_degree_neg 𝓛)

/-- The preimage of `freeAugmentation ^ (c + 1)` under `ι ℚ` is the `c`-th lower central term of
`FreeLieTwo`. -/
theorem comap_freeAugmentation_pow_ι (c : ℕ) :
    ((freeAugmentation ^ (c + 1)).restrictScalars ℚ).comap
        (ι ℚ :
          FreeLieTwo →ₗ⁅ℚ⁆ _root_.UniversalEnvelopingAlgebra ℚ FreeLieTwo).toLinearMap =
      (lowerCentralSeries ℚ FreeLieTwo FreeLieTwo c).toSubmodule :=
  comap_augmentation_pow_ι_of_algebra_rat ℚ (Fin 2) c

private noncomputable def bchGroupLikeFactor (i : Fin 2) :=
  completedLieExpEquiv naturals 𝓛
    (LieIdeal.toCompletion (naturals.degreeIdeal 𝓛)
      (naturals.degreeIdeal_antitone 𝓛) (of ℚ i))

/-- The completed Baker–Campbell–Hausdorff series in the word-length completion of `FreeLieTwo`,
obtained by pulling back the product of the completed exponentials of the two free generators. -/
noncomputable def bchCompleted : naturals.completedLie 𝓛 :=
  (completedLieExpEquiv naturals 𝓛).symm
    ⟨(bchGroupLikeFactor 0).1 * (bchGroupLikeFactor 1).1,
      (bchGroupLikeFactor 0).2.mul (bchGroupLikeFactor 1).2⟩

/-- In the completed enveloping algebra of `FreeLieTwo`, the completed exponential of `bchCompleted`
is the product of the completed exponentials of the two canonical generators. -/
theorem completedExp_completedLieToU_bchCompleted :
    (𝓕).completedExp
      ⟨completedLieToU naturals 𝓛 bchCompleted,
        completedLieToU_mem_completionIdeal_one naturals 𝓛 bchCompleted⟩ =
    (𝓕).completedExp
      ⟨(𝓕).toCompletion (ι ℚ (of ℚ 0)),
        toCompletion_ι_mem_completionIdeal_one 𝓛 naturals.degree
          (naturals.eq_bot_of_degree_nonpos 𝓛) (of ℚ 0)⟩ *
    (𝓕).completedExp
      ⟨(𝓕).toCompletion (ι ℚ (of ℚ 1)),
        toCompletion_ι_mem_completionIdeal_one 𝓛 naturals.degree
          (naturals.eq_bot_of_degree_nonpos 𝓛) (of ℚ 1)⟩ := by
  have happ := congrArg Subtype.val <|
    (completedLieExpEquiv naturals 𝓛).apply_symm_apply
      ⟨(bchGroupLikeFactor 0).1 * (bchGroupLikeFactor 1).1,
        (bchGroupLikeFactor 0).2.mul (bchGroupLikeFactor 1).2⟩
  simp only [bchCompleted, bchGroupLikeFactor, coe_completedLieExpEquiv_apply,
    completedLieToU_toCompletion] at happ ⊢
  exact happ

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
@[simp]
theorem quotEquivOfEq_completionProjection_bchCompleted (c : ℕ) :
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
      ⟨completedLieToU naturals 𝓛 bchCompleted,
        completedLieToU_mem_completionIdeal_one naturals 𝓛 bchCompleted⟩,
    completedExp_completedLieToU_bchCompleted, map_mul, map_mul,
    bchEnvEquiv_projection_completedExp c, bchEnvEquiv_projection_completedExp c]
  simp [bchEnvEquiv, freeAugmentation]

/-- Under `lowerCentralQuotientι`, `bchElement c` maps to the finite logarithm of `exp X * exp Y`
modulo `freeAugmentation ^ (c + 1)`. -/
theorem lowerCentralQuotientι_bchElement (c : ℕ) :
    lowerCentralQuotientι ℚ FreeLieTwo c (bchElement c) =
      IsNilpotent.log
        (IsNilpotent.exp (Ideal.Quotient.mk (freeAugmentation ^ (c + 1)) (ι ℚ (of ℚ 0))) *
          IsNilpotent.exp
            (Ideal.Quotient.mk (freeAugmentation ^ (c + 1)) (ι ℚ (of ℚ 1)))) := by
  rw [← exp_lowerCentralQuotientι_bchElement c,
    (isNilpotent_lowerCentralQuotientι ℚ FreeLieTwo c (bchElement c)).log_exp]

/-- Existence of a representative in `FreeLieTwo` whose exponential modulo
`freeAugmentation ^ (c + 1)` equals `exp X * exp Y`. -/
theorem exists_bch_exp_mul_exp (c : ℕ) :
    ∃ b : FreeLieTwo,
      IsNilpotent.exp (Ideal.Quotient.mk (freeAugmentation ^ (c + 1)) (ι ℚ b)) =
        IsNilpotent.exp (Ideal.Quotient.mk (freeAugmentation ^ (c + 1)) (ι ℚ (of ℚ 0))) *
          IsNilpotent.exp (Ideal.Quotient.mk (freeAugmentation ^ (c + 1)) (ι ℚ (of ℚ 1))) := by
  obtain ⟨b, hb⟩ :=
    LieIdeal.surjective_mkQ (lowerCentralSeries ℚ FreeLieTwo FreeLieTwo c) (bchElement c)
  exact ⟨b, by
    simpa only [← hb, LieIdeal.mkQ_apply, lowerCentralQuotientι_mk] using
      exp_lowerCentralQuotientι_bchElement c⟩

/-- `bchElement c` is the unique element of `FreeLieTwo ⧸ lowerCentralSeries c` sent by
`lowerCentralQuotientι` to `log (exp X * exp Y)`. -/
theorem eq_bchElement_of_lowerCentralQuotientι_eq {c : ℕ}
    {z : FreeLieTwo ⧸ lowerCentralSeries ℚ FreeLieTwo FreeLieTwo c}
    (hz : lowerCentralQuotientι ℚ FreeLieTwo c z =
      IsNilpotent.log
        (IsNilpotent.exp (Ideal.Quotient.mk (freeAugmentation ^ (c + 1)) (ι ℚ (of ℚ 0))) *
          IsNilpotent.exp (Ideal.Quotient.mk (freeAugmentation ^ (c + 1)) (ι ℚ (of ℚ 1))))) :
    z = bchElement c :=
  lowerCentralQuotientι_injective_of_algebra_rat ℚ (Fin 2) c
    (hz.trans (lowerCentralQuotientι_bchElement c).symm)

/-- Uniqueness of `bchElement c` characterized by its exponential in the truncated enveloping
algebra. -/
theorem eq_bchElement_iff_exp_lowerCentralQuotientι_eq (c : ℕ)
    (z : FreeLieTwo ⧸ lowerCentralSeries ℚ FreeLieTwo FreeLieTwo c) :
    z = bchElement c ↔
      IsNilpotent.exp (lowerCentralQuotientι ℚ FreeLieTwo c z) =
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
  let d := naturals
  obtain ⟨x, hx⟩ := (d.degreeIdeal 𝓛 c₂).surjective_mkQ
    (LieIdeal.completionProjection
      (d.degreeIdeal 𝓛) (d.degreeIdeal_antitone 𝓛) c₂ bchCompleted)
  have hc₁ : LieIdeal.completionProjection (d.degreeIdeal 𝓛) (d.degreeIdeal_antitone 𝓛) c₁
      bchCompleted = LieSubmodule.Quotient.mk x := by
    rw [← LieIdeal.factor_completionProjection
      (d.degreeIdeal 𝓛) (d.degreeIdeal_antitone 𝓛) h, ← hx, LieIdeal.mkQ_apply,
      LieIdeal.factor_apply]
  rw [bchElement, bchElement, ← hx, hc₁]
  simp [LieIdeal.mkQ_apply, LieIdeal.quotEquivOfEq_mk, LieIdeal.factor_apply]

/-! ### Explicit formulas in low nilpotency class -/

private noncomputable def quotAugmentationIdeal (c : ℕ) :
    Ideal (_root_.UniversalEnvelopingAlgebra ℚ FreeLieTwo ⧸ freeAugmentation ^ (c + 1)) :=
  freeAugmentation.map (Ideal.Quotient.mk (freeAugmentation ^ (c + 1)))

private theorem quotAugmentationIdeal_pow_le_map (c : ℕ) :
    ∀ m : ℕ, quotAugmentationIdeal c ^ m ≤
      (freeAugmentation ^ m).map (Ideal.Quotient.mk (freeAugmentation ^ (c + 1)))
  | 0 => fun z _ => by
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact Ideal.mem_map_of_mem _ (by simp [Submodule.pow_zero, Ideal.one_eq_top])
  | m + 1 => by
    rw [Submodule.pow_succ (quotAugmentationIdeal c), Submodule.mul_le]
    intro x hx y hy
    obtain ⟨u, hu, rfl⟩ := Ideal.mem_image_of_mem_map_of_surjective _
      Ideal.Quotient.mk_surjective (quotAugmentationIdeal_pow_le_map c m hx)
    obtain ⟨v, hv, rfl⟩ := Ideal.mem_image_of_mem_map_of_surjective _
      Ideal.Quotient.mk_surjective hy
    rw [← map_mul]
    exact Ideal.mem_map_of_mem _ (Submodule.pow_succ freeAugmentation ▸ Ideal.mul_mem_mul hu hv)

private theorem quotAugmentationIdeal_pow_eq_bot (c : ℕ) :
    quotAugmentationIdeal c ^ (c + 1) = ⊥ :=
  eq_bot_iff.mpr <| (quotAugmentationIdeal_pow_le_map c (c + 1)).trans <|
    Ideal.map_le_iff_le_comap.mpr fun _ hu =>
      Ideal.mem_bot.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr hu)

private theorem mk_ι_mem_quotAugmentationIdeal (c : ℕ) (x : FreeLieTwo) :
    Ideal.Quotient.mk (freeAugmentation ^ (c + 1)) (ι ℚ x) ∈ quotAugmentationIdeal c :=
  Ideal.mem_map_of_mem _
    (HopfIdeal.mem_toIdeal.mpr (UniversalEnvelopingAlgebra.ι_mem_augmentation ℚ FreeLieTwo x))

/-- At class `0`, `bchElement 0` vanishes. -/
@[simp]
theorem bchElement_zero : bchElement 0 = 0 :=
  (Submodule.quotEquivOfEq _ ⊤ (by simp)).injective (Subsingleton.elim _ _)

/-- At class `1`, `bchElement 1` is the sum `X + Y` of the two generators. -/
theorem bchElement_one :
    bchElement 1 = LieSubmodule.Quotient.mk (of ℚ 0) + LieSubmodule.Quotient.mk (of ℚ 1) := by
  symm; apply eq_bchElement_of_lowerCentralQuotientι_eq
  have hI3 : quotAugmentationIdeal 1 ^ 3 = ⊥ := le_bot_iff.mp <|
    quotAugmentationIdeal_pow_eq_bot 1 ▸ Ideal.pow_le_pow_right (by decide : 2 ≤ 3)
  rw [Ideal.log_exp_mul_exp_of_pow_three_eq_bot (quotAugmentationIdeal 1) hI3
    (mk_ι_mem_quotAugmentationIdeal 1 (of ℚ 0)) (mk_ι_mem_quotAugmentationIdeal 1 (of ℚ 1))]
  simp [LieRing.of_associative_ring_bracket]

/-- At class `2`, `bchElement 2` is `X + Y + (1 / 2) • ⁅X, Y⁆`. -/
theorem bchElement_two :
    bchElement 2 =
      LieSubmodule.Quotient.mk (of ℚ 0) + LieSubmodule.Quotient.mk (of ℚ 1) +
        (1 / 2 : ℚ) • ⁅(LieSubmodule.Quotient.mk (of ℚ 0) :
          FreeLieTwo ⧸ lowerCentralSeries ℚ FreeLieTwo FreeLieTwo 2),
          LieSubmodule.Quotient.mk (of ℚ 1)⁆ := by
  symm; apply eq_bchElement_of_lowerCentralQuotientι_eq
  rw [Ideal.log_exp_mul_exp_of_pow_three_eq_bot (quotAugmentationIdeal 2)
    (quotAugmentationIdeal_pow_eq_bot 2)
    (mk_ι_mem_quotAugmentationIdeal 2 (of ℚ 0)) (mk_ι_mem_quotAugmentationIdeal 2 (of ℚ 1))]
  simp only [map_add, map_smul, LieHom.map_lie, lowerCentralQuotientι_mk]

/-- At class `3`, `bchElement 3` is
`X + Y + (1 / 2) • ⁅X, Y⁆ + (1 / 12) • (⁅X, ⁅X, Y⁆⁆ + ⁅Y, ⁅Y, X⁆⁆)`. -/
theorem bchElement_three :
    bchElement 3 =
      LieSubmodule.Quotient.mk (of ℚ 0) + LieSubmodule.Quotient.mk (of ℚ 1) +
        (1 / 2 : ℚ) • ⁅(LieSubmodule.Quotient.mk (of ℚ 0) :
          FreeLieTwo ⧸ lowerCentralSeries ℚ FreeLieTwo FreeLieTwo 3),
          LieSubmodule.Quotient.mk (of ℚ 1)⁆ +
        (1 / 12 : ℚ) •
          (⁅(LieSubmodule.Quotient.mk (of ℚ 0) :
              FreeLieTwo ⧸ lowerCentralSeries ℚ FreeLieTwo FreeLieTwo 3),
            ⁅(LieSubmodule.Quotient.mk (of ℚ 0) :
                FreeLieTwo ⧸ lowerCentralSeries ℚ FreeLieTwo FreeLieTwo 3),
              LieSubmodule.Quotient.mk (of ℚ 1)⁆⁆ +
           ⁅(LieSubmodule.Quotient.mk (of ℚ 1) :
              FreeLieTwo ⧸ lowerCentralSeries ℚ FreeLieTwo FreeLieTwo 3),
            ⁅(LieSubmodule.Quotient.mk (of ℚ 1) :
                FreeLieTwo ⧸ lowerCentralSeries ℚ FreeLieTwo FreeLieTwo 3),
              LieSubmodule.Quotient.mk (of ℚ 0)⁆⁆) := by
  symm; apply eq_bchElement_of_lowerCentralQuotientι_eq
  rw [Ideal.log_exp_mul_exp_of_pow_four_eq_bot (quotAugmentationIdeal 3)
    (quotAugmentationIdeal_pow_eq_bot 3)
    (mk_ι_mem_quotAugmentationIdeal 3 (of ℚ 0)) (mk_ι_mem_quotAugmentationIdeal 3 (of ℚ 1))]
  simp only [map_add, map_smul, LieHom.map_lie, lowerCentralQuotientι_mk]

end BCH

end TauCeti.FreeLieAlgebra
