/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Free.Enveloping
public import TauCeti.Algebra.Lie.UniversalEnveloping.Completion.Primitive

import TauCeti.Algebra.Lie.UniversalEnveloping.Primitive
import TauCeti.RingTheory.Nilpotent.BCH

/-!
# Universal Baker–Campbell–Hausdorff elements in the free Lie algebra

Let `F = FreeLieAlgebra ℚ (Fin 2)` be the free Lie algebra over `ℚ` on two generators `X = of ℚ 0`
and `Y = of ℚ 1`, graded by word length over `PositiveDegrees.naturals`. Its word-length degree
ideals coincide with the lower central series (`naturals_degreeIdeal_eq_lowerCentralSeries`), and
the associated degree filtration on `U(F)` coincides with the powers of the augmentation ideal
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
-/

public section

namespace TauCeti.FreeLieAlgebra

section Grading

variable (R : Type*) [CommRing R] (S : Type*)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Word length is a positive Lie grading of `FreeLieAlgebra R S` over
`PositiveDegrees.naturals`. -/
instance isPositiveGrading_homogeneousSubmodule :
    IsPositiveGrading PositiveDegrees.naturals (homogeneousSubmodule R S) where
  eq_bot n hn := by
    rcases hn with hmem | rfl
    · exact (hmem PositiveDegrees.mem_naturals_monoid).elim
    · exact homogeneousSubmodule_zero R S

/-- For the word-length grading over `PositiveDegrees.naturals`, the degree ideal at cutoff `c` is
the `c`-th term of the lower central series. -/
theorem naturals_degreeIdeal_eq_lowerCentralSeries (c : ℕ) :
    PositiveDegrees.naturals.degreeIdeal (homogeneousSubmodule R S) c =
      LieModule.lowerCentralSeries R (_root_.FreeLieAlgebra R S)
        (_root_.FreeLieAlgebra R S) c := by
  apply LieSubmodule.toSubmodule_injective
  rw [PositiveDegrees.degreeIdeal_toSubmodule, PositiveDegrees.degreeSubmodule_def,
    lowerCentralSeries_toSubmodule_eq_iSup, iSup_subtype]
  refine iSup_congr fun n => iSup_congr_Prop ?_ fun _ => rfl
  simp [Nat.cast_lt]

/-- On `U(FreeLieAlgebra R S)`, the degree filtration for `PositiveDegrees.naturals` coincides with
powers of the augmentation ideal. -/
theorem naturals_degreeFiltration_eq_augmentation_pow (k : ℕ) :
    (UniversalEnvelopingAlgebra.degreeFiltration (homogeneousSubmodule R S)
      PositiveDegrees.naturals.degree
      (PositiveDegrees.naturals.eq_bot_of_degree_neg (homogeneousSubmodule R S))).ideal k =
    (HopfIdeal.augmentation R
      (_root_.UniversalEnvelopingAlgebra R (_root_.FreeLieAlgebra R S))).toIdeal ^ k :=
  UniversalEnvelopingAlgebra.degreeFiltration_eq_augmentation_pow
    (homogeneousSubmodule R S) PositiveDegrees.naturals.degree
    (PositiveDegrees.naturals.eq_bot_of_degree_nonpos (homogeneousSubmodule R S))
    (_root_.FreeLieAlgebra.of R) (fun _ => 1) (lieSpan_range_of_eq_top R S)
    (fun s => by simpa using word_mem_homogeneousSubmodule R (FreeMagma.of s))
    (fun _ => by simp) k

/-- `truncatedLieToU` for `PositiveDegrees.naturals` agrees with `lowerCentralQuotientι` across the
identifications of degree ideals with lower central terms and filtration ideals with augmentation
powers. -/
theorem quotientEquivAlgOfEq_truncatedLieToU (c : ℕ)
    (z : PositiveDegrees.naturals.truncatedLie (homogeneousSubmodule R S) c) :
    Ideal.quotientEquivAlgOfEq R
        (naturals_degreeFiltration_eq_augmentation_pow R S (c + 1))
        (UniversalEnvelopingAlgebra.truncatedLieToU PositiveDegrees.naturals
          (homogeneousSubmodule R S) c z) =
      UniversalEnvelopingAlgebra.lowerCentralQuotientι R (_root_.FreeLieAlgebra R S) c
        (((PositiveDegrees.naturals.degreeIdeal (homogeneousSubmodule R S) c).quotEquivOfEq _
          (naturals_degreeIdeal_eq_lowerCentralSeries R S c)) z) := by
  obtain ⟨x, rfl⟩ :=
    (PositiveDegrees.naturals.degreeIdeal (homogeneousSubmodule R S) c).surjective_mkQ z
  simp [LieIdeal.mkQ_apply, LieIdeal.quotEquivOfEq_mk]

end Grading

section RationalAugmentation

variable (R : Type) [CommRing R] [Algebra ℚ R] (S : Type*)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Over a commutative `ℚ`-algebra `R : Type`, the preimage of the `(c + 1)`-st power of the
augmentation ideal under `ι R` is the `c`-th term of the lower central series. -/
theorem comap_augmentation_pow_ι_of_algebra_rat (c : ℕ) :
    (((HopfIdeal.augmentation R
          (_root_.UniversalEnvelopingAlgebra R (_root_.FreeLieAlgebra R S))).toIdeal ^
        (c + 1)).restrictScalars R).comap
      (_root_.UniversalEnvelopingAlgebra.ι R : _root_.FreeLieAlgebra R S →ₗ⁅R⁆
        _root_.UniversalEnvelopingAlgebra R (_root_.FreeLieAlgebra R S)).toLinearMap =
      (LieModule.lowerCentralSeries R (_root_.FreeLieAlgebra R S)
        (_root_.FreeLieAlgebra R S) c).toSubmodule :=
  comap_augmentation_pow_ι R S
    (UniversalEnvelopingAlgebra.ι_injective_of_algebra_rat R (_root_.FreeLieAlgebra R S)) c

/-- Over a commutative `ℚ`-algebra `R : Type`, the free nilpotent Lie algebra of class at most `c`
embeds into the truncated enveloping algebra modulo the `(c + 1)`-st augmentation power. -/
theorem lowerCentralQuotientι_injective_of_algebra_rat (c : ℕ) :
    Function.Injective
      (UniversalEnvelopingAlgebra.lowerCentralQuotientι R (_root_.FreeLieAlgebra R S) c) :=
  lowerCentralQuotientι_injective R S
    (UniversalEnvelopingAlgebra.ι_injective_of_algebra_rat R (_root_.FreeLieAlgebra R S)) c

end RationalAugmentation

section BCH

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The free Lie algebra over `ℚ` on two generators `of ℚ 0` and `of ℚ 1`. -/
abbrev FreeLieTwo : Type := _root_.FreeLieAlgebra ℚ (Fin 2)

/-- The augmentation ideal of `U(FreeLieTwo)`. -/
noncomputable abbrev freeAugmentation : Ideal (_root_.UniversalEnvelopingAlgebra ℚ FreeLieTwo) :=
  (HopfIdeal.augmentation ℚ (_root_.UniversalEnvelopingAlgebra ℚ FreeLieTwo)).toIdeal

/-- The preimage of `freeAugmentation ^ (c + 1)` under `ι ℚ` is the `c`-th lower central term of
`FreeLieTwo`. -/
theorem comap_freeAugmentation_pow_ι (c : ℕ) :
    ((freeAugmentation ^ (c + 1)).restrictScalars ℚ).comap
        (_root_.UniversalEnvelopingAlgebra.ι ℚ : FreeLieTwo →ₗ⁅ℚ⁆
          _root_.UniversalEnvelopingAlgebra ℚ FreeLieTwo).toLinearMap =
      (LieModule.lowerCentralSeries ℚ FreeLieTwo FreeLieTwo c).toSubmodule :=
  comap_augmentation_pow_ι_of_algebra_rat ℚ (Fin 2) c

private noncomputable def bchGroupLikeFactor (i : Fin 2) :=
  UniversalEnvelopingAlgebra.completedLieExpEquiv PositiveDegrees.naturals
    (homogeneousSubmodule ℚ (Fin 2))
    (LieIdeal.toCompletion
      (PositiveDegrees.naturals.degreeIdeal (homogeneousSubmodule ℚ (Fin 2)))
      (PositiveDegrees.naturals.degreeIdeal_antitone (homogeneousSubmodule ℚ (Fin 2)))
      (_root_.FreeLieAlgebra.of ℚ i))

/-- The completed Baker–Campbell–Hausdorff series in the word-length completion of `FreeLieTwo`,
obtained by pulling back the product of the completed exponentials of the two free generators. -/
noncomputable def bchCompleted :
    PositiveDegrees.naturals.completedLie (homogeneousSubmodule ℚ (Fin 2)) :=
  (UniversalEnvelopingAlgebra.completedLieExpEquiv PositiveDegrees.naturals
      (homogeneousSubmodule ℚ (Fin 2))).symm
    ⟨(bchGroupLikeFactor 0).1 * (bchGroupLikeFactor 1).1,
      (bchGroupLikeFactor 0).2.mul (homogeneousSubmodule ℚ (Fin 2))
        PositiveDegrees.naturals.degree (bchGroupLikeFactor 1).2⟩

/-- The universal Baker–Campbell–Hausdorff element of nilpotency class `c` in
`FreeLieTwo ⧸ lowerCentralSeries ℚ FreeLieTwo FreeLieTwo c`. -/
noncomputable def bchElement (c : ℕ) :
    FreeLieTwo ⧸ LieModule.lowerCentralSeries ℚ FreeLieTwo FreeLieTwo c :=
  ((PositiveDegrees.naturals.degreeIdeal (homogeneousSubmodule ℚ (Fin 2)) c).quotEquivOfEq _
    (naturals_degreeIdeal_eq_lowerCentralSeries ℚ (Fin 2) c))
    (LieIdeal.completionProjection
      (PositiveDegrees.naturals.degreeIdeal (homogeneousSubmodule ℚ (Fin 2)))
      (PositiveDegrees.naturals.degreeIdeal_antitone (homogeneousSubmodule ℚ (Fin 2)))
      c bchCompleted)

private theorem eEnv_projection_completedLieExpEquiv_toCompletion (c : ℕ) (x : FreeLieTwo) :
    Ideal.quotientEquivAlgOfEq ℚ
        (naturals_degreeFiltration_eq_augmentation_pow ℚ (Fin 2) (c + 1))
        ((UniversalEnvelopingAlgebra.degreeFiltration (homogeneousSubmodule ℚ (Fin 2))
            PositiveDegrees.naturals.degree
            (PositiveDegrees.naturals.eq_bot_of_degree_neg
              (homogeneousSubmodule ℚ (Fin 2)))).projection c
          (UniversalEnvelopingAlgebra.completedLieExpEquiv PositiveDegrees.naturals
            (homogeneousSubmodule ℚ (Fin 2))
            (LieIdeal.toCompletion
              (PositiveDegrees.naturals.degreeIdeal (homogeneousSubmodule ℚ (Fin 2)))
              (PositiveDegrees.naturals.degreeIdeal_antitone (homogeneousSubmodule ℚ (Fin 2)))
              x)).1) =
      IsNilpotent.exp
        (Ideal.Quotient.mk (freeAugmentation ^ (c + 1))
          (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) := by
  let d := PositiveDegrees.naturals
  let ℒ := homogeneousSubmodule ℚ (Fin 2)
  let 𝓕 := UniversalEnvelopingAlgebra.degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)
  let eEnv := Ideal.quotientEquivAlgOfEq ℚ
    (naturals_degreeFiltration_eq_augmentation_pow ℚ (Fin 2) (c + 1))
  let xHat : d.completedLie ℒ :=
    LieIdeal.toCompletion (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) x
  have hmem := UniversalEnvelopingAlgebra.completedLieToU_mem_completionIdeal_one d ℒ xHat
  have hnil :
      IsNilpotent (𝓕.projection c (UniversalEnvelopingAlgebra.completedLieToU d ℒ xHat)) :=
    𝓕.isNilpotent_projection hmem c
  calc
    eEnv (𝓕.projection c (UniversalEnvelopingAlgebra.completedLieExpEquiv d ℒ xHat).1)
      = eEnv (𝓕.projection c
          (𝓕.completedExp
            ⟨UniversalEnvelopingAlgebra.completedLieToU d ℒ xHat, hmem⟩)) := by
          rw [UniversalEnvelopingAlgebra.coe_completedLieExpEquiv_apply]; rfl
    _ = eEnv (IsNilpotent.exp
          (𝓕.projection c (UniversalEnvelopingAlgebra.completedLieToU d ℒ xHat))) :=
          congrArg eEnv (𝓕.projection_completedExp ⟨_, hmem⟩ c)
    _ = IsNilpotent.exp
          (eEnv (𝓕.projection c (UniversalEnvelopingAlgebra.completedLieToU d ℒ xHat))) :=
          hnil.map_exp eEnv
    _ = IsNilpotent.exp
          (Ideal.Quotient.mk (freeAugmentation ^ (c + 1))
            (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) := by
          simp [d, ℒ, eEnv, 𝓕, xHat, freeAugmentation]

/-- Under `lowerCentralQuotientι`, `bchElement c` maps to the finite logarithm of `exp X * exp Y`
modulo `freeAugmentation ^ (c + 1)`. -/
theorem lowerCentralQuotientι_bchElement (c : ℕ) :
    UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ FreeLieTwo c (bchElement c) =
      IsNilpotent.log
        (IsNilpotent.exp
            (Ideal.Quotient.mk (freeAugmentation ^ (c + 1))
              (_root_.UniversalEnvelopingAlgebra.ι ℚ (_root_.FreeLieAlgebra.of ℚ 0))) *
          IsNilpotent.exp
            (Ideal.Quotient.mk (freeAugmentation ^ (c + 1))
              (_root_.UniversalEnvelopingAlgebra.ι ℚ (_root_.FreeLieAlgebra.of ℚ 1)))) := by
  let d := PositiveDegrees.naturals
  let ℒ := homogeneousSubmodule ℚ (Fin 2)
  let 𝓕 := UniversalEnvelopingAlgebra.degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)
  let eEnv := Ideal.quotientEquivAlgOfEq ℚ
    (naturals_degreeFiltration_eq_augmentation_pow ℚ (Fin 2) (c + 1))
  have hsub1 : (bchGroupLikeFactor 0).1 * (bchGroupLikeFactor 1).1 - 1 ∈ 𝓕.completionIdeal 1 :=
    ((bchGroupLikeFactor 0).2.mul ℒ d.degree
      (bchGroupLikeFactor 1).2).sub_one_mem_completionIdeal_one ℒ d.degree
      (hpos := d.eq_bot_of_degree_nonpos ℒ)
  have hnil : IsNilpotent
      (𝓕.projection c ((bchGroupLikeFactor 0).1 * (bchGroupLikeFactor 1).1) - 1) := by
    simpa using 𝓕.isNilpotent_projection hsub1 c
  calc
    UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ FreeLieTwo c (bchElement c)
      = eEnv (𝓕.projection c
          (UniversalEnvelopingAlgebra.completedLieToU d ℒ bchCompleted)) := by
          rw [bchElement, ← quotientEquivAlgOfEq_truncatedLieToU ℚ (Fin 2) c,
            ← UniversalEnvelopingAlgebra.projection_completedLieToU d ℒ c bchCompleted]
    _ = eEnv (𝓕.projection c
          (𝓕.completedLog
            ⟨(bchGroupLikeFactor 0).1 * (bchGroupLikeFactor 1).1, hsub1⟩)) := by
          rw [bchCompleted, UniversalEnvelopingAlgebra.completedLieToU_completedLieExpEquiv_symm]
          rfl
    _ = eEnv (IsNilpotent.log
          (𝓕.projection c ((bchGroupLikeFactor 0).1 * (bchGroupLikeFactor 1).1))) :=
          congrArg eEnv (𝓕.projection_completedLog ⟨_, hsub1⟩ c)
    _ = IsNilpotent.log
          (eEnv (𝓕.projection c ((bchGroupLikeFactor 0).1 * (bchGroupLikeFactor 1).1))) :=
          hnil.map_log eEnv
    _ = _ := by
          rw [map_mul, map_mul, bchGroupLikeFactor, bchGroupLikeFactor,
            eEnv_projection_completedLieExpEquiv_toCompletion c (_root_.FreeLieAlgebra.of ℚ 0),
            eEnv_projection_completedLieExpEquiv_toCompletion c (_root_.FreeLieAlgebra.of ℚ 1)]

/-- Exponentiating the image of `bchElement c` in `U(FreeLieTwo) ⧸ freeAugmentation ^ (c + 1)`
recovers `exp X * exp Y`. -/
theorem exp_lowerCentralQuotientι_bchElement (c : ℕ) :
    IsNilpotent.exp
        (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ FreeLieTwo c (bchElement c)) =
      IsNilpotent.exp
          (Ideal.Quotient.mk (freeAugmentation ^ (c + 1))
            (_root_.UniversalEnvelopingAlgebra.ι ℚ (_root_.FreeLieAlgebra.of ℚ 0))) *
        IsNilpotent.exp
          (Ideal.Quotient.mk (freeAugmentation ^ (c + 1))
            (_root_.UniversalEnvelopingAlgebra.ι ℚ (_root_.FreeLieAlgebra.of ℚ 1))) := by
  let d := PositiveDegrees.naturals
  let ℒ := homogeneousSubmodule ℚ (Fin 2)
  let 𝓕 := UniversalEnvelopingAlgebra.degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)
  let eEnv := Ideal.quotientEquivAlgOfEq ℚ
    (naturals_degreeFiltration_eq_augmentation_pow ℚ (Fin 2) (c + 1))
  have hmem := UniversalEnvelopingAlgebra.completedLieToU_mem_completionIdeal_one d ℒ bchCompleted
  have hnil : IsNilpotent
      (𝓕.projection c (UniversalEnvelopingAlgebra.completedLieToU d ℒ bchCompleted)) :=
    𝓕.isNilpotent_projection hmem c
  have happ :
      (UniversalEnvelopingAlgebra.completedLieExpEquiv d ℒ bchCompleted).1 =
        (bchGroupLikeFactor 0).1 * (bchGroupLikeFactor 1).1 :=
    congrArg Subtype.val <|
      (UniversalEnvelopingAlgebra.completedLieExpEquiv d ℒ).apply_symm_apply
        ⟨(bchGroupLikeFactor 0).1 * (bchGroupLikeFactor 1).1,
          (bchGroupLikeFactor 0).2.mul ℒ d.degree (bchGroupLikeFactor 1).2⟩
  calc
    IsNilpotent.exp
        (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ FreeLieTwo c (bchElement c))
      = IsNilpotent.exp
          (eEnv (𝓕.projection c
            (UniversalEnvelopingAlgebra.completedLieToU d ℒ bchCompleted))) := by
          rw [bchElement, ← quotientEquivAlgOfEq_truncatedLieToU ℚ (Fin 2) c,
            ← UniversalEnvelopingAlgebra.projection_completedLieToU d ℒ c bchCompleted]
    _ = eEnv (IsNilpotent.exp
          (𝓕.projection c (UniversalEnvelopingAlgebra.completedLieToU d ℒ bchCompleted))) :=
          (hnil.map_exp eEnv).symm
    _ = eEnv (𝓕.projection c
          (𝓕.completedExp
            ⟨UniversalEnvelopingAlgebra.completedLieToU d ℒ bchCompleted, hmem⟩)) :=
          congrArg eEnv (𝓕.projection_completedExp ⟨_, hmem⟩ c).symm
    _ = eEnv (𝓕.projection c
          (UniversalEnvelopingAlgebra.completedLieExpEquiv d ℒ bchCompleted).1) := by
          rw [UniversalEnvelopingAlgebra.coe_completedLieExpEquiv_apply]; rfl
    _ = eEnv (𝓕.projection c ((bchGroupLikeFactor 0).1 * (bchGroupLikeFactor 1).1)) :=
          congrArg (fun u => eEnv (𝓕.projection c u)) happ
    _ = _ := by
          rw [map_mul, map_mul, bchGroupLikeFactor, bchGroupLikeFactor,
            eEnv_projection_completedLieExpEquiv_toCompletion c (_root_.FreeLieAlgebra.of ℚ 0),
            eEnv_projection_completedLieExpEquiv_toCompletion c (_root_.FreeLieAlgebra.of ℚ 1)]

/-- Existence of a representative in `FreeLieTwo` whose exponential modulo
`freeAugmentation ^ (c + 1)` equals `exp X * exp Y`. -/
theorem exists_bch_exp_mul_exp (c : ℕ) :
    ∃ b : FreeLieTwo,
      IsNilpotent.exp (Ideal.Quotient.mk (freeAugmentation ^ (c + 1))
          (_root_.UniversalEnvelopingAlgebra.ι ℚ b)) =
        IsNilpotent.exp (Ideal.Quotient.mk (freeAugmentation ^ (c + 1))
            (_root_.UniversalEnvelopingAlgebra.ι ℚ (_root_.FreeLieAlgebra.of ℚ 0))) *
          IsNilpotent.exp (Ideal.Quotient.mk (freeAugmentation ^ (c + 1))
            (_root_.UniversalEnvelopingAlgebra.ι ℚ (_root_.FreeLieAlgebra.of ℚ 1))) := by
  obtain ⟨b, hb⟩ :=
    LieIdeal.surjective_mkQ
      (LieModule.lowerCentralSeries ℚ FreeLieTwo FreeLieTwo c) (bchElement c)
  refine ⟨b, ?_⟩
  simpa only [← hb, LieIdeal.mkQ_apply,
    UniversalEnvelopingAlgebra.lowerCentralQuotientι_mk] using
      exp_lowerCentralQuotientι_bchElement c

/-- `bchElement c` is the unique element of `FreeLieTwo ⧸ lowerCentralSeries c` sent by
`lowerCentralQuotientι` to `log (exp X * exp Y)`. -/
theorem eq_bchElement_of_lowerCentralQuotientι_eq {c : ℕ}
    {z : FreeLieTwo ⧸ LieModule.lowerCentralSeries ℚ FreeLieTwo FreeLieTwo c}
    (hz : UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ FreeLieTwo c z =
      IsNilpotent.log
        (IsNilpotent.exp
            (Ideal.Quotient.mk (freeAugmentation ^ (c + 1))
              (_root_.UniversalEnvelopingAlgebra.ι ℚ (_root_.FreeLieAlgebra.of ℚ 0))) *
          IsNilpotent.exp
            (Ideal.Quotient.mk (freeAugmentation ^ (c + 1))
              (_root_.UniversalEnvelopingAlgebra.ι ℚ (_root_.FreeLieAlgebra.of ℚ 1))))) :
    z = bchElement c :=
  lowerCentralQuotientι_injective_of_algebra_rat ℚ (Fin 2) c
    (hz.trans (lowerCentralQuotientι_bchElement c).symm)

/-- Uniqueness of `bchElement c` characterized by its exponential in the truncated enveloping
algebra. -/
theorem eq_bchElement_iff_exp_lowerCentralQuotientι_eq (c : ℕ)
    (z : FreeLieTwo ⧸ LieModule.lowerCentralSeries ℚ FreeLieTwo FreeLieTwo c) :
    z = bchElement c ↔
      IsNilpotent.exp
          (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ FreeLieTwo c z) =
        IsNilpotent.exp
            (Ideal.Quotient.mk (freeAugmentation ^ (c + 1))
              (_root_.UniversalEnvelopingAlgebra.ι ℚ (_root_.FreeLieAlgebra.of ℚ 0))) *
          IsNilpotent.exp
            (Ideal.Quotient.mk (freeAugmentation ^ (c + 1))
              (_root_.UniversalEnvelopingAlgebra.ι ℚ (_root_.FreeLieAlgebra.of ℚ 1))) := by
  refine ⟨fun h => h ▸ exp_lowerCentralQuotientι_bchElement c, fun h => ?_⟩
  apply lowerCentralQuotientι_injective_of_algebra_rat ℚ (Fin 2) c
  have hexp := h.trans (exp_lowerCentralQuotientι_bchElement c).symm
  have hlog := congrArg IsNilpotent.log hexp
  rwa [(UniversalEnvelopingAlgebra.isNilpotent_lowerCentralQuotientι ℚ FreeLieTwo c z).log_exp,
    (UniversalEnvelopingAlgebra.isNilpotent_lowerCentralQuotientι ℚ FreeLieTwo c
      (bchElement c)).log_exp] at hlog

/-- The universal Baker–Campbell–Hausdorff elements are compatible across nilpotency bounds. -/
@[simp]
theorem factor_bchElement {c₁ c₂ : ℕ} (h : c₁ ≤ c₂) :
    LieIdeal.factor (LieModule.antitone_lowerCentralSeries ℚ FreeLieTwo FreeLieTwo h)
        (bchElement c₂) =
      bchElement c₁ := by
  let d := PositiveDegrees.naturals
  let ℒ := homogeneousSubmodule ℚ (Fin 2)
  obtain ⟨x, hx⟩ := (d.degreeIdeal ℒ c₂).surjective_mkQ
    (LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ)
      c₂ bchCompleted)
  have hc₁ :
      LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ)
          c₁ bchCompleted =
        LieSubmodule.Quotient.mk x := by
    rw [← LieIdeal.factor_completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) h,
      ← hx, LieIdeal.mkQ_apply, LieIdeal.factor_apply]
  rw [bchElement, bchElement, ← hx, hc₁]
  simp [LieIdeal.mkQ_apply, LieIdeal.quotEquivOfEq_mk, LieIdeal.factor_apply]

/-! ### Explicit formulas in low nilpotency class -/

private noncomputable def quotAugmentationIdeal (c : ℕ) :
    Ideal (_root_.UniversalEnvelopingAlgebra ℚ FreeLieTwo ⧸ freeAugmentation ^ (c + 1)) :=
  RingHom.ker (Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (Nat.succ_pos c) :
      freeAugmentation ^ (c + 1) ≤ freeAugmentation ^ 1))

private theorem mk_mem_quotAugmentationIdeal_iff (c : ℕ)
    (u : _root_.UniversalEnvelopingAlgebra ℚ FreeLieTwo) :
    Ideal.Quotient.mk (freeAugmentation ^ (c + 1)) u ∈ quotAugmentationIdeal c ↔
      u ∈ freeAugmentation := by
  rw [quotAugmentationIdeal, RingHom.mem_ker, Ideal.Quotient.factor_mk,
    Ideal.Quotient.eq_zero_iff_mem, Submodule.pow_one]

private theorem exists_rep_of_mem_quotAugmentationIdeal_pow (c : ℕ) :
    ∀ {m : ℕ}
      {z : _root_.UniversalEnvelopingAlgebra ℚ FreeLieTwo ⧸ freeAugmentation ^ (c + 1)},
      z ∈ quotAugmentationIdeal c ^ m →
        ∃ u ∈ freeAugmentation ^ m, Ideal.Quotient.mk (freeAugmentation ^ (c + 1)) u = z
  | 0, z, _ => by
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨u, by simp [Submodule.pow_zero, Ideal.one_eq_top], rfl⟩
  | m + 1, z, hz => by
    rw [Submodule.pow_succ (quotAugmentationIdeal c)] at hz
    refine Submodule.mul_induction_on hz (fun x hx y hy => ?_)
      fun _ _ ⟨u₁, hu₁, h₁⟩ ⟨u₂, hu₂, h₂⟩ =>
        ⟨u₁ + u₂, add_mem hu₁ hu₂, by rw [map_add, h₁, h₂]⟩
    obtain ⟨u, hu, rfl⟩ := exists_rep_of_mem_quotAugmentationIdeal_pow c hx
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hv : v ∈ freeAugmentation := (mk_mem_quotAugmentationIdeal_iff c v).mp hy
    exact ⟨u * v, by rw [Submodule.pow_succ]; exact Ideal.mul_mem_mul hu hv, map_mul _ u v⟩

private theorem quotAugmentationIdeal_pow_eq_bot (c : ℕ) :
    quotAugmentationIdeal c ^ (c + 1) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨u, hu, rfl⟩ := exists_rep_of_mem_quotAugmentationIdeal_pow c hz
  simpa only [Submodule.mem_bot] using Ideal.Quotient.eq_zero_iff_mem.mpr hu

private theorem mk_ι_mem_quotAugmentationIdeal (c : ℕ) (x : FreeLieTwo) :
    Ideal.Quotient.mk (freeAugmentation ^ (c + 1))
        (_root_.UniversalEnvelopingAlgebra.ι ℚ x) ∈ quotAugmentationIdeal c :=
  (mk_mem_quotAugmentationIdeal_iff c _).mpr
    (HopfIdeal.mem_toIdeal.mpr
      (UniversalEnvelopingAlgebra.ι_mem_augmentation ℚ FreeLieTwo x))

/-- At class `0`, `bchElement 0` vanishes. -/
@[simp]
theorem bchElement_zero : bchElement 0 = 0 := by
  have htop : (LieModule.lowerCentralSeries ℚ FreeLieTwo FreeLieTwo 0).toSubmodule = ⊤ := by
    simp
  apply (Submodule.quotEquivOfEq _ ⊤ htop).injective
  exact Subsingleton.elim _ _

/-- At class `1`, `bchElement 1` is the sum `X + Y` of the two generators. -/
theorem bchElement_one :
    bchElement 1 =
      LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ 0) +
        LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ 1) := by
  symm
  apply eq_bchElement_of_lowerCentralQuotientι_eq
  have hI2 := quotAugmentationIdeal_pow_eq_bot 1
  have hI3 : quotAugmentationIdeal 1 ^ 3 = ⊥ :=
    le_bot_iff.mp (hI2 ▸ Ideal.pow_le_pow_right (by decide : 2 ≤ 3))
  have hx := mk_ι_mem_quotAugmentationIdeal 1 (_root_.FreeLieAlgebra.of ℚ 0)
  have hy := mk_ι_mem_quotAugmentationIdeal 1 (_root_.FreeLieAlgebra.of ℚ 1)
  rw [Ideal.log_exp_mul_exp_of_pow_three_eq_bot (quotAugmentationIdeal 1) hI3 hx hy]
  simp [LieRing.of_associative_ring_bracket]

/-- At class `2`, `bchElement 2` is `X + Y + (1 / 2) • ⁅X, Y⁆`. -/
theorem bchElement_two :
    bchElement 2 =
      LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ 0) +
        LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ 1) +
        (1 / 2 : ℚ) •
          ⁅(LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ 0) :
              FreeLieTwo ⧸ LieModule.lowerCentralSeries ℚ FreeLieTwo FreeLieTwo 2),
            LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ 1)⁆ := by
  symm
  apply eq_bchElement_of_lowerCentralQuotientι_eq
  have hx := mk_ι_mem_quotAugmentationIdeal 2 (_root_.FreeLieAlgebra.of ℚ 0)
  have hy := mk_ι_mem_quotAugmentationIdeal 2 (_root_.FreeLieAlgebra.of ℚ 1)
  rw [Ideal.log_exp_mul_exp_of_pow_three_eq_bot (quotAugmentationIdeal 2)
    (quotAugmentationIdeal_pow_eq_bot 2) hx hy]
  simp only [map_add, map_smul, LieHom.map_lie,
    UniversalEnvelopingAlgebra.lowerCentralQuotientι_mk]

/-- At class `3`, `bchElement 3` is
`X + Y + (1 / 2) • ⁅X, Y⁆ + (1 / 12) • (⁅X, ⁅X, Y⁆⁆ + ⁅Y, ⁅Y, X⁆⁆)`. -/
theorem bchElement_three :
    bchElement 3 =
      LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ 0) +
        LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ 1) +
        (1 / 2 : ℚ) •
          ⁅(LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ 0) :
              FreeLieTwo ⧸ LieModule.lowerCentralSeries ℚ FreeLieTwo FreeLieTwo 3),
            LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ 1)⁆ +
        (1 / 12 : ℚ) •
          (⁅(LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ 0) :
                FreeLieTwo ⧸ LieModule.lowerCentralSeries ℚ FreeLieTwo FreeLieTwo 3),
              ⁅(LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ 0) :
                  FreeLieTwo ⧸ LieModule.lowerCentralSeries ℚ FreeLieTwo FreeLieTwo 3),
                LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ 1)⁆⁆ +
            ⁅(LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ 1) :
                FreeLieTwo ⧸ LieModule.lowerCentralSeries ℚ FreeLieTwo FreeLieTwo 3),
              ⁅(LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ 1) :
                  FreeLieTwo ⧸ LieModule.lowerCentralSeries ℚ FreeLieTwo FreeLieTwo 3),
                LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ 0)⁆⁆) := by
  symm
  apply eq_bchElement_of_lowerCentralQuotientι_eq
  have hx := mk_ι_mem_quotAugmentationIdeal 3 (_root_.FreeLieAlgebra.of ℚ 0)
  have hy := mk_ι_mem_quotAugmentationIdeal 3 (_root_.FreeLieAlgebra.of ℚ 1)
  rw [Ideal.log_exp_mul_exp_of_pow_four_eq_bot (quotAugmentationIdeal 3)
    (quotAugmentationIdeal_pow_eq_bot 3) hx hy]
  simp only [map_add, map_smul, LieHom.map_lie,
    UniversalEnvelopingAlgebra.lowerCentralQuotientι_mk]

end BCH

end TauCeti.FreeLieAlgebra
