/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Free.Enveloping
public import TauCeti.Algebra.Lie.UniversalEnveloping.Completion

import TauCeti.RingTheory.Nilpotent.BCH

/-!
# The universal Baker–Campbell–Hausdorff element

Word length equips a free Lie algebra `F` over a commutative ring `R` with positive degree data
`wordLengthDegrees : PositiveDegrees ℕ`, whose degree ideal at cutoff `c` is the `c`-th term of the
lower central series (`degreeIdeal_eq_lowerCentralSeries`) and whose induced enveloping-algebra
filtration is the filtration by powers of the augmentation ideal
(`positiveDegreeFiltration_ideal_eq_augmentation_pow`).

Over `ℚ`, the classification of completed primitive and group-like elements in the completed
enveloping algebra (`UniversalEnvelopingAlgebra.completedLieEquivCompletedGroupLike`) identifies the
word-length completion of `F₂ = FreeLieAlgebra ℚ (Fin 2)` with the completed group-like elements of
its completed enveloping algebra. Since the product of the completed exponentials of the two
generators `X = of 0` and `Y = of 1` is completed group-like, its inverse image defines the
universal Baker–Campbell–Hausdorff element `completedBCH` in the completed free Lie algebra and its
finite-class truncations `bchElement c : F₂ ⧸ lowerCentralSeries ℚ F₂ F₂ c`.

## Main definitions

* `TauCeti.FreeLieAlgebra.wordLengthDegrees`: the natural numbers with identity degree as positive
  degree data for word-length gradings.
* `TauCeti.FreeLieAlgebra.completedBCH`: the universal Baker–Campbell–Hausdorff element in the
  word-length completion of `FreeLieAlgebra ℚ (Fin 2)`.
* `TauCeti.FreeLieAlgebra.bchElement`: the universal Baker–Campbell–Hausdorff element of nilpotency
  class at most `c` in `FreeLieAlgebra ℚ (Fin 2) ⧸ lowerCentralSeries c`.

## Main results

* `TauCeti.FreeLieAlgebra.degreeIdeal_eq_lowerCentralSeries`: the word-length degree ideal at
  cutoff `c` coincides with the `c`-th term of the lower central series.
* `TauCeti.FreeLieAlgebra.comap_augmentation_pow_ι_of_algebra_rat` and
  `TauCeti.FreeLieAlgebra.lowerCentralQuotientι_injective_of_algebra_rat`: over a commutative
  `ℚ`-algebra, `ι⁻¹(J ^ (c + 1)) = lowerCentralSeries c` and `lowerCentralQuotientι` is injective.
* `TauCeti.FreeLieAlgebra.exp_lowerCentralQuotientι_bchElement` and
  `TauCeti.FreeLieAlgebra.lowerCentralQuotientι_bchElement`: in `U(F₂) ⧸ J ^ (c + 1)`,
  `exp (ι_c (bchElement c)) = exp (ι_c X) * exp (ι_c Y)` and
  `ι_c (bchElement c) = log (exp (ι_c X) * exp (ι_c Y))`.
* `TauCeti.FreeLieAlgebra.exists_bch_exp_mul_exp`: existence of a lift `b : F₂` satisfying
  `exp (ι b) = exp (ι X) * exp (ι Y)` in `U(F₂) ⧸ J ^ (c + 1)`.
* `TauCeti.FreeLieAlgebra.eq_bchElement_of_exp_lowerCentralQuotientι_eq`: uniqueness of
  `bchElement c`.
* `TauCeti.FreeLieAlgebra.factor_bchElement`: compatibility of `bchElement c` across nilpotency
  classes.
* `TauCeti.FreeLieAlgebra.bchElement_zero`, `bchElement_one`, `bchElement_two`, and
  `bchElement_three`: explicit formulas through nilpotency class three.
-/

public section

namespace TauCeti.FreeLieAlgebra

section WordLength

/-- The natural numbers with identity degree, used as positive degree data for word-length
gradings on free Lie algebras. -/
def wordLengthDegrees : PositiveDegrees ℕ where
  monoid := ⊤
  degree := Nat.castAddMonoidHom ℤ
  degree_pos _ hne := Int.natCast_pos.mpr (Nat.pos_of_ne_zero hne)
  finite_le k := (Set.finite_Iic k).subset fun _ hn => Int.ofNat_le.mp hn.2

/-- Every natural number belongs to the allowed monoid of `wordLengthDegrees`. -/
@[simp]
theorem wordLengthDegrees_monoid : wordLengthDegrees.monoid = ⊤ := (rfl)

/-- The degree of a natural number in `wordLengthDegrees` is its cast to `ℤ`. -/
@[simp]
theorem wordLengthDegrees_degree (n : ℕ) : wordLengthDegrees.degree n = n := (rfl)

variable (R : Type*) [CommRing R] (S : Type*)

/-- The word-length grading of a free Lie algebra is positive with respect to
`wordLengthDegrees`. -/
instance isPositiveGrading_homogeneousSubmodule :
    IsPositiveGrading wordLengthDegrees (homogeneousSubmodule R S) where
  eq_bot n hn := by
    rcases hn with h | rfl
    · exact absurd (AddSubmonoid.mem_top n) h
    · exact homogeneousSubmodule_zero R S

/-- The word-length degree ideal of a free Lie algebra at cutoff `c` is the `c`-th term of the
lower central series. -/
theorem degreeIdeal_eq_lowerCentralSeries (c : ℕ) :
    wordLengthDegrees.degreeIdeal (homogeneousSubmodule R S) c =
      LieModule.lowerCentralSeries R (_root_.FreeLieAlgebra R S) (_root_.FreeLieAlgebra R S) c := by
  apply LieSubmodule.toSubmodule_injective
  rw [PositiveDegrees.degreeIdeal_toSubmodule, PositiveDegrees.degreeSubmodule_def,
    lowerCentralSeries_toSubmodule_eq_iSup, iSup_subtype]
  refine iSup_congr fun n => iSup_congr_Prop ?_ fun _ => rfl
  simp only [wordLengthDegrees_degree, Int.ofNat_lt]

/-- The positive-degree filtration of the enveloping algebra of a free Lie algebra coincides with
the filtration by powers of the augmentation ideal. -/
theorem positiveDegreeFiltration_ideal_eq_augmentation_pow (k : ℕ) :
    (UniversalEnvelopingAlgebra.positiveDegreeFiltration wordLengthDegrees
        (homogeneousSubmodule R S)).ideal k =
      (HopfIdeal.augmentation R
        (_root_.UniversalEnvelopingAlgebra R (_root_.FreeLieAlgebra R S))).toIdeal ^ k :=
  degreeFiltration_eq_augmentation_pow R S k

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Transporting `truncatedLieToU` along the canonical identifications of word-length quotients
with lower-central and augmentation-power quotients gives `lowerCentralQuotientι`. -/
theorem quotEquivOfEq_truncatedLieToU (c : ℕ)
    (z : wordLengthDegrees.truncatedLie (homogeneousSubmodule R S) c) :
    Ideal.quotEquivOfEq (positiveDegreeFiltration_ideal_eq_augmentation_pow R S (c + 1))
        (UniversalEnvelopingAlgebra.truncatedLieToU wordLengthDegrees
          (homogeneousSubmodule R S) c z) =
      UniversalEnvelopingAlgebra.lowerCentralQuotientι R (_root_.FreeLieAlgebra R S) c
        (LieIdeal.quotEquivOfEq _ _ (degreeIdeal_eq_lowerCentralSeries R S c) z) := by
  obtain ⟨x, rfl⟩ := LieIdeal.surjective_mkQ _ z
  simp [LieIdeal.mkQ_apply, UniversalEnvelopingAlgebra.truncatedLieToU_mk]

end WordLength

section RationalFreeLie

variable (R : Type) [CommRing R] [Algebra ℚ R] (S : Type*)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Over a commutative `ℚ`-algebra `R : Type`, the Lie elements sent into the `(c + 1)`-st power
of the augmentation ideal of `U(F)` are precisely the `c`-th term of the lower central series. -/
theorem comap_augmentation_pow_ι_of_algebra_rat (c : ℕ) :
    (((HopfIdeal.augmentation R
          (_root_.UniversalEnvelopingAlgebra R (_root_.FreeLieAlgebra R S))).toIdeal ^
        (c + 1)).restrictScalars R).comap
        (_root_.UniversalEnvelopingAlgebra.ι R :
          _root_.FreeLieAlgebra R S →ₗ⁅R⁆
            _root_.UniversalEnvelopingAlgebra R (_root_.FreeLieAlgebra R S)).toLinearMap =
      (LieModule.lowerCentralSeries R
        (_root_.FreeLieAlgebra R S) (_root_.FreeLieAlgebra R S) c).toSubmodule :=
  comap_augmentation_pow_ι R S UniversalEnvelopingAlgebra.ι_injective_of_algebra_rat c

/-- Over a commutative `ℚ`-algebra `R : Type`, `lowerCentralQuotientι` embeds the free nilpotent
Lie algebra of class at most `c` into `U(F) ⧸ J ^ (c + 1)`. -/
theorem lowerCentralQuotientι_injective_of_algebra_rat (c : ℕ) :
    Function.Injective
      (UniversalEnvelopingAlgebra.lowerCentralQuotientι R (_root_.FreeLieAlgebra R S) c) :=
  lowerCentralQuotientι_injective R S UniversalEnvelopingAlgebra.ι_injective_of_algebra_rat c

end RationalFreeLie

section UniversalBCH

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "F₂" => _root_.FreeLieAlgebra ℚ (Fin 2)
local notation "U₂" => _root_.UniversalEnvelopingAlgebra ℚ F₂
local notation "J₂" => HopfIdeal.toIdeal (HopfIdeal.augmentation ℚ U₂)
local notation "ℒ₂" => homogeneousSubmodule ℚ (Fin 2)
local notation "𝓕₂" => UniversalEnvelopingAlgebra.positiveDegreeFiltration wordLengthDegrees ℒ₂

/-- The universal Baker–Campbell–Hausdorff element in the word-length completion of the free
`ℚ`-Lie algebra on two generators `X = of 0` and `Y = of 1`, obtained as the Lie logarithm of
`exp(X) * exp(Y)` in the completed enveloping algebra. -/
noncomputable def completedBCH : wordLengthDegrees.completedLie ℒ₂ :=
  let gX := UniversalEnvelopingAlgebra.completedLieEquivCompletedGroupLike wordLengthDegrees ℒ₂
    (LieIdeal.toCompletion (wordLengthDegrees.degreeIdeal ℒ₂)
      (wordLengthDegrees.degreeIdeal_antitone ℒ₂) (_root_.FreeLieAlgebra.of ℚ (0 : Fin 2)))
  let gY := UniversalEnvelopingAlgebra.completedLieEquivCompletedGroupLike wordLengthDegrees ℒ₂
    (LieIdeal.toCompletion (wordLengthDegrees.degreeIdeal ℒ₂)
      (wordLengthDegrees.degreeIdeal_antitone ℒ₂) (_root_.FreeLieAlgebra.of ℚ (1 : Fin 2)))
  (UniversalEnvelopingAlgebra.completedLieEquivCompletedGroupLike wordLengthDegrees ℒ₂).symm
    ⟨gX.1 * gY.1, gX.2.mul gY.2⟩

/-- In the completed enveloping algebra of `F₂`, the completed exponential of
`completedLieToU completedBCH` equals the product of the completed exponentials of the two
generators. -/
theorem completedExp_completedLieToU_completedBCH :
    (𝓕₂).completedExp
        ⟨UniversalEnvelopingAlgebra.completedLieToU wordLengthDegrees ℒ₂ completedBCH,
          UniversalEnvelopingAlgebra.completedLieToU_mem_completionIdeal_one
            wordLengthDegrees ℒ₂ completedBCH⟩ =
      (𝓕₂).completedExp
          ⟨UniversalEnvelopingAlgebra.completedLieToU wordLengthDegrees ℒ₂
              (LieIdeal.toCompletion (wordLengthDegrees.degreeIdeal ℒ₂)
                (wordLengthDegrees.degreeIdeal_antitone ℒ₂)
                (_root_.FreeLieAlgebra.of ℚ (0 : Fin 2))),
            UniversalEnvelopingAlgebra.completedLieToU_mem_completionIdeal_one
              wordLengthDegrees ℒ₂ _⟩ *
        (𝓕₂).completedExp
          ⟨UniversalEnvelopingAlgebra.completedLieToU wordLengthDegrees ℒ₂
              (LieIdeal.toCompletion (wordLengthDegrees.degreeIdeal ℒ₂)
                (wordLengthDegrees.degreeIdeal_antitone ℒ₂)
                (_root_.FreeLieAlgebra.of ℚ (1 : Fin 2))),
            UniversalEnvelopingAlgebra.completedLieToU_mem_completionIdeal_one
              wordLengthDegrees ℒ₂ _⟩ := by
  let e := UniversalEnvelopingAlgebra.completedLieEquivCompletedGroupLike wordLengthDegrees ℒ₂
  let x0 := LieIdeal.toCompletion (wordLengthDegrees.degreeIdeal ℒ₂)
    (wordLengthDegrees.degreeIdeal_antitone ℒ₂) (_root_.FreeLieAlgebra.of ℚ (0 : Fin 2))
  let y0 := LieIdeal.toCompletion (wordLengthDegrees.degreeIdeal ℒ₂)
    (wordLengthDegrees.degreeIdeal_antitone ℒ₂) (_root_.FreeLieAlgebra.of ℚ (1 : Fin 2))
  have h := congrArg Subtype.val (e.apply_symm_apply ⟨(e x0).1 * (e y0).1, (e x0).2.mul (e y0).2⟩)
  simpa only [e, x0, y0, completedBCH,
    UniversalEnvelopingAlgebra.coe_completedLieEquivCompletedGroupLike] using h

/-- The universal Baker–Campbell–Hausdorff element of nilpotency class at most `c`, living in the
free nilpotent `ℚ`-Lie algebra `F₂ ⧸ lowerCentralSeries ℚ F₂ F₂ c` on two generators. -/
noncomputable def bchElement (c : ℕ) :
    F₂ ⧸ LieModule.lowerCentralSeries ℚ F₂ F₂ c :=
  LieIdeal.quotEquivOfEq _ _ (degreeIdeal_eq_lowerCentralSeries ℚ (Fin 2) c)
    (LieIdeal.completionProjection (wordLengthDegrees.degreeIdeal ℒ₂)
      (wordLengthDegrees.degreeIdeal_antitone ℒ₂) c completedBCH)

/-- In `U(F₂) ⧸ J ^ (c + 1)`, exponentiating `ι_c (bchElement c)` recovers
`exp (ι_c X) * exp (ι_c Y)`. -/
theorem exp_lowerCentralQuotientι_bchElement (c : ℕ) :
    IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F₂ c (bchElement c)) =
      IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F₂ c
          (LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ (0 : Fin 2)))) *
        IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F₂ c
          (LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ (1 : Fin 2)))) := by
  let eU := Ideal.quotEquivOfEq
    (positiveDegreeFiltration_ideal_eq_augmentation_pow ℚ (Fin 2) (c + 1))
  have hproj := congrArg (fun u => eU ((𝓕₂).projection c u))
    completedExp_completedLieToU_completedBCH
  have hnil (x : wordLengthDegrees.completedLie ℒ₂) :
      IsNilpotent ((𝓕₂).projection c
        (UniversalEnvelopingAlgebra.completedLieToU wordLengthDegrees ℒ₂ x)) :=
    (𝓕₂).isNilpotent_projection
      (UniversalEnvelopingAlgebra.completedLieToU_mem_completionIdeal_one
        wordLengthDegrees ℒ₂ x) c
  simp only [map_mul, AlgFiltration.projection_completedExp, (hnil _).map_exp] at hproj
  rw [UniversalEnvelopingAlgebra.projection_completedLieToU,
    UniversalEnvelopingAlgebra.projection_completedLieToU,
    UniversalEnvelopingAlgebra.projection_completedLieToU,
    quotEquivOfEq_truncatedLieToU, quotEquivOfEq_truncatedLieToU,
    quotEquivOfEq_truncatedLieToU] at hproj
  simpa only [bchElement, LieIdeal.completionProjection_toCompletion, LieIdeal.mkQ_apply,
    LieIdeal.quotEquivOfEq_mk] using hproj

/-- In `U(F₂) ⧸ J ^ (c + 1)`, the image of `bchElement c` under `lowerCentralQuotientι` is
`log (exp (ι_c X) * exp (ι_c Y))`. -/
theorem lowerCentralQuotientι_bchElement (c : ℕ) :
    UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F₂ c (bchElement c) =
      IsNilpotent.log
        (IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F₂ c
            (LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ (0 : Fin 2)))) *
          IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F₂ c
            (LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ (1 : Fin 2))))) := by
  rw [← exp_lowerCentralQuotientι_bchElement c,
    IsNilpotent.log_exp
      (UniversalEnvelopingAlgebra.isNilpotent_lowerCentralQuotientι ℚ F₂ c (bchElement c))]

/-- The universal Baker–Campbell–Hausdorff element of class `c` lifts to an element `b : F₂`
satisfying `exp (ι b) = exp (ι X) * exp (ι Y)` in `U(F₂) ⧸ J ^ (c + 1)`. -/
theorem exists_bch_exp_mul_exp (c : ℕ) :
    ∃ b : F₂,
      IsNilpotent.exp (Ideal.Quotient.mk (J₂ ^ (c + 1))
          (_root_.UniversalEnvelopingAlgebra.ι ℚ b)) =
        IsNilpotent.exp (Ideal.Quotient.mk (J₂ ^ (c + 1))
            (_root_.UniversalEnvelopingAlgebra.ι ℚ (_root_.FreeLieAlgebra.of ℚ 0))) *
          IsNilpotent.exp (Ideal.Quotient.mk (J₂ ^ (c + 1))
            (_root_.UniversalEnvelopingAlgebra.ι ℚ (_root_.FreeLieAlgebra.of ℚ 1))) := by
  obtain ⟨b, hb⟩ := LieIdeal.surjective_mkQ _ (bchElement c)
  refine ⟨b, ?_⟩
  simpa only [← hb, LieIdeal.mkQ_apply, UniversalEnvelopingAlgebra.lowerCentralQuotientι_mk] using
    exp_lowerCentralQuotientι_bchElement c

/-- `bchElement c` is the unique element of `F₂ ⧸ lowerCentralSeries ℚ F₂ F₂ c` whose image under
`lowerCentralQuotientι` is `log (exp (ι_c X) * exp (ι_c Y))`. -/
theorem eq_bchElement_of_lowerCentralQuotientι_eq {c : ℕ}
    {z : F₂ ⧸ LieModule.lowerCentralSeries ℚ F₂ F₂ c}
    (hz : UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F₂ c z =
      IsNilpotent.log
        (IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F₂ c
            (LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ (0 : Fin 2)))) *
          IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F₂ c
            (LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ (1 : Fin 2)))))) :
    z = bchElement c :=
  lowerCentralQuotientι_injective_of_algebra_rat ℚ (Fin 2) c
    (hz.trans (lowerCentralQuotientι_bchElement c).symm)

/-- `bchElement c` is uniquely characterized by the exponential identity
`exp (ι_c z) = exp (ι_c X) * exp (ι_c Y)` in `U(F₂) ⧸ J ^ (c + 1)`. -/
theorem eq_bchElement_of_exp_lowerCentralQuotientι_eq {c : ℕ}
    {z : F₂ ⧸ LieModule.lowerCentralSeries ℚ F₂ F₂ c}
    (hz : IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F₂ c z) =
      IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F₂ c
          (LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ (0 : Fin 2)))) *
        IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F₂ c
          (LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ (1 : Fin 2))))) :
    z = bchElement c := by
  apply eq_bchElement_of_lowerCentralQuotientι_eq
  rw [← hz, IsNilpotent.log_exp
    (UniversalEnvelopingAlgebra.isNilpotent_lowerCentralQuotientι ℚ F₂ c z)]

/-- The universal Baker–Campbell–Hausdorff elements are compatible under transitions between
nilpotency classes. -/
@[simp]
theorem factor_bchElement {c d : ℕ} (h : c ≤ d) :
    LieIdeal.factor (LieModule.antitone_lowerCentralSeries ℚ F₂ F₂ h) (bchElement d) =
      bchElement c := by
  apply eq_bchElement_of_exp_lowerCentralQuotientι_eq
  rw [UniversalEnvelopingAlgebra.lowerCentralQuotientι_factor ℚ F₂ h,
    ← (UniversalEnvelopingAlgebra.isNilpotent_lowerCentralQuotientι ℚ F₂ d (bchElement d)).map_exp,
    exp_lowerCentralQuotientι_bchElement d, map_mul,
    (UniversalEnvelopingAlgebra.isNilpotent_lowerCentralQuotientι ℚ F₂ d _).map_exp,
    (UniversalEnvelopingAlgebra.isNilpotent_lowerCentralQuotientι ℚ F₂ d _).map_exp]
  simp only [← UniversalEnvelopingAlgebra.lowerCentralQuotientι_factor ℚ F₂ h,
    LieIdeal.factor_apply]

/-- Pushing a two-sided ideal `I` forward into the quotient by `I ^ n` yields an ideal whose
`n`-th power vanishes. -/
private theorem map_quotient_pow_eq_bot {A : Type*} [Ring A] (I : Ideal A) [I.IsTwoSided] (n : ℕ) :
    Ideal.map (Ideal.Quotient.mk (I ^ n)) I ^ n = ⊥ := by
  have hle (k : ℕ) :
      Ideal.map (Ideal.Quotient.mk (I ^ n)) I ^ k ≤
        Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ k) := by
    induction k with
    | zero =>
      rw [Submodule.pow_zero, Submodule.pow_zero]
      intro y _
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact Ideal.mem_map_of_mem _ (by simp [Ideal.one_eq_top])
    | succ k ih =>
      rw [Submodule.pow_succ, Submodule.pow_succ]
      refine Submodule.mul_le.mpr fun a ha b hb => ?_
      obtain ⟨x, hx, rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp (ih ha)
      obtain ⟨y, hy, rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hb
      rw [← map_mul]
      exact Ideal.mem_map_of_mem _ (Ideal.mul_mem_mul hx hy)
  exact le_bot_iff.mp ((hle n).trans (Ideal.map_quotient_self (I ^ n)).le)

/-- In nilpotency class `0`, the universal Baker–Campbell–Hausdorff element is `0`. -/
@[simp]
theorem bchElement_zero : bchElement 0 = 0 := by
  obtain ⟨z, hz⟩ := LieIdeal.surjective_mkQ _ (bchElement 0)
  rw [← hz, LieIdeal.mkQ_eq_zero, LieModule.lowerCentralSeries_zero]
  trivial

/-- In nilpotency class at most `2`, the universal Baker–Campbell–Hausdorff element is the class of
`X + Y + ½ ⁅X, Y⁆`. -/
theorem bchElement_two :
    bchElement 2 =
      LieSubmodule.Quotient.mk
        (_root_.FreeLieAlgebra.of ℚ (0 : Fin 2) + _root_.FreeLieAlgebra.of ℚ (1 : Fin 2) +
          (1 / 2 : ℚ) • ⁅_root_.FreeLieAlgebra.of ℚ (0 : Fin 2),
            _root_.FreeLieAlgebra.of ℚ (1 : Fin 2)⁆) := by
  symm
  apply eq_bchElement_of_lowerCentralQuotientι_eq
  have hx : UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F₂ 2
        (LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ (0 : Fin 2))) ∈
      Ideal.map (Ideal.Quotient.mk (J₂ ^ 3)) J₂ := by
    rw [UniversalEnvelopingAlgebra.lowerCentralQuotientι_mk]
    exact Ideal.mem_map_of_mem _ (HopfIdeal.mem_toIdeal.mpr
      (UniversalEnvelopingAlgebra.ι_mem_augmentation ℚ F₂ _))
  have hy : UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F₂ 2
        (LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ (1 : Fin 2))) ∈
      Ideal.map (Ideal.Quotient.mk (J₂ ^ 3)) J₂ := by
    rw [UniversalEnvelopingAlgebra.lowerCentralQuotientι_mk]
    exact Ideal.mem_map_of_mem _ (HopfIdeal.mem_toIdeal.mpr
      (UniversalEnvelopingAlgebra.ι_mem_augmentation ℚ F₂ _))
  rw [Ideal.log_exp_mul_exp_of_pow_three_eq_bot _ (map_quotient_pow_eq_bot J₂ 3) hx hy]
  let q := (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F₂ 2).comp
    (LieIdeal.mkQ (LieModule.lowerCentralSeries ℚ F₂ F₂ 2))
  change q _ = _
  simp only [map_add, map_smul, LieHom.map_lie, q, LieHom.comp_apply, LieIdeal.mkQ_apply]

/-- In nilpotency class at most `1`, the universal Baker–Campbell–Hausdorff element is the class of
`X + Y`. -/
theorem bchElement_one :
    bchElement 1 =
      LieSubmodule.Quotient.mk
        (_root_.FreeLieAlgebra.of ℚ (0 : Fin 2) + _root_.FreeLieAlgebra.of ℚ (1 : Fin 2)) := by
  rw [← factor_bchElement (by omega : 1 ≤ 2), bchElement_two, LieIdeal.factor_apply]
  change LieIdeal.mkQ (LieModule.lowerCentralSeries ℚ F₂ F₂ 1)
      (_root_.FreeLieAlgebra.of ℚ (0 : Fin 2) + _root_.FreeLieAlgebra.of ℚ (1 : Fin 2) +
        (1 / 2 : ℚ) • ⁅_root_.FreeLieAlgebra.of ℚ (0 : Fin 2),
          _root_.FreeLieAlgebra.of ℚ (1 : Fin 2)⁆) =
    LieIdeal.mkQ (LieModule.lowerCentralSeries ℚ F₂ F₂ 1)
      (_root_.FreeLieAlgebra.of ℚ (0 : Fin 2) + _root_.FreeLieAlgebra.of ℚ (1 : Fin 2))
  rw [map_add, map_smul]
  have hlie : LieIdeal.mkQ (LieModule.lowerCentralSeries ℚ F₂ F₂ 1)
      ⁅_root_.FreeLieAlgebra.of ℚ (0 : Fin 2), _root_.FreeLieAlgebra.of ℚ (1 : Fin 2)⁆ = 0 := by
    rw [LieIdeal.mkQ_eq_zero, LieModule.lowerCentralSeries_succ]
    exact LieSubmodule.lie_mem_lie trivial trivial
  simp [hlie]

/-- In nilpotency class at most `3`, the universal Baker–Campbell–Hausdorff element is the class of
`X + Y + ½ ⁅X, Y⁆ + 1/12 (⁅X, ⁅X, Y⁆⁆ + ⁅Y, ⁅Y, X⁆⁆)`. -/
theorem bchElement_three :
    bchElement 3 =
      LieSubmodule.Quotient.mk
        (_root_.FreeLieAlgebra.of ℚ (0 : Fin 2) + _root_.FreeLieAlgebra.of ℚ (1 : Fin 2) +
          (1 / 2 : ℚ) • ⁅_root_.FreeLieAlgebra.of ℚ (0 : Fin 2),
            _root_.FreeLieAlgebra.of ℚ (1 : Fin 2)⁆ +
          (1 / 12 : ℚ) •
            (⁅_root_.FreeLieAlgebra.of ℚ (0 : Fin 2),
              ⁅_root_.FreeLieAlgebra.of ℚ (0 : Fin 2),
                _root_.FreeLieAlgebra.of ℚ (1 : Fin 2)⁆⁆ +
            ⁅_root_.FreeLieAlgebra.of ℚ (1 : Fin 2),
              ⁅_root_.FreeLieAlgebra.of ℚ (1 : Fin 2),
                _root_.FreeLieAlgebra.of ℚ (0 : Fin 2)⁆⁆)) := by
  symm
  apply eq_bchElement_of_lowerCentralQuotientι_eq
  have hx : UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F₂ 3
        (LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ (0 : Fin 2))) ∈
      Ideal.map (Ideal.Quotient.mk (J₂ ^ 4)) J₂ := by
    rw [UniversalEnvelopingAlgebra.lowerCentralQuotientι_mk]
    exact Ideal.mem_map_of_mem _ (HopfIdeal.mem_toIdeal.mpr
      (UniversalEnvelopingAlgebra.ι_mem_augmentation ℚ F₂ _))
  have hy : UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F₂ 3
        (LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ (1 : Fin 2))) ∈
      Ideal.map (Ideal.Quotient.mk (J₂ ^ 4)) J₂ := by
    rw [UniversalEnvelopingAlgebra.lowerCentralQuotientι_mk]
    exact Ideal.mem_map_of_mem _ (HopfIdeal.mem_toIdeal.mpr
      (UniversalEnvelopingAlgebra.ι_mem_augmentation ℚ F₂ _))
  rw [Ideal.log_exp_mul_exp_of_pow_four_eq_bot _ (map_quotient_pow_eq_bot J₂ 4) hx hy]
  let q := (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F₂ 3).comp
    (LieIdeal.mkQ (LieModule.lowerCentralSeries ℚ F₂ F₂ 3))
  change q _ = _
  simp only [map_add, map_smul, LieHom.map_lie, q, LieHom.comp_apply, LieIdeal.mkQ_apply]

end UniversalBCH

end TauCeti.FreeLieAlgebra
