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
# The universal Baker–Campbell–Hausdorff element

Word length equips `FreeLieAlgebra R S` over any commutative ring `R` with a positive `ℕ`-grading
(`TauCeti.FreeLieAlgebra.isPositiveGrading`) whose degree ideals are the lower central series
(`TauCeti.FreeLieAlgebra.degreeIdeal_eq_lowerCentralSeries`) and whose enveloping filtration
coincides with the powers of the augmentation ideal
(`TauCeti.FreeLieAlgebra.envelopingFiltration_ideal_eq_augmentation_pow`). Over a commutative
rational algebra `R : Type`, `TauCeti.FreeLieAlgebra.comap_augmentation_pow_ι_of_rat` removes the
injectivity hypothesis on `ι`.

Specializing `TauCeti.PositiveDegrees.completedLieBCH` to `FreeLieAlgebra ℚ S` constructs, for any
`x, y : FreeLieAlgebra ℚ S` and nilpotency class `c : ℕ`, the unique class
`TauCeti.FreeLieAlgebra.bchQuotient S x y c` modulo `lowerCentralSeries c` whose image in the
truncated enveloping algebra exponentiates to `exp x * exp y`. On `FreeLieTwo` this defines
`TauCeti.FreeLieAlgebra.bchElement`, proves `TauCeti.FreeLieAlgebra.comap_freeAugmentation_pow_ι`
and `TauCeti.FreeLieAlgebra.exists_bch_exp_mul_exp`, and evaluates `bchElement` explicitly through
nilpotency class three.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter II, §6.
* C. Reutenauer, *Free Lie Algebras*, Chapter 3.
* J.-P. Serre, *Lie Algebras and Lie Groups*, Part I, Chapter IV.
-/

public section

namespace TauCeti.FreeLieAlgebra

open _root_.UniversalEnvelopingAlgebra

section CommRing

variable (R : Type*) [CommRing R] (S : Type*)

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "F" => _root_.FreeLieAlgebra R S
local notation "U" => _root_.UniversalEnvelopingAlgebra R F
local notation "J" => HopfIdeal.toIdeal (HopfIdeal.augmentation R U)
local notation "ℒ" => homogeneousSubmodule R S

/-- Word length equips the free Lie algebra over any commutative ring with a positive
`ℕ`-grading. -/
instance isPositiveGrading : IsPositiveGrading PositiveDegrees.naturals ℒ where
  eq_bot n hn := by
    rcases hn with hnot | rfl
    · exact False.elim (hnot (PositiveDegrees.mem_naturals_monoid n))
    · exact homogeneousSubmodule_zero R S

/-- For the word-length grading of a free Lie algebra, the degree ideal above cutoff `c` is the
`c`-th term of Mathlib's zero-based lower central series. -/
theorem degreeIdeal_eq_lowerCentralSeries (c : ℕ) :
    PositiveDegrees.naturals.degreeIdeal ℒ c = LieModule.lowerCentralSeries R F F c := by
  apply LieSubmodule.toSubmodule_injective
  rw [PositiveDegrees.degreeIdeal_toSubmodule, PositiveDegrees.degreeSubmodule_def,
    lowerCentralSeries_toSubmodule_eq_iSup, iSup_subtype]
  exact iSup_congr fun _ => iSup_congr_Prop (by simp) fun _ => rfl

/-- For the word-length grading of a free Lie algebra, the positive-degree enveloping filtration
coincides with the powers of the augmentation ideal. -/
theorem envelopingFiltration_ideal_eq_augmentation_pow (k : ℕ) :
    (PositiveDegrees.naturals.envelopingFiltration ℒ).ideal k = J ^ k := by
  rw [PositiveDegrees.envelopingFiltration_def]
  exact UniversalEnvelopingAlgebra.degreeFiltration_eq_augmentation_pow ℒ
    PositiveDegrees.naturals.degree (PositiveDegrees.naturals.eq_bot_of_degree_nonpos ℒ)
    (_root_.FreeLieAlgebra.of R) (fun _ => 1) (lieSpan_range_of_eq_top R S)
    (fun s => by simpa using word_mem_homogeneousSubmodule R (FreeMagma.of s)) (fun _ => by simp) k

/-- The Lie equivalence identifying the order-`c` word-length truncation of `FreeLieAlgebra R S`
with its nilpotent quotient modulo `lowerCentralSeries c`. -/
noncomputable def truncatedLieEquivLowerCentralQuotient (c : ℕ) :
    PositiveDegrees.naturals.truncatedLie ℒ c ≃ₗ⁅R⁆ F ⧸ LieModule.lowerCentralSeries R F F c :=
  (PositiveDegrees.naturals.degreeIdeal ℒ c).quotEquivOfEq
    (LieModule.lowerCentralSeries R F F c) (degreeIdeal_eq_lowerCentralSeries R S c)

@[simp]
theorem truncatedLieEquivLowerCentralQuotient_mk (c : ℕ) (x : F) :
    truncatedLieEquivLowerCentralQuotient R S c (LieSubmodule.Quotient.mk x) =
      LieSubmodule.Quotient.mk x :=
  LieIdeal.quotEquivOfEq_mk _ _ _ x

theorem factor_truncatedLieEquivLowerCentralQuotient {c₁ c₂ : ℕ} (h : c₁ ≤ c₂)
    (y : PositiveDegrees.naturals.truncatedLie ℒ c₂) :
    LieIdeal.factor (LieModule.antitone_lowerCentralSeries R F F h)
        (truncatedLieEquivLowerCentralQuotient R S c₂ y) =
      truncatedLieEquivLowerCentralQuotient R S c₁
        (LieIdeal.factor (PositiveDegrees.naturals.degreeIdeal_antitone ℒ h) y) := by
  obtain ⟨x, rfl⟩ := (PositiveDegrees.naturals.degreeIdeal ℒ c₂).surjective_mkQ y
  simp [LieIdeal.mkQ_apply]

/-- The ring equivalence identifying the order-`k` enveloping quotient for word length with the
quotient by the `k`-th power of the augmentation ideal. -/
noncomputable def envelopingQuotientEquivAugmentationPow (k : ℕ) :
    U ⧸ (PositiveDegrees.naturals.envelopingFiltration ℒ).ideal k ≃+* U ⧸ J ^ k :=
  Ideal.quotEquivOfEq (envelopingFiltration_ideal_eq_augmentation_pow R S k)

@[simp]
theorem envelopingQuotientEquivAugmentationPow_mk (k : ℕ) (u : U) :
    envelopingQuotientEquivAugmentationPow R S k (Ideal.Quotient.mk _ u) =
      Ideal.Quotient.mk (J ^ k) u :=
  Ideal.quotEquivOfEq_mk _ u

theorem envelopingQuotientEquivAugmentationPow_truncatedLieToU (c : ℕ)
    (y : PositiveDegrees.naturals.truncatedLie ℒ c) :
    envelopingQuotientEquivAugmentationPow R S (c + 1)
        (PositiveDegrees.naturals.truncatedLieToU ℒ c y) =
      UniversalEnvelopingAlgebra.lowerCentralQuotientι R F c
        (truncatedLieEquivLowerCentralQuotient R S c y) := by
  obtain ⟨x, rfl⟩ := (PositiveDegrees.naturals.degreeIdeal ℒ c).surjective_mkQ y
  simp [LieIdeal.mkQ_apply]

end CommRing

section RatAlgebra

universe u

variable (R : Type) [CommRing R] [Algebra ℚ R] (S : Type u)

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "F" => _root_.FreeLieAlgebra R S
local notation "U" => _root_.UniversalEnvelopingAlgebra R F
local notation "J" => HopfIdeal.toIdeal (HopfIdeal.augmentation R U)

/-- Over a commutative rational algebra `R : Type`, the preimage of `J ^ (c + 1)` along the
canonical map `ι : FreeLieAlgebra R S → U(FreeLieAlgebra R S)` is `lowerCentralSeries c`. -/
theorem comap_augmentation_pow_ι_of_rat (c : ℕ) :
    ((J ^ (c + 1)).restrictScalars R).comap
        (_root_.UniversalEnvelopingAlgebra.ι R : F →ₗ⁅R⁆ U).toLinearMap =
      (LieModule.lowerCentralSeries R F F c).toSubmodule :=
  comap_augmentation_pow_ι R S (UniversalEnvelopingAlgebra.ι_injective_of_rat R F) c

/-- Over a commutative rational algebra `R : Type`, the induced Lie homomorphism from
`FreeLieAlgebra R S ⧸ lowerCentralSeries c` into `U ⧸ J ^ (c + 1)` is injective. -/
theorem lowerCentralQuotientι_injective_of_rat (c : ℕ) :
    Function.Injective (UniversalEnvelopingAlgebra.lowerCentralQuotientι R F c) :=
  lowerCentralQuotientι_injective R S (UniversalEnvelopingAlgebra.ι_injective_of_rat R F) c

end RatAlgebra

section RationalBCH

universe u

variable (S : Type u)

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "F" => _root_.FreeLieAlgebra ℚ S
local notation "U" => _root_.UniversalEnvelopingAlgebra ℚ F
local notation "J" => HopfIdeal.toIdeal (HopfIdeal.augmentation ℚ U)
local notation "ℒ" => homogeneousSubmodule ℚ S

/-- The completed Baker–Campbell–Hausdorff product of two elements of `FreeLieAlgebra ℚ S` in its
word-length completion. -/
noncomputable def completedBCH (x y : F) : PositiveDegrees.naturals.completedLie ℒ :=
  PositiveDegrees.naturals.completedLieBCH ℒ
    (LieIdeal.toCompletion (PositiveDegrees.naturals.degreeIdeal ℒ)
      (PositiveDegrees.naturals.degreeIdeal_antitone ℒ) x)
    (LieIdeal.toCompletion (PositiveDegrees.naturals.degreeIdeal ℒ)
      (PositiveDegrees.naturals.degreeIdeal_antitone ℒ) y)

/-- The class-`c` Baker–Campbell–Hausdorff element associated to `x, y : FreeLieAlgebra ℚ S` in
`FreeLieAlgebra ℚ S ⧸ lowerCentralSeries c`. -/
noncomputable def bchQuotient (x y : F) (c : ℕ) :
    F ⧸ LieModule.lowerCentralSeries ℚ F F c :=
  truncatedLieEquivLowerCentralQuotient ℚ S c
    (LieIdeal.completionProjection (PositiveDegrees.naturals.degreeIdeal ℒ)
      (PositiveDegrees.naturals.degreeIdeal_antitone ℒ) c (completedBCH S x y))

/-- The class-`c` Baker–Campbell–Hausdorff elements are compatible with the transitions between
lower central quotients. -/
@[simp]
theorem factor_bchQuotient {c₁ c₂ : ℕ} (h : c₁ ≤ c₂) (x y : F) :
    LieIdeal.factor (LieModule.antitone_lowerCentralSeries ℚ F F h) (bchQuotient S x y c₂) =
      bchQuotient S x y c₁ := by
  rw [bchQuotient, bchQuotient, factor_truncatedLieEquivLowerCentralQuotient ℚ S h,
    LieIdeal.factor_completionProjection]

/-- In `U(FreeLieAlgebra ℚ S) ⧸ J ^ (c + 1)`, the image of `bchQuotient S x y c` is the nilpotent
logarithm of `exp (ι x) * exp (ι y)`. -/
theorem lowerCentralQuotientι_bchQuotient (x y : F) (c : ℕ) :
    UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c (bchQuotient S x y c) =
      IsNilpotent.log
        (IsNilpotent.exp (Ideal.Quotient.mk (J ^ (c + 1)) (ι ℚ x)) *
          IsNilpotent.exp (Ideal.Quotient.mk (J ^ (c + 1)) (ι ℚ y))) := by
  let Φ := PositiveDegrees.naturals.envelopingFiltration ℒ
  let e := envelopingQuotientEquivAugmentationPow ℚ S (c + 1)
  let u (z : F) : Φ.completionIdeal 1 :=
    ⟨PositiveDegrees.naturals.completedLieToU ℒ
        (LieIdeal.toCompletion (PositiveDegrees.naturals.degreeIdeal ℒ)
          (PositiveDegrees.naturals.degreeIdeal_antitone ℒ) z),
      PositiveDegrees.naturals.completedLieToU_mem_completionIdeal_one ℒ _⟩
  let prod : {v : Φ.completion // v - 1 ∈ Φ.completionIdeal 1} :=
    ⟨Φ.completedExp (u x) * Φ.completedExp (u y),
      Φ.completedExp_mul_completedExp_sub_one_mem (u x) (u y)⟩
  have hu (z : F) : e (Φ.projection c (u z).val) = Ideal.Quotient.mk (J ^ (c + 1)) (ι ℚ z) := by
    simp [e, u, Φ, AlgFiltration.projection_toCompletion]
  rw [bchQuotient, ← envelopingQuotientEquivAugmentationPow_truncatedLieToU,
    ← PositiveDegrees.projection_completedLieToU, completedBCH,
    PositiveDegrees.completedLieToU_completedLieBCH]
  -- Fold the enveloping filtration, quotient equivalence, and product into local abbreviations.
  change e (Φ.projection c (Φ.completedLog prod)) = _
  rw [AlgFiltration.projection_completedLog,
    (by simpa only [map_sub, map_one] using Φ.isNilpotent_projection prod.property c :
      IsNilpotent (Φ.projection c prod.val - 1)).map_log e]
  congr 1
  simp only [prod, map_mul, AlgFiltration.projection_completedExp,
    (Φ.isNilpotent_projection (u x).property c).map_exp e,
    (Φ.isNilpotent_projection (u y).property c).map_exp e, hu]

private noncomputable def quotAugmentationPow (m k : ℕ) : Ideal (U ⧸ J ^ m) where
  carrier := Ideal.Quotient.mk (J ^ m) '' ((J ^ k : Ideal U) : Set U)
  add_mem' := by rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩; exact ⟨a + b, add_mem ha hb, map_add _ a b⟩
  zero_mem' := ⟨0, zero_mem _, map_zero _⟩
  smul_mem' r := by
    rintro _ ⟨a, ha, rfl⟩; obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective r
    exact ⟨s * a, (J ^ k).mul_mem_left s ha, map_mul _ s a⟩

private theorem mk_ι_mem_quotAugmentationPow (m : ℕ) (x : F) :
    Ideal.Quotient.mk (J ^ m) (ι ℚ x) ∈ quotAugmentationPow S m 1 :=
  ⟨ι ℚ x, by
    rw [Submodule.pow_one, SetLike.mem_coe, HopfIdeal.mem_toIdeal]
    exact UniversalEnvelopingAlgebra.ι_mem_augmentation ℚ F x, rfl⟩

private theorem quotAugmentationPow_one_pow_eq_bot (m : ℕ) :
    (quotAugmentationPow S m 1) ^ m = ⊥ := by
  have hle (k : ℕ) : (quotAugmentationPow S m 1) ^ k ≤ quotAugmentationPow S m k := by
    induction k with
    | zero =>
      rintro u -; obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective u
      exact ⟨a, by simp [Submodule.pow_zero, Ideal.one_eq_top], rfl⟩
    | succ k ih =>
      rw [Submodule.pow_succ]; refine Submodule.mul_le.mpr fun u hu v hv => ?_
      obtain ⟨a, ha, rfl⟩ := ih hu; obtain ⟨b, hb, rfl⟩ := hv
      exact ⟨a * b, by
        rw [Submodule.pow_succ]; exact Ideal.mul_mem_mul ha (by simpa [Submodule.pow_one] using hb),
        map_mul _ a b⟩
  refine eq_bot_iff.mpr ((hle m).trans ?_)
  rintro _ ⟨a, ha, rfl⟩; simpa using Ideal.Quotient.eq_zero_iff_mem.mpr ha

/-- Exponentiating the image of `bchQuotient S x y c` in `U ⧸ J ^ (c + 1)` recovers the product
`exp (ι x) * exp (ι y)`. -/
@[simp]
theorem exp_lowerCentralQuotientι_bchQuotient (x y : F) (c : ℕ) :
    IsNilpotent.exp
        (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c (bchQuotient S x y c)) =
      IsNilpotent.exp (Ideal.Quotient.mk (J ^ (c + 1)) (ι ℚ x)) *
        IsNilpotent.exp (Ideal.Quotient.mk (J ^ (c + 1)) (ι ℚ y)) := by
  rw [lowerCentralQuotientι_bchQuotient]
  exact IsNilpotent.exp_log ⟨c + 1,
    (quotAugmentationPow S (c + 1) 1).exp_mul_exp_sub_one_pow_eq_zero
      (quotAugmentationPow_one_pow_eq_bot S (c + 1))
      (mk_ι_mem_quotAugmentationPow S (c + 1) x) (mk_ι_mem_quotAugmentationPow S (c + 1) y)⟩

/-- `bchQuotient S x y c` is the unique element of `FreeLieAlgebra ℚ S ⧸ lowerCentralSeries c`
whose image in `U ⧸ J ^ (c + 1)` exponentiates to `exp (ι x) * exp (ι y)`. -/
theorem eq_bchQuotient_of_exp_eq {x y : F} {c : ℕ}
    {z : F ⧸ LieModule.lowerCentralSeries ℚ F F c}
    (hz : IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c z) =
      IsNilpotent.exp (Ideal.Quotient.mk (J ^ (c + 1)) (ι ℚ x)) *
        IsNilpotent.exp (Ideal.Quotient.mk (J ^ (c + 1)) (ι ℚ y))) :
    z = bchQuotient S x y c :=
  lowerCentralQuotientι_injective_of_rat ℚ S c <| by
    rw [lowerCentralQuotientι_bchQuotient, ← hz]
    exact (IsNilpotent.log_exp
      (UniversalEnvelopingAlgebra.isNilpotent_lowerCentralQuotientι ℚ F c z)).symm

/-- Through nilpotency class three, `bchQuotient S x y 3` is given by the cubic
Baker–Campbell–Hausdorff polynomial `x + y + ½⁅x, y⁆ + 1/12 (⁅x, ⁅x, y⁆⁆ + ⁅y, ⁅y, x⁆⁆)`. -/
theorem bchQuotient_three (x y : F) :
    bchQuotient S x y 3 = LieSubmodule.Quotient.mk
      (x + y + (1 / 2 : ℚ) • ⁅x, y⁆ + (1 / 12 : ℚ) • (⁅x, ⁅x, y⁆⁆ + ⁅y, ⁅y, x⁆⁆)) := by
  let I : LieIdeal ℚ F := LieModule.lowerCentralSeries ℚ F F 3
  apply lowerCentralQuotientι_injective_of_rat ℚ S 3
  rw [lowerCentralQuotientι_bchQuotient,
    Ideal.log_exp_mul_exp_of_pow_four_eq_bot (quotAugmentationPow S 4 1)
      (quotAugmentationPow_one_pow_eq_bot S 4)
      (mk_ι_mem_quotAugmentationPow S 4 x) (mk_ι_mem_quotAugmentationPow S 4 y)]
  -- Express the quotient class via `I.mkQ` so `map_add`, `map_smul`, and `map_lie` expand it.
  change _ = UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F 3 (I.mkQ _)
  simp only [map_add, map_smul, LieHom.map_lie, I, LieIdeal.mkQ_apply,
    UniversalEnvelopingAlgebra.lowerCentralQuotientι_mk]

/-- Through nilpotency class two, `bchQuotient S x y 2` is `x + y + ½⁅x, y⁆`. -/
theorem bchQuotient_two (x y : F) :
    bchQuotient S x y 2 = LieSubmodule.Quotient.mk (x + y + (1 / 2 : ℚ) • ⁅x, y⁆) := by
  let I : LieIdeal ℚ F := LieModule.lowerCentralSeries ℚ F F 2
  apply lowerCentralQuotientι_injective_of_rat ℚ S 2
  rw [lowerCentralQuotientι_bchQuotient,
    Ideal.log_exp_mul_exp_of_pow_three_eq_bot (quotAugmentationPow S 3 1)
      (quotAugmentationPow_one_pow_eq_bot S 3)
      (mk_ι_mem_quotAugmentationPow S 3 x) (mk_ι_mem_quotAugmentationPow S 3 y)]
  -- Express the quotient class via `I.mkQ` so `map_add`, `map_smul`, and `map_lie` expand it.
  change _ = UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F 2 (I.mkQ _)
  simp only [map_add, map_smul, LieHom.map_lie, I, LieIdeal.mkQ_apply,
    UniversalEnvelopingAlgebra.lowerCentralQuotientι_mk]

/-- At nilpotency class one, `bchQuotient S x y 1` is the abelian sum `x + y`. -/
theorem bchQuotient_one (x y : F) :
    bchQuotient S x y 1 = LieSubmodule.Quotient.mk (x + y) := by
  rw [← factor_bchQuotient S (by decide : 1 ≤ 2) x y, bchQuotient_two, LieIdeal.factor_apply]
  have hlie : ⁅x, y⁆ ∈ LieModule.lowerCentralSeries ℚ F F 1 := by
    rw [LieModule.lowerCentralSeries_succ]; exact LieSubmodule.lie_mem_lie trivial trivial
  let I : LieIdeal ℚ F := LieModule.lowerCentralSeries ℚ F F 1
  -- Rewrite both quotient classes as `I.mkQ` applications to kill the commutator term.
  change I.mkQ (x + y + (1 / 2 : ℚ) • ⁅x, y⁆) = I.mkQ (x + y)
  rw [map_add, map_smul, I.mkQ_eq_zero.mpr hlie, smul_zero, add_zero]

/-- At nilpotency class zero, `bchQuotient S x y 0` vanishes. -/
@[simp]
theorem bchQuotient_zero (x y : F) : bchQuotient S x y 0 = 0 := by
  obtain ⟨z, hz⟩ :=
    LieIdeal.surjective_mkQ (LieModule.lowerCentralSeries ℚ F F 0) (bchQuotient S x y 0)
  exact hz ▸ (LieIdeal.mkQ_eq_zero _).mpr (by simp [LieModule.lowerCentralSeries_zero])

end RationalBCH

section FreeLieTwo

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The free Lie algebra over `ℚ` on two canonical generators `of 0` and `of 1`. -/
abbrev FreeLieTwo : Type := _root_.FreeLieAlgebra ℚ (Fin 2)

/-- The augmentation ideal of `U(FreeLieTwo)` for its canonical Hopf algebra structure. -/
noncomputable abbrev freeAugmentation : Ideal (_root_.UniversalEnvelopingAlgebra ℚ FreeLieTwo) :=
  (HopfIdeal.augmentation ℚ (_root_.UniversalEnvelopingAlgebra ℚ FreeLieTwo)).toIdeal

local notation "X" => _root_.FreeLieAlgebra.of ℚ (0 : Fin 2)
local notation "Y" => _root_.FreeLieAlgebra.of ℚ (1 : Fin 2)

/-- The preimage of `freeAugmentation ^ (c + 1)` under `ι : FreeLieTwo → U(FreeLieTwo)` is the
`c`-th term of the lower central series. -/
theorem comap_freeAugmentation_pow_ι (c : ℕ) :
    ((freeAugmentation ^ (c + 1)).restrictScalars ℚ).comap
        (ι ℚ : FreeLieTwo →ₗ⁅ℚ⁆ _root_.UniversalEnvelopingAlgebra ℚ FreeLieTwo).toLinearMap =
      (LieModule.lowerCentralSeries ℚ FreeLieTwo FreeLieTwo c).toSubmodule :=
  comap_augmentation_pow_ι_of_rat ℚ (Fin 2) c

/-- The universal Baker–Campbell–Hausdorff element of nilpotency class `c` in
`FreeLieTwo ⧸ lowerCentralSeries c`, on the two free generators `of 0` and `of 1`. -/
noncomputable def bchElement (c : ℕ) :
    FreeLieTwo ⧸ LieModule.lowerCentralSeries ℚ FreeLieTwo FreeLieTwo c :=
  bchQuotient (Fin 2) X Y c

/-- The universal Baker–Campbell–Hausdorff elements form a compatible family along the lower
central quotient tower. -/
@[simp]
theorem factor_bchElement {c₁ c₂ : ℕ} (h : c₁ ≤ c₂) :
    LieIdeal.factor (LieModule.antitone_lowerCentralSeries ℚ FreeLieTwo FreeLieTwo h)
        (bchElement c₂) = bchElement c₁ :=
  factor_bchQuotient (Fin 2) h _ _

/-- In `U(FreeLieTwo) ⧸ freeAugmentation ^ (c + 1)`, the image of `bchElement c` is
`log (exp (of 0) * exp (of 1))`. -/
theorem lowerCentralQuotientι_bchElement (c : ℕ) :
    UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ FreeLieTwo c (bchElement c) =
      IsNilpotent.log
        (IsNilpotent.exp (Ideal.Quotient.mk (freeAugmentation ^ (c + 1)) (ι ℚ X)) *
          IsNilpotent.exp (Ideal.Quotient.mk (freeAugmentation ^ (c + 1)) (ι ℚ Y))) :=
  lowerCentralQuotientι_bchQuotient (Fin 2) _ _ c

/-- Exponentiating the image of `bchElement c` in `U(FreeLieTwo) ⧸ freeAugmentation ^ (c + 1)`
gives `exp (of 0) * exp (of 1)`. -/
@[simp]
theorem exp_lowerCentralQuotientι_bchElement (c : ℕ) :
    IsNilpotent.exp
        (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ FreeLieTwo c (bchElement c)) =
      IsNilpotent.exp (Ideal.Quotient.mk (freeAugmentation ^ (c + 1)) (ι ℚ X)) *
        IsNilpotent.exp (Ideal.Quotient.mk (freeAugmentation ^ (c + 1)) (ι ℚ Y)) :=
  exp_lowerCentralQuotientι_bchQuotient (Fin 2) _ _ c

/-- For every nilpotency class `c`, there exists a Lie element `b : FreeLieTwo` whose exponential
in `U(FreeLieTwo) ⧸ freeAugmentation ^ (c + 1)` equals `exp (of 0) * exp (of 1)`; by
`comap_freeAugmentation_pow_ι`, `b` is unique modulo `lowerCentralSeries c`. -/
theorem exists_bch_exp_mul_exp (c : ℕ) :
    ∃ b : FreeLieTwo,
      IsNilpotent.exp (Ideal.Quotient.mk (freeAugmentation ^ (c + 1)) (ι ℚ b)) =
        IsNilpotent.exp (Ideal.Quotient.mk (freeAugmentation ^ (c + 1)) (ι ℚ X)) *
          IsNilpotent.exp (Ideal.Quotient.mk (freeAugmentation ^ (c + 1)) (ι ℚ Y)) := by
  obtain ⟨b, hb⟩ :=
    LieIdeal.surjective_mkQ (LieModule.lowerCentralSeries ℚ FreeLieTwo FreeLieTwo c) (bchElement c)
  exact ⟨b, by
    simpa only [← hb, LieIdeal.mkQ_apply, UniversalEnvelopingAlgebra.lowerCentralQuotientι_mk] using
      exp_lowerCentralQuotientι_bchElement c⟩

/-- `bchElement c` is uniquely characterized in `FreeLieTwo ⧸ lowerCentralSeries c` by the
exponential identity in `U(FreeLieTwo) ⧸ freeAugmentation ^ (c + 1)`. -/
theorem eq_bchElement_of_exp_eq {c : ℕ}
    {z : FreeLieTwo ⧸ LieModule.lowerCentralSeries ℚ FreeLieTwo FreeLieTwo c}
    (hz : IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ FreeLieTwo c z) =
      IsNilpotent.exp (Ideal.Quotient.mk (freeAugmentation ^ (c + 1)) (ι ℚ X)) *
        IsNilpotent.exp (Ideal.Quotient.mk (freeAugmentation ^ (c + 1)) (ι ℚ Y))) :
    z = bchElement c :=
  eq_bchQuotient_of_exp_eq (Fin 2) hz

@[simp]
theorem bchElement_zero : bchElement 0 = 0 := bchQuotient_zero (Fin 2) _ _

theorem bchElement_one : bchElement 1 = LieSubmodule.Quotient.mk (X + Y) :=
  bchQuotient_one (Fin 2) _ _

theorem bchElement_two : bchElement 2 = LieSubmodule.Quotient.mk (X + Y + (1 / 2 : ℚ) • ⁅X, Y⁆) :=
  bchQuotient_two (Fin 2) _ _

/-- Through nilpotency class three, the universal Baker–Campbell–Hausdorff element is
`X + Y + ½⁅X, Y⁆ + 1/12 (⁅X, ⁅X, Y⁆⁆ + ⁅Y, ⁅Y, X⁆⁆)`. -/
theorem bchElement_three :
    bchElement 3 = LieSubmodule.Quotient.mk
      (X + Y + (1 / 2 : ℚ) • ⁅X, Y⁆ + (1 / 12 : ℚ) • (⁅X, ⁅X, Y⁆⁆ + ⁅Y, ⁅Y, X⁆⁆)) :=
  bchQuotient_three (Fin 2) _ _

end FreeLieTwo

end TauCeti.FreeLieAlgebra
