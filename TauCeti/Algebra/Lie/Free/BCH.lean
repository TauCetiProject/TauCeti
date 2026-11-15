/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Free.Enveloping
public import TauCeti.Algebra.Lie.UniversalEnveloping.Completion.Primitive
public import TauCeti.RingTheory.Nilpotent.BCH

/-!
# The universal Baker–Campbell–Hausdorff element

Let `F = FreeLieAlgebra ℚ S` be the free Lie algebra over `ℚ` on a generating type `S`, graded by
word length over `PositiveDegrees.naturals`, and let `J` be the augmentation ideal of `U(F)`. The
word-length degree ideals `PositiveDegrees.naturals.degreeIdeal` coincide with the zero-based lower
central series of `F`, while the enveloping degree filtration coincides with the powers `J ^ k`.

In the degree completion of `U(F)`, the completed exponentials of Lie generators are completed
group-like (`AlgFiltration.isCompletedGroupLike_completedExp_iff`), their product remains completed
group-like, and its completed logarithm is completed primitive
(`AlgFiltration.isCompletedPrimitive_completedLog_iff`). By
`UniversalEnvelopingAlgebra.completedPrimitiveLieEquiv`, that logarithm comes from a unique element
of the completed free Lie algebra. Projecting to cutoff `c` produces the Baker–Campbell–Hausdorff
product `bchQuotient S c x y` on the free nilpotent Lie algebra
`F ⧸ LieModule.lowerCentralSeries ℚ F F c`, characterized uniquely by
`exp (ι_c (bchQuotient S c x y)) = exp (ι_c x) * exp (ι_c y)` in `U(F) ⧸ J ^ (c + 1)`.

Specializing `S = Fin 2` at the canonical generators `X = of ℚ 0` and `Y = of ℚ 1` yields the
universal Baker–Campbell–Hausdorff element `bchElement c` of nilpotency class `c`, compatible
across truncation cutoffs and matching the explicit polynomials through degree three.

## Main definitions

* `TauCeti.FreeLieAlgebra.instIsPositiveGradingNaturals`: word length is a positive grading of
  `FreeLieAlgebra R S` over `PositiveDegrees.naturals`.
* `TauCeti.FreeLieAlgebra.bchQuotient`: the Baker–Campbell–Hausdorff binary operation on
  `FreeLieAlgebra ℚ S ⧸ LieModule.lowerCentralSeries ℚ _ _ c`.
* `TauCeti.FreeLieAlgebra.bchElement`: the universal Baker–Campbell–Hausdorff element of class `c`
  in `FreeLieAlgebra ℚ (Fin 2) ⧸ LieModule.lowerCentralSeries ℚ _ _ c`.

## Main results

* `TauCeti.FreeLieAlgebra.naturals_degreeIdeal_eq_lowerCentralSeries`: the word-length degree ideal
  at cutoff `c` is `LieModule.lowerCentralSeries R F F c`.
* `TauCeti.FreeLieAlgebra.comap_augmentation_pow_ι_of_ratAlgebra` and
  `TauCeti.FreeLieAlgebra.lowerCentralQuotientι_injective_of_ratAlgebra`: over any commutative
  `ℚ`-algebra `R : Type`, the nilpotent quotient embeds into `U(F) ⧸ J ^ (c + 1)`.
* `TauCeti.FreeLieAlgebra.lowerCentralQuotientι_bchQuotient`,
  `TauCeti.FreeLieAlgebra.exp_lowerCentralQuotientι_bchQuotient`, and
  `TauCeti.FreeLieAlgebra.bchQuotient_unique`: logarithmic formula, exponential product law, and
  uniqueness of `bchQuotient`.
* `TauCeti.FreeLieAlgebra.bchQuotient_assoc`, `TauCeti.FreeLieAlgebra.bchQuotient_zero_left`,
  `TauCeti.FreeLieAlgebra.bchQuotient_zero_right`, `TauCeti.FreeLieAlgebra.bchQuotient_neg_left`,
  `TauCeti.FreeLieAlgebra.bchQuotient_neg_right`, and `TauCeti.FreeLieAlgebra.factor_bchQuotient`:
  group axioms and truncation compatibility of `bchQuotient`.
* `TauCeti.FreeLieAlgebra.exists_bch_exp_mul_exp` and
  `TauCeti.FreeLieAlgebra.bchElement_zero`..`bchElement_three`: existence of a Lie representative
  with `exp (ι b) = exp (ι X) * exp (ι Y)` modulo `J ^ (c + 1)` and explicit low-degree formulas.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters 1–3, Ch. II, §6 (construction of the
  Campbell–Hausdorff series via primitive and group-like elements of the completed enveloping
  algebra of a free Lie algebra).
-/

public section

namespace TauCeti.FreeLieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

section CommRing

variable (R : Type*) [CommRing R] (S : Type*)

local notation "F" => _root_.FreeLieAlgebra R S
local notation "U" => _root_.UniversalEnvelopingAlgebra R F
local notation "J" => HopfIdeal.toIdeal (HopfIdeal.augmentation R U)
local notation "ℒ" => homogeneousSubmodule R S

/-- Word length equips `FreeLieAlgebra R S` with a positive grading over `PositiveDegrees.naturals`.
-/
instance instIsPositiveGradingNaturals :
    IsPositiveGrading PositiveDegrees.naturals (homogeneousSubmodule R S) where
  eq_bot n hn := by
    rcases hn with hmon | rfl
    · exact (hmon PositiveDegrees.mem_naturals_monoid).elim
    · exact homogeneousSubmodule_zero R S

/-- The word-length degree ideal at cutoff `c` is the `c`-th term of the lower central series. -/
theorem naturals_degreeIdeal_eq_lowerCentralSeries (c : ℕ) :
    PositiveDegrees.naturals.degreeIdeal ℒ c = LieModule.lowerCentralSeries R F F c := by
  apply LieSubmodule.toSubmodule_injective
  rw [PositiveDegrees.degreeIdeal_toSubmodule, ← degreeTail_eq_lowerCentralSeries]
  ext x
  rw [PositiveDegrees.mem_degreeSubmodule_iff, DirectSum.mem_degreeTail_iff]
  simp only [PositiveDegrees.naturals_degree, Nat.coe_castAddMonoidHom]
  exact ⟨fun h n hn => h n (by omega), fun h n hn => h n (by omega)⟩

/-- For `PositiveDegrees.naturals`, the enveloping degree filtration on `U(FreeLieAlgebra R S)` is
the filtration by powers of the augmentation ideal. -/
theorem naturals_degreeFiltration_eq_augmentation_pow
    (hneg : ∀ n, PositiveDegrees.naturals.degree n < 0 → ℒ n = ⊥) (k : ℕ) :
    (UniversalEnvelopingAlgebra.degreeFiltration ℒ PositiveDegrees.naturals.degree hneg).ideal k =
      J ^ k :=
  UniversalEnvelopingAlgebra.degreeFiltration_eq_augmentation_pow ℒ
    PositiveDegrees.naturals.degree (PositiveDegrees.naturals.eq_bot_of_degree_nonpos ℒ)
    (_root_.FreeLieAlgebra.of R) (fun _ => 1) (lieSpan_range_of_eq_top R S)
    (fun s => by simpa using word_mem_homogeneousSubmodule R (FreeMagma.of s))
    (fun _ => by simp) k

end CommRing

section RatAlgebra

variable (R : Type) [CommRing R] [Algebra ℚ R] (S : Type*)

local notation "F" => _root_.FreeLieAlgebra R S
local notation "U" => _root_.UniversalEnvelopingAlgebra R F
local notation "J" => HopfIdeal.toIdeal (HopfIdeal.augmentation R U)

/-- Over a commutative `ℚ`-algebra `R : Type`, the Lie elements sent into `J ^ (c + 1)` by `ι R` are
precisely `LieModule.lowerCentralSeries R F F c`. -/
theorem comap_augmentation_pow_ι_of_ratAlgebra (c : ℕ) :
    ((J ^ (c + 1)).restrictScalars R).comap
        (_root_.UniversalEnvelopingAlgebra.ι R : F →ₗ⁅R⁆ U).toLinearMap =
      (LieModule.lowerCentralSeries R F F c).toSubmodule :=
  comap_augmentation_pow_ι R S (UniversalEnvelopingAlgebra.ι_injective_of_ratAlgebra R F) c

/-- Over a commutative `ℚ`-algebra `R : Type`, the free nilpotent quotient of class at most `c`
embeds into `U(F) ⧸ J ^ (c + 1)`. -/
theorem lowerCentralQuotientι_injective_of_ratAlgebra (c : ℕ) :
    Function.Injective (UniversalEnvelopingAlgebra.lowerCentralQuotientι R F c) :=
  lowerCentralQuotientι_injective R S (UniversalEnvelopingAlgebra.ι_injective_of_ratAlgebra R F) c

end RatAlgebra

section BCHQuotient

variable (S : Type*)

local notation "F" => _root_.FreeLieAlgebra ℚ S
local notation "U" => _root_.UniversalEnvelopingAlgebra ℚ F
local notation "J" => HopfIdeal.toIdeal (HopfIdeal.augmentation ℚ U)
local notation "ℒ" => homogeneousSubmodule ℚ S
local notation "δ" => PositiveDegrees.naturals

private theorem hneg_naturals (n : ℕ) (hn : PositiveDegrees.naturals.degree n < 0) : ℒ n = ⊥ :=
  PositiveDegrees.naturals.eq_bot_of_degree_nonpos ℒ n hn.le

private noncomputable abbrev freeFiltration : AlgFiltration U :=
  UniversalEnvelopingAlgebra.degreeFiltration ℒ PositiveDegrees.naturals.degree (hneg_naturals S)

private noncomputable def completedGeneratorExp (w : F) : (freeFiltration S).completion :=
  (freeFiltration S).completedExp
    ⟨UniversalEnvelopingAlgebra.completedLieToU ℒ δ (hneg_naturals S)
      (LieIdeal.toCompletion ((δ).degreeIdeal ℒ) ((δ).degreeIdeal_antitone ℒ) w),
     UniversalEnvelopingAlgebra.completedLieToU_mem_completionIdeal_one ℒ δ (hneg_naturals S) _⟩

private theorem isCompletedGroupLike_completedGeneratorExp (w : F) :
    (freeFiltration S).IsCompletedGroupLike ℚ (completedGeneratorExp S w) :=
  ((freeFiltration S).isCompletedGroupLike_completedExp_iff ℚ _).mpr
    (UniversalEnvelopingAlgebra.isCompletedPrimitive_completedLieToU ℒ δ (hneg_naturals S) _)

private theorem completedGeneratorExp_mul_sub_one_mem (x₀ y₀ : F) :
    completedGeneratorExp S x₀ * completedGeneratorExp S y₀ - 1 ∈
      (freeFiltration S).completionIdeal 1 :=
  ((freeFiltration S).sub_one_mem_completionIdeal_one_iff_completedCounit_eq_one ℚ
    (UniversalEnvelopingAlgebra.ker_counitAlgHom_le_positiveDegreeFiltration_one ℒ δ
      (hneg_naturals S)) _).mpr
    ((isCompletedGroupLike_completedGeneratorExp S x₀).mul
      (isCompletedGroupLike_completedGeneratorExp S y₀)).completedCounit_eq_one

private noncomputable def completedBCHOfElem (x₀ y₀ : F) : (δ).completedLie ℒ :=
  (UniversalEnvelopingAlgebra.completedPrimitiveLieEquiv ℚ ℒ δ (hneg_naturals S)).symm
    ⟨(freeFiltration S).completedLog ⟨completedGeneratorExp S x₀ * completedGeneratorExp S y₀,
        completedGeneratorExp_mul_sub_one_mem S x₀ y₀⟩,
     (UniversalEnvelopingAlgebra.mem_completedPrimitives_iff ℒ (δ).degree (hneg_naturals S)).mpr <|
       ((freeFiltration S).isCompletedPrimitive_completedLog_iff ℚ _).mpr
         ((isCompletedGroupLike_completedGeneratorExp S x₀).mul
           (isCompletedGroupLike_completedGeneratorExp S y₀))⟩

private theorem lowerCentralQuotientι_quotEquiv (c : ℕ) (z : (δ).truncatedLie ℒ c) :
    UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c
        (((δ).degreeIdeal ℒ c).quotEquivOfEq _
          (naturals_degreeIdeal_eq_lowerCentralSeries ℚ S c) z) =
      Ideal.quotEquivOfEq
        (naturals_degreeFiltration_eq_augmentation_pow ℚ S (hneg_naturals S) (c + 1))
        (UniversalEnvelopingAlgebra.truncatedLieToU ℒ δ (hneg_naturals S) c z) := by
  obtain ⟨w, rfl⟩ := LieIdeal.surjective_mkQ ((δ).degreeIdeal ℒ c) z
  simp [LieIdeal.mkQ_apply]

/-- The Baker–Campbell–Hausdorff product on the free nilpotent Lie algebra
`FreeLieAlgebra ℚ S ⧸ LieModule.lowerCentralSeries ℚ _ _ c`, obtained by projecting the completed
logarithm of `exp x * exp y` from the completed enveloping algebra. -/
noncomputable def bchQuotient (c : ℕ)
    (x y : F ⧸ LieModule.lowerCentralSeries ℚ F F c) :
    F ⧸ LieModule.lowerCentralSeries ℚ F F c :=
  let x₀ := (LieIdeal.surjective_mkQ (LieModule.lowerCentralSeries ℚ F F c) x).choose
  let y₀ := (LieIdeal.surjective_mkQ (LieModule.lowerCentralSeries ℚ F F c) y).choose
  (((δ).degreeIdeal ℒ c).quotEquivOfEq _ (naturals_degreeIdeal_eq_lowerCentralSeries ℚ S c))
    (LieIdeal.completionProjection ((δ).degreeIdeal ℒ) ((δ).degreeIdeal_antitone ℒ) c
      (completedBCHOfElem S x₀ y₀))

/-- In `U(F) ⧸ J ^ (c + 1)`, every image of `lowerCentralQuotientι` lies in the image of the
augmentation ideal `J`. -/
theorem lowerCentralQuotientι_mem_map_augmentation (c : ℕ)
    (x : F ⧸ LieModule.lowerCentralSeries ℚ F F c) :
    UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c x ∈
      Ideal.map (Ideal.Quotient.mk ((J) ^ (c + 1))) (J) := by
  obtain ⟨x₀, rfl⟩ := LieIdeal.surjective_mkQ (LieModule.lowerCentralSeries ℚ F F c) x
  rw [LieIdeal.mkQ_apply, UniversalEnvelopingAlgebra.lowerCentralQuotientι_mk]
  exact Ideal.mem_map_of_mem _
    (HopfIdeal.mem_toIdeal.mpr (UniversalEnvelopingAlgebra.ι_mem_augmentation ℚ F x₀))

private theorem map_quotient_mk_pow_eq_bot {A : Type*} [Ring A] (K : Ideal A) [K.IsTwoSided]
    (n : ℕ) : (Ideal.map (Ideal.Quotient.mk (K ^ n)) K) ^ n = ⊥ := by
  have hle (m : ℕ) :
      (Ideal.map (Ideal.Quotient.mk (K ^ n)) K) ^ m ≤
        Ideal.map (Ideal.Quotient.mk (K ^ n)) (K ^ m) := by
    induction m with
    | zero => simp [Submodule.pow_zero, Ideal.one_eq_top, Ideal.map_top]
    | succ m ih =>
      rw [Submodule.pow_succ, Submodule.pow_succ]
      refine (Ideal.mul_mono_left ih).trans (Ideal.mul_le.mpr ?_)
      intro r hr s hs
      obtain ⟨a, ha, rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hr
      obtain ⟨b, hb, rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hs
      rw [← map_mul]
      exact Ideal.mem_map_of_mem _ (Ideal.mul_mem_mul ha hb)
  exact le_bot_iff.mp ((hle n).trans_eq (Ideal.map_quotient_self (K ^ n)))

/-- For `x, y` in the free nilpotent quotient of class `c`, `exp (ι_c x) * exp (ι_c y) - 1` is
nilpotent in `U(F) ⧸ J ^ (c + 1)`. -/
theorem isNilpotent_exp_mul_exp_sub_one_lowerCentralQuotientι (c : ℕ)
    (x y : F ⧸ LieModule.lowerCentralSeries ℚ F F c) :
    IsNilpotent
      (IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c x) *
        IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c y) - 1) :=
  ⟨c + 1, (Ideal.map (Ideal.Quotient.mk ((J) ^ (c + 1))) (J)).exp_mul_exp_sub_one_pow_eq_zero
    (map_quotient_mk_pow_eq_bot (J) (c + 1))
    (lowerCentralQuotientι_mem_map_augmentation S c x)
    (lowerCentralQuotientι_mem_map_augmentation S c y)⟩

/-- Mapping `bchQuotient S c x y` into `U(F) ⧸ J ^ (c + 1)` computes the finite logarithm
`log (exp (ι_c x) * exp (ι_c y))`. -/
theorem lowerCentralQuotientι_bchQuotient (c : ℕ)
    (x y : F ⧸ LieModule.lowerCentralSeries ℚ F F c) :
    UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c (bchQuotient S c x y) =
      IsNilpotent.log
        (IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c x) *
          IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c y)) := by
  let x₀ := (LieIdeal.surjective_mkQ (LieModule.lowerCentralSeries ℚ F F c) x).choose
  let y₀ := (LieIdeal.surjective_mkQ (LieModule.lowerCentralSeries ℚ F F c) y).choose
  have hx₀ : (LieSubmodule.Quotient.mk x₀ : F ⧸ LieModule.lowerCentralSeries ℚ F F c) = x :=
    (LieIdeal.surjective_mkQ (LieModule.lowerCentralSeries ℚ F F c) x).choose_spec
  have hy₀ : (LieSubmodule.Quotient.mk y₀ : F ⧸ LieModule.lowerCentralSeries ℚ F F c) = y :=
    (LieIdeal.surjective_mkQ (LieModule.lowerCentralSeries ℚ F F c) y).choose_spec
  let eU := Ideal.quotEquivOfEq
    (naturals_degreeFiltration_eq_augmentation_pow ℚ S (hneg_naturals S) (c + 1))
  have hproj :
      (freeFiltration S).projection c
          (UniversalEnvelopingAlgebra.completedLieToU ℒ δ (hneg_naturals S)
            (completedBCHOfElem S x₀ y₀)) =
        IsNilpotent.log
          ((freeFiltration S).projection c
            (completedGeneratorExp S x₀ * completedGeneratorExp S y₀)) := by
    rw [completedBCHOfElem,
      UniversalEnvelopingAlgebra.completedLieToU_completedPrimitiveLieEquiv_symm,
      AlgFiltration.projection_completedLog]
  have hnil_sub :
      IsNilpotent
        ((freeFiltration S).projection c
          (completedGeneratorExp S x₀ * completedGeneratorExp S y₀) - 1) := by
    simpa only [map_sub, map_one] using
      (freeFiltration S).isNilpotent_projection
        (completedGeneratorExp_mul_sub_one_mem S x₀ y₀) c
  have hgen (w : F) :
      eU ((freeFiltration S).projection c (completedGeneratorExp S w)) =
        IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c
          (LieSubmodule.Quotient.mk w)) := by
    have hnil_w :
        IsNilpotent
          ((freeFiltration S).projection c
            (UniversalEnvelopingAlgebra.completedLieToU ℒ δ (hneg_naturals S)
              (LieIdeal.toCompletion ((δ).degreeIdeal ℒ) ((δ).degreeIdeal_antitone ℒ) w))) :=
      (freeFiltration S).isNilpotent_projection
        (UniversalEnvelopingAlgebra.completedLieToU_mem_completionIdeal_one ℒ δ
          (hneg_naturals S) _) c
    rw [completedGeneratorExp, AlgFiltration.projection_completedExp,
      IsNilpotent.map_exp hnil_w eU]
    congr 1
    simp [eU, UniversalEnvelopingAlgebra.completedLieToU_toCompletion]
  rw [bchQuotient, lowerCentralQuotientι_quotEquiv,
    ← UniversalEnvelopingAlgebra.projection_completedLieToU, hproj]
  change eU (IsNilpotent.log _) = _
  rw [IsNilpotent.map_log hnil_sub eU, map_mul, map_mul, hgen x₀, hgen y₀, hx₀, hy₀]

/-- **Exponential law for `bchQuotient`:** exponentiating the image of `bchQuotient S c x y` in
`U(F) ⧸ J ^ (c + 1)` recovers `exp (ι_c x) * exp (ι_c y)`. -/
@[simp]
theorem exp_lowerCentralQuotientι_bchQuotient (c : ℕ)
    (x y : F ⧸ LieModule.lowerCentralSeries ℚ F F c) :
    IsNilpotent.exp
        (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c (bchQuotient S c x y)) =
      IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c x) *
        IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c y) := by
  rw [lowerCentralQuotientι_bchQuotient,
    IsNilpotent.exp_log (isNilpotent_exp_mul_exp_sub_one_lowerCentralQuotientι S c x y)]

/-- `bchQuotient S c x y` is the unique element of the free nilpotent quotient whose exponential in
`U(F) ⧸ J ^ (c + 1)` equals `exp (ι_c x) * exp (ι_c y)`. -/
theorem bchQuotient_unique (c : ℕ)
    {x y z : F ⧸ LieModule.lowerCentralSeries ℚ F F c} :
    IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c z) =
        IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c x) *
          IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c y) ↔
      z = bchQuotient S c x y := by
  refine ⟨fun h => ?_, fun h => h ▸ exp_lowerCentralQuotientι_bchQuotient S c x y⟩
  apply lowerCentralQuotientι_injective_of_ratAlgebra ℚ S c
  rw [lowerCentralQuotientι_bchQuotient, ← h,
    IsNilpotent.log_exp (UniversalEnvelopingAlgebra.isNilpotent_lowerCentralQuotientι ℚ F c z)]

/-- The Baker–Campbell–Hausdorff operation on `F ⧸ lowerCentralSeries ℚ F F c` is associative. -/
theorem bchQuotient_assoc (c : ℕ)
    (x y z : F ⧸ LieModule.lowerCentralSeries ℚ F F c) :
    bchQuotient S c (bchQuotient S c x y) z =
      bchQuotient S c x (bchQuotient S c y z) := by
  rw [← bchQuotient_unique, exp_lowerCentralQuotientι_bchQuotient,
    exp_lowerCentralQuotientι_bchQuotient, mul_assoc, ← exp_lowerCentralQuotientι_bchQuotient]

/-- Zero is a left identity for `bchQuotient`. -/
@[simp]
theorem bchQuotient_zero_left (c : ℕ) (x : F ⧸ LieModule.lowerCentralSeries ℚ F F c) :
    bchQuotient S c 0 x = x := by
  symm
  rw [← bchQuotient_unique, map_zero, IsNilpotent.exp_zero, one_mul]

/-- Zero is a right identity for `bchQuotient`. -/
@[simp]
theorem bchQuotient_zero_right (c : ℕ) (x : F ⧸ LieModule.lowerCentralSeries ℚ F F c) :
    bchQuotient S c x 0 = x := by
  symm
  rw [← bchQuotient_unique, map_zero, IsNilpotent.exp_zero, mul_one]

/-- Negation is a left inverse for `bchQuotient`. -/
@[simp]
theorem bchQuotient_neg_left (c : ℕ) (x : F ⧸ LieModule.lowerCentralSeries ℚ F F c) :
    bchQuotient S c (-x) x = 0 := by
  symm
  rw [← bchQuotient_unique, map_zero, map_neg, IsNilpotent.exp_zero]
  exact (IsNilpotent.exp_neg_mul_exp_self
    (UniversalEnvelopingAlgebra.isNilpotent_lowerCentralQuotientι ℚ F c x)).symm

/-- Negation is a right inverse for `bchQuotient`. -/
@[simp]
theorem bchQuotient_neg_right (c : ℕ) (x : F ⧸ LieModule.lowerCentralSeries ℚ F F c) :
    bchQuotient S c x (-x) = 0 := by
  symm
  rw [← bchQuotient_unique, map_zero, map_neg, IsNilpotent.exp_zero]
  exact (IsNilpotent.exp_mul_exp_neg_self
    (UniversalEnvelopingAlgebra.isNilpotent_lowerCentralQuotientι ℚ F c x)).symm

/-- When two elements commute in `F ⧸ lowerCentralSeries ℚ F F c`, their Baker–Campbell–Hausdorff
product is their sum. -/
theorem bchQuotient_of_lie_eq_zero (c : ℕ)
    {x y : F ⧸ LieModule.lowerCentralSeries ℚ F F c} (hxy : ⁅x, y⁆ = 0) :
    bchQuotient S c x y = x + y := by
  symm
  rw [← bchQuotient_unique, map_add]
  have hcomm : Commute
      (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c x)
      (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c y) := by
    have hlie := congrArg (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c) hxy
    rw [LieHom.map_lie, map_zero, Ring.lie_def, sub_eq_zero] at hlie
    exact hlie
  exact IsNilpotent.exp_add_of_commute hcomm
    (UniversalEnvelopingAlgebra.isNilpotent_lowerCentralQuotientι ℚ F c x)
    (UniversalEnvelopingAlgebra.isNilpotent_lowerCentralQuotientι ℚ F c y)

/-- `bchQuotient` commutes with the lower-central truncation transitions `LieIdeal.factor`. -/
theorem factor_bchQuotient {c d : ℕ} (h : c ≤ d)
    (x y : F ⧸ LieModule.lowerCentralSeries ℚ F F d) :
    LieIdeal.factor (LieModule.antitone_lowerCentralSeries ℚ F F h) (bchQuotient S d x y) =
      bchQuotient S c
        (LieIdeal.factor (LieModule.antitone_lowerCentralSeries ℚ F F h) x)
        (LieIdeal.factor (LieModule.antitone_lowerCentralSeries ℚ F F h) y) := by
  rw [← bchQuotient_unique]
  let f := Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (I := (J)) (Nat.add_le_add_right h 1))
  calc
    IsNilpotent.exp
        (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c
          (LieIdeal.factor (LieModule.antitone_lowerCentralSeries ℚ F F h) (bchQuotient S d x y)))
        = IsNilpotent.exp
            (f (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F d (bchQuotient S d x y))) := by
          rw [UniversalEnvelopingAlgebra.lowerCentralQuotientι_factor ℚ F h]
    _ = f (IsNilpotent.exp
          (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F d (bchQuotient S d x y))) :=
        (IsNilpotent.map_exp
          (UniversalEnvelopingAlgebra.isNilpotent_lowerCentralQuotientι ℚ F d _) f).symm
    _ = f (IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F d x)) *
          f (IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F d y)) := by
        rw [exp_lowerCentralQuotientι_bchQuotient, map_mul]
    _ = IsNilpotent.exp
          (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c
            (LieIdeal.factor (LieModule.antitone_lowerCentralSeries ℚ F F h) x)) *
        IsNilpotent.exp
          (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c
            (LieIdeal.factor (LieModule.antitone_lowerCentralSeries ℚ F F h) y)) := by
        rw [IsNilpotent.map_exp
              (UniversalEnvelopingAlgebra.isNilpotent_lowerCentralQuotientι ℚ F d x) f,
            IsNilpotent.map_exp
              (UniversalEnvelopingAlgebra.isNilpotent_lowerCentralQuotientι ℚ F d y) f,
            ← UniversalEnvelopingAlgebra.lowerCentralQuotientι_factor ℚ F h,
            ← UniversalEnvelopingAlgebra.lowerCentralQuotientι_factor ℚ F h]

/-- At nilpotency class zero, `bchQuotient` vanishes. -/
@[simp]
theorem bchQuotient_zero (x y : F ⧸ LieModule.lowerCentralSeries ℚ F F 0) :
    bchQuotient S 0 x y = 0 := by
  obtain ⟨z, hz⟩ :=
    LieIdeal.surjective_mkQ (LieModule.lowerCentralSeries ℚ F F 0) (bchQuotient S 0 x y)
  rw [← hz, LieIdeal.mkQ_apply, LieSubmodule.Quotient.mk_eq_zero']
  simp

/-- At nilpotency class one (abelianization), `bchQuotient` is addition. -/
theorem bchQuotient_one (x y : F ⧸ LieModule.lowerCentralSeries ℚ F F 1) :
    bchQuotient S 1 x y = x + y := by
  apply bchQuotient_of_lie_eq_zero
  obtain ⟨x₀, rfl⟩ := LieIdeal.surjective_mkQ (LieModule.lowerCentralSeries ℚ F F 1) x
  obtain ⟨y₀, rfl⟩ := LieIdeal.surjective_mkQ (LieModule.lowerCentralSeries ℚ F F 1) y
  rw [LieIdeal.mkQ_apply, LieIdeal.mkQ_apply, ← LieSubmodule.Quotient.mk_bracket,
    LieSubmodule.Quotient.mk_eq_zero', LieModule.lowerCentralSeries_succ]
  exact LieSubmodule.lie_mem_lie trivial trivial

/-- At nilpotency class two, `bchQuotient` is `x + y + (1 / 2) • ⁅x, y⁆`. -/
theorem bchQuotient_two (x y : F ⧸ LieModule.lowerCentralSeries ℚ F F 2) :
    bchQuotient S 2 x y = x + y + (1 / 2 : ℚ) • ⁅x, y⁆ := by
  apply lowerCentralQuotientι_injective_of_ratAlgebra ℚ S 2
  rw [lowerCentralQuotientι_bchQuotient,
    Ideal.log_exp_mul_exp_of_pow_three_eq_bot
      (Ideal.map (Ideal.Quotient.mk ((J) ^ 3)) (J)) (map_quotient_mk_pow_eq_bot (J) 3)
      (lowerCentralQuotientι_mem_map_augmentation S 2 x)
      (lowerCentralQuotientι_mem_map_augmentation S 2 y)]
  simp [map_add, map_smul, LieHom.map_lie]

/-- At nilpotency class three, `bchQuotient` is
`x + y + (1 / 2) • ⁅x, y⁆ + (1 / 12) • (⁅x, ⁅x, y⁆⁆ + ⁅y, ⁅y, x⁆⁆)`. -/
theorem bchQuotient_three (x y : F ⧸ LieModule.lowerCentralSeries ℚ F F 3) :
    bchQuotient S 3 x y =
      x + y + (1 / 2 : ℚ) • ⁅x, y⁆ + (1 / 12 : ℚ) • (⁅x, ⁅x, y⁆⁆ + ⁅y, ⁅y, x⁆⁆) := by
  apply lowerCentralQuotientι_injective_of_ratAlgebra ℚ S 3
  rw [lowerCentralQuotientι_bchQuotient,
    Ideal.log_exp_mul_exp_of_pow_four_eq_bot
      (Ideal.map (Ideal.Quotient.mk ((J) ^ 4)) (J)) (map_quotient_mk_pow_eq_bot (J) 4)
      (lowerCentralQuotientι_mem_map_augmentation S 3 x)
      (lowerCentralQuotientι_mem_map_augmentation S 3 y)]
  simp [map_add, map_smul, LieHom.map_lie]

end BCHQuotient

section BCHElement

local notation "F₂" => _root_.FreeLieAlgebra ℚ (Fin 2)
local notation "U₂" => _root_.UniversalEnvelopingAlgebra ℚ F₂
local notation "J₂" => HopfIdeal.toIdeal (HopfIdeal.augmentation ℚ U₂)

/-- The universal Baker–Campbell–Hausdorff element of nilpotency class `c`, evaluated at the two
free generators `X = FreeLieAlgebra.of ℚ 0` and `Y = FreeLieAlgebra.of ℚ 1`. -/
noncomputable def bchElement (c : ℕ) : F₂ ⧸ LieModule.lowerCentralSeries ℚ F₂ F₂ c :=
  bchQuotient (Fin 2) c
    (LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ (0 : Fin 2)))
    (LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ (1 : Fin 2)))

/-- Mapping `bchElement c` into `U(F₂) ⧸ J₂ ^ (c + 1)` computes `log (exp (ι X) * exp (ι Y))`. -/
theorem lowerCentralQuotientι_bchElement (c : ℕ) :
    UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F₂ c (bchElement c) =
      IsNilpotent.log
        (IsNilpotent.exp
            (Ideal.Quotient.mk ((J₂) ^ (c + 1))
              (_root_.UniversalEnvelopingAlgebra.ι ℚ (_root_.FreeLieAlgebra.of ℚ (0 : Fin 2)))) *
          IsNilpotent.exp
            (Ideal.Quotient.mk ((J₂) ^ (c + 1))
              (_root_.UniversalEnvelopingAlgebra.ι ℚ
                (_root_.FreeLieAlgebra.of ℚ (1 : Fin 2))))) := by
  simpa only [bchElement, UniversalEnvelopingAlgebra.lowerCentralQuotientι_mk] using
    lowerCentralQuotientι_bchQuotient (Fin 2) c
      (LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ (0 : Fin 2)))
      (LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ (1 : Fin 2)))

/-- Exponentiating the image of `bchElement c` in `U(F₂) ⧸ J₂ ^ (c + 1)` recovers
`exp (ι X) * exp (ι Y)`. -/
@[simp]
theorem exp_lowerCentralQuotientι_bchElement (c : ℕ) :
    IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F₂ c (bchElement c)) =
      IsNilpotent.exp
          (Ideal.Quotient.mk ((J₂) ^ (c + 1))
            (_root_.UniversalEnvelopingAlgebra.ι ℚ (_root_.FreeLieAlgebra.of ℚ (0 : Fin 2)))) *
        IsNilpotent.exp
          (Ideal.Quotient.mk ((J₂) ^ (c + 1))
            (_root_.UniversalEnvelopingAlgebra.ι ℚ (_root_.FreeLieAlgebra.of ℚ (1 : Fin 2)))) := by
  simpa only [bchElement, UniversalEnvelopingAlgebra.lowerCentralQuotientι_mk] using
    exp_lowerCentralQuotientι_bchQuotient (Fin 2) c
      (LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ (0 : Fin 2)))
      (LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ (1 : Fin 2)))

/-- Uniqueness of the universal Baker–Campbell–Hausdorff element of class `c`. -/
theorem bchElement_unique (c : ℕ) {z : F₂ ⧸ LieModule.lowerCentralSeries ℚ F₂ F₂ c} :
    IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F₂ c z) =
        IsNilpotent.exp
            (Ideal.Quotient.mk ((J₂) ^ (c + 1))
              (_root_.UniversalEnvelopingAlgebra.ι ℚ (_root_.FreeLieAlgebra.of ℚ (0 : Fin 2)))) *
          IsNilpotent.exp
            (Ideal.Quotient.mk ((J₂) ^ (c + 1))
              (_root_.UniversalEnvelopingAlgebra.ι ℚ (_root_.FreeLieAlgebra.of ℚ (1 : Fin 2)))) ↔
      z = bchElement c := by
  simpa only [bchElement, UniversalEnvelopingAlgebra.lowerCentralQuotientι_mk] using
    bchQuotient_unique (Fin 2) c
      (x := LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ (0 : Fin 2)))
      (y := LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ (1 : Fin 2))) (z := z)

/-- Existence of a Lie representative `b : FreeLieAlgebra ℚ (Fin 2)` satisfying
`exp (ι b) = exp (ι X) * exp (ι Y)` in `U(FreeLieAlgebra ℚ (Fin 2)) ⧸ J ^ (c + 1)`. -/
theorem exists_bch_exp_mul_exp (c : ℕ) :
    ∃ b : F₂,
      IsNilpotent.exp
          (Ideal.Quotient.mk ((J₂) ^ (c + 1)) (_root_.UniversalEnvelopingAlgebra.ι ℚ b)) =
        IsNilpotent.exp
            (Ideal.Quotient.mk ((J₂) ^ (c + 1))
              (_root_.UniversalEnvelopingAlgebra.ι ℚ (_root_.FreeLieAlgebra.of ℚ (0 : Fin 2)))) *
          IsNilpotent.exp
            (Ideal.Quotient.mk ((J₂) ^ (c + 1))
              (_root_.UniversalEnvelopingAlgebra.ι ℚ
                (_root_.FreeLieAlgebra.of ℚ (1 : Fin 2)))) := by
  obtain ⟨b, hb⟩ := LieIdeal.surjective_mkQ (LieModule.lowerCentralSeries ℚ F₂ F₂ c) (bchElement c)
  have hb' : (LieSubmodule.Quotient.mk b : F₂ ⧸ LieModule.lowerCentralSeries ℚ F₂ F₂ c) =
      bchElement c := hb
  refine ⟨b, ?_⟩
  rw [← UniversalEnvelopingAlgebra.lowerCentralQuotientι_mk, hb',
    exp_lowerCentralQuotientι_bchElement]

/-- The universal Baker–Campbell–Hausdorff elements form a compatible family in the lower-central
tower. -/
theorem factor_bchElement {c d : ℕ} (h : c ≤ d) :
    LieIdeal.factor (LieModule.antitone_lowerCentralSeries ℚ F₂ F₂ h) (bchElement d) =
      bchElement c := by
  simp [bchElement, factor_bchQuotient (Fin 2) h]

/-- At nilpotency class zero, `bchElement 0` is zero. -/
@[simp]
theorem bchElement_zero : bchElement 0 = 0 :=
  bchQuotient_zero (Fin 2) _ _

/-- At nilpotency class one, `bchElement 1` is `X + Y`. -/
theorem bchElement_one :
    bchElement 1 =
      (LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ (0 : Fin 2)) :
          F₂ ⧸ LieModule.lowerCentralSeries ℚ F₂ F₂ 1) +
        LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ (1 : Fin 2)) :=
  bchQuotient_one (Fin 2) _ _

/-- At nilpotency class two, `bchElement 2` is `X + Y + (1 / 2) • ⁅X, Y⁆`. -/
theorem bchElement_two :
    bchElement 2 =
      let X : F₂ ⧸ LieModule.lowerCentralSeries ℚ F₂ F₂ 2 :=
        LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ (0 : Fin 2))
      let Y : F₂ ⧸ LieModule.lowerCentralSeries ℚ F₂ F₂ 2 :=
        LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ (1 : Fin 2))
      X + Y + (1 / 2 : ℚ) • ⁅X, Y⁆ :=
  bchQuotient_two (Fin 2) _ _

/-- At nilpotency class three, `bchElement 3` is
`X + Y + (1 / 2) • ⁅X, Y⁆ + (1 / 12) • (⁅X, ⁅X, Y⁆⁆ + ⁅Y, ⁅Y, X⁆⁆)`. -/
theorem bchElement_three :
    bchElement 3 =
      let X : F₂ ⧸ LieModule.lowerCentralSeries ℚ F₂ F₂ 3 :=
        LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ (0 : Fin 2))
      let Y : F₂ ⧸ LieModule.lowerCentralSeries ℚ F₂ F₂ 3 :=
        LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ (1 : Fin 2))
      X + Y + (1 / 2 : ℚ) • ⁅X, Y⁆ + (1 / 12 : ℚ) • (⁅X, ⁅X, Y⁆⁆ + ⁅Y, ⁅Y, X⁆⁆) :=
  bchQuotient_three (Fin 2) _ _

end BCHElement

end TauCeti.FreeLieAlgebra
