/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.VecNotation
public import TauCeti.Algebra.Lie.Free.Enveloping
public import TauCeti.Algebra.Lie.UniversalEnveloping.Completion.Primitive
public import TauCeti.RingTheory.Ideal.Quotient.Nilpotent
public import TauCeti.RingTheory.Nilpotent.BCH

/-!
# The universal Baker–Campbell–Hausdorff product and element

For `F = FreeLieAlgebra ℚ S` graded by word length over `PositiveDegrees.naturals` with enveloping
augmentation ideal `J`, the degree ideals agree with the lower central series of `F` and the
enveloping degree filtration agrees with `J ^ k`. Combining
`AlgFiltration.isCompletedGroupLike_completedExp_iff`,
`AlgFiltration.isCompletedPrimitive_completedLog_iff`, and
`UniversalEnvelopingAlgebra.completedPrimitiveLieEquiv` produces the Baker–Campbell–Hausdorff
product `bchQuotient S c x y` on `F ⧸ LieModule.lowerCentralSeries ℚ F F c`, uniquely characterized
by `exp (ι_c (bchQuotient S c x y)) = exp (ι_c x) * exp (ι_c y)` in `U(F) ⧸ J ^ (c + 1)`.
Specializing `S = Fin 2` at `X = of ℚ 0` and `Y = of ℚ 1` defines the universal
Baker–Campbell–Hausdorff element `bchElement c`.

## Main definitions

* `TauCeti.FreeLieAlgebra.bchQuotient`: the Baker–Campbell–Hausdorff product on
  `FreeLieAlgebra ℚ S ⧸ LieModule.lowerCentralSeries ℚ _ _ c`.
* `TauCeti.FreeLieAlgebra.bchElement`: the universal Baker–Campbell–Hausdorff element of class `c`.

## Main results

* `TauCeti.FreeLieAlgebra.lowerCentralQuotientι_bchQuotient`,
  `TauCeti.FreeLieAlgebra.exp_lowerCentralQuotientι_bchQuotient`, and
  `TauCeti.FreeLieAlgebra.eq_bchQuotient_iff`: logarithm formula, exponential law, and uniqueness.
* `TauCeti.FreeLieAlgebra.exists_exp_ι_eq_exp_mul_exp`: in `U(F) ⧸ J ^ (c + 1)`, a product of
  exponentials of Lie elements is the exponential of a Lie element.
* `TauCeti.FreeLieAlgebra.bchQuotient_assoc`,
  `TauCeti.FreeLieAlgebra.map_bchQuotient_of_lowerCentralQuotientι`,
  `TauCeti.FreeLieAlgebra.factor_bchQuotient`, `TauCeti.FreeLieAlgebra.mapQ_bchQuotient`, and
  `TauCeti.FreeLieAlgebra.mapQ_lift_bchElement`: group laws, functoriality, and evaluation of
  `bchElement`.
* `TauCeti.FreeLieAlgebra.exp_lowerCentralQuotientι_bchElement`,
  `TauCeti.FreeLieAlgebra.eq_bchElement_iff`,
  `TauCeti.FreeLieAlgebra.lowerCentralQuotientι_bchElement`,
  `TauCeti.FreeLieAlgebra.factor_bchElement`, and `TauCeti.FreeLieAlgebra.bchElement_three`:
  characterization, compatibility across classes, and explicit formulas through degree three.

## References

* C. Reutenauer, *Free Lie Algebras*, Oxford University Press (1993), §3.1.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters 1–3, Springer (1989), Chapter II, §6.
-/

public section

namespace TauCeti.FreeLieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

section BCHQuotient

variable (S : Type*)

local notation "F" => _root_.FreeLieAlgebra ℚ S
local notation "U" => _root_.UniversalEnvelopingAlgebra ℚ F
local notation "J" => HopfIdeal.toIdeal (HopfIdeal.augmentation ℚ U)
local notation "ℒ" => homogeneousSubmodule ℚ S
local notation "δ" => PositiveDegrees.naturals
local notation "LCS" => LieModule.lowerCentralSeries ℚ F F
local notation "ι" => _root_.UniversalEnvelopingAlgebra.ι ℚ
local notation "ι_c" => UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F

private noncomputable abbrev freeFiltration : AlgFiltration U :=
  UniversalEnvelopingAlgebra.degreeFiltration ℒ PositiveDegrees.naturals.degree
    (fun n hn => PositiveDegrees.naturals.eq_bot_of_degree_nonpos ℒ n hn.le)

private noncomputable def completedGeneratorExp (w : F) : (freeFiltration S).completion :=
  (freeFiltration S).completedExp
    ⟨UniversalEnvelopingAlgebra.completedLieToU ℒ δ
      (LieIdeal.toCompletion ((δ).degreeIdeal ℒ) ((δ).degreeIdeal_antitone ℒ) w),
     UniversalEnvelopingAlgebra.completedLieToU_mem_completionIdeal_one ℒ δ _⟩

private theorem isCompletedGroupLike_completedGeneratorExp (w : F) :
    (freeFiltration S).IsCompletedGroupLike ℚ (completedGeneratorExp S w) :=
  ((freeFiltration S).isCompletedGroupLike_completedExp_iff ℚ _).mpr
    (UniversalEnvelopingAlgebra.isCompletedPrimitive_completedLieToU ℒ δ _)

private theorem completedGeneratorExp_mul_sub_one_mem (x₀ y₀ : F) :
    completedGeneratorExp S x₀ * completedGeneratorExp S y₀ - 1 ∈
      (freeFiltration S).completionIdeal 1 :=
  ((isCompletedGroupLike_completedGeneratorExp S x₀).mul
    (isCompletedGroupLike_completedGeneratorExp S y₀)).sub_one_mem
    (UniversalEnvelopingAlgebra.ker_counitAlgHom_le_degreeFiltration_one_of_isPositiveGrading ℒ δ)

private noncomputable def completedBCHOfElem (x₀ y₀ : F) : (δ).completedLie ℒ :=
  (UniversalEnvelopingAlgebra.completedPrimitiveLieEquiv ℚ ℒ δ).symm
    ⟨(freeFiltration S).completedLog ⟨_, completedGeneratorExp_mul_sub_one_mem S x₀ y₀⟩,
     (UniversalEnvelopingAlgebra.mem_completedPrimitives_iff ℒ (δ).degree _).mpr <|
       ((freeFiltration S).isCompletedPrimitive_completedLog_iff ℚ _).mpr
         ((isCompletedGroupLike_completedGeneratorExp S x₀).mul
           (isCompletedGroupLike_completedGeneratorExp S y₀))⟩

private theorem lowerCentralQuotientι_quotEquiv (c : ℕ) (z : (δ).truncatedLie ℒ c) :
    ι_c c (((δ).degreeIdeal ℒ c).quotEquivOfEq _
        (naturals_degreeIdeal_eq_lowerCentralSeries ℚ S c) z) =
      Ideal.quotEquivOfEq (naturals_degreeFiltration_eq_augmentation_pow ℚ S (c + 1))
        (UniversalEnvelopingAlgebra.truncatedLieToU ℒ δ c z) := by
  obtain ⟨w, rfl⟩ := LieIdeal.surjective_mkQ ((δ).degreeIdeal ℒ c) z; simp [LieIdeal.mkQ_apply]

private theorem quotEquivOfEq_projection_completedGeneratorExp (c : ℕ) (w : F) :
    Ideal.quotEquivOfEq (naturals_degreeFiltration_eq_augmentation_pow ℚ S (c + 1))
        ((freeFiltration S).projection c (completedGeneratorExp S w)) =
      IsNilpotent.exp (ι_c c ((LCS c).mkQ w)) := by
  rw [completedGeneratorExp, AlgFiltration.projection_completedExp, IsNilpotent.map_exp
    ((freeFiltration S).isNilpotent_projection
      (UniversalEnvelopingAlgebra.completedLieToU_mem_completionIdeal_one ℒ δ _) c) _]
  congr 1
  simp [UniversalEnvelopingAlgebra.completedLieToU_toCompletion]

private theorem truncatedLieToU_completionProjection_completedBCHOfElem (c : ℕ) (x₀ y₀ : F) :
    UniversalEnvelopingAlgebra.truncatedLieToU ℒ δ c
        (LieIdeal.completionProjection ((δ).degreeIdeal ℒ) ((δ).degreeIdeal_antitone ℒ) c
          (completedBCHOfElem S x₀ y₀)) =
      IsNilpotent.log ((freeFiltration S).projection c
        (completedGeneratorExp S x₀ * completedGeneratorExp S y₀)) := by
  rw [← UniversalEnvelopingAlgebra.projection_completedLieToU, completedBCHOfElem,
    UniversalEnvelopingAlgebra.completedLieToU_completedPrimitiveLieEquiv_symm, Subtype.coe_mk,
    AlgFiltration.projection_completedLog]

/-- The Baker–Campbell–Hausdorff product on `FreeLieAlgebra ℚ S ⧸ lowerCentralSeries ℚ _ _ c`,
obtained by projecting the completed logarithm of `exp x * exp y` from the completed enveloping
algebra. -/
noncomputable def bchQuotient (c : ℕ) (x y : F ⧸ LCS c) : F ⧸ LCS c :=
  (((δ).degreeIdeal ℒ c).quotEquivOfEq _ (naturals_degreeIdeal_eq_lowerCentralSeries ℚ S c))
    (LieIdeal.completionProjection ((δ).degreeIdeal ℒ) ((δ).degreeIdeal_antitone ℒ) c
      (completedBCHOfElem S (LieIdeal.surjective_mkQ (LCS c) x).choose
        (LieIdeal.surjective_mkQ (LCS c) y).choose))

/-- For `x, y` in the free nilpotent quotient of class `c`, `exp (ι_c x) * exp (ι_c y) - 1` is
nilpotent in `U(F) ⧸ J ^ (c + 1)`. -/
theorem isNilpotent_exp_mul_exp_sub_one_lowerCentralQuotientι (c : ℕ) (x y : F ⧸ LCS c) :
    IsNilpotent (IsNilpotent.exp (ι_c c x) * IsNilpotent.exp (ι_c c y) - 1) :=
  ⟨c + 1, (Ideal.map (Ideal.Quotient.mk ((J) ^ (c + 1))) (J)).exp_mul_exp_sub_one_pow_eq_zero
    (Ideal.map_quotient_mk_pow_eq_bot (J) (c + 1))
    (UniversalEnvelopingAlgebra.lowerCentralQuotientι_mem_map_augmentation ℚ F c x)
    (UniversalEnvelopingAlgebra.lowerCentralQuotientι_mem_map_augmentation ℚ F c y)⟩

/-- Mapping `bchQuotient S c x y` into `U(F) ⧸ J ^ (c + 1)` computes
`log (exp (ι_c x) * exp (ι_c y))`. -/
theorem lowerCentralQuotientι_bchQuotient (c : ℕ) (x y : F ⧸ LCS c) :
    ι_c c (bchQuotient S c x y) =
      IsNilpotent.log (IsNilpotent.exp (ι_c c x) * IsNilpotent.exp (ι_c c y)) := by
  let x₀ := (LieIdeal.surjective_mkQ (LCS c) x).choose
  let y₀ := (LieIdeal.surjective_mkQ (LCS c) y).choose
  have hx₀ : (LCS c).mkQ x₀ = x := (LieIdeal.surjective_mkQ (LCS c) x).choose_spec
  have hy₀ : (LCS c).mkQ y₀ = y := (LieIdeal.surjective_mkQ (LCS c) y).choose_spec
  have hnil : IsNilpotent ((freeFiltration S).projection c
      (completedGeneratorExp S x₀ * completedGeneratorExp S y₀) - 1) := by
    simpa only [map_sub, map_one] using
      (freeFiltration S).isNilpotent_projection (completedGeneratorExp_mul_sub_one_mem S x₀ y₀) c
  rw [bchQuotient, lowerCentralQuotientι_quotEquiv,
    truncatedLieToU_completionProjection_completedBCHOfElem, IsNilpotent.map_log hnil]
  simp [quotEquivOfEq_projection_completedGeneratorExp, hx₀, hy₀]

/-- **Exponential law for `bchQuotient`:** exponentiating the image of `bchQuotient S c x y` in
`U(F) ⧸ J ^ (c + 1)` recovers `exp (ι_c x) * exp (ι_c y)`. -/
@[simp] theorem exp_lowerCentralQuotientι_bchQuotient (c : ℕ) (x y : F ⧸ LCS c) :
    IsNilpotent.exp (ι_c c (bchQuotient S c x y)) =
      IsNilpotent.exp (ι_c c x) * IsNilpotent.exp (ι_c c y) := by
  rw [lowerCentralQuotientι_bchQuotient,
    IsNilpotent.exp_log (isNilpotent_exp_mul_exp_sub_one_lowerCentralQuotientι S c x y)]

/-- `bchQuotient S c x y` is the unique element of the free nilpotent quotient whose exponential in
`U(F) ⧸ J ^ (c + 1)` equals `exp (ι_c x) * exp (ι_c y)`. -/
theorem eq_bchQuotient_iff {c : ℕ} {x y z : F ⧸ LCS c} :
    z = bchQuotient S c x y ↔
      IsNilpotent.exp (ι_c c z) = IsNilpotent.exp (ι_c c x) * IsNilpotent.exp (ι_c c y) := by
  refine ⟨fun h => h ▸ exp_lowerCentralQuotientι_bchQuotient S c x y,
    fun h => lowerCentralQuotientι_injective_of_ratAlgebra ℚ S c ?_⟩
  rw [lowerCentralQuotientι_bchQuotient, ← h,
    IsNilpotent.log_exp (UniversalEnvelopingAlgebra.isNilpotent_lowerCentralQuotientι ℚ F c z)]

/-- In the enveloping algebra of a free Lie algebra over `ℚ`, truncated at the `(c + 1)`-st power
of the augmentation ideal, a product of the exponentials of two Lie elements is the exponential of
a Lie element. -/
theorem exists_exp_ι_eq_exp_mul_exp (c : ℕ) (x y : F) :
    ∃ b : F, IsNilpotent.exp (Ideal.Quotient.mk ((J) ^ (c + 1)) (ι b)) =
      IsNilpotent.exp (Ideal.Quotient.mk ((J) ^ (c + 1)) (ι x)) *
        IsNilpotent.exp (Ideal.Quotient.mk ((J) ^ (c + 1)) (ι y)) := by
  obtain ⟨b, hb⟩ := LieIdeal.surjective_mkQ (LCS c)
    (bchQuotient S c (LieSubmodule.Quotient.mk x) (LieSubmodule.Quotient.mk y))
  refine ⟨b, ?_⟩
  simpa only [← hb, LieIdeal.mkQ_apply, UniversalEnvelopingAlgebra.lowerCentralQuotientι_mk] using
    exp_lowerCentralQuotientι_bchQuotient S c
      (LieSubmodule.Quotient.mk x) (LieSubmodule.Quotient.mk y)

/-- The Baker–Campbell–Hausdorff operation on `F ⧸ lowerCentralSeries ℚ F F c` is associative. -/
theorem bchQuotient_assoc (c : ℕ) (x y z : F ⧸ LCS c) :
    bchQuotient S c (bchQuotient S c x y) z = bchQuotient S c x (bchQuotient S c y z) := by
  rw [eq_bchQuotient_iff, exp_lowerCentralQuotientι_bchQuotient,
    exp_lowerCentralQuotientι_bchQuotient, mul_assoc, ← exp_lowerCentralQuotientι_bchQuotient]

/-- Zero is a left identity for `bchQuotient`. -/
@[simp] theorem bchQuotient_zero_left (c : ℕ) (x : F ⧸ LCS c) : bchQuotient S c 0 x = x := by
  symm; rw [eq_bchQuotient_iff, map_zero, IsNilpotent.exp_zero, one_mul]

/-- Zero is a right identity for `bchQuotient`. -/
@[simp] theorem bchQuotient_zero_right (c : ℕ) (x : F ⧸ LCS c) : bchQuotient S c x 0 = x := by
  symm; rw [eq_bchQuotient_iff, map_zero, IsNilpotent.exp_zero, mul_one]

/-- Negation is a left inverse for `bchQuotient`. -/
@[simp] theorem bchQuotient_neg_left (c : ℕ) (x : F ⧸ LCS c) : bchQuotient S c (-x) x = 0 := by
  symm; rw [eq_bchQuotient_iff, map_zero, map_neg, IsNilpotent.exp_zero]
  exact (IsNilpotent.exp_neg_mul_exp_self
    (UniversalEnvelopingAlgebra.isNilpotent_lowerCentralQuotientι ℚ F c x)).symm

/-- Negation is a right inverse for `bchQuotient`. -/
@[simp] theorem bchQuotient_neg_right (c : ℕ) (x : F ⧸ LCS c) : bchQuotient S c x (-x) = 0 := by
  symm; rw [eq_bchQuotient_iff, map_zero, map_neg, IsNilpotent.exp_zero]
  exact (IsNilpotent.exp_mul_exp_neg_self
    (UniversalEnvelopingAlgebra.isNilpotent_lowerCentralQuotientι ℚ F c x)).symm

/-- Commuting elements in `F ⧸ lowerCentralSeries ℚ F F c` have `bchQuotient` equal to `x + y`. -/
theorem bchQuotient_of_lie_eq_zero (c : ℕ) {x y : F ⧸ LCS c} (hxy : ⁅x, y⁆ = 0) :
    bchQuotient S c x y = x + y := by
  symm; rw [eq_bchQuotient_iff, map_add]
  have hlie := congrArg (ι_c c) hxy
  rw [LieHom.map_lie, map_zero, Ring.lie_def, sub_eq_zero] at hlie
  exact IsNilpotent.exp_add_of_commute hlie
    (UniversalEnvelopingAlgebra.isNilpotent_lowerCentralQuotientι ℚ F c x)
    (UniversalEnvelopingAlgebra.isNilpotent_lowerCentralQuotientι ℚ F c y)

/-- Any map between free lower-central quotients that intertwines `lowerCentralQuotientι` with a
ring homomorphism on the truncated enveloping algebras preserves `bchQuotient`. -/
theorem map_bchQuotient_of_lowerCentralQuotientι {T : Type*} {c d : ℕ}
    {Φ : Type*} [FunLike Φ (U ⧸ (J) ^ (c + 1))
      (_root_.UniversalEnvelopingAlgebra ℚ (_root_.FreeLieAlgebra ℚ T) ⧸
        (HopfIdeal.augmentation ℚ
          (_root_.UniversalEnvelopingAlgebra ℚ (_root_.FreeLieAlgebra ℚ T))).toIdeal ^ (d + 1))]
    [RingHomClass Φ _ _] (φ : Φ)
    (g : F ⧸ LCS c →
      _root_.FreeLieAlgebra ℚ T ⧸
        LieModule.lowerCentralSeries ℚ (_root_.FreeLieAlgebra ℚ T) (_root_.FreeLieAlgebra ℚ T) d)
    (hg : ∀ z,
      UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ (_root_.FreeLieAlgebra ℚ T) d (g z) =
        φ (ι_c c z))
    (x y : F ⧸ LCS c) :
    g (bchQuotient S c x y) = bchQuotient T d (g x) (g y) := by
  rw [eq_bchQuotient_iff, hg, hg, hg]
  have hnil := UniversalEnvelopingAlgebra.isNilpotent_lowerCentralQuotientι ℚ F c
  rw [← IsNilpotent.map_exp (hnil _) φ, ← IsNilpotent.map_exp (hnil x) φ,
    ← IsNilpotent.map_exp (hnil y) φ, exp_lowerCentralQuotientι_bchQuotient, map_mul]

/-- `bchQuotient` commutes with the lower-central truncation transitions `LieIdeal.factor`. -/
@[simp] theorem factor_bchQuotient {c d : ℕ} (h : c ≤ d) (x y : F ⧸ LCS d) :
    LieIdeal.factor (LieModule.antitone_lowerCentralSeries ℚ F F h) (bchQuotient S d x y) =
      bchQuotient S c (LieIdeal.factor (LieModule.antitone_lowerCentralSeries ℚ F F h) x)
        (LieIdeal.factor (LieModule.antitone_lowerCentralSeries ℚ F F h) y) :=
  map_bchQuotient_of_lowerCentralQuotientι S
    (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := (J)) (Nat.add_le_add_right h 1))) _
    (UniversalEnvelopingAlgebra.lowerCentralQuotientι_factor ℚ F h) x y

/-- `bchQuotient` is natural along any Lie homomorphism between free Lie algebras over `ℚ`. -/
theorem mapQ_bchQuotient {T : Type*} (f : F →ₗ⁅ℚ⁆ _root_.FreeLieAlgebra ℚ T) (c : ℕ)
    (hf : LCS c ≤ LieIdeal.comap f (LieModule.lowerCentralSeries ℚ (_root_.FreeLieAlgebra ℚ T)
        (_root_.FreeLieAlgebra ℚ T) c) :=
      LieIdeal.map_le_iff_le_comap.mp (LieIdeal.map_lowerCentralSeries_le c))
    (x y : F ⧸ LCS c) :
    LieIdeal.mapQ (LCS c) _ f hf (bchQuotient S c x y) =
      bchQuotient T c (LieIdeal.mapQ (LCS c) _ f hf x) (LieIdeal.mapQ (LCS c) _ f hf y) :=
  map_bchQuotient_of_lowerCentralQuotientι S
    (Ideal.quotientMapₐ _ (UniversalEnvelopingAlgebra.map ℚ f)
      (UniversalEnvelopingAlgebra.augmentation_toIdeal_pow_le_comap_map ℚ f (c + 1))) _
    (UniversalEnvelopingAlgebra.lowerCentralQuotientι_mapQ ℚ f c hf) x y

/-- At nilpotency class zero, `bchQuotient` vanishes. -/
@[simp] theorem bchQuotient_zero (x y : F ⧸ LCS 0) : bchQuotient S 0 x y = 0 := by
  obtain ⟨z, hz⟩ := LieIdeal.surjective_mkQ (LCS 0) (bchQuotient S 0 x y)
  rw [← hz, LieIdeal.mkQ_apply, LieSubmodule.Quotient.mk_eq_zero']; simp

/-- At nilpotency class one (abelianization), `bchQuotient` is addition. -/
theorem bchQuotient_one (x y : F ⧸ LCS 1) : bchQuotient S 1 x y = x + y := by
  apply bchQuotient_of_lie_eq_zero
  obtain ⟨x₀, rfl⟩ := LieIdeal.surjective_mkQ (LCS 1) x
  obtain ⟨y₀, rfl⟩ := LieIdeal.surjective_mkQ (LCS 1) y
  rw [LieIdeal.mkQ_apply, LieIdeal.mkQ_apply, ← LieSubmodule.Quotient.mk_bracket,
    LieSubmodule.Quotient.mk_eq_zero', LieModule.lowerCentralSeries_succ]
  exact LieSubmodule.lie_mem_lie trivial trivial

/-- At nilpotency class two, `bchQuotient` is `x + y + (1 / 2) • ⁅x, y⁆`. -/
theorem bchQuotient_two (x y : F ⧸ LCS 2) :
    bchQuotient S 2 x y = x + y + (1 / 2 : ℚ) • ⁅x, y⁆ := by
  apply lowerCentralQuotientι_injective_of_ratAlgebra ℚ S 2
  rw [lowerCentralQuotientι_bchQuotient, Ideal.log_exp_mul_exp_of_pow_three_eq_bot _
    (Ideal.map_quotient_mk_pow_eq_bot (J) 3)
    (UniversalEnvelopingAlgebra.lowerCentralQuotientι_mem_map_augmentation ℚ F 2 x)
    (UniversalEnvelopingAlgebra.lowerCentralQuotientι_mem_map_augmentation ℚ F 2 y)]
  simp [map_add, map_smul, LieHom.map_lie]

/-- At nilpotency class three, `bchQuotient` is
`x + y + (1 / 2) • ⁅x, y⁆ + (1 / 12) • (⁅x, ⁅x, y⁆⁆ + ⁅y, ⁅y, x⁆⁆)`. -/
theorem bchQuotient_three (x y : F ⧸ LCS 3) : bchQuotient S 3 x y =
    x + y + (1 / 2 : ℚ) • ⁅x, y⁆ + (1 / 12 : ℚ) • (⁅x, ⁅x, y⁆⁆ + ⁅y, ⁅y, x⁆⁆) := by
  apply lowerCentralQuotientι_injective_of_ratAlgebra ℚ S 3
  rw [lowerCentralQuotientι_bchQuotient, Ideal.log_exp_mul_exp_of_pow_four_eq_bot _
    (Ideal.map_quotient_mk_pow_eq_bot (J) 4)
    (UniversalEnvelopingAlgebra.lowerCentralQuotientι_mem_map_augmentation ℚ F 3 x)
    (UniversalEnvelopingAlgebra.lowerCentralQuotientι_mem_map_augmentation ℚ F 3 y)]
  simp [map_add, map_smul, LieHom.map_lie]

end BCHQuotient

section BCHElement

local notation "F₂" => _root_.FreeLieAlgebra ℚ (Fin 2)
local notation "U₂" => _root_.UniversalEnvelopingAlgebra ℚ F₂
local notation "J₂" => HopfIdeal.toIdeal (HopfIdeal.augmentation ℚ U₂)
local notation "LCS₂" => LieModule.lowerCentralSeries ℚ F₂ F₂
local notation "X₀" => _root_.FreeLieAlgebra.of ℚ (0 : Fin 2)
local notation "Y₀" => _root_.FreeLieAlgebra.of ℚ (1 : Fin 2)
local notation "ι₂" => _root_.UniversalEnvelopingAlgebra.ι ℚ
local notation "ι₂_c" => UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F₂

/-- The universal Baker–Campbell–Hausdorff element of nilpotency class `c`, evaluated at the two
free generators `X = FreeLieAlgebra.of ℚ 0` and `Y = FreeLieAlgebra.of ℚ 1`. -/
noncomputable def bchElement (c : ℕ) : F₂ ⧸ LCS₂ c :=
  bchQuotient (Fin 2) c (LieSubmodule.Quotient.mk X₀) (LieSubmodule.Quotient.mk Y₀)

/-- Unfolded definition of `bchElement c` as `bchQuotient (Fin 2) c` on the two free generators. -/
theorem bchElement_def (c : ℕ) : bchElement c =
    bchQuotient (Fin 2) c (LieSubmodule.Quotient.mk X₀) (LieSubmodule.Quotient.mk Y₀) := (rfl)

/-- Evaluating `bchElement c` along `FreeLieAlgebra.lift ℚ ![x₀, y₀]` recovers `bchQuotient S c`
on the classes of `x₀` and `y₀`. -/
theorem mapQ_lift_bchElement {S : Type*} (c : ℕ) (x₀ y₀ : _root_.FreeLieAlgebra ℚ S)
    (hf : LCS₂ c ≤ LieIdeal.comap (_root_.FreeLieAlgebra.lift ℚ ![x₀, y₀])
        (LieModule.lowerCentralSeries ℚ (_root_.FreeLieAlgebra ℚ S)
          (_root_.FreeLieAlgebra ℚ S) c) :=
      LieIdeal.map_le_iff_le_comap.mp (LieIdeal.map_lowerCentralSeries_le c)) :
    LieIdeal.mapQ (LCS₂ c) _ (_root_.FreeLieAlgebra.lift ℚ ![x₀, y₀]) hf (bchElement c) =
      bchQuotient S c (LieSubmodule.Quotient.mk x₀) (LieSubmodule.Quotient.mk y₀) := by
  simp [bchElement_def, mapQ_bchQuotient, LieIdeal.mapQ_apply]

/-- Mapping `bchElement c` into `U(F₂) ⧸ J₂ ^ (c + 1)` computes `log (exp (ι X) * exp (ι Y))`. -/
theorem lowerCentralQuotientι_bchElement (c : ℕ) : ι₂_c c (bchElement c) =
    IsNilpotent.log (IsNilpotent.exp (Ideal.Quotient.mk ((J₂) ^ (c + 1)) (ι₂ X₀)) *
      IsNilpotent.exp (Ideal.Quotient.mk ((J₂) ^ (c + 1)) (ι₂ Y₀))) := by
  simpa only [bchElement, UniversalEnvelopingAlgebra.lowerCentralQuotientι_mk] using
    lowerCentralQuotientι_bchQuotient (Fin 2) c
      (LieSubmodule.Quotient.mk X₀) (LieSubmodule.Quotient.mk Y₀)

/-- Exponentiating the image of `bchElement c` in `U(F₂) ⧸ J₂ ^ (c + 1)` recovers
`exp (ι X) * exp (ι Y)`. -/
@[simp] theorem exp_lowerCentralQuotientι_bchElement (c : ℕ) :
    IsNilpotent.exp (ι₂_c c (bchElement c)) =
      IsNilpotent.exp (Ideal.Quotient.mk ((J₂) ^ (c + 1)) (ι₂ X₀)) *
        IsNilpotent.exp (Ideal.Quotient.mk ((J₂) ^ (c + 1)) (ι₂ Y₀)) := by
  simpa only [bchElement, UniversalEnvelopingAlgebra.lowerCentralQuotientι_mk] using
    exp_lowerCentralQuotientι_bchQuotient (Fin 2) c
      (LieSubmodule.Quotient.mk X₀) (LieSubmodule.Quotient.mk Y₀)

/-- The Baker–Campbell–Hausdorff element is the unique element of the free nilpotent Lie algebra
whose image `b` in the truncated enveloping algebra satisfies `exp b = exp X * exp Y`. -/
theorem eq_bchElement_iff {c : ℕ} {z : F₂ ⧸ LCS₂ c} :
    z = bchElement c ↔
      IsNilpotent.exp (ι₂_c c z) = IsNilpotent.exp (Ideal.Quotient.mk ((J₂) ^ (c + 1)) (ι₂ X₀)) *
        IsNilpotent.exp (Ideal.Quotient.mk ((J₂) ^ (c + 1)) (ι₂ Y₀)) := by
  simpa only [bchElement, UniversalEnvelopingAlgebra.lowerCentralQuotientι_mk] using
    eq_bchQuotient_iff (Fin 2)
      (x := LieSubmodule.Quotient.mk X₀) (y := LieSubmodule.Quotient.mk Y₀) (z := z)

/-- The elements `bchElement c` form a compatible family in the lower-central tower. -/
@[simp] theorem factor_bchElement {c d : ℕ} (h : c ≤ d) :
    LieIdeal.factor (LieModule.antitone_lowerCentralSeries ℚ F₂ F₂ h) (bchElement d) =
      bchElement c := by simp [bchElement, factor_bchQuotient (Fin 2) h]

/-- At nilpotency class zero, `bchElement 0` is zero. -/
@[simp] theorem bchElement_zero : bchElement 0 = 0 := bchQuotient_zero (Fin 2) _ _

/-- At nilpotency class one, `bchElement 1` is `X + Y`. -/
theorem bchElement_one : bchElement 1 = LieSubmodule.Quotient.mk (X₀ + Y₀) := by
  simpa [bchElement_def] using
    bchQuotient_one (Fin 2) (LieSubmodule.Quotient.mk X₀) (LieSubmodule.Quotient.mk Y₀)

/-- At nilpotency class two, `bchElement 2` is `X + Y + (1 / 2) • ⁅X, Y⁆`. -/
theorem bchElement_two :
    bchElement 2 = LieSubmodule.Quotient.mk (X₀ + Y₀ + (1 / 2 : ℚ) • ⁅X₀, Y₀⁆) := by
  simpa [bchElement_def, LieSubmodule.Quotient.mk_bracket] using
    bchQuotient_two (Fin 2) (LieSubmodule.Quotient.mk X₀) (LieSubmodule.Quotient.mk Y₀)

/-- **The Baker–Campbell–Hausdorff element through degree three**: the element of class three is
`X + Y + ½ ⁅X, Y⁆ + 1/12 (⁅X, ⁅X, Y⁆⁆ + ⁅Y, ⁅Y, X⁆⁆)`. -/
theorem bchElement_three :
    bchElement 3 = LieSubmodule.Quotient.mk (X₀ + Y₀ + (1 / 2 : ℚ) • ⁅X₀, Y₀⁆ +
      (1 / 12 : ℚ) • (⁅X₀, ⁅X₀, Y₀⁆⁆ + ⁅Y₀, ⁅Y₀, X₀⁆⁆)) := by
  simpa [bchElement_def, LieSubmodule.Quotient.mk_bracket] using
    bchQuotient_three (Fin 2) (LieSubmodule.Quotient.mk X₀) (LieSubmodule.Quotient.mk Y₀)

end BCHElement

end TauCeti.FreeLieAlgebra
