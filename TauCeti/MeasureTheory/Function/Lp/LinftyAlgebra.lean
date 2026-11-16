/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import TauCeti.MeasureTheory.Function.Lp.Indicator
public import TauCeti.MeasureTheory.Function.Lp.One
public import TauCeti.MeasureTheory.Function.Lp.Star
import TauCeti.MeasureTheory.Function.Lp.Const

/-!
# `L∞` as a normed algebra and a C⋆-algebra

For a normed ring `R`, the space `L∞(μ, R) = Lp R ∞ μ` of essentially bounded classes is a normed
ring under pointwise multiplication, on an arbitrary measure space. The product is Mathlib's
Hölder product `f • g` at the exponents `∞, ∞, ∞`, and the unit is the class of the constant
function one. It is commutative when `R` is, a normed algebra over `𝕜` when `R` is, and a star
ring with the pointwise involution when `R` is a normed star ring. When `R` is a C⋆-ring, so is
`L∞(μ, R)`: the essential supremum of `‖f‖ ^ 2` is the square of the essential supremum of `‖f‖`.

Consequently `L∞(μ, A)` is a (commutative) C⋆-algebra whenever `A` is. In particular
`Lp ℂ ∞ μ` is a commutative C⋆-algebra, so Mathlib's Gelfand duality
`gelfandStarTransform (Lp ℂ ∞ μ)` identifies it isometrically, as a C⋆-algebra, with the
continuous functions on its character space. When `μ ≠ 0`, `L∞(μ, R)` is nontrivial if `R` is,
and its unit has norm one if that of `R` does. Over a Dirac measure `Measure.dirac x₀`, every
element of `Lp 𝕜 ∞ (Measure.dirac x₀)` is a scalar in the image of `algebraMap`.

The unit indicator of any measurable set `s`, represented in `L∞(μ, R)` by
`TauCeti.linftyIndicator μ R s hs`, is an idempotent (and a star projection when `R` is a normed
star ring), with multiplication corresponding to intersection of sets. Over a normed ring `R`
without zero divisors, these measurable-set indicators exhaust all idempotents of `Lp R ∞ μ`.

The instances follow Mathlib's corresponding instances on the space `lp B ∞` of bounded families
(`lp.inftyNormedRing`, `lp.inftyNormedAlgebra`, `lp.inftyStarRing`, `lp.inftyCStarRing`), with
almost everywhere equalities in place of pointwise ones.

## Main declarations

* `MeasureTheory.Lp.smul_eq_mul`: the product is the Hölder product at exponents `∞, ∞, ∞`.
* `MeasureTheory.Lp.coeFn_mul`: the product is pointwise almost everywhere.
* `MeasureTheory.Lp.coeFn_algebraMap`: scalars act as almost everywhere constant classes.
* `MeasureTheory.Lp.exists_eq_algebraMap_dirac`: over a Dirac measure, every element of `L∞` is
  a scalar in the image of `algebraMap`.
* `TauCeti.linftyIndicator_mul_linftyIndicator`, `TauCeti.isStarProjection_linftyIndicator`:
  algebraic and star properties of measurable-set indicators in `L∞`.
* `MeasureTheory.Lp.exists_measurableSet_eq_linftyIndicator_of_isIdempotentElem`: over a normed
  ring without zero divisors, every idempotent in `Lp R ∞ μ` is the unit indicator of a measurable
  set.
* The instances `NormedRing`, `NormedCommRing`, `NormedAlgebra`, `StarRing`, `CStarRing`,
  `CStarAlgebra` and `CommCStarAlgebra` on `Lp R ∞ μ`.
-/

public section

noncomputable section

open scoped ENNReal

namespace MeasureTheory.Lp

variable {α R 𝕜 : Type*} {m : MeasurableSpace α} {μ : Measure α}

section NormedRing

variable [NormedRing R]

/-- Pointwise multiplication on `L∞(μ, R)`, given by the Hölder product at exponents
`∞, ∞, ∞`. -/
instance inftyMul : Mul (Lp R ∞ μ) where
  mul f g := f • g

/-- The product on `L∞` is Mathlib's Hölder product at exponents `∞, ∞, ∞`. -/
@[simp]
protected theorem smul_eq_mul (f g : Lp R ∞ μ) : f • g = f * g :=
  rfl

theorem coeFn_mul (f g : Lp R ∞ μ) : ⇑(f * g) =ᵐ[μ] ⇑f * ⇑g :=
  coeFn_lpSMul f g

instance inftyRing : Ring (Lp R ∞ μ) where
  mul_assoc f g h := by
    ext
    filter_upwards [coeFn_mul (f * g) h, coeFn_mul f g, coeFn_mul f (g * h), coeFn_mul g h]
      with x h₁ h₂ h₃ h₄
    simp [h₁, h₂, h₃, h₄, mul_assoc]
  one_mul f := by
    ext
    filter_upwards [coeFn_mul 1 f, coeFn_one (E := R) (μ := μ)] with x h₁ h₂
    simp [h₁, h₂]
  mul_one f := by
    ext
    filter_upwards [coeFn_mul f 1, coeFn_one (E := R) (μ := μ)] with x h₁ h₂
    simp [h₁, h₂]
  left_distrib := Lp.add_smul
  right_distrib := Lp.smul_add
  zero_mul := Lp.zero_smul R ∞
  mul_zero := Lp.smul_zero R ∞

theorem coeFn_pow (f : Lp R ∞ μ) (n : ℕ) : ⇑(f ^ n) =ᵐ[μ] ⇑f ^ n := by
  induction n with
  | zero => simpa using coeFn_one
  | succ n ih =>
    filter_upwards [coeFn_mul (f ^ n) f, ih] with x h₁ h₂
    simp [pow_succ, h₁, h₂]

instance inftyNormedRing : NormedRing (Lp R ∞ μ) where
  dist_eq := dist_eq_norm
  norm_mul_le := Lp.norm_smul_le

instance inftyNormOneClass [NormOneClass R] [NeZero μ] : NormOneClass (Lp R ∞ μ) where
  norm_one := by rw [norm_one_of_ne_zero (NeZero.ne μ), norm_one]

instance inftyNontrivial [Nontrivial R] [NeZero μ] : Nontrivial (Lp R ∞ μ) :=
  nontrivial_of_ne 1 0 fun h => by
    have h₁ := norm_one_of_ne_zero (E := R) (NeZero.ne μ)
    rw [h, norm_zero, eq_comm, norm_eq_zero] at h₁
    exact one_ne_zero h₁

end NormedRing

instance inftyNormedCommRing [NormedCommRing R] : NormedCommRing (Lp R ∞ μ) where
  mul_comm f g := by
    ext
    filter_upwards [coeFn_mul f g, coeFn_mul g f] with x h₁ h₂
    simp [h₁, h₂, mul_comm]

section NormedAlgebra

variable [NormedField 𝕜] [NormedRing R] [NormedAlgebra 𝕜 R]

instance inftyAlgebra : Algebra 𝕜 (Lp R ∞ μ) :=
  Algebra.ofModule Lp.smul_assoc fun c f g => (Lp.smul_comm c f g).symm

theorem coeFn_algebraMap (c : 𝕜) :
    ⇑(algebraMap 𝕜 (Lp R ∞ μ) c) =ᵐ[μ] fun _ => algebraMap 𝕜 R c := by
  filter_upwards [coeFn_smul c (1 : Lp R ∞ μ), coeFn_one (E := R) (μ := μ)] with x h₁ h₂
  simp [h₁, h₂, Algebra.algebraMap_eq_smul_one]

/-- The scalar embedding into L∞ is the class of the corresponding constant function. -/
theorem algebraMap_eq_const [IsFiniteMeasure μ] (c : 𝕜) :
    algebraMap 𝕜 (Lp R ∞ μ) c = Lp.const ∞ μ (algebraMap 𝕜 R c) := by
  ext
  exact (coeFn_algebraMap c).trans (coeFn_const ∞ μ (algebraMap 𝕜 R c)).symm

instance inftyNormedAlgebra : NormedAlgebra 𝕜 (Lp R ∞ μ) where
  norm_smul_le := norm_smul_le

end NormedAlgebra

/-- Over a Dirac measure `Measure.dirac x₀`, every element of `Lp 𝕜 ∞ (Measure.dirac x₀)` equals
a scalar in the image of `algebraMap` (with no singleton-measurability assumption on `α`). -/
theorem exists_eq_algebraMap_dirac [NormedField 𝕜] {x₀ : α} (a : Lp 𝕜 ∞ (Measure.dirac x₀)) :
    ∃ c : 𝕜, a = algebraMap 𝕜 (Lp 𝕜 ∞ (Measure.dirac x₀)) c :=
  (exists_eq_const_dirac a).imp fun c hc ↦ by
    simpa [algebraMap_eq_const (μ := Measure.dirac x₀) (𝕜 := 𝕜) (R := 𝕜) c] using hc

section StarRing

variable [NormedRing R] [StarRing R] [NormedStarGroup R]

instance inftyStarRing : StarRing (Lp R ∞ μ) where
  star_add := star_add
  star_mul f g := by
    ext
    filter_upwards [coeFn_star (f * g), coeFn_mul f g, coeFn_mul (star g) (star f),
      coeFn_star f, coeFn_star g] with x h₁ h₂ h₃ h₄ h₅
    simp [h₁, h₂, h₃, h₄, h₅]

/-- `L∞(μ, R)` satisfies the C⋆-identity `‖star f * f‖ = ‖f‖ * ‖f‖` when `R` does. -/
instance inftyCStarRing [CStarRing R] : CStarRing (Lp R ∞ μ) where
  norm_mul_self_le f := by
    have h : eLpNorm (⇑(star f * f)) ∞ μ = eLpNorm f ∞ μ ^ (2 : ℝ) := by
      have h₀ := eLpNorm_norm_rpow (p := ∞) (μ := μ) _ (Lp.aestronglyMeasurable f) two_pos
      rw [ENNReal.top_mul (by simp)] at h₀
      rw [← h₀]
      refine eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _)
        ((Lp.aestronglyMeasurable f).norm.aemeasurable.pow_const _).aestronglyMeasurable ?_
      filter_upwards [coeFn_mul (star f) f, coeFn_star f] with x h₁ h₂
      simp [h₁, h₂, CStarRing.norm_star_mul_self, sq]
    rw [norm_def (star f * f), h, ← ENNReal.toReal_rpow, Real.rpow_two, sq, norm_def]

end StarRing

instance inftyCStarAlgebra [CStarAlgebra R] : CStarAlgebra (Lp R ∞ μ) where

instance inftyCommCStarAlgebra [CommCStarAlgebra R] : CommCStarAlgebra (Lp R ∞ μ) where

section Idempotent

/-- Multiplying measurable-set unit indicators in `Lp R ∞ μ` intersects the underlying sets. -/
theorem _root_.TauCeti.linftyIndicator_mul_linftyIndicator [NormedRing R] {s t : Set α}
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    TauCeti.linftyIndicator μ R s hs * TauCeti.linftyIndicator μ R t ht =
      TauCeti.linftyIndicator μ R (s ∩ t) (hs.inter ht) := by
  apply Lp.ext
  filter_upwards [coeFn_mul (TauCeti.linftyIndicator μ R s hs) (TauCeti.linftyIndicator μ R t ht),
    TauCeti.coeFn_linftyIndicator (μ := μ) (R := R) hs,
    TauCeti.coeFn_linftyIndicator (μ := μ) (R := R) ht,
    TauCeti.coeFn_linftyIndicator (μ := μ) (R := R) (hs.inter ht)] with x hmul hsx htx hst
  rw [hmul, Pi.mul_apply, hsx, htx, hst]
  by_cases hxs : x ∈ s <;> by_cases hxt : x ∈ t <;> simp [hxs, hxt]

/-- If `s ⊆ t`, multiplying the unit indicator of `s` on the right by that of `t` fixes it. -/
theorem _root_.TauCeti.linftyIndicator_mul_linftyIndicator_of_subset_left [NormedRing R]
    {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : s ⊆ t) :
    TauCeti.linftyIndicator μ R s hs * TauCeti.linftyIndicator μ R t ht =
      TauCeti.linftyIndicator μ R s hs := by
  rw [TauCeti.linftyIndicator_mul_linftyIndicator]
  congr 1
  exact Set.inter_eq_self_of_subset_left hst

/-- If `t ⊆ s`, multiplying the unit indicator of `t` on the left by that of `s` fixes it. -/
theorem _root_.TauCeti.linftyIndicator_mul_linftyIndicator_of_subset_right [NormedRing R]
    {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t) (hts : t ⊆ s) :
    TauCeti.linftyIndicator μ R s hs * TauCeti.linftyIndicator μ R t ht =
      TauCeti.linftyIndicator μ R t ht := by
  rw [TauCeti.linftyIndicator_mul_linftyIndicator]
  congr 1
  exact Set.inter_eq_self_of_subset_right hts

/-- The unit indicator of a measurable set is an idempotent in `Lp R ∞ μ`. -/
theorem _root_.TauCeti.isIdempotentElem_linftyIndicator [NormedRing R] {s : Set α}
    (hs : MeasurableSet s) :
    IsIdempotentElem (TauCeti.linftyIndicator μ R s hs) :=
  TauCeti.linftyIndicator_mul_linftyIndicator_of_subset_left hs hs Set.Subset.rfl

/-- Measurable-set unit indicators in `Lp R ∞ μ` are self-adjoint. -/
@[simp]
theorem _root_.TauCeti.star_linftyIndicator [NormedRing R] [StarRing R] [NormedStarGroup R]
    {s : Set α} (hs : MeasurableSet s) :
    star (TauCeti.linftyIndicator μ R s hs) = TauCeti.linftyIndicator μ R s hs := by
  apply Lp.ext
  filter_upwards [coeFn_star (TauCeti.linftyIndicator μ R s hs),
    TauCeti.coeFn_linftyIndicator (μ := μ) (R := R) hs] with x hstar hx
  rw [hstar, Pi.star_apply, hx]
  by_cases hxs : x ∈ s <;> simp [hxs]

/-- The unit indicator of a measurable set is a star projection in `Lp R ∞ μ`. -/
theorem _root_.TauCeti.isStarProjection_linftyIndicator [NormedRing R] [StarRing R]
    [NormedStarGroup R] {s : Set α} (hs : MeasurableSet s) :
    IsStarProjection (TauCeti.linftyIndicator μ R s hs) :=
  ⟨TauCeti.isIdempotentElem_linftyIndicator hs, TauCeti.star_linftyIndicator hs⟩

/-- Over a normed ring without zero divisors, every idempotent in `Lp R ∞ μ` is the unit indicator
of a measurable set, for an arbitrary measure `μ`. -/
theorem exists_measurableSet_eq_linftyIndicator_of_isIdempotentElem [NormedRing R]
    [NoZeroDivisors R] {p : Lp R ∞ μ} (hp : IsIdempotentElem p) :
    ∃ (s : Set α) (hs : MeasurableSet s), p = TauCeti.linftyIndicator μ R s hs := by
  set s : Set α := {x | 0 < ‖p x‖}
  have hs : MeasurableSet s :=
    measurableSet_lt measurable_const (Lp.stronglyMeasurable p).norm.measurable
  refine ⟨s, hs, Lp.ext ?_⟩
  have hp_mul : ⇑p =ᵐ[μ] ⇑p * ⇑p :=
    (Lp.ext_iff.mp hp.eq.symm).trans (coeFn_mul p p)
  filter_upwards [hp_mul, TauCeti.coeFn_linftyIndicator (μ := μ) (R := R) hs] with x hmul hind
  rcases IsIdempotentElem.eq_zero_or_one hmul.symm with hx0 | hx1
  · have hxs : x ∉ s := by simp [s, hx0]
    simp [hind, hxs, hx0]
  · by_cases h10 : (1 : R) = 0
    · have hxs : x ∉ s := by simp [s, hx1, h10]
      simp [hind, hxs, hx1, h10]
    · have hxs : x ∈ s := by simp [s, hx1, h10]
      simp [hind, hxs, hx1]

end Idempotent

end MeasureTheory.Lp
