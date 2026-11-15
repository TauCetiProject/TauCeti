/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Function.Holder
public import TauCeti.MeasureTheory.Function.Lp.One
public import TauCeti.MeasureTheory.Function.Lp.Star
public import TauCeti.MeasureTheory.Function.SimpleFunc.Dense

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
and its unit has norm one if that of `R` does.

The unit indicator of any measurable set `s`, represented in `L∞(μ, R)` by
`MeasureTheory.SimpleFunc.toLpTop μ R (SimpleFunc.piecewise s hs 1 0)`, is an idempotent (and a
star projection when `R` is a normed star ring), with multiplication corresponding to intersection
of sets. Over a normed division ring `R`, these measurable-set indicators exhaust all idempotents
of `Lp R ∞ μ`.

The instances follow Mathlib's corresponding instances on the space `lp B ∞` of bounded families
(`lp.inftyNormedRing`, `lp.inftyNormedAlgebra`, `lp.inftyStarRing`, `lp.inftyCStarRing`), with
almost everywhere equalities in place of pointwise ones.

## Main declarations

* `MeasureTheory.Lp.smul_eq_mul`: the product is the Hölder product at exponents `∞, ∞, ∞`.
* `MeasureTheory.Lp.coeFn_mul`: the product is pointwise almost everywhere.
* `MeasureTheory.Lp.coeFn_algebraMap`: scalars act as almost everywhere constant classes.
* `MeasureTheory.Lp.exists_measurableSet_toLpTop_piecewise_eq_of_isIdempotentElem`: over a normed
  division ring, every idempotent in `Lp R ∞ μ` is the unit indicator of a measurable set.
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

/-- The `L∞` class of `SimpleFunc.piecewise s hs (1 : SimpleFunc α R) 0` agrees almost everywhere
with `s.indicator 1`. -/
theorem coeFn_toLpTop_piecewise_one_zero [NormedRing R] {s : Set α} (hs : MeasurableSet s) :
    SimpleFunc.toLpTop μ R (SimpleFunc.piecewise s hs (1 : SimpleFunc α R) 0) =ᵐ[μ]
      s.indicator 1 := by
  filter_upwards [SimpleFunc.coeFn_toLpTop (μ := μ) (𝕜 := R)
    (SimpleFunc.piecewise s hs (1 : SimpleFunc α R) 0)] with x hx
  rw [hx]
  by_cases hxs : x ∈ s <;> simp [hxs]

theorem toLpTop_piecewise_one_zero_empty [NormedRing R] :
    SimpleFunc.toLpTop μ R
      (SimpleFunc.piecewise ∅ MeasurableSet.empty (1 : SimpleFunc α R) 0) = 0 := by
  simp

theorem toLpTop_piecewise_one_zero_univ [NormedRing R] :
    SimpleFunc.toLpTop μ R
      (SimpleFunc.piecewise Set.univ MeasurableSet.univ (1 : SimpleFunc α R) 0) = 1 := by
  apply Lp.ext
  filter_upwards [coeFn_toLpTop_piecewise_one_zero (μ := μ) (R := R) MeasurableSet.univ,
    coeFn_one (E := R) (μ := μ)] with x h h₁
  rw [h, h₁, Set.indicator_univ]

/-- The unit indicator of a measurable set `s` vanishes in `Lp R ∞ μ` over a nontrivial normed ring
if and only if `s` is `μ`-null. -/
theorem toLpTop_piecewise_one_zero_eq_zero_iff [NormedRing R] [Nontrivial R] {s : Set α}
    (hs : MeasurableSet s) :
    SimpleFunc.toLpTop μ R (SimpleFunc.piecewise s hs (1 : SimpleFunc α R) 0) = 0 ↔ μ s = 0 := by
  rw [Lp.eq_zero_iff_ae_eq_zero]
  refine ⟨fun h ↦ measure_eq_zero_iff_ae_notMem.mpr ?_, fun h ↦ ?_⟩
  · filter_upwards [coeFn_toLpTop_piecewise_one_zero (μ := μ) (R := R) hs, h] with x hx hx0 hxs
    simp [hx, hxs] at hx0
  · filter_upwards [coeFn_toLpTop_piecewise_one_zero (μ := μ) (R := R) hs,
      measure_eq_zero_iff_ae_notMem.mp h] with x hx hxs
    rw [hx, Set.indicator_of_notMem hxs, Pi.zero_apply]

/-- Two measurable-set unit indicators in `Lp R ∞ μ` over a nontrivial normed ring agree if and
only if their underlying sets agree almost everywhere. -/
theorem toLpTop_piecewise_one_zero_inj [NormedRing R] [Nontrivial R] {s t : Set α}
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    SimpleFunc.toLpTop μ R (SimpleFunc.piecewise s hs (1 : SimpleFunc α R) 0) =
      SimpleFunc.toLpTop μ R (SimpleFunc.piecewise t ht (1 : SimpleFunc α R) 0) ↔ s =ᵐ[μ] t := by
  rw [Lp.ext_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · filter_upwards [coeFn_toLpTop_piecewise_one_zero (μ := μ) (R := R) hs,
      coeFn_toLpTop_piecewise_one_zero (μ := μ) (R := R) ht, h] with x hsx htx hxeq
    rw [hsx, htx] at hxeq
    by_cases hxs : x ∈ s <;> by_cases hxt : x ∈ t <;> simp_all
  · filter_upwards [coeFn_toLpTop_piecewise_one_zero (μ := μ) (R := R) hs,
      coeFn_toLpTop_piecewise_one_zero (μ := μ) (R := R) ht, h] with x hsx htx hxeq
    by_cases hxt : x ∈ t
    · simp [hsx, htx, hxeq.mpr hxt, hxt]
    · simp [hsx, htx, mt hxeq.mp hxt, hxt]

/-- Multiplying measurable-set unit indicators in `Lp R ∞ μ` intersects the underlying sets. -/
theorem toLpTop_piecewise_one_zero_mul [NormedRing R] {s t : Set α} (hs : MeasurableSet s)
    (ht : MeasurableSet t) :
    SimpleFunc.toLpTop μ R (SimpleFunc.piecewise s hs (1 : SimpleFunc α R) 0) *
      SimpleFunc.toLpTop μ R (SimpleFunc.piecewise t ht (1 : SimpleFunc α R) 0) =
      SimpleFunc.toLpTop μ R
        (SimpleFunc.piecewise (s ∩ t) (hs.inter ht) (1 : SimpleFunc α R) 0) := by
  apply Lp.ext
  filter_upwards [coeFn_mul
      (SimpleFunc.toLpTop μ R (SimpleFunc.piecewise s hs (1 : SimpleFunc α R) 0))
      (SimpleFunc.toLpTop μ R (SimpleFunc.piecewise t ht (1 : SimpleFunc α R) 0)),
    coeFn_toLpTop_piecewise_one_zero (μ := μ) (R := R) hs,
    coeFn_toLpTop_piecewise_one_zero (μ := μ) (R := R) ht,
    coeFn_toLpTop_piecewise_one_zero (μ := μ) (R := R) (hs.inter ht)] with x hmul hsx htx hst
  rw [hmul, Pi.mul_apply, hsx, htx, hst]
  by_cases hxs : x ∈ s <;> by_cases hxt : x ∈ t <;> simp [hxs, hxt]

theorem isIdempotentElem_toLpTop_piecewise_one_zero [NormedRing R] {s : Set α}
    (hs : MeasurableSet s) :
    IsIdempotentElem (SimpleFunc.toLpTop μ R
      (SimpleFunc.piecewise s hs (1 : SimpleFunc α R) 0)) := by
  rw [IsIdempotentElem, toLpTop_piecewise_one_zero_mul]
  congr 1
  ext x
  by_cases hxs : x ∈ s <;> simp [hxs]

@[simp]
theorem star_toLpTop_piecewise_one_zero [NormedRing R] [StarRing R] [NormedStarGroup R] {s : Set α}
    (hs : MeasurableSet s) :
    star (SimpleFunc.toLpTop μ R (SimpleFunc.piecewise s hs (1 : SimpleFunc α R) 0)) =
      SimpleFunc.toLpTop μ R (SimpleFunc.piecewise s hs (1 : SimpleFunc α R) 0) := by
  apply Lp.ext
  filter_upwards [coeFn_star
      (SimpleFunc.toLpTop μ R (SimpleFunc.piecewise s hs (1 : SimpleFunc α R) 0)),
    coeFn_toLpTop_piecewise_one_zero (μ := μ) (R := R) hs] with x hstar hx
  rw [hstar, Pi.star_apply, hx]
  by_cases hxs : x ∈ s <;> simp [hxs]

theorem isStarProjection_toLpTop_piecewise_one_zero [NormedRing R] [StarRing R] [NormedStarGroup R]
    {s : Set α} (hs : MeasurableSet s) :
    IsStarProjection (SimpleFunc.toLpTop μ R
      (SimpleFunc.piecewise s hs (1 : SimpleFunc α R) 0)) :=
  ⟨isIdempotentElem_toLpTop_piecewise_one_zero hs, star_toLpTop_piecewise_one_zero hs⟩

/-- Over a normed division ring, every idempotent in `Lp R ∞ μ` is the unit indicator of a
measurable set, for an arbitrary measure `μ`. -/
theorem exists_measurableSet_toLpTop_piecewise_eq_of_isIdempotentElem [NormedDivisionRing R]
    {p : Lp R ∞ μ} (hp : IsIdempotentElem p) :
    ∃ (s : Set α) (hs : MeasurableSet s),
      p = SimpleFunc.toLpTop μ R (SimpleFunc.piecewise s hs (1 : SimpleFunc α R) 0) := by
  set s : Set α := {x | (2⁻¹ : ℝ) < ‖p x‖}
  have hs : MeasurableSet s :=
    measurableSet_lt measurable_const (Lp.stronglyMeasurable p).norm.measurable
  refine ⟨s, hs, Lp.ext ?_⟩
  have hp_mul : ⇑p =ᵐ[μ] ⇑p * ⇑p :=
    (Lp.ext_iff.mp hp.eq.symm).trans (coeFn_mul p p)
  filter_upwards [hp_mul, coeFn_toLpTop_piecewise_one_zero (μ := μ) (R := R) hs] with x hmul hind
  have hx01 : p x = 1 ∨ p x = 0 := by
    have hsub : (p x - 1) * p x = 0 := by
      rw [sub_mul, one_mul, sub_eq_zero]
      exact hmul.symm
    exact (mul_eq_zero.mp hsub).imp sub_eq_zero.mp id
  rcases hx01 with hx1 | hx0
  · have hxs : x ∈ s := by
      change (2⁻¹ : ℝ) < ‖p x‖
      simp [hx1]
      norm_num
    simp [hind, hxs, hx1]
  · have hxs : x ∉ s := by
      change ¬ (2⁻¹ : ℝ) < ‖p x‖
      simp [hx0]
    simp [hind, hxs, hx0]

end Idempotent

end MeasureTheory.Lp
