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

The instances follow Mathlib's corresponding instances on the space `lp B ∞` of bounded families
(`lp.inftyNormedRing`, `lp.inftyNormedAlgebra`, `lp.inftyStarRing`, `lp.inftyCStarRing`), with
almost everywhere equalities in place of pointwise ones.

## Main declarations

* `MeasureTheory.Lp.smul_eq_mul`: the product is the Hölder product at exponents `∞, ∞, ∞`.
* `MeasureTheory.Lp.coeFn_mul`: the product is pointwise almost everywhere.
* `MeasureTheory.Lp.coeFn_algebraMap`: scalars act as almost everywhere constant classes.
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

end MeasureTheory.Lp
