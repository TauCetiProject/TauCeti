/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Function.Holder
public import TauCeti.MeasureTheory.Function.Lp.Norm
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

The file also records how `ofRealLI`, `reCLM`, and `imCLM` interact with `L∞` multiplication and
scalars, defines the pointwise square root `MeasureTheory.Lp.sqrtLp` on `Lp ℝ ∞ μ` to characterize
nonnegative classes as squares (`MeasureTheory.Lp.nonneg_iff_exists_mul_self`), and defines the
finite square function `MeasureTheory.Lp.squareFunction` of a tuple in `Lp E ∞ μ`.

The instances follow Mathlib's corresponding instances on the space `lp B ∞` of bounded families
(`lp.inftyNormedRing`, `lp.inftyNormedAlgebra`, `lp.inftyStarRing`, `lp.inftyCStarRing`), with
almost everywhere equalities in place of pointwise ones.

## Main declarations

* `MeasureTheory.Lp.smul_eq_mul`: the product is the Hölder product at exponents `∞, ∞, ∞`.
* `MeasureTheory.Lp.coeFn_mul`: the product is pointwise almost everywhere.
* `MeasureTheory.Lp.sum_mul_eq_of_ae_eq`: an almost everywhere identity `∑ₖ aₖ aⱼ = aⱼ` of
  representatives gives the same identity in `Lp R ∞ μ`.
* `MeasureTheory.Lp.coeFn_algebraMap`: scalars act as almost everywhere constant classes.
* `MeasureTheory.Lp.lpSMul_mul_assoc` and `MeasureTheory.Lp.mul_lpSMul_comm`: heterogeneous `L∞`
  scalar multiplication associates and commutes with multiplication in `Lp R ∞ μ`.
* The instances `NormedRing`, `NormedCommRing`, `NormedAlgebra`, `StarRing`, `CStarRing`,
  `CStarAlgebra` and `CommCStarAlgebra` on `Lp R ∞ μ`.
* `MeasureTheory.Lp.reCLM_mul`, `MeasureTheory.Lp.imCLM_mul`, `MeasureTheory.Lp.normLp_mul_self_eq`:
  real/imaginary parts and squared pointwise norm of products in `Lp 𝕜 ∞ μ`.
* `MeasureTheory.MemLp.sqrt_top`, `MeasureTheory.Lp.sqrtLp`,
  `MeasureTheory.Lp.nonneg_iff_exists_mul_self`: pointwise square roots and square characterization
  of nonnegative classes in `Lp ℝ ∞ μ`.
* `MeasureTheory.Lp.squareFunction`: bundled finite square function in `Lp ℝ ∞ μ`.
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

/-- If the classes `mₖ ∈ L^∞` are almost everywhere the functions `aₖ`, and
`∑_{k ∈ s} aₖ aⱼ = aⱼ` almost everywhere, then `∑_{k ∈ s} mₖ mⱼ = mⱼ` in `L^∞`. -/
theorem sum_mul_eq_of_ae_eq {ι : Type*} {m : ι → Lp R ∞ μ} {a : ι → α → R}
    (hm : ∀ k, m k =ᵐ[μ] a k) {s : Finset ι} {j : ι}
    (h : ∀ᵐ x ∂μ, ∑ k ∈ s, a k x * a j x = a j x) :
    ∑ k ∈ s, m k * m j = m j := by
  apply Lp.ext
  filter_upwards [coeFn_fun_finsetSum s fun k ↦ m k * m j,
    (Filter.eventually_all_finset s).2 fun k _ ↦ coeFn_mul (m k) (m j),
    (Filter.eventually_all_finset s).2 fun k _ ↦ hm k, hm j, h] with x h₁ h₂ h₃ hj h₄
  rw [h₁, hj, ← h₄]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [h₂ k hk, Pi.mul_apply, h₃ k hk, hj]

end NormedRing

section LpSMul

variable [NormedRing 𝕜] [NormedRing R] [MulActionWithZero 𝕜 R] [IsBoundedSMul 𝕜 R]

/-- Heterogeneous `L∞` scalar multiplication associates with multiplication in `Lp R ∞ μ`. -/
theorem lpSMul_mul_assoc [IsScalarTower 𝕜 R R] (a : Lp 𝕜 ∞ μ) (f g : Lp R ∞ μ) :
    (a • f : Lp R ∞ μ) * g = (a • (f * g) : Lp R ∞ μ) := Lp.ext <| by
  filter_upwards [coeFn_mul (a • f : Lp R ∞ μ) g, coeFn_lpSMul (r := ∞) a f,
    coeFn_lpSMul (r := ∞) a (f * g), coeFn_mul f g] with x h₁ h₂ h₃ h₄
  simp [h₁, h₂, h₃, h₄, smul_mul_assoc]

/-- Multiplication in `Lp R ∞ μ` commutes with heterogeneous `L∞` scalar multiplication on the
right factor. -/
theorem mul_lpSMul_comm [SMulCommClass 𝕜 R R] (a : Lp 𝕜 ∞ μ) (f g : Lp R ∞ μ) :
    f * (a • g : Lp R ∞ μ) = (a • (f * g) : Lp R ∞ μ) := Lp.ext <| by
  filter_upwards [coeFn_mul f (a • g : Lp R ∞ μ), coeFn_lpSMul (r := ∞) a g,
    coeFn_lpSMul (r := ∞) a (f * g), coeFn_mul f g] with x h₁ h₂ h₃ h₄
  simp [h₁, h₂, h₃, h₄, mul_smul_comm]

end LpSMul

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

section SelfAdjoint

variable [RCLike 𝕜]

/-- `Lp.ofRealLI` preserves the multiplicative identity in `L∞`. -/
@[simp]
theorem ofRealLI_one : ofRealLI 𝕜 ∞ μ 1 = 1 := by
  refine Lp.ext ?_
  filter_upwards [coeFn_ofRealLI (𝕜 := 𝕜) (1 : Lp ℝ ∞ μ), coeFn_one (E := ℝ) (μ := μ),
    coeFn_one (E := 𝕜) (μ := μ)] with x h₁ h₂ h₃
  simp [h₁, h₂, h₃]

/-- `Lp.ofRealLI` preserves pointwise multiplication in `L∞`. -/
@[simp]
theorem ofRealLI_mul (f g : Lp ℝ ∞ μ) :
    ofRealLI 𝕜 ∞ μ (f * g) = ofRealLI 𝕜 ∞ μ f * ofRealLI 𝕜 ∞ μ g := by
  refine Lp.ext ?_
  filter_upwards [coeFn_ofRealLI (𝕜 := 𝕜) (f * g), coeFn_mul f g,
    coeFn_mul (ofRealLI 𝕜 ∞ μ f) (ofRealLI 𝕜 ∞ μ g),
    coeFn_ofRealLI (𝕜 := 𝕜) f, coeFn_ofRealLI (𝕜 := 𝕜) g] with x h₁ h₂ h₃ h₄ h₅
  simp [h₁, h₂, h₃, h₄, h₅]

/-- `Lp.reCLM` preserves the multiplicative identity in `L∞`. -/
@[simp]
theorem reCLM_one : reCLM 𝕜 ∞ μ 1 = 1 := by
  rw [← ofRealLI_one (𝕜 := 𝕜) (μ := μ), reCLM_ofRealLI]

/-- `Lp.imCLM` vanishes on the multiplicative identity in `L∞`. -/
@[simp]
theorem imCLM_one : imCLM 𝕜 ∞ μ 1 = 0 := by
  rw [← ofRealLI_one (𝕜 := 𝕜) (μ := μ), imCLM_ofRealLI]

/-- `Lp.reCLM` maps scalar classes `algebraMap 𝕜 (Lp 𝕜 ∞ μ) c` to `RCLike.re c • 1`. -/
@[simp]
theorem reCLM_algebraMap (c : 𝕜) :
    reCLM 𝕜 ∞ μ (algebraMap 𝕜 (Lp 𝕜 ∞ μ) c) = RCLike.re c • 1 := by
  refine Lp.ext ?_
  filter_upwards [coeFn_reCLM (algebraMap 𝕜 (Lp 𝕜 ∞ μ) c),
    coeFn_algebraMap (R := 𝕜) (μ := μ) c, coeFn_smul (RCLike.re c) (1 : Lp ℝ ∞ μ),
    coeFn_one (E := ℝ) (μ := μ)] with x h₁ h₂ h₃ h₄
  simp [h₁, h₂, h₃, h₄]

/-- `Lp.imCLM` maps scalar classes `algebraMap 𝕜 (Lp 𝕜 ∞ μ) c` to `RCLike.im c • 1`. -/
@[simp]
theorem imCLM_algebraMap (c : 𝕜) :
    imCLM 𝕜 ∞ μ (algebraMap 𝕜 (Lp 𝕜 ∞ μ) c) = RCLike.im c • 1 := by
  refine Lp.ext ?_
  filter_upwards [coeFn_imCLM (algebraMap 𝕜 (Lp 𝕜 ∞ μ) c),
    coeFn_algebraMap (R := 𝕜) (μ := μ) c, coeFn_smul (RCLike.im c) (1 : Lp ℝ ∞ μ),
    coeFn_one (E := ℝ) (μ := μ)] with x h₁ h₂ h₃ h₄
  simp [h₁, h₂, h₃, h₄]

/-- Real part of a product in `Lp 𝕜 ∞ μ`. -/
theorem reCLM_mul (f g : Lp 𝕜 ∞ μ) :
    reCLM 𝕜 ∞ μ (f * g) =
      reCLM 𝕜 ∞ μ f * reCLM 𝕜 ∞ μ g - imCLM 𝕜 ∞ μ f * imCLM 𝕜 ∞ μ g := by
  refine Lp.ext ?_
  filter_upwards [coeFn_reCLM (f * g), coeFn_mul f g,
    coeFn_sub (reCLM 𝕜 ∞ μ f * reCLM 𝕜 ∞ μ g) (imCLM 𝕜 ∞ μ f * imCLM 𝕜 ∞ μ g),
    coeFn_mul (reCLM 𝕜 ∞ μ f) (reCLM 𝕜 ∞ μ g), coeFn_mul (imCLM 𝕜 ∞ μ f) (imCLM 𝕜 ∞ μ g),
    coeFn_reCLM f, coeFn_reCLM g, coeFn_imCLM f, coeFn_imCLM g]
    with x h₁ h₂ hsub hm₁ hm₂ hr₁ hr₂ hi₁ hi₂
  rw [hsub]
  simp [h₁, h₂, hm₁, hm₂, hr₁, hr₂, hi₁, hi₂, RCLike.mul_re]

/-- Imaginary part of a product in `Lp 𝕜 ∞ μ`. -/
theorem imCLM_mul (f g : Lp 𝕜 ∞ μ) :
    imCLM 𝕜 ∞ μ (f * g) =
      reCLM 𝕜 ∞ μ f * imCLM 𝕜 ∞ μ g + imCLM 𝕜 ∞ μ f * reCLM 𝕜 ∞ μ g := by
  refine Lp.ext ?_
  filter_upwards [coeFn_imCLM (f * g), coeFn_mul f g,
    coeFn_add (reCLM 𝕜 ∞ μ f * imCLM 𝕜 ∞ μ g) (imCLM 𝕜 ∞ μ f * reCLM 𝕜 ∞ μ g),
    coeFn_mul (reCLM 𝕜 ∞ μ f) (imCLM 𝕜 ∞ μ g), coeFn_mul (imCLM 𝕜 ∞ μ f) (reCLM 𝕜 ∞ μ g),
    coeFn_reCLM f, coeFn_reCLM g, coeFn_imCLM f, coeFn_imCLM g]
    with x h₁ h₂ hadd hm₁ hm₂ hr₁ hr₂ hi₁ hi₂
  rw [hadd]
  simp [h₁, h₂, hm₁, hm₂, hr₁, hr₂, hi₁, hi₂, RCLike.mul_im]

/-- In `Lp 𝕜 ∞ μ`, `normLp f * normLp f` equals `(reCLM f) ^ 2 + (imCLM f) ^ 2`. -/
theorem normLp_mul_self_eq (f : Lp 𝕜 ∞ μ) :
    normLp f * normLp f =
      reCLM 𝕜 ∞ μ f * reCLM 𝕜 ∞ μ f + imCLM 𝕜 ∞ μ f * imCLM 𝕜 ∞ μ f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_mul (normLp f) (normLp f), coeFn_normLp f,
    coeFn_add (reCLM 𝕜 ∞ μ f * reCLM 𝕜 ∞ μ f) (imCLM 𝕜 ∞ μ f * imCLM 𝕜 ∞ μ f),
    coeFn_mul (reCLM 𝕜 ∞ μ f) (reCLM 𝕜 ∞ μ f), coeFn_reCLM f,
    coeFn_mul (imCLM 𝕜 ∞ μ f) (imCLM 𝕜 ∞ μ f), coeFn_imCLM f] with x hn₁ hn₂ ha hr₁ hr₂ hi₁ hi₂
  rw [ha]
  simp [hn₁, hn₂, hr₁, hr₂, hi₁, hi₂, RCLike.mul_self_norm, RCLike.normSq_apply]

/-- The inverse of `selfAdjointLinearIsometryEquiv` preserves `1` on `L∞`. -/
@[simp]
theorem selfAdjointLinearIsometryEquiv_symm_one :
    (selfAdjointLinearIsometryEquiv 𝕜 ∞ μ).symm 1 = 1 := by
  apply Subtype.ext
  rw [coe_selfAdjointLinearIsometryEquiv_symm_apply, ofRealLI_one, selfAdjoint.val_one]

/-- The inverse of `selfAdjointLinearIsometryEquiv` preserves multiplication on `L∞`. -/
@[simp]
theorem selfAdjointLinearIsometryEquiv_symm_mul (f g : Lp ℝ ∞ μ) :
    (selfAdjointLinearIsometryEquiv 𝕜 ∞ μ).symm (f * g) =
      (selfAdjointLinearIsometryEquiv 𝕜 ∞ μ).symm f *
        (selfAdjointLinearIsometryEquiv 𝕜 ∞ μ).symm g := by
  apply Subtype.ext
  rw [coe_selfAdjointLinearIsometryEquiv_symm_apply, ofRealLI_mul, selfAdjoint.val_mul,
    coe_selfAdjointLinearIsometryEquiv_symm_apply,
    coe_selfAdjointLinearIsometryEquiv_symm_apply]

/-- `selfAdjointLinearIsometryEquiv` preserves `1` on `L∞`. -/
@[simp]
theorem selfAdjointLinearIsometryEquiv_one :
    selfAdjointLinearIsometryEquiv 𝕜 ∞ μ 1 = 1 := by
  rw [← selfAdjointLinearIsometryEquiv_symm_one (𝕜 := 𝕜) (μ := μ),
    LinearIsometryEquiv.apply_symm_apply]

/-- `selfAdjointLinearIsometryEquiv` preserves multiplication on `L∞`. -/
@[simp]
theorem selfAdjointLinearIsometryEquiv_mul (f g : selfAdjoint (Lp 𝕜 ∞ μ)) :
    selfAdjointLinearIsometryEquiv 𝕜 ∞ μ (f * g) =
      selfAdjointLinearIsometryEquiv 𝕜 ∞ μ f * selfAdjointLinearIsometryEquiv 𝕜 ∞ μ g := by
  refine (selfAdjointLinearIsometryEquiv 𝕜 ∞ μ).symm.injective ?_
  rw [selfAdjointLinearIsometryEquiv_symm_mul, LinearIsometryEquiv.symm_apply_apply,
    LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.symm_apply_apply]

end SelfAdjoint

section SqrtAndSquareFunction

/-- The pointwise square root of an essentially bounded real function is essentially bounded. -/
theorem _root_.MeasureTheory.MemLp.sqrt_top {f : α → ℝ} (hf : MemLp f ∞ μ) :
    MemLp (fun x ↦ √(f x)) ∞ μ := by
  refine memLp_top_of_bound (Real.continuous_sqrt.comp_aestronglyMeasurable
    hf.aestronglyMeasurable) √(lpNorm f ∞ μ) ?_
  filter_upwards [ae_le_lpNorm_exponent_top hf] with x hx
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_sqrt ((le_abs_self _).trans (by rwa [Real.norm_eq_abs] at hx))

/-- Pointwise square root `x ↦ √(f x)` on `Lp ℝ ∞ μ`. -/
def sqrtLp (f : Lp ℝ ∞ μ) : Lp ℝ ∞ μ :=
  (Lp.memLp f).sqrt_top.toLp fun x ↦ √(f x)

/-- `Lp.sqrtLp f` equals `x ↦ √(f x)` almost everywhere. -/
theorem coeFn_sqrtLp (f : Lp ℝ ∞ μ) : sqrtLp f =ᵐ[μ] fun x ↦ √(f x) :=
  (Lp.memLp f).sqrt_top.coeFn_toLp

/-- `Lp.sqrtLp` sends `0` to `0`. -/
@[simp]
theorem sqrtLp_zero : sqrtLp (0 : Lp ℝ ∞ μ) = 0 := by
  refine Lp.ext ?_
  filter_upwards [coeFn_sqrtLp (0 : Lp ℝ ∞ μ), Lp.coeFn_zero ℝ ∞ μ] with x h₁ h₂
  rw [h₁, h₂, Pi.zero_apply, Real.sqrt_zero]

/-- `Lp.sqrtLp` sends `1` to `1`. -/
@[simp]
theorem sqrtLp_one : sqrtLp (1 : Lp ℝ ∞ μ) = 1 := by
  refine Lp.ext ?_
  filter_upwards [coeFn_sqrtLp (1 : Lp ℝ ∞ μ), coeFn_one (E := ℝ) (μ := μ)] with x h₁ h₂
  simp [h₁, h₂]

/-- `Lp.sqrtLp f` is nonnegative. -/
@[simp]
theorem sqrtLp_nonneg (f : Lp ℝ ∞ μ) : 0 ≤ sqrtLp f := by
  rw [← Lp.coeFn_nonneg]
  filter_upwards [coeFn_sqrtLp f] with x hx
  rw [Pi.zero_apply, hx]
  exact Real.sqrt_nonneg _

/-- Squaring `Lp.sqrtLp f` recovers a nonnegative `f : Lp ℝ ∞ μ`. -/
@[simp]
theorem mul_self_sqrtLp {f : Lp ℝ ∞ μ} (hf : 0 ≤ f) : sqrtLp f * sqrtLp f = f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_mul (sqrtLp f) (sqrtLp f), coeFn_sqrtLp f,
    (Lp.coeFn_nonneg f).2 hf] with x h₁ h₂ h₃
  rw [h₁, Pi.mul_apply, h₂, Real.mul_self_sqrt h₃]

/-- Taking `Lp.sqrtLp` of a square `f * f` gives `|f|`. -/
@[simp]
theorem sqrtLp_mul_self_eq_abs (f : Lp ℝ ∞ μ) : sqrtLp (f * f) = |f| := by
  refine Lp.ext ?_
  filter_upwards [coeFn_sqrtLp (f * f), coeFn_mul f f, Lp.coeFn_abs f] with x h₁ h₂ h₃
  rw [h₁, h₂, Pi.mul_apply, Real.sqrt_mul_self_eq_abs, h₃]

/-- A class in `Lp ℝ ∞ μ` is nonnegative if and only if it is a square. -/
theorem nonneg_iff_exists_mul_self {f : Lp ℝ ∞ μ} :
    0 ≤ f ↔ ∃ r : Lp ℝ ∞ μ, f = r * r := by
  refine ⟨fun hf ↦ ⟨sqrtLp f, (mul_self_sqrtLp hf).symm⟩, ?_⟩
  rintro ⟨r, rfl⟩
  rw [← Lp.coeFn_nonneg]
  filter_upwards [coeFn_mul r r] with x hx
  rw [Pi.zero_apply, hx, Pi.mul_apply]
  exact mul_self_nonneg _

variable {E ι : Type*} [NormedAddCommGroup E] [Fintype ι]

/-- The finite square function `x ↦ √(∑ i, ‖g i x‖ ^ 2)` of a family `g : ι → Lp E ∞ μ`, bundled
in `Lp ℝ ∞ μ`. -/
def squareFunction (g : ι → Lp E ∞ μ) : Lp ℝ ∞ μ :=
  sqrtLp (∑ i, normLp (g i) * normLp (g i))

/-- Defining formula for `Lp.squareFunction` in terms of `sqrtLp` and `normLp`. -/
theorem squareFunction_def (g : ι → Lp E ∞ μ) :
    squareFunction g = sqrtLp (∑ i, normLp (g i) * normLp (g i)) :=
  (rfl)

/-- `Lp.squareFunction` vanishes on the zero family. -/
@[simp]
theorem squareFunction_zero : squareFunction (0 : ι → Lp E ∞ μ) = 0 := by
  rw [squareFunction_def]
  simp

/-- `Lp.squareFunction g` is nonnegative. -/
@[simp]
theorem squareFunction_nonneg (g : ι → Lp E ∞ μ) : 0 ≤ squareFunction g :=
  sqrtLp_nonneg _

/-- `Lp.squareFunction g` equals `x ↦ √(∑ i, ‖g i x‖ ^ 2)` almost everywhere. -/
theorem coeFn_squareFunction (g : ι → Lp E ∞ μ) :
    squareFunction g =ᵐ[μ] fun x ↦ √(∑ i, ‖g i x‖ ^ 2) := by
  have hsum : (∑ i, normLp (g i) * normLp (g i) : Lp ℝ ∞ μ) =ᵐ[μ]
      fun x ↦ ∑ i, ‖g i x‖ ^ 2 := by
    filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i ↦ normLp (g i) * normLp (g i)),
      Filter.eventually_all.mpr fun i ↦ coeFn_mul (normLp (g i)) (normLp (g i)),
      Filter.eventually_all.mpr fun i ↦ coeFn_normLp (g i)] with x hs hm hn
    rw [hs, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hm i, Pi.mul_apply, hn i, sq]
  filter_upwards [coeFn_sqrtLp (∑ i, normLp (g i) * normLp (g i)), hsum] with x h₁ h₂
  rw [squareFunction_def, h₁, h₂]

end SqrtAndSquareFunction

end MeasureTheory.Lp
