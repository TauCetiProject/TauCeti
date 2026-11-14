/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import TauCeti.CategoryTheory.Dagger.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# C*-categories

A C*-category is a complex-linear dagger category whose Hom spaces are complex Banach spaces in
which composition is contractive (`‖f ≫ g‖ ≤ ‖g‖ * ‖f‖`), the C*-identity
`‖f ≫ dagger f‖ = ‖f‖ ^ 2` holds in categorical composition order, and every `f ≫ dagger f`
is a positive endomorphism in `End X` (expressed here without spectral prerequisites as
`∃ g : X ⟶ X, f ≫ dagger f = g ≫ dagger g`, and shown equivalent to spectral nonnegativity in
`TauCeti.CategoryTheory.CStarCategory.End`).

To avoid algebraic or module-theoretic diamonds against `CategoryTheory.Preadditive` and
`CategoryTheory.Linear ℂ`, `TauCeti.CStarCategory` stores only the norm, compatible metric,
completeness, and scalar-norm bound on Hom spaces, assembling `NormedAddCommGroup (X ⟶ Y)` and
`NormedSpace ℂ (X ⟶ Y)` directly over the existing Hom group and `ℂ`-module structures.

Isometricity of the dagger (`‖dagger f‖ = ‖f‖`) is derived from submultiplicativity of
composition and the C*-identity rather than assumed as an axiom. Pre- and post-composition bundle
into a norm-contractive continuous bilinear map `compCLM`, whose specializations `leftCompCLM X f`
and `rightCompCLM Z g` recover the exact morphism norms `‖f‖` and `‖g‖`. Continuous linear maps on
Hom spaces—including left/right annihilators and intertwiner spaces—have closed Banach kernels,
and identity, unitary, self-adjoint-idempotent, zero-object, and polarization formulas follow.

## References

* P. Ghez, R. Lima, J. E. Roberts, *W\*-categories*, Pacific J. Math. 120 (1985), 79–109.
* P. D. Mitchener, *C\*-categories*, Proc. London Math. Soc. (3) 84 (2002), 375–404.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe v u

namespace TauCeti

section Polarization

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C] {X Y : C}

/-- Scaled complex polarization identity for `f ≫ dagger g` in a complex-linear dagger category. -/
theorem four_smul_comp_dagger (f g : X ⟶ Y) :
    (4 : ℂ) • (f ≫ dagger g) =
      (f + g) ≫ dagger (f + g) - (f - g) ≫ dagger (f - g) +
        Complex.I • ((f + Complex.I • g) ≫ dagger (f + Complex.I • g) -
          (f - Complex.I • g) ≫ dagger (f - Complex.I • g)) := by
  simp only [dagger_add, dagger_sub, dagger_smul, RCLike.star_def, Complex.conj_I,
    Preadditive.add_comp, Preadditive.sub_comp, Preadditive.comp_add, Preadditive.comp_sub,
    Linear.smul_comp, Linear.comp_smul, neg_smul, Preadditive.comp_neg,
    smul_sub, smul_add, smul_neg, smul_smul, Complex.I_mul_I, one_smul]
  module

/-- Complex polarization expresses `f ≫ dagger g` as a linear combination of four positive-form
endomorphisms `(f + c • g) ≫ dagger (f + c • g)`. -/
theorem comp_dagger_eq_polarization (f g : X ⟶ Y) :
    f ≫ dagger g =
      (4 : ℂ)⁻¹ • ((f + g) ≫ dagger (f + g) - (f - g) ≫ dagger (f - g) +
        Complex.I • ((f + Complex.I • g) ≫ dagger (f + Complex.I • g) -
          (f - Complex.I • g) ≫ dagger (f - Complex.I • g))) := by
  rw [← four_smul_comp_dagger, smul_smul, inv_mul_cancel₀ (by norm_num), one_smul]

/-- Scaled complex polarization identity for `dagger f ≫ g` in a complex-linear dagger category. -/
theorem four_smul_dagger_comp (f g : X ⟶ Y) :
    (4 : ℂ) • (dagger f ≫ g) =
      dagger (f + g) ≫ (f + g) - dagger (f - g) ≫ (f - g) -
        Complex.I • (dagger (f + Complex.I • g) ≫ (f + Complex.I • g) -
          dagger (f - Complex.I • g) ≫ (f - Complex.I • g)) := by
  simp only [dagger_add, dagger_sub, dagger_smul, RCLike.star_def, Complex.conj_I,
    Preadditive.add_comp, Preadditive.sub_comp, Preadditive.comp_add, Preadditive.comp_sub,
    Linear.smul_comp, Linear.comp_smul, neg_smul, Preadditive.neg_comp,
    smul_sub, smul_add, smul_neg, smul_smul, Complex.I_mul_I, one_smul]
  module

/-- Complex polarization expresses `dagger f ≫ g` as a linear combination of four endomorphisms
`dagger (f + c • g) ≫ (f + c • g)`. -/
theorem dagger_comp_eq_polarization (f g : X ⟶ Y) :
    dagger f ≫ g =
      (4 : ℂ)⁻¹ • (dagger (f + g) ≫ (f + g) - dagger (f - g) ≫ (f - g) -
        Complex.I • (dagger (f + Complex.I • g) ≫ (f + Complex.I • g) -
          dagger (f - Complex.I • g) ≫ (f - Complex.I • g))) := by
  rw [← four_smul_dagger_comp, smul_smul, inv_mul_cancel₀ (by norm_num), one_smul]

end Polarization

/-- A complex C*-category: a `ℂ`-linear dagger category with Banach Hom spaces, contractive
composition, the C*-identity `‖f ≫ dagger f‖ = ‖f‖ ^ 2`, and positivity of `f ≫ dagger f` in
`End X` (expressed as `f ≫ dagger f = g ≫ dagger g` for some `g : X ⟶ X`). -/
class CStarCategory (C : Type u) [Category.{v} C] [Preadditive C] [Linear ℂ C]
    [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C] where
  /-- The norm on each Hom space. -/
  homNorm : ∀ X Y : C, Norm (X ⟶ Y) := by infer_instance
  /-- The metric on each Hom space. -/
  homMetricSpace : ∀ X Y : C, MetricSpace (X ⟶ Y) := by infer_instance
  /-- Distance on each Hom space is induced by the norm and preadditive subtraction. -/
  dist_eq : ∀ {X Y : C} (f g : X ⟶ Y), dist f g = ‖-f + g‖ := by aesop
  /-- Completeness of each Hom space in its norm metric. -/
  homCompleteSpace : ∀ X Y : C, CompleteSpace (X ⟶ Y) := by infer_instance
  /-- Scalar multiplication on Hom spaces is bounded by the complex norm. -/
  norm_smul_le : ∀ {X Y : C} (c : ℂ) (f : X ⟶ Y), ‖c • f‖ ≤ ‖c‖ * ‖f‖ := by
    intro X Y c f; exact NormedSpace.norm_smul_le c f
  /-- Categorical composition is contractive. -/
  norm_comp_le : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), ‖f ≫ g‖ ≤ ‖g‖ * ‖f‖
  /-- The C*-identity in categorical composition order. -/
  norm_comp_dagger_self : ∀ {X Y : C} (f : X ⟶ Y), ‖f ≫ dagger f‖ = ‖f‖ ^ 2
  /-- Every `f ≫ dagger f` arises as `g ≫ dagger g` for an endomorphism `g : X ⟶ X`, encoding
  positivity in the C*-algebra `End X`. -/
  exists_comp_dagger_eq : ∀ {X Y : C} (f : X ⟶ Y), ∃ g : X ⟶ X, f ≫ dagger f = g ≫ dagger g

attribute [instance_reducible, instance]
  CStarCategory.homNorm CStarCategory.homMetricSpace

attribute [instance] CStarCategory.homCompleteSpace

namespace CStarCategory

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C] [CStarCategory C]
variable {W X Y Z : C}

/-- Each Hom space in a C*-category is a normed additive commutative group over its preadditive
Hom group. -/
@[instance_reducible]
instance homNormedAddCommGroup (X Y : C) : NormedAddCommGroup (X ⟶ Y) where
  __ := Preadditive.homGroup X Y
  __ := CStarCategory.homNorm X Y
  __ := CStarCategory.homMetricSpace X Y
  dist_eq := CStarCategory.dist_eq

/-- Each Hom space in a C*-category is a complex normed space over its linear Hom module. -/
@[instance_reducible]
instance homNormedSpace (X Y : C) : NormedSpace ℂ (X ⟶ Y) where
  __ := Linear.homModule X Y
  norm_smul_le := CStarCategory.norm_smul_le

/-- Composition in a C*-category is submultiplicative in either factor order. -/
theorem norm_comp_le' (f : X ⟶ Y) (g : Y ⟶ Z) : ‖f ≫ g‖ ≤ ‖f‖ * ‖g‖ := by
  rw [mul_comm]
  exact norm_comp_le f g

/-- The C*-identity written with multiplication rather than squaring. -/
theorem norm_comp_dagger_self' (f : X ⟶ Y) : ‖f ≫ dagger f‖ = ‖f‖ * ‖f‖ := by
  rw [norm_comp_dagger_self, sq]

/-- Taking the dagger in a C*-category is norm-preserving. -/
@[simp] theorem norm_dagger (f : X ⟶ Y) : ‖dagger f‖ = ‖f‖ := by
  have hle : ∀ {A B : C} (h : A ⟶ B), ‖h‖ ≤ ‖dagger h‖ := fun h => by
    by_cases h0 : ‖h‖ = 0
    · simp [h0]
    · have hpos : 0 < ‖h‖ := lt_of_le_of_ne (norm_nonneg h) (Ne.symm h0)
      exact le_of_mul_le_mul_right
        ((norm_comp_dagger_self' h).symm.le.trans (norm_comp_le h (dagger h))) hpos
  exact le_antisymm (by simpa using hle (dagger f)) (hle f)

/-- Taking the dagger preserves the nonnegative norm. -/
@[simp] theorem nnNorm_dagger (f : X ⟶ Y) : ‖dagger f‖₊ = ‖f‖₊ :=
  Subtype.ext (norm_dagger f)

/-- Taking the dagger preserves distances on Hom spaces. -/
@[simp] theorem dist_dagger (f g : X ⟶ Y) : dist (dagger f) (dagger g) = dist f g := by
  rw [dist_eq_norm, dist_eq_norm, ← dagger_sub, norm_dagger]

/-- Taking the dagger is an isometry between opposite Hom spaces. -/
theorem isometry_dagger (X Y : C) : Isometry (dagger : (X ⟶ Y) → (Y ⟶ X)) :=
  Isometry.of_dist_eq dist_dagger

/-- Taking the dagger is continuous on Hom spaces. -/
@[fun_prop] theorem continuous_dagger (X Y : C) : Continuous (dagger : (X ⟶ Y) → (Y ⟶ X)) :=
  (isometry_dagger X Y).continuous

/-- The dagger bundled as a conjugate-linear isometric equivalence between opposite Hom spaces. -/
def daggerLinearIsometryEquiv (X Y : C) :
    (X ⟶ Y) ≃ₗᵢ⋆[ℂ] (Y ⟶ X) where
  __ := daggerLinearEquiv ℂ X Y
  norm_map' _ := by simp

/-- Evaluation of `daggerLinearIsometryEquiv`. -/
@[simp] theorem daggerLinearIsometryEquiv_apply (f : X ⟶ Y) :
    daggerLinearIsometryEquiv X Y f = dagger f := by
  simp [daggerLinearIsometryEquiv]

/-- The inverse of `daggerLinearIsometryEquiv` reverses its endpoints. -/
@[simp] theorem daggerLinearIsometryEquiv_symm :
    (daggerLinearIsometryEquiv X Y).symm = daggerLinearIsometryEquiv Y X := by
  ext f
  exact (daggerLinearIsometryEquiv X Y).injective (by simp)

/-- The C*-identity in opposite composition order `dagger f ≫ f`. -/
@[simp] theorem norm_dagger_comp_self (f : X ⟶ Y) : ‖dagger f ≫ f‖ = ‖f‖ ^ 2 := by
  simpa only [dagger_dagger, norm_dagger] using norm_comp_dagger_self (dagger f)

/-- Multiplicative form of the opposite-order C*-identity. -/
theorem norm_dagger_comp_self' (f : X ⟶ Y) : ‖dagger f ≫ f‖ = ‖f‖ * ‖f‖ := by
  rw [norm_dagger_comp_self, sq]

/-- `f ≫ dagger f` vanishes precisely when `f` vanishes. -/
@[simp] theorem comp_dagger_self_eq_zero_iff (f : X ⟶ Y) :
    f ≫ dagger f = 0 ↔ f = 0 := by
  rw [← norm_eq_zero, norm_comp_dagger_self, sq_eq_zero_iff, norm_eq_zero]

/-- `dagger f ≫ f` vanishes precisely when `f` vanishes. -/
@[simp] theorem dagger_comp_self_eq_zero_iff (f : X ⟶ Y) :
    dagger f ≫ f = 0 ↔ f = 0 := by
  rw [← norm_eq_zero, norm_dagger_comp_self, sq_eq_zero_iff, norm_eq_zero]

/-- Norm Cauchy–Schwarz inequality for `f ≫ dagger g`:
`‖f ≫ dagger g‖ ^ 2 ≤ ‖f ≫ dagger f‖ * ‖g ≫ dagger g‖`. -/
theorem norm_comp_dagger_sq_le (f : X ⟶ Y) (g : Z ⟶ Y) :
    ‖f ≫ dagger g‖ ^ 2 ≤ ‖f ≫ dagger f‖ * ‖g ≫ dagger g‖ := by
  calc
    ‖f ≫ dagger g‖ ^ 2 ≤ (‖f‖ * ‖dagger g‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_comp_le' f (dagger g)) 2
    _ = ‖f‖ ^ 2 * ‖g‖ ^ 2 := by rw [norm_dagger, mul_pow]
    _ = ‖f ≫ dagger f‖ * ‖g ≫ dagger g‖ := by
      rw [norm_comp_dagger_self, norm_comp_dagger_self]

/-- Norm Cauchy–Schwarz inequality for `dagger f ≫ g`:
`‖dagger f ≫ g‖ ^ 2 ≤ ‖dagger f ≫ f‖ * ‖dagger g ≫ g‖`. -/
theorem norm_dagger_comp_sq_le (f : Y ⟶ X) (g : Y ⟶ Z) :
    ‖dagger f ≫ g‖ ^ 2 ≤ ‖dagger f ≫ f‖ * ‖dagger g ≫ g‖ := by
  simpa only [dagger_dagger] using norm_comp_dagger_sq_le (dagger f) (dagger g)

/-- Polarization norm bound on `f ≫ dagger g` in terms of the four polarized combinations. -/
theorem norm_comp_dagger_le_polarization (f g : X ⟶ Y) :
    ‖f ≫ dagger g‖ ≤
      (4 : ℝ)⁻¹ * (‖f + g‖ ^ 2 + ‖f - g‖ ^ 2 +
        ‖f + Complex.I • g‖ ^ 2 + ‖f - Complex.I • g‖ ^ 2) := by
  rw [comp_dagger_eq_polarization f g, norm_smul]
  have h4 : ‖(4 : ℂ)⁻¹‖ = (4 : ℝ)⁻¹ := by norm_num
  rw [h4]
  gcongr
  calc
    ‖(f + g) ≫ dagger (f + g) - (f - g) ≫ dagger (f - g) +
        Complex.I • ((f + Complex.I • g) ≫ dagger (f + Complex.I • g) -
          (f - Complex.I • g) ≫ dagger (f - Complex.I • g))‖
      ≤ ‖(f + g) ≫ dagger (f + g) - (f - g) ≫ dagger (f - g)‖ +
          ‖Complex.I • ((f + Complex.I • g) ≫ dagger (f + Complex.I • g) -
            (f - Complex.I • g) ≫ dagger (f - Complex.I • g))‖ := norm_add_le _ _
    _ ≤ (‖(f + g) ≫ dagger (f + g)‖ + ‖(f - g) ≫ dagger (f - g)‖) +
          (‖(f + Complex.I • g) ≫ dagger (f + Complex.I • g)‖ +
            ‖(f - Complex.I • g) ≫ dagger (f - Complex.I • g)‖) := by
        rw [norm_smul, Complex.norm_I, one_mul]
        exact add_le_add (norm_sub_le _ _) (norm_sub_le _ _)
    _ = ‖f + g‖ ^ 2 + ‖f - g‖ ^ 2 +
          ‖f + Complex.I • g‖ ^ 2 + ‖f - Complex.I • g‖ ^ 2 := by
        simp only [norm_comp_dagger_self, add_assoc]

/-! ### Continuous bilinear composition and closed Hom-space kernels -/

/-- Categorical composition bundled as a continuous `ℂ`-bilinear map of norm at most `1`,
built from `CategoryTheory.Linear.comp`. -/
def compCLM (X Y Z : C) : (X ⟶ Y) →L[ℂ] (Y ⟶ Z) →L[ℂ] (X ⟶ Z) :=
  (Linear.comp X Y Z : (X ⟶ Y) →ₗ[ℂ] (Y ⟶ Z) →ₗ[ℂ] (X ⟶ Z)).mkContinuous₂ 1 fun f g => by
    simpa only [Linear.comp_apply, Linear.leftComp_apply, one_mul] using norm_comp_le' f g

/-- Evaluation of `compCLM` is categorical composition. -/
@[simp] theorem compCLM_apply (f : X ⟶ Y) (g : Y ⟶ Z) :
    compCLM X Y Z f g = f ≫ g := (rfl)

/-- The bilinear composition operator has norm at most `1`. -/
theorem norm_compCLM_le (X Y Z : C) : ‖compCLM X Y Z‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

/-- Categorical composition is jointly continuous on Hom spaces. -/
theorem continuous_comp (X Y Z : C) :
    Continuous (fun p : (X ⟶ Y) × (Y ⟶ Z) => p.1 ≫ p.2) :=
  (compCLM X Y Z).continuous₂

/-- Pre-composition with `f : X ⟶ Y` as a continuous linear map `(Y ⟶ Z) →L[ℂ] (X ⟶ Z)`. -/
def leftCompCLM (Z : C) (f : X ⟶ Y) : (Y ⟶ Z) →L[ℂ] (X ⟶ Z) :=
  compCLM X Y Z f

/-- Evaluation of `leftCompCLM` is pre-composition with `f`. -/
@[simp] theorem leftCompCLM_apply (Z : C) (f : X ⟶ Y) (g : Y ⟶ Z) :
    leftCompCLM Z f g = f ≫ g := (rfl)

/-- Forgetting continuity from `leftCompCLM` recovers `CategoryTheory.Linear.leftComp`. -/
@[simp] theorem leftCompCLM_toLinearMap (Z : C) (f : X ⟶ Y) :
    (leftCompCLM Z f).toLinearMap = Linear.leftComp ℂ Z f := by
  ext g; rfl

/-- The operator norm of pre-composition by `f` is bounded by `‖f‖`. -/
theorem norm_leftCompCLM_le (Z : C) (f : X ⟶ Y) : ‖leftCompCLM Z f‖ ≤ ‖f‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f) fun g => norm_comp_le' f g

/-- Pre-composition `(Y ⟶ X) →L[ℂ] (X ⟶ X)` by `f : X ⟶ Y` has operator norm equal to `‖f‖`. -/
@[simp] theorem norm_leftCompCLM_self (f : X ⟶ Y) : ‖leftCompCLM X f‖ = ‖f‖ := by
  refine le_antisymm (norm_leftCompCLM_le X f) ?_
  by_cases hf : ‖f‖ = 0
  · simp [hf]
  · have hpos : 0 < ‖f‖ := lt_of_le_of_ne (norm_nonneg f) (Ne.symm hf)
    refine le_of_mul_le_mul_right ?_ hpos
    calc
      ‖f‖ * ‖f‖ = ‖leftCompCLM X f (dagger f)‖ := (norm_comp_dagger_self' f).symm
      _ ≤ ‖leftCompCLM X f‖ * ‖dagger f‖ := (leftCompCLM X f).le_opNorm (dagger f)
      _ = ‖leftCompCLM X f‖ * ‖f‖ := by rw [norm_dagger]

/-- Post-composition with `g : Y ⟶ Z` as a continuous linear map `(X ⟶ Y) →L[ℂ] (X ⟶ Z)`. -/
def rightCompCLM (X : C) (g : Y ⟶ Z) : (X ⟶ Y) →L[ℂ] (X ⟶ Z) :=
  (compCLM X Y Z).flip g

/-- Evaluation of `rightCompCLM` is post-composition with `g`. -/
@[simp] theorem rightCompCLM_apply (X : C) (g : Y ⟶ Z) (f : X ⟶ Y) :
    rightCompCLM X g f = f ≫ g := (rfl)

/-- Forgetting continuity from `rightCompCLM` recovers `CategoryTheory.Linear.rightComp`. -/
@[simp] theorem rightCompCLM_toLinearMap (X : C) (g : Y ⟶ Z) :
    (rightCompCLM X g).toLinearMap = Linear.rightComp ℂ X g := by
  ext f; rfl

/-- The operator norm of post-composition by `g` is bounded by `‖g‖`. -/
theorem norm_rightCompCLM_le (X : C) (g : Y ⟶ Z) : ‖rightCompCLM X g‖ ≤ ‖g‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg g) fun f => norm_comp_le f g

/-- Post-composition `(Z ⟶ Y) →L[ℂ] (Z ⟶ Z)` by `g : Y ⟶ Z` has operator norm equal to `‖g‖`. -/
@[simp] theorem norm_rightCompCLM_self (g : Y ⟶ Z) : ‖rightCompCLM Z g‖ = ‖g‖ := by
  refine le_antisymm (norm_rightCompCLM_le Z g) ?_
  by_cases hg : ‖g‖ = 0
  · simp [hg]
  · have hpos : 0 < ‖g‖ := lt_of_le_of_ne (norm_nonneg g) (Ne.symm hg)
    refine le_of_mul_le_mul_right ?_ hpos
    calc
      ‖g‖ * ‖g‖ = ‖rightCompCLM Z g (dagger g)‖ := (norm_dagger_comp_self' g).symm
      _ ≤ ‖rightCompCLM Z g‖ * ‖dagger g‖ := (rightCompCLM Z g).le_opNorm (dagger g)
      _ = ‖rightCompCLM Z g‖ * ‖g‖ := by rw [norm_dagger]

/-- Any continuous linear map out of a Hom space into a `T₁` topological module has closed kernel
subspace, making that kernel a complete Banach subspace of `X ⟶ Y`. -/
theorem isClosed_ker_hom {E : Type*} [TopologicalSpace E] [T1Space E] [AddCommMonoid E]
    [Module ℂ E] (L : (X ⟶ Y) →L[ℂ] E) : IsClosed (L.ker : Set (X ⟶ Y)) :=
  L.isClosed_ker

/-- The right-annihilator `{g : Y ⟶ Z | f ≫ g = 0}` of `f : X ⟶ Y` is closed in `Y ⟶ Z`. -/
theorem isClosed_rightAnnihilator (Z : C) (f : X ⟶ Y) :
    IsClosed {g : Y ⟶ Z | f ≫ g = 0} :=
  (leftCompCLM Z f).isClosed_ker

/-- The left-annihilator `{f : X ⟶ Y | f ≫ g = 0}` of `g : Y ⟶ Z` is closed in `X ⟶ Y`. -/
theorem isClosed_leftAnnihilator (X : C) (g : Y ⟶ Z) :
    IsClosed {f : X ⟶ Y | f ≫ g = 0} :=
  (rightCompCLM X g).isClosed_ker

/-- The space of intertwiners `{h : X ⟶ Y | a ≫ h = h ≫ b}` between endomorphisms `a` and `b`
is closed in `X ⟶ Y`. -/
theorem isClosed_intertwiner (a : X ⟶ X) (b : Y ⟶ Y) :
    IsClosed {h : X ⟶ Y | a ≫ h = h ≫ b} := by
  have hset : {h : X ⟶ Y | a ≫ h = h ≫ b} =
      ((leftCompCLM Y a - rightCompCLM X b).ker : Set (X ⟶ Y)) := by
    ext h
    simp [sub_eq_zero]
  rw [hset]
  exact (leftCompCLM Y a - rightCompCLM X b).isClosed_ker

/-! ### Identity, unitary, projection, and zero-object norm formulas -/

/-- Every self-adjoint idempotent `p : X ⟶ X` in a C*-category has norm `0` or `1`. -/
theorem norm_eq_zero_or_one_of_idempotent_of_dagger {p : X ⟶ X}
    (hp : p ≫ p = p) (hsa : dagger p = p) : ‖p‖ = 0 ∨ ‖p‖ = 1 := by
  have hsq : ‖p‖ ^ 2 = ‖p‖ := by
    calc
      ‖p‖ ^ 2 = ‖p ≫ dagger p‖ := (norm_comp_dagger_self p).symm
      _ = ‖p‖ := by rw [hsa, hp]
  by_cases h0 : ‖p‖ = 0
  · exact Or.inl h0
  · exact Or.inr (mul_left_cancel₀ h0 (by simpa [sq] using hsq))

/-- A nonzero self-adjoint idempotent has norm `1`. -/
theorem norm_eq_one_of_idempotent_of_dagger {p : X ⟶ X}
    (hp : p ≫ p = p) (hsa : dagger p = p) (hp0 : p ≠ 0) : ‖p‖ = 1 :=
  (norm_eq_zero_or_one_of_idempotent_of_dagger hp hsa).resolve_left (norm_ne_zero_iff.mpr hp0)

/-- Every self-adjoint idempotent is a contraction (`‖p‖ ≤ 1`). -/
theorem norm_le_one_of_idempotent_of_dagger {p : X ⟶ X}
    (hp : p ≫ p = p) (hsa : dagger p = p) : ‖p‖ ≤ 1 := by
  rcases norm_eq_zero_or_one_of_idempotent_of_dagger hp hsa with h | h <;> linarith

/-- The identity arrow of any object in a C*-category has norm `0` or `1`. -/
theorem norm_id_eq_zero_or_one (X : C) : ‖(𝟙 X : X ⟶ X)‖ = 0 ∨ ‖(𝟙 X : X ⟶ X)‖ = 1 :=
  norm_eq_zero_or_one_of_idempotent_of_dagger (Category.id_comp (𝟙 X)) (dagger_id X)

/-- Every identity arrow has norm at most `1`. -/
theorem norm_id_le_one (X : C) : ‖(𝟙 X : X ⟶ X)‖ ≤ 1 :=
  norm_le_one_of_idempotent_of_dagger (Category.id_comp (𝟙 X)) (dagger_id X)

/-- Every arrow out of a zero object has norm `0`. -/
theorem _root_.CategoryTheory.Limits.IsZero.norm_hom_left (hX : IsZero X) (f : X ⟶ Y) :
    ‖f‖ = 0 := by
  rw [hX.eq_of_src f 0, norm_zero]

/-- Every arrow into a zero object has norm `0`. -/
theorem _root_.CategoryTheory.Limits.IsZero.norm_hom_right (hY : IsZero Y) (f : X ⟶ Y) :
    ‖f‖ = 0 := by
  rw [hY.eq_of_tgt f 0, norm_zero]

/-- The identity arrow of a zero object has norm `0`. -/
theorem _root_.CategoryTheory.Limits.IsZero.norm_id (hX : IsZero X) :
    ‖(𝟙 X : X ⟶ X)‖ = 0 :=
  hX.norm_hom_left (𝟙 X)

/-- An object in a C*-category is a zero object precisely when its identity arrow has norm `0`. -/
theorem isZero_iff_norm_id_eq_zero (X : C) : IsZero X ↔ ‖(𝟙 X : X ⟶ X)‖ = 0 := by
  rw [IsZero.iff_id_eq_zero, norm_eq_zero]

/-- An object in a C*-category is nonzero precisely when its identity arrow has norm `1`. -/
theorem not_isZero_iff_norm_id_eq_one (X : C) : ¬ IsZero X ↔ ‖(𝟙 X : X ⟶ X)‖ = 1 := by
  rw [isZero_iff_norm_id_eq_zero]
  rcases norm_id_eq_zero_or_one X with h | h <;> simp [h]

/-- If `X ⟶ X` is nontrivial, the identity arrow `𝟙 X` has norm `1`. -/
@[simp] theorem norm_id_of_nontrivial (X : C) [Nontrivial (X ⟶ X)] :
    ‖(𝟙 X : X ⟶ X)‖ = 1 := by
  refine (not_isZero_iff_norm_id_eq_one X).mp fun hX => ?_
  obtain ⟨f, g, hfg⟩ := exists_pair_ne (X ⟶ X)
  exact hfg (hX.eq_of_src f g)

/-- In a C*-category with a chosen zero object `0`, `‖𝟙 (0 : C)‖ = 0`. -/
theorem norm_id_zero_object [HasZeroObject C] :
    ‖(𝟙 (0 : C) : (0 : C) ⟶ 0)‖ = 0 :=
  (isZero_zero C).norm_id

/-- Pre-composing with an arrow satisfying `dagger u ≫ u = 𝟙 Y` preserves norms. -/
theorem norm_comp_of_dagger_comp_id {u : X ⟶ Y} (hu : dagger u ≫ u = 𝟙 Y) (g : Y ⟶ Z) :
    ‖u ≫ g‖ = ‖g‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← norm_dagger_comp_self,
    ← norm_dagger_comp_self g, dagger_comp, Category.assoc, ← Category.assoc (dagger u) u g,
    hu, Category.id_comp]

/-- Post-composing with an arrow satisfying `u ≫ dagger u = 𝟙 X` preserves norms. -/
theorem norm_comp_of_comp_dagger_id {u : X ⟶ Y} (hu : u ≫ dagger u = 𝟙 X) (f : W ⟶ X) :
    ‖f ≫ u‖ = ‖f‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← norm_comp_dagger_self,
    ← norm_comp_dagger_self f, dagger_comp, Category.assoc, ← Category.assoc u (dagger u),
    hu, Category.id_comp]

/-- Pre-composing with a unitary arrow preserves norms. -/
@[simp] theorem _root_.TauCeti.IsUnitary.norm_comp_left {u : X ⟶ Y} (hu : IsUnitary u)
    (g : Y ⟶ Z) : ‖u ≫ g‖ = ‖g‖ :=
  norm_comp_of_dagger_comp_id hu.dagger_hom_id g

/-- Post-composing with a unitary arrow preserves norms. -/
@[simp] theorem _root_.TauCeti.IsUnitary.norm_comp_right {u : X ⟶ Y} (hu : IsUnitary u)
    (f : W ⟶ X) : ‖f ≫ u‖ = ‖f‖ :=
  norm_comp_of_comp_dagger_id hu.hom_dagger_id f

/-- The norm of a unitary arrow `u : X ⟶ Y` equals `‖𝟙 X‖` (`1` when `X` is nonzero, `0` when `X`
is a zero object). -/
theorem _root_.TauCeti.IsUnitary.norm_eq_norm_id {u : X ⟶ Y} (hu : IsUnitary u) :
    ‖u‖ = ‖(𝟙 X : X ⟶ X)‖ := by
  have hsq : ‖u‖ ^ 2 = ‖(𝟙 X : X ⟶ X)‖ ^ 2 := by
    calc
      ‖u‖ ^ 2 = ‖u ≫ dagger u‖ := (norm_comp_dagger_self u).symm
      _ = ‖(𝟙 X : X ⟶ X)‖ := by rw [hu.hom_dagger_id]
      _ = ‖(𝟙 X : X ⟶ X)‖ ^ 2 := by
        rcases norm_id_eq_zero_or_one X with h | h <;> simp [h]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Every unitary arrow is a contraction (`‖u‖ ≤ 1`). -/
theorem _root_.TauCeti.IsUnitary.norm_le_one {u : X ⟶ Y} (hu : IsUnitary u) : ‖u‖ ≤ 1 :=
  hu.norm_eq_norm_id.trans_le (norm_id_le_one X)

/-- A unitary arrow out of an object with nontrivial endomorphisms has norm `1`. -/
theorem _root_.TauCeti.IsUnitary.norm_eq_one {u : X ⟶ Y} (hu : IsUnitary u)
    [Nontrivial (X ⟶ X)] : ‖u‖ = 1 := by
  rw [hu.norm_eq_norm_id, norm_id_of_nontrivial]

end CStarCategory

end TauCeti
