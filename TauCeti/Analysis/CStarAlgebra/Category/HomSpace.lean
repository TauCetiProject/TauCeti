/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import TauCeti.Analysis.CStarAlgebra.Category.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Continuous linear maps, isometries, and closed subspaces on Hom spaces

Because `TauCeti.CStarCategory` does not register global `NormedAddCommGroup` instances on Hom
types (to avoid metric/uniformity diamonds on concrete categories such as `TauCeti.HilbertCat`),
this file develops the metric, topological, and continuous-linear-map API on each Hom space
equipped with its canonical norm-induced structures `CStarCategory.normedAddCommGroup` and
`CStarCategory.normedSpace`. These are activated only as local instances inside this module so no
global instances leak to downstream importers.

## Main declarations

* `TauCeti.CStarCategory.dist_dagger`, `isometry_dagger`, `continuous_dagger`,
  `daggerLinearIsometryEquiv`: taking the dagger is a conjugate-linear isometric equivalence
  between opposite Hom spaces.
* `TauCeti.CStarCategory.compCLM`, `leftCompCLM`, `rightCompCLM`: categorical composition as a
  norm-contractive continuous `ℂ`-bilinear map, with exact operator norms `‖leftCompCLM X f‖ = ‖f‖`
  and `‖rightCompCLM Z g‖ = ‖g‖`.
* `TauCeti.CStarCategory.isClosed_rightAnnihilator`, `isClosed_leftAnnihilator`,
  `isClosed_intertwiner`: annihilators and intertwiner spaces are norm-closed subspaces.
* `CategoryTheory.End.linearIsometryEquiv`: `End X ≃ₗᵢ[ℂ] (X ⟶ X)`.

## References

* P. Ghez, R. Lima, J. E. Roberts, *W\*-categories*, Pacific J. Math. 120 (1985), 79–109.
* P. D. Mitchener, *C\*-categories*, Proc. London Math. Soc. (3) 84 (2002), 375–404.
-/

public section

noncomputable section

open CategoryTheory

universe v u

namespace TauCeti.CStarCategory

attribute [local instance] normedAddCommGroup normedSpace

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C]
  [∀ X Y : C, Norm (X ⟶ Y)] [CStarCategory C]
variable {X Y Z : C}

/-! ### Dagger as a conjugate-linear isometry -/

/-- Taking the dagger preserves the nonnegative norm on Hom spaces. -/
@[simp] theorem nnNorm_dagger (f : X ⟶ Y) :
    ‖dagger f‖₊ = ‖f‖₊ :=
  Subtype.ext (norm_dagger f)

/-- Taking the dagger preserves distances on Hom spaces under the norm-induced metric. -/
@[simp] theorem dist_dagger (f g : X ⟶ Y) :
    dist (dagger f) (dagger g) = dist f g := by
  rw [dist_eq_norm, dist_eq_norm, ← dagger_sub, norm_dagger]

/-- Taking the dagger is an isometry between opposite Hom spaces. -/
theorem isometry_dagger (X Y : C) :
    Isometry (dagger : (X ⟶ Y) → (Y ⟶ X)) :=
  Isometry.of_dist_eq dist_dagger

/-- Taking the dagger is continuous on Hom spaces. -/
@[fun_prop] theorem continuous_dagger (X Y : C) :
    Continuous (dagger : (X ⟶ Y) → (Y ⟶ X)) :=
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

/-! ### Continuous bilinear composition, annihilators, and intertwiners -/

/-- Categorical composition bundled as a continuous `ℂ`-bilinear map of norm at most `1`,
built from `CategoryTheory.Linear.comp`. -/
def compCLM (X Y Z : C) : (X ⟶ Y) →L[ℂ] (Y ⟶ Z) →L[ℂ] (X ⟶ Z) :=
  (Linear.comp X Y Z : (X ⟶ Y) →ₗ[ℂ] (Y ⟶ Z) →ₗ[ℂ] (X ⟶ Z)).mkContinuous₂ 1 fun f g => by
    simpa only [Linear.comp_apply, Linear.leftComp_apply, one_mul] using norm_comp_le f g

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
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f) fun g => norm_comp_le f g

/-- Pre-composition `(Y ⟶ X) →L[ℂ] (X ⟶ X)` by `f : X ⟶ Y` has operator norm equal to `‖f‖`. -/
@[simp] theorem norm_leftCompCLM_self (f : X ⟶ Y) : ‖leftCompCLM X f‖ = ‖f‖ := by
  refine le_antisymm (norm_leftCompCLM_le X f) ?_
  by_cases hf : ‖f‖ = 0
  · simp [hf]
  · have hpos : 0 < ‖f‖ := lt_of_le_of_ne (norm_nonneg f) (Ne.symm hf)
    refine le_of_mul_le_mul_right ?_ hpos
    calc
      ‖f‖ * ‖f‖ = ‖leftCompCLM X f (dagger f)‖ := by
        rw [leftCompCLM_apply, norm_self_comp_dagger, sq]
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
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg g) fun f => by
    simpa [mul_comm] using norm_comp_le f g

/-- Post-composition `(Z ⟶ Y) →L[ℂ] (Z ⟶ Z)` by `g : Y ⟶ Z` has operator norm equal to `‖g‖`. -/
@[simp] theorem norm_rightCompCLM_self (g : Y ⟶ Z) : ‖rightCompCLM Z g‖ = ‖g‖ := by
  refine le_antisymm (norm_rightCompCLM_le Z g) ?_
  by_cases hg : ‖g‖ = 0
  · simp [hg]
  · have hpos : 0 < ‖g‖ := lt_of_le_of_ne (norm_nonneg g) (Ne.symm hg)
    refine le_of_mul_le_mul_right ?_ hpos
    calc
      ‖g‖ * ‖g‖ = ‖rightCompCLM Z g (dagger g)‖ := by
        rw [rightCompCLM_apply, norm_dagger_comp_self, sq]
      _ ≤ ‖rightCompCLM Z g‖ * ‖dagger g‖ := (rightCompCLM Z g).le_opNorm (dagger g)
      _ = ‖rightCompCLM Z g‖ * ‖g‖ := by rw [norm_dagger]

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

end TauCeti.CStarCategory

namespace CategoryTheory.End

open TauCeti

attribute [local instance] CStarCategory.normedAddCommGroup CStarCategory.normedSpace

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C]
  [∀ X Y : C, Norm (X ⟶ Y)] [CStarCategory C]

/-- Distance on underlying arrows agrees with distance in `End X`. -/
@[simp] theorem dist_asHom {X : C} (a b : End X) : dist a.asHom b.asHom = dist a b := by
  rw [dist_eq_norm, dist_eq_norm, End.norm_def, End.sub_asHom]

/-- Bundling endomorphism arrows preserves distance. -/
@[simp] theorem dist_of {X : C} (f g : X ⟶ X) : dist (End.of f) (End.of g) = dist f g := by
  rw [dist_eq_norm, dist_eq_norm, ← End.norm_of (f - g)]
  rfl

/-- `End.asHom` and `End.of` form a `ℂ`-linear isometric equivalence between `End X` and
`X ⟶ X` (with its norm-induced structure). -/
def linearIsometryEquiv (X : C) : End X ≃ₗᵢ[ℂ] (X ⟶ X) :=
  linearIsometryEquivOf (CStarCategory.normedSpaceCore X X)

/-- Forward evaluation of `End.linearIsometryEquiv`. -/
@[simp] theorem linearIsometryEquiv_apply {X : C} (a : End X) :
    linearIsometryEquiv X a = a.asHom := (rfl)

/-- Inverse evaluation of `End.linearIsometryEquiv`. -/
@[simp] theorem linearIsometryEquiv_symm_apply {X : C} (f : X ⟶ X) :
    (linearIsometryEquiv X).symm f = End.of f := (rfl)

end CategoryTheory.End
