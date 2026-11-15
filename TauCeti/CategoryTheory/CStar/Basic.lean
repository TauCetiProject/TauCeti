/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Module.Basic
public import TauCeti.CategoryTheory.Dagger.Endomorphism

/-!
# C⋆-categories

A C⋆-category is a complex-linear dagger category whose Hom spaces are complex Banach spaces such
that categorical composition is contractive (`‖f ≫ g‖ ≤ ‖g‖ * ‖f‖`), every arrow satisfies the
C⋆-identity (`‖f ≫ dagger f‖ = ‖f‖ ^ 2`, stated as the lower bound `‖f‖ * ‖f‖ ≤ ‖f ≫ dagger f‖`
matching `CStarRing`), and `f ≫ dagger f` is positive in `CategoryTheory.End X`.

Using Mathlib's operator-order multiplication on `End X`, each endomorphism algebra inherits a
compatible unital `CStarAlgebra` structure together with its spectral order
`CStarAlgebra.spectralOrder`. Positivity of `f ≫ dagger f` is stated in the class as the
existence of an endomorphism `h : X ⟶ X` with `f ≫ dagger f = h ≫ dagger h` so that no preliminary
algebraic or order instances are needed in the class signature; once `CStarAlgebra (End X)` is
established, this is equivalent both to `0 ≤ End.of (f ≫ dagger f)` in the spectral order and to
nonnegativity of the spectrum of `End.of (f ≫ dagger f)` (`TauCeti.CStarCategory.ofSpectrumNonneg`).

Each Hom space `X ⟶ Y` carries canonical left `End Y` and right `End X` Hilbert C⋆-module
structures (`CStarModule (End Y) (X ⟶ Y)` and `CStarModule (End X)ᵐᵒᵖ (X ⟶ Y)`), yielding the
endomorphism-valued Cauchy–Schwarz inequalities, norm recovery over the closed unit ball,
inner-product extensionality, and the polarization identities.

## Main declarations

* `TauCeti.CStarCategory`: C⋆-category structure on a native `ℂ`-linear dagger category.
* `TauCeti.CStarCategory.ofSpectrumNonneg`: constructor from spectral nonnegativity of
  `End.of (f ≫ dagger f)`.
* `TauCeti.daggerLinearIsometryEquiv`: the dagger as a conjugate-linear isometric equivalence
  `(X ⟶ Y) ≃ₗᵢ⋆[ℂ] (Y ⟶ X)`.
* `TauCeti.compCLM`, `TauCeti.leftCompCLM`, `TauCeti.rightCompCLM`: categorical composition
  bundled as contractive continuous `ℂ`-linear maps, with closed kernels.
* `CategoryTheory.End.instCStarAlgebra`, `CategoryTheory.End.linearIsometryEquiv`: the compatible
  unital C⋆-algebra structure and spectral order on `End X`.
* `TauCeti.norm_id_eq_zero_or_one`, `TauCeti.IsUnitary.norm_eq_one`,
  `TauCeti.norm_le_one_of_idempotent_of_dagger_eq`: norm formulas for identities, zero objects,
  unitary arrows, and self-adjoint projections.
* `TauCeti.instCStarModuleEndHom`, `TauCeti.instCStarModuleOpEndHom`: left and right Hilbert
  C⋆-module structures on Hom spaces, together with categorical Cauchy–Schwarz and polarization.

## References

* P. Ghez, R. Lima, and J. E. Roberts, *W⋆-categories*, Pacific J. Math. 120 (1985), 79–109.
-/

public section

noncomputable section

open CategoryTheory MulOpposite Complex
open scoped NNReal

universe v u

namespace TauCeti

/-- A C⋆-category structure on a complex-linear dagger category: Banach Hom spaces, contractive
composition, the C⋆-norm estimate `‖f‖ * ‖f‖ ≤ ‖f ≫ dagger f‖` (from which `‖dagger f‖ = ‖f‖` and
`‖f ≫ dagger f‖ = ‖f‖ ^ 2` follow), and positivity of `f ≫ dagger f` in `End X`. -/
class CStarCategory (C : Type u) [Category.{v} C] [Preadditive C] [Linear ℂ C]
    [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C] where
  /-- Norm on each Hom space. -/
  [homNorm : ∀ X Y : C, Norm (X ⟶ Y)]
  /-- Metric space structure on each Hom space. -/
  [homMetricSpace : ∀ X Y : C, MetricSpace (X ⟶ Y)]
  /-- Completeness of each Hom space. -/
  [homCompleteSpace : ∀ X Y : C, CompleteSpace (X ⟶ Y)]
  /-- The distance on each Hom space is induced by its norm. -/
  dist_eq : ∀ {X Y : C} (f g : X ⟶ Y), dist f g = ‖-f + g‖ := by
    intros; exact dist_eq_norm_neg_add _ _
  /-- Complex scalar multiplication on Hom spaces is bounded. -/
  norm_smul_le : ∀ {X Y : C} (c : ℂ) (f : X ⟶ Y), ‖c • f‖ ≤ ‖c‖ * ‖f‖
  /-- Categorical composition is contractive. -/
  norm_comp_le : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), ‖f ≫ g‖ ≤ ‖g‖ * ‖f‖
  /-- Lower C⋆-bound on `f ≫ dagger f`; equality is `TauCeti.norm_self_comp_dagger`. -/
  norm_mul_self_le : ∀ {X Y : C} (f : X ⟶ Y), ‖f‖ * ‖f‖ ≤ ‖f ≫ dagger f‖
  /-- Every `f ≫ dagger f` factors as `h ≫ dagger h` for an endomorphism `h : X ⟶ X`, expressing
  positivity of `End.of (f ≫ dagger f)` in `End X`. -/
  exists_comp_dagger_eq : ∀ {X Y : C} (f : X ⟶ Y), ∃ h : X ⟶ X, f ≫ dagger f = h ≫ dagger h

section Basic

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C] [CStarCategory C]
variable {W X Y Z : C}

instance (priority := 100) instNormHom (X Y : C) : Norm (X ⟶ Y) :=
  CStarCategory.homNorm X Y

instance (priority := 100) instMetricSpaceHom (X Y : C) : MetricSpace (X ⟶ Y) :=
  CStarCategory.homMetricSpace X Y

instance (priority := 100) instCompleteSpaceHom (X Y : C) : CompleteSpace (X ⟶ Y) :=
  CStarCategory.homCompleteSpace X Y

instance (priority := 100) instNormedAddCommGroupHom (X Y : C) : NormedAddCommGroup (X ⟶ Y) where
  dist_eq := CStarCategory.dist_eq

instance (priority := 100) instNormedSpaceHom (X Y : C) : NormedSpace ℂ (X ⟶ Y) where
  norm_smul_le := CStarCategory.norm_smul_le

/-- Categorical composition is submultiplicative in operator order: `‖f ≫ g‖ ≤ ‖g‖ * ‖f‖`. -/
theorem norm_comp_le (f : X ⟶ Y) (g : Y ⟶ Z) : ‖f ≫ g‖ ≤ ‖g‖ * ‖f‖ :=
  CStarCategory.norm_comp_le f g

/-- Categorical composition is submultiplicative in diagram order: `‖f ≫ g‖ ≤ ‖f‖ * ‖g‖`. -/
theorem norm_comp_le' (f : X ⟶ Y) (g : Y ⟶ Z) : ‖f ≫ g‖ ≤ ‖f‖ * ‖g‖ :=
  (norm_comp_le f g).trans_eq (mul_comm _ _)

/-- Nonnegative-real norm submultiplicativity for categorical composition. -/
theorem nnNorm_comp_le (f : X ⟶ Y) (g : Y ⟶ Z) : ‖f ≫ g‖₊ ≤ ‖g‖₊ * ‖f‖₊ :=
  norm_comp_le f g

private theorem norm_dagger_le (f : X ⟶ Y) : ‖dagger f‖ ≤ ‖f‖ := by
  obtain (hf | hf) := eq_zero_or_norm_pos (dagger f)
  · simp [hf]
  · refine le_of_mul_le_mul_right ?_ hf
    calc ‖dagger f‖ * ‖dagger f‖ ≤ ‖dagger f ≫ dagger (dagger f)‖ :=
          CStarCategory.norm_mul_self_le (dagger f)
      _ = ‖dagger f ≫ f‖ := by simp
      _ ≤ ‖f‖ * ‖dagger f‖ := norm_comp_le _ _

/-- The dagger involution is isometric on Hom spaces. -/
@[simp] theorem norm_dagger (f : X ⟶ Y) : ‖dagger f‖ = ‖f‖ :=
  le_antisymm (norm_dagger_le f) (by simpa using norm_dagger_le (dagger f))

/-- The dagger involution preserves `nnNorm` on Hom spaces. -/
@[simp] theorem nnNorm_dagger (f : X ⟶ Y) : ‖dagger f‖₊ = ‖f‖₊ :=
  Subtype.ext (norm_dagger f)

/-- The dagger bundled as a conjugate-linear isometric equivalence of opposite Hom spaces. -/
def daggerLinearIsometryEquiv (X Y : C) : (X ⟶ Y) ≃ₗᵢ⋆[ℂ] (Y ⟶ X) where
  toFun := dagger
  invFun := dagger
  left_inv := dagger_dagger
  right_inv := dagger_dagger
  map_add' := dagger_add
  map_smul' := dagger_smul
  norm_map' := norm_dagger

/-- Evaluation of `daggerLinearIsometryEquiv`. -/
@[simp] theorem daggerLinearIsometryEquiv_apply (f : X ⟶ Y) :
    daggerLinearIsometryEquiv X Y f = dagger f := (rfl)

/-- The inverse of `daggerLinearIsometryEquiv` reverses its endpoints. -/
@[simp] theorem daggerLinearIsometryEquiv_symm (X Y : C) :
    (daggerLinearIsometryEquiv X Y).symm = daggerLinearIsometryEquiv Y X := (rfl)

/-- Forgetting norms from `daggerLinearIsometryEquiv` recovers `daggerLinearEquiv`. -/
@[simp] theorem daggerLinearIsometryEquiv_toLinearEquiv (X Y : C) :
    (daggerLinearIsometryEquiv X Y).toLinearEquiv = daggerLinearEquiv ℂ X Y := by
  ext
  simp

/-- Taking daggers is an isometry between opposite Hom spaces. -/
theorem isometry_dagger (X Y : C) : Isometry (dagger : (X ⟶ Y) → (Y ⟶ X)) :=
  (daggerLinearIsometryEquiv X Y).isometry

/-- The C⋆-identity in categorical composition order: `‖f ≫ dagger f‖ = ‖f‖ ^ 2`. -/
@[simp] theorem norm_self_comp_dagger (f : X ⟶ Y) : ‖f ≫ dagger f‖ = ‖f‖ ^ 2 := by
  rw [sq]
  exact le_antisymm ((norm_comp_le f (dagger f)).trans_eq (by rw [norm_dagger]))
    (CStarCategory.norm_mul_self_le f)

/-- The dual C⋆-identity: `‖dagger f ≫ f‖ = ‖f‖ ^ 2`. -/
@[simp] theorem norm_dagger_comp_self (f : X ⟶ Y) : ‖dagger f ≫ f‖ = ‖f‖ ^ 2 := by
  simpa using norm_self_comp_dagger (dagger f)

/-- The `nnNorm` C⋆-identity `‖f ≫ dagger f‖₊ = ‖f‖₊ ^ 2`. -/
@[simp] theorem nnNorm_self_comp_dagger (f : X ⟶ Y) : ‖f ≫ dagger f‖₊ = ‖f‖₊ ^ 2 :=
  Subtype.ext (by simp)

/-- The dual `nnNorm` C⋆-identity `‖dagger f ≫ f‖₊ = ‖f‖₊ ^ 2`. -/
@[simp] theorem nnNorm_dagger_comp_self (f : X ⟶ Y) : ‖dagger f ≫ f‖₊ = ‖f‖₊ ^ 2 :=
  Subtype.ext (by simp)

/-- `f ≫ dagger f = 0` holds precisely when `f = 0`. -/
@[simp] theorem self_comp_dagger_eq_zero (f : X ⟶ Y) : f ≫ dagger f = 0 ↔ f = 0 := by
  rw [← norm_eq_zero, norm_self_comp_dagger, sq_eq_zero_iff, norm_eq_zero]

/-- `dagger f ≫ f = 0` holds precisely when `f = 0`. -/
@[simp] theorem dagger_comp_self_eq_zero (f : X ⟶ Y) : dagger f ≫ f = 0 ↔ f = 0 := by
  rw [← norm_eq_zero, norm_dagger_comp_self, sq_eq_zero_iff, norm_eq_zero]

/-! ### Continuous bilinear composition and closed kernels -/

/-- Categorical composition as a continuous `ℂ`-bilinear map of operator norm at most `1`. -/
def compCLM (X Y Z : C) : (X ⟶ Y) →L[ℂ] (Y ⟶ Z) →L[ℂ] (X ⟶ Z) :=
  LinearMap.mkContinuous₂
    { toFun := fun f => Linear.leftComp ℂ Z f
      map_add' := fun f₁ f₂ => by ext g; exact Preadditive.add_comp X Y Z f₁ f₂ g
      map_smul' := fun c f => by ext g; exact Linear.smul_comp X Y Z c f g }
    1 (fun f g => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Linear.leftComp_apply, one_mul]
      exact norm_comp_le' f g)

/-- Applying `compCLM` composes the two arrows. -/
@[simp] theorem compCLM_apply (f : X ⟶ Y) (g : Y ⟶ Z) : compCLM X Y Z f g = f ≫ g := (rfl)

/-- The bilinear composition operator has norm at most `1`. -/
theorem norm_compCLM_le (X Y Z : C) : ‖compCLM X Y Z‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

/-- Precomposition with `f : X ⟶ Y` as a continuous `ℂ`-linear map `(Y ⟶ Z) →L[ℂ] (X ⟶ Z)`. -/
def leftCompCLM (Z : C) (f : X ⟶ Y) : (Y ⟶ Z) →L[ℂ] (X ⟶ Z) :=
  compCLM X Y Z f

/-- Applying `leftCompCLM` precomposes by `f`. -/
@[simp] theorem leftCompCLM_apply (Z : C) (f : X ⟶ Y) (g : Y ⟶ Z) :
    leftCompCLM Z f g = f ≫ g := (rfl)

/-- The operator norm of precomposition with `f` is at most `‖f‖`. -/
theorem norm_leftCompCLM_le (Z : C) (f : X ⟶ Y) : ‖leftCompCLM Z f‖ ≤ ‖f‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f) fun g => norm_comp_le' f g

/-- Postcomposition with `g : Y ⟶ Z` as a continuous `ℂ`-linear map `(X ⟶ Y) →L[ℂ] (X ⟶ Z)`. -/
def rightCompCLM (X : C) (g : Y ⟶ Z) : (X ⟶ Y) →L[ℂ] (X ⟶ Z) :=
  (compCLM X Y Z).flip g

/-- Applying `rightCompCLM` postcomposes by `g`. -/
@[simp] theorem rightCompCLM_apply (X : C) (g : Y ⟶ Z) (f : X ⟶ Y) :
    rightCompCLM X g f = f ≫ g := (rfl)

/-- The operator norm of postcomposition with `g` is at most `‖g‖`. -/
theorem norm_rightCompCLM_le (X : C) (g : Y ⟶ Z) : ‖rightCompCLM X g‖ ≤ ‖g‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg g) fun f => norm_comp_le f g

/-- Categorical composition is jointly continuous on `Hom(X, Y) × Hom(Y, Z)`. -/
theorem continuous_comp :
    Continuous (fun p : (X ⟶ Y) × (Y ⟶ Z) => p.1 ≫ p.2) :=
  (compCLM X Y Z).isBoundedBilinearMap.continuous

/-- The subspace of arrows `g : Y ⟶ Z` annihilated on the left by `f : X ⟶ Y` is closed. -/
theorem isClosed_setOf_comp_eq_zero_right (f : X ⟶ Y) (Z : C) :
    IsClosed {g : Y ⟶ Z | f ≫ g = 0} :=
  ContinuousLinearMap.isClosed_ker (leftCompCLM Z f)

/-- The subspace of arrows `f : X ⟶ Y` annihilated on the right by `g : Y ⟶ Z` is closed. -/
theorem isClosed_setOf_comp_eq_zero_left (X : C) (g : Y ⟶ Z) :
    IsClosed {f : X ⟶ Y | f ≫ g = 0} :=
  ContinuousLinearMap.isClosed_ker (rightCompCLM X g)

end Basic

end TauCeti

/-! ### Compatible C⋆-algebra structure and spectral order on `CategoryTheory.End` -/

namespace CategoryTheory.End

open TauCeti

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C] [CStarCategory C]
variable {X Y : C}

instance instNorm (X : C) : Norm (End X) where
  norm a := ‖a.asHom‖

/-- The norm of `a : End X` equals the Hom-space norm of `a.asHom`. -/
@[simp] theorem norm_asHom (a : End X) : ‖a.asHom‖ = ‖a‖ := (rfl)

/-- Wrapping an endomorphism in `End.of` preserves its norm. -/
@[simp] theorem norm_of (f : X ⟶ X) : ‖End.of f‖ = ‖f‖ := (rfl)

instance instMetricSpace (X : C) : MetricSpace (End X) :=
  MetricSpace.induced End.asHom End.homEquiv.injective inferInstance

instance instNormedRing (X : C) : NormedRing (End X) where
  dist_eq a b := dist_eq_norm_neg_add a.asHom b.asHom
  norm_mul_le a b := norm_comp_le b.asHom a.asHom

instance instNormedAlgebra (X : C) : NormedAlgebra ℂ (End X) where
  norm_smul_le c a := norm_smul_le c a.asHom

/-- `End.linearEquiv` upgraded to a `ℂ`-linear isometric equivalence `End X ≃ₗᵢ[ℂ] (X ⟶ X)`. -/
def linearIsometryEquiv (X : C) : End X ≃ₗᵢ[ℂ] (X ⟶ X) where
  toLinearEquiv := End.linearEquiv
  norm_map' _ := (rfl)

/-- Forward evaluation of `End.linearIsometryEquiv`. -/
@[simp] theorem linearIsometryEquiv_apply (a : End X) :
    linearIsometryEquiv X a = a.asHom := (rfl)

/-- Inverse evaluation of `End.linearIsometryEquiv`. -/
@[simp] theorem linearIsometryEquiv_symm_apply (f : X ⟶ X) :
    (linearIsometryEquiv X).symm f = .of f := (rfl)

instance instCompleteSpace (X : C) : CompleteSpace (End X) :=
  (IsUniformInducing.completeSpace_congr ⟨rfl⟩ End.homEquiv.surjective).mpr inferInstance

instance instCStarRing (X : C) : CStarRing (End X) where
  norm_mul_self_le a := CStarCategory.norm_mul_self_le a.asHom

instance instCStarAlgebra (X : C) : CStarAlgebra (End X) where

instance instPartialOrder (X : C) : PartialOrder (End X) :=
  CStarAlgebra.spectralOrder (End X)

instance instStarOrderedRing (X : C) : StarOrderedRing (End X) :=
  CStarAlgebra.spectralOrderedRing (End X)

/-- Positivity of `f ≫ dagger f` in the spectral order of `End X`. -/
@[simp] theorem of_comp_dagger_self_nonneg (f : X ⟶ Y) :
    0 ≤ (End.of (f ≫ dagger f) : End X) := by
  obtain ⟨h, hh⟩ := CStarCategory.exists_comp_dagger_eq f
  have heq : (End.of (f ≫ dagger f) : End X) = star (End.of h) * End.of h := by
    ext
    simpa using hh
  rw [heq]
  exact star_mul_self_nonneg _

/-- Positivity of `dagger f ≫ f` in the spectral order of `End Y`. -/
@[simp] theorem of_dagger_comp_self_nonneg (f : X ⟶ Y) :
    0 ≤ (End.of (dagger f ≫ f) : End Y) := by
  simpa using of_comp_dagger_self_nonneg (dagger f)

/-- Conjugating a self-adjoint endomorphism `b : Y ⟶ Y` by `f : X ⟶ Y` is bounded in the spectral
order of `End X` by `‖b‖ • End.of (f ≫ dagger f)`. -/
theorem of_comp_selfAdjoint_comp_dagger_le_norm_smul (f : X ⟶ Y) {b : Y ⟶ Y}
    (hb : dagger b = b) :
    End.of (f ≫ b ≫ dagger f) ≤ ‖b‖ • End.of (f ≫ dagger f) := by
  -- Decompose `‖b‖ • 𝟙 Y - b` as a positive square `s * s` in `End Y`, then conjugate by `f`.
  have hb_sa : IsSelfAdjoint (End.of b) := (isSelfAdjoint_of_iff b).mpr hb
  have hle : End.of b ≤ algebraMap ℝ (End Y) ‖End.of b‖ := hb_sa.le_algebraMap_norm_self
  have hsub : 0 ≤ algebraMap ℝ (End Y) ‖b‖ - End.of b := sub_nonneg.mpr hle
  let s : End Y := CFC.sqrt (algebraMap ℝ (End Y) ‖b‖ - End.of b)
  have hs_sa : dagger s.asHom = s.asHom :=
    (isSelfAdjoint_iff s).mp (CFC.sqrt_nonneg _).isSelfAdjoint
  have hs_sq : s.asHom ≫ s.asHom = (‖b‖ : ℂ) • 𝟙 Y - b := by
    have h1 := congrArg End.asHom (CFC.sqrt_mul_sqrt_self _ hsub)
    have halg : (algebraMap ℝ (End Y) ‖b‖).asHom = (‖b‖ : ℂ) • 𝟙 Y := by
      rw [Algebra.algebraMap_eq_smul_one]
      rfl
    simpa [halg, ← Complex.coe_smul] using h1
  rw [← sub_nonneg]
  have hdiff : ‖b‖ • End.of (f ≫ dagger f) - End.of (f ≫ b ≫ dagger f) =
      End.of ((f ≫ s.asHom) ≫ dagger (f ≫ s.asHom)) := by
    ext
    have hsmul : (‖b‖ • End.of (f ≫ dagger f)).asHom = (‖b‖ : ℂ) • (f ≫ dagger f) := rfl
    calc (‖b‖ • End.of (f ≫ dagger f) - End.of (f ≫ b ≫ dagger f)).asHom
        = (‖b‖ : ℂ) • (f ≫ dagger f) - f ≫ b ≫ dagger f := by rw [sub_asHom, hsmul]
      _ = f ≫ ((‖b‖ : ℂ) • 𝟙 Y - b) ≫ dagger f := by
          rw [Preadditive.sub_comp, Preadditive.comp_sub, Linear.smul_comp, Category.id_comp,
            Linear.comp_smul]
      _ = f ≫ (s.asHom ≫ s.asHom) ≫ dagger f := by rw [hs_sq]
      _ = (End.of ((f ≫ s.asHom) ≫ dagger (f ≫ s.asHom))).asHom := by
          simp [Category.assoc, hs_sa]
  rw [hdiff]
  exact of_comp_dagger_self_nonneg (f ≫ s.asHom)

end CategoryTheory.End

namespace TauCeti

section Consequences

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C]

@[instance_reducible]
private def mkEndCStarAlgebraAux
    (X : C)
    (nX : Norm (X ⟶ X)) (mX : MetricSpace (X ⟶ X)) (cX : CompleteSpace (X ⟶ X))
    (dist_eq : ∀ f g : X ⟶ X, dist f g = ‖-f + g‖)
    (norm_smul_le : ∀ (c : ℂ) (f : X ⟶ X), ‖c • f‖ ≤ ‖c‖ * ‖f‖)
    (norm_comp_le : ∀ f g : X ⟶ X, ‖f ≫ g‖ ≤ ‖g‖ * ‖f‖)
    (norm_mul_self_le : ∀ f : X ⟶ X, ‖f‖ * ‖f‖ ≤ ‖f ≫ dagger f‖) :
    CStarAlgebra (End X) :=
  let mEnd : MetricSpace (End X) := MetricSpace.induced End.asHom End.homEquiv.injective mX
  let nrEnd : NormedRing (End X) :=
    { (inferInstance : Ring (End X)), mEnd with
      norm := fun a => @Norm.norm _ nX a.asHom
      dist_eq := fun a b => dist_eq a.asHom b.asHom
      norm_mul_le := fun a b => norm_comp_le b.asHom a.asHom }
  { nrEnd, (inferInstance : StarRing (End X)), (inferInstance : Algebra ℂ (End X)) with
    toCompleteSpace :=
      (@IsUniformInducing.completeSpace_congr _ _ mEnd.toUniformSpace mX.toUniformSpace
        End.asHom ⟨rfl⟩ End.homEquiv.surjective).mpr cX
    norm_mul_self_le := fun a => norm_mul_self_le a.asHom
    norm_smul_le := fun c a => norm_smul_le c a.asHom
    star_smul := star_smul }

omit [DaggerPreadditive C] [DaggerLinear ℂ C] in
private theorem existsSqrtAux {X Y : C} (f : X ⟶ Y) {A : Type v} [CStarAlgebra A]
    (e : End X ≃⋆ₐ[ℂ] A)
    (hspec : ∀ {r : ℝ}, (r : ℂ) ∈ spectrum ℂ (End.of (f ≫ dagger f)) → 0 ≤ r) :
    ∃ h : X ⟶ X, f ≫ dagger f = h ≫ dagger h := by
  have ha : IsSelfAdjoint (e (End.of (f ≫ dagger f))) :=
    ((End.isSelfAdjoint_of_iff (f ≫ dagger f)).mpr (by simp)).map e
  have ha_spec : SpectrumRestricts (e (End.of (f ≫ dagger f))) ContinuousMap.realToNNReal := by
    rw [SpectrumRestricts.nnreal_iff]
    intro r hr
    have hrC : (r : ℂ) ∈ spectrum ℂ (e (End.of (f ≫ dagger f))) :=
      (spectrum.algebraMap_mem_iff ℂ).mpr hr
    rw [← StarAlgEquiv.coe_toAlgEquiv, AlgEquiv.spectrum_eq] at hrC
    exact hspec hrC
  obtain ⟨s, hs_sa, -, hs_sq⟩ :=
    CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts ha ha_spec
  have hsymm_sa : dagger (e.symm s).asHom = (e.symm s).asHom :=
    (End.isSelfAdjoint_iff _).mp (hs_sa.map e.symm)
  have hsymm_sq : (e.symm s) * (e.symm s) = End.of (f ≫ dagger f) := by
    rw [← map_mul, hs_sq, e.symm_apply_apply]
  exact ⟨(e.symm s).asHom, by simpa [hsymm_sa] using congrArg End.asHom hsymm_sq.symm⟩

/-- Construct a `CStarCategory` from Ghez–Lima–Roberts' spectral positivity condition:
every real spectral value of `End.of (f ≫ dagger f)` in `End X` is nonnegative. -/
@[instance_reducible]
def CStarCategory.ofSpectrumNonneg
    [homNorm : ∀ X Y : C, Norm (X ⟶ Y)]
    [homMetricSpace : ∀ X Y : C, MetricSpace (X ⟶ Y)]
    [homCompleteSpace : ∀ X Y : C, CompleteSpace (X ⟶ Y)]
    (dist_eq : ∀ {X Y : C} (f g : X ⟶ Y), dist f g = ‖-f + g‖)
    (norm_smul_le : ∀ {X Y : C} (c : ℂ) (f : X ⟶ Y), ‖c • f‖ ≤ ‖c‖ * ‖f‖)
    (norm_comp_le : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), ‖f ≫ g‖ ≤ ‖g‖ * ‖f‖)
    (norm_mul_self_le : ∀ {X Y : C} (f : X ⟶ Y), ‖f‖ * ‖f‖ ≤ ‖f ≫ dagger f‖)
    (spectrum_nonneg : ∀ {X Y : C} (f : X ⟶ Y) {r : ℝ},
      (r : ℂ) ∈ spectrum ℂ (End.of (f ≫ dagger f)) → 0 ≤ r) :
    CStarCategory C where
  homNorm := homNorm
  homMetricSpace := homMetricSpace
  homCompleteSpace := homCompleteSpace
  dist_eq := dist_eq
  norm_smul_le := norm_smul_le
  norm_comp_le := norm_comp_le
  norm_mul_self_le := norm_mul_self_le
  exists_comp_dagger_eq {X Y} f :=
    @existsSqrtAux C _ _ _ _ X Y f (End X)
      (mkEndCStarAlgebraAux X (homNorm X X) (homMetricSpace X X) (homCompleteSpace X X)
        dist_eq norm_smul_le norm_comp_le norm_mul_self_le)
      (StarAlgEquiv.refl ℂ (End X)) (spectrum_nonneg f)

variable [CStarCategory C] {W X Y Z : C}

/-- Every `f ≫ dagger f` admits a self-adjoint square root `h : X ⟶ X` with
`h ≫ h = f ≫ dagger f`. -/
theorem exists_selfAdjoint_sq_eq_comp_dagger_self (f : X ⟶ Y) :
    ∃ h : X ⟶ X, dagger h = h ∧ h ≫ h = f ≫ dagger f := by
  let s : End X := CFC.sqrt (End.of (f ≫ dagger f))
  refine ⟨s.asHom, (End.isSelfAdjoint_iff s).mp (CFC.sqrt_nonneg _).isSelfAdjoint, ?_⟩
  exact congrArg End.asHom (CFC.sqrt_mul_sqrt_self _ (End.of_comp_dagger_self_nonneg f))

/-! ### Norm formulas for identities, zero objects, unitaries, and projections -/

/-- For every object `X`, the norm of `𝟙 X` is either `0` (when `X` is a zero object) or `1`. -/
theorem norm_id_eq_zero_or_one (X : C) : ‖(𝟙 X : X ⟶ X)‖ = 0 ∨ ‖(𝟙 X : X ⟶ X)‖ = 1 := by
  have hsq : ‖(𝟙 X : X ⟶ X)‖ ^ 2 = ‖(𝟙 X : X ⟶ X)‖ := by
    simpa using (norm_self_comp_dagger (𝟙 X)).symm
  have hmul : ‖(𝟙 X : X ⟶ X)‖ * (‖(𝟙 X : X ⟶ X)‖ - 1) = 0 := by
    linarith [sq (‖(𝟙 X : X ⟶ X)‖)]
  rcases mul_eq_zero.mp hmul with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

/-- Identity morphisms have norm at most `1`, unconditionally (including on zero objects). -/
theorem norm_id_le_one (X : C) : ‖(𝟙 X : X ⟶ X)‖ ≤ 1 := by
  rcases norm_id_eq_zero_or_one X with h | h <;> linarith

/-- A nonzero identity morphism has norm `1`. -/
theorem norm_id_of_ne_zero {X : C} (h : (𝟙 X : X ⟶ X) ≠ 0) : ‖(𝟙 X : X ⟶ X)‖ = 1 :=
  (norm_id_eq_zero_or_one X).resolve_left (norm_ne_zero_iff.mpr h)

/-- When `End X` is nontrivial, `‖𝟙 X‖ = 1`. -/
@[simp] theorem norm_id_of_nontrivial (X : C) [Nontrivial (End X)] : ‖(𝟙 X : X ⟶ X)‖ = 1 :=
  CStarRing.norm_one (E := End X)

/-- `‖𝟙 X‖ = 0` holds precisely when `X` is a zero object. -/
theorem norm_id_eq_zero_iff (X : C) : ‖(𝟙 X : X ⟶ X)‖ = 0 ↔ Limits.IsZero X := by
  rw [norm_eq_zero, Limits.IsZero.iff_id_eq_zero]

/-- On a non-zero object `X`, `‖𝟙 X‖ = 1`. -/
theorem norm_id_of_not_isZero {X : C} (hX : ¬Limits.IsZero X) : ‖(𝟙 X : X ⟶ X)‖ = 1 :=
  norm_id_of_ne_zero fun h => hX ((Limits.IsZero.iff_id_eq_zero X).mpr h)

namespace IsUnitary

/-- Precomposing with a unitary arrow preserves norms on all Hom spaces. -/
@[simp] theorem norm_comp_left {u : X ⟶ Y} (hu : IsUnitary u) (g : Y ⟶ Z) :
    ‖u ≫ g‖ = ‖g‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← norm_dagger_comp_self,
    ← norm_dagger_comp_self g]
  simp [Category.assoc, hu.dagger_hom_id_assoc]

/-- Postcomposing with a unitary arrow preserves norms on all Hom spaces. -/
@[simp] theorem norm_comp_right (f : W ⟶ X) {u : X ⟶ Y} (hu : IsUnitary u) :
    ‖f ≫ u‖ = ‖f‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← norm_self_comp_dagger,
    ← norm_self_comp_dagger f]
  simp [Category.assoc, hu.hom_dagger_id_assoc]

/-- Precomposition with a unitary arrow as a `ℂ`-linear isometric equivalence of Hom spaces. -/
def leftCompLinearIsometryEquiv {u : X ⟶ Y} (hu : IsUnitary u) (Z : C) :
    (Y ⟶ Z) ≃ₗᵢ[ℂ] (X ⟶ Z) where
  toFun g := u ≫ g
  invFun h := TauCeti.dagger u ≫ h
  left_inv g := by simp [hu.dagger_hom_id_assoc]
  right_inv h := by simp [hu.hom_dagger_id_assoc]
  map_add' _ _ := Preadditive.comp_add _ _ _ _ _ _
  map_smul' _ _ := Linear.comp_smul _ _ _ _ _ _
  norm_map' := hu.norm_comp_left

/-- Postcomposition with a unitary arrow as a `ℂ`-linear isometric equivalence of Hom spaces. -/
def rightCompLinearIsometryEquiv (W : C) {u : X ⟶ Y} (hu : IsUnitary u) :
    (W ⟶ X) ≃ₗᵢ[ℂ] (W ⟶ Y) where
  toFun f := f ≫ u
  invFun h := h ≫ TauCeti.dagger u
  left_inv f := by simp [Category.assoc, hu.hom_dagger_id]
  right_inv h := by simp [Category.assoc, hu.dagger_hom_id]
  map_add' _ _ := Preadditive.add_comp _ _ _ _ _ _
  map_smul' _ _ := Linear.smul_comp _ _ _ _ _ _
  norm_map' f := hu.norm_comp_right f

/-- Every unitary arrow has norm at most `1`. -/
theorem norm_le_one {u : X ⟶ Y} (hu : IsUnitary u) : ‖u‖ ≤ 1 := by
  rw [← sq_le_one_iff₀ (norm_nonneg u), ← norm_self_comp_dagger, hu.hom_dagger_id]
  exact norm_id_le_one X

/-- A unitary arrow out of an object with nontrivial endomorphisms has norm `1`. -/
theorem norm_eq_one {u : X ⟶ Y} (hu : IsUnitary u) [Nontrivial (End X)] : ‖u‖ = 1 := by
  have hsq : ‖u‖ ^ 2 = 1 := by
    rw [← norm_self_comp_dagger, hu.hom_dagger_id, norm_id_of_nontrivial]
  nlinarith [norm_nonneg u]

/-- A unitary arrow out of a non-zero object has norm `1`. -/
theorem norm_eq_one_of_not_isZero {u : X ⟶ Y} (hu : IsUnitary u) (hX : ¬Limits.IsZero X) :
    ‖u‖ = 1 := by
  have hsq : ‖u‖ ^ 2 = 1 := by
    rw [← norm_self_comp_dagger, hu.hom_dagger_id, norm_id_of_not_isZero hX]
  nlinarith [norm_nonneg u]

/-- A unitary arrow out of a zero object has norm `0`. -/
theorem norm_eq_zero_of_isZero {u : X ⟶ Y} (hu : IsUnitary u) (hX : Limits.IsZero X) :
    ‖u‖ = 0 := by
  rw [← sq_eq_zero_iff, ← norm_self_comp_dagger, hu.hom_dagger_id,
    (norm_id_eq_zero_iff X).mpr hX]

end IsUnitary

/-- Any self-adjoint idempotent endomorphism (a projection) has norm at most `1`. -/
theorem norm_le_one_of_idempotent_of_dagger_eq {e : X ⟶ X} (he_idem : e ≫ e = e)
    (he_sa : dagger e = e) : ‖e‖ ≤ 1 :=
  IsStarProjection.norm_le (End.of e) ((End.isStarProjection_of_iff e).mpr ⟨he_idem, he_sa⟩)

/-- Any nonzero self-adjoint idempotent endomorphism has norm `1`. -/
theorem norm_eq_one_of_idempotent_of_dagger_eq {e : X ⟶ X} (he_idem : e ≫ e = e)
    (he_sa : dagger e = e) (he0 : e ≠ 0) : ‖e‖ = 1 := by
  have hsq : ‖e‖ ^ 2 = ‖e‖ := by
    calc ‖e‖ ^ 2 = ‖e ≫ dagger e‖ := (norm_self_comp_dagger e).symm
      _ = ‖e‖ := by rw [he_sa, he_idem]
  have hpos : 0 < ‖e‖ := norm_pos_iff.mpr he0
  nlinarith

/-! ### Hilbert C⋆-module structures on Hom spaces, Cauchy–Schwarz, and polarization -/

/-- Each Hom space `X ⟶ Y` is a Hilbert C⋆-module over `End Y` via postcomposition
`b • f = f ≫ b.asHom` and `End Y`-valued inner product `⟪f, g⟫ = End.of (dagger f ≫ g)`. -/
instance instCStarModuleEndHom (X Y : C) : CStarModule (End Y) (X ⟶ Y) where
  inner f g := End.of (dagger f ≫ g)
  inner_add_right := by intros; ext; simp
  inner_self_nonneg := fun {f} => End.of_dagger_comp_self_nonneg f
  inner_self := fun {f} => by simp [End.ext_iff]
  inner_op_smul_right := fun {b f g} => by
    ext
    simp [End.smul_right, Category.assoc]
  inner_smul_right_complex := by intros; ext; simp
  star_inner f g := by ext; simp
  norm_eq_sqrt_norm_inner_self f := by
    rw [End.norm_of, norm_dagger_comp_self, Real.sqrt_sq (norm_nonneg f)]

/-- Each Hom space `X ⟶ Y` is a right Hilbert C⋆-module over `End X` (represented as
`CStarModule (End X)ᵐᵒᵖ (X ⟶ Y)`) via precomposition `op a • f = a.asHom ≫ f` and `End X`-valued
inner product `unop ⟪f, g⟫ = End.of (g ≫ dagger f)`. -/
instance instCStarModuleOpEndHom (X Y : C) : CStarModule (End X)ᵐᵒᵖ (X ⟶ Y) where
  inner f g := op (End.of (g ≫ dagger f))
  inner_add_right := by
    intro f g h
    apply unop_injective
    ext
    simp
  inner_self_nonneg := fun {f} => op_nonneg.mpr (End.of_comp_dagger_self_nonneg f)
  inner_self := fun {f} => by
    simp [op_eq_zero_iff, End.ext_iff]
  inner_op_smul_right := fun {a f g} => by
    apply unop_injective
    ext
    simp [End.smul_left, Category.assoc]
  inner_smul_right_complex := by
    intro z f g
    apply unop_injective
    ext
    simp
  star_inner f g := by
    apply unop_injective
    ext
    simp
  norm_eq_sqrt_norm_inner_self f := by
    rw [norm_op, End.norm_of, norm_self_comp_dagger, Real.sqrt_sq (norm_nonneg f)]

/-- Evaluation of the `End Y`-valued Hom inner product. -/
@[simp] theorem inner_end_hom (f g : X ⟶ Y) :
    inner (End Y) f g = End.of (dagger f ≫ g) := (rfl)

/-- Evaluation of the `End X`-valued right-module Hom inner product. -/
@[simp] theorem unop_inner_opEnd_hom (f g : X ⟶ Y) :
    unop (inner (End X)ᵐᵒᵖ f g) = End.of (g ≫ dagger f) := (rfl)

/-- Cauchy–Schwarz inequality in the spectral order of `End X`:
`End.of (f ≫ dagger g) * End.of (g ≫ dagger f) ≤ ‖f‖ ^ 2 • End.of (g ≫ dagger g)`. -/
theorem end_of_comp_dagger_mul_le (f g : X ⟶ Y) :
    End.of (f ≫ dagger g) * End.of (g ≫ dagger f) ≤ ‖f‖ ^ 2 • End.of (g ≫ dagger g) := by
  have h := CStarModule.star_unop_inner_mul_unop_inner_le (A := End X) f g
  have hstar : star (End.of (g ≫ dagger f)) = End.of (f ≫ dagger g) := by ext; simp
  rwa [unop_inner_opEnd_hom, hstar] at h

/-- Cauchy–Schwarz inequality in the spectral order of `End Y`:
`End.of (dagger f ≫ g) * End.of (dagger g ≫ f) ≤ ‖f‖ ^ 2 • End.of (dagger g ≫ g)`. -/
theorem end_of_dagger_comp_mul_le (f g : X ⟶ Y) :
    End.of (dagger f ≫ g) * End.of (dagger g ≫ f) ≤ ‖f‖ ^ 2 • End.of (dagger g ≫ g) := by
  simpa using CStarModule.inner_mul_inner_swap_le (A := End Y) (x := f) (y := g)

/-- Norm recovery: `‖f‖` is the greatest value of `‖f ≫ dagger g‖` as `g : X ⟶ Y` ranges over the
closed unit ball. -/
theorem isGreatest_norm_comp_dagger (f : X ⟶ Y) :
    IsGreatest {‖f ≫ dagger g‖ | (g : X ⟶ Y) (_ : ‖g‖ ≤ 1)} ‖f‖ := by
  simpa using CStarModule.isGreatest_norm_unop_inner (A := End X) f

/-- Morphisms in `X ⟶ Y` are determined by pairing on the right with `dagger h` for all
`h : X ⟶ Y`. -/
theorem ext_comp_dagger {f g : X ⟶ Y} (h : ∀ k : X ⟶ Y, f ≫ dagger k = g ≫ dagger k) :
    f = g := by
  refine CStarModule.ext_inner_left (A := (End X)ᵐᵒᵖ) fun k => ?_
  apply unop_injective
  ext
  exact h k

/-- Morphisms in `X ⟶ Y` are determined by pairing on the left with `dagger h` for all
`h : X ⟶ Y`. -/
theorem ext_dagger_comp {f g : X ⟶ Y} (h : ∀ k : X ⟶ Y, dagger k ≫ f = dagger k ≫ g) :
    f = g := by
  refine CStarModule.ext_inner_left (A := End Y) fun k => ?_
  ext
  exact h k

/-- Polarization identity in `X ⟶ X`: `g ≫ dagger f` is a linear combination of four
self-composites `h ≫ dagger h`. -/
theorem comp_dagger_polarization (f g : X ⟶ Y) :
    g ≫ dagger f = (4 : ℂ)⁻¹ •
      ((f + g) ≫ dagger (f + g) - (f - g) ≫ dagger (f - g) -
        I • ((f + I • g) ≫ dagger (f + I • g)) +
        I • ((f - I • g) ≫ dagger (f - I • g))) := by
  have h := congrArg (End.asHom ∘ unop) (CStarModule.inner_polarization (A := (End X)ᵐᵒᵖ) f g)
  simp only [Function.comp_apply, unop_smul, unop_inner_opEnd_hom, End.smul_asHom] at h
  exact h

/-- Dual polarization identity in `Y ⟶ Y`: `dagger f ≫ g` is a linear combination of four
self-composites `dagger h ≫ h`. -/
theorem dagger_comp_polarization (f g : X ⟶ Y) :
    dagger f ≫ g = (4 : ℂ)⁻¹ •
      (dagger (f + g) ≫ (f + g) - dagger (f - g) ≫ (f - g) -
        I • (dagger (f + I • g) ≫ (f + I • g)) +
        I • (dagger (f - I • g) ≫ (f - I • g))) := by
  have h := congrArg End.asHom (CStarModule.inner_polarization (A := End Y) f g)
  simpa using h

end Consequences

end TauCeti

namespace CategoryTheory.Limits.IsZero

open TauCeti

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C] [CStarCategory C]

/-- On a zero object `X`, the identity morphism has norm `0`. -/
@[simp] theorem norm_id_eq_zero {X : C} (hX : IsZero X) : ‖(𝟙 X : X ⟶ X)‖ = 0 :=
  (norm_id_eq_zero_iff X).mpr hX

end CategoryTheory.Limits.IsZero
