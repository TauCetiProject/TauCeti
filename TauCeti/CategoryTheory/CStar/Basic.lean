/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import TauCeti.CategoryTheory.Dagger.Basic
public import TauCeti.CategoryTheory.Linear.Endomorphism
import TauCeti.Analysis.CStarAlgebra.Module.Basic

/-!
# C⋆-categories

A complex C⋆-category is a complex linear dagger category whose Hom spaces are complex Banach
spaces such that composition is submultiplicative, the norm satisfies the C⋆-inequality
`‖f‖ * ‖f‖ ≤ ‖f ≫ f†‖`, and every `f ≫ f†` has the form `g ≫ g†` for an endomorphism `g : X ⟶ X`.

From these axioms it follows automatically that the dagger is isometric (`‖f†‖ = ‖f‖`) and that the
C⋆-identity `‖f ≫ f†‖ = ‖f‖ ^ 2` holds in both categorical orders. Each endomorphism algebra
`CategoryTheory.End X` inherits a compatible unital C⋆-algebra structure with Mathlib's
operator-order multiplication (`End.mul f g = End.of (g.asHom ≫ f.asHom)`), together with its
spectral order `CStarAlgebra.spectralOrder (End X)`. Under this order, the positivity axiom is
equivalent to `0 ≤ End.of (f ≫ f†)` for all `f : X ⟶ Y`, and each Hom space `X ⟶ Y` carries a
Hilbert C⋆-module structure over `End Y`, yielding endomorphism-valued and norm Cauchy–Schwarz
inequalities, polarization identities, and norm recovery.

## Main declarations

* `TauCeti.CStarCategory`: the class of complex C⋆-categories over a native complex linear dagger
  category, reusing `Preadditive.homGroup` and `Linear.homModule` without diamonds.
* `TauCeti.CStarCategory.norm_dagger`, `TauCeti.CStarCategory.norm_self_comp_dagger`,
  `TauCeti.CStarCategory.norm_dagger_comp_self`: isometry of the dagger and the C⋆-identities.
* `TauCeti.CStarCategory.daggerLinearIsometryEquiv`: the dagger as a conjugate-linear isometric
  equivalence `(X ⟶ Y) ≃ₗᵢ⋆[ℂ] (Y ⟶ X)`.
* `TauCeti.CStarCategory.compCLM`, `TauCeti.CStarCategory.leftCompCLM`,
  `TauCeti.CStarCategory.rightCompCLM`: continuous bilinear composition and its closed kernels.
* `TauCeti.CStarCategory.norm_id_eq_zero_iff`, `TauCeti.CStarCategory.norm_id_eq_one_iff`:
  zero-object norm formulas, showing `‖𝟙 X‖ = 0` iff `IsZero X` and `‖𝟙 X‖ = 1` otherwise.
* `CategoryTheory.End.instCStarAlgebra`, `CategoryTheory.End.instPartialOrder`,
  `CategoryTheory.End.instStarOrderedRing`: the C⋆-algebra and spectral order on `End X`.
* `TauCeti.CStarCategory.self_comp_dagger_nonneg`, `TauCeti.CStarCategory.conjugate_mono`:
  positivity and monotonicity of conjugation in endomorphism algebras.
* `TauCeti.CStarCategory.homCStarModule`, `TauCeti.CStarCategory.comp_dagger_comp_le`,
  `TauCeti.CStarCategory.norm_dagger_comp_sq_le`: Hilbert C⋆-module structure and Cauchy–Schwarz
  inequalities on Hom spaces.
* `TauCeti.dagger_comp_polarization`, `TauCeti.comp_dagger_polarization`: complex polarization
  identities in any complex linear dagger category.

## References

* P. Ghez, R. Lima, J. E. Roberts, *W*-categories*, Pacific J. Math. 120 (1985), 79–109.
* P. D. Mitchener, *C*-categories*, Proc. London Math. Soc. (3) 84 (2002), 375–404.
-/

public section

noncomputable section

open CategoryTheory
open scoped ComplexOrder

universe v u

namespace TauCeti

section Polarization

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C]
  {X Y : C}

/-- Complex polarization identity for `f† ≫ g` in a complex linear dagger category. -/
theorem dagger_comp_polarization (f g : X ⟶ Y) :
    dagger f ≫ g =
      (4 : ℂ)⁻¹ •
        (dagger (f + g) ≫ (f + g) - dagger (f - g) ≫ (f - g) -
          Complex.I • (dagger (f + Complex.I • g) ≫ (f + Complex.I • g)) +
          Complex.I • (dagger (f - Complex.I • g) ≫ (f - Complex.I • g))) := by
  simp only [dagger_add, dagger_sub, dagger_smul, Preadditive.add_comp, Preadditive.comp_add,
    Preadditive.sub_comp, Preadditive.comp_sub, Preadditive.neg_comp, Linear.smul_comp,
    Linear.comp_smul, Complex.star_def, Complex.conj_I, smul_add, smul_sub, smul_neg, smul_smul,
    neg_smul, Complex.I_mul_I]
  module

/-- Complex polarization identity for `f ≫ g†` in a complex linear dagger category. -/
theorem comp_dagger_polarization (f g : X ⟶ Y) :
    f ≫ dagger g =
      (4 : ℂ)⁻¹ •
        ((f + g) ≫ dagger (f + g) - (f - g) ≫ dagger (f - g) +
          Complex.I • ((f + Complex.I • g) ≫ dagger (f + Complex.I • g)) -
          Complex.I • ((f - Complex.I • g) ≫ dagger (f - Complex.I • g))) := by
  simp only [dagger_add, dagger_sub, dagger_smul, Preadditive.add_comp, Preadditive.comp_add,
    Preadditive.sub_comp, Preadditive.comp_sub, Preadditive.comp_neg, Linear.smul_comp,
    Linear.comp_smul, Complex.star_def, Complex.conj_I, smul_add, smul_sub, smul_neg, smul_smul,
    neg_smul, Complex.I_mul_I]
  module

end Polarization

/-- A complex C⋆-category is a complex linear dagger category whose Hom spaces are Banach spaces
with submultiplicative composition, the C⋆-inequality `‖f‖ * ‖f‖ ≤ ‖f ≫ f†‖`, and positivity of
`f ≫ f†` in `End X` (Ghez–Lima–Roberts): every `f ≫ f†` factors as `g ≫ g†` for some
endomorphism `g : X ⟶ X`.

The `AddCommGroup` and `Module ℂ` structures are inherited from `Preadditive C` and `Linear ℂ C`
so that no algebraic diamonds arise, while `homNorm`, `homMetricSpace`, and `homCompleteSpace`
preserve pre-existing Banach-space structures on concrete categories such as `HilbertCat ℂ`. -/
class CStarCategory (C : Type u) [Category.{v} C] [Preadditive C] [Linear ℂ C]
    [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C] where
  /-- The norm on each Hom space. -/
  homNorm : ∀ X Y : C, Norm (X ⟶ Y) := by infer_instance
  /-- The metric space structure on each Hom space. -/
  homMetricSpace : ∀ X Y : C, MetricSpace (X ⟶ Y) := by infer_instance
  /-- The metric distance is induced by the norm. -/
  dist_eq : ∀ {X Y : C} (f g : X ⟶ Y),
    @dist (X ⟶ Y) (homMetricSpace X Y).toDist f g =
      @norm (X ⟶ Y) (homNorm X Y) (-f + g) := by
    intro _ _ f g; exact NormedAddCommGroup.dist_eq f g
  /-- Scalar multiplication is submultiplicative with respect to the norm. -/
  norm_smul_le : ∀ {X Y : C} (c : ℂ) (f : X ⟶ Y),
    @norm (X ⟶ Y) (homNorm X Y) (c • f) ≤ ‖c‖ * @norm (X ⟶ Y) (homNorm X Y) f := by
    intro _ _ c f; exact norm_smul_le c f
  /-- Each Hom space is complete. -/
  homCompleteSpace : ∀ X Y : C,
    @CompleteSpace (X ⟶ Y) (homMetricSpace X Y).toUniformSpace := by infer_instance
  /-- Composition is contractive (submultiplicative). -/
  protected norm_comp_le' : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
    @norm (X ⟶ Z) (homNorm X Z) (f ≫ g) ≤
      @norm (X ⟶ Y) (homNorm X Y) f * @norm (Y ⟶ Z) (homNorm Y Z) g
  /-- The C⋆-inequality in categorical composition order: `‖f‖ * ‖f‖ ≤ ‖f ≫ f†‖`. -/
  protected norm_sq_le_norm_self_comp_dagger' : ∀ {X Y : C} (f : X ⟶ Y),
    @norm (X ⟶ Y) (homNorm X Y) f * @norm (X ⟶ Y) (homNorm X Y) f ≤
      @norm (X ⟶ X) (homNorm X X) (f ≫ dagger f)
  /-- Positivity axiom: every `f ≫ f†` has the form `g ≫ g†` for some endomorphism `g : X ⟶ X`. -/
  exists_self_comp_dagger : ∀ {X Y : C} (f : X ⟶ Y),
    ∃ g : X ⟶ X, g ≫ dagger g = f ≫ dagger f

namespace CStarCategory

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C] [CStarCategory C]

/-- The normed additive group structure on Hom spaces of a C⋆-category, reusing
`Preadditive.homGroup`. -/
instance (priority := 900) instNormedAddCommGroupHom (X Y : C) : NormedAddCommGroup (X ⟶ Y) where
  toNorm := CStarCategory.homNorm X Y
  toAddCommGroup := Preadditive.homGroup X Y
  toMetricSpace := CStarCategory.homMetricSpace X Y
  dist_eq := CStarCategory.dist_eq

/-- The complex normed space structure on Hom spaces of a C⋆-category, reusing
`Linear.homModule`. -/
instance (priority := 900) instNormedSpaceHom (X Y : C) : NormedSpace ℂ (X ⟶ Y) where
  toModule := Linear.homModule X Y
  norm_smul_le := CStarCategory.norm_smul_le

/-- Each Hom space of a C⋆-category is complete. -/
instance (priority := 900) instCompleteSpaceHom (X Y : C) : CompleteSpace (X ⟶ Y) :=
  CStarCategory.homCompleteSpace X Y

variable {W X Y Z : C}

/-! ### Basic norm, dagger, and composition laws -/

/-- Composition in a C⋆-category is submultiplicative: `‖f ≫ g‖ ≤ ‖f‖ * ‖g‖`. -/
theorem norm_comp_le (f : X ⟶ Y) (g : Y ⟶ Z) : ‖f ≫ g‖ ≤ ‖f‖ * ‖g‖ :=
  CStarCategory.norm_comp_le' f g

/-- The C⋆-inequality in categorical composition order: `‖f‖ * ‖f‖ ≤ ‖f ≫ f†‖`. -/
theorem norm_sq_le_norm_self_comp_dagger (f : X ⟶ Y) : ‖f‖ * ‖f‖ ≤ ‖f ≫ dagger f‖ :=
  CStarCategory.norm_sq_le_norm_self_comp_dagger' f

private theorem norm_le_norm_dagger (f : X ⟶ Y) : ‖f‖ ≤ ‖dagger f‖ := by
  obtain h | h := eq_zero_or_norm_pos f
  · simp [h]
  · exact le_of_mul_le_mul_left
      ((norm_sq_le_norm_self_comp_dagger f).trans (norm_comp_le f (dagger f))) h

/-- The dagger preserves the Hom norm. -/
@[simp]
theorem norm_dagger (f : X ⟶ Y) : ‖dagger f‖ = ‖f‖ :=
  le_antisymm (by simpa only [dagger_dagger] using norm_le_norm_dagger (dagger f))
    (norm_le_norm_dagger f)

/-- Taking daggers is an isometry between opposite Hom spaces. -/
theorem isometry_dagger (X Y : C) : Isometry (dagger : (X ⟶ Y) → (Y ⟶ X)) :=
  Isometry.of_dist_eq fun f g => by
    rw [dist_eq_norm, dist_eq_norm, ← dagger_sub, norm_dagger]

/-- Taking daggers is continuous. -/
@[fun_prop]
theorem continuous_dagger (X Y : C) : Continuous (dagger : (X ⟶ Y) → (Y ⟶ X)) :=
  (isometry_dagger X Y).continuous

/-- The dagger bundled as a conjugate-linear isometric equivalence between opposite Hom spaces. -/
def daggerLinearIsometryEquiv (X Y : C) : (X ⟶ Y) ≃ₗᵢ⋆[ℂ] (Y ⟶ X) where
  toFun := dagger
  invFun := dagger
  left_inv := dagger_dagger
  right_inv := dagger_dagger
  map_add' := dagger_add
  map_smul' := dagger_smul
  norm_map' := norm_dagger

/-- Evaluation of the conjugate-linear isometric dagger equivalence. -/
@[simp]
theorem daggerLinearIsometryEquiv_apply (f : X ⟶ Y) :
    daggerLinearIsometryEquiv X Y f = dagger f := (rfl)

/-- The inverse of the conjugate-linear isometric dagger equivalence reverses endpoints. -/
@[simp]
theorem daggerLinearIsometryEquiv_symm :
    (daggerLinearIsometryEquiv X Y).symm = daggerLinearIsometryEquiv Y X := (rfl)

/-- The C⋆-identity in categorical composition order: `‖f ≫ f†‖ = ‖f‖ ^ 2`. -/
@[simp]
theorem norm_self_comp_dagger (f : X ⟶ Y) : ‖f ≫ dagger f‖ = ‖f‖ ^ 2 := by
  rw [sq]
  exact le_antisymm
    ((norm_comp_le f (dagger f)).trans_eq (by rw [norm_dagger]))
    (norm_sq_le_norm_self_comp_dagger f)

/-- The C⋆-identity in opposite order: `‖f† ≫ f‖ = ‖f‖ ^ 2`. -/
@[simp]
theorem norm_dagger_comp_self (f : X ⟶ Y) : ‖dagger f ≫ f‖ = ‖f‖ ^ 2 := by
  simpa only [dagger_dagger, norm_dagger] using norm_self_comp_dagger (dagger f)

/-- A morphism satisfies `f ≫ f† = 0` precisely when `f = 0`. -/
@[simp]
theorem self_comp_dagger_eq_zero (f : X ⟶ Y) : f ≫ dagger f = 0 ↔ f = 0 := by
  rw [← norm_eq_zero, norm_self_comp_dagger, sq_eq_zero_iff, norm_eq_zero]

/-- A morphism satisfies `f† ≫ f = 0` precisely when `f = 0`. -/
@[simp]
theorem dagger_comp_self_eq_zero (f : X ⟶ Y) : dagger f ≫ f = 0 ↔ f = 0 := by
  rw [← norm_eq_zero, norm_dagger_comp_self, sq_eq_zero_iff, norm_eq_zero]

/-- Every identity arrow has norm either `0` or `1`. -/
theorem norm_id_eq_zero_or_one (X : C) : ‖𝟙 X‖ = 0 ∨ ‖𝟙 X‖ = 1 := by
  have h : ‖𝟙 X‖ ^ 2 = ‖𝟙 X‖ := by
    simpa only [dagger_id, Category.id_comp] using (norm_self_comp_dagger (𝟙 X)).symm
  have hmul : ‖𝟙 X‖ * (‖𝟙 X‖ - 1) = 0 := by linarith [sq ‖𝟙 X‖]
  exact (mul_eq_zero.mp hmul).imp_right sub_eq_zero.mp

/-- Every identity arrow has norm at most `1`. -/
theorem norm_id_le_one (X : C) : ‖𝟙 X‖ ≤ 1 := by
  rcases norm_id_eq_zero_or_one X with h | h <;> simp [h]

/-- A unitary arrow has the same norm as the identity on its source (either `0` or `1`). -/
theorem norm_of_isUnitary {f : X ⟶ Y} (hf : IsUnitary f) : ‖f‖ = ‖𝟙 X‖ := by
  have hsq : ‖f‖ ^ 2 = ‖𝟙 X‖ ^ 2 := by
    rw [← norm_self_comp_dagger, hf.hom_dagger_id]
    rcases norm_id_eq_zero_or_one X with h | h <;> simp [h]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Every unitary arrow has norm at most `1`. -/
theorem norm_le_one_of_isUnitary {f : X ⟶ Y} (hf : IsUnitary f) : ‖f‖ ≤ 1 := by
  rw [norm_of_isUnitary hf]
  exact norm_id_le_one X

/-- Postcomposing by a unitary arrow preserves norms. -/
theorem norm_comp_of_isUnitary {f : X ⟶ Y} {u : Y ⟶ Z} (hu : IsUnitary u) :
    ‖f ≫ u‖ = ‖f‖ := by
  refine le_antisymm ?_ ?_
  · calc ‖f ≫ u‖ ≤ ‖f‖ * ‖u‖ := norm_comp_le f u
      _ ≤ ‖f‖ * 1 := by gcongr; exact norm_le_one_of_isUnitary hu
      _ = ‖f‖ := mul_one _
  · calc ‖f‖ = ‖(f ≫ u) ≫ dagger u‖ := by simp [Category.assoc, hu.hom_dagger_id]
      _ ≤ ‖f ≫ u‖ * ‖dagger u‖ := norm_comp_le _ _
      _ = ‖f ≫ u‖ * ‖u‖ := by rw [norm_dagger]
      _ ≤ ‖f ≫ u‖ * 1 := by gcongr; exact norm_le_one_of_isUnitary hu
      _ = ‖f ≫ u‖ := mul_one _

/-- Precomposing by a unitary arrow preserves norms. -/
theorem norm_of_isUnitary_comp {u : X ⟶ Y} {g : Y ⟶ Z} (hu : IsUnitary u) :
    ‖u ≫ g‖ = ‖g‖ := by
  have h := norm_comp_of_isUnitary (f := dagger g) hu.dagger
  rwa [← dagger_comp, norm_dagger, norm_dagger] at h

/-! ### Continuous bilinear composition and closed kernels -/

/-- Composition bundled as a continuous bilinear map on Hom spaces. -/
def compCLM (X Y Z : C) : (X ⟶ Y) →L[ℂ] (Y ⟶ Z) →L[ℂ] (X ⟶ Z) :=
  LinearMap.mkContinuous₂
    { toFun := fun f => Linear.leftComp ℂ Z f
      map_add' := fun f₁ f₂ => by ext g; exact Preadditive.add_comp X Y Z f₁ f₂ g
      map_smul' := fun r f => by ext g; exact Linear.smul_comp X Y Z r f g }
    1 (fun f g => by simpa [one_mul] using norm_comp_le f g)

/-- Evaluation of the continuous bilinear composition map. -/
@[simp]
theorem compCLM_apply (f : X ⟶ Y) (g : Y ⟶ Z) : compCLM X Y Z f g = f ≫ g := (rfl)

/-- The continuous bilinear composition map has norm at most `1`. -/
theorem opNorm_compCLM_le_one (X Y Z : C) : ‖compCLM X Y Z‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

/-- Composition is jointly continuous on Hom spaces. -/
@[fun_prop]
theorem continuous_comp (X Y Z : C) :
    Continuous (fun p : (X ⟶ Y) × (Y ⟶ Z) => p.1 ≫ p.2) :=
  (compCLM X Y Z).continuous₂

/-- Composition on the left with `f : X ⟶ Y` (`g ↦ f ≫ g`) as a continuous linear map
`(Y ⟶ Z) →L[ℂ] (X ⟶ Z)`, refining `CategoryTheory.Linear.leftComp`. -/
def leftCompCLM (Z : C) (f : X ⟶ Y) : (Y ⟶ Z) →L[ℂ] (X ⟶ Z) :=
  compCLM X Y Z f

/-- Evaluation of `leftCompCLM`. -/
@[simp]
theorem leftCompCLM_apply (f : X ⟶ Y) (g : Y ⟶ Z) : leftCompCLM Z f g = f ≫ g := (rfl)

/-- `leftCompCLM` by `f` has operator norm at most `‖f‖`. -/
theorem opNorm_leftCompCLM_le (Z : C) (f : X ⟶ Y) : ‖leftCompCLM Z f‖ ≤ ‖f‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f) fun g => norm_comp_le f g

/-- On `(Y ⟶ Y)`, left composition by `f : X ⟶ Y` has operator norm equal to `‖f‖`. -/
@[simp]
theorem opNorm_leftCompCLM_self (f : X ⟶ Y) : ‖leftCompCLM Y f‖ = ‖f‖ := by
  refine le_antisymm (opNorm_leftCompCLM_le Y f) ?_
  calc ‖f‖ = ‖leftCompCLM Y f (𝟙 Y)‖ := by simp
    _ ≤ ‖leftCompCLM Y f‖ * ‖𝟙 Y‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖leftCompCLM Y f‖ * 1 := by gcongr; exact norm_id_le_one Y
    _ = ‖leftCompCLM Y f‖ := mul_one _

/-- Composition on the right with `g : Y ⟶ Z` (`f ↦ f ≫ g`) as a continuous linear map
`(X ⟶ Y) →L[ℂ] (X ⟶ Z)`, refining `CategoryTheory.Linear.rightComp`. -/
def rightCompCLM (X : C) (g : Y ⟶ Z) : (X ⟶ Y) →L[ℂ] (X ⟶ Z) :=
  (compCLM X Y Z).flip g

/-- Evaluation of `rightCompCLM`. -/
@[simp]
theorem rightCompCLM_apply (f : X ⟶ Y) (g : Y ⟶ Z) : rightCompCLM X g f = f ≫ g := (rfl)

/-- `rightCompCLM` by `g` has operator norm at most `‖g‖`. -/
theorem opNorm_rightCompCLM_le (X : C) (g : Y ⟶ Z) : ‖rightCompCLM X g‖ ≤ ‖g‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg g) fun f =>
    (norm_comp_le f g).trans_eq (mul_comm _ _)

/-- On `(Y ⟶ Y)`, right composition by `g : Y ⟶ Z` has operator norm equal to `‖g‖`. -/
@[simp]
theorem opNorm_rightCompCLM_self (g : Y ⟶ Z) : ‖rightCompCLM Y g‖ = ‖g‖ := by
  refine le_antisymm (opNorm_rightCompCLM_le Y g) ?_
  calc ‖g‖ = ‖rightCompCLM Y g (𝟙 Y)‖ := by simp
    _ ≤ ‖rightCompCLM Y g‖ * ‖𝟙 Y‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖rightCompCLM Y g‖ * 1 := by gcongr; exact norm_id_le_one Y
    _ = ‖rightCompCLM Y g‖ := mul_one _

/-- The right annihilator `{g : Y ⟶ Z | f ≫ g = 0}` of a morphism is closed in `Y ⟶ Z`. -/
theorem isClosed_setOf_comp_eq_zero_right (Z : C) (f : X ⟶ Y) :
    IsClosed {g : Y ⟶ Z | f ≫ g = 0} :=
  (leftCompCLM Z f).isClosed_ker

/-- The left annihilator `{f : X ⟶ Y | f ≫ g = 0}` of a morphism is closed in `X ⟶ Y`. -/
theorem isClosed_setOf_comp_eq_zero_left (X : C) (g : Y ⟶ Z) :
    IsClosed {f : X ⟶ Y | f ≫ g = 0} :=
  (rightCompCLM X g).isClosed_ker

/-! ### Zero-object formulas -/

/-- The identity arrow of an object has norm `0` if and only if the object is a zero object. -/
theorem norm_id_eq_zero_iff (X : C) : ‖𝟙 X‖ = 0 ↔ Limits.IsZero X := by
  rw [norm_eq_zero, ← Limits.IsZero.iff_id_eq_zero]

/-- The identity arrow of an object has norm `1` if and only if the object is not a zero object. -/
@[simp]
theorem norm_id_eq_one_iff (X : C) : ‖𝟙 X‖ = 1 ↔ ¬ Limits.IsZero X := by
  constructor
  · intro h h0
    have := (norm_id_eq_zero_iff X).mpr h0
    linarith
  · intro h
    exact (norm_id_eq_zero_or_one X).resolve_left fun h0 => h ((norm_id_eq_zero_iff X).mp h0)

/-- The identity arrow of a zero object has norm `0`. -/
theorem norm_id_of_isZero {X : C} (hX : Limits.IsZero X) : ‖𝟙 X‖ = 0 :=
  (norm_id_eq_zero_iff X).mpr hX

/-- The identity arrow of a nonzero object has norm `1`. -/
theorem norm_id_of_not_isZero {X : C} (hX : ¬ Limits.IsZero X) : ‖𝟙 X‖ = 1 :=
  (norm_id_eq_one_iff X).mpr hX

/-- Every morphism out of a zero object has norm `0`. -/
theorem norm_eq_zero_of_isZero_left (hX : Limits.IsZero X) (f : X ⟶ Y) : ‖f‖ = 0 := by
  rw [hX.eq_of_src f 0, norm_zero]

/-- Every morphism into a zero object has norm `0`. -/
theorem norm_eq_zero_of_isZero_right (hY : Limits.IsZero Y) (f : X ⟶ Y) : ‖f‖ = 0 := by
  rw [hY.eq_of_tgt f 0, norm_zero]

/-- A unitary arrow from a nonzero object has norm `1`. -/
theorem norm_of_isUnitary_of_not_isZero {f : X ⟶ Y} (hf : IsUnitary f) (hX : ¬ Limits.IsZero X) :
    ‖f‖ = 1 := by
  rw [norm_of_isUnitary hf, norm_id_of_not_isZero hX]

open scoped ZeroObject in
/-- In a C⋆-category with a zero object, the identity of `0` has norm `0`. -/
theorem norm_id_zero [Limits.HasZeroObject C] : ‖𝟙 (0 : C)‖ = 0 :=
  norm_id_of_isZero (Limits.isZero_zero C)

end CStarCategory

end TauCeti

/-! ### Endomorphism C⋆-algebras -/

namespace CategoryTheory.End

open TauCeti

section Preadditive

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- An object of a preadditive category is a zero object precisely when its endomorphism ring is
subsingleton. -/
theorem subsingleton_iff_isZero (X : C) : Subsingleton (End X) ↔ Limits.IsZero X := by
  rw [Limits.IsZero.iff_id_eq_zero]
  constructor
  · intro h
    exact congrArg End.asHom (Subsingleton.elim (1 : End X) 0)
  · intro h
    refine ⟨fun a b => End.ext ?_⟩
    have ha : a.asHom = 0 := by rw [← Category.id_comp a.asHom, h, Limits.zero_comp]
    have hb : b.asHom = 0 := by rw [← Category.id_comp b.asHom, h, Limits.zero_comp]
    rw [ha, hb]

/-- An object of a preadditive category is not a zero object precisely when its endomorphism ring
is nontrivial. -/
theorem nontrivial_iff_not_isZero (X : C) : Nontrivial (End X) ↔ ¬ Limits.IsZero X := by
  rw [← not_subsingleton_iff_nontrivial, subsingleton_iff_isZero]

end Preadditive

section Dagger

variable {C : Type u} [Category.{v} C] [DaggerCategory C]

/-- An endomorphism is unitary in the dagger category iff it belongs to `unitary (End X)`. -/
theorem isUnitary_asHom_iff {X : C} (f : End X) :
    IsUnitary f.asHom ↔ f ∈ unitary (End X) := by
  rw [isUnitary_iff, Unitary.mem_iff]
  simp only [End.ext_iff, mul_asHom, star_asHom, one_asHom]

/-- An endomorphism is self-adjoint in `End X` iff its underlying arrow equals its dagger. -/
theorem isSelfAdjoint_iff {X : C} (f : End X) :
    IsSelfAdjoint f ↔ dagger f.asHom = f.asHom := by
  rw [IsSelfAdjoint, End.ext_iff, star_asHom]

end Dagger

section CStar

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C] [CStarCategory C]

/-- The norm on `End X` transferred from `X ⟶ X`. -/
instance instNorm (X : C) : Norm (End X) where
  norm f := ‖f.asHom‖

/-- The normed ring structure on `End X`, reusing Mathlib's operator-order `Ring (End X)`. -/
instance instNormedRing (X : C) : NormedRing (End X) where
  toRing := inferInstance
  toNorm := instNorm X
  toMetricSpace := MetricSpace.induced End.asHom End.homEquiv.injective inferInstance
  dist_eq f g := by
    change dist f.asHom g.asHom = ‖-f.asHom + g.asHom‖
    rw [NormedAddCommGroup.dist_eq]
  norm_mul_le f g := (CStarCategory.norm_comp_le g.asHom f.asHom).trans_eq (mul_comm _ _)

/-- The norm of `f.asHom` agrees with the norm of `f : End X`. -/
@[simp]
theorem norm_asHom {X : C} (f : End X) : ‖f.asHom‖ = ‖f‖ := (rfl)

/-- The norm of `End.of f` agrees with the norm of `f : X ⟶ X`. -/
@[simp]
theorem norm_of {X : C} (f : X ⟶ X) : ‖End.of f‖ = ‖f‖ := (rfl)

/-- The projection `End.asHom` is an isometry. -/
theorem isometry_asHom (X : C) : Isometry (End.asHom : End X → (X ⟶ X)) :=
  fun _ _ => rfl

/-- The constructor `End.of` is an isometry. -/
theorem isometry_of (X : C) : Isometry (End.of : (X ⟶ X) → End X) :=
  fun _ _ => rfl

/-- The normed `ℂ`-algebra structure on `End X`, reusing Mathlib's `Algebra ℂ (End X)`. -/
instance instNormedAlgebra (X : C) : NormedAlgebra ℂ (End X) where
  toAlgebra := inferInstance
  norm_smul_le c f := norm_smul_le c f.asHom

/-- The canonical linear isometric equivalence `End X ≃ₗᵢ[ℂ] (X ⟶ X)`. -/
def linearIsometryEquiv (X : C) : End X ≃ₗᵢ[ℂ] (X ⟶ X) where
  toEquiv := End.homEquiv
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

/-- Evaluation of `End.linearIsometryEquiv`. -/
@[simp]
theorem linearIsometryEquiv_apply {X : C} (f : End X) :
    linearIsometryEquiv X f = f.asHom := (rfl)

/-- Evaluation of `(End.linearIsometryEquiv X).symm`. -/
@[simp]
theorem linearIsometryEquiv_symm_apply {X : C} (f : X ⟶ X) :
    (linearIsometryEquiv X).symm f = End.of f := (rfl)

/-- `End X` is complete because `X ⟶ X` is complete and `End.asHom` is an isometric bijection. -/
instance instCompleteSpace (X : C) : CompleteSpace (End X) :=
  ({ toEquiv := End.homEquiv
     uniformContinuous_toFun := (isometry_asHom X).uniformContinuous
     uniformContinuous_invFun := (isometry_of X).uniformContinuous } :
    End X ≃ᵤ (X ⟶ X)).completeSpace_iff.mpr inferInstance

/-- The endomorphism ring of any object in a C⋆-category is a C⋆-ring. -/
instance instCStarRing (X : C) : CStarRing (End X) where
  norm_mul_self_le f := CStarCategory.norm_sq_le_norm_self_comp_dagger f.asHom

/-- The endomorphism algebra of any object in a C⋆-category is a unital complex C⋆-algebra. -/
instance instCStarAlgebra (X : C) : CStarAlgebra (End X) where

/-- The canonical spectral partial order on the endomorphism C⋆-algebra `End X`. -/
instance instPartialOrder (X : C) : PartialOrder (End X) :=
  CStarAlgebra.spectralOrder (End X)

/-- The spectral order makes `End X` a star-ordered ring. -/
instance instStarOrderedRing (X : C) : StarOrderedRing (End X) :=
  CStarAlgebra.spectralOrderedRing (End X)

/-- The unit of `End X` has norm `0` precisely when `X` is a zero object. -/
theorem norm_one_eq_zero_iff (X : C) : ‖(1 : End X)‖ = 0 ↔ Limits.IsZero X :=
  CStarCategory.norm_id_eq_zero_iff X

/-- The unit of `End X` has norm `1` precisely when `X` is not a zero object. -/
@[simp]
theorem norm_one_eq_one_iff (X : C) : ‖(1 : End X)‖ = 1 ↔ ¬ Limits.IsZero X :=
  CStarCategory.norm_id_eq_one_iff X

end CStar

end CategoryTheory.End

/-! ### Positivity, Hilbert C⋆-module structure, and Cauchy–Schwarz -/

namespace TauCeti.CStarCategory

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C] [CStarCategory C]
  {X Y Z : C}

/-- For every morphism `f : X ⟶ Y`, `End.of (f ≫ f†)` is positive in `End X`. -/
theorem self_comp_dagger_nonneg (f : X ⟶ Y) : (0 : End X) ≤ End.of (f ≫ dagger f) := by
  obtain ⟨g, hg⟩ := CStarCategory.exists_self_comp_dagger f
  have hmul : End.of (f ≫ dagger f) = star (End.of g) * End.of g := End.ext hg.symm
  rw [hmul]
  exact star_mul_self_nonneg (End.of g)

/-- For every morphism `f : X ⟶ Y`, `End.of (f† ≫ f)` is positive in `End Y`. -/
theorem dagger_comp_self_nonneg (f : X ⟶ Y) : (0 : End Y) ≤ End.of (dagger f ≫ f) := by
  simpa only [dagger_dagger] using self_comp_dagger_nonneg (dagger f)

/-- For every morphism `f : X ⟶ Y`, `End.of (f ≫ f†)` is self-adjoint in `End X`. -/
theorem isSelfAdjoint_self_comp_dagger (f : X ⟶ Y) :
    IsSelfAdjoint (End.of (f ≫ dagger f)) :=
  (self_comp_dagger_nonneg f).isSelfAdjoint

/-- For every morphism `f : X ⟶ Y`, `End.of (f† ≫ f)` is self-adjoint in `End Y`. -/
theorem isSelfAdjoint_dagger_comp_self (f : X ⟶ Y) :
    IsSelfAdjoint (End.of (dagger f ≫ f)) :=
  (dagger_comp_self_nonneg f).isSelfAdjoint

/-- An element of `End X` is positive iff it has the form `End.of (g ≫ g†)` for some `g : X ⟶ X`. -/
theorem nonneg_iff_exists_self_comp_dagger (a : End X) :
    0 ≤ a ↔ ∃ g : X ⟶ X, g ≫ dagger g = a.asHom := by
  constructor
  · intro ha
    refine ⟨(CFC.sqrt a).asHom, ?_⟩
    have hsq : CFC.sqrt a * CFC.sqrt a = a := CFC.sqrt_mul_sqrt_self a ha
    have hsa : star (CFC.sqrt a) = CFC.sqrt a := (CFC.sqrt_nonneg a).isSelfAdjoint.star_eq
    have hmul : star (CFC.sqrt a) * CFC.sqrt a = a := by rwa [hsa]
    simpa only [End.mul_asHom, End.star_asHom] using congrArg End.asHom hmul
  · rintro ⟨g, hg⟩
    have : a = End.of (g ≫ dagger g) := End.ext hg.symm
    rw [this]
    exact self_comp_dagger_nonneg g

/-- An element of `End X` is positive iff it has the form `End.of (g† ≫ g)` for some `g : X ⟶ X`. -/
theorem nonneg_iff_exists_dagger_comp_self (a : End X) :
    0 ≤ a ↔ ∃ g : X ⟶ X, dagger g ≫ g = a.asHom := by
  rw [nonneg_iff_exists_self_comp_dagger]
  exact ⟨fun ⟨g, hg⟩ => ⟨dagger g, by simpa only [dagger_dagger] using hg⟩,
    fun ⟨g, hg⟩ => ⟨dagger g, by simpa only [dagger_dagger] using hg⟩⟩

/-- Conjugating a positive endomorphism `a : End Y` by `f : X ⟶ Y` yields a positive endomorphism
`End.of (f ≫ a.asHom ≫ f†)` in `End X`. -/
theorem conjugate_nonneg {a : End Y} (ha : 0 ≤ a) (f : X ⟶ Y) :
    (0 : End X) ≤ End.of (f ≫ a.asHom ≫ dagger f) := by
  obtain ⟨g, hg⟩ := (nonneg_iff_exists_self_comp_dagger a).mp ha
  have hcomp : f ≫ a.asHom ≫ dagger f = (f ≫ g) ≫ dagger (f ≫ g) := by
    rw [← hg, dagger_comp]
    simp [Category.assoc]
  rw [hcomp]
  exact self_comp_dagger_nonneg (f ≫ g)

/-- Conjugating a positive endomorphism `a : End X` by `f†` yields a positive endomorphism
`End.of (f† ≫ a.asHom ≫ f)` in `End Y`. -/
theorem dagger_conjugate_nonneg {a : End X} (ha : 0 ≤ a) (f : X ⟶ Y) :
    (0 : End Y) ≤ End.of (dagger f ≫ a.asHom ≫ f) := by
  simpa only [dagger_dagger] using conjugate_nonneg ha (dagger f)

/-- Conjugation by `f : X ⟶ Y` is monotone from `End Y` to `End X`. -/
theorem conjugate_mono {a b : End Y} (hab : a ≤ b) (f : X ⟶ Y) :
    End.of (f ≫ a.asHom ≫ dagger f) ≤ End.of (f ≫ b.asHom ≫ dagger f) := by
  rw [← sub_nonneg] at hab ⊢
  have hsub : End.of (f ≫ b.asHom ≫ dagger f) - End.of (f ≫ a.asHom ≫ dagger f) =
      End.of (f ≫ (b - a).asHom ≫ dagger f) := by
    ext
    simp [Preadditive.comp_sub, Preadditive.sub_comp]
  rw [hsub]
  exact conjugate_nonneg hab f

/-- Conjugation by `f†` is monotone from `End X` to `End Y`. -/
theorem dagger_conjugate_mono {a b : End X} (hab : a ≤ b) (f : X ⟶ Y) :
    End.of (dagger f ≫ a.asHom ≫ f) ≤ End.of (dagger f ≫ b.asHom ≫ f) := by
  simpa only [dagger_dagger] using conjugate_mono hab (dagger f)

/-- For a self-adjoint `a : End Y`, `f ≫ a ≫ f† ≤ ‖a‖ • (f ≫ f†)` in `End X`. -/
theorem conjugate_le_norm_smul {a : End Y} (ha : IsSelfAdjoint a) (f : X ⟶ Y) :
    End.of (f ≫ a.asHom ≫ dagger f) ≤ ‖a‖ • End.of (f ≫ dagger f) := by
  have hle : a ≤ algebraMap ℝ (End Y) ‖a‖ := ha.le_algebraMap_norm_self
  have hconj := conjugate_mono hle f
  have halg : (algebraMap ℝ (End Y) ‖a‖).asHom = (‖a‖ : ℂ) • 𝟙 Y := by
    rw [IsScalarTower.algebraMap_apply ℝ ℂ (End Y), End.algebraMap_asHom, Complex.coe_algebraMap]
  have hrhs : End.of (f ≫ (algebraMap ℝ (End Y) ‖a‖).asHom ≫ dagger f) =
      ‖a‖ • End.of (f ≫ dagger f) := by
    rw [halg, ← Complex.coe_smul]
    ext
    simp only [Linear.comp_smul, Linear.smul_comp, Category.id_comp, End.smul_asHom]
  rwa [hrhs] at hconj

/-- For a self-adjoint `a : End X`, `f† ≫ a ≫ f ≤ ‖a‖ • (f† ≫ f)` in `End Y`. -/
theorem dagger_conjugate_le_norm_smul {a : End X} (ha : IsSelfAdjoint a) (f : X ⟶ Y) :
    End.of (dagger f ≫ a.asHom ≫ f) ≤ ‖a‖ • End.of (dagger f ≫ f) := by
  simpa only [dagger_dagger] using conjugate_le_norm_smul ha (dagger f)

/-- Each Hom space `X ⟶ Y` in a C⋆-category is a Hilbert C⋆-module over `End Y` with
`End Y`-valued inner product `⟪f, g⟫ = End.of (f† ≫ g)`. -/
scoped instance homCStarModule (X Y : C) : CStarModule (End Y) (X ⟶ Y) where
  inner f g := End.of (dagger f ≫ g)
  inner_add_right := by intros; ext; simp
  inner_self_nonneg := by intro f; exact dagger_comp_self_nonneg f
  inner_self := by
    intro f
    simp only [End.ext_iff, End.zero_asHom]
    exact dagger_comp_self_eq_zero f
  inner_op_smul_right := by
    intro a f g
    ext
    simp [End.smul_right, Category.assoc]
  inner_smul_right_complex := by intros; ext; simp
  star_inner f g := by ext; simp
  norm_eq_sqrt_norm_inner_self f := by
    simp only [End.norm_of, norm_dagger_comp_self, Real.sqrt_sq (norm_nonneg f)]

/-- The `End Y`-valued inner product on `X ⟶ Y` is `End.of (f† ≫ g)`. -/
@[simp]
theorem inner_eq_of_dagger_comp (f g : X ⟶ Y) :
    inner (End Y) f g = End.of (dagger f ≫ g) := (rfl)

/-- Endomorphism-valued Cauchy–Schwarz inequality in `End Y`:
`(f† ≫ g) * (g† ≫ f) ≤ ‖f‖² • (g† ≫ g)`, written in categorical composition order as
`g† ≫ f ≫ f† ≫ g ≤ ‖f‖² • (g† ≫ g)`. -/
theorem comp_dagger_comp_le (f g : X ⟶ Y) :
    End.of (dagger g ≫ f ≫ dagger f ≫ g) ≤ ‖f‖ ^ 2 • End.of (dagger g ≫ g) := by
  have h := CStarModule.inner_mul_inner_swap_le (A := End Y) (x := f) (y := g)
  simpa only [inner, ← End.of_comp, Category.assoc] using h

/-- Endomorphism-valued Cauchy–Schwarz inequality in `End X`:
`g ≫ f† ≫ f ≫ g† ≤ ‖f‖² • (g ≫ g†)`. -/
theorem self_comp_dagger_comp_le (f g : X ⟶ Y) :
    End.of (g ≫ dagger f ≫ f ≫ dagger g) ≤ ‖f‖ ^ 2 • End.of (g ≫ dagger g) := by
  simpa only [dagger_dagger, norm_dagger] using comp_dagger_comp_le (dagger f) (dagger g)

/-- Norm Cauchy–Schwarz inequality: `‖f† ≫ g‖ ≤ ‖f‖ * ‖g‖`. -/
theorem norm_dagger_comp_le (f g : X ⟶ Y) : ‖dagger f ≫ g‖ ≤ ‖f‖ * ‖g‖ :=
  (norm_comp_le (dagger f) g).trans_eq (by rw [norm_dagger])

/-- Norm Cauchy–Schwarz inequality in opposite order: `‖f ≫ g†‖ ≤ ‖f‖ * ‖g‖`. -/
theorem norm_self_comp_dagger_le (f g : X ⟶ Y) : ‖f ≫ dagger g‖ ≤ ‖f‖ * ‖g‖ :=
  (norm_comp_le f (dagger g)).trans_eq (by rw [norm_dagger])

/-- Squared norm Cauchy–Schwarz inequality: `‖f† ≫ g‖ ^ 2 ≤ ‖f† ≫ f‖ * ‖g† ≫ g‖`. -/
theorem norm_dagger_comp_sq_le (f g : X ⟶ Y) :
    ‖dagger f ≫ g‖ ^ 2 ≤ ‖dagger f ≫ f‖ * ‖dagger g ≫ g‖ := by
  rw [norm_dagger_comp_self, norm_dagger_comp_self, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_dagger_comp_le f g) 2

/-- Squared norm Cauchy–Schwarz inequality in opposite order:
`‖f ≫ g†‖ ^ 2 ≤ ‖f ≫ f†‖ * ‖g ≫ g†‖`. -/
theorem norm_self_comp_dagger_sq_le (f g : X ⟶ Y) :
    ‖f ≫ dagger g‖ ^ 2 ≤ ‖f ≫ dagger f‖ * ‖g ≫ dagger g‖ := by
  rw [norm_self_comp_dagger, norm_self_comp_dagger, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_self_comp_dagger_le f g) 2

/-- Norm recovery: `‖f‖` is the maximum of `‖g† ≫ f‖` over the closed unit ball of `X ⟶ Y`. -/
theorem isGreatest_norm_dagger_comp (f : X ⟶ Y) :
    IsGreatest {‖dagger g ≫ f‖ | (g : X ⟶ Y) (_ : ‖g‖ ≤ 1)} ‖f‖ :=
  CStarModule.isGreatest_norm_inner (A := End Y) f

/-- Norm recovery in opposite order: `‖f‖` is the maximum of `‖f ≫ g†‖` over the closed unit ball
of `X ⟶ Y`. -/
theorem isGreatest_norm_self_comp_dagger (f : X ⟶ Y) :
    IsGreatest {‖f ≫ dagger g‖ | (g : X ⟶ Y) (_ : ‖g‖ ≤ 1)} ‖f‖ := by
  have h := isGreatest_norm_dagger_comp (dagger f)
  rw [norm_dagger] at h
  convert h using 1
  ext r
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨dagger g, by rwa [norm_dagger], ?_⟩
    rw [← norm_dagger (f ≫ dagger g), dagger_comp, dagger_dagger]
  · rintro ⟨g, hg, rfl⟩
    refine ⟨dagger g, by rwa [norm_dagger], ?_⟩
    rw [← norm_dagger (dagger g ≫ dagger f), dagger_comp, dagger_dagger, dagger_dagger]

/-- Morphisms in a C⋆-category are separated by left composition with daggers. -/
theorem ext_dagger_comp_left {f g : X ⟶ Y}
    (h : ∀ k : X ⟶ Y, dagger k ≫ f = dagger k ≫ g) : f = g :=
  CStarModule.ext_inner_left (A := End Y) fun k => End.ext (h k)

/-- Morphisms in a C⋆-category are separated by right composition with daggers. -/
theorem ext_comp_dagger_right {f g : X ⟶ Y}
    (h : ∀ k : X ⟶ Y, f ≫ dagger k = g ≫ dagger k) : f = g := by
  apply dagger_inj.mp
  exact ext_dagger_comp_left fun k => by
    have hk := congrArg dagger (h (dagger k))
    simpa only [dagger_comp, dagger_dagger] using hk

end TauCeti.CStarCategory
