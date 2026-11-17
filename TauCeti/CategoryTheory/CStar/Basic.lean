/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.Order.Hom.Basic
public import TauCeti.CategoryTheory.Dagger.Basic
public import TauCeti.CategoryTheory.Linear.Endomorphism

import Mathlib.Algebra.Order.Module.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# C*-categories and endomorphism C*-algebras

A C*-category is a complex conjugate-linear dagger category whose Hom spaces are Banach spaces
with submultiplicative composition, the C*-inequality `‖f‖ ^ 2 ≤ ‖f ≫ dagger f‖` (which yields
the C*-identity `‖f ≫ dagger f‖ = ‖f‖ ^ 2` and dagger isometry), and positivity of `f ≫ dagger f`
in `CategoryTheory.End X` (expressed without order circularity as the existence of `g : X ⟶ X`
with `f ≫ dagger f = g ≫ dagger g`).

The class `TauCeti.CStarCategory` supplies the `Norm`, `MetricSpace`, and `CompleteSpace`
structures on each Hom space while reusing the native `AddCommGroup` and `Module ℂ` instances from
`Preadditive` and `Linear ℂ`, avoiding instance diamonds on concrete categories whose Hom spaces
already carry Banach structures. From these axioms we deduce that the dagger is an antilinear
isometry and that `‖f ≫ dagger f‖ = ‖f‖ ^ 2`, establish the standard norm bounds on self-adjoint
idempotents, identities, zero objects, isometries, and unitaries, equip each endomorphism algebra
`CategoryTheory.End X` with its compatible `CStarAlgebra` and spectral `StarOrderedRing`
structures, and prove conjugation monotonicity, C*-order Cauchy–Schwarz, and positive-functional
Cauchy–Schwarz inequalities.

## References

* P. Ghez, R. Lima, and J. E. Roberts, *W*-categories*, Pacific J. Math. 120 (1985), 79–109,
  Definition 1.1.
-/

public section

open CategoryTheory
open scoped ComplexOrder

universe v u

namespace TauCeti

/-! ### Definition of a C*-category -/

/-- A C*-category structure on a complex conjugate-linear dagger category: Banach Hom spaces with
submultiplicative composition, the C*-inequality `‖f‖ ^ 2 ≤ ‖f ≫ dagger f‖` (yielding
`‖f ≫ dagger f‖ = ‖f‖ ^ 2`), and positivity of `f ≫ dagger f` in `End X` expressed as
`∃ g : X ⟶ X, f ≫ dagger f = g ≫ dagger g`.

The `AddCommGroup` and `Module ℂ` instances are taken from `Preadditive` and `Linear ℂ`, so
categories whose Hom spaces already carry Banach structures inherit compatible instances without
diamonds. -/
class CStarCategory (C : Type u) [Category.{v} C] [Preadditive C] [Linear ℂ C]
    [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C] where
  /-- The norm on each Hom space. -/
  homNorm : ∀ X Y : C, Norm (X ⟶ Y) := by infer_instance
  /-- The metric space structure on each Hom space. -/
  homMetricSpace : ∀ X Y : C, MetricSpace (X ⟶ Y) := by infer_instance
  /-- The metric on each Hom space is induced by the norm and additive structure. -/
  dist_eq' : ∀ {X Y : C} (f g : X ⟶ Y),
    @dist _ (homMetricSpace X Y).toDist f g = @norm _ (homNorm X Y) (-f + g) := by
    intro X Y f g; exact dist_eq_norm_neg_add f g
  /-- Scalar multiplication is submultiplicative with respect to the Hom norm. -/
  norm_smul_le' : ∀ {X Y : C} (c : ℂ) (f : X ⟶ Y),
    @norm _ (homNorm X Y) (c • f) ≤ ‖c‖ * @norm _ (homNorm X Y) f := by
    intro X Y c f; exact norm_smul_le c f
  /-- Each Hom space is complete. -/
  homCompleteSpace : ∀ X Y : C,
    @CompleteSpace (X ⟶ Y) (homMetricSpace X Y).toUniformSpace := by infer_instance
  /-- Composition is submultiplicative for the Hom norms. -/
  norm_comp_le' : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
    @norm _ (homNorm X Z) (f ≫ g) ≤ @norm _ (homNorm X Y) f * @norm _ (homNorm Y Z) g
  /-- The C*-inequality in categorical composition order, which together with submultiplicativity
  of composition yields the C*-identity `‖f ≫ dagger f‖ = ‖f‖ ^ 2`. -/
  norm_sq_le_self_comp_dagger' : ∀ {X Y : C} (f : X ⟶ Y),
    @norm _ (homNorm X Y) f ^ 2 ≤ @norm _ (homNorm X X) (f ≫ dagger f)
  /-- Positivity of `f ≫ dagger f` in `End X`: every `f ≫ dagger f` factors as `g ≫ dagger g`
  for some endomorphism `g : X ⟶ X`. -/
  exists_self_comp_dagger_eq : ∀ {X Y : C} (f : X ⟶ Y),
    ∃ g : X ⟶ X, f ≫ dagger f = g ≫ dagger g

namespace CStarCategory

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C] [CStarCategory C]

/-- The normed additive group structure on Hom spaces of a C*-category, reusing
`Preadditive.homGroup`. -/
instance (priority := 100) homNormedAddCommGroup (X Y : C) : NormedAddCommGroup (X ⟶ Y) where
  toNorm := CStarCategory.homNorm X Y
  toAddCommGroup := Preadditive.homGroup X Y
  toMetricSpace := CStarCategory.homMetricSpace X Y
  dist_eq := CStarCategory.dist_eq'

/-- The complex normed space structure on Hom spaces of a C*-category, reusing
`Linear.homModule`. -/
instance (priority := 100) homNormedSpace (X Y : C) : NormedSpace ℂ (X ⟶ Y) where
  toModule := Linear.homModule X Y
  norm_smul_le := CStarCategory.norm_smul_le'

/-- Hom spaces of a C*-category are complete. -/
instance (priority := 100) completeSpace_hom (X Y : C) : CompleteSpace (X ⟶ Y) :=
  CStarCategory.homCompleteSpace X Y

/-! ### Elementary norm, dagger, self-adjoint idempotent, zero-object, and isometry bounds -/

variable {X Y Z : C}

/-- Composition is submultiplicative for the Hom norms. -/
theorem norm_comp_le (f : X ⟶ Y) (g : Y ⟶ Z) : ‖f ≫ g‖ ≤ ‖f‖ * ‖g‖ :=
  CStarCategory.norm_comp_le' f g

private theorem norm_le_norm_dagger (f : X ⟶ Y) : ‖f‖ ≤ ‖dagger f‖ := by
  by_cases hf : f = 0
  · simp [hf]
  · have hf_pos : 0 < ‖f‖ := norm_pos_iff.mpr hf
    have hsq : ‖f‖ * ‖f‖ ≤ ‖f‖ * ‖dagger f‖ := by
      calc ‖f‖ * ‖f‖ = ‖f‖ ^ 2 := (sq ‖f‖).symm
        _ ≤ ‖f ≫ dagger f‖ := CStarCategory.norm_sq_le_self_comp_dagger' f
        _ ≤ ‖f‖ * ‖dagger f‖ := norm_comp_le f (dagger f)
    exact le_of_mul_le_mul_left hsq hf_pos

/-- Taking the dagger preserves the Hom norm. -/
@[simp] theorem norm_dagger (f : X ⟶ Y) : ‖dagger f‖ = ‖f‖ :=
  le_antisymm (by simpa only [dagger_dagger] using norm_le_norm_dagger (dagger f))
    (norm_le_norm_dagger f)

/-- The C*-identity `‖f ≫ dagger f‖ = ‖f‖ ^ 2`. -/
@[simp] theorem norm_self_comp_dagger (f : X ⟶ Y) : ‖f ≫ dagger f‖ = ‖f‖ ^ 2 :=
  le_antisymm
    ((norm_comp_le f (dagger f)).trans_eq (by rw [norm_dagger, sq]))
    (CStarCategory.norm_sq_le_self_comp_dagger' f)

/-- The C*-identity in the opposite order, `‖dagger f ≫ f‖ = ‖f‖ ^ 2`. -/
@[simp] theorem norm_dagger_comp_self (f : X ⟶ Y) : ‖dagger f ≫ f‖ = ‖f‖ ^ 2 := by
  simpa only [dagger_dagger, norm_dagger] using norm_self_comp_dagger (dagger f)

/-- A morphism vanishes precisely when `f ≫ dagger f = 0`. -/
@[simp] theorem self_comp_dagger_eq_zero (f : X ⟶ Y) : f ≫ dagger f = 0 ↔ f = 0 := by
  rw [← norm_eq_zero, norm_self_comp_dagger, sq_eq_zero_iff, norm_eq_zero]

/-- A morphism vanishes precisely when `dagger f ≫ f = 0`. -/
@[simp] theorem dagger_comp_self_eq_zero (f : X ⟶ Y) : dagger f ≫ f = 0 ↔ f = 0 := by
  rw [← norm_eq_zero, norm_dagger_comp_self, sq_eq_zero_iff, norm_eq_zero]

/-- A self-adjoint idempotent endomorphism has norm `0` or `1`. -/
theorem norm_eq_zero_or_one_of_dagger_eq_of_comp_self {p : X ⟶ X} (hsa : dagger p = p)
    (hidem : p ≫ p = p) : ‖p‖ = 0 ∨ ‖p‖ = 1 := by
  have hsq : ‖p‖ ^ 2 = ‖p‖ := by
    calc ‖p‖ ^ 2 = ‖p ≫ dagger p‖ := (norm_self_comp_dagger p).symm
      _ = ‖p‖ := by rw [hsa, hidem]
  have hfac : ‖p‖ * (‖p‖ - 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfac with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

/-- A self-adjoint idempotent endomorphism has norm at most `1`. -/
theorem norm_le_one_of_dagger_eq_of_comp_self {p : X ⟶ X} (hsa : dagger p = p)
    (hidem : p ≫ p = p) : ‖p‖ ≤ 1 := by
  rcases norm_eq_zero_or_one_of_dagger_eq_of_comp_self hsa hidem with h | h <;> linarith

/-- A nonzero self-adjoint idempotent endomorphism has norm `1`. -/
theorem norm_eq_one_of_dagger_eq_of_comp_self {p : X ⟶ X} (hsa : dagger p = p)
    (hidem : p ≫ p = p) (hp : p ≠ 0) : ‖p‖ = 1 :=
  (norm_eq_zero_or_one_of_dagger_eq_of_comp_self hsa hidem).resolve_left (norm_ne_zero_iff.mpr hp)

/-- The norm of an identity morphism is either `0` or `1`. -/
theorem norm_id_eq_zero_or_one (X : C) : ‖𝟙 X‖ = 0 ∨ ‖𝟙 X‖ = 1 :=
  norm_eq_zero_or_one_of_dagger_eq_of_comp_self (dagger_id X) (Category.id_comp _)

/-- The norm of an identity morphism is at most `1`. -/
theorem norm_id_le (X : C) : ‖𝟙 X‖ ≤ 1 :=
  norm_le_one_of_dagger_eq_of_comp_self (dagger_id X) (Category.id_comp _)

/-- An identity morphism has norm `0` if and only if its object is a zero object. -/
theorem norm_id_eq_zero_iff_isZero (X : C) : ‖𝟙 X‖ = 0 ↔ Limits.IsZero X := by
  rw [norm_eq_zero, Limits.IsZero.iff_id_eq_zero]

/-- An identity morphism has norm `1` if and only if its object is not a zero object. -/
theorem norm_id_eq_one_iff_not_isZero (X : C) : ‖𝟙 X‖ = 1 ↔ ¬ Limits.IsZero X := by
  rw [← norm_id_eq_zero_iff_isZero]
  rcases norm_id_eq_zero_or_one X with h | h <;> simp [h]

/-- Every morphism out of a zero object has norm `0`. -/
theorem norm_eq_zero_of_isZero_left (hX : Limits.IsZero X) (f : X ⟶ Y) : ‖f‖ = 0 := by
  rw [hX.eq_of_src f 0, norm_zero]

/-- Every morphism into a zero object has norm `0`. -/
theorem norm_eq_zero_of_isZero_right (hY : Limits.IsZero Y) (f : X ⟶ Y) : ‖f‖ = 0 := by
  rw [hY.eq_of_tgt f 0, norm_zero]

/-- Postcomposition by an arrow satisfying `u ≫ dagger u = 𝟙 Y` preserves norms. -/
theorem norm_comp_eq_of_comp_dagger_eq_id {u : Y ⟶ Z} (hu : u ≫ dagger u = 𝟙 Y) (f : X ⟶ Y) :
    ‖f ≫ u‖ = ‖f‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  calc ‖f ≫ u‖ ^ 2 = ‖(f ≫ u) ≫ dagger (f ≫ u)‖ := (norm_self_comp_dagger _).symm
    _ = ‖f ≫ (u ≫ dagger u) ≫ dagger f‖ := by simp only [dagger_comp, Category.assoc]
    _ = ‖f ≫ dagger f‖ := by rw [hu, Category.id_comp]
    _ = ‖f‖ ^ 2 := norm_self_comp_dagger f

/-- Precomposition by an arrow satisfying `dagger u ≫ u = 𝟙 Y` preserves norms. -/
theorem norm_comp_eq_of_dagger_comp_eq_id {u : X ⟶ Y} (hu : dagger u ≫ u = 𝟙 Y) (f : Y ⟶ Z) :
    ‖u ≫ f‖ = ‖f‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  calc ‖u ≫ f‖ ^ 2 = ‖dagger (u ≫ f) ≫ (u ≫ f)‖ := (norm_dagger_comp_self _).symm
    _ = ‖dagger f ≫ (dagger u ≫ u) ≫ f‖ := by simp only [dagger_comp, Category.assoc]
    _ = ‖dagger f ≫ f‖ := by rw [hu, Category.id_comp]
    _ = ‖f‖ ^ 2 := norm_dagger_comp_self f

/-- An arrow with `u ≫ dagger u = 𝟙 X` has norm at most `1`. -/
theorem norm_le_one_of_comp_dagger_eq_id {u : X ⟶ Y} (hu : u ≫ dagger u = 𝟙 X) : ‖u‖ ≤ 1 := by
  have hsq : ‖u‖ ^ 2 ≤ 1 ^ 2 := by
    rw [← norm_self_comp_dagger, hu, one_pow]
    exact norm_id_le X
  exact (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp hsq

/-- An arrow with `u ≫ dagger u = 𝟙 X` on a non-zero object `X` has norm `1`. -/
theorem norm_eq_one_of_comp_dagger_eq_id {u : X ⟶ Y} (hu : u ≫ dagger u = 𝟙 X)
    (hX : ¬ Limits.IsZero X) : ‖u‖ = 1 := by
  refine (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp ?_
  rw [← norm_self_comp_dagger, hu, one_pow]
  exact (norm_id_eq_one_iff_not_isZero X).mpr hX

/-- An arrow with `dagger u ≫ u = 𝟙 Y` has norm at most `1`. -/
theorem norm_le_one_of_dagger_comp_eq_id {u : X ⟶ Y} (hu : dagger u ≫ u = 𝟙 Y) : ‖u‖ ≤ 1 := by
  simpa only [norm_dagger] using
    norm_le_one_of_comp_dagger_eq_id (u := dagger u) (by simpa only [dagger_dagger] using hu)

/-- An arrow with `dagger u ≫ u = 𝟙 Y` into a non-zero object `Y` has norm `1`. -/
theorem norm_eq_one_of_dagger_comp_eq_id {u : X ⟶ Y} (hu : dagger u ≫ u = 𝟙 Y)
    (hY : ¬ Limits.IsZero Y) : ‖u‖ = 1 := by
  simpa only [norm_dagger] using
    norm_eq_one_of_comp_dagger_eq_id (u := dagger u) (by simpa only [dagger_dagger] using hu) hY

/-! ### Continuous composition and isometric dagger equivalences -/

/-- The dagger as an antilinear isometric equivalence `(X ⟶ Y) ≃ₗᵢ⋆[ℂ] (Y ⟶ X)`. -/
def daggerLinearIsometryEquiv (X Y : C) : (X ⟶ Y) ≃ₗᵢ⋆[ℂ] (Y ⟶ X) where
  toFun := dagger
  invFun := dagger
  left_inv := dagger_dagger
  right_inv := dagger_dagger
  map_add' := dagger_add
  map_smul' := dagger_smul
  norm_map' := norm_dagger

/-- Evaluation of the antilinear isometric dagger equivalence. -/
@[simp] theorem daggerLinearIsometryEquiv_apply (f : X ⟶ Y) :
    daggerLinearIsometryEquiv X Y f = dagger f := (rfl)

/-- The inverse of the antilinear isometric dagger equivalence swaps endpoints. -/
@[simp] theorem daggerLinearIsometryEquiv_symm :
    (daggerLinearIsometryEquiv X Y).symm = daggerLinearIsometryEquiv Y X := (rfl)

/-- Taking the dagger is continuous on Hom spaces. -/
@[fun_prop] theorem continuous_dagger : Continuous (dagger : (X ⟶ Y) → (Y ⟶ X)) :=
  (daggerLinearIsometryEquiv X Y).continuous

/-- Composition as a continuous bilinear map `(X ⟶ Y) →L[ℂ] (Y ⟶ Z) →L[ℂ] (X ⟶ Z)`. -/
noncomputable def compCLM (X Y Z : C) : (X ⟶ Y) →L[ℂ] (Y ⟶ Z) →L[ℂ] (X ⟶ Z) :=
  LinearMap.mkContinuous₂ (Linear.comp (S := ℂ) X Y Z) 1 fun f g => by
    simpa only [Linear.comp_apply, Linear.leftComp_apply, one_mul] using norm_comp_le f g

/-- Evaluation of the continuous bilinear composition map. -/
@[simp] theorem compCLM_apply (f : X ⟶ Y) (g : Y ⟶ Z) : compCLM X Y Z f g = f ≫ g := (rfl)

/-- Continuous bilinear composition is contractive. -/
theorem norm_compCLM_le (X Y Z : C) : ‖compCLM X Y Z‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

/-- Precomposition by a fixed morphism `f : X ⟶ Y` has operator norm at most `‖f‖`. -/
theorem norm_compCLM_apply_le (f : X ⟶ Y) (Z : C) : ‖compCLM X Y Z f‖ ≤ ‖f‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f) (norm_comp_le f)

/-- Postcomposition by a fixed morphism `g : Y ⟶ Z` has operator norm at most `‖g‖`. -/
theorem norm_compCLM_flip_apply_le (X : C) (g : Y ⟶ Z) : ‖(compCLM X Y Z).flip g‖ ≤ ‖g‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg g) fun f =>
    (norm_comp_le f g).trans_eq (mul_comm _ _)

end CStarCategory

/-! ### Norm bounds for unitary morphisms -/

namespace IsUnitary

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C] [CStarCategory C] {X Y Z : C}

/-- Every unitary morphism has norm at most `1`. -/
theorem norm_le_one {u : X ⟶ Y} (hu : IsUnitary u) : ‖u‖ ≤ 1 :=
  CStarCategory.norm_le_one_of_comp_dagger_eq_id hu.hom_dagger_id

/-- Every unitary morphism out of a non-zero object has norm `1`. -/
theorem norm_eq_one {u : X ⟶ Y} (hu : IsUnitary u) (hX : ¬ Limits.IsZero X) : ‖u‖ = 1 :=
  CStarCategory.norm_eq_one_of_comp_dagger_eq_id hu.hom_dagger_id hX

/-- Postcomposing by a unitary morphism preserves norms. -/
theorem norm_comp_right {u : Y ⟶ Z} (hu : IsUnitary u) (f : X ⟶ Y) : ‖f ≫ u‖ = ‖f‖ :=
  CStarCategory.norm_comp_eq_of_comp_dagger_eq_id hu.hom_dagger_id f

/-- Precomposing by a unitary morphism preserves norms. -/
theorem norm_comp_left {u : X ⟶ Y} (hu : IsUnitary u) (f : Y ⟶ Z) : ‖u ≫ f‖ = ‖f‖ :=
  CStarCategory.norm_comp_eq_of_dagger_comp_eq_id hu.dagger_hom_id f

end IsUnitary

end TauCeti

/-! ### C*-algebra structure on endomorphisms -/

namespace CategoryTheory.End

open TauCeti

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C] [CStarCategory C] {X : C}

/-- The norm on `End X` is the Hom norm of the underlying morphism. -/
instance instNorm : Norm (End X) where
  norm a := ‖a.asHom‖

/-- The underlying morphism of an endomorphism has the same norm. -/
@[simp] theorem norm_asHom (a : End X) : ‖a.asHom‖ = ‖a‖ := (rfl)

/-- Constructing an endomorphism via `End.of` preserves the norm. -/
@[simp] theorem norm_of (f : X ⟶ X) : ‖End.of f‖ = ‖f‖ := (rfl)

/-- The normed ring structure on `End X`, reusing the native ring structure from `Preadditive`. -/
instance instNormedRing : NormedRing (End X) where
  toNorm := instNorm
  toRing := inferInstance
  toMetricSpace := MetricSpace.induced End.asHom (fun _ _ h => End.ext h) inferInstance
  dist_eq a b := dist_eq_norm_neg_add a.asHom b.asHom
  norm_mul_le a b := by
    rw [← norm_asHom, End.mul_asHom, ← norm_asHom a, ← norm_asHom b]
    exact (CStarCategory.norm_comp_le b.asHom a.asHom).trans_eq (mul_comm _ _)

/-- The normed `ℂ`-algebra structure on `End X`, reusing the native `Algebra ℂ` instance from
`Linear ℂ`. -/
noncomputable instance instNormedAlgebra : NormedAlgebra ℂ (End X) where
  toAlgebra := inferInstance
  norm_smul_le c a := norm_smul_le c a.asHom

/-- The underlying-morphism map as a linear isometric equivalence `End X ≃ₗᵢ[ℂ] (X ⟶ X)`. -/
def asHomLinearIsometryEquiv (X : C) : End X ≃ₗᵢ[ℂ] (X ⟶ X) :=
  { End.linearEquiv with norm_map' _ := rfl }

/-- Evaluation of `End.asHomLinearIsometryEquiv`. -/
@[simp] theorem asHomLinearIsometryEquiv_apply (a : End X) :
    asHomLinearIsometryEquiv X a = a.asHom := (rfl)

/-- The inverse of `End.asHomLinearIsometryEquiv` is `End.of`. -/
@[simp] theorem asHomLinearIsometryEquiv_symm_apply (f : X ⟶ X) :
    (asHomLinearIsometryEquiv X).symm f = End.of f := (rfl)

/-- Endomorphism algebras of a C*-category are complete. -/
instance instCompleteSpace : CompleteSpace (End X) := by
  rw [completeSpace_iff_isComplete_range (asHomLinearIsometryEquiv X).isometry.isUniformInducing,
    (asHomLinearIsometryEquiv X).surjective.range_eq]
  exact isComplete_univ

/-- Endomorphism algebras of a C*-category satisfy the C*-norm identity. -/
instance instCStarRing : CStarRing (End X) where
  norm_mul_self_le a := by
    rw [← norm_asHom (star a * a), End.mul_asHom, End.star_asHom,
      CStarCategory.norm_self_comp_dagger, sq, norm_asHom]

/-- Endomorphism algebras of a C*-category are unital C*-algebras. -/
noncomputable instance instCStarAlgebra : CStarAlgebra (End X) where

/-- The spectral partial order on `End X`. -/
noncomputable instance instPartialOrder : PartialOrder (End X) :=
  CStarAlgebra.spectralOrder _

/-- Endomorphism algebras of a C*-category are star-ordered rings under the spectral order. -/
instance instStarOrderedRing : StarOrderedRing (End X) :=
  CStarAlgebra.spectralOrderedRing _

end CategoryTheory.End

/-! ### Positivity, conjugation monotonicity, and Cauchy–Schwarz -/

namespace TauCeti.CStarCategory

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C] [CStarCategory C] {X Y Z : C}

/-- For every morphism `f : X ⟶ Y`, the endomorphism `f ≫ dagger f` is positive in `End X`. -/
theorem self_comp_dagger_nonneg (f : X ⟶ Y) : 0 ≤ End.of (f ≫ dagger f) := by
  obtain ⟨g, hg⟩ := CStarCategory.exists_self_comp_dagger_eq f
  rw [hg, End.of_comp]
  exact star_mul_self_nonneg (End.of g)

/-- For every morphism `f : X ⟶ Y`, the endomorphism `dagger f ≫ f` is positive in `End Y`. -/
theorem dagger_comp_self_nonneg (f : X ⟶ Y) : 0 ≤ End.of (dagger f ≫ f) := by
  simpa only [dagger_dagger] using self_comp_dagger_nonneg (dagger f)

/-- An endomorphism `a : End X` is positive if and only if `a.asHom = g ≫ dagger g` for some
`g : X ⟶ X`. -/
theorem end_nonneg_iff_exists_self_comp_dagger {a : End X} :
    0 ≤ a ↔ ∃ g : X ⟶ X, a.asHom = g ≫ dagger g :=
  CStarAlgebra.nonneg_iff_eq_star_mul_self.trans
    ⟨fun ⟨b, hb⟩ =>
      ⟨b.asHom, by simpa only [End.mul_asHom, End.star_asHom] using congrArg End.asHom hb⟩,
     fun ⟨g, hg⟩ => ⟨End.of g, End.ext (by simpa only [End.mul_asHom, End.star_asHom] using hg)⟩⟩

/-- Conjugating a positive endomorphism `a : End Y` by `f : X ⟶ Y` produces a positive
endomorphism `f ≫ a.asHom ≫ dagger f` in `End X`. -/
theorem conjugate_nonneg {a : End Y} (ha : 0 ≤ a) (f : X ⟶ Y) :
    0 ≤ End.of (f ≫ a.asHom ≫ dagger f) := by
  obtain ⟨g, hg⟩ := end_nonneg_iff_exists_self_comp_dagger.mp ha
  have hcomp : f ≫ a.asHom ≫ dagger f = (f ≫ g) ≫ dagger (f ≫ g) := by
    simp only [hg, dagger_comp, Category.assoc]
  rw [hcomp]
  exact self_comp_dagger_nonneg (f ≫ g)

/-- Conjugation by a morphism `f : X ⟶ Y` is monotone from `End Y` to `End X`. -/
theorem conjugate_le_conjugate {a b : End Y} (hab : a ≤ b) (f : X ⟶ Y) :
    End.of (f ≫ a.asHom ≫ dagger f) ≤ End.of (f ≫ b.asHom ≫ dagger f) := by
  rw [← sub_nonneg]
  have hsub : End.of (f ≫ b.asHom ≫ dagger f) - End.of (f ≫ a.asHom ≫ dagger f) =
      End.of (f ≫ (b - a).asHom ≫ dagger f) := by
    apply End.ext
    simp only [End.sub_asHom, Preadditive.comp_sub, Preadditive.sub_comp]
  rw [hsub]
  exact conjugate_nonneg (sub_nonneg.mpr hab) f

/-- Conjugating a self-adjoint endomorphism `a : End Y` by `f : X ⟶ Y` is bounded above by
`‖a‖ • End.of (f ≫ dagger f)`. -/
theorem conjugate_le_norm_smul {a : End Y} (ha : IsSelfAdjoint a) (f : X ⟶ Y) :
    End.of (f ≫ a.asHom ≫ dagger f) ≤ ‖a‖ • End.of (f ≫ dagger f) := by
  have hconj := conjugate_le_conjugate ha.le_algebraMap_norm_self f
  have hsmul : End.of (f ≫ (algebraMap ℝ (End Y) ‖a‖).asHom ≫ dagger f) =
      ‖a‖ • End.of (f ≫ dagger f) := by
    apply End.ext
    rw [IsScalarTower.algebraMap_apply ℝ ℂ (End Y), End.algebraMap_asHom,
      ← algebraMap_smul ℂ ‖a‖, End.smul_asHom]
    simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp]
  rwa [hsmul] at hconj

/-- Composition norm bound in the spectral order:
`(f ≫ g) ≫ dagger (f ≫ g) ≤ ‖g‖ ^ 2 • (f ≫ dagger f)` in `End X`. -/
theorem comp_self_comp_dagger_le (f : X ⟶ Y) (g : Y ⟶ Z) :
    End.of ((f ≫ g) ≫ dagger (f ≫ g)) ≤ ‖g‖ ^ 2 • End.of (f ≫ dagger f) := by
  have h := conjugate_le_norm_smul (self_comp_dagger_nonneg g).isSelfAdjoint f
  simpa only [End.norm_of, norm_self_comp_dagger, dagger_comp, Category.assoc] using h

/-- C*-algebra-valued Cauchy–Schwarz inequality:
`star (End.of (f ≫ dagger g)) * End.of (f ≫ dagger g) ≤ ‖g‖ ^ 2 • End.of (f ≫ dagger f)`. -/
theorem star_mul_self_comp_dagger_le (f g : X ⟶ Y) :
    star (End.of (f ≫ dagger g)) * End.of (f ≫ dagger g) ≤
      ‖g‖ ^ 2 • End.of (f ≫ dagger f) := by
  have h := conjugate_le_norm_smul (dagger_comp_self_nonneg g).isSelfAdjoint f
  have hlhs : End.of (f ≫ (End.of (dagger g ≫ g)).asHom ≫ dagger f) =
      star (End.of (f ≫ dagger g)) * End.of (f ≫ dagger g) := by
    apply End.ext
    simp only [End.mul_asHom, End.star_asHom, dagger_comp, dagger_dagger, Category.assoc]
  rw [hlhs, End.norm_of, norm_dagger_comp_self] at h
  exact h

/-- C*-algebra-valued Cauchy–Schwarz inequality in the opposite product order:
`End.of (f ≫ dagger g) * star (End.of (f ≫ dagger g)) ≤ ‖f‖ ^ 2 • End.of (g ≫ dagger g)`. -/
theorem mul_star_self_comp_dagger_le (f g : X ⟶ Y) :
    End.of (f ≫ dagger g) * star (End.of (f ≫ dagger g)) ≤
      ‖f‖ ^ 2 • End.of (g ≫ dagger g) := by
  have heq : End.of (f ≫ dagger g) = star (End.of (g ≫ dagger f)) := by
    apply End.ext
    simp
  rw [heq, star_star]
  exact star_mul_self_comp_dagger_le g f

section FunctionalCauchySchwarz

variable {F : Type*} [FunLike F (End X) ℂ] [LinearMapClass F ℂ (End X) ℂ]
  [OrderHomClass F (End X) ℂ]

/-- Squared positive-functional Cauchy–Schwarz inequality for morphisms `f g : X ⟶ Y` and a
positive linear functional `φ` on `End X`. -/
theorem norm_map_comp_dagger_sq_le (φ : F) (f g : X ⟶ Y) :
    ‖φ (End.of (f ≫ dagger g))‖ ^ 2 ≤
      ‖φ (End.of (f ≫ dagger f))‖ * ‖φ (End.of (g ≫ dagger g))‖ := by
  let ψ : End X →ₚ[ℂ] ℂ := PositiveLinearMap.ofClass φ
  have hstar (u v : X ⟶ Y) : star (ψ (End.of (u ≫ dagger v))) = ψ (End.of (v ≫ dagger u)) := by
    have heq : star (End.of (u ≫ dagger v)) = End.of (v ≫ dagger u) := by apply End.ext; simp
    rw [← map_star ψ, heq]
  let core : PreInnerProductSpace.Core ℂ (X ⟶ Y) :=
    { inner := fun u v => ψ (End.of (v ≫ dagger u))
      conj_inner_symm := fun u v => by rw [← Complex.star_def, hstar]
      re_inner_nonneg := fun u =>
        (RCLike.nonneg_iff.mp (ψ.map_nonneg (self_comp_dagger_nonneg u))).1
      add_left := fun u v w => by
        simp only [dagger_add, Preadditive.comp_add, End.of_add, map_add]
      smul_left := fun u v c => by
        simp only [dagger_smul, Linear.comp_smul, End.of_smul, map_smul, smul_eq_mul,
          Complex.star_def] }
  have hinner (u v : X ⟶ Y) : core.inner u v = ψ (End.of (v ≫ dagger u)) := rfl
  have h := @InnerProductSpace.Core.inner_mul_inner_self_le ℂ (X ⟶ Y) _ _ _ core g f
  simp only [hinner, RCLike.re_to_complex] at h
  rw [← hstar f g, norm_star, ← sq,
    Complex.re_eq_norm.mpr (ψ.map_nonneg (self_comp_dagger_nonneg g)),
    Complex.re_eq_norm.mpr (ψ.map_nonneg (self_comp_dagger_nonneg f)), mul_comm] at h
  exact h

/-- Positive-functional Cauchy–Schwarz inequality for morphisms `f g : X ⟶ Y` and a positive
linear functional `φ` on `End X`. -/
theorem norm_map_comp_dagger_le (φ : F) (f g : X ⟶ Y) :
    ‖φ (End.of (f ≫ dagger g))‖ ≤
      √‖φ (End.of (f ≫ dagger f))‖ * √‖φ (End.of (g ≫ dagger g))‖ := by
  rw [← Real.sqrt_mul (norm_nonneg _)]
  exact Real.le_sqrt_of_sq_le (norm_map_comp_dagger_sq_le φ f g)

end FunctionalCauchySchwarz

end TauCeti.CStarCategory
