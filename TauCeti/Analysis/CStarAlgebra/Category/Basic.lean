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
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Order.Hom.Basic
public import TauCeti.CategoryTheory.Dagger.Basic

import Mathlib.Algebra.Order.Module.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.Basic
import TauCeti.CategoryTheory.Linear.Endomorphism

/-!
# C*-categories

A C*-category is a complex linear dagger category whose Hom spaces are Banach spaces, with
contractive composition, the C*-identity `‖f†f‖ = ‖f‖²`, and `f†f` positive in `End X` for
every arrow `f` out of `X`. Here `f†f` denotes the operator-order composite, which is
`f ≫ dagger f` in categorical notation.

`TauCeti.CStarCategory` adds this analytic structure to Mathlib's native `Preadditive` and
`Linear ℂ` carriers and to a conjugate-linear `TauCeti.DaggerCategory`. Positivity of `f†f`
is stated as `f ≫ dagger f = g ≫ dagger g` for an endomorphism `g` of `X`; in the C*-algebra
`End X` this is equivalent to `0 ≤ f†f` (`CategoryTheory.End.nonneg_iff`).

## Main declarations

* `TauCeti.CStarCategory`: the C*-category axioms on given Hom norms.
* `TauCeti.CStarCategory.norm_dagger` and `TauCeti.CStarCategory.norm_self_comp_dagger`: the
  dagger is isometric and the C*-identity holds with equality.
* `TauCeti.CStarCategory.norm_eq_zero_or_one_of_dagger_eq_of_comp_self` and
  `TauCeti.CStarCategory.norm_id`: self-adjoint idempotents have norm `0` or `1`, and identities of
  nonzero objects have norm one.
* `TauCeti.CStarCategory.daggerLinearIsometryEquiv` and `TauCeti.CStarCategory.compCLM`: the
  antilinear isometric dagger equivalence and contractive continuous bilinear composition.
* `CategoryTheory.End.instCStarAlgebra`: each endomorphism algebra `End X` is a unital
  C*-algebra, with Mathlib's operator-order multiplication and the dagger as star.
* `CategoryTheory.End.nonneg_iff`: the positive elements of `End X` are exactly the composites
  `f ≫ dagger f` for arrows `f` out of `X`.
* `TauCeti.CStarCategory.conjugate_le_conjugate`, `TauCeti.CStarCategory.comp_self_comp_dagger_le`,
  `TauCeti.CStarCategory.star_mul_self_comp_dagger_le`, and
  `TauCeti.CStarCategory.norm_map_comp_dagger_le`: conjugation monotonicity, C*-order
  Cauchy–Schwarz, and positive-functional Cauchy–Schwarz inequalities.

## Implementation notes

As for Mathlib's `CStarModule`, the class takes the Hom norms as `Norm` parameters and asks for
a `NormedSpace.Core`, rather than registering `NormedAddCommGroup` instances on Hom types: a
concrete category such as Hilbert spaces already carries normed structures on its Hom types,
whose uniformities need not be definitionally those induced by the norm. The abbreviations
`TauCeti.CStarCategory.normedAddCommGroup` and `TauCeti.CStarCategory.normedSpace` provide
these structures when no others are present. The type `End X` has no prior norm, so its
normed and C*-algebra structures are global instances.

## References

* P. Ghez, R. Lima, J. E. Roberts, *W*-categories*, Pacific J. Math. 120 (1985), 79–109.
* P. D. Mitchener, *C*-categories*, Proc. London Math. Soc. 84 (2002), 375–404.
-/

public section

noncomputable section

open CategoryTheory
open scoped ComplexOrder

universe v u

namespace TauCeti

/-- A *C*-category* structure on given norms of the Hom spaces of a complex linear dagger
category: the Hom spaces are complex Banach spaces, composition is contractive, the
C*-inequality `‖f‖² ≤ ‖f†f‖` holds, and `f†f` has the form `g†g` for an endomorphism `g`
of the source of `f`. Here `f†f` is the operator-order composite `f ≫ dagger f`. -/
class CStarCategory (C : Type u) [Category.{v} C] [Preadditive C] [Linear ℂ C]
    [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C]
    [∀ X Y : C, Norm (X ⟶ Y)] : Prop where
  /-- Each Hom space is a complex normed space for the given norm. -/
  normedSpaceCore (X Y : C) : NormedSpace.Core ℂ (X ⟶ Y)
  /-- Each Hom space is complete for the metric of its norm. -/
  completeSpace (X Y : C) :
    letI := NormedAddCommGroup.ofCore (normedSpaceCore X Y)
    CompleteSpace (X ⟶ Y)
  /-- Composition is contractive. -/
  norm_comp_le {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : ‖f ≫ g‖ ≤ ‖f‖ * ‖g‖
  /-- The C*-inequality; equality follows (`TauCeti.CStarCategory.norm_self_comp_dagger`). -/
  norm_mul_self_le {X Y : C} (f : X ⟶ Y) : ‖f‖ * ‖f‖ ≤ ‖f ≫ dagger f‖
  /-- Positivity of `f†f` in `End X`: it is `g†g` for some endomorphism `g` of `X`. -/
  exists_self_comp_dagger_eq {X Y : C} (f : X ⟶ Y) :
    ∃ g : X ⟶ X, f ≫ dagger f = g ≫ dagger g

namespace CStarCategory

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C]
  [∀ X Y : C, Norm (X ⟶ Y)] [CStarCategory C]

/-- The normed group structure of a Hom space of a C*-category. This is not an instance:
a Hom type may already carry a normed structure with a better uniformity. -/
abbrev normedAddCommGroup (X Y : C) : NormedAddCommGroup (X ⟶ Y) :=
  .ofCore (normedSpaceCore X Y)

/-- The complex normed space structure of a Hom space of a C*-category. This is not an
instance, for the same reason as `TauCeti.CStarCategory.normedAddCommGroup`. -/
abbrev normedSpace (X Y : C) :
    letI := normedAddCommGroup X Y
    NormedSpace ℂ (X ⟶ Y) :=
  letI := normedAddCommGroup X Y
  .ofCore (normedSpaceCore X Y)

variable {X Y Z : C}

/-- Hom norms are nonnegative. -/
theorem norm_nonneg (f : X ⟶ Y) : 0 ≤ ‖f‖ :=
  (normedSpaceCore X Y).norm_nonneg f

/-- An arrow has norm zero exactly when it is zero. -/
@[simp] theorem norm_eq_zero {f : X ⟶ Y} : ‖f‖ = 0 ↔ f = 0 :=
  (normedSpaceCore X Y).norm_eq_zero_iff f

/-- The zero arrow has norm zero. -/
@[simp] theorem norm_zero : ‖(0 : X ⟶ Y)‖ = 0 :=
  norm_eq_zero.2 rfl

/-- Hom norms are absolutely homogeneous for complex scalars. -/
theorem norm_smul (c : ℂ) (f : X ⟶ Y) : ‖c • f‖ = ‖c‖ * ‖f‖ :=
  (normedSpaceCore X Y).norm_smul c f

/-- Hom norms satisfy the triangle inequality. -/
theorem norm_add_le (f g : X ⟶ Y) : ‖f + g‖ ≤ ‖f‖ + ‖g‖ :=
  (normedSpaceCore X Y).norm_triangle f g

/-- Negating an arrow preserves its norm. -/
@[simp] theorem norm_neg (f : X ⟶ Y) : ‖-f‖ = ‖f‖ := by
  simpa using norm_smul (-1 : ℂ) f

/-- The dagger of a C*-category is isometric. -/
@[simp] theorem norm_dagger (f : X ⟶ Y) : ‖dagger f‖ = ‖f‖ := by
  -- `‖f‖² ≤ ‖f ≫ dagger f‖ ≤ ‖f‖ ‖dagger f‖` gives `‖f‖ ≤ ‖dagger f‖`, for `f` and `dagger f`.
  have key : ∀ {X Y : C} (f : X ⟶ Y), ‖f‖ ≤ ‖dagger f‖ := by
    intro X Y f
    have h := (norm_mul_self_le f).trans (norm_comp_le f (dagger f))
    rcases (norm_nonneg f).eq_or_lt with hf | hf
    · rw [← hf]
      exact norm_nonneg _
    · exact le_of_mul_le_mul_left h hf
  exact le_antisymm (by simpa using key (dagger f)) (key f)

/-- The C*-identity: `‖f†f‖ = ‖f‖²`, where `f†f` is `f ≫ dagger f`. -/
theorem norm_self_comp_dagger (f : X ⟶ Y) : ‖f ≫ dagger f‖ = ‖f‖ ^ 2 := by
  rw [pow_two]
  refine le_antisymm ?_ (norm_mul_self_le f)
  simpa using norm_comp_le f (dagger f)

/-- The C*-identity for `f f†`, where `f f†` is `dagger f ≫ f`. -/
theorem norm_dagger_comp_self (f : X ⟶ Y) : ‖dagger f ≫ f‖ = ‖f‖ ^ 2 := by
  simpa using norm_self_comp_dagger (dagger f)

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
  (norm_eq_zero_or_one_of_dagger_eq_of_comp_self hsa hidem).resolve_left (mt norm_eq_zero.mp hp)

/-- The norm of an identity morphism is either `0` or `1`. -/
theorem norm_id_eq_zero_or_one (X : C) : ‖𝟙 X‖ = 0 ∨ ‖𝟙 X‖ = 1 :=
  norm_eq_zero_or_one_of_dagger_eq_of_comp_self (dagger_id X) (Category.id_comp _)

/-- The identity of an object has norm at most one. -/
theorem norm_id_le_one (X : C) : ‖𝟙 X‖ ≤ 1 :=
  norm_le_one_of_dagger_eq_of_comp_self (dagger_id X) (Category.id_comp _)

/-- An identity morphism has norm `0` if and only if its object is a zero object. -/
theorem norm_id_eq_zero_iff_isZero (X : C) : ‖𝟙 X‖ = 0 ↔ Limits.IsZero X := by
  rw [norm_eq_zero, Limits.IsZero.iff_id_eq_zero]

/-- An identity morphism has norm `1` if and only if its object is not a zero object. -/
theorem norm_id_eq_one_iff_not_isZero (X : C) : ‖𝟙 X‖ = 1 ↔ ¬ Limits.IsZero X := by
  rw [← norm_id_eq_zero_iff_isZero]
  rcases norm_id_eq_zero_or_one X with h | h <;> simp [h]

/-- The identity of an object that is not a zero object has norm one. -/
theorem norm_id {X : C} (hX : ¬ Limits.IsZero X) : ‖𝟙 X‖ = 1 :=
  (norm_id_eq_one_iff_not_isZero X).2 hX

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
    exact norm_id_le_one X
  exact (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp hsq

/-- An arrow with `u ≫ dagger u = 𝟙 X` on a non-zero object `X` has norm `1`. -/
theorem norm_eq_one_of_comp_dagger_eq_id {u : X ⟶ Y} (hu : u ≫ dagger u = 𝟙 X)
    (hX : ¬ Limits.IsZero X) : ‖u‖ = 1 := by
  refine (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp ?_
  rw [← norm_self_comp_dagger, hu, one_pow]
  exact norm_id hX

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

/-- The dagger as an antilinear isometric equivalence `(X ⟶ Y) ≃ₗᵢ⋆[ℂ] (Y ⟶ X)` for the
normed structures induced by `TauCeti.CStarCategory.normedAddCommGroup`. -/
def daggerLinearIsometryEquiv (X Y : C) :
    letI := normedAddCommGroup X Y
    letI := normedAddCommGroup Y X
    (X ⟶ Y) ≃ₗᵢ⋆[ℂ] (Y ⟶ X) :=
  letI := normedAddCommGroup X Y
  letI := normedAddCommGroup Y X
  { toFun := dagger
    invFun := dagger
    left_inv := dagger_dagger
    right_inv := dagger_dagger
    map_add' := dagger_add
    map_smul' := dagger_smul
    norm_map' := norm_dagger }

/-- Evaluation of the antilinear isometric dagger equivalence. -/
@[simp] theorem daggerLinearIsometryEquiv_apply (f : X ⟶ Y) :
    daggerLinearIsometryEquiv X Y f = dagger f := (rfl)

/-- The inverse of the antilinear isometric dagger equivalence swaps endpoints. -/
@[simp] theorem daggerLinearIsometryEquiv_symm :
    letI := normedAddCommGroup X Y
    letI := normedAddCommGroup Y X
    (daggerLinearIsometryEquiv X Y).symm = daggerLinearIsometryEquiv Y X := (rfl)

/-- Taking the dagger is continuous on Hom spaces. -/
theorem continuous_dagger :
    letI := normedAddCommGroup X Y
    letI := normedAddCommGroup Y X
    Continuous (dagger : (X ⟶ Y) → (Y ⟶ X)) :=
  letI := normedAddCommGroup X Y
  letI := normedAddCommGroup Y X
  (daggerLinearIsometryEquiv X Y).continuous

/-- Composition as a continuous bilinear map `(X ⟶ Y) →L[ℂ] (Y ⟶ Z) →L[ℂ] (X ⟶ Z)` for the
normed structures induced by `TauCeti.CStarCategory.normedAddCommGroup`. -/
def compCLM (X Y Z : C) :
    letI := normedAddCommGroup X Y
    letI := normedAddCommGroup Y Z
    letI := normedAddCommGroup X Z
    letI := normedSpace X Z
    (X ⟶ Y) →L[ℂ] (Y ⟶ Z) →L[ℂ] (X ⟶ Z) :=
  letI := normedAddCommGroup X Y
  letI := normedSpace X Y
  letI := normedAddCommGroup Y Z
  letI := normedSpace Y Z
  letI := normedAddCommGroup X Z
  letI := normedSpace X Z
  LinearMap.mkContinuous₂ (Linear.comp (S := ℂ) X Y Z) 1 fun f g => by
    simpa only [Linear.comp_apply, Linear.leftComp_apply, one_mul] using norm_comp_le f g

/-- Evaluation of the continuous bilinear composition map. -/
@[simp] theorem compCLM_apply (f : X ⟶ Y) (g : Y ⟶ Z) : compCLM X Y Z f g = f ≫ g := (rfl)

/-- Continuous bilinear composition is contractive. -/
theorem norm_compCLM_le (X Y Z : C) :
    letI := normedAddCommGroup X Y
    letI := normedSpace X Y
    letI := normedAddCommGroup Y Z
    letI := normedSpace Y Z
    letI := normedAddCommGroup X Z
    letI := normedSpace X Z
    ‖compCLM X Y Z‖ ≤ 1 := by
  let := normedAddCommGroup X Y
  let := normedSpace X Y
  let := normedAddCommGroup Y Z
  let := normedSpace Y Z
  let := normedAddCommGroup X Z
  let := normedSpace X Z
  exact LinearMap.mkContinuous₂_norm_le _ zero_le_one _

/-- Precomposition by a fixed morphism `f : X ⟶ Y` has operator norm at most `‖f‖`. -/
theorem norm_compCLM_apply_le (f : X ⟶ Y) (Z : C) :
    letI := normedAddCommGroup Y Z
    letI := normedSpace Y Z
    letI := normedAddCommGroup X Z
    letI := normedSpace X Z
    ‖compCLM X Y Z f‖ ≤ ‖f‖ := by
  let := normedAddCommGroup Y Z
  let := normedSpace Y Z
  let := normedAddCommGroup X Z
  let := normedSpace X Z
  exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f) (norm_comp_le f)

/-- Postcomposition by a fixed morphism `g : Y ⟶ Z` has operator norm at most `‖g‖`. -/
theorem norm_compCLM_flip_apply_le (X : C) (g : Y ⟶ Z) :
    letI := normedAddCommGroup X Y
    letI := normedSpace X Y
    letI := normedAddCommGroup X Z
    letI := normedSpace X Z
    letI := normedAddCommGroup Y Z
    letI := normedSpace Y Z
    ‖(compCLM X Y Z).flip g‖ ≤ ‖g‖ := by
  let := normedAddCommGroup X Y
  let := normedSpace X Y
  let := normedAddCommGroup X Z
  let := normedSpace X Z
  let := normedAddCommGroup Y Z
  let := normedSpace Y Z
  exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg g) fun f =>
    (norm_comp_le f g).trans_eq (mul_comm _ _)

end CStarCategory

/-! ### Norm bounds for unitary morphisms -/

namespace IsUnitary

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C]
  [∀ X Y : C, Norm (X ⟶ Y)] [CStarCategory C] {X Y Z : C}

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

namespace CategoryTheory.End

open TauCeti

variable {C : Type u} [Category.{v} C]

section Norm

variable [∀ X Y : C, Norm (X ⟶ Y)] {X : C}

/-- An endomorphism has the norm of its underlying arrow. -/
instance instNorm : Norm (End X) where
  norm a := ‖a.asHom‖

/-- The norm of an endomorphism is the norm of its underlying arrow. -/
theorem norm_def (a : End X) : ‖a‖ = ‖a.asHom‖ := (rfl)

/-- Regarding an arrow as an endomorphism preserves its norm. -/
@[simp] theorem norm_of (f : X ⟶ X) : ‖End.of f‖ = ‖f‖ := (rfl)

end Norm

variable [Preadditive C] [Linear ℂ C] [DaggerCategory C] [DaggerPreadditive C]
  [DaggerLinear ℂ C] [∀ X Y : C, Norm (X ⟶ Y)] [CStarCategory C] {X : C}

/-- The normed space axioms for `End X`, transported from the Hom space of `X`. -/
theorem normedSpaceCore (X : C) : NormedSpace.Core ℂ (End X) where
  norm_nonneg a := CStarCategory.norm_nonneg a.asHom
  norm_smul c a := by
    simpa only [norm_def, smul_asHom] using
      (CStarCategory.normedSpaceCore X X).norm_smul c a.asHom
  norm_triangle a b := by
    simpa only [norm_def, add_asHom] using
      (CStarCategory.normedSpaceCore X X).norm_triangle a.asHom b.asHom
  norm_eq_zero_iff a := by
    rw [norm_def, CStarCategory.norm_eq_zero, End.ext_iff, zero_asHom]

/-- `End X` is a normed group for the norm of its underlying arrows. -/
instance instNormedAddCommGroup : NormedAddCommGroup (End X) :=
  .ofCore (normedSpaceCore X)

/-- `End X` is a normed ring: its operator-order multiplication is submultiplicative. -/
instance instNormedRing : NormedRing (End X) where
  __ := (inferInstance : NormedAddCommGroup (End X))
  __ := (inferInstance : Ring (End X))
  norm_mul_le a b := by
    simpa only [norm_def, mul_asHom, mul_comm ‖a.asHom‖] using
      CStarCategory.norm_comp_le b.asHom a.asHom

/-- `End X` is a normed complex algebra. -/
instance instNormedAlgebra : NormedAlgebra ℂ (End X) where
  norm_smul_le c a := ((normedSpaceCore X).norm_smul c a).le

/-- The underlying-morphism map as a linear isometric equivalence `End X ≃ₗᵢ[ℂ] (X ⟶ X)`. -/
def asHomLinearIsometryEquiv (X : C) :
    letI := CStarCategory.normedAddCommGroup X X
    End X ≃ₗᵢ[ℂ] (X ⟶ X) :=
  letI := CStarCategory.normedAddCommGroup X X
  { End.linearEquiv with norm_map' _ := rfl }

/-- Evaluation of `End.asHomLinearIsometryEquiv`. -/
@[simp] theorem asHomLinearIsometryEquiv_apply (a : End X) :
    asHomLinearIsometryEquiv X a = a.asHom := (rfl)

/-- The inverse of `End.asHomLinearIsometryEquiv` is `End.of`. -/
@[simp] theorem asHomLinearIsometryEquiv_symm_apply (f : X ⟶ X) :
    letI := CStarCategory.normedAddCommGroup X X
    (asHomLinearIsometryEquiv X).symm f = End.of f := (rfl)

/-- `End X` is complete, since the Hom space of `X` is. -/
instance instCompleteSpace : CompleteSpace (End X) := by
  let := CStarCategory.normedAddCommGroup X X
  have : CompleteSpace (X ⟶ X) := CStarCategory.completeSpace X X
  let e : End X ≃ᵢ (X ⟶ X) :=
    { toEquiv := End.addEquiv.toEquiv
      isometry_toFun := AddMonoidHomClass.isometry_of_norm End.addEquiv fun a => by
        rw [End.addEquiv_apply, End.norm_def] }
  exact e.completeSpace

/-- The C*-identity in `End X`, from the C*-inequality of the category. -/
instance instCStarRing : CStarRing (End X) where
  norm_mul_self_le a := by
    simpa only [norm_def, mul_asHom, star_asHom] using CStarCategory.norm_mul_self_le a.asHom

/-- Each endomorphism algebra of a C*-category is a unital C*-algebra, with the dagger as
star and Mathlib's operator-order multiplication. -/
instance instCStarAlgebra : CStarAlgebra (End X) where

/-- The positive cone of the C*-algebra `End X`: self-adjoint elements with nonnegative
spectrum. -/
instance instPartialOrder : PartialOrder (End X) := CStarAlgebra.spectralOrder (End X)

/-- The order of `End X` is the C*-algebra order. -/
instance instStarOrderedRing : StarOrderedRing (End X) :=
  CStarAlgebra.spectralOrderedRing (End X)

/-- For an arrow `f` out of `X`, the endomorphism `f†f`, that is `f ≫ dagger f`, is
positive in the C*-algebra `End X`. -/
theorem self_comp_dagger_nonneg {Y : C} (f : X ⟶ Y) : 0 ≤ End.of (f ≫ dagger f) := by
  obtain ⟨g, hg⟩ := CStarCategory.exists_self_comp_dagger_eq f
  rw [hg]
  exact star_mul_self_nonneg (End.of g)

/-- For an arrow `f` into `X`, the endomorphism `f f†`, that is `dagger f ≫ f`, is
positive in the C*-algebra `End X`. -/
theorem dagger_comp_self_nonneg {Y : C} (f : Y ⟶ X) : 0 ≤ End.of (dagger f ≫ f) := by
  simpa only [dagger_dagger] using self_comp_dagger_nonneg (dagger f)

/-- The positive elements of `End X` are exactly the endomorphisms `f ≫ dagger f`, for arrows
`f` out of `X`. -/
theorem nonneg_iff {a : End X} : 0 ≤ a ↔ ∃ (Y : C) (f : X ⟶ Y), a = End.of (f ≫ dagger f) := by
  refine ⟨fun ha => ?_, ?_⟩
  · obtain ⟨b, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 ha
    exact ⟨X, b.asHom, End.ext (by simp)⟩
  · rintro ⟨Y, f, rfl⟩
    exact self_comp_dagger_nonneg f

/-- An endomorphism `a : End X` is positive if and only if `a.asHom = g ≫ dagger g` for some
endomorphism `g : X ⟶ X`. -/
theorem nonneg_iff_exists_self_comp_dagger {a : End X} :
    0 ≤ a ↔ ∃ g : X ⟶ X, a.asHom = g ≫ dagger g :=
  CStarAlgebra.nonneg_iff_eq_star_mul_self.trans
    ⟨fun ⟨b, hb⟩ =>
      ⟨b.asHom, by simpa only [End.mul_asHom, End.star_asHom] using congrArg End.asHom hb⟩,
     fun ⟨g, hg⟩ => ⟨End.of g, End.ext (by simpa only [End.mul_asHom, End.star_asHom] using hg)⟩⟩

end CategoryTheory.End

/-! ### Conjugation monotonicity and Cauchy–Schwarz inequalities -/

namespace TauCeti.CStarCategory

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C]
  [∀ X Y : C, Norm (X ⟶ Y)] [CStarCategory C] {X Y Z : C}

/-- Conjugating a positive endomorphism `a : End Y` by `f : X ⟶ Y` produces a positive
endomorphism `f ≫ a.asHom ≫ dagger f` in `End X`. -/
theorem conjugate_nonneg {a : End Y} (ha : 0 ≤ a) (f : X ⟶ Y) :
    0 ≤ End.of (f ≫ a.asHom ≫ dagger f) := by
  obtain ⟨g, hg⟩ := End.nonneg_iff_exists_self_comp_dagger.mp ha
  have hcomp : f ≫ a.asHom ≫ dagger f = (f ≫ g) ≫ dagger (f ≫ g) := by
    simp only [hg, dagger_comp, Category.assoc]
  rw [hcomp]
  exact End.self_comp_dagger_nonneg (f ≫ g)

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
  have h := conjugate_le_norm_smul (End.self_comp_dagger_nonneg g).isSelfAdjoint f
  simpa only [End.norm_of, norm_self_comp_dagger, dagger_comp, Category.assoc] using h

/-- C*-algebra-valued Cauchy–Schwarz inequality:
`star (End.of (f ≫ dagger g)) * End.of (f ≫ dagger g) ≤ ‖g‖ ^ 2 • End.of (f ≫ dagger f)`. -/
theorem star_mul_self_comp_dagger_le (f g : X ⟶ Y) :
    star (End.of (f ≫ dagger g)) * End.of (f ≫ dagger g) ≤
      ‖g‖ ^ 2 • End.of (f ≫ dagger f) := by
  have h := conjugate_le_norm_smul (End.dagger_comp_self_nonneg g).isSelfAdjoint f
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
        (RCLike.nonneg_iff.mp (ψ.map_nonneg (End.self_comp_dagger_nonneg u))).1
      add_left := fun u v w => by
        simp only [dagger_add, Preadditive.comp_add, End.of_add, map_add]
      smul_left := fun u v c => by
        simp only [dagger_smul, Linear.comp_smul, End.of_smul, map_smul, smul_eq_mul,
          Complex.star_def] }
  have hinner (u v : X ⟶ Y) : core.inner u v = ψ (End.of (v ≫ dagger u)) := rfl
  have h := @InnerProductSpace.Core.inner_mul_inner_self_le ℂ (X ⟶ Y) _ _ _ core g f
  simp only [hinner, RCLike.re_to_complex] at h
  rw [← hstar f g, norm_star, ← sq,
    Complex.re_eq_norm.mpr (ψ.map_nonneg (End.self_comp_dagger_nonneg g)),
    Complex.re_eq_norm.mpr (ψ.map_nonneg (End.self_comp_dagger_nonneg f)), mul_comm] at h
  exact h

/-- Positive-functional Cauchy–Schwarz inequality for morphisms `f g : X ⟶ Y` and a positive
linear functional `φ` on `End X`. -/
theorem norm_map_comp_dagger_le (φ : F) (f g : X ⟶ Y) :
    ‖φ (End.of (f ≫ dagger g))‖ ≤
      √‖φ (End.of (f ≫ dagger f))‖ * √‖φ (End.of (g ≫ dagger g))‖ := by
  rw [← Real.sqrt_mul (_root_.norm_nonneg _)]
  exact Real.le_sqrt_of_sq_le (norm_map_comp_dagger_sq_le φ f g)

end FunctionalCauchySchwarz

end TauCeti.CStarCategory
