/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import TauCeti.CategoryTheory.Dagger.Linear

/-!
# C*-categories and their endomorphism C*-algebras

A **C\*-category** (`TauCeti.CStarCategory`) is a complex linear dagger category whose Hom spaces
carry complete norms making composition bilinear and contractive, satisfying the C\*-inequality
`‖f‖ ^ 2 ≤ ‖f ≫ dagger f‖` (which forces the dagger to be isometric and `‖f ≫ dagger f‖ = ‖f‖ ^ 2`),
and satisfying positivity: every `f ≫ dagger f` is of the form `g ≫ dagger g` for an endomorphism
`g : X ⟶ X`.

Each endomorphism algebra `CategoryTheory.End X` inherits a compatible `CStarAlgebra` structure
under Mathlib's operator-order multiplication `(a * b).asHom = b.asHom ≫ a.asHom`, together with
its canonical spectral partial order (`CStarAlgebra.spectralOrder`) and `StarOrderedRing`
instance. Under this order, `End.of (f ≫ dagger f)` and `End.of (dagger f ≫ f)` are positive for
every morphism `f : X ⟶ Y`; conversely, `TauCeti.CStarCategory.ofSpectrumNonneg` constructs a
`CStarCategory` from nonnegativity of the real parts of the complex spectrum of
`End.of (f ≫ dagger f)`.

The positivity condition on off-diagonal composites `f ≫ dagger f` cannot be omitted when `C` has
more than one object: on a two-object category `{0, 1}` with one-dimensional Hom spaces `ℂ`,
setting `dagger z = -star z` on off-diagonal arrows satisfies `‖f ≫ dagger f‖ = ‖f‖ ^ 2` while
producing negative elements `f ≫ dagger f = -|z| ^ 2 • 𝟙 0`.

## Main declarations

* `TauCeti.CStarCategory`: the typeclass of C\*-categories on a `ℂ`-linear `DaggerCategory`.
* `CategoryTheory.End.instCStarAlgebra`, `CategoryTheory.End.instPartialOrder`,
  `CategoryTheory.End.instStarOrderedRing`: the C\*-algebra and spectral-order structure on
  `End X`.
* `TauCeti.CStarCategory.ofSpectrumNonneg`: constructor building `CStarCategory C` from spectral
  nonnegativity of `End.of (f ≫ dagger f)`.
* `TauCeti.daggerLinearIsometryEquiv`: the conjugate-linear isometric equivalence
  `(X ⟶ Y) ≃ₗᵢ⋆[ℂ] (Y ⟶ X)`.
* `TauCeti.leftCompCLM`, `TauCeti.rightCompCLM`, `TauCeti.compCLM`: composition bundled as
  continuous linear and continuous bilinear maps, with closed composition-annihilator kernels.
* `TauCeti.inducedCategoryCStar`, `TauCeti.fullSubcategoryCStar`: C\*-category instances on
  induced categories and full subcategories.

## References

* P. Ghez, R. Lima, J. E. Roberts, *W\*-categories*, Pacific J. Math. **120** (1985), 79–109.
* P. D. Mitchener, *C\*-categories*, Proc. London Math. Soc. (3) **84** (2002), 375–404.
-/

public section

noncomputable section

open CategoryTheory

universe w v u

namespace TauCeti

/-- A **C\*-category** is a `ℂ`-linear dagger category equipped with Banach-space norms on its Hom
spaces such that composition is contractive, `‖f‖ ^ 2 ≤ ‖f ≫ dagger f‖` for every arrow `f`, and
every `f ≫ dagger f` is of the form `g ≫ dagger g` for an endomorphism `g : X ⟶ X`.

Taking `[Preadditive C]` and `[Linear ℂ C]` as parameters keeps the underlying additive group and
`ℂ`-module structures on `X ⟶ Y` definitionally equal to those of the ambient linear category. -/
class CStarCategory (C : Type u) [Category.{v} C] [DaggerCategory C]
    [Preadditive C] [Linear ℂ C] extends DaggerPreadditive C, DaggerLinear ℂ C where
  /-- The norm on each Hom space. -/
  homNorm : ∀ X Y : C, Norm (X ⟶ Y) := by infer_instance
  /-- The metric space structure on each Hom space. -/
  homMetricSpace : ∀ X Y : C, MetricSpace (X ⟶ Y) := by infer_instance
  /-- Distance on each Hom space is induced by the norm and group subtraction. -/
  dist_eq : ∀ {X Y : C} (f g : X ⟶ Y), dist f g = ‖-f + g‖ := by aesop
  /-- Complex scalar multiplication on Hom spaces is bounded by the product of norms. -/
  norm_smul_le : ∀ {X Y : C} (c : ℂ) (f : X ⟶ Y), ‖c • f‖ ≤ ‖c‖ * ‖f‖
  /-- Each Hom space is complete with respect to its metric. -/
  completeSpace : ∀ X Y : C, CompleteSpace (X ⟶ Y) := by infer_instance
  /-- Categorical composition is contractive (`‖f ≫ g‖ ≤ ‖g‖ * ‖f‖`). -/
  norm_comp_le : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), ‖f ≫ g‖ ≤ ‖g‖ * ‖f‖
  /-- The C\*-inequality `‖f‖ ^ 2 ≤ ‖f ≫ dagger f‖`, which implies equality and isometric dagger. -/
  norm_sq_le_comp_dagger : ∀ {X Y : C} (f : X ⟶ Y), ‖f‖ ^ 2 ≤ ‖f ≫ dagger f‖
  /-- Positivity of `f ≫ dagger f`: it equals `g ≫ dagger g` for some endomorphism `g : X ⟶ X`. -/
  exists_comp_dagger_eq : ∀ {X Y : C} (f : X ⟶ Y), ∃ g : X ⟶ X, f ≫ dagger f = g ≫ dagger g

export CStarCategory (norm_comp_le norm_sq_le_comp_dagger exists_comp_dagger_eq)

section HomBanachSpace

variable {C : Type u} [Category.{v} C] [DaggerCategory C] [Preadditive C] [Linear ℂ C]
variable [CStarCategory C] {W X Y Z : C}

instance (priority := 100) instHomNormedAddCommGroup (X Y : C) :
    NormedAddCommGroup (X ⟶ Y) where
  toNorm := CStarCategory.homNorm X Y
  toAddCommGroup := Preadditive.homGroup X Y
  toMetricSpace := CStarCategory.homMetricSpace X Y
  dist_eq := CStarCategory.dist_eq

instance (priority := 100) instHomNormedSpace (X Y : C) :
    NormedSpace ℂ (X ⟶ Y) where
  toModule := Linear.homModule X Y
  norm_smul_le := CStarCategory.norm_smul_le

instance (priority := 100) instHomCompleteSpace (X Y : C) :
    CompleteSpace (X ⟶ Y) :=
  CStarCategory.completeSpace X Y

/-- Taking the dagger does not increase the norm. -/
theorem norm_dagger_le (f : X ⟶ Y) : ‖dagger f‖ ≤ ‖f‖ := by
  obtain h0 | hpos := eq_zero_or_norm_pos (dagger f)
  · simp [h0]
  · refine le_of_mul_le_mul_right ?_ hpos
    calc
      ‖dagger f‖ * ‖dagger f‖ = ‖dagger f‖ ^ 2 := (sq _).symm
      _ ≤ ‖dagger f ≫ dagger (dagger f)‖ := norm_sq_le_comp_dagger (dagger f)
      _ = ‖dagger f ≫ f‖ := by rw [dagger_dagger]
      _ ≤ ‖f‖ * ‖dagger f‖ := norm_comp_le (dagger f) f

/-- Taking the dagger preserves the norm on Hom spaces. -/
@[simp] theorem norm_dagger (f : X ⟶ Y) : ‖dagger f‖ = ‖f‖ :=
  le_antisymm (norm_dagger_le f) (by simpa only [dagger_dagger] using norm_dagger_le (dagger f))

/-- Taking the dagger preserves the `ℝ≥0`-valued norm on Hom spaces. -/
@[simp] theorem nnNorm_dagger (f : X ⟶ Y) : ‖dagger f‖₊ = ‖f‖₊ :=
  Subtype.ext (norm_dagger f)

/-- Submultiplicativity of composition in `ℝ≥0`-norms. -/
theorem nnNorm_comp_le (f : X ⟶ Y) (g : Y ⟶ Z) : ‖f ≫ g‖₊ ≤ ‖g‖₊ * ‖f‖₊ :=
  norm_comp_le f g

/-- The C\*-identity `‖f ≫ dagger f‖ = ‖f‖ ^ 2` in categorical composition order. -/
@[simp] theorem norm_comp_dagger_self (f : X ⟶ Y) : ‖f ≫ dagger f‖ = ‖f‖ ^ 2 :=
  le_antisymm
    ((norm_comp_le f (dagger f)).trans_eq (by rw [norm_dagger, sq]))
    (norm_sq_le_comp_dagger f)

/-- The dual C\*-identity `‖dagger f ≫ f‖ = ‖f‖ ^ 2`. -/
@[simp] theorem norm_dagger_comp_self (f : X ⟶ Y) : ‖dagger f ≫ f‖ = ‖f‖ ^ 2 := by
  simpa only [dagger_dagger, norm_dagger] using norm_comp_dagger_self (dagger f)

/-- The `ℝ≥0`-norm C\*-identity `‖f ≫ dagger f‖₊ = ‖f‖₊ ^ 2`. -/
@[simp] theorem nnNorm_comp_dagger_self (f : X ⟶ Y) : ‖f ≫ dagger f‖₊ = ‖f‖₊ ^ 2 :=
  Subtype.ext <| by simp [norm_comp_dagger_self]

/-- The dual `ℝ≥0`-norm C\*-identity `‖dagger f ≫ f‖₊ = ‖f‖₊ ^ 2`. -/
@[simp] theorem nnNorm_dagger_comp_self (f : X ⟶ Y) : ‖dagger f ≫ f‖₊ = ‖f‖₊ ^ 2 :=
  Subtype.ext <| by simp [norm_dagger_comp_self]

/-- Composing an arrow with its dagger gives zero precisely when the arrow is zero. -/
@[simp] theorem comp_dagger_self_eq_zero (f : X ⟶ Y) : f ≫ dagger f = 0 ↔ f = 0 := by
  rw [← norm_eq_zero, norm_comp_dagger_self, sq_eq_zero_iff, norm_eq_zero]

/-- Composing the dagger of an arrow with the arrow gives zero precisely when the arrow is zero. -/
@[simp] theorem dagger_comp_self_eq_zero (f : X ⟶ Y) : dagger f ≫ f = 0 ↔ f = 0 := by
  rw [← norm_eq_zero, norm_dagger_comp_self, sq_eq_zero_iff, norm_eq_zero]

/-- Positivity of `dagger f ≫ f` as an endomorphism square: every `dagger f ≫ f` equals
`g ≫ dagger g` for some `g : Y ⟶ Y`. -/
theorem exists_dagger_comp_eq (f : X ⟶ Y) : ∃ g : Y ⟶ Y, dagger f ≫ f = g ≫ dagger g := by
  simpa only [dagger_dagger] using exists_comp_dagger_eq (dagger f)

/-- Taking daggers bundled as a conjugate-linear isometric equivalence between opposite Hom
spaces. -/
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
@[simp] theorem daggerLinearIsometryEquiv_symm :
    (daggerLinearIsometryEquiv X Y).symm = daggerLinearIsometryEquiv Y X := (rfl)

/-- Taking daggers is an isometry on Hom spaces. -/
theorem isometry_dagger : Isometry (dagger : (X ⟶ Y) → (Y ⟶ X)) :=
  (daggerLinearIsometryEquiv X Y).isometry

/-- Taking daggers preserves distances on Hom spaces. -/
@[simp] theorem dist_dagger_dagger (f g : X ⟶ Y) :
    dist (dagger f) (dagger g) = dist f g :=
  isometry_dagger.dist_eq f g

/-- Taking daggers is continuous on Hom spaces. -/
@[continuity, fun_prop] theorem continuous_dagger :
    Continuous (dagger : (X ⟶ Y) → (Y ⟶ X)) :=
  isometry_dagger.continuous

/-! ### Continuous bilinear composition and closed kernels -/

/-- Precomposition with a fixed arrow `f : X ⟶ Y`, bundled as a continuous `ℂ`-linear map. -/
def leftCompCLM (Z : C) (f : X ⟶ Y) : (Y ⟶ Z) →L[ℂ] (X ⟶ Z) :=
  LinearMap.mkContinuous (Linear.leftComp ℂ Z f) ‖f‖ fun g => by
    rw [Linear.leftComp_apply, mul_comm]
    exact norm_comp_le f g

/-- Evaluation of `leftCompCLM`. -/
@[simp] theorem leftCompCLM_apply (Z : C) (f : X ⟶ Y) (g : Y ⟶ Z) :
    leftCompCLM Z f g = f ≫ g := (rfl)

/-- Forgetting continuity from `leftCompCLM` recovers `CategoryTheory.Linear.leftComp`. -/
@[simp] theorem leftCompCLM_toLinearMap (Z : C) (f : X ⟶ Y) :
    (leftCompCLM Z f).toLinearMap = Linear.leftComp ℂ Z f := (rfl)

/-- Operator norm bound for `leftCompCLM`. -/
theorem norm_leftCompCLM_le (Z : C) (f : X ⟶ Y) : ‖leftCompCLM Z f‖ ≤ ‖f‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg f) _

/-- Postcomposition with a fixed arrow `g : Y ⟶ Z`, bundled as a continuous `ℂ`-linear map. -/
def rightCompCLM (X : C) (g : Y ⟶ Z) : (X ⟶ Y) →L[ℂ] (X ⟶ Z) :=
  LinearMap.mkContinuous (Linear.rightComp ℂ X g) ‖g‖ fun f => norm_comp_le f g

/-- Evaluation of `rightCompCLM`. -/
@[simp] theorem rightCompCLM_apply (X : C) (g : Y ⟶ Z) (f : X ⟶ Y) :
    rightCompCLM X g f = f ≫ g := (rfl)

/-- Forgetting continuity from `rightCompCLM` recovers `CategoryTheory.Linear.rightComp`. -/
@[simp] theorem rightCompCLM_toLinearMap (X : C) (g : Y ⟶ Z) :
    (rightCompCLM X g).toLinearMap = Linear.rightComp ℂ X g := (rfl)

/-- Operator norm bound for `rightCompCLM`. -/
theorem norm_rightCompCLM_le (X : C) (g : Y ⟶ Z) : ‖rightCompCLM X g‖ ≤ ‖g‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg g) _

/-- Categorical composition bundled as a continuous bilinear map of norm at most `1`. -/
def compCLM (X Y Z : C) : (X ⟶ Y) →L[ℂ] (Y ⟶ Z) →L[ℂ] (X ⟶ Z) :=
  LinearMap.mkContinuous₂ (Linear.comp (S := ℂ) X Y Z) 1 fun f g => by
    rw [Linear.comp_apply, Linear.leftComp_apply, one_mul, mul_comm]
    exact norm_comp_le f g

/-- Applying `compCLM` to its first argument recovers `leftCompCLM`. -/
@[simp] theorem compCLM_apply_left (f : X ⟶ Y) :
    compCLM X Y Z f = leftCompCLM Z f := by
  ext g; rfl

/-- Evaluation of `compCLM` on composable arrows. -/
theorem compCLM_apply (f : X ⟶ Y) (g : Y ⟶ Z) :
    compCLM X Y Z f g = f ≫ g := (rfl)

/-- The bilinear composition operator has norm at most `1`. -/
theorem norm_compCLM_le_one (X Y Z : C) : ‖compCLM X Y Z‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

/-- Categorical composition is jointly continuous on Hom spaces. -/
@[continuity, fun_prop] theorem continuous_comp :
    Continuous (fun p : (X ⟶ Y) × (Y ⟶ Z) => p.1 ≫ p.2) :=
  (compCLM X Y Z).isBoundedBilinearMap.continuous

/-- Arrows annihilated on the left by `f : X ⟶ Y` form a closed subspace of `Y ⟶ Z`. -/
theorem isClosed_setOf_comp_eq_zero_right (Z : C) (f : X ⟶ Y) :
    IsClosed { g : Y ⟶ Z | f ≫ g = 0 } :=
  (leftCompCLM Z f).isClosed_ker

/-- Arrows annihilated on the right by `g : Y ⟶ Z` form a closed subspace of `X ⟶ Y`. -/
theorem isClosed_setOf_comp_eq_zero_left (X : C) (g : Y ⟶ Z) :
    IsClosed { f : X ⟶ Y | f ≫ g = 0 } :=
  (rightCompCLM X g).isClosed_ker

/-! ### Unitary, isometric, and partial-isometry norm laws -/

/-- Postcomposing with a morphism satisfying `u ≫ dagger u = 𝟙 X` preserves norms. -/
theorem norm_comp_of_comp_dagger_id {u : X ⟶ Y} (hu : u ≫ dagger u = 𝟙 X) (f : W ⟶ X) :
    ‖f ≫ u‖ = ‖f‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← norm_comp_dagger_self,
    ← norm_comp_dagger_self f, dagger_comp, Category.assoc, ← Category.assoc u, hu,
    Category.id_comp]

/-- Precomposing with a morphism satisfying `dagger u ≫ u = 𝟙 Y` preserves norms. -/
theorem norm_comp_of_dagger_comp_id {u : X ⟶ Y} (hu : dagger u ≫ u = 𝟙 Y) (g : Y ⟶ Z) :
    ‖u ≫ g‖ = ‖g‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← norm_dagger_comp_self,
    ← norm_dagger_comp_self g, dagger_comp, Category.assoc, ← Category.assoc (dagger u), hu,
    Category.id_comp]

/-- Postcomposing with a unitary arrow preserves norms. -/
@[simp] theorem IsUnitary.norm_comp_right {u : X ⟶ Y} (hu : IsUnitary u) (f : W ⟶ X) :
    ‖f ≫ u‖ = ‖f‖ :=
  norm_comp_of_comp_dagger_id hu.hom_dagger_id f

/-- Precomposing with a unitary arrow preserves norms. -/
@[simp] theorem IsUnitary.norm_comp_left {u : X ⟶ Y} (hu : IsUnitary u) (g : Y ⟶ Z) :
    ‖u ≫ g‖ = ‖g‖ :=
  norm_comp_of_dagger_comp_id hu.dagger_hom_id g

/-- A nonzero partial isometry (`f ≫ dagger f ≫ f = f`) has norm `1`. -/
theorem norm_eq_one_of_comp_dagger_comp_self {f : X ⟶ Y} (hf : f ≫ dagger f ≫ f = f)
    (hf0 : f ≠ 0) : ‖f‖ = 1 := by
  have hpos : 0 < ‖f‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hf0)
  have hsq : (‖f‖ ^ 2) ^ 2 = ‖f‖ ^ 2 := by
    calc
      (‖f‖ ^ 2) ^ 2 = ‖f ≫ dagger f‖ ^ 2 := by rw [norm_comp_dagger_self]
      _ = ‖(f ≫ dagger f) ≫ dagger (f ≫ dagger f)‖ := (norm_comp_dagger_self _).symm
      _ = ‖(f ≫ dagger f ≫ f) ≫ dagger f‖ := by simp [Category.assoc]
      _ = ‖f ≫ dagger f‖ := by rw [hf]
      _ = ‖f‖ ^ 2 := norm_comp_dagger_self f
  have h1 : ‖f‖ ^ 2 = 1 := mul_left_cancel₀ hpos.ne' (by simpa only [sq, mul_one] using hsq)
  exact (sq_eq_one_iff.mp h1).resolve_right (by linarith [norm_nonneg f])

/-- Every partial isometry (`f ≫ dagger f ≫ f = f`) has norm at most `1`. -/
theorem norm_le_one_of_comp_dagger_comp_self {f : X ⟶ Y} (hf : f ≫ dagger f ≫ f = f) :
    ‖f‖ ≤ 1 := by
  obtain rfl | hf0 := eq_or_ne f 0
  · simp
  · exact (norm_eq_one_of_comp_dagger_comp_self hf hf0).le

end HomBanachSpace

end TauCeti

/-! ### The C\*-algebra structure and spectral order on `CategoryTheory.End X` -/

namespace CategoryTheory.End

open TauCeti

variable {C : Type u} [Category.{v} C] [DaggerCategory C] [Preadditive C] [Linear ℂ C]
variable [CStarCategory C] {X Y : C}

instance instNorm : Norm (End X) where
  norm f := ‖f.asHom‖

/-- The norm of an endomorphism is the norm of its underlying arrow. -/
@[simp] theorem norm_asHom (f : End X) : ‖f.asHom‖ = ‖f‖ := (rfl)

/-- Wrapping an arrow as an endomorphism preserves its norm. -/
@[simp] theorem norm_of (f : X ⟶ X) : ‖End.of f‖ = ‖f‖ := (rfl)

instance instMetricSpace : MetricSpace (End X) :=
  MetricSpace.induced End.asHom (fun _ _ => End.ext) inferInstance

/-- Distance in `End X` agrees with distance of underlying arrows. -/
@[simp] theorem dist_asHom (f g : End X) : dist f.asHom g.asHom = dist f g := (rfl)

/-- Wrapping arrows in `End X` preserves distance. -/
@[simp] theorem dist_of (f g : X ⟶ X) : dist (End.of f) (End.of g) = dist f g := (rfl)

instance instNormedRing : NormedRing (End X) where
  toNorm := inferInstance
  toRing := inferInstance
  toMetricSpace := inferInstance
  dist_eq f g := dist_eq_norm_neg_add f.asHom g.asHom
  norm_mul_le f g := norm_comp_le g.asHom f.asHom

/-- The `ℝ≥0`-norm of an endomorphism agrees with that of its underlying arrow. -/
@[simp] theorem nnNorm_asHom (f : End X) : ‖f.asHom‖₊ = ‖f‖₊ := (rfl)

/-- Wrapping an arrow as an endomorphism preserves its `ℝ≥0`-norm. -/
@[simp] theorem nnNorm_of (f : X ⟶ X) : ‖End.of f‖₊ = ‖f‖₊ := (rfl)

instance instNormedAlgebra : NormedAlgebra ℂ (End X) where
  toAlgebra := inferInstance
  norm_smul_le c f := CStarCategory.norm_smul_le c f.asHom

/-- `End.asHom` bundled as a `ℂ`-linear isometric equivalence `End X ≃ₗᵢ[ℂ] (X ⟶ X)`. -/
def homLinearIsometryEquiv (X : C) : End X ≃ₗᵢ[ℂ] (X ⟶ X) where
  toFun := End.asHom
  invFun := End.of
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

/-- Applying `homLinearIsometryEquiv` extracts `asHom`. -/
@[simp] theorem homLinearIsometryEquiv_apply (f : End X) :
    homLinearIsometryEquiv X f = f.asHom := (rfl)

/-- Applying `(homLinearIsometryEquiv X).symm` wraps an arrow via `End.of`. -/
@[simp] theorem homLinearIsometryEquiv_symm_apply (f : X ⟶ X) :
    (homLinearIsometryEquiv X).symm f = End.of f := (rfl)

instance instCompleteSpace : CompleteSpace (End X) :=
  (IsUniformInducing.completeSpace_congr (f := (End.asHom : End X → (X ⟶ X))) ⟨rfl⟩
    (fun f => ⟨End.of f, rfl⟩)).2 inferInstance

instance instCStarRing : CStarRing (End X) where
  norm_mul_self_le f := by
    rw [← norm_asHom, ← norm_asHom, mul_asHom, star_asHom, ← sq]
    exact norm_sq_le_comp_dagger f.asHom

instance instCStarAlgebra : CStarAlgebra (End X) where

/-- Endomorphisms of an object in a C\*-category carry the spectral partial order. -/
instance instPartialOrder : PartialOrder (End X) :=
  CStarAlgebra.spectralOrder (End X)

instance instStarOrderedRing : StarOrderedRing (End X) :=
  CStarAlgebra.spectralOrderedRing (End X)

/-- For every morphism `f : X ⟶ Y`, `End.of (f ≫ dagger f)` is positive in `End X`. -/
@[simp] theorem of_comp_dagger_self_nonneg (f : X ⟶ Y) :
    0 ≤ End.of (f ≫ dagger f) := by
  obtain ⟨g, hg⟩ := exists_comp_dagger_eq f
  rw [hg, of_comp, of_dagger]
  exact star_mul_self_nonneg (End.of g)

/-- For every morphism `f : X ⟶ Y`, `End.of (dagger f ≫ f)` is positive in `End Y`. -/
@[simp] theorem of_dagger_comp_self_nonneg (f : X ⟶ Y) :
    0 ≤ End.of (dagger f ≫ f) := by
  simpa only [dagger_dagger] using of_comp_dagger_self_nonneg (dagger f)

/-- Every real spectral value of `End.of (f ≫ dagger f)` is nonnegative. -/
theorem spectrum_real_of_comp_dagger_self_nonneg (f : X ⟶ Y) {x : ℝ}
    (hx : x ∈ spectrum ℝ (End.of (f ≫ dagger f))) : 0 ≤ x :=
  spectrum_nonneg_of_nonneg (of_comp_dagger_self_nonneg f) hx

/-- Sandwiching a positive endomorphism `a : End Y` as `f ≫ a.asHom ≫ dagger f` gives a positive
endomorphism in `End X`. -/
theorem of_comp_nonneg_comp_dagger (f : X ⟶ Y) {a : End Y} (ha : 0 ≤ a) :
    0 ≤ End.of (f ≫ a.asHom ≫ dagger f) := by
  have hsq : (CFC.sqrt a).asHom ≫ dagger (CFC.sqrt a).asHom = a.asHom := by
    have h := congrArg End.asHom (CFC.sqrt_mul_sqrt_self a ha)
    simpa only [mul_asHom, (CFC.sqrt_nonneg a).isSelfAdjoint.star_eq, ← star_asHom] using h
  have hrew : f ≫ a.asHom ≫ dagger f =
      (f ≫ (CFC.sqrt a).asHom) ≫ dagger (f ≫ (CFC.sqrt a).asHom) := by
    rw [dagger_comp, Category.assoc, ← Category.assoc ((CFC.sqrt a).asHom), hsq]
  rw [hrew]
  exact of_comp_dagger_self_nonneg (f ≫ (CFC.sqrt a).asHom)

/-- Sandwiching a positive endomorphism `b : End X` as `dagger f ≫ b.asHom ≫ f` gives a positive
endomorphism in `End Y`. -/
theorem of_dagger_comp_nonneg_comp (f : X ⟶ Y) {b : End X} (hb : 0 ≤ b) :
    0 ≤ End.of (dagger f ≫ b.asHom ≫ f) := by
  simpa only [dagger_dagger] using of_comp_nonneg_comp_dagger (dagger f) hb

/-- Sandwiching `a ↦ End.of (f ≫ a.asHom ≫ dagger f)` bundled as a positive `ℂ`-linear map
`End Y →ₚ[ℂ] End X`. -/
def conjPositiveLinearMap (f : X ⟶ Y) : End Y →ₚ[ℂ] End X where
  toFun a := End.of (f ≫ a.asHom ≫ dagger f)
  map_add' a b := by simp [Preadditive.comp_add, Preadditive.add_comp]
  map_smul' c a := by simp
  monotone' a b hab := by
    rw [← sub_nonneg] at hab ⊢
    simpa only [sub_asHom, Preadditive.comp_sub, Preadditive.sub_comp, of_sub] using
      of_comp_nonneg_comp_dagger f hab

/-- Evaluation of `End.conjPositiveLinearMap`. -/
@[simp] theorem conjPositiveLinearMap_apply (f : X ⟶ Y) (a : End Y) :
    conjPositiveLinearMap f a = End.of (f ≫ a.asHom ≫ dagger f) := (rfl)

/-- Sandwiching by `f : X ⟶ Y` is monotone from `End Y` to `End X`. -/
theorem conj_mono (f : X ⟶ Y) : Monotone (fun a : End Y => End.of (f ≫ a.asHom ≫ dagger f)) :=
  (conjPositiveLinearMap f).monotone

end CategoryTheory.End

namespace TauCeti

/-! ### Zero-object and identity-norm formulas -/

section ZeroObject

variable {C : Type u} [Category.{v} C] [DaggerCategory C] [Preadditive C] [Linear ℂ C]
variable [CStarCategory C] {X Y : C}

/-- Every arrow out of a zero object has norm `0`. -/
theorem isZero_norm_to (hX : Limits.IsZero X) (f : X ⟶ Y) : ‖f‖ = 0 := by
  rw [hX.eq_of_src f 0, norm_zero]

/-- Every arrow into a zero object has norm `0`. -/
theorem isZero_norm_from (hY : Limits.IsZero Y) (f : X ⟶ Y) : ‖f‖ = 0 := by
  rw [hY.eq_of_tgt f 0, norm_zero]

/-- The identity arrow of `X` has norm `0` precisely when `X` is a zero object. -/
theorem norm_id_eq_zero_iff_isZero (X : C) :
    ‖𝟙 X‖ = 0 ↔ Limits.IsZero X := by
  rw [norm_eq_zero, Limits.IsZero.iff_id_eq_zero]

/-- On a nonzero object `X`, the identity arrow has norm `1`. -/
theorem norm_id_of_not_isZero {X : C} (hX : ¬ Limits.IsZero X) : ‖𝟙 X‖ = 1 := by
  have hnt : Nontrivial (End X) :=
    ⟨⟨1, 0, fun h10 => hX ((Limits.IsZero.iff_id_eq_zero X).mpr (congrArg End.asHom h10))⟩⟩
  exact CStarRing.norm_one (E := End X)

/-- Every identity arrow in a C\*-category has norm `0` or `1`. -/
theorem norm_id_eq_zero_or_one (X : C) : ‖𝟙 X‖ = 0 ∨ ‖𝟙 X‖ = 1 := by
  by_cases hX : Limits.IsZero X
  · exact Or.inl ((norm_id_eq_zero_iff_isZero X).mpr hX)
  · exact Or.inr (norm_id_of_not_isZero hX)

/-- Every identity arrow in a C\*-category has norm at most `1`. -/
theorem norm_id_le_one (X : C) : ‖𝟙 X‖ ≤ 1 := by
  rcases norm_id_eq_zero_or_one X with h | h <;> linarith

/-- A unitary arrow out of a nonzero object has norm `1`. -/
theorem IsUnitary.norm_eq_one {u : X ⟶ Y} (hu : IsUnitary u) (hX : ¬ Limits.IsZero X) :
    ‖u‖ = 1 := by
  calc
    ‖u‖ = ‖𝟙 X ≫ u‖ := by rw [Category.id_comp]
    _ = ‖𝟙 X‖ := hu.norm_comp_right (𝟙 X)
    _ = 1 := norm_id_of_not_isZero hX

end ZeroObject

/-! ### Constructing a `CStarCategory` from spectral positivity -/

namespace CStarCategory

/-- Construct a `CStarCategory` from Banach Hom spaces, contractive composition,
`‖f‖ ^ 2 ≤ ‖f ≫ dagger f‖`, and nonnegativity of the real parts of the complex spectrum of
`End.of (f ≫ dagger f)`.

Because `End.of (f ≫ dagger f)` is self-adjoint in the Banach \*-algebra `End X`, its complex
spectrum automatically lies in `ℝ`; nonnegativity of the real parts therefore gives positivity in
the spectral order and supplies a self-adjoint square root `g` with
`f ≫ dagger f = g ≫ dagger g`. -/
@[instance_reducible]
def ofSpectrumNonneg {C : Type u} [Category.{v} C] [DaggerCategory C]
    [Preadditive C] [Linear ℂ C] [DaggerPreadditive C] [DaggerLinear ℂ C]
    [homNorm : ∀ X Y : C, Norm (X ⟶ Y)]
    [homMetricSpace : ∀ X Y : C, MetricSpace (X ⟶ Y)]
    [completeSpace : ∀ X Y : C, CompleteSpace (X ⟶ Y)]
    (hdist : ∀ {X Y : C} (f g : X ⟶ Y), dist f g = ‖-f + g‖ := by aesop)
    (hsmul : ∀ {X Y : C} (c : ℂ) (f : X ⟶ Y), ‖c • f‖ ≤ ‖c‖ * ‖f‖)
    (hcomp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), ‖f ≫ g‖ ≤ ‖g‖ * ‖f‖)
    (hsq : ∀ {X Y : C} (f : X ⟶ Y), ‖f‖ ^ 2 ≤ ‖f ≫ dagger f‖)
    (hspec : ∀ {X Y : C} (f : X ⟶ Y) (z : ℂ),
      z ∈ spectrum ℂ (End.of (f ≫ dagger f)) → 0 ≤ z.re) :
    CStarCategory C where
  homNorm := homNorm
  homMetricSpace := homMetricSpace
  dist_eq := hdist
  norm_smul_le := hsmul
  completeSpace := completeSpace
  norm_comp_le := hcomp
  norm_sq_le_comp_dagger := hsq
  exists_comp_dagger_eq {X Y} f := by
    let instNormEnd : Norm (End X) := ⟨fun a => ‖a.asHom‖⟩
    let instMetricEnd : MetricSpace (End X) :=
      MetricSpace.induced End.asHom (fun _ _ => End.ext) inferInstance
    let instNormedRingEnd : NormedRing (End X) :=
      { toNorm := instNormEnd
        toRing := inferInstance
        toMetricSpace := instMetricEnd
        dist_eq := fun a b => hdist a.asHom b.asHom
        norm_mul_le := fun a b => hcomp b.asHom a.asHom }
    let instNormedAlgEnd : NormedAlgebra ℂ (End X) :=
      { toAlgebra := inferInstance
        norm_smul_le := fun c a => hsmul c a.asHom }
    have instCompleteEnd : CompleteSpace (End X) :=
      (IsUniformInducing.completeSpace_congr (f := (End.asHom : End X → (X ⟶ X))) ⟨rfl⟩
        (fun g => ⟨End.of g, rfl⟩)).2 inferInstance
    have instCStarRingEnd : CStarRing (End X) :=
      { norm_mul_self_le := fun a => by
          change ‖a.asHom‖ * ‖a.asHom‖ ≤ ‖a.asHom ≫ dagger a.asHom‖
          simpa only [sq] using hsq a.asHom }
    let instCStarAlgEnd : CStarAlgebra (End X) := {}
    have hsa : IsSelfAdjoint (End.of (f ≫ dagger f)) := by
      rw [IsSelfAdjoint, ← End.of_dagger, dagger_comp, dagger_dagger]
    have hqr : QuasispectrumRestricts (End.of (f ≫ dagger f)) ContinuousMap.realToNNReal := by
      rw [QuasispectrumRestricts.nnreal_iff]
      intro x hx
      rw [mem_quasispectrum_iff] at hx
      rcases hx with rfl | hx'
      · exact le_rfl
      · have hxc : (algebraMap ℝ ℂ x) ∈ spectrum ℂ (End.of (f ≫ dagger f)) := by
          rw [← hsa.spectrumRestricts.algebraMap_image]
          exact ⟨x, hx', rfl⟩
        simpa using hspec f (algebraMap ℝ ℂ x) hxc
    obtain ⟨s, hs_sa, -, hs_sq⟩ :=
      CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts hsa hqr
    refine ⟨s.asHom, ?_⟩
    have hss : (star s * s).asHom = (End.of (f ≫ dagger f)).asHom := by
      rw [hs_sa.star_eq, hs_sq]
    exact hss.symm

end CStarCategory

/-! ### Induced categories and full subcategories -/

section InducedCategory

variable {C : Type u} [Category.{v} C] [DaggerCategory C] [Preadditive C] [Linear ℂ C]
variable [CStarCategory C]

/-- Induced categories of a C\*-category inherit a C\*-category structure via the restricted
norm. -/
instance inducedCategoryCStar {D : Type w} (F : D → C) :
    CStarCategory (InducedCategory C F) where
  homNorm X Y := ⟨fun f => ‖f.hom‖⟩
  homMetricSpace X Y :=
    MetricSpace.induced (fun f : X ⟶ Y => f.hom) (fun _ _ h => InducedCategory.hom_ext h)
      inferInstance
  dist_eq f g := dist_eq_norm_neg_add f.hom g.hom
  norm_smul_le c f := norm_smul_le c f.hom
  completeSpace X Y := by
    let _ : UniformSpace (X ⟶ Y) := UniformSpace.comap (fun f : X ⟶ Y => f.hom) inferInstance
    exact (IsUniformInducing.completeSpace_congr (f := fun f : X ⟶ Y => f.hom) ⟨rfl⟩
      (fun f => ⟨InducedCategory.homMk f, rfl⟩)).2 inferInstance
  norm_comp_le f g := norm_comp_le f.hom g.hom
  norm_sq_le_comp_dagger f := norm_sq_le_comp_dagger f.hom
  exists_comp_dagger_eq f := by
    obtain ⟨g, hg⟩ := exists_comp_dagger_eq f.hom
    exact ⟨InducedCategory.homMk g, InducedCategory.hom_ext hg⟩

/-- The norm of an arrow in an induced C\*-category equals the norm of its underlying arrow. -/
@[simp] theorem inducedCategory_norm_hom {D : Type w} {F : D → C}
    {X Y : InducedCategory C F} (f : X ⟶ Y) : ‖f.hom‖ = ‖f‖ := (rfl)

/-- Constructing an arrow in an induced C\*-category preserves its norm. -/
@[simp] theorem inducedCategory_norm_homMk {D : Type w} {F : D → C}
    {X Y : InducedCategory C F} (f : F X ⟶ F Y) :
    ‖InducedCategory.homMk (F := F) (X := X) (Y := Y) f‖ = ‖f‖ := (rfl)

/-- Every full subcategory of a C\*-category inherits a C\*-category structure. -/
instance fullSubcategoryCStar (Z : ObjectProperty C) : CStarCategory Z.FullSubcategory where
  homNorm X Y := ⟨fun f => ‖f.hom‖⟩
  homMetricSpace X Y :=
    MetricSpace.induced (fun f : X ⟶ Y => f.hom) (fun _ _ h => ObjectProperty.hom_ext Z h)
      inferInstance
  dist_eq f g := dist_eq_norm_neg_add f.hom g.hom
  norm_smul_le c f := norm_smul_le c f.hom
  completeSpace X Y := by
    let _ : UniformSpace (X ⟶ Y) := UniformSpace.comap (fun f : X ⟶ Y => f.hom) inferInstance
    exact (IsUniformInducing.completeSpace_congr (f := fun f : X ⟶ Y => f.hom) ⟨rfl⟩
      (fun f => ⟨Z.homMk f, rfl⟩)).2 inferInstance
  norm_comp_le f g := norm_comp_le f.hom g.hom
  norm_sq_le_comp_dagger f := norm_sq_le_comp_dagger f.hom
  exists_comp_dagger_eq f := by
    obtain ⟨g, hg⟩ := exists_comp_dagger_eq f.hom
    exact ⟨Z.homMk g, ObjectProperty.hom_ext Z hg⟩

/-- The norm of an arrow in a full subcategory equals the norm of its underlying arrow. -/
theorem fullSubcategory_norm_hom {Z : ObjectProperty C}
    {X Y : Z.FullSubcategory} (f : X ⟶ Y) : ‖f.hom‖ = ‖f‖ := (rfl)

/-- Constructing an arrow in a full subcategory preserves its norm. -/
@[simp] theorem fullSubcategory_norm_homMk {Z : ObjectProperty C}
    {X Y : Z.FullSubcategory} (f : X.obj ⟶ Y.obj) : ‖Z.homMk f‖ = ‖f‖ := (rfl)

end InducedCategory

end TauCeti
