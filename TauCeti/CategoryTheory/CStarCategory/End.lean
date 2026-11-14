/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import TauCeti.CategoryTheory.CStarCategory.Basic
public import TauCeti.CategoryTheory.Linear.Endomorphism

/-!
# Endomorphism C*-algebras, positivity, and subcategory inheritance

In a C*-category `C`, the endomorphism algebra `CategoryTheory.End X` of every object `X : C`
carries a canonical unital complex C*-algebra structure with operator-order multiplication
`(a * b).asHom = b.asHom ≫ a.asHom` and star `(star a).asHom = dagger a.asHom`. Equipping `End X`
with `CStarAlgebra.spectralOrder` makes it a `StarOrderedRing` in which every
`End.of (f ≫ dagger f)` and `End.of (dagger f ≫ f)` is positive, congruence
`a ↦ End.of (f ≫ a.asHom ≫ dagger f)` is order-preserving across arbitrary objects, and
operator-order Cauchy–Schwarz inequalities hold.

We also provide `TauCeti.CStarCategory.ofSpectrumNonneg`, showing that the algebraic positivity
field `exists_comp_dagger_eq` in `CStarCategory` is equivalent to spectral nonnegativity of
`End.of (f ≫ dagger f)`, and establish inheritance of `CStarCategory` along `InducedCategory` and
`ObjectProperty.FullSubcategory`.

## References

* P. Ghez, R. Lima, J. E. Roberts, *W\*-categories*, Pacific J. Math. 120 (1985), 79–109.
* P. D. Mitchener, *C\*-categories*, Proc. London Math. Soc. (3) 84 (2002), 375–404.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TauCeti

universe w v u

namespace CategoryTheory.End

section CStarAlgebra

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C] [CStarCategory C]
variable {X Y Z : C}

/-- The norm on `End X` induced by the Hom-space norm on `X ⟶ X`. -/
instance instNorm (X : C) : Norm (End X) where
  norm a := ‖a.asHom‖

/-- The norm of the underlying arrow of `a : End X` equals `‖a‖`. -/
@[simp] theorem norm_asHom (a : End X) : ‖a.asHom‖ = ‖a‖ := (rfl)

/-- Bundling `f : X ⟶ X` as `End.of f` preserves its norm. -/
@[simp] theorem norm_of (f : X ⟶ X) : ‖End.of f‖ = ‖f‖ := (rfl)

/-- The metric space on `End X` induced along `End.asHom`. -/
instance instMetricSpace (X : C) : MetricSpace (End X) :=
  MetricSpace.induced End.asHom (fun _ _ => End.ext) inferInstance

/-- Distance on underlying arrows agrees with distance in `End X`. -/
@[simp] theorem dist_asHom (a b : End X) : dist a.asHom b.asHom = dist a b := (rfl)

/-- Bundling endomorphism arrows preserves distance. -/
@[simp] theorem dist_of (f g : X ⟶ X) : dist (End.of f) (End.of g) = dist f g := (rfl)

/-- `End X` is a normed ring over its preadditive endomorphism ring. -/
instance instNormedRing (X : C) : NormedRing (End X) where
  dist_eq a b := CStarCategory.dist_eq a.asHom b.asHom
  norm_mul_le a b := CStarCategory.norm_comp_le b.asHom a.asHom

/-- `End X` is a complex normed algebra over its linear endomorphism algebra. -/
instance instNormedAlgebraComplex (X : C) : NormedAlgebra ℂ (End X) where
  norm_smul_le c a := CStarCategory.norm_smul_le c a.asHom

-- Verify that `NormedRing` and `NormedAlgebra ℂ` on `End X` reuse the existing ring and algebra.
example (X : C) : (inferInstance : NormedRing (End X)).toRing = (inferInstance : Ring (End X)) :=
  rfl

example (X : C) :
    (inferInstance : NormedAlgebra ℂ (End X)).toAlgebra = (inferInstance : Algebra ℂ (End X)) :=
  rfl

/-- `End.asHom` and `End.of` form a `ℂ`-linear isometric equivalence between `End X` and `X ⟶ X`. -/
def linearIsometryEquiv (X : C) : End X ≃ₗᵢ[ℂ] (X ⟶ X) where
  toFun := End.asHom
  invFun := End.of
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

/-- Forward evaluation of `End.linearIsometryEquiv`. -/
@[simp] theorem linearIsometryEquiv_apply (a : End X) :
    linearIsometryEquiv X a = a.asHom := (rfl)

/-- Inverse evaluation of `End.linearIsometryEquiv`. -/
@[simp] theorem linearIsometryEquiv_symm_apply (f : X ⟶ X) :
    (linearIsometryEquiv X).symm f = End.of f := (rfl)

/-- `End X` is complete in its norm metric. -/
instance instCompleteSpace (X : C) : CompleteSpace (End X) :=
  (linearIsometryEquiv X).toIsometryEquiv.completeSpace_iff.mpr inferInstance

/-- `End X` satisfies the C*-ring norm law via `CStarCategory.norm_comp_dagger_self`. -/
instance instCStarRing (X : C) : CStarRing (End X) where
  norm_mul_self_le a := by
    rw [← norm_asHom, ← norm_asHom (star a * a), mul_asHom, star_asHom,
      CStarCategory.norm_comp_dagger_self']

/-- The endomorphism algebra `End X` of any object in a C*-category is a unital C*-algebra. -/
instance instCStarAlgebra (X : C) : CStarAlgebra (End X) where

/-- The spectral partial order on the endomorphism C*-algebra `End X`. -/
instance instPartialOrder (X : C) : PartialOrder (End X) :=
  CStarAlgebra.spectralOrder (End X)

/-- With its spectral partial order, `End X` is a `StarOrderedRing`. -/
instance instStarOrderedRing (X : C) : StarOrderedRing (End X) :=
  CStarAlgebra.spectralOrderedRing (End X)

/-- Real scalar multiplication on `End X` acts on underlying arrows via coercion to `ℂ`. -/
@[simp] theorem real_smul_asHom (r : ℝ) (a : End X) :
    (r • a).asHom = (r : ℂ) • a.asHom := by
  rw [← Complex.coe_smul, smul_asHom]

/-! ### Zero-object vs nontrivial endomorphism C*-algebras -/

/-- In the endomorphism C*-algebra of a zero object, `‖(1 : End X)‖ = 0`. -/
theorem _root_.CategoryTheory.Limits.IsZero.norm_one_end (hX : IsZero X) :
    ‖(1 : End X)‖ = 0 :=
  hX.norm_id

/-- The unit of `End X` has norm `0` precisely when `X` is a zero object. -/
theorem norm_one_eq_zero_iff_isZero (X : C) :
    ‖(1 : End X)‖ = 0 ↔ IsZero X :=
  (CStarCategory.isZero_iff_norm_id_eq_zero X).symm

/-- An object is nonzero precisely when the unit of `End X` has norm `1`. -/
theorem norm_one_eq_one_iff_not_isZero (X : C) :
    ‖(1 : End X)‖ = 1 ↔ ¬ IsZero X :=
  (CStarCategory.not_isZero_iff_norm_id_eq_one X).symm

/-! ### Positivity, congruence, and Cauchy–Schwarz inequalities in `End X` -/

/-- Every `End.of (f ≫ dagger f)` is a positive element of `End X`. -/
theorem comp_dagger_self_nonneg (f : X ⟶ Y) : 0 ≤ End.of (f ≫ dagger f) := by
  obtain ⟨g, hg⟩ := CStarCategory.exists_comp_dagger_eq f
  rw [hg, of_comp, of_dagger]
  exact star_mul_self_nonneg (End.of g)

/-- Every `End.of (dagger f ≫ f)` is a positive element of `End Y`. -/
theorem dagger_comp_self_nonneg (f : X ⟶ Y) : 0 ≤ End.of (dagger f ≫ f) := by
  simpa only [dagger_dagger] using comp_dagger_self_nonneg (dagger f)

/-- An endomorphism `a : End X` is positive if and only if `a.asHom = g ≫ dagger g` for some
`g : X ⟶ X`. -/
theorem nonneg_iff_exists_comp_dagger_self {a : End X} :
    0 ≤ a ↔ ∃ g : X ⟶ X, a.asHom = g ≫ dagger g := by
  rw [CStarAlgebra.nonneg_iff_eq_star_mul_self]
  exact ⟨fun ⟨b, hb⟩ => ⟨b.asHom, by rw [hb, mul_asHom, star_asHom]⟩,
    fun ⟨g, hg⟩ => ⟨End.of g, End.ext hg⟩⟩

/-- Every real spectral value of `End.of (f ≫ dagger f)` is nonnegative. -/
theorem spectrum_comp_dagger_self_nonneg (f : X ⟶ Y) ⦃x : ℝ⦄
    (hx : x ∈ spectrum ℝ (End.of (f ≫ dagger f))) : 0 ≤ x :=
  spectrum_nonneg_of_nonneg (comp_dagger_self_nonneg f) hx

/-- Every complex spectral value of `End.of (f ≫ dagger f)` has nonnegative real part and zero
imaginary part. -/
theorem complexSpectrum_comp_dagger_self_nonneg (f : X ⟶ Y) ⦃z : ℂ⦄
    (hz : z ∈ spectrum ℂ (End.of (f ≫ dagger f))) : 0 ≤ z.re ∧ z.im = 0 := by
  open ComplexOrder in
  obtain ⟨hre, him⟩ :=
    Complex.nonneg_iff.mp (spectrum_nonneg_of_nonneg (comp_dagger_self_nonneg f) hz)
  exact ⟨hre, him.symm⟩

/-- Congruence `a ↦ End.of (f ≫ a.asHom ≫ dagger f)` sends positive elements of `End Y` to
positive elements of `End X` for any `f : X ⟶ Y`. -/
theorem comp_asHom_comp_dagger_nonneg (f : X ⟶ Y) {a : End Y} (ha : 0 ≤ a) :
    0 ≤ End.of (f ≫ a.asHom ≫ dagger f) := by
  obtain ⟨g, hg⟩ := nonneg_iff_exists_comp_dagger_self.mp ha
  have hfg : f ≫ a.asHom ≫ dagger f = (f ≫ g) ≫ dagger (f ≫ g) := by
    rw [hg, dagger_comp, Category.assoc, Category.assoc]
  rw [hfg]
  exact comp_dagger_self_nonneg (f ≫ g)

/-- Congruence `a ↦ End.of (f ≫ a.asHom ≫ dagger f)` is monotone from `End Y` to `End X`. -/
theorem comp_asHom_comp_dagger_mono (f : X ⟶ Y) {a b : End Y} (hab : a ≤ b) :
    End.of (f ≫ a.asHom ≫ dagger f) ≤ End.of (f ≫ b.asHom ≫ dagger f) := by
  rw [← sub_nonneg] at hab ⊢
  have hsub : End.of (f ≫ b.asHom ≫ dagger f) - End.of (f ≫ a.asHom ≫ dagger f) =
      End.of (f ≫ (b - a).asHom ≫ dagger f) := by
    ext
    simp [Preadditive.comp_sub, Preadditive.sub_comp]
  rw [hsub]
  exact comp_asHom_comp_dagger_nonneg f hab

/-- Dual congruence `a ↦ End.of (dagger g ≫ a.asHom ≫ g)` sends positive elements of `End X` to
positive elements of `End Y` for any `g : X ⟶ Y`. -/
theorem dagger_comp_asHom_comp_nonneg (g : X ⟶ Y) {a : End X} (ha : 0 ≤ a) :
    0 ≤ End.of (dagger g ≫ a.asHom ≫ g) := by
  simpa only [dagger_dagger] using comp_asHom_comp_dagger_nonneg (dagger g) ha

/-- Dual congruence `a ↦ End.of (dagger g ≫ a.asHom ≫ g)` is monotone from `End X` to `End Y`. -/
theorem dagger_comp_asHom_comp_mono (g : X ⟶ Y) {a b : End X} (hab : a ≤ b) :
    End.of (dagger g ≫ a.asHom ≫ g) ≤ End.of (dagger g ≫ b.asHom ≫ g) := by
  simpa only [dagger_dagger] using comp_asHom_comp_dagger_mono (dagger g) hab

/-- Categorical operator-order bound: `End.of ((f ≫ g) ≫ dagger (f ≫ g))` is bounded in `End X` by
`(‖g‖ ^ 2) • End.of (f ≫ dagger f)`. -/
theorem comp_dagger_self_comp_le (f : X ⟶ Y) (g : Y ⟶ Z) :
    End.of ((f ≫ g) ≫ dagger (f ≫ g)) ≤ (‖g‖ ^ 2) • End.of (f ≫ dagger f) := by
  have hle : End.of (g ≫ dagger g) ≤ algebraMap ℝ (End Y) ‖End.of (g ≫ dagger g)‖ :=
    IsSelfAdjoint.le_algebraMap_norm_self _
      (IsSelfAdjoint.of_nonneg (comp_dagger_self_nonneg g))
  rw [norm_of, CStarCategory.norm_comp_dagger_self] at hle
  have hcong := comp_asHom_comp_dagger_mono f hle
  have hlhs : End.of (f ≫ (End.of (g ≫ dagger g)).asHom ≫ dagger f) =
      End.of ((f ≫ g) ≫ dagger (f ≫ g)) := by
    ext
    simp [Category.assoc]
  have hrhs : End.of (f ≫ (algebraMap ℝ (End Y) (‖g‖ ^ 2)).asHom ≫ dagger f) =
      (‖g‖ ^ 2) • End.of (f ≫ dagger f) := by
    ext
    simp [Algebra.algebraMap_eq_smul_one]
  rwa [hlhs, hrhs] at hcong

/-- Dual operator-order bound: `End.of (dagger (f ≫ g) ≫ (f ≫ g))` is bounded in `End Z` by
`(‖f‖ ^ 2) • End.of (dagger g ≫ g)`. -/
theorem dagger_comp_self_comp_le (f : X ⟶ Y) (g : Y ⟶ Z) :
    End.of (dagger (f ≫ g) ≫ (f ≫ g)) ≤ (‖f‖ ^ 2) • End.of (dagger g ≫ g) := by
  simpa only [dagger_comp, dagger_dagger, CStarCategory.norm_dagger] using
    comp_dagger_self_comp_le (dagger g) (dagger f)

/-- Categorical Cauchy–Schwarz inequality in `End X` for two co-targeted morphisms `f : X ⟶ Y` and
`g : Z ⟶ Y`: `<f, g> <f, g>† ≤ ‖<g, g>‖ • <f, f>` where `<f, g> = f ≫ dagger g`. -/
theorem comp_dagger_comp_dagger_le_norm_smul (f : X ⟶ Y) (g : Z ⟶ Y) :
    End.of ((f ≫ dagger g) ≫ dagger (f ≫ dagger g)) ≤
      ‖g ≫ dagger g‖ • End.of (f ≫ dagger f) := by
  simpa only [CStarCategory.norm_dagger, CStarCategory.norm_comp_dagger_self] using
    comp_dagger_self_comp_le f (dagger g)

/-- Dual categorical Cauchy–Schwarz inequality in `End Z` for two co-sourced morphisms `f : Y ⟶ X`
and `g : Y ⟶ Z`. -/
theorem dagger_comp_dagger_comp_le_norm_smul (f : Y ⟶ X) (g : Y ⟶ Z) :
    End.of (dagger (dagger f ≫ g) ≫ (dagger f ≫ g)) ≤
      ‖dagger f ≫ f‖ • End.of (dagger g ≫ g) := by
  simpa only [CStarCategory.norm_dagger, CStarCategory.norm_dagger_comp_self] using
    dagger_comp_self_comp_le (dagger f) g

end CStarAlgebra

end CategoryTheory.End

namespace TauCeti.CStarCategory

/-- Construct a `CStarCategory` from spectral nonnegativity of `End.of (f ≫ dagger f)` over `ℂ`
instead of providing explicit square-root witnesses `exists_comp_dagger_eq`. -/
@[instance_reducible]
def ofSpectrumNonneg {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
    [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C]
    (homNorm : ∀ X Y : C, Norm (X ⟶ Y) := by infer_instance)
    (homMetricSpace : ∀ X Y : C, MetricSpace (X ⟶ Y) := by infer_instance)
    (dist_eq : ∀ {X Y : C} (f g : X ⟶ Y),
      @Dist.dist _ (homMetricSpace X Y).toDist f g =
        @Norm.norm _ (homNorm X Y) (-f + g) := by aesop)
    (homCompleteSpace : ∀ X Y : C, @CompleteSpace (X ⟶ Y)
      (homMetricSpace X Y).toUniformSpace := by infer_instance)
    (norm_smul_le : ∀ {X Y : C} (c : ℂ) (f : X ⟶ Y),
      @Norm.norm _ (homNorm X Y) (c • f) ≤ ‖c‖ * @Norm.norm _ (homNorm X Y) f := by
      intro X Y c f; exact NormedSpace.norm_smul_le c f)
    (norm_comp_le : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
      @Norm.norm _ (homNorm X Z) (f ≫ g) ≤
        @Norm.norm _ (homNorm Y Z) g * @Norm.norm _ (homNorm X Y) f)
    (norm_comp_dagger_self : ∀ {X Y : C} (f : X ⟶ Y),
      @Norm.norm _ (homNorm X X) (f ≫ dagger f) = @Norm.norm _ (homNorm X Y) f ^ 2)
    (spectrum_nonneg : ∀ {X Y : C} (f : X ⟶ Y) ⦃z : ℂ⦄,
      z ∈ spectrum ℂ (End.of (f ≫ dagger f)) → 0 ≤ z.re) :
    CStarCategory C where
  homNorm := homNorm
  homMetricSpace := homMetricSpace
  dist_eq := dist_eq
  homCompleteSpace := homCompleteSpace
  norm_smul_le := norm_smul_le
  norm_comp_le := norm_comp_le
  norm_comp_dagger_self := norm_comp_dagger_self
  exists_comp_dagger_eq {X Y} f := by
    let _ : Norm (X ⟶ X) := homNorm X X
    let _ : MetricSpace (X ⟶ X) := homMetricSpace X X
    have _ : CompleteSpace (X ⟶ X) := homCompleteSpace X X
    let _ : Norm (End X) := ⟨fun a => ‖a.asHom‖⟩
    let _ : MetricSpace (End X) :=
      MetricSpace.induced End.asHom (fun _ _ => End.ext) inferInstance
    let _ : NormedRing (End X) :=
      { dist_eq a b := dist_eq a.asHom b.asHom
        norm_mul_le a b := norm_comp_le b.asHom a.asHom }
    let _ : NormedAlgebra ℂ (End X) := ⟨fun c a => norm_smul_le c a.asHom⟩
    let e : End X ≃ᵢ (X ⟶ X) :=
      { toEquiv := ⟨End.asHom, End.of, fun _ => rfl, fun _ => rfl⟩
        isometry_toFun := Isometry.of_dist_eq fun _ _ => rfl }
    have _ : CompleteSpace (End X) := e.completeSpace_iff.mpr inferInstance
    have hnorm : ∀ b : End X, ‖b‖ = ‖b.asHom‖ := fun _ => rfl
    have _ : CStarRing (End X) := ⟨fun a => by
      rw [hnorm a, hnorm (star a * a), End.mul_asHom, End.star_asHom, norm_comp_dagger_self, sq]⟩
    let _ : CStarAlgebra (End X) := {}
    let _ : PartialOrder (End X) := CStarAlgebra.spectralOrder (End X)
    have _ : StarOrderedRing (End X) := CStarAlgebra.spectralOrderedRing (End X)
    have hsa : IsSelfAdjoint (End.of (f ≫ dagger f)) := by
      rw [isSelfAdjoint_iff]
      ext
      simp
    have hpos : 0 ≤ End.of (f ≫ dagger f) := by
      rw [StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ hsa]
      intro x hx
      simpa using spectrum_nonneg f (spectrum.algebraMap_mem ℂ hx)
    obtain ⟨b, hb⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hpos
    exact ⟨b.asHom, congrArg End.asHom hb⟩

end TauCeti.CStarCategory

namespace CategoryTheory.InducedCategory

open TauCeti

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C] [CStarCategory C]
variable {D : Type w}

/-- A category induced along a map on objects inherits the ambient C*-category structure. -/
instance instCStarCategory (F : D → C) : CStarCategory (InducedCategory C F) where
  homNorm _ _ := ⟨fun f => ‖f.hom‖⟩
  homMetricSpace _ _ :=
    MetricSpace.induced InducedCategory.Hom.hom (fun _ _ => InducedCategory.hom_ext) inferInstance
  dist_eq f g := CStarCategory.dist_eq f.hom g.hom
  homCompleteSpace X Y := by
    let _ : MetricSpace (X ⟶ Y) :=
      MetricSpace.induced InducedCategory.Hom.hom (fun _ _ => InducedCategory.hom_ext) inferInstance
    let e : (X ⟶ Y) ≃ᵢ (F X ⟶ F Y) :=
      { toEquiv := homEquiv
        isometry_toFun := Isometry.of_dist_eq fun _ _ => rfl }
    exact e.completeSpace_iff.mpr inferInstance
  norm_smul_le c f := CStarCategory.norm_smul_le c f.hom
  norm_comp_le f g := CStarCategory.norm_comp_le f.hom g.hom
  norm_comp_dagger_self f := CStarCategory.norm_comp_dagger_self f.hom
  exists_comp_dagger_eq f := by
    obtain ⟨g, hg⟩ := CStarCategory.exists_comp_dagger_eq f.hom
    exact ⟨homMk g, hom_ext hg⟩

/-- The norm of the underlying arrow in an induced category equals the arrow's norm. -/
@[simp] theorem norm_hom {F : D → C} {X Y : InducedCategory C F} (f : X ⟶ Y) :
    ‖f.hom‖ = ‖f‖ := by rfl

/-- Bundling an arrow in an induced category preserves its norm. -/
@[simp] theorem norm_homMk {F : D → C} {X Y : InducedCategory C F} (f : F X ⟶ F Y) :
    ‖homMk (F := F) f‖ = ‖f‖ := by rfl

end CategoryTheory.InducedCategory

namespace CategoryTheory.ObjectProperty

open TauCeti

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C] [CStarCategory C]

/-- Any full subcategory of a C*-category inherits a C*-category structure. -/
instance instCStarCategoryFullSubcategory (P : ObjectProperty C) :
    CStarCategory P.FullSubcategory :=
  InducedCategory.instCStarCategory FullSubcategory.obj

/-- The norm of the underlying arrow in a full subcategory equals the arrow's norm. -/
theorem norm_hom {P : ObjectProperty C} {X Y : P.FullSubcategory} (f : X ⟶ Y) :
    ‖f.hom‖ = ‖f‖ := by rfl

/-- Bundling an arrow in a full subcategory preserves its norm. -/
@[simp] theorem norm_homMk {P : ObjectProperty C} {X Y : P.FullSubcategory}
    (f : X.obj ⟶ Y.obj) :
    ‖(homMk f : X ⟶ Y)‖ = ‖f‖ := by rfl

end CategoryTheory.ObjectProperty
