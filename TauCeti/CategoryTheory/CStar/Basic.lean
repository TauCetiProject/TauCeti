/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import TauCeti.Analysis.CStarAlgebra.Module.Basic
public import TauCeti.CategoryTheory.Dagger.Basic

/-!
# Complex C⋆-categories

A complex C⋆-category is a `ℂ`-linear dagger category whose Hom spaces are complex Banach spaces
such that composition is contractive (`‖f ≫ g‖ ≤ ‖g‖ * ‖f‖`), the C⋆-identity
`‖f ≫ dagger f‖ = ‖f‖ ^ 2` holds on every Hom space, and every composite `f ≫ dagger f` is a
positive element of the endomorphism algebra `CategoryTheory.End X` (formulated algebraically via a
square-root factorization `f ≫ dagger f = h ≫ dagger h`, which is equivalent to spectral
nonnegativity in `End X`).

From these laws:
* taking daggers is automatically a conjugate-linear isometric equivalence between opposite Hom
  spaces, and `‖dagger f ≫ f‖ = ‖f‖ ^ 2`;
* each endomorphism ring `CategoryTheory.End X`, with Mathlib's operator-order multiplication
  `(a * b).asHom = b.asHom ≫ a.asHom`, inherits a compatible unital complex `CStarAlgebra`
  structure together with its spectral `PartialOrder` and `StarOrderedRing` instances, in which
  `End.of (f ≫ dagger f)` and `End.of (dagger f ≫ f)` are nonnegative;
* the Banach norms and metrics of a `CStarCategory` are uniquely determined by the underlying
  `ℂ`-linear dagger category (`Subsingleton (CStarCategory C)`);
* identity arrows have norm `0` on zero objects and norm `1` on nonzero objects, dagger-isometries
  and unitaries act isometrically on Hom spaces, and nonzero self-adjoint idempotents have norm `1`;
* every Hom space `X ⟶ Y` is both a right Hilbert `End X`-module (`CStarModule (End X)ᵐᵒᵖ (X ⟶ Y)`)
  and a left Hilbert `End Y`-module (`CStarModule (End Y) (X ⟶ Y)`), yielding the operator-valued
  Cauchy–Schwarz inequalities and polarization identities on `X ⟶ Y`;
* pre-composition, post-composition, and bilinear composition bundle as continuous linear maps with
  sharp norm bounds and closed (hence Banach) kernels and idempotent corner subspaces.

## Main declarations

* `TauCeti.CStarCategory`: complex C⋆-category structure on a `ℂ`-linear dagger category.
* `TauCeti.CStarCategory.ofSpectrumNonneg`: constructor from spectral nonnegativity of
  `End.of (f ≫ dagger f)`.
* `CategoryTheory.End.instCStarAlgebra`: unital `CStarAlgebra` structure on `End X`.
* `TauCeti.comp_dagger_self_nonneg`, `TauCeti.dagger_comp_self_nonneg`: positivity of
  `f ≫ dagger f` in `End X` and `dagger f ≫ f` in `End Y`.
* `TauCeti.homRightCStarModule`, `TauCeti.homLeftCStarModule`: Hilbert C⋆-module structures on
  `X ⟶ Y` over `(End X)ᵐᵒᵖ` and `End Y`.
* `TauCeti.comp_dagger_mul_comp_dagger_le`, `TauCeti.comp_dagger_polarization`: operator-valued
  Cauchy–Schwarz and polarization identities on Hom spaces.
* `TauCeti.leftCompCLM`, `TauCeti.rightCompCLM`, `TauCeti.compCLM`: continuous linear composition
  maps and closedness of their kernels.

## References

* P. Ghez, R. Lima, and J. E. Roberts, *W⋆-categories*, Pacific J. Math. **120** (1985), 79–109,
  Section 1.
* R. Longo and J. E. Roberts, *A theory of dimension*, K-Theory **11** (1997), 103–159, Section 2.
-/

public section

noncomputable section

open CategoryTheory Complex MulOpposite
open scoped NNReal

universe v u

namespace TauCeti

/-- A complex C⋆-category is a `ℂ`-linear dagger category equipped with Banach-space structures on
its Hom spaces (compatible with the additive group from `Preadditive` and the `ℂ`-action from
`Linear ℂ`), contractive composition, the C⋆-identity `‖f ≫ dagger f‖ = ‖f‖ ^ 2`, and positivity
of `f ≫ dagger f` in `End X` (expressed as `f ≫ dagger f = h ≫ dagger h` for some `h : X ⟶ X`). -/
class CStarCategory (C : Type u) [Category.{v} C] [Preadditive C] [Linear ℂ C]
    [DaggerCategory C] extends DaggerPreadditive C, DaggerLinear ℂ C where
  /-- The norm on each Hom space. -/
  homNorm : ∀ X Y : C, Norm (X ⟶ Y) := by infer_instance
  /-- The metric structure on each Hom space. -/
  homMetricSpace : ∀ X Y : C, MetricSpace (X ⟶ Y) := by infer_instance
  /-- Distance on each Hom space is induced by the norm and `Preadditive` subtraction. -/
  hom_dist_eq : ∀ (X Y : C) (f g : X ⟶ Y), dist f g = ‖-f + g‖ := by
    intros; exact dist_eq_norm_neg_add _ _
  /-- Scalar multiplication on each Hom space is bounded by the product of norms. -/
  hom_norm_smul_le : ∀ (X Y : C) (c : ℂ) (f : X ⟶ Y), ‖c • f‖ ≤ ‖c‖ * ‖f‖ := by
    intros; exact norm_smul_le _ _
  /-- Every Hom space is complete with respect to its metric. -/
  homCompleteSpace : ∀ X Y : C, CompleteSpace (X ⟶ Y) := by infer_instance
  /-- Categorical composition is contractive in operator order. -/
  norm_comp_le : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), ‖f ≫ g‖ ≤ ‖g‖ * ‖f‖
  /-- The C⋆-norm identity in categorical composition order. -/
  norm_comp_dagger_self : ∀ {X Y : C} (f : X ⟶ Y), ‖f ≫ dagger f‖ = ‖f‖ ^ 2
  /-- Every `f ≫ dagger f` factors as `h ≫ dagger h` for an endomorphism `h : X ⟶ X`, making
  `End.of (f ≫ dagger f)` positive in the C⋆-algebra `End X`. -/
  exists_comp_dagger_eq : ∀ {X Y : C} (f : X ⟶ Y), ∃ h : X ⟶ X, f ≫ dagger f = h ≫ dagger h

namespace CStarCategory

section Instances

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [DaggerCategory C]
  [CStarCategory C]

/-- Each Hom space of a C⋆-category is a normed additive commutative group whose underlying
additive group is definitionally `Preadditive.homGroup`. -/
instance homNormedAddCommGroup (X Y : C) : NormedAddCommGroup (X ⟶ Y) where
  toAddCommGroup := Preadditive.homGroup X Y
  toNorm := CStarCategory.homNorm X Y
  toMetricSpace := CStarCategory.homMetricSpace X Y
  dist_eq := CStarCategory.hom_dist_eq X Y

/-- Each Hom space of a C⋆-category is a complex normed space whose underlying `ℂ`-module is
definitionally `Linear.homModule`. -/
instance homNormedSpace (X Y : C) : NormedSpace ℂ (X ⟶ Y) where
  toModule := Linear.homModule X Y
  norm_smul_le := CStarCategory.hom_norm_smul_le X Y

/-- Each Hom space of a C⋆-category is a Banach space. -/
instance instCompleteSpaceHom (X Y : C) : CompleteSpace (X ⟶ Y) :=
  CStarCategory.homCompleteSpace X Y

end Instances

end CStarCategory

export CStarCategory (norm_comp_le norm_comp_dagger_self exists_comp_dagger_eq)

attribute [simp] norm_comp_dagger_self

section Elementary

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [DaggerCategory C]
  [CStarCategory C] {W X Y Z : C}

/-- Categorical composition is submultiplicative with factors in diagram order. -/
theorem norm_comp_le' (f : X ⟶ Y) (g : Y ⟶ Z) : ‖f ≫ g‖ ≤ ‖f‖ * ‖g‖ :=
  mul_comm ‖g‖ ‖f‖ ▸ norm_comp_le f g

private theorem norm_le_norm_dagger (f : X ⟶ Y) : ‖f‖ ≤ ‖dagger f‖ := by
  rcases eq_or_lt_of_le (norm_nonneg f) with hf | hf
  · rw [← hf]
    exact norm_nonneg _
  · have hsq : ‖f‖ * ‖f‖ ≤ ‖dagger f‖ * ‖f‖ := by
      simpa only [sq] using (norm_comp_dagger_self f).symm.trans_le (norm_comp_le f (dagger f))
    exact le_of_mul_le_mul_right hsq hf

/-- Taking the dagger is norm-preserving on every Hom space. -/
@[simp] theorem norm_dagger (f : X ⟶ Y) : ‖dagger f‖ = ‖f‖ :=
  le_antisymm (by simpa only [dagger_dagger] using norm_le_norm_dagger (dagger f))
    (norm_le_norm_dagger f)

/-- Taking the dagger preserves the `ℝ≥0`-valued norm. -/
@[simp] theorem nnNorm_dagger (f : X ⟶ Y) : ‖dagger f‖₊ = ‖f‖₊ :=
  Subtype.ext (norm_dagger f)

/-- Taking the dagger preserves distances between morphisms. -/
@[simp] theorem dist_dagger (f g : X ⟶ Y) : dist (dagger f) (dagger g) = dist f g := by
  rw [dist_eq_norm, dist_eq_norm, ← dagger_sub, norm_dagger]

/-- The dagger map between opposite Hom spaces is an isometry. -/
theorem dagger_isometry (X Y : C) : Isometry (dagger : (X ⟶ Y) → (Y ⟶ X)) :=
  Isometry.of_dist_eq dist_dagger

/-- The dagger bundled as a conjugate-linear isometric equivalence `(X ⟶ Y) ≃ₗᵢ⋆[ℂ] (Y ⟶ X)`. -/
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

/-- The inverse of `daggerLinearIsometryEquiv` reverses endpoints. -/
@[simp] theorem daggerLinearIsometryEquiv_symm (X Y : C) :
    (daggerLinearIsometryEquiv X Y).symm = daggerLinearIsometryEquiv Y X := (rfl)

/-- The dagger bundled as a conjugate-linear continuous linear equivalence. -/
def daggerContinuousLinearEquiv (X Y : C) : (X ⟶ Y) ≃L⋆[ℂ] (Y ⟶ X) :=
  (daggerLinearIsometryEquiv X Y).toContinuousLinearEquiv

/-- Evaluation of `daggerContinuousLinearEquiv`. -/
@[simp] theorem daggerContinuousLinearEquiv_apply (f : X ⟶ Y) :
    daggerContinuousLinearEquiv X Y f = dagger f := (rfl)

/-- The inverse of `daggerContinuousLinearEquiv` reverses endpoints. -/
@[simp] theorem daggerContinuousLinearEquiv_symm (X Y : C) :
    (daggerContinuousLinearEquiv X Y).symm = daggerContinuousLinearEquiv Y X := (rfl)

/-- The C⋆-norm identity with the dagger on the left. -/
@[simp] theorem norm_dagger_comp_self (f : X ⟶ Y) : ‖dagger f ≫ f‖ = ‖f‖ ^ 2 := by
  simpa only [dagger_dagger, norm_dagger] using norm_comp_dagger_self (dagger f)

/-- Recovering the norm of `f` as the square root of `‖f ≫ dagger f‖`. -/
theorem sqrt_norm_comp_dagger_self (f : X ⟶ Y) : √‖f ≫ dagger f‖ = ‖f‖ := by
  rw [norm_comp_dagger_self, Real.sqrt_sq (norm_nonneg f)]

/-- Recovering the norm of `f` as the square root of `‖dagger f ≫ f‖`. -/
theorem sqrt_norm_dagger_comp_self (f : X ⟶ Y) : √‖dagger f ≫ f‖ = ‖f‖ := by
  rw [norm_dagger_comp_self, Real.sqrt_sq (norm_nonneg f)]

/-- `f ≫ dagger f` vanishes precisely when `f` vanishes. -/
@[simp] theorem comp_dagger_self_eq_zero_iff (f : X ⟶ Y) : f ≫ dagger f = 0 ↔ f = 0 := by
  rw [← norm_eq_zero, norm_comp_dagger_self, sq_eq_zero_iff, norm_eq_zero]

/-- `dagger f ≫ f` vanishes precisely when `f` vanishes. -/
@[simp] theorem dagger_comp_self_eq_zero_iff (f : X ⟶ Y) : dagger f ≫ f = 0 ↔ f = 0 := by
  rw [← norm_eq_zero, norm_dagger_comp_self, sq_eq_zero_iff, norm_eq_zero]

end Elementary

end TauCeti

/-! ### C⋆-algebra structure on endomorphism rings -/

namespace CategoryTheory.End

open TauCeti

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [DaggerCategory C]
  [CStarCategory C] {X : C}

/-- Endomorphisms of an object in a C⋆-category form a normed ring under operator-order
multiplication `(f * g).asHom = g.asHom ≫ f.asHom`. -/
instance instNormedRing : NormedRing (End X) where
  norm f := ‖f.asHom‖
  toMetricSpace := MetricSpace.induced End.asHom End.homEquiv.injective inferInstance
  dist_eq f g := dist_eq_norm_neg_add f.asHom g.asHom
  norm_mul_le f g := norm_comp_le g.asHom f.asHom

/-- Bundling an endomorphism preserves its norm. -/
@[simp] theorem norm_of (f : X ⟶ X) : ‖End.of f‖ = ‖f‖ := (rfl)

/-- Unbundling an endomorphism preserves its norm. -/
@[simp] theorem norm_asHom (f : End X) : ‖f.asHom‖ = ‖f‖ := (rfl)

/-- Bundling an endomorphism preserves its `ℝ≥0`-valued norm. -/
@[simp] theorem nnNorm_of (f : X ⟶ X) : ‖End.of f‖₊ = ‖f‖₊ := (rfl)

/-- Unbundling an endomorphism preserves its `ℝ≥0`-valued norm. -/
@[simp] theorem nnNorm_asHom (f : End X) : ‖f.asHom‖₊ = ‖f‖₊ := (rfl)

/-- Bundling endomorphisms preserves distances. -/
@[simp] theorem dist_of (f g : X ⟶ X) : dist (End.of f) (End.of g) = dist f g := (rfl)

/-- Unbundling endomorphisms preserves distances. -/
@[simp] theorem dist_asHom (f g : End X) : dist f.asHom g.asHom = dist f g := (rfl)

/-- Endomorphisms of an object in a C⋆-category form a normed `ℂ`-algebra. -/
instance instNormedAlgebra : NormedAlgebra ℂ (End X) where
  norm_smul_le r f := norm_smul_le r f.asHom

/-- The canonical `ℂ`-linear isometric equivalence `End X ≃ₗᵢ[ℂ] (X ⟶ X)`. -/
def homLinearIsometryEquiv (X : C) : End X ≃ₗᵢ[ℂ] (X ⟶ X) where
  toLinearEquiv := End.linearEquiv
  norm_map' _ := (rfl)

/-- Evaluation of `End.homLinearIsometryEquiv`. -/
@[simp] theorem homLinearIsometryEquiv_apply (f : End X) :
    homLinearIsometryEquiv X f = f.asHom := (rfl)

/-- Inverse evaluation of `End.homLinearIsometryEquiv`. -/
@[simp] theorem homLinearIsometryEquiv_symm_apply (f : X ⟶ X) :
    (homLinearIsometryEquiv X).symm f = End.of f := (rfl)

instance instCompleteSpace : CompleteSpace (End X) :=
  (homLinearIsometryEquiv X).toIsometryEquiv.completeSpace_iff.2 inferInstance

instance instCStarRing : CStarRing (End X) where
  norm_mul_self_le f := by
    rw [← sq, ← norm_asHom, ← norm_comp_dagger_self]
    exact le_rfl

/-- Every endomorphism algebra `End X` in a complex C⋆-category is a unital complex C⋆-algebra. -/
noncomputable instance instCStarAlgebra : CStarAlgebra (End X) where

/-- Every endomorphism C⋆-algebra `End X` carries its canonical spectral partial order. -/
noncomputable instance instPartialOrder : PartialOrder (End X) :=
  CStarAlgebra.spectralOrder (End X)

/-- With the spectral partial order, `End X` is a `StarOrderedRing`. -/
instance instStarOrderedRing : StarOrderedRing (End X) :=
  CStarAlgebra.spectralOrderedRing (End X)

end CategoryTheory.End

namespace TauCeti

section PositivityAndUniqueness

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [DaggerCategory C]

section WithCStar

variable [CStarCategory C] {W X Y Z : C}

omit [Preadditive C] [Linear ℂ C] [CStarCategory C] in
/-- An endomorphism is self-adjoint in `End X` precisely when it is fixed by `dagger`. -/
@[simp] theorem isSelfAdjoint_end_of_iff (h : X ⟶ X) :
    IsSelfAdjoint (End.of h) ↔ dagger h = h := by
  rw [IsSelfAdjoint, End.ext_iff]
  rfl

omit [Preadditive C] [Linear ℂ C] [CStarCategory C] in
/-- `End.of (f ≫ dagger f)` is self-adjoint in `End X`. -/
theorem isSelfAdjoint_comp_dagger_self (f : X ⟶ Y) :
    IsSelfAdjoint (End.of (f ≫ dagger f)) := by
  simp

omit [Preadditive C] [Linear ℂ C] [CStarCategory C] in
/-- `End.of (dagger f ≫ f)` is self-adjoint in `End Y`. -/
theorem isSelfAdjoint_dagger_comp_self (f : X ⟶ Y) :
    IsSelfAdjoint (End.of (dagger f ≫ f)) := by
  simp

/-- Positivity of `f† f`: for any `f : X ⟶ Y`, `End.of (f ≫ dagger f)` is nonnegative in the
C⋆-algebra `End X`. -/
theorem comp_dagger_self_nonneg (f : X ⟶ Y) : (0 : End X) ≤ End.of (f ≫ dagger f) := by
  obtain ⟨h, hh⟩ := exists_comp_dagger_eq f
  have hfac : End.of (f ≫ dagger f) = star (End.of h) * End.of h := by
    ext
    simpa using hh
  rw [hfac]
  exact star_mul_self_nonneg (End.of h)

/-- Positivity of `f f†`: for any `f : X ⟶ Y`, `End.of (dagger f ≫ f)` is nonnegative in the
C⋆-algebra `End Y`. -/
theorem dagger_comp_self_nonneg (f : X ⟶ Y) : (0 : End Y) ≤ End.of (dagger f ≫ f) := by
  simpa only [dagger_dagger] using comp_dagger_self_nonneg (dagger f)

/-- The spectrum of `End.of (f ≫ dagger f)` in `End X` restricts to `ℝ≥0`. -/
theorem spectrumRestricts_comp_dagger_self (f : X ⟶ Y) :
    SpectrumRestricts (End.of (f ≫ dagger f)) ContinuousMap.realToNNReal :=
  SpectrumRestricts.nnreal_of_nonneg (comp_dagger_self_nonneg f)

/-- Every real spectral value of `End.of (f ≫ dagger f)` is nonnegative. -/
theorem spectrum_comp_dagger_self_nonneg (f : X ⟶ Y) {r : ℝ}
    (hr : r ∈ spectrum ℝ (End.of (f ≫ dagger f))) : 0 ≤ r :=
  SpectrumRestricts.nnreal_iff.mp (spectrumRestricts_comp_dagger_self f) r hr

/-- Every `f ≫ dagger f` admits a positive self-adjoint square root `h : X ⟶ X` satisfying
`dagger h = h`, `0 ≤ End.of h`, and `h ≫ h = f ≫ dagger f`. -/
theorem exists_isSelfAdjoint_comp_self_eq_comp_dagger_self (f : X ⟶ Y) :
    ∃ h : X ⟶ X, dagger h = h ∧ (0 : End X) ≤ End.of h ∧ h ≫ h = f ≫ dagger f := by
  let s : End X := CFC.sqrt (End.of (f ≫ dagger f))
  have hs0 : 0 ≤ s := CFC.sqrt_nonneg _
  have hsa : dagger s.asHom = s.asHom := congrArg End.asHom hs0.isSelfAdjoint.star_eq
  have hsq : s * s = End.of (f ≫ dagger f) :=
    CFC.sqrt_mul_sqrt_self _ (comp_dagger_self_nonneg f)
  exact ⟨s.asHom, hsa, by simpa using hs0, congrArg End.asHom hsq⟩

end WithCStar

/-- Two `CStarCategory` structures on the same `ℂ`-linear dagger category coincide as soon as
their Hom-space norms agree. -/
@[ext]
theorem CStarCategory.ext {I₁ I₂ : CStarCategory C}
    (h : ∀ (X Y : C) (f : X ⟶ Y),
      @Norm.norm _ (I₁.homNorm X Y) f = @Norm.norm _ (I₂.homNorm X Y) f) :
    I₁ = I₂ := by
  cases I₁ with
  | mk hn₁ hm₁ hd₁ hs₁ hc₁ hcomp₁ hcstar₁ hpos₁ =>
    cases I₂ with
    | mk hn₂ hm₂ hd₂ hs₂ hc₂ hcomp₂ hcstar₂ hpos₂ =>
      have hnorm : hn₁ = hn₂ := funext₂ fun X Y => congrArg Norm.mk (funext (h X Y))
      subst hnorm
      have hmet : hm₁ = hm₂ := by
        funext X Y
        refine MetricSpace.ext ?_
        ext f g
        exact (hd₁ X Y f g).trans (hd₂ X Y f g).symm
      subst hmet
      rfl

private structure PreEnd (X : C) (nX : Norm (X ⟶ X)) where
  of ::
  val : End X

private def preEndEquiv {X : C} {nX : Norm (X ⟶ X)} : PreEnd X nX ≃ End X where
  toFun := PreEnd.val
  invFun := PreEnd.of
  left_inv _ := rfl
  right_inv _ := rfl

private instance {X : C} {nX : Norm (X ⟶ X)} : Ring (PreEnd X nX) :=
  preEndEquiv.ring

private instance [DaggerPreadditive C] {X : C} {nX : Norm (X ⟶ X)} : StarRing (PreEnd X nX) where
  star x := ⟨star x.val⟩
  star_involutive x := congrArg PreEnd.of (star_involutive x.val)
  star_mul x y := congrArg PreEnd.of (star_mul x.val y.val)
  star_add x y := congrArg PreEnd.of (star_add x.val y.val)

private instance {X : C} {nX : Norm (X ⟶ X)} : Algebra ℂ (PreEnd X nX) :=
  preEndEquiv.algebra ℂ

private instance [DaggerPreadditive C] [DaggerLinear ℂ C] {X : C} {nX : Norm (X ⟶ X)} :
    StarModule ℂ (PreEnd X nX) where
  star_smul c x := congrArg PreEnd.of (star_smul c x.val)

@[instance_reducible]
private noncomputable def mkPreEndCStarAlgebra [DaggerPreadditive C] [DaggerLinear ℂ C]
    (X : C) (nX : Norm (X ⟶ X)) (mX : MetricSpace (X ⟶ X))
    (hdX : ∀ f g : X ⟶ X, @Dist.dist _ mX.toDist f g = @Norm.norm _ nX (-f + g))
    (hsX : ∀ (c : ℂ) (f : X ⟶ X), @Norm.norm _ nX (c • f) ≤ ‖c‖ * @Norm.norm _ nX f)
    (hcX : @CompleteSpace (X ⟶ X) mX.toUniformSpace)
    (hcomp : ∀ f g : X ⟶ X, @Norm.norm _ nX (f ≫ g) ≤ @Norm.norm _ nX g * @Norm.norm _ nX f)
    (hcstar : ∀ f : X ⟶ X, @Norm.norm _ nX (f ≫ dagger f) = @Norm.norm _ nX f ^ 2) :
    CStarAlgebra (PreEnd X nX) :=
  letI : NormedAddCommGroup (X ⟶ X) :=
    { toAddCommGroup := Preadditive.homGroup X X
      toNorm := nX
      toMetricSpace := mX
      dist_eq := hdX }
  letI : NormedSpace ℂ (X ⟶ X) :=
    { toModule := Linear.homModule X X
      norm_smul_le := hsX }
  letI : CompleteSpace (X ⟶ X) := hcX
  letI : NormedRing (PreEnd X nX) :=
    { norm x := ‖x.val.asHom‖
      toMetricSpace := MetricSpace.induced (fun x : PreEnd X nX => x.val.asHom)
        (End.homEquiv.injective.comp preEndEquiv.injective) inferInstance
      dist_eq x y := dist_eq_norm_neg_add x.val.asHom y.val.asHom
      norm_mul_le x y := hcomp y.val.asHom x.val.asHom }
  letI : NormedAlgebra ℂ (PreEnd X nX) :=
    { norm_smul_le c x := norm_smul_le c x.val.asHom }
  let eIso : PreEnd X nX ≃ᵢ (X ⟶ X) :=
    { toEquiv := preEndEquiv.trans End.homEquiv
      isometry_toFun := fun _ _ => rfl }
  letI : CompleteSpace (PreEnd X nX) := eIso.completeSpace_iff.2 hcX
  letI : CStarRing (PreEnd X nX) :=
    { norm_mul_self_le x := by
        have h := hcstar x.val.asHom
        rw [sq] at h
        exact h.symm.le }
  {}

/-- The Banach norms and metrics of a complex `CStarCategory` are uniquely determined by its
underlying `ℂ`-linear dagger category structure. -/
instance CStarCategory.instSubsingleton : Subsingleton (CStarCategory C) where
  allEq I₁ I₂ := by
    refine CStarCategory.ext fun X Y f => ?_
    have h₁ := @sqrt_norm_comp_dagger_self C _ _ _ _ I₁ X Y f
    have h₂ := @sqrt_norm_comp_dagger_self C _ _ _ _ I₂ X Y f
    rw [← h₁, ← h₂]
    congr 1
    have : DaggerPreadditive C := I₁.toDaggerPreadditive
    have : DaggerLinear ℂ C := I₁.toDaggerLinear
    let : CStarAlgebra (PreEnd X (I₁.homNorm X X)) :=
      mkPreEndCStarAlgebra X (I₁.homNorm X X) (I₁.homMetricSpace X X) (I₁.hom_dist_eq X X)
        (I₁.hom_norm_smul_le X X) (I₁.homCompleteSpace X X) I₁.norm_comp_le
        I₁.norm_comp_dagger_self
    let : CStarAlgebra (PreEnd X (I₂.homNorm X X)) :=
      mkPreEndCStarAlgebra X (I₂.homNorm X X) (I₂.homMetricSpace X X) (I₂.hom_dist_eq X X)
        (I₂.hom_norm_smul_le X X) (I₂.homCompleteSpace X X) I₂.norm_comp_le
        I₂.norm_comp_dagger_self
    let φ : PreEnd X (I₂.homNorm X X) ≃⋆ₐ[ℂ] PreEnd X (I₁.homNorm X X) :=
      { (preEndEquiv.trans preEndEquiv.symm).ringEquiv with
        map_smul' _ _ := rfl
        map_star' _ := rfl }
    exact StarAlgEquiv.norm_map φ ⟨End.of (f ≫ dagger f)⟩

/-- Construct a `CStarCategory` by verifying that every `End.of (f ≫ dagger f)` has complex
spectrum contained in the nonnegative real axis `{z : ℂ | 0 ≤ z.re ∧ z.im = 0}` (using only the
algebraic `Algebra ℂ (End X)` structure in the hypothesis). -/
@[instance_reducible]
def CStarCategory.ofSpectrumNonneg [DaggerPreadditive C] [DaggerLinear ℂ C]
    [homNorm : ∀ X Y : C, Norm (X ⟶ Y)]
    [homMetricSpace : ∀ X Y : C, MetricSpace (X ⟶ Y)]
    (hom_dist_eq : ∀ (X Y : C) (f g : X ⟶ Y), dist f g = ‖-f + g‖ := by
      intros; exact dist_eq_norm_neg_add _ _)
    (hom_norm_smul_le : ∀ (X Y : C) (c : ℂ) (f : X ⟶ Y), ‖c • f‖ ≤ ‖c‖ * ‖f‖ := by
      intros; exact norm_smul_le _ _)
    [homCompleteSpace : ∀ X Y : C, CompleteSpace (X ⟶ Y)]
    (norm_comp_le : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), ‖f ≫ g‖ ≤ ‖g‖ * ‖f‖)
    (norm_comp_dagger_self : ∀ {X Y : C} (f : X ⟶ Y), ‖f ≫ dagger f‖ = ‖f‖ ^ 2)
    (spectrum_nonneg : ∀ {X Y : C} (f : X ⟶ Y) {z : ℂ},
      z ∈ spectrum ℂ (End.of (f ≫ dagger f)) → 0 ≤ z.re ∧ z.im = 0) :
    CStarCategory C where
  homNorm := homNorm
  homMetricSpace := homMetricSpace
  hom_dist_eq := hom_dist_eq
  hom_norm_smul_le := hom_norm_smul_le
  homCompleteSpace := homCompleteSpace
  norm_comp_le := norm_comp_le
  norm_comp_dagger_self := norm_comp_dagger_self
  exists_comp_dagger_eq {X Y} f := by
    let : CStarAlgebra (PreEnd X (homNorm X X)) :=
      mkPreEndCStarAlgebra X (homNorm X X) (homMetricSpace X X) (hom_dist_eq X X)
        (hom_norm_smul_le X X) (homCompleteSpace X X) norm_comp_le norm_comp_dagger_self
    let a : PreEnd X (homNorm X X) := ⟨End.of (f ≫ dagger f)⟩
    have hsa : IsSelfAdjoint a := congrArg PreEnd.of (End.ext (by simp [a]))
    let ψ : PreEnd X (homNorm X X) ≃ₐ[ℂ] End X :=
      { preEndEquiv.ringEquiv with commutes' _ := rfl }
    have hsr : SpectrumRestricts a ContinuousMap.realToNNReal := by
      rw [SpectrumRestricts.nnreal_iff]
      intro r hr
      have hc : (r : ℂ) ∈ spectrum ℂ a := spectrum.algebraMap_mem ℂ hr
      have hc' : (r : ℂ) ∈ spectrum ℂ (End.of (f ≫ dagger f)) := by
        rwa [← AlgEquiv.spectrum_eq ψ a] at hc
      simpa using (spectrum_nonneg f hc').1
    obtain ⟨s, hs₁, _, hs₂⟩ :=
      CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts hsa hsr
    refine ⟨s.val.asHom, ?_⟩
    have hstar : star s.val = s.val := congrArg PreEnd.val hs₁.star_eq
    have hmul : End.of (f ≫ dagger f) = star s.val * s.val := by
      rw [hstar]
      exact congrArg PreEnd.val hs₂.symm
    exact congrArg End.asHom hmul

end PositivityAndUniqueness

/-! ### Identities, zero-object dichotomy, unitaries, isometries, and projections -/

section IdentitiesAndBounds

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [DaggerCategory C]
  [CStarCategory C] {W X Y Z : C}

/-- Every self-adjoint idempotent (`p ≫ p = p` and `dagger p = p`) in a C⋆-category has norm `0`
or `1`. -/
theorem norm_eq_zero_or_one_of_idempotent_of_dagger_eq {p : X ⟶ X}
    (hp : p ≫ p = p) (hd : dagger p = p) : ‖p‖ = 0 ∨ ‖p‖ = 1 := by
  rcases eq_or_ne p 0 with rfl | hp0
  · exact Or.inl norm_zero
  · right
    have hpos : 0 < ‖p‖ := norm_pos_iff.mpr hp0
    have hsq : ‖p‖ * ‖p‖ = ‖p‖ := by
      simpa only [sq, hd, hp] using (norm_comp_dagger_self p).symm
    exact (mul_eq_right₀ hpos.ne').mp hsq

/-- Every self-adjoint idempotent (`p ≫ p = p` and `dagger p = p`) in a C⋆-category is a
contraction (`‖p‖ ≤ 1`). -/
theorem norm_le_one_of_idempotent_of_dagger_eq {p : X ⟶ X}
    (hp : p ≫ p = p) (hd : dagger p = p) : ‖p‖ ≤ 1 := by
  rcases norm_eq_zero_or_one_of_idempotent_of_dagger_eq hp hd with h | h <;> linarith

/-- Every nonzero self-adjoint idempotent in a C⋆-category has norm `1`. -/
theorem norm_eq_one_of_idempotent_of_dagger_eq_of_ne_zero {p : X ⟶ X}
    (hp : p ≫ p = p) (hd : dagger p = p) (hp0 : p ≠ 0) : ‖p‖ = 1 :=
  (norm_eq_zero_or_one_of_idempotent_of_dagger_eq hp hd).resolve_left (norm_ne_zero_iff.mpr hp0)

/-- Every identity morphism in a C⋆-category has norm `0` or `1`. -/
theorem norm_id_eq_zero_or_one (X : C) : ‖(𝟙 X : X ⟶ X)‖ = 0 ∨ ‖(𝟙 X : X ⟶ X)‖ = 1 :=
  norm_eq_zero_or_one_of_idempotent_of_dagger_eq (Category.id_comp (𝟙 X)) (dagger_id X)

/-- Every identity morphism in a C⋆-category has norm at most `1`. -/
theorem norm_id_le_one (X : C) : ‖(𝟙 X : X ⟶ X)‖ ≤ 1 :=
  norm_le_one_of_idempotent_of_dagger_eq (Category.id_comp (𝟙 X)) (dagger_id X)

/-- On an object with a nontrivial endomorphism space, the identity morphism has norm `1`. -/
@[simp] theorem norm_id [Nontrivial (X ⟶ X)] : ‖(𝟙 X : X ⟶ X)‖ = 1 := by
  have : Nontrivial (End X) := End.homEquiv.nontrivial
  exact CStarRing.norm_one (E := End X)

/-- `X ⟶ X` is a subsingleton precisely when `‖𝟙 X‖ = 0`. -/
theorem subsingleton_hom_self_iff_norm_id_eq_zero (X : C) :
    Subsingleton (X ⟶ X) ↔ ‖(𝟙 X : X ⟶ X)‖ = 0 := by
  rw [norm_eq_zero]
  refine ⟨fun _ => Subsingleton.elim _ _, fun h => ⟨fun f g => ?_⟩⟩
  calc
    f = f ≫ 𝟙 X := (Category.comp_id f).symm
    _ = 0 := by rw [h, Limits.comp_zero]
    _ = g ≫ 𝟙 X := by rw [h, Limits.comp_zero]
    _ = g := Category.comp_id g

/-- `X ⟶ X` is nontrivial precisely when `‖𝟙 X‖ = 1`. -/
theorem nontrivial_hom_self_iff_norm_id_eq_one (X : C) :
    Nontrivial (X ⟶ X) ↔ ‖(𝟙 X : X ⟶ X)‖ = 1 := by
  refine ⟨fun _ => norm_id, fun h => ?_⟩
  rw [← not_subsingleton_iff_nontrivial, subsingleton_hom_self_iff_norm_id_eq_zero, h]
  exact one_ne_zero

/-- An object in a C⋆-category is a zero object precisely when its identity arrow has norm `0`. -/
theorem isZero_iff_norm_id_eq_zero (X : C) :
    Limits.IsZero X ↔ ‖(𝟙 X : X ⟶ X)‖ = 0 := by
  rw [Limits.IsZero.iff_id_eq_zero, norm_eq_zero]

/-- An object in a C⋆-category is nonzero precisely when its identity arrow has norm `1`. -/
theorem not_isZero_iff_norm_id_eq_one (X : C) :
    ¬ Limits.IsZero X ↔ ‖(𝟙 X : X ⟶ X)‖ = 1 := by
  rw [isZero_iff_norm_id_eq_zero]
  rcases norm_id_eq_zero_or_one X with h | h <;> simp [h]

/-- Post-composing by a dagger-isometry (`f ≫ dagger f = 𝟙 X`) preserves norms on every incoming
Hom space `W ⟶ X`. -/
theorem norm_comp_of_comp_dagger_id {f : X ⟶ Y} (hf : f ≫ dagger f = 𝟙 X) (g : W ⟶ X) :
    ‖g ≫ f‖ = ‖g‖ := by
  rw [← sqrt_norm_comp_dagger_self (g ≫ f), ← sqrt_norm_comp_dagger_self g]
  congr 2
  rw [dagger_comp, Category.assoc, ← Category.assoc f (dagger f), hf, Category.id_comp]

/-- Pre-composing by a dagger-coisometry (`dagger f ≫ f = 𝟙 Y`) preserves norms on every outgoing
Hom space `Y ⟶ Z`. -/
theorem norm_comp_of_dagger_comp_id {f : X ⟶ Y} (hf : dagger f ≫ f = 𝟙 Y) (g : Y ⟶ Z) :
    ‖f ≫ g‖ = ‖g‖ := by
  rw [← norm_dagger (f ≫ g), dagger_comp]
  have hf' : dagger f ≫ dagger (dagger f) = 𝟙 Y := by simpa only [dagger_dagger] using hf
  simpa only [norm_dagger] using norm_comp_of_comp_dagger_id hf' (dagger g)

/-- Any dagger-isometry (`f ≫ dagger f = 𝟙 X`) has norm `0` or `1`. -/
theorem norm_eq_zero_or_one_of_comp_dagger_id {f : X ⟶ Y} (hf : f ≫ dagger f = 𝟙 X) :
    ‖f‖ = 0 ∨ ‖f‖ = 1 := by
  have hsq : ‖f‖ ^ 2 = ‖(𝟙 X : X ⟶ X)‖ := by rw [← norm_comp_dagger_self, hf]
  rcases norm_id_eq_zero_or_one X with h0 | h1
  · left
    exact sq_eq_zero_iff.mp (hsq.trans h0)
  · right
    have h1' : ‖f‖ ^ 2 = 1 ^ 2 := by simpa using hsq.trans h1
    exact (sq_eq_sq₀ (norm_nonneg f) zero_le_one).mp h1'

/-- Any dagger-isometry (`f ≫ dagger f = 𝟙 X`) has norm at most `1`. -/
theorem norm_le_one_of_comp_dagger_id {f : X ⟶ Y} (hf : f ≫ dagger f = 𝟙 X) : ‖f‖ ≤ 1 := by
  rcases norm_eq_zero_or_one_of_comp_dagger_id hf with h | h <;> linarith

/-- A dagger-isometry out of an object with nontrivial endomorphisms has norm `1`. -/
theorem norm_eq_one_of_comp_dagger_id [Nontrivial (X ⟶ X)] {f : X ⟶ Y}
    (hf : f ≫ dagger f = 𝟙 X) : ‖f‖ = 1 := by
  have hsq : ‖f‖ ^ 2 = 1 ^ 2 := by rw [← norm_comp_dagger_self, hf, norm_id, one_pow]
  exact (sq_eq_sq₀ (norm_nonneg f) zero_le_one).mp hsq

/-- Any dagger-coisometry (`dagger f ≫ f = 𝟙 Y`) has norm at most `1`. -/
theorem norm_le_one_of_dagger_comp_id {f : X ⟶ Y} (hf : dagger f ≫ f = 𝟙 Y) : ‖f‖ ≤ 1 := by
  rw [← norm_dagger]
  exact norm_le_one_of_comp_dagger_id (by simpa only [dagger_dagger] using hf)

namespace IsUnitary

/-- Every unitary arrow has norm `0` or `1`. -/
theorem norm_eq_zero_or_one {f : X ⟶ Y} (hf : IsUnitary f) : ‖f‖ = 0 ∨ ‖f‖ = 1 :=
  norm_eq_zero_or_one_of_comp_dagger_id hf.hom_dagger_id

/-- Every unitary arrow has norm at most `1`. -/
theorem norm_le_one {f : X ⟶ Y} (hf : IsUnitary f) : ‖f‖ ≤ 1 :=
  norm_le_one_of_comp_dagger_id hf.hom_dagger_id

/-- A unitary arrow on a nonzero object has norm `1`. -/
theorem norm_eq_one [Nontrivial (X ⟶ X)] {f : X ⟶ Y} (hf : IsUnitary f) : ‖f‖ = 1 :=
  norm_eq_one_of_comp_dagger_id hf.hom_dagger_id

/-- Pre-composing by a unitary arrow preserves norms. -/
@[simp] theorem norm_comp_left {u : X ⟶ Y} (hu : IsUnitary u) (f : Y ⟶ Z) :
    ‖u ≫ f‖ = ‖f‖ :=
  norm_comp_of_dagger_comp_id hu.dagger_hom_id f

/-- Post-composing by a unitary arrow preserves norms. -/
@[simp] theorem norm_comp_right (f : W ⟶ X) {u : X ⟶ Y} (hu : IsUnitary u) :
    ‖f ≫ u‖ = ‖f‖ :=
  norm_comp_of_comp_dagger_id hu.hom_dagger_id f

/-- Pre-composition with a unitary arrow as a `ℂ`-linear isometric equivalence. -/
def leftCompLinearIsometryEquiv {u : X ⟶ Y} (hu : IsUnitary u) (Z : C) :
    (Y ⟶ Z) ≃ₗᵢ[ℂ] (X ⟶ Z) where
  toFun f := u ≫ f
  invFun g := TauCeti.dagger u ≫ g
  left_inv f := hu.dagger_hom_id_assoc f
  right_inv g := hu.hom_dagger_id_assoc g
  map_add' _ _ := Preadditive.comp_add _ _ _ _ _ _
  map_smul' _ _ := Linear.comp_smul _ _ _ _ _ _
  norm_map' := hu.norm_comp_left

/-- Evaluation of `IsUnitary.leftCompLinearIsometryEquiv`. -/
@[simp] theorem leftCompLinearIsometryEquiv_apply {u : X ⟶ Y} (hu : IsUnitary u) (Z : C)
    (f : Y ⟶ Z) : hu.leftCompLinearIsometryEquiv Z f = u ≫ f := (rfl)

/-- Post-composition with a unitary arrow as a `ℂ`-linear isometric equivalence. -/
def rightCompLinearIsometryEquiv (W : C) {u : X ⟶ Y} (hu : IsUnitary u) :
    (W ⟶ X) ≃ₗᵢ[ℂ] (W ⟶ Y) where
  toFun f := f ≫ u
  invFun g := g ≫ TauCeti.dagger u
  left_inv f := by simp only [Category.assoc, hu.hom_dagger_id, Category.comp_id]
  right_inv g := by simp only [Category.assoc, hu.dagger_hom_id, Category.comp_id]
  map_add' _ _ := Preadditive.add_comp _ _ _ _ _ _
  map_smul' _ _ := Linear.smul_comp _ _ _ _ _ _
  norm_map' f := hu.norm_comp_right f

/-- Evaluation of `IsUnitary.rightCompLinearIsometryEquiv`. -/
@[simp] theorem rightCompLinearIsometryEquiv_apply (W : C) {u : X ⟶ Y} (hu : IsUnitary u)
    (f : W ⟶ X) : hu.rightCompLinearIsometryEquiv W f = f ≫ u := (rfl)

end IsUnitary

/-- Equality arrows have norm `0` or `1`. -/
theorem norm_eqToHom_eq_zero_or_one (h : X = Y) : ‖eqToHom h‖ = 0 ∨ ‖eqToHom h‖ = 1 :=
  (isUnitary_eqToHom h).norm_eq_zero_or_one

/-- Equality arrows have norm at most `1`. -/
theorem norm_eqToHom_le_one (h : X = Y) : ‖eqToHom h‖ ≤ 1 :=
  (isUnitary_eqToHom h).norm_le_one

end IdentitiesAndBounds

end TauCeti

namespace CategoryTheory.Limits.IsZero

open TauCeti

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [DaggerCategory C]
  [CStarCategory C] {X Y : C}

/-- The identity arrow of a zero object has norm `0`. -/
@[simp] theorem norm_id_eq_zero (hX : IsZero X) : ‖(𝟙 X : X ⟶ X)‖ = 0 :=
  (TauCeti.isZero_iff_norm_id_eq_zero X).mp hX

/-- The unit of `End X` for a zero object `X` has norm `0`. -/
@[simp] theorem norm_one_end_eq_zero (hX : IsZero X) : ‖(1 : End X)‖ = 0 :=
  hX.norm_id_eq_zero

/-- Every arrow out of a zero object has norm `0`. -/
theorem norm_eq_zero_of_src (hX : IsZero X) (f : X ⟶ Y) : ‖f‖ = 0 := by
  rw [hX.eq_of_src f 0, norm_zero]

/-- Every arrow into a zero object has norm `0`. -/
theorem norm_eq_zero_of_tgt (hY : IsZero Y) (f : X ⟶ Y) : ‖f‖ = 0 := by
  rw [hY.eq_of_tgt f 0, norm_zero]

end CategoryTheory.Limits.IsZero

/-! ### Hilbert C⋆-module structure, Cauchy–Schwarz, and polarization on Hom spaces -/

namespace TauCeti

section CStarModuleAndPolarization

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [DaggerCategory C]
  [CStarCategory C] {X Y Z : C}

/-- Every Hom space `X ⟶ Y` in a C⋆-category is a right Hilbert `End X`-module (with Mathlib's
right action `MulOpposite.op a • f = a.asHom ≫ f` and `End X`-valued inner product
`⟨f, g⟩_{End X} = End.of (g ≫ dagger f)`). -/
instance homRightCStarModule (X Y : C) : CStarModule (End X)ᵐᵒᵖ (X ⟶ Y) where
  inner f g := op (End.of (g ≫ dagger f))
  inner_add_right := by
    intro f g h
    apply unop_injective
    ext
    exact Preadditive.add_comp _ _ _ _ _ _
  inner_self_nonneg := op_nonneg.mpr (comp_dagger_self_nonneg _)
  inner_self := by
    intro f
    rw [op_eq_zero_iff, End.ext_iff, End.zero_asHom, comp_dagger_self_eq_zero_iff]
  inner_op_smul_right := by
    intro a f g
    apply unop_injective
    ext
    exact Category.assoc a.unop.asHom g (dagger f)
  inner_smul_right_complex := by
    intro z f g
    apply unop_injective
    ext
    exact Linear.smul_comp X Y X z g (dagger f)
  star_inner f g := by
    apply unop_injective
    ext
    simp
  norm_eq_sqrt_norm_inner_self f := by
    rw [norm_op, End.norm_of, sqrt_norm_comp_dagger_self]

/-- Evaluation of the `End X`-valued right Hilbert-module inner product on `X ⟶ Y`. -/
@[simp] theorem unop_inner_end_hom (f g : X ⟶ Y) :
    unop (inner (End X)ᵐᵒᵖ f g) = End.of (g ≫ dagger f) := (rfl)

/-- Every Hom space `X ⟶ Y` in a C⋆-category is a left Hilbert `End Y`-module (with Mathlib's
action `(b : End Y) • f = f ≫ b.asHom` and `End Y`-valued inner product
`⟪f, g⟫_{End Y} = End.of (dagger f ≫ g)`). -/
instance homLeftCStarModule (X Y : C) : CStarModule (End Y) (X ⟶ Y) where
  inner f g := End.of (dagger f ≫ g)
  inner_add_right := by
    intro f g h
    ext
    exact Preadditive.comp_add _ _ _ _ _ _
  inner_self_nonneg := dagger_comp_self_nonneg _
  inner_self := by
    intro f
    rw [End.ext_iff, End.zero_asHom, dagger_comp_self_eq_zero_iff]
  inner_op_smul_right := by
    intro b f g
    ext
    exact (Category.assoc (dagger f) g b.asHom).symm
  inner_smul_right_complex := by
    intro z f g
    ext
    exact Linear.comp_smul Y X Y (dagger f) z g
  star_inner f g := by
    ext
    simp
  norm_eq_sqrt_norm_inner_self f := by
    rw [End.norm_of, sqrt_norm_dagger_comp_self]

/-- Evaluation of the `End Y`-valued left Hilbert-module inner product on `X ⟶ Y`. -/
@[simp] theorem inner_end_hom (f g : X ⟶ Y) :
    inner (End Y) f g = End.of (dagger f ≫ g) := (rfl)

/-- Operator-valued Cauchy–Schwarz inequality in `End X`: for any `f, g : X ⟶ Y`,
`(g ≫ dagger f) ≫ (f ≫ dagger g) ≤ ‖f‖ ^ 2 • (g ≫ dagger g)` in the spectral order of `End X`. -/
theorem comp_dagger_mul_comp_dagger_le (f g : X ⟶ Y) :
    End.of (f ≫ dagger g) * End.of (g ≫ dagger f) ≤ ‖f‖ ^ 2 • End.of (g ≫ dagger g) := by
  have hstar : star (End.of (g ≫ dagger f)) = End.of (f ≫ dagger g) := by
    ext
    simp
  simpa only [unop_inner_end_hom, hstar] using
    CStarModule.star_unop_inner_mul_unop_inner_le (A := End X) f g

/-- Operator-valued Cauchy–Schwarz inequality in `End Y`: for any `f, g : X ⟶ Y`,
`(dagger g ≫ f) ≫ (dagger f ≫ g) ≤ ‖f‖ ^ 2 • (dagger g ≫ g)` in the spectral order of `End Y`. -/
theorem dagger_comp_mul_dagger_comp_le (f g : X ⟶ Y) :
    End.of (dagger f ≫ g) * End.of (dagger g ≫ f) ≤ ‖f‖ ^ 2 • End.of (dagger g ≫ g) :=
  CStarModule.inner_mul_inner_swap_le (A := End Y) (x := f) (y := g)

/-- Scalar Cauchy–Schwarz bound for `g ≫ dagger f`. -/
theorem norm_comp_dagger_le (f g : X ⟶ Y) : ‖g ≫ dagger f‖ ≤ ‖f‖ * ‖g‖ :=
  CStarModule.norm_unop_inner_le (A := End X) f g

/-- Scalar Cauchy–Schwarz bound for `dagger f ≫ g`. -/
theorem norm_dagger_comp_le (f g : X ⟶ Y) : ‖dagger f ≫ g‖ ≤ ‖f‖ * ‖g‖ :=
  CStarModule.norm_inner_le (A := End Y) (X ⟶ Y)

/-- Norm recovery over the closed unit ball of `X ⟶ Y` using `f ≫ dagger g`. -/
theorem isGreatest_norm_comp_dagger (f : X ⟶ Y) :
    IsGreatest {‖f ≫ dagger g‖ | (g : X ⟶ Y) (_ : ‖g‖ ≤ 1)} ‖f‖ :=
  CStarModule.isGreatest_norm_unop_inner (A := End X) f

/-- Norm recovery over the closed unit ball of `X ⟶ Y` using `dagger g ≫ f`. -/
theorem isGreatest_norm_dagger_comp (f : X ⟶ Y) :
    IsGreatest {‖dagger g ≫ f‖ | (g : X ⟶ Y) (_ : ‖g‖ ≤ 1)} ‖f‖ :=
  CStarModule.isGreatest_norm_inner (A := End Y) f

/-- Polarization identity in `X ⟶ X`: `g ≫ dagger f` is recovered as a linear combination of the
positive diagonal composites `h ≫ dagger h`. -/
theorem comp_dagger_polarization (f g : X ⟶ Y) :
    g ≫ dagger f =
      (4 : ℂ)⁻¹ • ((f + g) ≫ dagger (f + g) - (f - g) ≫ dagger (f - g) -
        I • ((f + I • g) ≫ dagger (f + I • g)) +
        I • ((f - I • g) ≫ dagger (f - I • g))) := by
  have h := congrArg (End.asHom ∘ unop) (CStarModule.inner_polarization (A := (End X)ᵐᵒᵖ) f g)
  exact h

/-- Polarization identity in `Y ⟶ Y`: `dagger f ≫ g` is recovered as a linear combination of the
positive diagonal composites `dagger h ≫ h`. -/
theorem dagger_comp_polarization (f g : X ⟶ Y) :
    dagger f ≫ g =
      (4 : ℂ)⁻¹ • (dagger (f + g) ≫ (f + g) - dagger (f - g) ≫ (f - g) -
        I • (dagger (f + I • g) ≫ (f + I • g)) +
        I • (dagger (f - I • g) ≫ (f - I • g))) :=
  congrArg End.asHom (CStarModule.inner_polarization (A := End Y) f g)

/-- Morphisms in `X ⟶ Y` are determined by right-pairing with `dagger h` for all `h : X ⟶ Y`. -/
theorem ext_comp_dagger_left {f g : X ⟶ Y}
    (h : ∀ k : X ⟶ Y, f ≫ dagger k = g ≫ dagger k) : f = g :=
  CStarModule.ext_inner_left (A := (End X)ᵐᵒᵖ) fun k =>
    unop_injective (End.ext (h k))

/-- Morphisms in `X ⟶ Y` are determined by left-pairing `k ≫ dagger -` against all `k : X ⟶ Y`. -/
theorem ext_comp_dagger_right {f g : X ⟶ Y}
    (h : ∀ k : X ⟶ Y, k ≫ dagger f = k ≫ dagger g) : f = g :=
  CStarModule.ext_inner_right (A := (End X)ᵐᵒᵖ) fun k =>
    unop_injective (End.ext (h k))

/-- Morphisms in `X ⟶ Y` are determined by left-pairing with `dagger k` for all `k : X ⟶ Y`. -/
theorem ext_dagger_comp_left {f g : X ⟶ Y}
    (h : ∀ k : X ⟶ Y, dagger k ≫ f = dagger k ≫ g) : f = g :=
  CStarModule.ext_inner_left (A := End Y) fun k => End.ext (h k)

/-- Morphisms in `X ⟶ Y` are determined by right-pairing `dagger - ≫ k` against all `k : X ⟶ Y`. -/
theorem ext_dagger_comp_right {f g : X ⟶ Y}
    (h : ∀ k : X ⟶ Y, dagger f ≫ k = dagger g ≫ k) : f = g :=
  CStarModule.ext_inner_right (A := End Y) fun k => End.ext (h k)

end CStarModuleAndPolarization

/-! ### Continuous bilinear composition and closed kernels on Hom spaces -/

section ContinuousComposition

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [DaggerCategory C]
  [CStarCategory C] {W X Y Z : C}

/-- Pre-composition `g ↦ f ≫ g` as a continuous `ℂ`-linear map `(Y ⟶ Z) →L[ℂ] (X ⟶ Z)`. -/
def leftCompCLM (Z : C) (f : X ⟶ Y) : (Y ⟶ Z) →L[ℂ] (X ⟶ Z) :=
  (Linear.leftComp ℂ Z f).mkContinuous ‖f‖ fun g => by
    rw [Linear.leftComp_apply]
    exact norm_comp_le' f g

/-- Evaluation of `leftCompCLM`. -/
@[simp] theorem leftCompCLM_apply (Z : C) (f : X ⟶ Y) (g : Y ⟶ Z) :
    leftCompCLM Z f g = f ≫ g := (rfl)

/-- Forgetting continuity from `leftCompCLM` recovers `Linear.leftComp ℂ`. -/
@[simp] theorem toLinearMap_leftCompCLM (Z : C) (f : X ⟶ Y) :
    (leftCompCLM Z f).toLinearMap = Linear.leftComp ℂ Z f := (rfl)

/-- The operator norm of `leftCompCLM Z f` is at most `‖f‖`. -/
theorem norm_leftCompCLM_le (Z : C) (f : X ⟶ Y) : ‖leftCompCLM Z f‖ ≤ ‖f‖ :=
  LinearMap.mkContinuous_norm_le (Linear.leftComp ℂ Z f) (norm_nonneg f) _

/-- When `Z = X`, the operator norm of `leftCompCLM X f` is `‖f‖`. -/
@[simp] theorem norm_leftCompCLM_self (f : X ⟶ Y) : ‖leftCompCLM X f‖ = ‖f‖ := by
  apply le_antisymm (norm_leftCompCLM_le X f)
  rcases eq_or_lt_of_le (norm_nonneg f) with hf | hf
  · rw [← hf]
    exact norm_nonneg _
  · refine le_of_mul_le_mul_right ?_ hf
    calc
      ‖f‖ * ‖f‖ = ‖leftCompCLM X f (dagger f)‖ := by
        rw [leftCompCLM_apply, norm_comp_dagger_self, sq]
      _ ≤ ‖leftCompCLM X f‖ * ‖dagger f‖ := (leftCompCLM X f).le_opNorm (dagger f)
      _ = ‖leftCompCLM X f‖ * ‖f‖ := by rw [norm_dagger]

/-- Post-composition `f ↦ f ≫ g` as a continuous `ℂ`-linear map `(X ⟶ Y) →L[ℂ] (X ⟶ Z)`. -/
def rightCompCLM (X : C) (g : Y ⟶ Z) : (X ⟶ Y) →L[ℂ] (X ⟶ Z) :=
  (Linear.rightComp ℂ X g).mkContinuous ‖g‖ fun f => by
    rw [Linear.rightComp_apply]
    exact norm_comp_le f g

/-- Evaluation of `rightCompCLM`. -/
@[simp] theorem rightCompCLM_apply (X : C) (g : Y ⟶ Z) (f : X ⟶ Y) :
    rightCompCLM X g f = f ≫ g := (rfl)

/-- Forgetting continuity from `rightCompCLM` recovers `Linear.rightComp ℂ`. -/
@[simp] theorem toLinearMap_rightCompCLM (X : C) (g : Y ⟶ Z) :
    (rightCompCLM X g).toLinearMap = Linear.rightComp ℂ X g := (rfl)

/-- The operator norm of `rightCompCLM X g` is at most `‖g‖`. -/
theorem norm_rightCompCLM_le (X : C) (g : Y ⟶ Z) : ‖rightCompCLM X g‖ ≤ ‖g‖ :=
  LinearMap.mkContinuous_norm_le (Linear.rightComp ℂ X g) (norm_nonneg g) _

/-- When `X = Z`, the operator norm of `rightCompCLM Z g` is `‖g‖`. -/
@[simp] theorem norm_rightCompCLM_self (g : Y ⟶ Z) : ‖rightCompCLM Z g‖ = ‖g‖ := by
  apply le_antisymm (norm_rightCompCLM_le Z g)
  rcases eq_or_lt_of_le (norm_nonneg g) with hg | hg
  · rw [← hg]
    exact norm_nonneg _
  · refine le_of_mul_le_mul_right ?_ hg
    calc
      ‖g‖ * ‖g‖ = ‖rightCompCLM Z g (dagger g)‖ := by
        rw [rightCompCLM_apply, norm_dagger_comp_self, sq]
      _ ≤ ‖rightCompCLM Z g‖ * ‖dagger g‖ := (rightCompCLM Z g).le_opNorm (dagger g)
      _ = ‖rightCompCLM Z g‖ * ‖g‖ := by rw [norm_dagger]

/-- Categorical composition `(f, g) ↦ f ≫ g` bundled as a contractive `ℂ`-bilinear continuous
linear map `(X ⟶ Y) →L[ℂ] (Y ⟶ Z) →L[ℂ] (X ⟶ Z)`. -/
def compCLM (X Y Z : C) : (X ⟶ Y) →L[ℂ] (Y ⟶ Z) →L[ℂ] (X ⟶ Z) :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℂ (fun f g => f ≫ g)
      (fun _ _ _ => Preadditive.add_comp _ _ _ _ _ _)
      (fun _ _ _ => Linear.smul_comp _ _ _ _ _ _)
      (fun _ _ _ => Preadditive.comp_add _ _ _ _ _ _)
      (fun _ _ _ => Linear.comp_smul _ _ _ _ _ _))
    1
    fun f g => by simpa only [LinearMap.mk₂_apply, one_mul] using norm_comp_le' f g

/-- Evaluation of `compCLM` in its first argument gives `leftCompCLM`. -/
@[simp] theorem compCLM_apply_left (f : X ⟶ Y) :
    compCLM X Y Z f = leftCompCLM Z f := by
  ext g
  rfl

/-- Doubly-applied evaluation of `compCLM`. -/
theorem compCLM_apply (f : X ⟶ Y) (g : Y ⟶ Z) :
    compCLM X Y Z f g = f ≫ g := (rfl)

/-- Bilinear categorical composition is contractive (`‖compCLM X Y Z‖ ≤ 1`). -/
theorem norm_compCLM_le_one (X Y Z : C) : ‖compCLM X Y Z‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

/-- On a nonzero object `X`, the bilinear composition map `compCLM X X X` has norm `1`. -/
@[simp] theorem norm_compCLM_self [Nontrivial (X ⟶ X)] : ‖compCLM X X X‖ = 1 := by
  apply le_antisymm (norm_compCLM_le_one X X X)
  have h := (compCLM X X X).le_opNorm (𝟙 X)
  simpa only [compCLM_apply_left, norm_leftCompCLM_self, norm_id, mul_one] using h

/-- The kernel `{g : Y ⟶ Z | f ≫ g = 0}` of pre-composition by `f` is norm-closed in `Y ⟶ Z`. -/
theorem isClosed_ker_leftComp (Z : C) (f : X ⟶ Y) :
    IsClosed (LinearMap.ker (Linear.leftComp ℂ Z f) : Set (Y ⟶ Z)) :=
  (leftCompCLM Z f).isClosed_ker

/-- The kernel `{g : Y ⟶ Z | f ≫ g = 0}` of pre-composition by `f` is a complete subspace. -/
instance completeSpace_ker_leftComp (Z : C) (f : X ⟶ Y) :
    CompleteSpace (LinearMap.ker (Linear.leftComp ℂ Z f)) :=
  (leftCompCLM Z f).completeSpace_ker

/-- The kernel `{f : X ⟶ Y | f ≫ g = 0}` of post-composition by `g` is norm-closed in `X ⟶ Y`. -/
theorem isClosed_ker_rightComp (X : C) (g : Y ⟶ Z) :
    IsClosed (LinearMap.ker (Linear.rightComp ℂ X g) : Set (X ⟶ Y)) :=
  (rightCompCLM X g).isClosed_ker

/-- The kernel `{f : X ⟶ Y | f ≫ g = 0}` of post-composition by `g` is a complete subspace. -/
instance completeSpace_ker_rightComp (X : C) (g : Y ⟶ Z) :
    CompleteSpace (LinearMap.ker (Linear.rightComp ℂ X g)) :=
  (rightCompCLM X g).completeSpace_ker

/-- For any endomorphisms `p : X ⟶ X` and `q : Y ⟶ Y` (in particular idempotents defining objects
of the Karoubi envelope), the corner subspace `{f : X ⟶ Y | p ≫ f = f ∧ f ≫ q = f}` is closed in
`X ⟶ Y`. -/
theorem isClosed_setOf_comp_eq_and_comp_eq (p : X ⟶ X) (q : Y ⟶ Y) :
    IsClosed {f : X ⟶ Y | p ≫ f = f ∧ f ≫ q = f} :=
  ((leftCompCLM Y p).isClosed_eqLocus (ContinuousLinearMap.id ℂ (X ⟶ Y))).inter
    ((rightCompCLM X q).isClosed_eqLocus (ContinuousLinearMap.id ℂ (X ⟶ Y)))

end ContinuousComposition

end TauCeti
