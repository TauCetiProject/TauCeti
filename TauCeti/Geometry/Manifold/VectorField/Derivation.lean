/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.RingTheory.Derivation.Lie
public import TauCeti.Geometry.Manifold.DerivationBundle
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Module
public import TauCeti.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.Algebra.Monoid
import TauCeti.Geometry.Manifold.ContMDiffMap.ExtChartAt
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Derivations of smooth functions are smooth vector fields

Differentiating along a smooth vector field `X` is a derivation `f ↦ (x ↦ df_x (X x))` of the
algebra of smooth scalar functions. On a finite-dimensional, Hausdorff, boundaryless real
manifold every derivation of `C^∞(M, ℝ)` arises this way from a unique smooth vector field. No
continuity of the derivation is assumed: at each point it is a point derivation, hence a tangent
vector, and smoothness of the resulting field is read off from the values of the derivation on
bump-localized coordinate functions.

## Main definitions

* `TauCeti.vectorFieldDerivation`: the derivation of smooth functions given by differentiation
  along a smooth vector field, as a linear map in the vector field.
* `Derivation.vectorField`: the tangent vector field of a derivation, read pointwise
  through `pointDerivationEquivTangentSpace`.
* `TauCeti.derivationEquivSmoothVectorField`: the `C^∞(M, ℝ)`-linear equivalence between
  derivations of `C^∞(M, ℝ)` and smooth vector fields.

## Main results

* `Derivation.mvfderiv_vectorField`: the inverse evaluation equation `δ f x = df_x (X x)`.
* `Derivation.contMDiff_vectorField`: the vector field of a derivation is smooth.
* `TauCeti.exists_derivationEquivSmoothVectorField`: derivations of `C^∞(M, ℝ)` are
  `C^∞(M, ℝ)`-linearly equivalent to smooth vector fields, compatibly with the evaluation
  equation.
* `Derivation.vectorField_smul`: multiplying a derivation by a smooth function multiplies
  its vector field pointwise.
* `Derivation.vectorField_lie`: the commutator of derivations corresponds to the manifold
  Lie bracket of vector fields.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, Lemma 3.3, p. 16.
-/

public section

open Bundle Filter Manifold VectorField
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti

section VectorFieldDerivation

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Differentiation of smooth scalar functions along a smooth vector field `X` is a derivation:
it sends `f` to the smooth function `x ↦ df_x (X x)`. -/
def vectorFieldDerivation :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ →ₗ[𝕜] Derivation 𝕜 C^∞⟮I, M; 𝕜⟯ C^∞⟮I, M; 𝕜⟯ where
  toFun X :=
    Derivation.mk'
      { toFun := fun f ↦
          ⟨fun x ↦ mvfderiv I f x (X x),
            (ContMDiff.contMDiff_mvfderiv_apply f.contMDiff (by simp)).comp X.contMDiff⟩
        map_add' := fun f g ↦ by
          ext x
          -- Unfold the smooth-function wrappers to use linearity of `mvfderiv`.
          change mvfderiv I (⇑f + ⇑g) x (X x) = mvfderiv I f x (X x) + mvfderiv I g x (X x)
          exact congr($(mvfderiv_add
            (f.contMDiff.mdifferentiable (by simp)).mdifferentiableAt
            (g.contMDiff.mdifferentiable (by simp)).mdifferentiableAt) (X x))
        map_smul' := fun c f ↦ by
          ext x
          -- Unfold the smooth-function wrappers to use homogeneity of `mvfderiv`.
          change mvfderiv I (c • ⇑f) x (X x) = c • mvfderiv I f x (X x)
          exact congr($(mvfderiv_const_smul_field (I := I) (⇑f) x c) (X x)) }
      fun f g ↦ by
        ext x
        -- Unfold the smooth-function wrappers to use the product rule for `mvfderiv`.
        change mvfderiv I (⇑f * ⇑g) x (X x) =
          f x * mvfderiv I g x (X x) + g x * mvfderiv I f x (X x)
        exact congr($(mvfderiv_mul
          (f.contMDiff.mdifferentiable (by simp)).mdifferentiableAt
          (g.contMDiff.mdifferentiable (by simp)).mdifferentiableAt) (X x))
  map_add' X Y := by
    ext f x
    -- Unfold the derivations to the pointwise directional derivatives.
    change mvfderiv I f x ((X + Y) x) = mvfderiv I f x (X x) + mvfderiv I f x (Y x)
    rw [ContMDiffSection.coe_add, Pi.add_apply, map_add]
  map_smul' c X := by
    ext f x
    -- Unfold the derivations to the pointwise directional derivatives.
    change mvfderiv I f x ((c • X) x) = c • mvfderiv I f x (X x)
    rw [ContMDiffSection.coe_smul, Pi.smul_apply, map_smul]

end VectorFieldDerivation

end TauCeti

namespace ContMDiffSection

open TauCeti

section VectorFieldDerivation

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The derivation of a smooth vector field differentiates a smooth function along the field. -/
@[simp]
theorem vectorFieldDerivation_apply_apply (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (f : C^∞⟮I, M; 𝕜⟯) (x : M) :
    vectorFieldDerivation X f x = mvfderiv I f x (X x) :=
  (rfl)

end VectorFieldDerivation

end ContMDiffSection

section DerivationVectorField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M]

namespace Derivation

open TauCeti

/-- The tangent vector field of a derivation of smooth functions: at each point `x`, the
derivation followed by evaluation at `x` is a point derivation, hence a tangent vector. -/
def vectorField (δ : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯) (x : M) :
    TangentSpace I x :=
  pointDerivationEquivTangentSpace x BoundarylessManifold.isInteriorPoint (Derivation.evalAt x δ)

/-- **Inverse evaluation.** A derivation differentiates every smooth function along its vector
field: `δ f x = df_x (X x)`. -/
theorem mvfderiv_vectorField (δ : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯)
    (f : C^∞⟮I, M; ℝ⟯) (x : M) :
    mvfderiv I f x (δ.vectorField x) = δ f x := by
  have h := congrArg (fun D : PointDerivation I x ↦ D f)
    (tangentToPointDerivation_pointDerivationEquivTangentSpace x
      BoundarylessManifold.isInteriorPoint (Derivation.evalAt x δ))
  simpa only [vectorField, tangentToPointDerivation_apply, Derivation.evalAt_apply] using h

/-- The inverse evaluation equation in the `mfderiv` normal form. -/
@[simp]
theorem mfderiv_vectorField (δ : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯)
    (f : C^∞⟮I, M; ℝ⟯) (x : M) :
    mfderiv I 𝓘(ℝ, ℝ) f x (δ.vectorField x) = δ f x := by
  rw [← mvfderiv_apply_eq_mfderiv_apply, mvfderiv_vectorField]

/-- The value of the vector field of a derivation at `x` is the unique tangent vector along which
every smooth function is differentiated by the derivation at `x`. -/
theorem eq_vectorField_iff {δ : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯} {x : M}
    {v : TangentSpace I x} :
    v = δ.vectorField x ↔ ∀ f : C^∞⟮I, M; ℝ⟯, mvfderiv I f x v = δ f x := by
  refine ⟨fun h f ↦ h ▸ mvfderiv_vectorField δ f x, fun h ↦ ?_⟩
  apply tangentToPointDerivation_injective (I := I) x
  ext (f : C^∞⟮I, M; ℝ⟯)
  rw [tangentToPointDerivation_apply, tangentToPointDerivation_apply]
  exact (h f).trans (mvfderiv_vectorField δ f x).symm

/-- The zero derivation has the zero vector field. -/
@[simp]
theorem vectorField_zero (x : M) :
    (0 : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯).vectorField x = 0 := by
  simp only [vectorField, map_zero]

/-- The vector field of a sum of derivations is the sum of their vector fields. -/
@[simp]
theorem vectorField_add (δ₁ δ₂ : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯) (x : M) :
    (δ₁ + δ₂).vectorField x = δ₁.vectorField x + δ₂.vectorField x := by
  simp only [vectorField, map_add]

/-- The vector field of a real multiple of a derivation is the same multiple of its vector field. -/
@[simp]
theorem vectorField_const_smul (r : ℝ) (δ : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯)
    (x : M) : (r • δ).vectorField x = r • δ.vectorField x := by
  have h : Derivation.evalAt x (r • δ) = r • Derivation.evalAt x δ :=
    LinearMap.map_smul_of_tower _ r δ
  simp only [vectorField, h, _root_.map_smul]

/-- **Smoothness of the vector field of a derivation.** In the chart at `x₀`, the coordinates of
`δ.vectorField` are the values of `δ` on bump-localized coordinate functions, which are
smooth because `δ` takes values in smooth functions. -/
theorem contMDiff_vectorField (δ : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯) :
    ContMDiff I I.tangent ∞ (T% δ.vectorField) := by
  intro x₀
  rw [contMDiffAt_section]
  -- A globally smooth map with the germ of the extended chart at `x₀`.
  obtain ⟨F, hF⟩ := exists_contMDiffMap_eventuallyEq_extChartAt (I := I) x₀
  -- Composing with the coordinates of a basis gives smooth scalar coordinate functions.
  let b := Module.finBasis ℝ E
  let φ (i : Fin (Module.finrank ℝ E)) : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (b.coord i)
  let c (i : Fin (Module.finrank ℝ E)) : C^∞⟮I, M; ℝ⟯ :=
    ⟨fun y ↦ φ i (F y), (φ i).contMDiff.comp F.contMDiff⟩
  have hsmooth : ContMDiffAt I 𝓘(ℝ, E) ∞ (fun y ↦ ∑ i, δ (c i) y • b i) x₀ :=
    contMDiffAt_finsetSum fun i _ ↦ (δ (c i)).contMDiff.contMDiffAt.smul contMDiffAt_const
  refine hsmooth.congr_of_eventuallyEq ?_
  have hsource : ∀ᶠ y in 𝓝 x₀, y ∈ (chartAt H x₀).source :=
    (chartAt H x₀).open_source.mem_nhds (mem_chart_source H x₀)
  filter_upwards [hF.eventuallyEq_nhds, hsource] with y hFy hy
  -- At `y` near `x₀` the trivialization reads a tangent vector through the derivative of the
  -- extended chart, which agrees with the derivative of `F`.
  have hFd : MDiffAt F y := F.contMDiff.mdifferentiable (by simp) y
  have hcoord (i : Fin (Module.finrank ℝ E)) :
      δ (c i) y = b.coord i (mvfderiv I (extChartAt I x₀) y (δ.vectorField y)) := by
    rw [← mvfderiv_vectorField, ← hFy.mvfderiv_eq]
    -- The coordinate function is the composite of `F` with the linear map `φ i`.
    change mvfderiv I (φ i ∘ F) y (δ.vectorField y) = _
    rw [mvfderiv_comp y (φ i).mdifferentiableAt hFd, ContinuousLinearMap.comp_apply,
      mvfderiv_eq_fderiv, (φ i).fderiv]
    rw [ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap',
      mvfderiv_apply_eq_mfderiv_apply, ContinuousLinearEquiv.coe_coe,
      NormedSpace.fromTangentSpace_apply]
  have htriv : (trivializationAt E (TangentSpace I) x₀ (T% δ.vectorField y)).2 =
      mvfderiv I (extChartAt I x₀) y (δ.vectorField y) := by
    have h := Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ)
      (trivializationAt E (TangentSpace I) x₀) (b := y) (by simpa using hy)
      (δ.vectorField y)
    rw [TangentBundle.continuousLinearMapAt_trivializationAt hy] at h
    rw [mvfderiv_apply_eq_mfderiv_apply]
    exact h.symm
  rw [htriv]
  conv_lhs => rw [← b.sum_repr (mvfderiv I (extChartAt I x₀) y (δ.vectorField y))]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [hcoord, Module.Basis.coord_apply]

/-- Multiplying a derivation by a smooth function multiplies its vector field pointwise. -/
@[simp]
theorem vectorField_smul (g : C^∞⟮I, M; ℝ⟯)
    (δ : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯) (x : M) :
    (g • δ).vectorField x = g x • δ.vectorField x := by
  refine (eq_vectorField_iff.mpr fun f ↦ ?_).symm
  rw [_root_.map_smul, mvfderiv_vectorField, _root_.smul_apply, smul_eq_mul,
    smul_eq_mul, ContMDiffMap.coe_mul, Pi.mul_apply]

/-- **Commutators of derivations are Lie brackets.** The vector field of the commutator of two
derivations is the manifold Lie bracket of their vector fields. -/
theorem vectorField_lie (δ₁ δ₂ : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯) (x : M) :
    ⁅δ₁, δ₂⁆.vectorField x = mlieBracket I δ₁.vectorField δ₂.vectorField x := by
  refine (eq_vectorField_iff.mpr fun f ↦ ?_).symm
  have h2 : minSmoothness ℝ 2 ≤ ∞ := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact ENat.LEInfty.out
  have : IsManifold I (minSmoothness ℝ 2) M := .of_le h2
  have hX (δ : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯) :
      MDiffAt (T% δ.vectorField) x :=
    (contMDiff_vectorField δ).mdifferentiable (by simp) x
  have hderiv (δ : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯) :
      (fun y ↦ mvfderiv I f y (δ.vectorField y)) = δ f :=
    funext fun y ↦ mvfderiv_vectorField δ f y
  rw [mvfderiv_mlieBracket f.contMDiff.contMDiffAt h2 (hX δ₁) (hX δ₂), hderiv, hderiv,
    mvfderiv_vectorField, mvfderiv_vectorField, Derivation.commutator_apply,
    ContMDiffMap.coe_sub, Pi.sub_apply]

end Derivation

namespace ContMDiffSection

open TauCeti

/-- The vector field of the derivation along a smooth vector field is that field. -/
@[simp]
theorem vectorField_vectorFieldDerivation (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (x : M) : (vectorFieldDerivation X).vectorField x = X x :=
  (Derivation.eq_vectorField_iff.mpr fun f ↦ (X.vectorFieldDerivation_apply_apply f x).symm).symm

end ContMDiffSection

namespace TauCeti

/-- **Derivations are smooth vector fields.** On a finite-dimensional, Hausdorff, boundaryless
real manifold, sending a derivation of `C^∞(M, ℝ)` to its vector field is a `C^∞(M, ℝ)`-linear
equivalence onto the smooth sections of the tangent bundle; its inverse differentiates along the
field. No continuity of the derivations is assumed. -/
def derivationEquivSmoothVectorField :
    Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ ≃ₗ[C^∞⟮I, M; ℝ⟯]
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ where
  toFun δ := ⟨δ.vectorField, δ.contMDiff_vectorField⟩
  map_add' δ₁ δ₂ := ContMDiffSection.ext (δ₁.vectorField_add δ₂)
  map_smul' g δ := by ext x; simp
  invFun := vectorFieldDerivation
  left_inv δ := by
    ext f x
    exact δ.mvfderiv_vectorField f x
  right_inv X := by
    ext x
    exact X.vectorField_vectorFieldDerivation x

/-- **Derivations and smooth vector fields.** On a finite-dimensional, Hausdorff, boundaryless real
manifold there is a `C^∞(M, ℝ)`-linear equivalence between derivations of `C^∞(M, ℝ)` and smooth
vector fields under which `δ f x = df_x (X x)`. -/
theorem exists_derivationEquivSmoothVectorField :
    ∃ e : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ ≃ₗ[C^∞⟮I, M; ℝ⟯]
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯,
      ∀ δ (f : C^∞⟮I, M; ℝ⟯) (x : M), δ f x = mvfderiv I f x (e δ x) :=
  ⟨derivationEquivSmoothVectorField, fun δ f x ↦ (δ.mvfderiv_vectorField f x).symm⟩

end TauCeti

namespace Derivation

open TauCeti

/-- The equivalence sends a derivation to its vector field. -/
@[simp]
theorem derivationEquivSmoothVectorField_apply_apply
    (δ : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯) (x : M) :
    derivationEquivSmoothVectorField δ x = δ.vectorField x :=
  (rfl)

end Derivation

namespace ContMDiffSection

open TauCeti

/-- The inverse equivalence sends a smooth vector field to differentiation along it. -/
@[simp]
theorem derivationEquivSmoothVectorField_symm_apply
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    derivationEquivSmoothVectorField.symm X = vectorFieldDerivation X :=
  (rfl)

end ContMDiffSection

end DerivationVectorField
