/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.RingTheory.Derivation.Lie
public import TauCeti.Geometry.Manifold.DerivationBundle
public import TauCeti.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.BumpFunction
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
* `TauCeti.derivationVectorField`: the tangent vector field of a derivation, read pointwise
  through `pointDerivationEquivTangentSpace`.
* `TauCeti.derivationEquivSmoothVectorField`: the real-linear equivalence between derivations of
  `C^∞(M, ℝ)` and smooth vector fields.

## Main results

* `TauCeti.mvfderiv_derivationVectorField`: the inverse evaluation equation `δ f x = df_x (X x)`.
* `TauCeti.contMDiff_derivationVectorField`: the vector field of a derivation is smooth.
* `TauCeti.exists_derivationEquivSmoothVectorField`: derivations of `C^∞(M, ℝ)` are linearly
  equivalent to smooth vector fields, compatibly with the evaluation equation.
* `TauCeti.derivation_apply_congr_of_eventuallyEq`: derivations are local operators.
* `TauCeti.derivationVectorField_smul`: multiplying a derivation by a smooth function multiplies
  its vector field pointwise.
* `TauCeti.derivationVectorField_lie`: the commutator of derivations corresponds to the manifold
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
          have hc : MDiffAt (fun _ : M ↦ c) x := mdifferentiableAt_const
          -- Unfold the smooth-function wrappers to use the product rule for `mvfderiv`.
          change mvfderiv I ((fun _ : M ↦ c) • ⇑f) x (X x) = c • mvfderiv I f x (X x)
          have h := congr($(mvfderiv_smul hc
            (f.contMDiff.mdifferentiable (by simp)).mdifferentiableAt) (X x))
          calc
            _ = (c • mvfderiv I f x + (mvfderiv I (fun _ : M ↦ c) x).smulRight (f x))
                (X x) := h
            _ = _ := by simp [mvfderiv_const] }
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

/-- The derivation of a smooth vector field differentiates a smooth function along the field. -/
@[simp]
theorem vectorFieldDerivation_apply_apply (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (f : C^∞⟮I, M; 𝕜⟯) (x : M) :
    vectorFieldDerivation X f x = mvfderiv I f x (X x) :=
  (rfl)

end VectorFieldDerivation

section DerivationVectorField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M]

/-- The tangent vector field of a derivation of smooth functions: at each point `x`, the
derivation followed by evaluation at `x` is a point derivation, hence a tangent vector. -/
def derivationVectorField (δ : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯) (x : M) :
    TangentSpace I x :=
  pointDerivationEquivTangentSpace x BoundarylessManifold.isInteriorPoint (Derivation.evalAt x δ)

/-- **Inverse evaluation.** A derivation differentiates every smooth function along its vector
field: `δ f x = df_x (X x)`. -/
theorem mvfderiv_derivationVectorField (δ : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯)
    (f : C^∞⟮I, M; ℝ⟯) (x : M) :
    mvfderiv I f x (derivationVectorField δ x) = δ f x := by
  have h := congrArg (fun D : PointDerivation I x ↦ D f)
    (tangentToPointDerivation_pointDerivationEquivTangentSpace x
      BoundarylessManifold.isInteriorPoint (Derivation.evalAt x δ))
  -- Unfold the point derivation of a tangent vector and evaluation of a global derivation.
  exact h

/-- The value of the vector field of a derivation at `x` is the unique tangent vector along which
every smooth function is differentiated by the derivation at `x`. -/
theorem eq_derivationVectorField_iff {δ : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯} {x : M}
    {v : TangentSpace I x} :
    v = derivationVectorField δ x ↔ ∀ f : C^∞⟮I, M; ℝ⟯, mvfderiv I f x v = δ f x := by
  refine ⟨fun h f ↦ h ▸ mvfderiv_derivationVectorField δ f x, fun h ↦ ?_⟩
  apply tangentToPointDerivation_injective (I := I) x
  ext f
  -- Unfold the point derivations of the two tangent vectors on the pointed smooth function.
  change mvfderiv I f x v = mvfderiv I f x (derivationVectorField δ x)
  exact (h f).trans (mvfderiv_derivationVectorField δ f x).symm

/-- **Smoothness of the vector field of a derivation.** In the chart at `x₀`, the coordinates of
`derivationVectorField δ` are the values of `δ` on bump-localized coordinate functions, which are
smooth because `δ` takes values in smooth functions. -/
theorem contMDiff_derivationVectorField (δ : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯) :
    ContMDiff I I.tangent ∞ (T% (derivationVectorField δ)) := by
  intro x₀
  rw [contMDiffAt_section]
  -- A bump function at `x₀` times the extended chart is a globally smooth map with the germ of
  -- the chart at `x₀`.
  let β : SmoothBumpFunction I x₀ := Classical.choice inferInstance
  let F : C^∞⟮I, M; 𝓘(ℝ, E), E⟯ :=
    ⟨fun y ↦ β y • extChartAt I x₀ y, β.contMDiff_smul contMDiffOn_extChartAt⟩
  have hF : (F : M → E) =ᶠ[𝓝 x₀] extChartAt I x₀ := by
    filter_upwards [β.eventuallyEq_one] with y hy
    simp [F, hy]
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
      δ (c i) y = b.coord i (mvfderiv I (extChartAt I x₀) y (derivationVectorField δ y)) := by
    rw [← mvfderiv_derivationVectorField, ← hFy.mvfderiv_eq]
    -- The coordinate function is the composite of `F` with the linear map `φ i`.
    change mvfderiv I (φ i ∘ F) y (derivationVectorField δ y) = _
    rw [mvfderiv_comp y (φ i).mdifferentiableAt hFd, ContinuousLinearMap.comp_apply,
      mvfderiv_eq_fderiv, (φ i).fderiv]
    rw [ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap']
    -- `mvfderiv` is by definition the manifold derivative read in the model space through
    -- `NormedSpace.fromTangentSpace`, which is the left-hand side.
    rfl
  have htriv : (trivializationAt E (TangentSpace I) x₀ (T% (derivationVectorField δ) y)).2 =
      mvfderiv I (extChartAt I x₀) y (derivationVectorField δ y) := by
    have h := Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ)
      (trivializationAt E (TangentSpace I) x₀) (b := y) (by simpa using hy)
      (derivationVectorField δ y)
    rw [TangentBundle.continuousLinearMapAt_trivializationAt hy] at h
    rw [mvfderiv_apply_eq_mfderiv_apply]
    exact h.symm
  rw [htriv]
  conv_lhs => rw [← b.sum_repr (mvfderiv I (extChartAt I x₀) y (derivationVectorField δ y))]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [hcoord, Module.Basis.coord_apply]

/-- **Derivations are smooth vector fields.** On a finite-dimensional, Hausdorff, boundaryless
real manifold, sending a derivation of `C^∞(M, ℝ)` to its vector field is a real-linear
equivalence onto the smooth sections of the tangent bundle; its inverse differentiates along the
field. -/
def derivationEquivSmoothVectorField :
    Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ ≃ₗ[ℝ] Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  LinearEquiv.ofLinearMap
    { toFun δ := ⟨derivationVectorField δ, contMDiff_derivationVectorField δ⟩
      map_add' δ₁ δ₂ := ContMDiffSection.ext fun x ↦ by
        rw [ContMDiffSection.coe_add, Pi.add_apply, ContMDiffSection.coeFn_mk,
          ContMDiffSection.coeFn_mk, ContMDiffSection.coeFn_mk, eq_comm,
          eq_derivationVectorField_iff]
        intro f
        rw [map_add, mvfderiv_derivationVectorField, mvfderiv_derivationVectorField,
          add_apply, ContMDiffMap.coe_add, Pi.add_apply]
      map_smul' r δ := ContMDiffSection.ext fun x ↦ by
        rw [ContMDiffSection.coe_smul, Pi.smul_apply, ContMDiffSection.coeFn_mk,
          ContMDiffSection.coeFn_mk, RingHom.id_apply, eq_comm, eq_derivationVectorField_iff]
        intro f
        rw [map_smul, mvfderiv_derivationVectorField, smul_apply,
          ContMDiffMap.coe_smul, Pi.smul_apply] }
    vectorFieldDerivation
    (by
      ext X x
      exact (eq_derivationVectorField_iff.mpr fun f ↦
        (vectorFieldDerivation_apply_apply X f x).symm).symm)
    (by
      ext δ f x
      exact mvfderiv_derivationVectorField δ f x)

/-- The equivalence sends a derivation to its vector field. -/
@[simp]
theorem derivationEquivSmoothVectorField_apply_apply
    (δ : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯) (x : M) :
    derivationEquivSmoothVectorField δ x = derivationVectorField δ x :=
  (rfl)

/-- The inverse equivalence sends a smooth vector field to differentiation along it. -/
@[simp]
theorem derivationEquivSmoothVectorField_symm_apply
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    derivationEquivSmoothVectorField.symm X = vectorFieldDerivation X :=
  (rfl)

/-- **Derivations and smooth vector fields.** On a finite-dimensional, Hausdorff, boundaryless real
manifold there is a real-linear equivalence between derivations of `C^∞(M, ℝ)` and smooth vector
fields under which `δ f x = df_x (X x)`. -/
theorem exists_derivationEquivSmoothVectorField :
    ∃ e : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ ≃ₗ[ℝ] Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯,
      ∀ δ (f : C^∞⟮I, M; ℝ⟯) (x : M), δ f x = mvfderiv I f x (e δ x) :=
  ⟨derivationEquivSmoothVectorField, fun δ f x ↦ (mvfderiv_derivationVectorField δ f x).symm⟩

omit [BoundarylessManifold I M] in
/-- **Locality of derivations.** A derivation of `C^∞(M, ℝ)` evaluated at `x` depends only on the
germ of the function at `x`. -/
theorem derivation_apply_congr_of_eventuallyEq (δ : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯)
    {f g : C^∞⟮I, M; ℝ⟯} {x : M} (hfg : (f : M → ℝ) =ᶠ[𝓝 x] g) : δ f x = δ g x :=
  (Derivation.evalAt x δ).congr_of_eventuallyEq f g hfg

/-- Multiplying a derivation by a smooth function multiplies its vector field pointwise. -/
theorem derivationVectorField_smul (g : C^∞⟮I, M; ℝ⟯)
    (δ : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯) (x : M) :
    derivationVectorField (g • δ) x = g x • derivationVectorField δ x := by
  refine (eq_derivationVectorField_iff.mpr fun f ↦ ?_).symm
  rw [map_smul, mvfderiv_derivationVectorField, smul_apply, smul_eq_mul,
    smul_eq_mul, ContMDiffMap.coe_mul, Pi.mul_apply]

/-- **Commutators of derivations are Lie brackets.** The vector field of the commutator of two
derivations is the manifold Lie bracket of their vector fields. -/
theorem derivationVectorField_lie (δ₁ δ₂ : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯) (x : M) :
    derivationVectorField ⁅δ₁, δ₂⁆ x =
      mlieBracket I (derivationVectorField δ₁) (derivationVectorField δ₂) x := by
  refine (eq_derivationVectorField_iff.mpr fun f ↦ ?_).symm
  have h2 : minSmoothness ℝ 2 ≤ ∞ := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact ENat.LEInfty.out
  have : IsManifold I (minSmoothness ℝ 2) M := .of_le h2
  have hX (δ : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯) :
      MDiffAt (T% (derivationVectorField δ)) x :=
    (contMDiff_derivationVectorField δ).mdifferentiable (by simp) x
  have hderiv (δ : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯) :
      (fun y ↦ mvfderiv I f y (derivationVectorField δ y)) = δ f :=
    funext fun y ↦ mvfderiv_derivationVectorField δ f y
  rw [mvfderiv_mlieBracket f.contMDiff.contMDiffAt h2 (hX δ₁) (hX δ₂), hderiv, hderiv,
    mvfderiv_derivationVectorField, mvfderiv_derivationVectorField, Derivation.commutator_apply,
    ContMDiffMap.coe_sub, Pi.sub_apply]

end DerivationVectorField

end TauCeti
