/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Derivation.Lie
public import TauCeti.Geometry.Manifold.DerivationBundle
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Module
public import TauCeti.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.ContMDiffMap.ExtChartAt
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Derivations of smooth functions are smooth vector fields

Let `M` be a finite-dimensional Hausdorff real manifold without boundary. Every algebraic
derivation `D` of the ring `C^∞(M, ℝ)` of smooth real functions, with no continuity assumption,
is differentiation along a unique smooth vector field `X`: `(D f)(x) = df_x(X_x)`.

The field is defined pointwise: evaluating `D f` at `x` is a point derivation at `x`, and the
point derivations at `x` are the tangent vectors at `x` (`pointDerivationEquivTangentSpace`).
Smoothness is read off in a chart: the chart coordinates of `X` near `x₀` are the smooth
functions `D cᵢ`, where the `cᵢ` are the coordinate functions of the chart at `x₀` multiplied by a
bump function equal to one near `x₀`.

Conversely, differentiation along a smooth vector field is a derivation, and the two constructions
are inverse to each other. Multiplying a derivation by a smooth function multiplies its field
pointwise, so the correspondence is `C^∞(M, ℝ)`-linear for the module structure of smooth
sections. The commutator of derivations corresponds to the Lie bracket of vector fields.

## Main declarations

* `Derivation.vectorField`: the tangent vector field of a derivation of `C^∞(M, ℝ)`.
* `Derivation.mvfderiv_vectorField`: the defining equation `df_x(X_x) = (D f)(x)`.
* `Derivation.vectorField_eq_iff`: this equation characterizes the field.
* `Derivation.contMDiff_vectorField`: the field is a smooth section of the tangent bundle.
* `Derivation.vectorField_smul`: the field of `f • D` is `f • X` pointwise.
* `Derivation.vectorField_lie`: the field of a commutator is the Lie bracket of the fields.
* `TauCeti.derivationEquivSmoothVectorField`: the `C^∞(M, ℝ)`-linear equivalence between
  derivations of `C^∞(M, ℝ)` and smooth vector fields.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural operations in differential geometry*, Springer,
  1993, Lemma 3.3 (derivations of smooth functions are vector fields).
-/

public section

noncomputable section

open Bundle VectorField
open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M]

namespace Derivation

/-- The tangent vector field of a derivation `D` of `C^∞(M, ℝ)`: its value at `x` is the tangent
vector corresponding to the point derivation `f ↦ (D f)(x)`. -/
def vectorField (D : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯) (x : M) : TangentSpace I x :=
  pointDerivationEquivTangentSpace x BoundarylessManifold.isInteriorPoint (evalAt x D)

variable (D : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯)

/-- Differentiating a smooth function along the field of a derivation `D` recovers `D`:
`df_x(X_x) = (D f)(x)`. -/
theorem mvfderiv_vectorField (f : C^∞⟮I, M; ℝ⟯) (x : M) :
    mvfderiv I f x (D.vectorField x) = D f x := by
  -- Both point derivations act on `f` through the pointed type synonym `C^∞⟮I, M; ℝ⟯⟨x⟩`, where
  -- `rw` cannot match their evaluation lemmas, so chain those lemmas as equations instead.
  exact (tangentToPointDerivation_apply x _ f).symm.trans
    ((DFunLike.congr_fun (tangentToPointDerivation_pointDerivationEquivTangentSpace x
      BoundarylessManifold.isInteriorPoint (evalAt x D)) f).trans (evalAt_apply D f x))

/-- The defining equation of the field of a derivation, in the `mfderiv` normal form. -/
@[simp]
theorem mfderiv_vectorField (f : C^∞⟮I, M; ℝ⟯) (x : M) :
    mfderiv I 𝓘(ℝ, ℝ) f x (D.vectorField x) = D f x := by
  rw [← mvfderiv_apply_eq_mfderiv_apply, mvfderiv_vectorField]

/-- The field of a derivation `D` is characterized by its defining equation: it is the only
tangent vector along which every smooth function differentiates as under `D`. -/
theorem vectorField_eq_iff {x : M} {v : TangentSpace I x} :
    D.vectorField x = v ↔ ∀ f : C^∞⟮I, M; ℝ⟯, mvfderiv I f x v = D f x := by
  refine ⟨fun h f ↦ h ▸ D.mvfderiv_vectorField f x, fun h ↦ ?_⟩
  apply tangentToPointDerivation_injective (I := I) x
  ext f
  -- As above, `f` lives in the pointed type synonym, so chain the evaluation lemmas.
  exact (tangentToPointDerivation_apply x _ f).trans <| (D.mvfderiv_vectorField f x).trans <|
    (h f).symm.trans (tangentToPointDerivation_apply x v f).symm

/-- The zero derivation has the zero field. -/
@[simp]
theorem vectorField_zero (x : M) :
    (0 : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯).vectorField x = 0 := by
  simp only [vectorField_eq_iff, map_zero, zero_apply, ContMDiffMap.coe_zero, Pi.zero_apply,
    implies_true]

/-- The field of a sum of derivations is the sum of their fields. -/
@[simp]
theorem vectorField_add (D₁ D₂ : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯) (x : M) :
    (D₁ + D₂).vectorField x = D₁.vectorField x + D₂.vectorField x := by
  simp only [vectorField_eq_iff, map_add, mvfderiv_vectorField, add_apply, ContMDiffMap.coe_add,
    Pi.add_apply, implies_true]

/-- Multiplying a derivation by a smooth function multiplies its field pointwise. -/
@[simp]
theorem vectorField_smul (g : C^∞⟮I, M; ℝ⟯) (x : M) :
    (g • D).vectorField x = g x • D.vectorField x := by
  simp only [vectorField_eq_iff, ContinuousLinearMap.map_smul, mvfderiv_vectorField, smul_apply,
    smul_eq_mul, ContMDiffMap.coe_mul, Pi.mul_apply, implies_true]

/-- Multiplying a derivation by a real number multiplies its field. -/
@[simp]
theorem vectorField_smul_real (c : ℝ) (x : M) :
    (c • D).vectorField x = c • D.vectorField x := by
  simp only [vectorField_eq_iff, ContinuousLinearMap.map_smul, mvfderiv_vectorField, smul_apply,
    ContMDiffMap.coe_smul, Pi.smul_apply, implies_true]

/-- The tangent vector field of a derivation of `C^∞(M, ℝ)` is smooth. -/
theorem contMDiff_vectorField :
    ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, D.vectorField x⟩ : TangentBundle I M)) := by
  intro x₀
  rw [contMDiffAt_section]
  -- Near `x₀` the extended chart agrees with a globally smooth map `F`. Composing `F` with the
  -- coordinates of a basis gives global smooth functions `c i`, and the chart coordinates of
  -- the field near `x₀` are the smooth functions `D (c i)`.
  obtain ⟨F, hF⟩ := TauCeti.exists_contMDiffMap_eventuallyEq_extChartAt (I := I) x₀
  let b := Module.finBasis ℝ E
  let φ (i : Fin (Module.finrank ℝ E)) : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (b.coord i)
  let c (i : Fin (Module.finrank ℝ E)) : C^∞⟮I, M; ℝ⟯ :=
    ⟨φ i ∘ F, (φ i).contDiff.contMDiff.comp F.contMDiff⟩
  have hsmooth : ContMDiff I 𝓘(ℝ, E) ∞ (fun y ↦ ∑ i, D (c i) y • b i) :=
    contMDiff_finsetSum fun i _ ↦ (D (c i)).contMDiff.smul contMDiff_const
  refine (hsmooth x₀).congr_of_eventuallyEq ?_
  filter_upwards [hF.eventuallyEq_nhds, extChartAt_source_mem_nhds (I := I) x₀] with y hy hys
  have hys' : y ∈ (chartAt H x₀).source := by simpa using hys
  -- In the trivialization at `x₀`, the coordinates of a tangent vector at `y` are its image
  -- under the derivative of the extended chart, which near `x₀` is the derivative of `F`.
  rw [← Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) _ (by simpa using hys'),
    TangentBundle.continuousLinearMapAt_trivializationAt hys']
  refine (mvfderiv_apply_eq_mfderiv_apply (extChartAt I x₀) y _).symm.trans ?_
  rw [← hy.mvfderiv_eq, ← b.sum_repr (mvfderiv I F y _)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← D.mvfderiv_vectorField (c i) y, ← b.coord_apply]
  congr 1
  have h := TauCeti.mvfderiv_comp_apply_of_differentiableAt (φ i).differentiableAt
    (F.contMDiff.mdifferentiable (by simp)).mdifferentiableAt (D.vectorField y)
  rw [ContinuousLinearMap.fderiv] at h
  simpa [c, φ] using h.symm

/-- The field of the commutator of two derivations is the Lie bracket of their fields. -/
theorem vectorField_lie (D₁ D₂ : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯) (x : M) :
    ⁅D₁, D₂⁆.vectorField x = mlieBracket I D₁.vectorField D₂.vectorField x := by
  have : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by simp)
  rw [vectorField_eq_iff]
  intro f
  -- Differentiating `f` along the field of a derivation `D` is the smooth function `D f`.
  have h (D : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯) :
      (fun y ↦ mvfderiv I f y (D.vectorField y)) = D f :=
    funext fun y ↦ D.mvfderiv_vectorField f y
  rw [mvfderiv_mlieBracket (f.contMDiff x) (by simp)
    ((D₁.contMDiff_vectorField x).mdifferentiableAt (by simp))
    ((D₂.contMDiff_vectorField x).mdifferentiableAt (by simp)), h, h,
    mvfderiv_vectorField, mvfderiv_vectorField, commutator_apply, ContMDiffMap.coe_sub,
    Pi.sub_apply]

end Derivation

namespace TauCeti

/-- The derivative of a smooth function along a smooth vector field, as a smooth function. -/
private def mvfderivSmooth (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (f : C^∞⟮I, M; ℝ⟯) :
    C^∞⟮I, M; ℝ⟯ :=
  ⟨fun x ↦ mvfderiv I f x (X x),
    (f.contMDiff.contMDiff_mvfderiv_apply (m := ∞) (by simp)).comp X.contMDiff⟩

omit [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] in
private theorem mvfderivSmooth_apply (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (f : C^∞⟮I, M; ℝ⟯) (x : M) :
    mvfderivSmooth X f x = mvfderiv I f x (X x) :=
  rfl

/-- Differentiation along a smooth vector field, as a linear map on `C^∞(M, ℝ)`. -/
private def mvfderivLinearMap (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯ where
  toFun := mvfderivSmooth X
  map_add' f g := by
    ext x
    rw [ContMDiffMap.coe_add (mvfderivSmooth X f), Pi.add_apply, mvfderivSmooth_apply,
      mvfderivSmooth_apply, mvfderivSmooth_apply, ContMDiffMap.coe_add,
      mvfderiv_add ((f.contMDiff x).mdifferentiableAt (by simp))
        ((g.contMDiff x).mdifferentiableAt (by simp)), add_apply]
  map_smul' c f := by
    ext x
    rw [RingHom.id_apply, ContMDiffMap.coe_smul c (mvfderivSmooth X f), Pi.smul_apply,
      mvfderivSmooth_apply, mvfderivSmooth_apply, ContMDiffMap.coe_smul,
      mvfderiv_const_smul_field, smul_apply]

omit [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] in
private theorem mvfderivLinearMap_apply (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (f : C^∞⟮I, M; ℝ⟯) (x : M) :
    mvfderivLinearMap X f x = mvfderiv I f x (X x) :=
  rfl

/-- Differentiation along a smooth vector field, as a derivation of `C^∞(M, ℝ)`. -/
private def derivationOfSection (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ :=
  Derivation.mk' (mvfderivLinearMap X) fun f g ↦ by
    ext x
    simp only [mvfderivLinearMap_apply, smul_eq_mul, ContMDiffMap.coe_add, ContMDiffMap.coe_mul,
      Pi.add_apply, Pi.mul_apply]
    rw [mvfderiv_mul ((f.contMDiff x).mdifferentiableAt (by simp))
      ((g.contMDiff x).mdifferentiableAt (by simp))]
    simp only [add_apply, smul_apply, smul_eq_mul]

omit [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] in
private theorem derivationOfSection_apply (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (f : C^∞⟮I, M; ℝ⟯) (x : M) :
    derivationOfSection X f x = mvfderiv I f x (X x) :=
  rfl

variable (I M) in
/-- **Derivations of `C^∞(M, ℝ)` are smooth vector fields.** On a finite-dimensional Hausdorff
real manifold without boundary, sending a derivation to its field is a `C^∞(M, ℝ)`-linear
equivalence between the derivations of `C^∞(M, ℝ)` and the smooth sections of the tangent
bundle. No continuity of the derivations is assumed. -/
def derivationEquivSmoothVectorField :
    Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ ≃ₗ[C^∞⟮I, M; ℝ⟯]
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ where
  toFun D := ⟨D.vectorField, D.contMDiff_vectorField⟩
  map_add' D₁ D₂ := ContMDiffSection.ext fun x ↦ Derivation.vectorField_add D₁ D₂ x
  map_smul' g D := by ext x; simp
  invFun := derivationOfSection
  left_inv D := by
    ext f x
    exact (derivationOfSection_apply _ f x).trans (D.mvfderiv_vectorField f x)
  right_inv X := ContMDiffSection.ext fun x ↦
    (Derivation.vectorField_eq_iff _).2 fun f ↦ (derivationOfSection_apply X f x).symm

/-- The section associated to a derivation is its field. -/
@[simp]
theorem derivationEquivSmoothVectorField_apply (D : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯)
    (x : M) : derivationEquivSmoothVectorField I M D x = D.vectorField x :=
  (rfl)

/-- The derivation of a smooth vector field `X` differentiates along `X`. -/
@[simp]
theorem derivationEquivSmoothVectorField_symm_apply
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (f : C^∞⟮I, M; ℝ⟯) (x : M) :
    (derivationEquivSmoothVectorField I M).symm X f x = mvfderiv I f x (X x) :=
  (rfl)

end TauCeti

end
