/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.UpperHalfSpace.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LocalFrame
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Basic
import TauCeti.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import all TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.UpperHalfSpace.Basic
import all TauCeti.Geometry.Manifold.VectorBundle.Tangent

/-!
# The Levi-Civita connection in the upper half-space

Compute the Levi-Civita connection of the metric `(‖dx‖² + dt²) / t²` on constant coordinate
fields and identify its Christoffel map. These formulas give the connection coefficients used
to compute the curvature of the upper-half-space model. They hold over any finite-dimensional
real inner product space of horizontal coordinates, including dimension zero.

The Euclidean inner product in the formulas is the model-space inner product; the tangent
metric is divided by the square of the height. The order of the Christoffel-map arguments
follows the local-frame API: field value first, differentiation direction second.

The calculation uses Mathlib's `CovariantDerivative.leviCivitaConnection` through the Koszul
formula, and the existing inherited tangent-bundle trivializations of open submanifolds.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 3
  (upper half-space metric) and Theorem 5.10 (Koszul formula).
-/

public section

open Bundle Manifold CovariantDerivative VectorField Set
open scoped Manifold ContDiff Topology

noncomputable section

namespace TauCeti.UpperHalfSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local notation "P" => WithLp 2 (E × ℝ)
local notation "J" => 𝓘(ℝ, P)

private def constantField (v : P) (x : UpperHalfSpace E) : TangentSpace J x :=
  (tangentSpaceCastModel J x).symm v

omit [FiniteDimensional ℝ E] in
private theorem mpullback_const (v : P) :
    mpullback J J coe (fun _ : P => v : ∀ y : P, TangentSpace J y) = constantField v := by
  let A : ∀ y : P, TangentSpace J y := fun _ => v
  -- Name the dependent field to keep the pullback well typed during rewriting.
  change mpullback J J coe A = constantField v
  funext x
  have hcoe : mfderiv J J (coe : UpperHalfSpace E → P) x =
      ((tangentSpaceCastModel J x).trans
        (NormedSpace.fromTangentSpace (coe x)).symm).toContinuousLinearMap :=
    TauCeti.Manifold.mfderiv_subtype_val (I := J) (show upperHalfSpaceOpens E from x)
  rw [mpullback_apply, hcoe, ContinuousLinearMap.inverse_equiv]
  rfl

private theorem mdifferentiableAt_constantField (v : P) (x : UpperHalfSpace E) :
    MDifferentiableAt J ((J).prod J)
      (fun y => (⟨y, constantField v y⟩ : TangentBundle J (UpperHalfSpace E))) x := by
  rw [← mpullback_const]
  exact ((contMDiffAt_vectorSpace_iff_contDiffAt (n := 1)).2
    (contDiffAt_const (c := v))).mdifferentiableAt one_ne_zero |>.mpullback_vectorField
      (contMDiff_coe.of_le (show (2 : ℕ∞ω) ≤ ω from le_top) x)
      (by
        have hcoe : mfderiv J J (coe : UpperHalfSpace E → P) x =
            ((tangentSpaceCastModel J x).trans
              (NormedSpace.fromTangentSpace (coe x)).symm).toContinuousLinearMap :=
          TauCeti.Manifold.mfderiv_subtype_val (I := J) (show upperHalfSpaceOpens E from x)
        rw [hcoe]
        exact ContinuousLinearMap.isInvertible_equiv) le_rfl

private theorem mlieBracket_constantField (u v : P) (x : UpperHalfSpace E) :
    mlieBracket J (constantField u) (constantField v) x = 0 := by
  rw [← mpullback_const, ← mpullback_const]
  have h := mpullback_mlieBracket (I := J) (I' := J) (f := coe)
    (V := fun _ : P => u) (W := fun _ : P => v)
    (((contMDiffAt_vectorSpace_iff_contDiffAt (n := 1)).2
      contDiffAt_const).mdifferentiableAt one_ne_zero)
    (((contMDiffAt_vectorSpace_iff_contDiffAt (n := 1)).2
      contDiffAt_const).mdifferentiableAt one_ne_zero)
    (contMDiff_coe.of_le (show (2 : ℕ∞ω) ≤ ω from le_top) x) (by simp)
  rw [← h]
  simp only [mpullback, TauCeti.mlieBracket_const_model_space, map_zero]

omit [FiniteDimensional ℝ E] in
private theorem mvfderiv_inner_constantField (u v w : P) (x : UpperHalfSpace E) :
    mvfderiv J (fun y => inner ℝ (constantField u y) (constantField v y)) x (constantField w x) =
      -2 * inner ℝ u v * w.snd / height x ^ 3 := by
  have heq : (fun y => inner ℝ (constantField u y) (constantField v y)) =
      (fun p : P => inner ℝ u v / p.snd ^ 2) ∘ coe := by
    funext y
    simp [inner_def, constantField]
  rw [heq]
  have hd := (WithLp.sndL 2 ℝ E ℝ).hasFDerivAt (x := coe x)
  have hs := HasDerivAt.fun_div (hasDerivAt_const (height x) (inner ℝ u v))
    ((hasDerivAt_id (height x)).pow 2) (pow_ne_zero 2 (height_pos x).ne')
  have h := hs.comp_hasFDerivAt (coe x) hd
  simp only [Function.comp_def, Pi.pow_apply, id_eq] at h
  rw [mvfderiv_comp_apply x h.differentiableAt.mdifferentiableAt
    (contMDiff_coe.mdifferentiable (by simp) x)]
  have hcoe : mfderiv J J (coe : UpperHalfSpace E → P) x =
      ((tangentSpaceCastModel J x).trans
        (NormedSpace.fromTangentSpace (coe x)).symm).toContinuousLinearMap :=
    TauCeti.Manifold.mfderiv_subtype_val (I := J) (show upperHalfSpaceOpens E from x)
  rw [hcoe]
  -- Read the manifold derivative in the model and cancel the tangent-space casts.
  rw [mvfderiv_eq_fderiv]
  change fderiv ℝ (fun p : P => inner ℝ u v / p.snd ^ 2) (coe x) w = _
  rw [h.fderiv]
  simp
  field_simp [(height_pos x).ne']

/-- In the upper-half-space coordinates, the Levi-Civita derivative of the constant field
`v` in direction `u` is `(⟪u,v⟫ eₜ - uₜ v - vₜ u) / t`, where `eₜ` is the vertical unit vector.
The tangent-space identifications read the result in the Euclidean model. -/
@[simp] theorem leviCivitaConnection_const_apply (x : UpperHalfSpace E) (u v : P) :
    tangentSpaceCastModel J x
      (leviCivitaConnection J (UpperHalfSpace E)
        (fun y => (tangentSpaceCastModel J y).symm v) x
        ((tangentSpaceCastModel J x).symm u)) =
      (height x)⁻¹ • (inner ℝ u v • WithLp.toLp 2 (0, 1) - u.snd • v - v.snd • u) := by
  -- Name the dependent coordinate fields so the Koszul expression remains well typed.
  change tangentSpaceCastModel J x
    (leviCivitaConnection J (UpperHalfSpace E) (constantField v) x (constantField u x)) = _
  apply ext_inner_right ℝ
  intro w
  have h := two_inner_leviCivitaConnection_eq_koszul (I := J) (M := UpperHalfSpace E)
    (mdifferentiableAt_constantField u x) (mdifferentiableAt_constantField v x)
    (mdifferentiableAt_constantField w x)
  rw [TauCeti.Manifold.koszul_apply] at h
  simp only [mlieBracket_constantField, inner_zero_left, mvfderiv_inner_constantField] at h
  rw [inner_def] at h
  simp only [constantField, ContinuousLinearEquiv.apply_symm_apply] at h
  simp only [real_inner_smul_left, inner_sub_left]
  have hz : inner ℝ (WithLp.toLp 2 (0, (1 : ℝ)) : P) w = w.snd := by simp
  rw [hz]
  rw [real_inner_comm u w] at h
  simp only [constantField]
  field_simp [(height_pos x).ne'] at h ⊢
  linarith

omit [FiniteDimensional ℝ E] in
private theorem eventually_symmL_eq_constantField (x : UpperHalfSpace E) :
    ∀ᶠ y in 𝓝 x, ∀ v : P,
      (trivializationAt P (TangentSpace J) x).symmL ℝ y v = constantField v y := by
  have h := TauCeti.Manifold.eventually_tangentSpaceOpenEquiv_symmL_trivializationAt_eq
    (I := J) (show upperHalfSpaceOpens E from x)
  filter_upwards [h] with y hy
  intro v
  have h' := hy v
  rw [TangentBundle.symmL_model_space] at h'
  exact h'

omit [FiniteDimensional ℝ E] in
private theorem frameCovariantDerivative_constantField {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ P)
    (x : UpperHalfSpace E) (v : P) :
    TauCeti.Manifold.frameCovariantDerivative J b (trivializationAt P (TangentSpace J) x)
      (constantField v) x = 0 := by
  let e := trivializationAt P (TangentSpace J) x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt P (TangentSpace J) x
  have hcoeff (i : ι) :
      (fun y => e.localFrameCoeff J b i y (constantField v y)) =ᶠ[𝓝 x]
        fun _ => b.repr v i := by
    filter_upwards [eventually_symmL_eq_constantField x, e.open_baseSet.mem_nhds hx]
      with y hy hybase
    have hread : e.continuousLinearMapAt ℝ y (constantField v y) = v := by
      rw [← hy v]
      exact e.continuousLinearMapAt_symmL hybase v
    rw [Bundle.Trivialization.localFrameCoeff_eq_coeff e hybase]
    rw [Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ e hybase] at hread
    exact congrArg (fun a => b.repr a i) hread
  ext u
  rw [TauCeti.Manifold.frameCovariantDerivative_apply]
  simp only [zero_apply]
  apply Finset.sum_eq_zero
  intro i _
  have hd : HasMFDerivAt J 𝓘(ℝ) (fun y => e.localFrameCoeff J b i y (constantField v y)) x 0 :=
    (hasMFDerivAt_const (I := J) (c := b.repr v i) x).congr_of_eventuallyEq (hcoeff i)
  -- The coefficient expression is the application of the section coefficient linear map.
  have hzero :
      mvfderiv J ((LinearMap.piApply (e.localFrameCoeff J b i)) (constantField v)) x = 0 := by
    have heq : ((LinearMap.piApply (e.localFrameCoeff J b i)) (constantField v)) =
        fun y => e.localFrameCoeff J b i y (constantField v y) := rfl
    rw [heq, mvfderiv, hd.mfderiv]
    exact ContinuousLinearMap.comp_zero _
  rw [hzero]
  simp only [zero_apply, zero_smul]

/-- The Christoffel map of the upper-half-space metric in its inherited coordinates,
independently of the finite basis used to construct the map. The first input `v` is the field
value and the second input `u` is the direction of differentiation. -/
@[simp] theorem christoffelMap_leviCivitaConnection_apply {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ P)
    (x : UpperHalfSpace E) (u v : P) :
    TauCeti.Manifold.christoffelMap b
      ((leviCivitaConnection J (UpperHalfSpace E)).isCovariantDerivativeOn
        (s := (trivializationAt P (TangentSpace J) x).baseSet)) x v u =
      (height x)⁻¹ • (inner ℝ u v • WithLp.toLp 2 (0, 1) - u.snd • v - v.snd • u) := by
  let cov := leviCivitaConnection J (UpperHalfSpace E)
  let e := trivializationAt P (TangentSpace J) x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt P (TangentSpace J) x
  have hc := TauCeti.Manifold.covariantDerivative_eq_add_christoffelForm b
    (cov.isCovariantDerivativeOn (s := e.baseSet)) hx (mdifferentiableAt_constantField v x)
  rw [frameCovariantDerivative_constantField b x v, zero_add] at hc
  have hmap := TauCeti.Manifold.christoffelMap_apply b
    (cov.isCovariantDerivativeOn (s := e.baseSet)) hx v u
  have he (a : P) : e.symmL ℝ x a = constantField a x := by
    exact (eventually_symmL_eq_constantField x).self_of_nhds a
  rw [he v, he u, ← hc] at hmap
  have hread (a : TangentSpace J x) : e.continuousLinearMapAt ℝ x a = tangentSpaceCastModel J x a :=
    TauCeti.Manifold.continuousLinearMapAt_trivializationAt_self x a
  rw [hread] at hmap
  exact hmap.trans (leviCivitaConnection_const_apply x u v)

end TauCeti.UpperHalfSpace
