/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Sol.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LocalFrame
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Basic
import TauCeti.Geometry.Manifold.VectorField.LieBracket
import all TauCeti.Geometry.Manifold.Riemannian.Sol.Basic

/-!
# The Levi-Civita connection of Sol

Compute the Levi-Civita derivative of constant coordinate fields for the metric
`exp (2z) dx² + exp (-2z) dy² + dz²`, and its Christoffel map in the global coordinates.
These coefficients are the input for curvature computations and for the geodesic equation
of Sol. The Christoffel map takes the field value first and the differentiation direction
second, following the local-frame convention.

The calculation uses Mathlib's Levi-Civita connection, characterized by the Koszul formula
`CovariantDerivative.two_inner_leviCivitaConnection_eq_koszul`. Constant coordinate fields
commute, but their metric inner products vary with height. This follows the constant-field
Koszul calculation in `TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.UpperHalfSpace.Connection`;
the chart-frame identification uses the model-space trivializations as in
`TauCeti.Geometry.Manifold.Riemannian.Geodesic.Euclidean`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 5
  (the Koszul formula and Christoffel symbols).
* P. Scott, *The geometries of 3-manifolds*, Bull. London Math. Soc. 15 (1983), 401–487
  (the Sol geometry and its metric).
-/

public section

open Bundle Manifold CovariantDerivative VectorField Real
open scoped Manifold ContDiff

noncomputable section

namespace TauCeti.Sol

local notation "P" => ℝ × ℝ × ℝ
local notation "J" => 𝓘(ℝ, P)

private def C (v : P) (p : Sol) : TangentSpace J p :=
  (tangentSpaceCastModel J p).symm v

private theorem mdifferentiableAt_C (v : P) (p : Sol) :
    MDifferentiableAt J ((J).prod J)
      (fun q => (⟨q, C v q⟩ : TangentBundle J Sol)) p := by
  -- Sol inherits the model-space charts, and the tangent-space casts are identities.
  exact ((contMDiffAt_vectorSpace_iff_contDiffAt (n := (1 : ℕ∞ω))
    (V := fun _ : P => v)).2 contDiffAt_const).mdifferentiableAt one_ne_zero

private theorem mvfderiv_inner_C (u v w : P) (p : Sol) :
    mvfderiv J (fun q => inner ℝ (C u q) (C v q)) p (C w p) =
      2 * exp (2 * p.z) * w.2.2 * u.1 * v.1 -
        2 * exp (-2 * p.z) * w.2.2 * u.2.1 * v.2.1 := by
  have heq : (fun q => inner ℝ (C u q) (C v q)) =
      fun q : P => exp (2 * q.2.2) * u.1 * v.1 +
        exp (-2 * q.2.2) * u.2.1 * v.2.1 + u.2.2 * v.2.2 := by
    funext q
    simp only [inner_def, C, ContinuousLinearEquiv.apply_symm_apply]
    rfl
  rw [heq]
  -- Replace the inherited Sol charts by the identical model-space charts to use
  -- the model-space derivative formula; the constant tangent vector is unchanged.
  change (mvfderiv J (fun q : P => exp (2 * q.2.2) * u.1 * v.1 +
    exp (-2 * q.2.2) * u.2.1 * v.2.1 + u.2.2 * v.2.2) (toProd p)) w = _
  rw [mvfderiv_eq_fderiv]
  -- The model-space tangent cast in `mvfderiv_eq_fderiv` is the identity.
  change fderiv ℝ (fun q : P => exp (2 * q.2.2) * u.1 * v.1 +
    exp (-2 * q.2.2) * u.2.1 * v.2.1 + u.2.2 * v.2.2) (toProd p) w = _
  let hz := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
    (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))
  have hd := hz.hasFDerivAt (x := toProd p)
  have h := ((((hd.const_mul 2).exp.mul_const u.1).mul_const v.1).add
    (((hd.const_mul (-2)).exp.mul_const u.2.1).mul_const v.2.1)).add_const
      (u.2.2 * v.2.2)
  simp only [hz, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd',
    Pi.add_apply] at h
  rw [h.fderiv]
  simp only [add_apply, smul_apply,
    smul_eq_mul, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd']
  simp only [snd_snd_toProd]
  ring

/-- The Levi-Civita derivative of a constant coordinate field on Sol. The horizontal
coefficients couple the horizontal and vertical directions; the vertical coefficient is
`-exp (2z) u₁ v₁ + exp (-2z) u₂ v₂`. -/
@[simp] theorem leviCivitaConnection_const_apply (p : Sol) (u v : P) :
    tangentSpaceCastModel J p
      (leviCivitaConnection J Sol
        (fun q => (tangentSpaceCastModel J q).symm v) p
        ((tangentSpaceCastModel J p).symm u)) =
      (u.2.2 * v.1 + v.2.2 * u.1,
        -(u.2.2 * v.2.1 + v.2.2 * u.2.1),
        -exp (2 * p.z) * u.1 * v.1 + exp (-2 * p.z) * u.2.1 * v.2.1) := by
  let a : P := (u.2.2 * v.1 + v.2.2 * u.1,
    -(u.2.2 * v.2.1 + v.2.2 * u.2.1),
    -exp (2 * p.z) * u.1 * v.1 + exp (-2 * p.z) * u.2.1 * v.2.1)
  have heq : leviCivitaConnection J Sol (C v) p (C u p) = C a p := by
    apply ext_inner_right ℝ
    intro w
    obtain ⟨w, rfl⟩ := (tangentSpaceCastModel J p).symm.surjective w
    have h := two_inner_leviCivitaConnection_eq_koszul (I := J) (M := Sol)
      (mdifferentiableAt_C u p) (mdifferentiableAt_C v p) (mdifferentiableAt_C w p)
    rw [TauCeti.Manifold.koszul_apply] at h
    have hb (b c : P) : mlieBracket J (C b) (C c) p = 0 :=
      TauCeti.mlieBracket_const_model_space b c (toProd p)
    simp only [hb, inner_zero_left, mvfderiv_inner_C] at h
    simp only [inner_def, C, ContinuousLinearEquiv.apply_symm_apply] at h ⊢
    dsimp only [a]
    linear_combination h / 2
  exact congrArg (tangentSpaceCastModel J p) heq

private def Γ (p : Sol) : P →L[ℝ] P →L[ℝ] P :=
  xL.smulRight (zL.smulRight (1, 0, 0)) + zL.smulRight (xL.smulRight (1, 0, 0)) -
    yL.smulRight (zL.smulRight (0, 1, 0)) - zL.smulRight (yL.smulRight (0, 1, 0)) -
    exp (2 * p.z) • xL.smulRight (xL.smulRight (0, 0, 1)) +
    exp (-2 * p.z) • yL.smulRight (yL.smulRight (0, 0, 1))

private theorem Γ_apply (p : Sol) (v u : P) :
    Γ p v u = (u.2.2 * v.1 + v.2.2 * u.1,
      -(u.2.2 * v.2.1 + v.2.2 * u.2.1),
      -exp (2 * p.z) * u.1 * v.1 + exp (-2 * p.z) * u.2.1 * v.2.1) := by
  simp only [Γ, add_apply, sub_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    xL, yL, zL, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd']
  apply Prod.ext
  · simp; ring
  · apply Prod.ext <;> simp <;> ring

private theorem localFrame_eq_C {ι : Type*} (b : Module.Basis ι ℝ P)
    (p : Sol) (i : ι) :
    (trivializationAt P (TangentSpace J) p).localFrame b i = C (b i) := by
  funext q
  have hq : q ∈ (trivializationAt P (TangentSpace J) p).baseSet := by
    -- Sol's inherited global chart has the whole model space as its source.
    change toProd q ∈ (trivializationAt P (TangentSpace J) (toProd p)).baseSet
    simp [TangentBundle.trivializationAt_baseSet, chartAt_self_eq]
  rw [← TauCeti.Manifold.symmL_basis_eq_localFrame b hq i]
  -- In the model-space atlas the inverse fibre trivialization is the identity.
  change (trivializationAt P (TangentSpace J) (toProd p)).symmL ℝ (toProd q) (b i) = C (b i) q
  rw [TangentBundle.symmL_model_space]
  rfl

/-- The Christoffel map of Sol in its global coordinate chart. The formula is independent
of the finite basis used to define the map, and applies at every height. -/
@[simp] theorem christoffelMap_leviCivitaConnection_apply {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ P) (p : Sol) (u v : P) :
    TauCeti.Manifold.christoffelMap b
      ((leviCivitaConnection J Sol).isCovariantDerivativeOn
        (s := (trivializationAt P (TangentSpace J) p).baseSet)) p v u =
      (u.2.2 * v.1 + v.2.2 * u.1,
        -(u.2.2 * v.2.1 + v.2.2 * u.2.1),
        -exp (2 * p.z) * u.1 * v.1 + exp (-2 * p.z) * u.2.1 * v.2.1) := by
  classical
  let e := trivializationAt P (TangentSpace J) p
  let hc := (leviCivitaConnection J Sol).isCovariantDerivativeOn (s := e.baseSet)
  have hx : p ∈ e.baseSet := mem_baseSet_trivializationAt P (TangentSpace J) p
  have heq : TauCeti.Manifold.christoffelMap b hc p = Γ p := by
    refine ContinuousLinearMap.coe_injective (b.ext fun j => ?_)
    simp only [ContinuousLinearMap.coe_coe]
    refine ContinuousLinearMap.coe_injective (b.ext fun i => ?_)
    simp only [ContinuousLinearMap.coe_coe]
    have hs := TauCeti.Manifold.covariantDerivative_localFrame_eq_sum_christoffelSymbol
      b (cov := leviCivitaConnection J Sol) hx i j
    have hread := congrArg (tangentSpaceCastModel J p) hs
    simp only [e, localFrame_eq_C, C, map_sum, map_smul,
      ContinuousLinearEquiv.apply_symm_apply] at hread
    rw [TauCeti.Manifold.christoffelMap_apply_basis b hc hx i j, ← hread, Γ_apply]
    exact leviCivitaConnection_const_apply p (b i) (b j)
  rw [heq, Γ_apply]

end TauCeti.Sol
