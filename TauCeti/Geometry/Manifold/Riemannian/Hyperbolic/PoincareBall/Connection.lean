/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.PoincareBall.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LocalFrame
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Geometry.Manifold.VectorField.LieBracket
import all TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.PoincareBall.Basic
import all TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# The Levi-Civita connection in the Poincaré ball

For a finite-dimensional real inner product space `E`, we compute the Levi-Civita connection of the
Poincaré ball metric `4 ⟪dx, dy⟫ / (1 - ‖x‖²)²` on constant coordinate fields, identify its
Christoffel map, and deduce the coordinate covariant-derivative formula for general vector fields on
`PoincareBall E`.

In the inherited model-space coordinates on `PoincareBall E`, the covariant derivative of the
constant vector field `v` in direction `u` at `x` is

`(2 / (1 - ‖x‖²)) (⟪x, u⟫ v + ⟪x, v⟫ u - ⟪u, v⟫ x)`,

where `⟪·, ·⟫` is the Euclidean inner product of `E`. All formulas hold in every finite dimension
`dim E ≥ 0`, including dimensions zero and one.

## Main definitions

* `TauCeti.PoincareBall.constantField`: the vector field with constant coordinate value `v : E`.

## Main results

* `TauCeti.PoincareBall.leviCivitaConnection_const_apply`: explicit formula for the Levi-Civita
  derivative of a constant coordinate vector field.
* `TauCeti.PoincareBall.christoffelMap_leviCivitaConnection_apply`: the model-space Christoffel map
  of the Poincaré ball metric, independent of the finite basis used to construct it.
* `TauCeti.PoincareBall.leviCivitaConnection_comp_apply`: coordinate formula for the Levi-Civita
  derivative of a differentiable model-space-valued vector field.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 3
  and Theorem 5.10 (Koszul formula).
-/

public section

open Bundle CovariantDerivative Manifold Set VectorField
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.PoincareBall

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local notation "J" => 𝓘(ℝ, E)

/-- The vector field on `PoincareBall E` with constant coordinate value `v` in the model space
`E`. -/
def constantField (v : E) (x : PoincareBall E) : TangentSpace J x :=
  (tangentSpaceCastModel J x).symm v

/-- Evaluation of a constant coordinate vector field at `x`. -/
@[simp]
theorem constantField_apply (v : E) (x : PoincareBall E) :
    constantField v x = (tangentSpaceCastModel J x).symm v :=
  (rfl)

private theorem mpullback_const (v : E) :
    mpullback J J coe (fun _ : E ↦ v : ∀ y : E, TangentSpace J y) = constantField v := by
  let A : ∀ y : E, TangentSpace J y := fun _ ↦ v
  -- Name the ambient section so `rw` keeps its dependent fibre type aligned.
  change mpullback J J coe A = constantField v
  funext x
  have hcoe : mfderiv J J (coe : PoincareBall E → E) x =
      ((tangentSpaceCastModel J x).trans
        (NormedSpace.fromTangentSpace (coe x)).symm).toContinuousLinearMap :=
    TauCeti.Manifold.mfderiv_subtype_val (I := J) (show poincareBallOpens E from x)
  rw [mpullback_apply, hcoe, ContinuousLinearMap.inverse_equiv]
  rfl

/-- Constant coordinate vector fields are smooth sections of the tangent bundle. -/
theorem contMDiff_constantField [CompleteSpace E] (v : E) :
    ContMDiff J ((J).prod J) ∞
      (fun y ↦ (⟨y, constantField v y⟩ : TangentBundle J (PoincareBall E))) := by
  rw [← mpullback_const]
  exact ((contMDiff_vectorSpace_iff_contDiff (n := ∞)).2
    (contDiff_const (c := v))).mpullback_vectorField
      (contMDiff_coe.of_le (show (∞ : ℕ∞ω) ≤ ω from le_top))
      (fun x ↦ by
        have hcoe : mfderiv J J (coe : PoincareBall E → E) x =
            ((tangentSpaceCastModel J x).trans
              (NormedSpace.fromTangentSpace (coe x)).symm).toContinuousLinearMap :=
          TauCeti.Manifold.mfderiv_subtype_val (I := J) (show poincareBallOpens E from x)
        rw [hcoe]
        exact ContinuousLinearMap.isInvertible_equiv) (by simp)

private theorem mdifferentiableAt_constantField [CompleteSpace E] (v : E) (x : PoincareBall E) :
    MDifferentiableAt J ((J).prod J)
      (fun y ↦ (⟨y, constantField v y⟩ : TangentBundle J (PoincareBall E))) x :=
  (contMDiff_constantField v x).mdifferentiableAt (by simp)

/-- Constant coordinate vector fields commute. -/
@[simp]
theorem mlieBracket_constantField [CompleteSpace E] (u v : E) (x : PoincareBall E) :
    mlieBracket J (constantField u) (constantField v) x = 0 := by
  rw [← mpullback_const, ← mpullback_const]
  have h := mpullback_mlieBracket (I := J) (I' := J) (f := coe)
    (V := fun _ : E ↦ u) (W := fun _ : E ↦ v)
    (((contMDiffAt_vectorSpace_iff_contDiffAt (n := 1)).2
      contDiffAt_const).mdifferentiableAt one_ne_zero)
    (((contMDiffAt_vectorSpace_iff_contDiffAt (n := 1)).2
      contDiffAt_const).mdifferentiableAt one_ne_zero)
    (contMDiff_coe.of_le (show (2 : ℕ∞ω) ≤ ω from le_top) x) (by simp)
  rw [← h]
  simp only [mpullback, mlieBracket_const_model_space, map_zero]

end NormedSpace

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local notation "J" => 𝓘(ℝ, E)

omit [FiniteDimensional ℝ E] in
private theorem mvfderiv_inner_constantField (u v w : E) (x : PoincareBall E) :
    mvfderiv J (fun y ↦ inner ℝ (constantField u y) (constantField v y)) x (constantField w x) =
      16 * inner ℝ (x : E) w * inner ℝ u v / (1 - ‖(x : E)‖ ^ 2) ^ 3 := by
  have heq : (fun y ↦ inner ℝ (constantField u y) (constantField v y)) =
      (fun p : E ↦ 4 * inner ℝ u v / (1 - ‖p‖ ^ 2) ^ 2) ∘ coe := by
    funext y
    simp [inner_def, constantField]
  rw [heq]
  set t₀ : ℝ := 1 - ‖(x : E)‖ ^ 2
  have ht₀ : t₀ ≠ 0 := (one_sub_norm_sq_pos x).ne'
  have hsub : HasFDerivAt (fun p : E ↦ 1 - ‖p‖ ^ 2) (0 - 2 • innerSL ℝ (x : E)) (x : E) :=
    (hasFDerivAt_const (1 : ℝ) (x : E)).sub (hasStrictFDerivAt_norm_sq (x : E)).hasFDerivAt
  have hdiv : HasDerivAt (fun t : ℝ ↦ 4 * inner ℝ u v / t ^ 2)
      ((0 * t₀ ^ 2 - 4 * inner ℝ u v * ((2 : ℕ) * t₀ ^ (2 - 1) * 1)) / (t₀ ^ 2) ^ 2) t₀ :=
    HasDerivAt.fun_div (hasDerivAt_const t₀ (4 * inner ℝ u v))
      ((hasDerivAt_id t₀).pow 2) (pow_ne_zero 2 ht₀)
  have h := hdiv.comp_hasFDerivAt (x : E) hsub
  simp only [Function.comp_def] at h
  rw [mvfderiv_comp_apply x h.differentiableAt.mdifferentiableAt
    (contMDiff_coe.mdifferentiable (by simp) x)]
  have hcoe : mfderiv J J (coe : PoincareBall E → E) x =
      ((tangentSpaceCastModel J x).trans
        (NormedSpace.fromTangentSpace (coe x)).symm).toContinuousLinearMap :=
    TauCeti.Manifold.mfderiv_subtype_val (I := J) (show poincareBallOpens E from x)
  rw [hcoe, mvfderiv_eq_fderiv]
  change fderiv ℝ (fun p : E ↦ 4 * inner ℝ u v / (1 - ‖p‖ ^ 2) ^ 2) (x : E) w = _
  rw [h.fderiv]
  simp only [zero_sub, smul_apply, neg_apply, innerSL_apply_apply, smul_eq_mul, zero_mul,
    Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one]
  field_simp [ht₀]
  ring

/-- In the Poincaré ball coordinates, the Levi-Civita derivative of the constant coordinate vector
field `v` in direction `u` at `x` is `(2 / (1 - ‖x‖²)) (⟪x, u⟫ v + ⟪x, v⟫ u - ⟪u, v⟫ x)`, read in
the Euclidean model `E`. -/
@[simp]
theorem leviCivitaConnection_const_apply (x : PoincareBall E) (u v : E) :
    tangentSpaceCastModel J x
      (leviCivitaConnection J (PoincareBall E) (constantField v) x
        ((tangentSpaceCastModel J x).symm u)) =
      (2 / (1 - ‖(x : E)‖ ^ 2)) •
        (inner ℝ (x : E) u • v + inner ℝ (x : E) v • u - inner ℝ u v • (x : E)) := by
  rw [← constantField_apply u x]
  apply ext_inner_right ℝ
  intro w
  have h := two_inner_leviCivitaConnection_eq_koszul (I := J) (M := PoincareBall E)
    (mdifferentiableAt_constantField u x) (mdifferentiableAt_constantField v x)
    (mdifferentiableAt_constantField w x)
  rw [TauCeti.Manifold.koszul_apply] at h
  simp only [mlieBracket_constantField, inner_zero_left, mvfderiv_inner_constantField] at h
  rw [inner_def] at h
  simp only [constantField, ContinuousLinearEquiv.apply_symm_apply] at h
  rw [real_inner_comm u w] at h
  simp only [constantField, real_inner_smul_left, inner_add_left, inner_sub_left]
  field_simp [(one_sub_norm_sq_pos x).ne'] at h ⊢
  linarith

omit [FiniteDimensional ℝ E] in
private theorem eventually_symm_eq_constantField (x : PoincareBall E) :
    ∀ᶠ y in 𝓝 x, ∀ v : E,
      (trivializationAt E (TangentSpace J) x).symm y v = constantField v y := by
  let e := trivializationAt E (TangentSpace J) x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace J) x
  have h := TauCeti.Manifold.eventually_tangentSpaceOpenEquiv_symmL_trivializationAt_eq
    (I := J) (show poincareBallOpens E from x)
  filter_upwards [h, e.open_baseSet.mem_nhds hx] with y hy hyb v
  have h' := hy v
  rw [TangentBundle.symmL_model_space] at h'
  exact (e.symmL_apply (R := ℝ) hyb v).symm.trans h'

/-- The model-space Christoffel map of the Poincaré ball metric in its inherited coordinates,
independently of the finite basis used to construct it. The first argument `v` is the field value
and the second argument `u` is the differentiation direction. -/
@[simp]
theorem christoffelMap_leviCivitaConnection_apply {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ E) (x : PoincareBall E) (u v : E) :
    TauCeti.Manifold.christoffelMap b
      ((leviCivitaConnection J (PoincareBall E)).isCovariantDerivativeOn
        (s := (trivializationAt E (TangentSpace J) x).baseSet)) x v u =
      (2 / (1 - ‖(x : E)‖ ^ 2)) •
        (inner ℝ (x : E) u • v + inner ℝ (x : E) v • u - inner ℝ u v • (x : E)) := by
  let cov := leviCivitaConnection J (PoincareBall E)
  let e := trivializationAt E (TangentSpace J) x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace J) x
  have hsymm := eventually_symm_eq_constantField x
  have heq : (fun y ↦ e.symm y v) =ᶠ[𝓝 x] constantField v := hsymm.mono fun _ hy ↦ hy v
  have hσ' := mdifferentiableAt_constantField v x
  have hσ := hσ'.congr_of_eventuallyEq (heq.mono fun y hy ↦ congrArg (TotalSpace.mk' E y) hy)
  have hcongr : cov (fun y ↦ e.symm y v) x = cov (constantField v) x :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hσ hσ' Filter.univ_mem heq
  have h := TauCeti.Manifold.covariantDerivative_symm_apply_symm b
    (cov.isCovariantDerivativeOn (s := e.baseSet)) hx v u
  change cov (fun y ↦ e.symm y v) x (e.symm x u) =
    e.symm x (TauCeti.Manifold.christoffelMap b
      (cov.isCovariantDerivativeOn (s := e.baseSet)) x v u) at h
  rw [hcongr, hsymm.self_of_nhds u] at h
  have hread : ∀ w : E, tangentSpaceCastModel J x (e.symm x w) = w := fun w ↦ by
    rw [hsymm.self_of_nhds w, constantField_apply, ContinuousLinearEquiv.apply_symm_apply]
  exact (hread _).symm.trans ((congrArg (tangentSpaceCastModel J x) h.symm).trans
    (leviCivitaConnection_const_apply x u v))

/-- Coordinate formula for the Levi-Civita derivative of a vector field on `PoincareBall E` whose
model-space representation `g : PoincareBall E → E` is differentiable at `x`. -/
theorem leviCivitaConnection_comp_apply {g : PoincareBall E → E} {x : PoincareBall E}
    (hg : MDifferentiableAt J J g x) (u : E) :
    tangentSpaceCastModel J x
      (leviCivitaConnection J (PoincareBall E)
        (fun y ↦ (tangentSpaceCastModel J y).symm (g y)) x
        ((tangentSpaceCastModel J x).symm u)) =
      mvfderiv J g x (constantField u x) +
        (2 / (1 - ‖(x : E)‖ ^ 2)) •
          (inner ℝ (x : E) u • g x + inner ℝ (x : E) (g x) • u - inner ℝ u (g x) • (x : E)) := by
  let cov := leviCivitaConnection J (PoincareBall E)
  let e := trivializationAt E (TangentSpace J) x
  let b := Module.finBasis ℝ E
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace J) x
  have hsymm := eventually_symm_eq_constantField x
  have heq : (fun y ↦ e.symm y (g y)) =ᶠ[𝓝 x] fun y ↦ (tangentSpaceCastModel J y).symm (g y) :=
    hsymm.mono fun y hy ↦ hy (g y)
  have hread_g : ∀ᶠ y in 𝓝 x, (e ⟨y, e.symm y (g y)⟩).2 = g y :=
    Filter.eventually_of_mem (e.open_baseSet.mem_nhds hx) fun y hy ↦ by rw [e.apply_mk_symm hy]
  have hσ := (e.mdifferentiableAt_section_iff J _ hx).2 (hg.congr_of_eventuallyEq hread_g)
  have hσ' := hσ.congr_of_eventuallyEq (heq.symm.mono fun y hy ↦ congrArg (TotalSpace.mk' E y) hy)
  have hcongr : cov (fun y ↦ e.symm y (g y)) x =
      cov (fun y ↦ (tangentSpaceCastModel J y).symm (g y)) x :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hσ hσ' Filter.univ_mem heq
  have h := TauCeti.Manifold.covariantDerivative_symm_comp_apply_symm b
    (cov.isCovariantDerivativeOn (s := e.baseSet)) hx hg u
  change cov (fun y ↦ e.symm y (g y)) x (e.symm x u) = _ at h
  rw [hcongr, hsymm.self_of_nhds u] at h
  have hread : ∀ w : E, tangentSpaceCastModel J x (e.symm x w) = w := fun w ↦ by
    rw [hsymm.self_of_nhds w, constantField_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [← constantField_apply u x]
  exact (congrArg (tangentSpaceCastModel J x) h).trans
    ((hread _).trans (by rw [christoffelMap_leviCivitaConnection_apply]))

end FiniteDimensional

end TauCeti.PoincareBall
