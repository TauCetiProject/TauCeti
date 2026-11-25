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

/-!
# The Levi-Civita connection in the Poincaré ball

For a finite-dimensional real inner product space `E`, we compute the Levi-Civita connection of the
Poincaré ball metric `4 ⟪dx, dy⟫ / (1 - ‖x‖²)²` on constant coordinate fields `constantField v`,
`(2 / (1 - ‖x‖²)) (⟪x, u⟫ v + ⟪x, v⟫ u - ⟪u, v⟫ x)` (`leviCivitaConnection_const_apply`), identify
its model-space Christoffel map (`christoffelMap_leviCivitaConnection_apply`), and deduce the
coordinate covariant-derivative formula (`leviCivitaConnection_comp_apply`) in every finite
dimension `dim E ≥ 0`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 3
  and Theorem 5.10.
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
@[simp] theorem constantField_apply (v : E) (x : PoincareBall E) :
    constantField v x = (tangentSpaceCastModel J x).symm v := (rfl)

/-- Constant vector field on `E` (`TangentSpace 𝓘(ℝ, E) y` is the type synonym `E`,
`Mathlib/Geometry/Manifold/IsManifold/Basic.lean`). -/
private def ambientConstField (v : E) (y : E) : TangentSpace J y := v

private theorem mpullback_const (v : E) :
    mpullback J J coe (ambientConstField v) = constantField v := by
  funext x
  rw [mpullback_apply, mfderiv_coe, ContinuousLinearMap.inverse_equiv, constantField_apply]
  exact congrArg (tangentSpaceCastModel J x).symm
    (NormedSpace.fromTangentSpace_apply (𝕜 := ℝ) (x : E) v)

/-- Constant coordinate vector fields are smooth sections of the tangent bundle. -/
theorem contMDiff_constantField [CompleteSpace E] (v : E) :
    ContMDiff J ((J).prod J) ∞
      (fun y ↦ (⟨y, constantField v y⟩ : TangentBundle J (PoincareBall E))) := by
  rw [← mpullback_const]
  exact ((contMDiff_vectorSpace_iff_contDiff (𝕜 := ℝ) (n := ∞) (V := ambientConstField v)).2
    (contDiff_const (c := v))).mpullback_vectorField contMDiff_coe
      (fun x ↦ mfderiv_coe x ▸ ContinuousLinearMap.isInvertible_equiv) (by simp)

private theorem mdifferentiableAt_constantField [CompleteSpace E] (v : E) (x : PoincareBall E) :
    MDifferentiableAt J ((J).prod J)
      (fun y ↦ (⟨y, constantField v y⟩ : TangentBundle J (PoincareBall E))) x :=
  (contMDiff_constantField v x).mdifferentiableAt (by simp)

/-- Constant coordinate vector fields commute. -/
@[simp] theorem mlieBracket_constantField [CompleteSpace E] (u v : E) (x : PoincareBall E) :
    mlieBracket J (constantField u) (constantField v) x = 0 := by
  have hd (w : E) := ((contMDiffAt_vectorSpace_iff_contDiffAt (𝕜 := ℝ) (n := 1)
    (V := ambientConstField w) (x := (x : E))).2 contDiffAt_const).mdifferentiableAt one_ne_zero
  rw [← mpullback_const, ← mpullback_const, ← mpullback_mlieBracket (I := J) (I' := J) (f := coe)
    (hd u) (hd v) (contMDiff_coe x) (by simp), mpullback_apply]
  have hbr : mlieBracket J (ambientConstField u) (ambientConstField v) (x : E) = 0 :=
    mlieBracket_const_model_space u v (x : E)
  rw [hbr, map_zero]

end NormedSpace

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local notation "J" => 𝓘(ℝ, E)

omit [FiniteDimensional ℝ E] in
private theorem mvfderiv_inner_constantField (u v w : E) (x : PoincareBall E) :
    mvfderiv J (fun y ↦ inner ℝ (constantField u y) (constantField v y)) x (constantField w x) =
      16 * inner ℝ (x : E) w * inner ℝ u v / (1 - ‖(x : E)‖ ^ 2) ^ 3 := by
  have heq : (fun y ↦ inner ℝ (constantField u y) (constantField v y)) =
      (fun p : E ↦ 4 * inner ℝ u v / (1 - ‖p‖ ^ 2) ^ 2) ∘ coe :=
    funext fun y ↦ by simp [inner_def, constantField]
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
  rw [heq, TauCeti.mvfderiv_comp_apply_of_differentiableAt h.differentiableAt
      (contMDiff_coe.mdifferentiable (by simp) x),
    mvfderiv_coe_apply, constantField_apply, ContinuousLinearEquiv.apply_symm_apply, h.fderiv]
  simp only [zero_sub, smul_apply, neg_apply, innerSL_apply_apply, smul_eq_mul, zero_mul,
    Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one]
  field_simp [ht₀]
  ring

/-- In the Poincaré ball coordinates, the Levi-Civita derivative of the constant coordinate vector
field `v` in direction `u` at `x` is `(2 / (1 - ‖x‖²)) (⟪x, u⟫ v + ⟪x, v⟫ u - ⟪u, v⟫ x)`, read in
the Euclidean model `E`. -/
@[simp] theorem leviCivitaConnection_const_apply (x : PoincareBall E) (u v : E) :
    tangentSpaceCastModel J x
      (leviCivitaConnection J (PoincareBall E) (constantField v) x
        ((tangentSpaceCastModel J x).symm u)) =
      (2 / (1 - ‖(x : E)‖ ^ 2)) •
        (inner ℝ (x : E) u • v + inner ℝ (x : E) v • u - inner ℝ u v • (x : E)) := by
  rw [← constantField_apply u x]
  refine ext_inner_right ℝ fun w ↦ ?_
  have h := two_inner_leviCivitaConnection_eq_koszul (I := J) (M := PoincareBall E)
    (mdifferentiableAt_constantField u x) (mdifferentiableAt_constantField v x)
    (mdifferentiableAt_constantField w x)
  rw [TauCeti.Manifold.koszul_apply] at h
  simp only [mlieBracket_constantField, inner_zero_left, mvfderiv_inner_constantField] at h
  rw [inner_def] at h
  simp only [constantField, ContinuousLinearEquiv.apply_symm_apply, real_inner_comm u w] at h
  simp only [constantField, real_inner_smul_left, inner_add_left, inner_sub_left]
  field_simp [(one_sub_norm_sq_pos x).ne'] at h ⊢
  linarith

omit [FiniteDimensional ℝ E] in
private theorem eventually_symm_eq_constantField (x : PoincareBall E) :
    ∀ᶠ y in 𝓝 x, ∀ v : E,
      (trivializationAt E (TangentSpace J) x).symm y v = constantField v y := by
  let e := trivializationAt E (TangentSpace J) x
  filter_upwards [eventually_symmL_trivializationAt_eq x,
    e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt E (TangentSpace J) x)] with y hy hyb v
  exact (e.symmL_apply (R := ℝ) hyb v).symm.trans (hy v)

omit [FiniteDimensional ℝ E] in
private theorem tangentSpaceCastModel_trivializationAt_symm (x : PoincareBall E) (w : E) :
    tangentSpaceCastModel J x ((trivializationAt E (TangentSpace J) x).symm x w) = w := by
  rw [(eventually_symm_eq_constantField x).self_of_nhds w, constantField_apply,
    ContinuousLinearEquiv.apply_symm_apply]

private theorem leviCivitaConnection_trivializationAt_symm_comp {g : PoincareBall E → E}
    {x : PoincareBall E} (hg : MDifferentiableAt J J g x) :
    leviCivitaConnection J (PoincareBall E)
        (fun y ↦ (trivializationAt E (TangentSpace J) x).symm y (g y)) x =
      leviCivitaConnection J (PoincareBall E)
        (fun y ↦ (tangentSpaceCastModel J y).symm (g y)) x := by
  set cov := leviCivitaConnection J (PoincareBall E)
  set e := trivializationAt E (TangentSpace J) x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace J) x
  have heq : (fun y ↦ e.symm y (g y)) =ᶠ[𝓝 x] fun y ↦ (tangentSpaceCastModel J y).symm (g y) :=
    (eventually_symm_eq_constantField x).mono fun y hy ↦ hy (g y)
  have hread_g : ∀ᶠ y in 𝓝 x, (e ⟨y, e.symm y (g y)⟩).2 = g y :=
    Filter.eventually_of_mem (e.open_baseSet.mem_nhds hx) fun y hy ↦ by rw [e.apply_mk_symm hy]
  have hσ := (e.mdifferentiableAt_section_iff J _ hx).2 (hg.congr_of_eventuallyEq hread_g)
  have hσ' := hσ.congr_of_eventuallyEq (heq.symm.mono fun y hy ↦ congrArg (TotalSpace.mk' E y) hy)
  exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hσ hσ' Filter.univ_mem heq

/-- The model-space Christoffel map of the Poincaré ball metric in its inherited coordinates,
independently of the finite basis used to construct it. The first argument `v` is the field value
and the second argument `u` is the differentiation direction. -/
@[simp] theorem christoffelMap_leviCivitaConnection_apply {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ E) (x : PoincareBall E) (u v : E) :
    TauCeti.Manifold.christoffelMap b
      ((leviCivitaConnection J (PoincareBall E)).isCovariantDerivativeOn
        (s := (trivializationAt E (TangentSpace J) x).baseSet)) x v u =
      (2 / (1 - ‖(x : E)‖ ^ 2)) •
        (inner ℝ (x : E) u • v + inner ℝ (x : E) v • u - inner ℝ u v • (x : E)) := by
  set cov := leviCivitaConnection J (PoincareBall E)
  set e := trivializationAt E (TangentSpace J) x
  have hcongr : cov (fun y ↦ e.symm y v) x = cov (constantField v) x := by
    simpa only [← constantField_apply] using
      leviCivitaConnection_trivializationAt_symm_comp (x := x) (mdifferentiableAt_const (c := v))
  have h := TauCeti.Manifold.covariantDerivative_symm_apply_symm b (e := e)
    (cov.isCovariantDerivativeOn (s := e.baseSet))
    (mem_baseSet_trivializationAt E (TangentSpace J) x) v u
  rw [hcongr, (eventually_symm_eq_constantField x).self_of_nhds u] at h
  exact (tangentSpaceCastModel_trivializationAt_symm x _).symm.trans
    ((congrArg (tangentSpaceCastModel J x) h.symm).trans (leviCivitaConnection_const_apply x u v))

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
  set cov := leviCivitaConnection J (PoincareBall E)
  set e := trivializationAt E (TangentSpace J) x
  have h := TauCeti.Manifold.covariantDerivative_symm_comp_apply_symm (Module.finBasis ℝ E)
    (e := e) (cov.isCovariantDerivativeOn (s := e.baseSet))
    (mem_baseSet_trivializationAt E (TangentSpace J) x) hg u
  rw [leviCivitaConnection_trivializationAt_symm_comp hg,
    (eventually_symm_eq_constantField x).self_of_nhds u] at h
  rw [← constantField_apply u x]
  exact (congrArg (tangentSpaceCastModel J x) h).trans
    ((tangentSpaceCastModel_trivializationAt_symm x _).trans
      (by rw [christoffelMap_leviCivitaConnection_apply]))

end FiniteDimensional

end TauCeti.PoincareBall
