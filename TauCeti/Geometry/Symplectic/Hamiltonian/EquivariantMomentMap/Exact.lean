/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.DegreeOne
public import TauCeti.Geometry.Manifold.DifferentialForm.Flow
public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Basic

import TauCeti.Geometry.Manifold.Flow.Complete

/-!
# Moment maps of actions preserving a primitive

Let a Lie group `G` act smoothly on a manifold `M`, and let `α` be a smooth one-form on `M`
preserved by the action: `g^* α = α` for every `g`. Contracting `α` with the fundamental vector
fields gives a map

`μ : M → 𝔤*`, `⟨μ x, ξ⟩ = α_x(ξ_M x)`

(`TauCeti.SmoothForm.momentMap`). It is a group-level moment map for the exact two-form
`σ = -dα`: the components of `μ` are smooth, `d⟨μ, ξ⟩ = ι_{ξ_M} σ`, and `μ` is equivariant for the
coadjoint action, `μ (g • x) = Ad*_g (μ x)`
(`TauCeti.SmoothForm.isEquivariantMomentMap_momentMap`).

Equivariance follows from invariance of `α` and the equivariance `g_* (Ad_{g⁻¹} ξ)_M = ξ_M` of
fundamental vector fields (`TauCeti.SmoothForm.momentMap_smul`). For the moment map equation, the
flow of `ξ_M` is the action of the one-parameter subgroup `exp(t ξ)`, which preserves `α`, so the
Lie derivative `L_{ξ_M} α` vanishes (`TauCeti.mlieDerivForm_fundamentalVectorField_eq_zero`);
Cartan's formula `L_{ξ_M} α = ι_{ξ_M} dα + d(ι_{ξ_M} α)` then reads `ι_{ξ_M} σ = d⟨μ, ξ⟩`.

The main example is the cotangent bundle `T*Q` with its Liouville form, preserved by the cotangent
lift of any smooth action on `Q`; see
`TauCeti.Geometry.Symplectic.Cotangent.Bundle.MomentMap`.

## Main definitions

* `TauCeti.SmoothForm.momentMap I G α`: the map `x ↦ (ξ ↦ α_x(ξ_M x))` into the dual of the Lie
  algebra of `G`.

## Main results

* `TauCeti.SmoothForm.momentMap_smul`: if the action preserves `α`, then `μ` is coadjoint
  equivariant.
* `TauCeti.mlieDerivForm_fundamentalVectorField_eq_zero`: a form preserved by the action has zero
  Lie derivative along every fundamental vector field.
* `TauCeti.SmoothForm.isEquivariantMomentMap_momentMap`: if the action preserves `α`, then `μ` is
  a group-level moment map for `-dα`.

## References

* R. Abraham, J. E. Marsden, *Foundations of Mechanics*, 2nd ed., Benjamin/Cummings, 1978,
  Section 4.2 (momentum maps of exact symplectic actions).
* J. E. Marsden, T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in Applied
  Mathematics 17, Springer, 1999, Chapter 12.
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]
  [IsManifold I' ∞ M] [MulAction G M]

namespace SmoothForm

variable (I G) in
/-- The **moment map determined by a one-form** `α` for an action of `G` on `M`: at `x`, the
linear form `ξ ↦ α_x(ξ_M x)` on the Lie algebra of `G`, the contraction of `α` with the fundamental
vector fields. When the action preserves `α`, it is a group-level moment map for `-dα`
(`TauCeti.SmoothForm.isEquivariantMomentMap_momentMap`). -/
def momentMap (α : SmoothForm I' M ℝ 1) (x : M) : Module.Dual ℝ (GroupLieAlgebra I G) where
  toFun ξ := degreeOneEquiv α x (fundamentalVectorField I' ξ x)
  map_add' ξ η := by rw [fundamentalVectorField_add, Pi.add_apply, map_add]
  map_smul' c ξ := by rw [fundamentalVectorField_smul, Pi.smul_apply, map_smul, RingHom.id_apply]

/-- The moment map determined by `α` evaluates `ξ` at `x` as `α_x(ξ_M x)`. -/
@[simp]
theorem momentMap_apply (α : SmoothForm I' M ℝ 1) (x : M) (ξ : GroupLieAlgebra I G) :
    α.momentMap I G x ξ = α.1 x ![fundamentalVectorField I' ξ x] := by
  rw [momentMap, LinearMap.coe_mk, AddHom.coe_mk, degreeOneEquiv_apply_apply_vec]

/-- **Equivariance.** If the action preserves `α`, the moment map determined by `α` is equivariant
for the coadjoint action: `μ (g • x) = Ad*_g (μ x)`. -/
theorem momentMap_smul [LieGroup I 1 G] [ContMDiffSMul I I' ∞ G M] {α : SmoothForm I' M ℝ 1}
    (hα : ∀ g : G, mpullback (fun x : M ↦ g • x) (ContMDiffSMul.contMDiff_const_smul (I := I) g)
      α = α) (g : G) (x : M) :
    α.momentMap I G (g • x) = Lie.coadjointRepresentation ℝ I G g (α.momentMap I G x) := by
  ext ξ
  -- Invariance of `α` under `g`, evaluated at `x` on `(Ad_{g⁻¹} ξ)_M x`.
  have h := congrArg (fun β : SmoothForm I' M ℝ 1 ↦ β.1 x ![fundamentalVectorField I'
    (Lie.adjointContinuousLinearMap (I := I) g⁻¹ ξ) x]) (hα g)
  simp only [mpullback_apply] at h
  rw [Lie.coadjointRepresentation_apply, momentMap_apply, momentMap_apply, ← h]
  congr 1
  funext i
  -- `g` carries `(Ad_{g⁻¹} ξ)_M` at `x` to `ξ_M` at `g • x`.
  rw [Matrix.cons_val_fin_one, Matrix.cons_val_fin_one, mfderiv_smul_fundamentalVectorField,
    ← ContinuousLinearMap.comp_apply, ← Lie.adjointContinuousLinearMap_mul, mul_inv_cancel,
    Lie.adjointContinuousLinearMap_one, ContinuousLinearMap.id_apply]

/-- The components `x ↦ α_x(ξ_M x)` of the moment map determined by `α` are smooth. -/
theorem contMDiff_momentMap_apply [IsManifold I 1 G] [ContMDiffSMul I I' ∞ G M]
    (α : SmoothForm I' M ℝ 1) (ξ : GroupLieAlgebra I G) :
    ContMDiff I' 𝓘(ℝ) ∞ fun x ↦ α.momentMap I G x ξ := by
  have hX := contMDiff_fundamentalVectorField (I := I) (I' := I') (M := M) (m := ∞) (n := ∞)
    (by simp) ξ
  -- Pair the smooth section of `T*M` defined by `α` with the smooth field `ξ_M`.
  have h := ((degreeOneEquiv α).contMDiff (n := ∞)).clm_bundle_apply hX
  intro x
  have hx := (Bundle.contMDiffAt_totalSpace (IB := I') (n := ∞)).mp (h x)
  simpa [Bundle.Trivial.eq_trivialization] using hx.2

end SmoothForm

section Invariant

variable [CompleteSpace E] [LieGroup I (minSmoothness ℝ 3) G] [IsManifold I 1 G] [T2Space G]
  [BoundarylessManifold I G] [FiniteDimensional ℝ E'] [I'.Boundaryless] [T2Space M]
  [ContMDiffSMul I I' ∞ G M]

/-- **Invariant forms have zero Lie derivative along fundamental vector fields.** If a smooth action
of `G` preserves a smooth form `α`, then `L_{ξ_M} α = 0` for every `ξ` in the Lie algebra: the flow
of `ξ_M` is the action of `exp(t ξ)`. -/
theorem mlieDerivForm_fundamentalVectorField_eq_zero {k : ℕ} {α : SmoothForm I' M ℝ k}
    (hα : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) α = α) (ξ : GroupLieAlgebra I G) :
    mlieDerivForm (fundamentalVectorField I' ξ) α.1 = 0 := by
  have hX : ContMDiff I' I'.tangent 2
      (fun y ↦ (⟨y, fundamentalVectorField I' ξ y⟩ : TangentBundle I' M)) :=
    contMDiff_fundamentalVectorField (m := 2) (n := ∞) (by simp) ξ
  -- The curves `t ↦ exp(t ξ) • x` are integral curves of `ξ_M` through every point.
  have hγ (x : M) := isMIntegralCurve_mulInvariantExp_smul_smul (I := I) (I' := I') ξ x
  have h0 (x : M) : mulInvariantExp ((0 : ℝ) • ξ) • x = x := by
    rw [zero_smul, mulInvariantExp_zero, one_smul]
  have hc : IsCompleteVectorField (fundamentalVectorField I' ξ (M := M)) :=
    (isCompleteVectorField_iff_exists_isMIntegralCurve (hX.of_le one_le_two)).2
      fun x ↦ ⟨_, h0 x, hγ x⟩
  refine (mlieDerivForm_eq_zero_iff_forall_mpullback_globalFlow_eq hc hX
    α.mdifferentiable).2 fun t ↦ ?_
  -- The flow of `ξ_M` is the action of the one-parameter subgroup `exp(t ξ)`.
  have hflow : globalFlow _ (hX.of_le one_le_two) hc t = fun x ↦ mulInvariantExp (t • ξ) • x :=
    funext fun x ↦ by
      simpa only [h0] using globalFlow_eq_of_isMIntegralCurve (hX.of_le one_le_two) hc (hγ x) t
  rw [hflow, ← SmoothForm.coe_mpullback _ (ContMDiffSMul.contMDiff_const_smul (I := I) _), hα]

namespace SmoothForm

/-- **Moment maps of actions preserving a primitive.** If a smooth action of a Lie group `G` on
`M` preserves a smooth one-form `α`, then `x ↦ (ξ ↦ α_x(ξ_M x))` is a coadjoint-equivariant moment
map of the action for the two-form `-dα`. -/
theorem isEquivariantMomentMap_momentMap {α : SmoothForm I' M ℝ 1}
    (hα : ∀ g : G, mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) α = α) :
    SmoothTwoForm.IsEquivariantMomentMap (-mextDerivₗ I' 1 α) (α.momentMap I G) where
  contMDiff := contMDiff_momentMap_apply α
  isHamiltonianVectorField ξ := SmoothTwoForm.isHamiltonianVectorField_iff.2 fun x v ↦ by
    have hX : ContMDiff I' I'.tangent 1
        (fun y ↦ (⟨y, fundamentalVectorField I' ξ y⟩ : TangentBundle I' M)) :=
      contMDiff_fundamentalVectorField (m := 1) (n := ∞) (by simp) ξ
    -- Cartan's formula `L_X α = ι_X dα + d(ι_X α)`, where `L_X α = 0` by invariance.
    have h := mlieDerivForm_apply_eq_mextDeriv_add (fun y ↦ (momentMap_apply α y ξ).symm)
      (α.mdifferentiable x) (hX.mdifferentiableAt one_ne_zero) v
    rw [mlieDerivForm_fundamentalVectorField_eq_zero hα, Pi.zero_apply,
      ContinuousAlternatingMap.coe_zero, Pi.zero_apply] at h
    rw [InfinitesimalAction.fundamental_apply, SmoothBundleForm.eval₂_neg,
      SmoothBundleForm.eval₂_apply, mextDerivₗ_apply]
    linear_combination h
  apply_smul :=
    -- The equivariance of fundamental vector fields only needs a `C¹` Lie group.
    haveI : LieGroup I 1 G :=
      LieGroup.of_le (n := minSmoothness ℝ 3) ((by norm_num : (1 : ℕ∞ω) ≤ 3).trans le_minSmoothness)
    momentMap_smul hα

end SmoothForm

end Invariant

end TauCeti
