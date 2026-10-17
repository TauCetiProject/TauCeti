/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
public import TauCeti.LinearAlgebra.BilinearForm.Multilinear
public import TauCeti.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap

/-!
# Smooth differential two-forms on manifolds

The generic smooth differential-form carrier already records the alternating map in each tangent
fibre. This module supplies the degree-two view used by the symplectic API: `SmoothTwoForm` is
the scalar degree-two specialization, and its bilinear, evaluation, and constant-form operations
are derived from `SmoothForm`.

The old independent structure has deliberately disappeared. Keeping the specialization name
lets the symplectic modules state their degree-two hypotheses while sharing the generic form
operations and their smoothness proofs.
-/

public section

open Bundle
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A smooth real differential two-form is the generic smooth scalar form in degree two. -/
abbrev SmoothTwoForm (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] : Type _ :=
  SmoothForm I M ℝ 2

namespace SmoothTwoForm

variable {form form' : SmoothTwoForm I M}

/-- Evaluate a degree-two form on two tangent vectors. -/
instance : CoeFun (SmoothTwoForm I M) fun _ ↦
    (x : M) → TangentSpace I x → TangentSpace I x → ℝ :=
  ⟨fun form x v w ↦ SmoothForm.eval₂ form x v w⟩

@[simp] theorem isAlt (form : SmoothTwoForm I M) (x : M) (v : TangentSpace I x) :
    (form.1 x) ![v, v] = 0 := by
  simpa only [SmoothForm.eval₂_apply] using SmoothForm.eval₂_self form x v

/-- The algebraic bilinear form represented by a smooth two-form at a point. -/
def bilinFormAt (form : SmoothTwoForm I M) (x : M) :
    LinearMap.BilinForm ℝ (TangentSpace I x) :=
  SmoothForm.bilinFormAt form x

@[simp] theorem bilinFormAt_apply (form : SmoothTwoForm I M) (x : M)
    (v w : TangentSpace I x) : form.bilinFormAt x v w = form x v w := by
  exact SmoothForm.bilinFormAt_apply form x v w

theorem isAlt_bilinFormAt (form : SmoothTwoForm I M) (x : M) :
    (form.bilinFormAt x).IsAlt :=
  SmoothForm.isAlt_bilinFormAt form x

/-- The value of a two-form on the model fibre, for chart-based exterior calculus. -/
def altAt (form : SmoothTwoForm I M) (x : M) : E [⋀^Fin 2]→L[ℝ] ℝ :=
  SmoothForm.altAt form x

@[simp] theorem altAt_apply (form : SmoothTwoForm I M) (x : M) (v : Fin 2 → E) :
    form.altAt x v = form x (v 0) (v 1) := by
  exact SmoothForm.altAt_apply_eval₂ form x v

@[ext] theorem ext (h : ∀ (x : M) (v w : TangentSpace I x), form x v w = form' x v w) :
    form = form' := by
  apply SmoothForm.ext
  intro x v w
  exact h x v w

section Evaluation

end Evaluation

private theorem constAltIsAlt {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : ∀ v, B v v = 0) : LinearMap.IsAlt B.toBilinForm :=
  fun v ↦ by simpa only [ContinuousLinearMap.toBilinForm_apply] using hB v

private def constAlt {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : ∀ v, B v v = 0) : V [⋀^Fin 2]→L[ℝ] ℝ :=
  (constAltIsAlt B hB).toAlternatingMap.mkContinuous ‖B‖ (by
    intro v
    calc
      ‖(constAltIsAlt B hB).toAlternatingMap v‖ = ‖B (v 0) (v 1)‖ := by
        rw [LinearMap.IsAlt.toAlternatingMap_apply]
        rfl
      _ ≤ ‖B‖ * ∏ i, ‖v i‖ := by
        rw [Fin.prod_univ_two, ← mul_assoc]
        exact B.le_opNorm₂ (v 0) (v 1))

@[simp] private theorem constAlt_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : ∀ v, B v v = 0) (z : Fin 2 → V) :
    constAlt B hB z = B (z 0) (z 1) := by
  rw [constAlt, AlternatingMap.coe_mkContinuous, LinearMap.IsAlt.toAlternatingMap_apply]
  rfl

/-- A continuous alternating bilinear form defines a constant smooth two-form on its model space. -/
def const {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : ∀ v, B v v = 0) :
    SmoothTwoForm (modelWithCornersSelf ℝ V) V := by
  let A := constAlt B hB
  let A' : ∀ x : V, TangentSpace (modelWithCornersSelf ℝ V) x [⋀^Fin 2]→L[ℝ] ℝ :=
    fun x ↦ A.compContinuousLinearMap (NormedSpace.fromTangentSpace x).toContinuousLinearMap
  exact ⟨A', by
    apply (mem_smoothForms (I := modelWithCornersSelf ℝ V) (M := V)
      (F := ℝ) (k := 2) (φ := A')).2
    change IsSmoothBundleForm (I := modelWithCornersSelf ℝ V) (F := ℝ)
      (V := Bundle.Trivial V ℝ) ∞ A'
    rw [isSmoothBundleForm_def]
    intro x
    rw [contMDiffAt_continuousAlternatingMap_bundle]
    refine ⟨?_, ?_⟩
    · simpa only [Function.id_def] using (contMDiffAt_id : ContMDiffAt (modelWithCornersSelf ℝ V)
          (modelWithCornersSelf ℝ V) ∞ id x)
    · change ContMDiffAt (modelWithCornersSelf ℝ V)
        (𝓘(ℝ, V [⋀^Fin 2]→L[ℝ] ℝ)) ∞
        (fun y => ContinuousAlternatingMap.inCoordinates V ℝ
          (E₁ := TangentSpace (modelWithCornersSelf ℝ V))
          (E₂ := Bundle.Trivial V ℝ) x y x y (A' y)) x
      have hcoord : (fun y : V =>
          ContinuousAlternatingMap.inCoordinates V ℝ
            (E₁ := TangentSpace (modelWithCornersSelf ℝ V))
            (E₂ := Bundle.Trivial V ℝ) x y x y (A' y)) = fun _ => A := by
        funext y
        ext v
        simp only [A', ContinuousAlternatingMap.inCoordinates,
          Bundle.Trivial.eq_trivialization V ℝ
            (trivializationAt ℝ (Trivial V ℝ) x),
          Bundle.Trivial.continuousLinearMapAt_trivialization,
          TangentBundle.symmL_model_space,
          ]
        rfl
      rw [hcoord]
      exact contMDiffAt_const⟩

theorem const_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : ∀ v, B v v = 0) (x : V)
    (v w : TangentSpace (modelWithCornersSelf ℝ V) x) :
    const B hB x v w = B (NormedSpace.fromTangentSpace x v) (NormedSpace.fromTangentSpace x w) := by
  change SmoothForm.eval₂ (const B hB) x v w = _
  rw [SmoothForm.eval₂_apply]
  dsimp [const]
  rw [constAlt_apply]
  simp only [Function.comp_apply]
  simp

theorem const_model_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : ∀ v, B v v = 0) (x v w : V) :
    SmoothForm.eval₂ (const B hB) x ((NormedSpace.fromTangentSpace x).symm v)
      ((NormedSpace.fromTangentSpace x).symm w) = B v w := by
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using
    (const_apply B hB x ((NormedSpace.fromTangentSpace x).symm v)
      ((NormedSpace.fromTangentSpace x).symm w))


end SmoothTwoForm

end TauCeti

end
