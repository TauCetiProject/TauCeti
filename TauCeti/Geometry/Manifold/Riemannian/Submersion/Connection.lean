/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Submersion.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Adjoint
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Basic
public import TauCeti.Geometry.Manifold.VectorField.Related
import TauCeti.Geometry.Manifold.IsManifold.Basic

/-!
# Horizontal Levi-Civita differentiation under a Riemannian submersion

Horizontal lifts of vector fields on the base preserve their regularity and inner products, and
every horizontal tangent vector extends locally to a `C^n` basic horizontal lift on an open
neighbourhood without assuming `[T2Space N]` (`exists_contMDiffOn_horizontalLift`).
Their brackets project to the brackets on the base, although those brackets need not themselves
be horizontal. The Koszul formula then identifies the horizontal component of their covariant
derivative with the lift of the base covariant derivative. This is the connection comparison
used in the fundamental curvature equations for a Riemannian submersion.

The connections may be any connections satisfying the native Levi-Civita predicate. No global
surjectivity, completeness or connectedness is needed. All differentiation identities are local
at the specified source point.

## References

* B. O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. 13 (1966),
  459–469, Lemma 1.
* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 2.

The construction uses the native metric-adjoint horizontal lift, the naturality theorem for
related vector fields, and Mathlib's Koszul characterization of Levi-Civita connections.
-/

public section

open Bundle Manifold VectorField
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.IsRiemannianSubmersion

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  {f : M → N} (h : IsRiemannianSubmersion I J f)

section Regularity

section ContMDiff

variable [IsManifold I 1 M] [IsManifold J 1 N]
  {n : ℕ∞ω} [IsManifold I (n + 1) M]
  [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle J n F (fun y : N ↦ TangentSpace J y)]

/-- Horizontal lifting of a base vector field preserves `C^n` regularity at a point, for
`C^n` metrics and `n + 1 ≤ ∞`. -/
theorem contMDiffAt_horizontalLift {X : Π y : N, TangentSpace J y} {x : M}
    (hX : ContMDiffAt J (J.prod 𝓘(ℝ, F)) n (T% X) (f x)) (hn : n + 1 ≤ ∞) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) n
      (T% (fun y ↦ h.horizontalLift y (X (f y)))) x := by
  have hf := (h.isSubmersion.contMDiff.of_le hn) x
  simpa only [h.horizontalLift_apply, Function.comp_def] using
    hf.mfderiv_adjoint_apply (hX.comp x (hf.of_le le_self_add))

/-- Horizontal lifting of a `C^n` base vector field is `C^n`, for `C^n` metrics and
`n + 1 ≤ ∞`. -/
theorem contMDiff_horizontalLift {X : Π y : N, TangentSpace J y}
    (hX : ContMDiff J (J.prod 𝓘(ℝ, F)) n (T% X)) (hn : n + 1 ≤ ∞) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) n
      (T% (fun y ↦ h.horizontalLift y (X (f y)))) :=
  fun x ↦ h.contMDiffAt_horizontalLift (hX (f x)) hn

variable (n) in
/-- Extend a horizontal tangent vector at `x` locally to a basic horizontal lift that is `C^n` on
an open neighbourhood of `x`, for `C^n` metrics and `n + 1 ≤ ∞`, without assuming `[T2Space N]`. -/
theorem exists_contMDiffOn_horizontalLift [IsManifold J (n + 1) N] {x : M}
    {u : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).kerᗮ) (hn : n + 1 ≤ ∞) :
    ∃ (W : Set N) (B : Π z : N, TangentSpace J z),
      IsOpen W ∧ f x ∈ W ∧ CMDiff[W] n (T% B) ∧
      CMDiff[f ⁻¹' W] n (T% (fun y ↦ h.horizontalLift y (B (f y)))) ∧
      h.horizontalLift x (B (f x)) = u := by
  let := TangentBundle.contMDiffVectorBundle (I := J) (M := N) (n := n)
  obtain ⟨s, hs, hBs⟩ := FiberBundle.exists_contMDiffOn_extend (k := n) J F (mfderiv I J f x u)
  refine ⟨interior s, FiberBundle.extend F (mfderiv I J f x u), isOpen_interior,
    mem_interior_iff_mem_nhds.2 hs, hBs.mono interior_subset, fun y hy ↦ ?_, ?_⟩
  · exact (h.contMDiffAt_horizontalLift
      ((hBs.mono interior_subset).contMDiffAt (isOpen_interior.mem_nhds hy))
      hn).contMDiffWithinAt
  · simp [FiberBundle.extend_apply_self, h.horizontalLift_mfderiv_of_mem x hu]

end ContMDiff

/-- Horizontal lifting of a base vector field that is `C^1` at `f x` is differentiable at `x`. -/
theorem mdifferentiableAt_horizontalLift [IsManifold I 2 M] [IsManifold J 1 N]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle J 1 F (fun y : N ↦ TangentSpace J y)]
    {Y : Π y : N, TangentSpace J y} {x : M}
    (hY : CMDiffAt 1 (T% Y) (f x)) :
    MDiffAt (T% (fun y ↦ h.horizontalLift y (Y (f y)))) x := by
  let : IsManifold I ((1 : ℕ∞ω) + 1) M := by
    simpa only [one_add_one_eq_two] using (inferInstance : IsManifold I 2 M)
  exact (h.contMDiffAt_horizontalLift hY (by norm_num)).mdifferentiableAt one_ne_zero

end Regularity

section Connection

variable [IsManifold I 2 M] [IsManifold J 2 N]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle J 1 F (fun y : N ↦ TangentSpace J y)]
  {X Y Z : Π y : N, TangentSpace J y} {x : M}

attribute [local instance] IsManifold.minSmoothness_of_isRCLikeNormedField

/-- The bracket of horizontal lifts projects to the base bracket. Its vertical component is
not asserted to vanish. -/
theorem mfderiv_mlieBracket_horizontalLift
    (hX : CMDiffAt 1 (T% X) (f x)) (hY : CMDiffAt 1 (T% Y) (f x)) :
    mfderiv I J f x
        (mlieBracket I (fun y ↦ h.horizontalLift y (X (f y)))
          (fun y ↦ h.horizontalLift y (Y (f y))) x) =
      mlieBracket J X Y (f x) := by
  exact TauCeti.mfderiv_mlieBracket_of_eventually_related
    (h.isSubmersion.contMDiff x) (by simp)
    (h.mdifferentiableAt_horizontalLift hX)
    (h.mdifferentiableAt_horizontalLift hY)
    (hX.mdifferentiableAt one_ne_zero) (hY.mdifferentiableAt one_ne_zero)
    (Filter.Eventually.of_forall fun y ↦ h.mfderiv_horizontalLift y _)
    (Filter.Eventually.of_forall fun y ↦ h.mfderiv_horizontalLift y _)

omit [IsManifold I 2 M]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] in
private theorem mvfderiv_inner_horizontalLift
    (hY : CMDiffAt 1 (T% Y) (f x)) (hZ : CMDiffAt 1 (T% Z) (f x))
    (v : TangentSpace J (f x)) :
    mvfderiv I (fun y ↦ inner ℝ (h.horizontalLift y (Y (f y)))
        (h.horizontalLift y (Z (f y)))) x (h.horizontalLift x v) =
      mvfderiv J (fun y ↦ inner ℝ (Y y) (Z y)) (f x) v := by
  have heq : (fun y ↦ inner ℝ (h.horizontalLift y (Y (f y)))
      (h.horizontalLift y (Z (f y)))) = (fun y ↦ inner ℝ (Y y) (Z y)) ∘ f := by
    ext y
    exact (h.horizontalLift y).inner_map_map _ _
  rw [heq, mvfderiv_comp_apply x
    (TauCeti.Manifold.mdifferentiableAt_inner
      (hY.mdifferentiableAt one_ne_zero) (hZ.mdifferentiableAt one_ne_zero))
    (h.isSubmersion.contMDiff.mdifferentiableAt (by simp)), h.mfderiv_horizontalLift]

/-- The Koszul expression on horizontal lifts is the pullback of the base Koszul expression.
Only the projection, not horizontality, of their brackets is used. -/
theorem koszul_horizontalLift
    (hX : CMDiffAt 1 (T% X) (f x)) (hY : CMDiffAt 1 (T% Y) (f x))
    (hZ : CMDiffAt 1 (T% Z) (f x)) :
    TauCeti.Manifold.koszul I (fun y ↦ h.horizontalLift y (X (f y)))
        (fun y ↦ h.horizontalLift y (Y (f y)))
        (fun y ↦ h.horizontalLift y (Z (f y))) x =
      TauCeti.Manifold.koszul J X Y Z (f x) := by
  rw [TauCeti.Manifold.koszul_apply, TauCeti.Manifold.koszul_apply,
    h.mvfderiv_inner_horizontalLift hY hZ, h.mvfderiv_inner_horizontalLift hZ hX,
    h.mvfderiv_inner_horizontalLift hX hY]
  rw [h.inner_horizontalLift_right, h.inner_horizontalLift_right, h.inner_horizontalLift_right,
    h.mfderiv_mlieBracket_horizontalLift hX hY,
    h.mfderiv_mlieBracket_horizontalLift hX hZ, h.mfderiv_mlieBracket_horizontalLift hY hZ]

variable {covM : CovariantDerivative I E (TangentSpace I : M → Type _)}
  {covN : CovariantDerivative J F (TangentSpace J : N → Type _)}

/-- Horizontal lifts intertwine Levi-Civita differentiation after projecting to the base. -/
theorem mfderiv_covariantDerivative_horizontalLift
    (hM : covM.IsLeviCivitaConnection) (hN : covN.IsLeviCivitaConnection)
    (hY : CMDiffAt 1 (T% Y) (f x)) (v : TangentSpace J (f x)) :
    mfderiv I J f x
        (covM (fun y ↦ h.horizontalLift y (Y (f y))) x (h.horizontalLift x v)) =
      covN Y (f x) v := by
  apply ext_inner_right ℝ
  intro w
  have hZ : CMDiffAt 1 (T% (FiberBundle.extend F w)) (f x) := FiberBundle.contMDiffAt_extend ..
  have hX : CMDiffAt 1 (T% (FiberBundle.extend F v)) (f x) := FiberBundle.contMDiffAt_extend ..
  have hk := h.koszul_horizontalLift hX hY hZ
  rw [← hM.two_inner_eq_koszul (h.mdifferentiableAt_horizontalLift hX)
      (h.mdifferentiableAt_horizontalLift hY) (h.mdifferentiableAt_horizontalLift hZ),
    ← hN.two_inner_eq_koszul (hX.mdifferentiableAt one_ne_zero)
      (hY.mdifferentiableAt one_ne_zero) (hZ.mdifferentiableAt one_ne_zero)] at hk
  simp only [h.inner_horizontalLift_right, FiberBundle.extend_apply_self] at hk ⊢
  linarith

/-- The horizontal component of the total-space covariant derivative of basic horizontal
fields is the horizontal lift of the base covariant derivative. -/
theorem starProjection_covariantDerivative_horizontalLift
    (hM : covM.IsLeviCivitaConnection) (hN : covN.IsLeviCivitaConnection)
    (hY : CMDiffAt 1 (T% Y) (f x)) (v : TangentSpace J (f x)) :
    (mfderiv I J f x).kerᗮ.starProjection
        (covM (fun y ↦ h.horizontalLift y (Y (f y))) x (h.horizontalLift x v)) =
      h.horizontalLift x (covN Y (f x) v) := by
  rw [← h.horizontalLift_mfderiv, h.mfderiv_covariantDerivative_horizontalLift hM hN hY]

end Connection

end TauCeti.IsRiemannianSubmersion
