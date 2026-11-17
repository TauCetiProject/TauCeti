/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Killing.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.LieDeriv
import TauCeti.Geometry.Manifold.Riemannian.Pullback.LieDeriv

/-!
# Characterization of Killing vector fields via the tensor Lie derivative

Shows that a vector field `X` on a Riemannian manifold is a Killing field (`IsKillingField I X`)
if and only if it is smooth and the bilinear Lie derivative `TauCeti.mlieDerivBilin` of the
Riemannian metric `RiemannianBundle.g.inner` along `X` vanishes.

## Main results

* `TauCeti.Manifold.isKillingField_iff_mlieDerivBilin_eq_zero`: `IsKillingField I X ↔
  CMDiff ∞ (T% X) ∧ mlieDerivBilin I X RiemannianBundle.g.inner = 0`.
* `TauCeti.Manifold.IsKillingField.mlieDerivBilin_inner_eq_zero`: for a Killing field `X`,
  `mlieDerivBilin I X RiemannianBundle.g.inner = 0`.

## References

* P. Petersen, *Riemannian Geometry*, 3rd ed., Springer GTM 171 (2016), Chapter 8.
-/

public section

noncomputable section

open Bundle CovariantDerivative
open scoped ContDiff Manifold

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {X : (x : M) → TangentSpace I x}

/-- **Characterization of Killing fields via `mlieDerivBilin`:** a vector field `X` is Killing
if and only if it is smooth and `L_X g = 0`. -/
theorem isKillingField_iff_mlieDerivBilin_eq_zero :
    IsKillingField I X ↔ CMDiff ∞ (T% X) ∧ mlieDerivBilin I X RiemannianBundle.g.inner = 0 := by
  let _ : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  rw [(CovariantDerivative.isMetricCompatible_leviCivitaConnection I).isKillingField_iff
    (CovariantDerivative.torsion_leviCivitaConnection_eq_zero I)]
  refine and_congr_right fun hX ↦ ⟨fun h ↦ ?_, fun h x u v ↦ ?_⟩
  · funext x; ext u v
    rw [Pi.zero_apply, zero_apply, zero_apply,
      mlieDerivBilin_inner_eq_leviCivitaConnection (hX.mdifferentiable (by simp) x), h x u v,
      neg_add_cancel]
  · have h0 : mlieDerivBilin I X RiemannianBundle.g.inner x u v = 0 := by simp [h]
    rw [mlieDerivBilin_inner_eq_leviCivitaConnection (hX.mdifferentiable (by simp) x)] at h0
    exact eq_neg_of_add_eq_zero_left h0

/-- The Lie derivative of the Riemannian metric along a Killing field vanishes. -/
theorem IsKillingField.mlieDerivBilin_inner_eq_zero (h : IsKillingField I X) :
    mlieDerivBilin I X RiemannianBundle.g.inner = 0 :=
  (isKillingField_iff_mlieDerivBilin_eq_zero.1 h).2

end TauCeti.Manifold
