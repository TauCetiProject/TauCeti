/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.HodgeStar
public import TauCeti.Geometry.Manifold.Orientation.OpenSubset
public import TauCeti.Geometry.Manifold.Riemannian.Restriction.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth

/-!
# Hodge star on open submanifolds

Restriction with the induced metric and orientation commutes with the Hodge star. This
identifies duality on forms on an open submanifold with ambient Hodge duality.
-/

public section

noncomputable section

open Bundle Manifold TopologicalSpace
open scoped ContDiff Manifold TauCeti

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The Hodge star commutes with restriction to an open submanifold with its induced
metric and orientation. -/
theorem hodgeStar_mpullback_subtypeVal {m k l : ℕ}
    (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m)
    (U : Opens M) (a : SmoothForm I M ℝ k) :
    hodgeStar (o.restrict U) hkl (mpullback (Subtype.val : U → M) contMDiff_subtypeVal a) =
      mpullback (Subtype.val : U → M) contMDiff_subtypeVal (hodgeStar o hkl a) := by
  apply Subtype.ext
  funext x
  let D := Manifold.tangentSpaceOpenEquiv (I := I) x
  have ho := (Manifold.Orientation.isOrientationPreservingAt_iff_of_coe_eq
    (o.restrict U) o (Subtype.val : U → M) x D (Manifold.mfderiv_subtype_val x).symm).1
      (o.isOrientationPreservingAt_restrict U x)
  let e := Manifold.tangentSpaceOpenLinearIsometryEquiv (I := I) U x
  have he : e.toLinearEquiv = D.toLinearEquiv := by
    ext v
    exact congrFun (Manifold.coe_tangentSpaceOpenLinearIsometryEquiv U x) v
  let := (o.restrict U).fact_finrank_tangentSpace x
  let := o.fact_finrank_tangentSpace (x : M)
  have hD : e.toLinearIsometry.toContinuousLinearMap = mfderiv I I (Subtype.val : U → M) x := by
    rw [Manifold.mfderiv_subtype_val]
    ext v
    exact congrFun (Manifold.coe_tangentSpaceOpenLinearIsometryEquiv U x) v
  simp only [coe_hodgeStar, coe_mpullback, RoughForm.hodgeStar_apply,
    TauCeti.mpullback_apply_eq_compContinuousLinearMapCLM,
    ContinuousAlternatingMap.compContinuousLinearMapCLM_apply, ← hD]
  have h := ((o.restrict U).orientationAt x).formHodgeStar_compContinuousLinearMap e
    (hkl.trans ((o.restrict U).fact_finrank_tangentSpace x).out.symm)
    (hkl.trans (o.fact_finrank_tangentSpace (x : M)).out.symm) (a.val x)
  rw [he, ho] at h
  exact h.symm

end TauCeti.SmoothForm
