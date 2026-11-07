/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.IntegralCurve.GlobalFlow
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
public import TauCeti.Geometry.Manifold.VectorField.Transverse

/-!
# The flow-out of a transverse hypersurface

Let `v` be a smooth complete vector field on a finite-dimensional boundaryless manifold `M`, with
flow `ψ`, and let `ι : S → M` be a smooth immersion of a boundaryless manifold of one dimension
less, to which `v` is transverse (`TauCeti.IsTransverseAlong`): `v (ι s)` does not lie in the
image of the differential of `ι` at `s`. The **flow-out** of `ι` is the map `Φ : ℝ × S → M`,
`Φ (t, s) = ψₜ (ι s)`. Its differential at `(t, s)` is

`dΦ (a, w) = dψₜ (a v (ι s) + dι w)`

(`TauCeti.mfderiv_globalFlow_comp_apply`), because the flow carries `v` to itself. Transversality
makes this injective, and since source and target have the same dimension, it is invertible. By
the inverse function theorem the flow-out is a local diffeomorphism
(`TauCeti.isLocalDiffeomorph_globalFlow_comp`).

This is the flow-out theorem in the form needed to identify the end of a Liouville completion with
the half-symplectization of its boundary: there `ι` is the inclusion of the boundary of a
Liouville domain, `v` is the Liouville field, and transversality is the outward-pointing condition.

## Main results

* `TauCeti.mfderiv_globalFlow_comp_apply`: the differential of the flow-out.
* `TauCeti.isLocalDiffeomorph_globalFlow_comp`: the flow-out of a transverse immersed hypersurface
  is a local diffeomorphism.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorem 9.20 (the flow-out theorem).
-/

public section

open Function Module Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [BoundarylessManifold I M] {v : (x : M) → TangentSpace I x}
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  (hc : IsCompleteVectorField v)
  {ι : S → M}

/-- **The differential of the flow-out.** For a complete `C¹` vector field `v` with flow `ψ` and
a map `ι : S → M` differentiable at `s`, the map `(t, s) ↦ ψₜ (ι s)` has differential
`(a, w) ↦ dψₜ (a v (ι s) + dι w)` at `(t, s)`. -/
theorem mfderiv_globalFlow_comp_apply [IsManifold I 1 M] (hv : ContMDiff I I.tangent 1 (T% v))
    (p : ℝ × S) (hι : MDifferentiableAt J I ι p.2) (a : ℝ) (w : TangentSpace J p.2) :
    mfderiv (𝓘(ℝ).prod J) I (fun p : ℝ × S ↦ globalFlow v hv hc p.1 (ι p.2))
        p ((Manifold.tangentSpaceProdEquiv p).symm (a, w)) =
      mfderiv I I (globalFlow v hv hc p.1) (ι p.2) (a • v (ι p.2) + mfderiv J I ι p.2 w) := by
  have hΦ : MDifferentiableAt (𝓘(ℝ).prod J) I
      (fun p : ℝ × S ↦ globalFlow v hv hc p.1 (ι p.2)) p :=
    ((contMDiff_globalFlow_uncurry hc le_rfl hv).mdifferentiableAt one_ne_zero).comp p
      (mdifferentiableAt_fst.prodMk (hι.comp p mdifferentiableAt_snd))
  rw [mfderiv_prod_eq_add_apply hΦ, map_add,
    ContinuousLinearMap.map_smul, mfderiv_globalFlow_apply_self hv hc,
    Manifold.tangentSpaceProdEquiv_symm_apply]
  dsimp only
  congr 1
  · -- The orbit of `ι s` has velocity `v`, so its differential sends `a` to `a • v`.
    rw [(isMIntegralCurve_globalFlow hv hc (ι p.2) p.1).mfderiv]
    -- `smulRight 1 v` sends `a` to `a • v`, reading `TangentSpace 𝓘(ℝ) t` as `ℝ`.
    rfl
  · exact mfderiv_comp_apply (I' := I) p.2
      ((contMDiff_globalFlow_apply hc le_rfl hv p.1).mdifferentiableAt one_ne_zero) hι w

variable [IsManifold I ∞ M] (hv : ContMDiff I I.tangent ∞ (T% v))
  [IsManifold J ∞ S] [BoundarylessManifold J S]

/-- **The flow-out theorem.** Let `v` be a smooth complete vector field on a finite-dimensional
boundaryless manifold `M`, with flow `ψ`, and let `ι : S → M` be a smooth immersion of a
boundaryless manifold of one dimension less, with `v` transverse to it: `v (ι s)` is never in the
image of `dι` at `s`. Then the flow-out `(t, s) ↦ ψₜ (ι s)` is a local diffeomorphism
`ℝ × S → M`. -/
theorem isLocalDiffeomorph_globalFlow_comp (hι : ContMDiff J I ∞ ι)
    (himm : ∀ s, Injective (mfderiv J I ι s))
    (htr : IsTransverseAlong J v ι)
    (hdim : finrank ℝ E = finrank ℝ E' + 1) :
    IsLocalDiffeomorph (𝓘(ℝ).prod J) I ∞
      (fun p : ℝ × S ↦ globalFlow v (hv.of_le (by simp)) hc p.1 (ι p.2)) := by
  set ψ := globalFlow v (hv.of_le (by simp)) hc
  have hΦ : ContMDiff (𝓘(ℝ).prod J) I ∞ (fun p : ℝ × S ↦ ψ p.1 (ι p.2)) :=
    (contMDiff_globalFlow_uncurry hc le_top hv).comp
      (contMDiff_fst.prodMk (hι.comp contMDiff_snd))
  rcases isEmpty_or_nonempty S with hS | ⟨⟨s₀⟩⟩
  · exact fun p ↦ isEmptyElim p.2
  -- The tangent space of `S` embeds in that of `M`, so it is finite-dimensional.
  have : FiniteDimensional ℝ E' := by
    have : FiniteDimensional ℝ (TangentSpace I (ι s₀)) := inferInstanceAs (FiniteDimensional ℝ E)
    exact FiniteDimensional.of_injective (mfderiv J I ι s₀).toLinearMap (himm s₀)
  refine isLocalDiffeomorph_of_mfderiv_eq hΦ (by simp) fun p ↦ ?_
  set L := mfderiv (𝓘(ℝ).prod J) I (fun p : ℝ × S ↦ ψ p.1 (ι p.2)) p
  -- The differential `dψₜ` is injective, since `ψₜ` is a diffeomorphism.
  have hψinj : Injective (mfderiv I I (ψ p.1) (ι p.2)) := by
    obtain ⟨e, he⟩ := (globalFlowDiffeomorph hc le_top hv p.1).isInvertible_mfderiv
      (x := ι p.2) (by simp)
    rw [coe_globalFlowDiffeomorph] at he
    exact he ▸ e.injective
  -- Transversality makes the differential of the flow-out injective.
  have hinj : Injective L := by
    refine (injective_iff_map_eq_zero L).2 fun x hx ↦ ?_
    obtain ⟨a, w⟩ := x
    have hL := mfderiv_globalFlow_comp_apply hc (hv.of_le (by simp)) p
      (hι.mdifferentiableAt (by simp)) a w
    rw [Manifold.tangentSpaceProdEquiv_symm_apply] at hL
    have h0 : a • v (ι p.2) + mfderiv J I ι p.2 w = 0 :=
      hψinj (hL.symm.trans (hx.trans (map_zero _).symm))
    obtain rfl : a = 0 := by
      by_contra ha
      refine isTransverseAlong_iff.1 htr p.2 (LinearMap.mem_range.2
        ⟨-a⁻¹ • w, ((mfderiv J I ι p.2).map_smul _ _).trans ?_⟩)
      rw [eq_neg_of_add_eq_zero_right h0, smul_neg, smul_smul, neg_mul, inv_mul_cancel₀ ha,
        neg_smul, one_smul, neg_neg]
    rw [zero_smul, zero_add] at h0
    exact Prod.ext rfl ((himm p.2) (h0.trans (map_zero _).symm))
  -- Source and target have the same dimension, so the differential is invertible.
  have hfin : finrank ℝ (TangentSpace (𝓘(ℝ).prod J) p) =
      finrank ℝ (TangentSpace I (ψ p.1 (ι p.2))) := by
    -- Both tangent spaces are their model vector spaces, `ℝ × E'` and `E`.
    change finrank ℝ (ℝ × E') = finrank ℝ E
    rw [Module.finrank_prod, finrank_self, hdim, add_comm]
  have hsurj : Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin (f := L.toLinearMap)).1 hinj
  exact ⟨(LinearEquiv.ofBijective L.toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv, rfl⟩

end TauCeti
