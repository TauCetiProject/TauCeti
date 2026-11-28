/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Invariant
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Ext

/-!
# The identity principle for smooth actions of compact groups

Let a compact group `G`, itself a manifold, act smoothly on a connected Hausdorff σ-compact
manifold `M` without boundary. If an element `g` acts as the identity on a neighbourhood of a single
point of `M`, then it acts as the identity on all of `M`
(`TauCeti.smul_eq_self_of_eventuallyEq_id`). In particular, if the action is effective, then the
only element acting as the identity near some point is `1`
(`TauCeti.eq_one_of_eventuallyEq_id`).

The proof chooses a smooth Riemannian metric on `M` preserved by `G`, the Haar average of an
arbitrary one (`TauCeti.of_forall_riemannianBundle_inner_mfderiv`). Then `x ↦ g • x` is
a Riemannian isometry with the same value and differential as the identity at the given point, and
an isometry of a connected manifold is determined by these first-order data
(`TauCeti.RiemannianIsometry.ext_of_mfderiv_eq`).

For an element of finite order the same conclusion holds without compactness of the group, by
Bochner linearization (`TauCeti.subset_interior_fixedBy_of_isPreconnected`).

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Proposition 5.22.
-/

public section

open Filter Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M] [PreconnectedSpace M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] (J : ModelWithCorners ℝ E' H')
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [ChartedSpace H' G] [IsManifold J ∞ G] [MulAction G M] [ContMDiffSMul J I ∞ G M]

include I J in
/-- **The identity principle for compact group actions.** If an element of a compact group acting
smoothly on a connected manifold acts as the identity near one point, it acts as the identity
everywhere. -/
theorem smul_eq_self_of_eventuallyEq_id (g : G) {p : M}
    (hg : (fun x : M ↦ g • x) =ᶠ[𝓝 p] id) (x : M) : g • x = x := by
  refine of_forall_riemannianBundle_inner_mfderiv (I := I) (M := M) J G fun hinv ↦ ?_
  -- With an invariant metric, `g` acts by a Riemannian isometry.
  let Φ : RiemannianIsometry I I M M :=
    { toEquiv := MulAction.toPerm g
      contMDiff_toFun := ContMDiffSMul.contMDiff_const_smul (I := J) g
      contMDiff_invFun := ContMDiffSMul.contMDiff_const_smul (I := J) g⁻¹
      inner_mfderiv' := hinv g }
  have hΦ : (Φ : M → M) = fun x ↦ g • x := rfl
  have hid : (RiemannianIsometry.refl I M : M → M) = id :=
    funext (RiemannianIsometry.refl_apply I M)
  have hΦp : Φ p = RiemannianIsometry.refl I M p := by
    simpa [hΦ] using hg.eq_of_nhds
  have hd : mfderiv I I Φ p = mfderiv I I (RiemannianIsometry.refl I M) p := by
    rw [hΦ, hid]
    -- Mathlib's congruence theorem inserts `tangentSpaceCast`, whose underlying function is the
    -- identity; the endpoints agree by `hg.eq_of_nhds`.
    ext v
    exact DFunLike.congr_fun (hg.mfderiv_eq (I := I) (I' := I)) v
  simpa [hΦ] using congrArg (· x) (DFunLike.coe_fn_eq.2 (Φ.ext_of_mfderiv_eq _ hΦp hd))

include I J in
/-- **Effective compact group actions are effective near every point.** If a compact group acts
smoothly and effectively on a connected manifold, the only element acting as the identity near a
point is `1`. -/
theorem eq_one_of_eventuallyEq_id [FaithfulSMul G M] {g : G} {p : M}
    (hg : (fun x : M ↦ g • x) =ᶠ[𝓝 p] id) : g = 1 :=
  eq_of_smul_eq_smul fun x ↦ by rw [smul_eq_self_of_eventuallyEq_id I J g hg x, one_smul]

end TauCeti
