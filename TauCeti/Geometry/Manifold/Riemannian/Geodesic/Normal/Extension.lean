/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Basic
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Coordinates
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Distortion
import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact

/-!
# Global vector fields parallel at a point

On a boundaryless Riemannian manifold, every tangent vector `v ∈ T_p M` is the value at `p` of a
smooth vector field `X` on all of `M` whose Levi-Civita covariant derivative vanishes at `p`
(`TauCeti.Manifold.exists_contMDiff_apply_eq_and_leviCivitaConnection_eq_zero`).

The normal coordinate field of `v` on a normal neighbourhood of `p` has these properties near `p`
(`TauCeti.Manifold.IsNormalDomain.leviCivitaConnection_normalCoordinateField_self`). Multiplying
it by a smooth cutoff equal to `1` near `p` and supported in the normal neighbourhood gives a
global smooth field, and the covariant derivative at `p` only depends on the germ there.

Such fields are the test sections of the maximum principle for tensors: at a point `p` they turn
`Δ ⟪A X, X⟫ (p)` into an expression in `∇*∇ A` alone, since all first-order terms vanish.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 5
  (normal coordinates and geodesic frames).
-/

public section

open Bundle CovariantDerivative Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [I.Boundaryless]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- **A global vector field parallel at a point.** On a boundaryless Riemannian manifold, every
tangent vector `v ∈ T_p M` extends to a smooth vector field `X` on `M` with `X p = v` and
`∇X (p) = 0` for the Levi-Civita connection. -/
theorem exists_contMDiff_apply_eq_and_leviCivitaConnection_eq_zero (p : M)
    (v : TangentSpace I p) :
    ∃ X : Π q : M, TangentSpace I q, CMDiff ∞ (T% X) ∧ X p = v ∧
      leviCivitaConnection I M X p = 0 := by
  obtain ⟨r, -, hN, -⟩ := exists_isNormalDomain_ball_norm_mfderiv_bounds (I := I) (M := M) p
    one_lt_two
  set O := riemannianExp I M p '' Metric.ball 0 r
  set N := normalCoordinateField I M p (Metric.ball 0 r) v
  -- A cutoff equal to `1` near `p` and supported in the normal neighbourhood `O`.
  obtain ⟨ψ, hψ, hψ1, -, hψO, -⟩ :=
    isCompact_singleton.exists_contMDiff_one_nhds_tsupport_subset I hN.isOpen_image
      (singleton_subset_iff.2 hN.self_mem_image)
  rw [nhdsSet_singleton] at hψ1
  have hNO := hN.contMDiffOn_normalCoordinateField v
  have hNp : MDiffAt (T% N) p := hN.mdifferentiableAt_normalCoordinateField v hN.self_mem_image
  have hX : CMDiff ∞ (T% (ψ • N)) := by
    intro q
    by_cases hq : q ∈ O
    · exact (hψ q).smul_section (hNO.contMDiffAt (hN.isOpen_image.mem_nhds hq))
    · have hz : ψ =ᶠ[𝓝 q] 0 := notMem_tsupport_iff_eventuallyEq.1 fun h ↦ hq (hψO h)
      exact (contMDiffAt_zeroSection (𝕜 := ℝ) (IB := I) (n := ∞) (F := E)
        (E := TangentSpace I)).congr_of_eventuallyEq
        (hz.mono fun y hy ↦ by simp [hy, zeroSection])
  refine ⟨ψ • N, hX, ?_, ?_⟩
  · simp [N, hψ1.self_of_nhds, hN.normalCoordinateField_self]
  · -- Near `p` the field is the normal coordinate field, which is parallel at `p`.
    rw [(leviCivitaConnection I M).isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      ((hX p).mdifferentiableAt (by simp)) hNp Filter.univ_mem
      (hψ1.mono fun y hy ↦ by simp [hy])]
    exact hN.leviCivitaConnection_normalCoordinateField_self v

end TauCeti.Manifold
