/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Polar.Basic
public import TauCeti.Topology.IsLocalHomeomorph.CompactLifting
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition

/-!
# Lifting short curves through nonsingular exponential balls

A `C¹` curve starting at `p`, whose length is at most `r < R`, lifts through the Riemannian
exponential map into the tangent ball of radius `R` whenever its differential is injective
there. The lifted curve starts at zero and stays in the closed tangent ball of radius `r`.

The polar length inequality derives this compact confinement for every partial lift. The
exponential map need not be injective on the ball, and completeness is not assumed.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Theorem 1.36.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public section

open Bundle Function Manifold Set
open scoped ContDiff ENNReal Manifold Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [I.Boundaryless]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [T2Space M]

omit [I.Boundaryless] [T2Space M] in
/-- A continuous lift through a nonsingular exponential ball is `C¹` when its projection is. -/
private theorem contDiffOn_lift_riemannianExp {p : M} {R : ℝ}
    (hlocal : IsLocalDiffeomorphOn 𝓘(ℝ, TangentSpace I p) I 1
      (riemannianExp I M p) (Metric.ball 0 R))
    {c : ℝ → M} {a b : ℝ} (hc : ContMDiffOn 𝓘(ℝ, ℝ) I 1 c (Icc a b))
    {l : ℝ → TangentSpace I p} (hl : ContinuousOn l (Icc a b))
    (hp : EqOn (riemannianExp I M p ∘ l) c (Icc a b))
    (hm : MapsTo l (Icc a b) (Metric.ball 0 R)) : ContDiffOn ℝ 1 l (Icc a b) := by
  apply contMDiffOn_iff_contDiffOn.mp
  intro t ht
  exact ((hc.congr hp) t ht).of_comp_isLocalDiffeomorph (hlocal ⟨l t, hm ht⟩) (hl t ht)

/-- A `C¹` curve of length at most `r < R` starting at `p` has a `C¹` lift from zero through
the exponential map if its differential is injective on the tangent ball of radius `R`.
The lift stays in the closed ball of radius `r`; injectivity of the exponential map itself
is not required. -/
theorem exists_lift_riemannianExp_Icc {p : M} {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hinj : ∀ v ∈ Metric.ball (0 : TangentSpace I p) R,
      Injective (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v))
    {c : ℝ → M} {a b : ℝ} (hc : ContMDiffOn 𝓘(ℝ, ℝ) I 1 c (Icc a b)) (hc0 : c a = p)
    (hlen : Manifold.pathELength I c a b ≤ ENNReal.ofReal r) :
    ∃ l : ℝ → TangentSpace I p, ContDiffOn ℝ 1 l (Icc a b) ∧ l a = 0 ∧
      EqOn (riemannianExp I M p ∘ l) c (Icc a b) ∧
      MapsTo l (Icc a b) (Metric.closedBall 0 r) := by
  have hdom : Metric.ball (0 : TangentSpace I p) R ⊆ expDomain I M p :=
    fun v hv ↦ mem_expDomain_of_injective_mfderiv_riemannianExp (hinj v hv)
  have hlocal : IsLocalDiffeomorphOn 𝓘(ℝ, TangentSpace I p) I 1
      (riemannianExp I M p) (Metric.ball 0 R) := by
    intro v
    exact isLocalDiffeomorphAt_of_injective_mfderiv
      (((contMDiffOn_riemannianExp (I := I) p).of_le (by simp)).mono hdom)
      Metric.isOpen_ball v.property BoundarylessManifold.isInteriorPoint le_rfl
      (hinj v v.property)
      (tangentSpaceCastModel I p).toLinearEquiv.finrank_eq
  have hKU : Metric.closedBall (0 : TangentSpace I p) r ⊆ Metric.ball 0 R :=
    Metric.closedBall_subset_ball hrR
  have htrap : ∀ t ∈ Icc a b, ∀ l : ℝ → TangentSpace I p,
      ContinuousOn l (Icc a t) → l a = 0 →
      EqOn (riemannianExp I M p ∘ l) c (Icc a t) →
      MapsTo l (Icc a t) (Metric.ball 0 R) → l t ∈ Metric.closedBall 0 r := by
    intro t ht l hl h0 hp hm
    have hc' := hc.mono (Icc_subset_Icc le_rfl ht.2)
    have hl' := contDiffOn_lift_riemannianExp hlocal hc' hl hp hm
    have hpolar := ofReal_abs_norm_sub_norm_le_pathELength_riemannianExp ht.1 hl'
      (hm.mono_right hdom)
    rw [h0, norm_zero, sub_zero, abs_norm, Manifold.pathELength_congr hp] at hpolar
    exact mem_closedBall_zero_iff.mpr
      ((ENNReal.ofReal_le_ofReal_iff hr).mp
        (hpolar.trans ((Manifold.pathELength_mono le_rfl ht.2).trans hlen)))
  obtain ⟨l, hl, h0, hp, hm⟩ :=
    (hlocal.isLocalHomeomorphOn.mono hKU).exists_lift_Icc_of_isCompact (q := (0 : TangentSpace I p))
      Metric.isOpen_ball hc.continuousOn
      (by simpa using hr.trans_lt hrR) (by simpa using hc0.symm)
      (isCompact_closedBall (0 : TangentSpace I p) r) hKU htrap
  exact ⟨l, contDiffOn_lift_riemannianExp hlocal hc hl hp (hm.mono_right hKU), h0, hp, hm⟩

end TauCeti.Manifold
