/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Basic
import TauCeti.Analysis.Calculus.LocalExtr.Max
import TauCeti.Topology.OpenPartialHomeomorph.Collision
import TauCeti.Topology.MetricSpace.Collision
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# First collisions of the Riemannian exponential map

At a least collision in a nonsingular closed tangent ball, the two initial vectors have the
same positive length and the terminal radial velocities are opposite. The inverse branches
come from the inverse function theorem, and the native Gauss lemma computes their radius
derivatives. This is the local Klingenberg argument; no completeness assumption is required.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Theorem 1.36.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public section

open Bundle Filter Function Manifold Metric Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {p : M} {v w : TangentSpace I p}

/-- In the extended chart at the endpoint, the derivative of half the squared radius of a local
inverse exponential branch at the endpoint's chart image is the metric dual of its terminal
radial velocity. -/
theorem _root_.IsLocalDiffeomorphAt.hasFDerivAt_half_sq_norm_localInverse_riemannianExp
    (h : IsLocalDiffeomorphAt 𝓘(ℝ, TangentSpace I p) I 1 (riemannianExp I M p) v) :
    HasFDerivAt
      (fun y : E ↦ ‖h.localInverse ((extChartAt I (riemannianExp I M p v)).symm y)‖ ^ 2 / 2)
      ((RiemannianBundle.g (E := fun x : M ↦ TangentSpace I x)).inner (riemannianExp I M p v)
        (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v v))
      (extChartAt I (riemannianExp I M p v) (riemannianExp I M p v)) := by
  have hv := mem_expDomain_of_injective_mfderiv_riemannianExp
    (h.isInvertible_mfderiv (by simp)).injective
  let q := riemannianExp I M p v
  let c := extChartAt I q
  have hcq : c.symm (c q) = q := c.left_inv (mem_extChartAt_source q)
  have hi : HasFDerivAt (h.localInverse ∘ c.symm)
      (mfderiv I 𝓘(ℝ, TangentSpace I p) h.localInverse q) (c q) := by
    simpa only [writtenInExtChartAt, ModelWithCorners.range_eq_univ,
      hasFDerivWithinAt_univ, c, q] using!
      (h.mdifferentiableAt_localInverse (by simp)).hasMFDerivAt.2
  have hs := hi.norm_sq.const_smul (1 / 2 : ℝ)
  have heq (y : E) : ‖h.localInverse (c.symm y)‖ ^ 2 / 2 =
      ((1 / 2 : ℝ) • (fun y : E ↦ ‖(h.localInverse ∘ c.symm) y‖ ^ 2)) y := by
    simp only [Pi.smul_apply, smul_eq_mul, Function.comp_apply]
    ring
  have hs' := hs.congr_of_eventuallyEq (.of_forall heq)
  apply hs'.congr_fderiv
  ext u
  have hback : mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v
      (mfderiv I 𝓘(ℝ, TangentSpace I p) h.localInverse q u) = u := by
    -- This equivalence is defined with the differential of the canonical inverse as its inverse.
    exact (h.mfderivToContinuousLinearEquiv (by simp)).apply_symm_apply u
  have hg := inner_mfderiv_riemannianExp_radial (I := I) (M := M) (v := v) hv
    (w := mfderiv I 𝓘(ℝ, TangentSpace I p) h.localInverse q u)
  rw [hback] at hg
  simp only [smul_apply, two_smul, add_apply, smul_eq_mul, Function.comp_apply, hcq]
  ring_nf
  -- The bundle instance defines the tangent-space inner product by the native metric;
  -- no rewrite lemma for this instance projection is available.
  change inner ℝ (h.localInverse q)
    (mfderiv I 𝓘(ℝ, TangentSpace I p) h.localInverse q u) = _
  have hiv : h.localInverse q = v := h.localInverse_left_inv h.localInverse_mem_target
  rw [hiv]
  exact hg.symm

omit [T2Space M] in
/-- At a least collision, the half squared radii of the two local inverse exponential
branches have a local minimum of their maximum in endpoint coordinates. -/
private theorem isLocalMin_max_half_sq_norm_inverse_riemannianExp
    {r : ℝ} (hv : ‖v‖ ≤ r) (hw : ‖w‖ ≤ r)
    (heq : riemannianExp I M p v = riemannianExp I M p w) (hne : v ≠ w)
    (hvlocal : IsLocalDiffeomorphAt 𝓘(ℝ, TangentSpace I p) I 1 (riemannianExp I M p) v)
    (hwlocal : IsLocalDiffeomorphAt 𝓘(ℝ, TangentSpace I p) I 1 (riemannianExp I M p) w)
    (hmin : ∀ x ∈ closedBall 0 r, ∀ y ∈ closedBall 0 r,
      riemannianExp I M p x = riemannianExp I M p y → x ≠ y →
      max ‖v‖ ‖w‖ ≤ max ‖x‖ ‖y‖) :
    ‖v‖ = ‖w‖ ∧ IsLocalMin
      (fun y : E ↦ max
        (‖hvlocal.localInverse ((extChartAt I (riemannianExp I M p v)).symm y)‖ ^ 2 / 2)
        (‖hwlocal.localInverse ((extChartAt I (riemannianExp I M p v)).symm y)‖ ^ 2 / 2))
      (extChartAt I (riemannianExp I M p v) (riemannianExp I M p v)) := by
  have hbranch (x : TangentSpace I p)
      (h : IsLocalDiffeomorphAt 𝓘(ℝ, TangentSpace I p) I 1 (riemannianExp I M p) x) :
      EqOn (riemannianExp I M p) h.localInverse.toOpenPartialHomeomorph.symm
        h.localInverse.target := by
    intro z hz
    have hback := h.localInverse_right_inv
      (h.localInverse.toOpenPartialHomeomorph.symm.map_source hz)
    simpa only [← PartialDiffeomorph.toFun'_toOpenPartialHomeomorph,
      h.localInverse.toOpenPartialHomeomorph.right_inv hz] using hback
  let ev := hvlocal.localInverse.toOpenPartialHomeomorph.symm
  let ew := hwlocal.localInverse.toOpenPartialHomeomorph.symm
  have hvs : v ∈ ev.source := hvlocal.localInverse_mem_target
  have hws : w ∈ ew.source := hwlocal.localInverse_mem_target
  have hev : EqOn (riemannianExp I M p) ev ev.source := hbranch v hvlocal
  have hew : EqOn (riemannianExp I M p) ew ew.source := hbranch w hwlocal
  have hnorm := norm_eq_of_minimal_collision hv hw heq hne ev ew hvs hws hev hew hmin
  let q := riemannianExp I M p v
  have hm : IsLocalMin (fun z ↦ max ‖hvlocal.localInverse z‖ ‖hwlocal.localInverse z‖) q := by
    simpa only [ev, ew, OpenPartialHomeomorph.symm_symm,
      PartialDiffeomorph.toFun'_toOpenPartialHomeomorph] using
      isLocalMin_max_inverse_norm_of_minimal_collision hv hw heq hne ev ew hvs hws hev hew hmin
  let c := extChartAt I q
  have hcq : c.symm (c q) = q := c.left_inv (mem_extChartAt_source q)
  have hc : Tendsto c.symm (𝓝 (c q)) (𝓝 q) := by
    rw [Filter.Tendsto]
    simpa only [ModelWithCorners.range_eq_univ, nhdsWithin_univ] using
      (map_extChartAt_symm_nhdsWithin_range (I := I) q).le
  refine ⟨hnorm, ?_⟩
  suffices hchart : IsLocalMin (fun y : E ↦ max
      (‖hvlocal.localInverse (c.symm y)‖ ^ 2 / 2)
      (‖hwlocal.localInverse (c.symm y)‖ ^ 2 / 2)) (c q) by
    simpa only [c, q] using hchart
  simp only [IsLocalMin, IsMinFilter]
  have hiv : hvlocal.localInverse q = v :=
    hvlocal.localInverse_left_inv hvlocal.localInverse_mem_target
  have hiw : hwlocal.localInverse q = w := by
    simpa only [q, heq] using hwlocal.localInverse_left_inv hwlocal.localInverse_mem_target
  simp only [hcq, hiv, hiw, hnorm, max_self]
  simp only [IsLocalMin, IsMinFilter, hiv, hiw, hnorm, max_self] at hm
  filter_upwards [hc hm] with y hy
  rcases le_max_iff.mp hy with hy | hy
  · exact (div_le_div_of_nonneg_right
      ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hy) (by norm_num : (0 : ℝ) ≤ 2)).trans
      (le_max_left _ _)
  · exact (div_le_div_of_nonneg_right
      ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hy) (by norm_num : (0 : ℝ) ≤ 2)).trans
      (le_max_right _ _)

/-- **Klingenberg's return-direction lemma.** At a least collision of the exponential map,
if both vectors are nonsingular, their lengths agree and
their terminal radial velocities are opposite. -/
theorem norm_eq_and_mfderiv_eq_neg_of_minimal_riemannianExp_collision
    {r : ℝ} (hv : ‖v‖ ≤ r) (hw : ‖w‖ ≤ r)
    (heq : riemannianExp I M p v = riemannianExp I M p w) (hne : v ≠ w)
    (hvlocal : IsLocalDiffeomorphAt 𝓘(ℝ, TangentSpace I p) I 1 (riemannianExp I M p) v)
    (hwlocal : IsLocalDiffeomorphAt 𝓘(ℝ, TangentSpace I p) I 1 (riemannianExp I M p) w)
    (hmin : ∀ x ∈ closedBall 0 r, ∀ y ∈ closedBall 0 r,
      riemannianExp I M p x = riemannianExp I M p y → x ≠ y →
      max ‖v‖ ‖w‖ ≤ max ‖x‖ ‖y‖) :
    ‖v‖ = ‖w‖ ∧
      (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v v : E) =
        -(mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) w w : E) := by
  obtain ⟨hnorm, hm⟩ := isLocalMin_max_half_sq_norm_inverse_riemannianExp
    hv hw heq hne hvlocal hwlocal hmin
  have hvd := mem_expDomain_of_injective_mfderiv_riemannianExp
    (hvlocal.isInvertible_mfderiv (by simp)).injective
  have hwd := mem_expDomain_of_injective_mfderiv_riemannianExp
    (hwlocal.isInvertible_mfderiv (by simp)).injective
  have hdv := hvlocal.hasFDerivAt_half_sq_norm_localInverse_riemannianExp
  have hdw := hwlocal.hasFDerivAt_half_sq_norm_localInverse_riemannianExp
  rw [← heq] at hdw
  let g := RiemannianBundle.g (E := fun x : M ↦ TangentSpace I x)
  refine ⟨hnorm, hm.eq_neg_of_max_hasFDerivAt_bilin
    (g.inner (riemannianExp I M p v)).toLinearMap
    (fun a b ↦ g.symm _ a b) (fun a ha ↦ g.pos _ a ha) hdv hdw ?_⟩
  have hgv := inner_mfderiv_riemannianExp_radial hvd (w := v)
  have hgw := inner_mfderiv_riemannianExp_radial hwd (w := w)
  rw [← heq] at hgw
  -- Gauss uses the tangent inner product installed by the bundle metric. This projection
  -- has no rewrite lemma, so expose it to compare the two metric self-pairings.
  change inner ℝ _ _ = _ at hgv hgw
  have hequal : inner ℝ v v = inner ℝ w w := by
    simp only [real_inner_self_eq_norm_sq, hnorm]
  exact hgv.trans (hequal.trans hgw.symm)

/-- **An attained Klingenberg first collision.** If the exponential map is
nonsingular on a closed tangent ball but is not injective there, it has a least positive
collision. The colliding vectors have equal norms and opposite terminal radial velocities. -/
theorem exists_norm_eq_and_mfderiv_eq_neg_of_not_injOn_riemannianExp
    {r : ℝ} (hreg : ∀ z ∈ closedBall (0 : TangentSpace I p) r,
      Function.Injective (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) z))
    (hnot : ¬ InjOn (riemannianExp I M p) (closedBall 0 r)) :
    ∃ v ∈ closedBall (0 : TangentSpace I p) r, ∃ w ∈ closedBall 0 r,
      riemannianExp I M p v = riemannianExp I M p w ∧ v ≠ w ∧
      0 < ‖v‖ ∧ ‖v‖ = ‖w‖ ∧
      (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v v : E) =
        -(mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) w w : E) ∧
      ∀ x ∈ closedBall (0 : TangentSpace I p) r, ∀ y ∈ closedBall 0 r,
        riemannianExp I M p x = riemannianExp I M p y → x ≠ y →
        ‖v‖ ≤ max ‖x‖ ‖y‖ := by
  have hdom : closedBall (0 : TangentSpace I p) r ⊆ expDomain I M p :=
    fun z hz ↦ mem_expDomain_of_injective_mfderiv_riemannianExp (hreg z hz)
  have hlocal (z : TangentSpace I p) (hz : z ∈ closedBall 0 r) :
      IsLocalDiffeomorphAt 𝓘(ℝ, TangentSpace I p) I 1 (riemannianExp I M p) z :=
    isLocalDiffeomorphAt_of_injective_mfderiv
      ((contMDiffOn_riemannianExp (I := I) p).of_le (by simp))
      (isOpen_expDomain p) (hdom hz)
      BoundarylessManifold.isInteriorPoint (by simp) (hreg z hz) rfl
  obtain ⟨v, hv, w, hw, heq, hne, hpos, hmin⟩ :=
    IsCompact.exists_eq_and_ne_and_max_dist_pos_and_le_of_not_injOn
      (isCompact_closedBall (0 : TangentSpace I p) r)
      ((continuousOn_riemannianExp (I := I) p).mono hdom)
      (fun z hz ↦ by
        obtain ⟨U, hU, hUi⟩ := (hlocal z hz).exists_mem_nhds_injOn
        exact ⟨U, mem_nhdsWithin_of_mem_nhds hU, hUi⟩) hnot 0
  simp only [dist_zero_right] at hpos hmin
  obtain ⟨hnorm, hreturn⟩ := norm_eq_and_mfderiv_eq_neg_of_minimal_riemannianExp_collision
    (by simpa using hv) (by simpa using hw) heq hne
    (hlocal v hv) (hlocal w hw) hmin
  refine ⟨v, hv, w, hw, heq, hne, ?_, hnorm, hreturn, ?_⟩
  · simpa only [hnorm, max_self] using hpos
  · simpa only [hnorm, max_self] using hmin

end TauCeti.Manifold
