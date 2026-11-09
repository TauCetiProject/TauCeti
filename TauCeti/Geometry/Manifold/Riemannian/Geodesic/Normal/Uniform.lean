/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Basic
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential.VariableBase
import TauCeti.Topology.VectorBundle.Radius

/-!
# Uniformly normal neighbourhoods

The exponential map with a variable base point, `(x, v) ↦ (x, exp_x v)`, is a local
diffeomorphism at every zero vector of the tangent bundle
(`TauCeti.Manifold.isLocalDiffeomorphAt_prodMk_proj_riemannianExp_zeroSection`).
Consequently every point `p` has a *uniformly normal* neighbourhood: there are a neighbourhood
`W` of `p` and a radius `r > 0` such that, for every `q ∈ W`, the ball of radius `r` in `T_q M`
is a normal domain at `q` and its exponential image contains all of `W`. The radius is uniform
in the base point, unlike the radius of `TauCeti.Manifold.exists_isNormalDomain_ball`, which
depends on the point. On a compact set of base points a single positive radius gives normal
domains at all of them.

These neighbourhoods are the starting point for geodesically convex neighbourhoods and for
coordinates built from the Riemannian distance to finitely many nearby centres.

## Main results

* `TauCeti.Manifold.exists_mem_nhds_forall_isNormalDomain_ball`: every point has a uniformly
  normal neighbourhood.
* `IsCompact.exists_pos_forall_isNormalDomain_ball`: on a compact set, one positive radius gives
  normal domains at every point.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 3, §3, Theorem 3.7 (totally normal
  neighbourhoods), whose proof applies the inverse function theorem to the same map.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176, 2018, Ch. 6
  (uniformly normal neighbourhoods).
-/

public section

noncomputable section

open Bundle Manifold Set Filter Function
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- A tangent ball at `q` is a normal domain as soon as all its vectors lie in a set of tangent
vectors on which `(x, v) ↦ (x, exp_x v)` is injective, a local diffeomorphism and defined. -/
private theorem isNormalDomain_ball_of_injOn {O : Set (TangentBundle I M)}
    (hinj : InjOn (fun z : TangentBundle I M ↦ (z.proj, riemannianExp I M z.proj z.2)) O)
    (hO : ∀ z ∈ O, IsLocalDiffeomorphAt I.tangent (I.prod I) ∞
      (fun z : TangentBundle I M ↦ (z.proj, riemannianExp I M z.proj z.2)) z ∧
        z.2 ∈ expDomain I M z.proj)
    {q : M} {r : ℝ} (hr : 0 < r)
    (hball : ∀ v : TangentSpace I q, ‖v‖ < r → TotalSpace.mk' E q v ∈ O) :
    IsNormalDomain I M q (Metric.ball 0 r) := by
  have hmem (v : TangentSpace I q) (hv : v ∈ Metric.ball 0 r) := hO _ (hball v
    (mem_ball_zero_iff.1 hv))
  refine ⟨Metric.isOpen_ball, Metric.mem_ball_self hr,
    (convex_ball 0 r).starConvex (Metric.mem_ball_self hr), fun v hv ↦ (hmem v hv).2,
    fun v hv w hw hvw ↦ TotalSpace.mk_inj.1 (hinj (hball v (mem_ball_zero_iff.1 hv))
      (hball w (mem_ball_zero_iff.1 hw)) (by simp only [hvw])),
    fun v ↦ isLocalDiffeomorphAt_riemannianExp_of_prodMk (hmem v v.2).2 (hmem v v.2).1⟩

/-- **Uniformly normal neighbourhoods.** Every point `p` has a neighbourhood `W` with a radius
`r > 0` such that, for every `q ∈ W`, the tangent ball of radius `r` at `q` is a normal domain whose
exponential image contains `W`. In particular `W` lies in a normal neighbourhood of each of its
points. -/
theorem exists_mem_nhds_forall_isNormalDomain_ball (p : M) :
    ∃ r : ℝ, 0 < r ∧ ∃ W ∈ 𝓝 p, ∀ q ∈ W, IsNormalDomain I M q (Metric.ball 0 r) ∧
      W ⊆ riemannianExp I M q '' Metric.ball 0 r := by
  set F := fun z : TangentBundle I M ↦ (z.proj, riemannianExp I M z.proj z.2)
  have hloc := isLocalDiffeomorphAt_prodMk_proj_riemannianExp_zeroSection (I := I) (M := M) p
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
  -- On `O`, the map `F` is a local diffeomorphism, injective (it has the left inverse
  -- `hloc.localInverse`), and the exponential map is defined.
  set O : Set (TangentBundle I M) := hloc.localInverse.target ∩
    ({z | IsLocalDiffeomorphAt I.tangent (I.prod I) ∞ F z} ∩
      {z | z.2 ∈ expDomain I M z.proj})
  have hOopen : IsOpen O := hloc.localInverse.open_target.inter
    ((isOpen_iff_mem_nhds.2 fun _ (hz : IsLocalDiffeomorphAt I.tangent (I.prod I) ∞ F _) ↦
      hz.eventually).inter isOpen_setOfPred_mem_expDomain)
  have hpO : zeroSection E (TangentSpace I) p ∈ O :=
    ⟨hloc.localInverse_mem_target, hloc, zero_mem_expDomain p⟩
  obtain ⟨r, hr, hball⟩ := hOopen.exists_pos_forall_norm_le_subset_bundle hpO
  obtain ⟨A, hAball, hAopen, hpA⟩ := eventually_nhds_iff.1 hball
  have hnorm : Continuous fun z : TangentBundle I M ↦ ‖z.2‖ :=
    TauCeti.continuous_norm_bundle E (TangentSpace I)
  set S : Set (TangentBundle I M) :=
    O ∩ (TotalSpace.proj ⁻¹' A ∩ {z | ‖z.2‖ < r})
  have hSopen : IsOpen S := hOopen.inter
    ((hAopen.preimage (FiberBundle.continuous_proj E _)).inter
      (isOpen_lt hnorm continuous_const))
  -- The zero of the fibre and that of its Riemannian normed group agree only up to instances,
  -- so `norm_zero` is applied after `convert` rather than by `simp`.
  have hpS : zeroSection E (TangentSpace I) p ∈ S :=
    ⟨hpO, hpA, by rw [mem_ofPred_eq]; convert hr using 1; exact norm_zero (E := TangentSpace I p)⟩
  -- The image of `S` is a neighbourhood of `F (0_p) = (p, p)`.
  have hFS : F '' S ∈ 𝓝 (p, p) := by
    have hlocS : IsLocalDiffeomorphOn I.tangent (I.prod I) ∞ F S := fun z ↦ z.2.1.2.1
    have hFp : F (zeroSection E (TangentSpace I) p) = (p, p) := by simp [F, zeroSection]
    exact (hlocS.isOpen_image hSopen).mem_nhds ⟨_, hpS, hFp⟩
  obtain ⟨W₁, hW₁, W₂, hW₂, hW⟩ := mem_nhds_prod_iff.1 hFS
  refine ⟨r, hr, W₁ ∩ W₂ ∩ A, inter_mem (inter_mem hW₁ hW₂) (hAopen.mem_nhds hpA),
    fun q hq ↦ ⟨?_, ?_⟩⟩
  · -- `F` is injective on `O`, where it has the left inverse `hloc.localInverse`.
    exact isNormalDomain_ball_of_injOn
      (fun z (hz : z ∈ O) z' (hz' : z' ∈ O) h ↦ (hloc.localInverse_left_inv hz.1).symm.trans
        ((congrArg hloc.localInverse h).trans (hloc.localInverse_left_inv hz'.1)))
      (fun z (hz : z ∈ O) ↦ hz.2) hr fun v hv ↦ hAball q hq.2 v hv.le
  · intro q' hq'
    obtain ⟨⟨b, w⟩, ⟨-, -, hzr⟩, hz⟩ := hW (mk_mem_prod hq.1.1 hq'.1.2)
    simp only [F, Prod.mk.injEq] at hz
    obtain ⟨rfl, rfl⟩ := hz
    exact ⟨w, mem_ball_zero_iff.2 hzr, rfl⟩

/-- **A uniform normal radius on a compact set.** For a compact set `K` of points there is one
radius `r > 0` such that the tangent ball of radius `r` at every point of `K` is a normal domain. -/
theorem _root_.IsCompact.exists_pos_forall_isNormalDomain_ball {K : Set M} (hK : IsCompact K) :
    ∃ r : ℝ, 0 < r ∧ ∀ q ∈ K, IsNormalDomain I M q (Metric.ball 0 r) := by
  choose! R hR W hW hRW using exists_mem_nhds_forall_isNormalDomain_ball (I := I) (M := M)
  obtain ⟨t, -, hKt⟩ := hK.elim_nhds_subcover W fun p _ ↦ hW p
  rcases t.eq_empty_or_nonempty with rfl | ht
  · exact ⟨1, one_pos, fun q hq ↦ by simpa using hKt hq⟩
  refine ⟨t.inf' ht R, (Finset.lt_inf'_iff ht).2 fun p _ ↦ hR p, fun q hq ↦ ?_⟩
  obtain ⟨p, hpt, hqp⟩ := mem_iUnion₂.1 (hKt hq)
  exact (hRW p q hqp).1.ball (Metric.ball_subset_ball (Finset.inf'_le R hpt))
    ((Finset.lt_inf'_iff ht).2 fun p _ ↦ hR p)

end TauCeti.Manifold
