/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Distance
import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Uniform

/-!
# Local coordinates from squared Riemannian distances

Near any point `p` of a smooth boundaryless Riemannian manifold `M` of dimension `d`, the squared
Riemannian distances `z ↦ (edist (y i) z).toReal ^ 2` to `d` nearby centres `y i` placed along the
rays of an orthonormal basis of `T_p M` form a smooth local coordinate system around `p`.

In a uniformly normal open neighbourhood `W` of `p` of radius `r > 0`, the tangent ball `B(0, r)`
is a normal domain at every `q ∈ W`. Choosing an orthonormal basis `b` of `T_p M` and a small
nonzero step `t` with `|t| < r` such that each `y i = exp_p (t • b i)` lies in `W`, the map
`z ↦ fun i ↦ (edist (y i) z).toReal ^ 2` is smooth on `⋂ i, eball (y i) r`. By the reversed-geodesic
formula for the differential of squared distance (`IsNormalDomain.mvfderiv_toReal_edist_sq_apply`),
its differential at `p` sends `w ∈ T_p M` to `i ↦ (-2 * t) * ⟪b i, w⟫`, as `log_p (y i) = t • b i`.
Because `b` is an orthonormal basis and `t ≠ 0`, this differential is injective between spaces of
the same finite dimension, so the manifold inverse function theorem
(`TauCeti.isLocalDiffeomorphAt_of_injective_mfderiv`) produces a smooth partial diffeomorphism onto
an open subset of `Fin d → ℝ` whose coordinates are squared distances to points inside any
prescribed neighbourhood of `p`.

Because these coordinates depend only on the Riemannian distance function, a metric isometry pulls
a squared-distance chart around `f p` back to a tuple of smooth squared-distance functions around
`p`, reducing smoothness of metric isometries to smoothness of chart inverses.

## Main results

* `TauCeti.Manifold.contMDiffOn_pi_toReal_edist_sq`: a finite tuple of squared distances from
  normal-ball centres `y i` is smooth on the intersection of their open `r`-balls.
* `TauCeti.Manifold.mvfderiv_pi_toReal_edist_sq_apply`: its differential at `p` has `i`-th
  component `-2 * ⟪log_p (y i), ·⟫`.
* `TauCeti.Manifold.IsNormalDomain.isLocalDiffeomorphAt_pi_toReal_edist_sq_riemannianExp`: placing
  centres at `exp_p (t • b i)` along an orthonormal basis `b` of `T_p M` gives a smooth local
  diffeomorphism at `p`.
* `TauCeti.Manifold.exists_partialDiffeomorph_pi_toReal_edist_sq`: inside any neighbourhood `s` of
  `p`, there exist `d = finrank ℝ E` centres `y i ∈ s` such that
  `z ↦ fun i ↦ (edist (y i) z).toReal ^ 2` restricts to a smooth partial diffeomorphism on an open
  neighbourhood of `p` contained in `s`.

## References

* M. Taylor, *Measure Theory and Integration*, Graduate Studies in Mathematics 76, AMS, 2006,
  Appendix E; and *Finsler structures and smoothness of isometries*, Proc. Amer. Math. Soc. 134
  (2006), no. 8, 2419–2423 (distance coordinates via Gauss's lemma and the inverse function
  theorem).
* S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience, 1963,
  Ch. IV, Theorem 3.10 (Myers–Steenrod theorem).
* P. Petersen, *Riemannian Geometry*, 3rd ed., Springer GTM 171, 2016, §5.6.2 (distance
  coordinates).
-/

public section

open Bundle Function Manifold Metric Set
open scoped ContDiff ENNReal Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [EMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]

/-- A finite tuple of squared Riemannian distances `z ↦ fun i ↦ (edist (y i) z).toReal ^ 2` is
smooth on the intersection of the open balls of radius `r` about the centres `y i`, whenever the
open tangent ball of radius `r` lies in a normal domain at each `y i`. -/
theorem contMDiffOn_pi_toReal_edist_sq {ι : Type*} [Fintype ι] {y : ι → M} {r : ℝ}
    {U : ∀ i, Set (TangentSpace I (y i))} (hy : ∀ i, IsNormalDomain I M (y i) (U i))
    (hU : ∀ i, Metric.ball 0 r ⊆ U i) :
    ContMDiffOn I 𝓘(ℝ, ι → ℝ) ∞ (fun z : M ↦ fun i : ι ↦ (edist (y i) z).toReal ^ 2)
      (⋂ i, eball (y i) (ENNReal.ofReal r)) :=
  contMDiffOn_pi_module_iff.2 fun i ↦
    ((hy i).contMDiffOn_toReal_edist_sq (hU i)).mono (iInter_subset _ i)

/-- At a point `p` at distance less than `r` from each normal-ball centre `y i`, the `i`-th
component of the differential of `z ↦ fun j ↦ (edist (y j) z).toReal ^ 2` is
`-2 * ⟪log_p (y i), ·⟫`. -/
theorem mvfderiv_pi_toReal_edist_sq_apply {ι : Type*} [Fintype ι] {y : ι → M} {p : M} {r : ℝ}
    {U : ∀ i, Set (TangentSpace I (y i))} {V : Set (TangentSpace I p)}
    (hy : ∀ i, IsNormalDomain I M (y i) (U i)) (hU : ∀ i, Metric.ball 0 r ⊆ U i)
    (hp : IsNormalDomain I M p V) (hV : Metric.ball 0 r ⊆ V)
    (hyp : ∀ i, edist (y i) p < ENNReal.ofReal r) (w : TangentSpace I p) (i : ι) :
    mvfderiv I (fun z : M ↦ fun j : ι ↦ (edist (y j) z).toReal ^ 2) p w i =
      -2 * inner ℝ (riemannianLog I M p V (y i)) w := by
  have hs : IsOpen (⋂ j, eball (y j) (ENNReal.ofReal r)) :=
    isOpen_iInter_of_finite fun _ ↦ Metric.isOpen_eball
  have hps : p ∈ ⋂ j, eball (y j) (ENNReal.ofReal r) :=
    mem_iInter.2 fun j ↦ mem_eball'.2 (hyp j)
  have hdiff : MDifferentiableAt I 𝓘(ℝ, ι → ℝ)
      (fun z : M ↦ fun j : ι ↦ (edist (y j) z).toReal ^ 2) p :=
    ((contMDiffOn_pi_toReal_edist_sq hy hU).contMDiffAt (hs.mem_nhds hps)).mdifferentiableAt
      (by simp)
  have hproj := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).mvfderiv_comp_apply
    hdiff w
  simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using
    hproj.symm.trans ((hy i).mvfderiv_toReal_edist_sq_apply (hU i) hp hV (hyp i) w)

/-- **Squared-distance coordinates along an orthonormal frame.** If `b` is an orthonormal basis of
`T_p M`, `t ≠ 0` satisfies `|t| < r`, and the open tangent ball of radius `r` is a normal domain at
`p` and at every point `y i = exp_p (t • b i)`, then `z ↦ fun i ↦ (edist (y i) z).toReal ^ 2` is a
smooth local diffeomorphism at `p`. -/
theorem IsNormalDomain.isLocalDiffeomorphAt_pi_toReal_edist_sq_riemannianExp
    {ι : Type*} [Fintype ι] {p : M} {r t : ℝ} (hp : IsNormalDomain I M p (Metric.ball 0 r))
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (ht : t ≠ 0) (htr : |t| < r)
    (hy : ∀ i, IsNormalDomain I M (riemannianExp I M p (t • b i)) (Metric.ball 0 r)) :
    IsLocalDiffeomorphAt I 𝓘(ℝ, ι → ℝ) ∞
      (fun z : M ↦ fun i : ι ↦ (edist (riemannianExp I M p (t • b i)) z).toReal ^ 2) p := by
  set y : ι → M := fun i ↦ riemannianExp I M p (t • b i)
  have hmem_ball (i : ι) : t • b i ∈ Metric.ball (0 : TangentSpace I p) r := by
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, b.orthonormal.1 i, mul_one]
    exact htr
  have hyp (i : ι) : edist (y i) p < ENNReal.ofReal r := by
    have hr : 0 < r := (abs_nonneg t).trans_lt htr
    rw [edist_comm, hp.edist_riemannianExp_eq_of_mem_ball subset_rfl (hmem_ball i), ← ofReal_norm]
    exact (ENNReal.ofReal_lt_ofReal_iff hr).2 (mem_ball_zero_iff.1 (hmem_ball i))
  have hs : IsOpen (⋂ i, eball (y i) (ENNReal.ofReal r)) :=
    isOpen_iInter_of_finite fun _ ↦ Metric.isOpen_eball
  have hps : p ∈ ⋂ i, eball (y i) (ENNReal.ofReal r) :=
    mem_iInter.2 fun i ↦ mem_eball'.2 (hyp i)
  refine TauCeti.isLocalDiffeomorphAt_of_injective_mfderiv
    (contMDiffOn_pi_toReal_edist_sq hy fun _ ↦ subset_rfl) hs hps
    BoundarylessManifold.isInteriorPoint (by simp) (fun u v huv ↦ ?_) ?_
  · apply b.repr.injective
    ext i
    have hu := mvfderiv_pi_toReal_edist_sq_apply hy (fun _ ↦ subset_rfl) hp subset_rfl hyp u i
    have hv := mvfderiv_pi_toReal_edist_sq_apply hy (fun _ ↦ subset_rfl) hp subset_rfl hyp v i
    rw [mvfderiv_apply_eq_mfderiv_apply] at hu hv
    have heq : -2 * inner ℝ (riemannianLog I M p (Metric.ball 0 r) (y i)) u =
        -2 * inner ℝ (riemannianLog I M p (Metric.ball 0 r) (y i)) v :=
      hu.symm.trans ((congrFun huv i).trans hv)
    rw [hp.riemannianLog_riemannianExp (hmem_ball i), real_inner_smul_left,
      real_inner_smul_left] at heq
    have hne : -2 * t ≠ 0 := mul_ne_zero (by norm_num) ht
    have hinner : inner ℝ (b i) u = inner ℝ (b i) v :=
      mul_left_cancel₀ hne (by linear_combination heq)
    simpa only [b.repr_apply_apply] using hinner
  · have hcard : Module.finrank ℝ (TangentSpace I p) = Fintype.card ι :=
      Module.finrank_eq_card_basis b.toBasis
    exact hcard.trans (Module.finrank_pi ℝ).symm

/-- **Existence of squared-distance coordinate charts.** Given any point `p` of a boundaryless
Riemannian manifold and any neighbourhood `s ∈ 𝓝 p`, there exist `d = finrank ℝ E` centres
`y i ∈ s` and a smooth partial diffeomorphism `Φ` onto an open subset of `Fin d → ℝ` whose source
is an open neighbourhood of `p` contained in `s`, such that `Φ z i = (edist (y i) z).toReal ^ 2`
for every `z ∈ Φ.source` and `i : Fin d`. -/
theorem exists_partialDiffeomorph_pi_toReal_edist_sq (p : M) {s : Set M} (hs : s ∈ 𝓝 p) :
    ∃ (y : Fin (Module.finrank ℝ E) → M)
      (Φ : PartialDiffeomorph I 𝓘(ℝ, Fin (Module.finrank ℝ E) → ℝ)
        M (Fin (Module.finrank ℝ E) → ℝ) ∞),
      (∀ i, y i ∈ s) ∧ p ∈ Φ.source ∧ Φ.source ⊆ s ∧
        ∀ z ∈ Φ.source, Φ z = fun i ↦ (edist (y i) z).toReal ^ 2 := by
  obtain ⟨r, hr, W, hW_nhds, hW⟩ := exists_mem_nhds_forall_isNormalDomain_ball (I := I) (M := M) p
  obtain ⟨U, hU_sub, hUo, hpU⟩ := mem_nhds_iff.1 (Filter.inter_mem hs hW_nhds)
  let b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I p) :=
    stdOrthonormalBasis ℝ (TangentSpace I p)
  have hcont : ContinuousAt
      (fun t : ℝ ↦ fun i : Fin (Module.finrank ℝ E) ↦ riemannianExp I M p (t • b i)) 0 := by
    refine continuousAt_pi.2 fun i ↦ ?_
    have hsmul : ContinuousAt (fun t : ℝ ↦ t • b i) 0 := by fun_prop
    exact (continuousAt_riemannianExp (by simp only [zero_smul]; exact zero_mem_expDomain p)).comp
      hsmul
  have hpre : {t : ℝ | ∀ i, riemannianExp I M p (t • b i) ∈ U} ∈ 𝓝 (0 : ℝ) := by
    have hpi : Set.pi univ (fun _ : Fin (Module.finrank ℝ E) ↦ U) ∈
        𝓝 (fun _ : Fin (Module.finrank ℝ E) ↦ p) :=
      set_pi_mem_nhds finite_univ fun _ _ ↦ hUo.mem_nhds hpU
    have h0 : (fun i : Fin (Module.finrank ℝ E) ↦ riemannianExp I M p ((0 : ℝ) • b i)) =
        fun _ ↦ p := funext fun _ ↦ by rw [zero_smul, riemannianExp_zero]
    refine Filter.mem_of_superset (hcont.preimage_mem_nhds (h0 ▸ hpi)) fun _ ht i ↦ ?_
    exact Set.mem_pi.1 ht i (mem_univ i)
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.1 hpre
  let t : ℝ := min (r / 2) (δ / 2)
  have ht_pos : 0 < t := lt_min (half_pos hr) (half_pos hδ)
  have htr : |t| < r := by
    rw [abs_of_pos ht_pos]
    exact (min_le_left _ _).trans_lt (half_lt_self hr)
  have htU : ∀ i, riemannianExp I M p (t • b i) ∈ U := by
    refine hδU ?_
    rw [Metric.mem_ball, Real.dist_0_eq_abs, abs_of_pos ht_pos]
    exact (min_le_right _ _).trans_lt (half_lt_self hδ)
  set y : Fin (Module.finrank ℝ E) → M := fun i ↦ riemannianExp I M p (t • b i)
  have hp_norm : IsNormalDomain I M p (Metric.ball 0 r) := (hW p (hU_sub hpU).2).1
  have hy_norm : ∀ i, IsNormalDomain I M (y i) (Metric.ball 0 r) :=
    fun i ↦ (hW (y i) (hU_sub (htU i)).2).1
  have hloc := hp_norm.isLocalDiffeomorphAt_pi_toReal_edist_sq_riemannianExp b ht_pos.ne' htr
    hy_norm
  let Ψ := hloc.localInverse.symm
  refine ⟨y, Ψ.restrOpen U hUo, fun i ↦ (hU_sub (htU i)).1, ?_, ?_, fun z hz ↦ ?_⟩
  · rw [PartialDiffeomorph.restrOpen_source]
    exact ⟨hloc.localInverse_mem_target, hpU⟩
  · rw [PartialDiffeomorph.restrOpen_source]
    exact fun z hz ↦ (hU_sub hz.2).1
  · rw [PartialDiffeomorph.restrOpen_source] at hz
    rw [PartialDiffeomorph.coe_restrOpen]
    have hzΨ : z ∈ hloc.localInverse.target := hz.1
    have hsymm : Ψ z ∈ hloc.localInverse.source := Ψ.map_source hzΨ
    have hleft : hloc.localInverse (Ψ z) = z := hloc.localInverse.right_inv hzΨ
    calc Ψ z
        = (fun z' : M ↦ fun i ↦ (edist (y i) z').toReal ^ 2) (hloc.localInverse (Ψ z)) :=
          (hloc.localInverse_right_inv hsymm).symm
      _ = fun i ↦ (edist (y i) z).toReal ^ 2 := by rw [hleft]

end TauCeti.Manifold

end
