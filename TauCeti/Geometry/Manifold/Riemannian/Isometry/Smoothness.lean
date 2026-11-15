/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Distance
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Local
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Topology
public import TauCeti.Topology.MetricSpace.Isometry.Group
import TauCeti.Analysis.Calculus.FDeriv.NormComparison
import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.DistanceChart
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Segment
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Uniform

/-!
# Smoothness of metric isometries of Riemannian manifolds

Every distance-preserving bijection between smooth boundaryless Riemannian manifolds is a smooth
Riemannian isometry, and on a compact manifold the weak Whitney `C^∞` topology on smooth
Riemannian isometries agrees with the compact-open topology on metric equivalences.

Near a point `p ∈ M` at which an open distance-preserving map `f : M → N` has open local image, one
chooses a squared-distance chart `Φ` around `f p` (`exists_partialDiffeomorph_pi_toReal_edist_sq`)
whose `d_N` centres `y i = f (a i)` come from points `a i` inside a uniformly normal ball around
`p`. Because `f` preserves Riemannian distance near `p`, `Φ (f z) i = (edist (a i) z).toReal ^ 2`,
so `f z = Φ.symm (fun i ↦ (edist (a i) z).toReal ^ 2)` is a composition of smooth maps near `p`.
Applying the same argument to the local inverse shows `f` is a smooth local diffeomorphism at `p`.
Once `f` is differentiable at `p`, comparing its germ in normal coordinates at `p` and `f p` along
radial rays shows `‖df_p v‖ = ‖v‖`, hence `df_p` preserves inner products by polarization.

For a family of metric equivalences `e : M ≃ᵢ N`, expressing `e` locally as
`Φ_N.symm (fun i ↦ (edist (e.symm (y_N i)) ·).toReal ^ 2)` writes the coordinate representative of
`e` as a smooth function of the evaluation points `e.symm (y_N i)` and the source chart coordinate.
Since inversion and evaluation are continuous in the compact-open topology on `M ≃ᵢ N`, all chart
iterated derivatives vary continuously with `e` (`IsometryEquiv.continuous_toContMDiffMap`), and
when `M` is compact this identifies the weak Whitney `C^∞` topology on
`RiemannianIsometry I J M N` with the compact-open topology on `M ≃ᵢ N`. Combining with the
van Dantzig–van der Waerden theorem (`IsometryEquiv.instCompactSpace`) shows that
`RiemannianIsometry I J M N` and `Isom I M` are compact Hausdorff spaces in the weak Whitney
topology.

## Main definitions

* `IsometryEquiv.toRiemannianIsometry`: a metric equivalence `M ≃ᵢ N` between smooth boundaryless
  Riemannian manifolds promoted to a smooth `TauCeti.RiemannianIsometry`.
* `Isometry.riemannianIsometryOfCompactSpace`: a distance-preserving self-map of a compact
  boundaryless Riemannian manifold promoted to an element of `TauCeti.Isom I M`.
* `TauCeti.RiemannianIsometry.isometryEquivEquiv`: the equivalence
  `RiemannianIsometry I J M N ≃ (M ≃ᵢ N)`.
* `TauCeti.RiemannianIsometry.isometryEquivMulEquiv`: the group isomorphism
  `Isom I M ≃* (M ≃ᵢ M)`.
* `TauCeti.RiemannianIsometry.isometryEquivHomeomorph`: the homeomorphism
  `RiemannianIsometry I J M N ≃ₜ (M ≃ᵢ N)` between the weak Whitney topology and the compact-open
  topology when `M` is compact.
* `TauCeti.RiemannianIsometry.isometryEquivContinuousMulEquiv`: the topological group isomorphism
  `Isom I M ≃ₜ* (M ≃ᵢ M)` when `M` is compact.

## Main results

* `MDifferentiableAt.norm_mfderiv_eq_of_eventually_edist_eq`,
  `MDifferentiableAt.inner_mfderiv_eq_of_eventually_edist_eq`: a map differentiable at `p` that
  preserves extended distances from `p` near `p` preserves norms and inner products on `T_p M`.
* `TauCeti.Manifold.contMDiffAt_of_isometry_domRestrict`,
  `TauCeti.Manifold.isLocalDiffeomorphAt_of_isometry_domRestrict`,
  `TauCeti.Manifold.isLocalRiemannianIsometry_of_forall_exists_isometry_domRestrict`: a map
  restricting locally around each point `p` to a metric isometry on an open neighbourhood `U` with
  `f '' U ∈ 𝓝 (f p)` is smooth, a smooth local diffeomorphism, and a smooth local Riemannian
  isometry.
* `Isometry.isLocalRiemannianIsometry_of_isOpen_range`: a metric isometry with open range is a
  smooth local Riemannian isometry.
* `IsometryEquiv.contMDiff`: every metric equivalence `M ≃ᵢ N` is smooth.
* `IsometryEquiv.continuous_toContMDiffMap`, `IsometryEquiv.continuous_toRiemannianIsometry`:
  promoting metric equivalences is continuous from the compact-open topology into the weak Whitney
  `C^∞` topology.
* `TauCeti.RiemannianIsometry.exists_coe_eq_iff_isometry_and_surjective`,
  `TauCeti.RiemannianIsometry.exists_isom_coe_eq_iff_isometry`: smooth Riemannian isometries are
  characterized among maps by preserving the Riemannian distance (and surjectivity, automatic for
  self-maps of compact manifolds).
* `TauCeti.RiemannianIsometry.compactSpace_weakWhitney`: `RiemannianIsometry I J M N` is compact
  in the weak Whitney topology when `M` is compact and Hausdorff.

## References

* S. B. Myers, N. E. Steenrod, *The group of isometries of a Riemannian manifold*, Ann. of Math.
  (2) 40 (1939), 400–416.
* M. Taylor, *Measure Theory and Integration*, Graduate Studies in Mathematics 76, AMS, 2006,
  Appendix E; and *Finsler structures and smoothness of isometries*, Proc. Amer. Math. Soc. 134
  (2006), no. 8, 2419–2423.
* S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience, 1963,
  Ch. IV, Theorem 3.10.
* P. Petersen, *Riemannian Geometry*, 3rd ed., Springer GTM 171, 2016, §5.6.2.
-/

public section

open Bundle Filter Function Manifold Metric Set Topology
open scoped ContDiff ENNReal Manifold

noncomputable section

section GroupToIsometryEquiv

namespace TauCeti.RiemannianIsometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]

/-- The unit of `Isom I M` coerces to the unit of `M ≃ᵢ M`. -/
@[simp]
theorem toIsometryEquiv_one : ((1 : Isom I M) : M ≃ᵢ M) = 1 := by
  ext x
  simp

/-- Coercing `Isom I M` to `M ≃ᵢ M` preserves multiplication. -/
@[simp]
theorem toIsometryEquiv_mul (Φ Ψ : Isom I M) :
    ((Φ * Ψ : Isom I M) : M ≃ᵢ M) = (Φ : M ≃ᵢ M) * (Ψ : M ≃ᵢ M) := by
  ext x
  simp

/-- Coercing `Isom I M` to `M ≃ᵢ M` preserves inversion. -/
@[simp]
theorem toIsometryEquiv_inv (Φ : Isom I M) :
    ((Φ⁻¹ : Isom I M) : M ≃ᵢ M) = (Φ : M ≃ᵢ M)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← toIsometryEquiv_mul, inv_mul_cancel, toIsometryEquiv_one])

/-- Coercing `Isom I M` to `M ≃ᵢ M` preserves division. -/
@[simp]
theorem toIsometryEquiv_div (Φ Ψ : Isom I M) :
    ((Φ / Ψ : Isom I M) : M ≃ᵢ M) = (Φ : M ≃ᵢ M) / (Ψ : M ≃ᵢ M) := by
  simp [div_eq_mul_inv]

/-- Coercing `Isom I M` to `M ≃ᵢ M` preserves natural powers. -/
@[simp]
theorem toIsometryEquiv_pow (Φ : Isom I M) (n : ℕ) :
    ((Φ ^ n : Isom I M) : M ≃ᵢ M) = (Φ : M ≃ᵢ M) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih]

/-- Coercing `Isom I M` to `M ≃ᵢ M` preserves integer powers. -/
@[simp]
theorem toIsometryEquiv_zpow (Φ : Isom I M) (n : ℤ) :
    ((Φ ^ n : Isom I M) : M ≃ᵢ M) = (Φ : M ≃ᵢ M) ^ n := by
  cases n with
  | ofNat n => simp
  | negSucc n => simp

end TauCeti.RiemannianIsometry

end GroupToIsometryEquiv

section Differential

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
  {M : Type*} [EMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]
  {N : Type*} [EMetricSpace N] [ChartedSpace H' N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)] [IsManifold J ∞ N]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]
  [IsRiemannianManifold J N]

/-- If a map between real normed spaces is differentiable at `0` and preserves norms near `0`,
its Fréchet derivative at `0` preserves norms. -/
private theorem DifferentiableAt.norm_fderiv_zero_eq
    {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] {Ψ : E₁ → E₂}
    (hΨ : DifferentiableAt ℝ Ψ 0) (hnorm : ∀ᶠ u in 𝓝 (0 : E₁), ‖Ψ u‖ = ‖u‖) (v : E₁) :
    ‖fderiv ℝ Ψ 0 v‖ = ‖v‖ := by
  have hΨ0 : Ψ 0 = 0 := by
    have h0 := hnorm.self_of_nhds
    rwa [norm_zero, norm_eq_zero] at h0
  have hpair := hΨ.hasFDerivAt.prodMk (hasFDerivAt_id (0 : E₁))
  refine le_antisymm ?_ ?_
  · simpa using hpair.norm_apply_le_mul_norm_apply
      (L := ContinuousLinearMap.fst ℝ E₂ E₁) (M := ContinuousLinearMap.snd ℝ E₂ E₁)
      (A := 1) (hnorm.mono fun u hu ↦ by simp [hΨ0, hu]) v
  · simpa using hpair.norm_apply_le_mul_norm_apply
      (L := ContinuousLinearMap.snd ℝ E₂ E₁) (M := ContinuousLinearMap.fst ℝ E₂ E₁)
      (A := 1) (hnorm.mono fun u hu ↦ by simp [hΨ0, hu]) v

namespace MDifferentiableAt

open TauCeti.Manifold

/-- If `f : M → N` is differentiable at `p` and preserves extended distances from `p` on a
neighbourhood of `p`, then `df_p` preserves tangent-vector norms. -/
theorem norm_mfderiv_eq_of_eventually_edist_eq {f : M → N} {p : M}
    (hf : MDifferentiableAt I J f p) (hedist : ∀ᶠ x in 𝓝 p, edist (f p) (f x) = edist p x)
    (v : TangentSpace I p) :
    ‖mfderiv I J f p v‖ = ‖v‖ := by
  obtain ⟨rM, hrM, hM⟩ := exists_isNormalDomain_ball (I := I) (M := M) p
  obtain ⟨rN, hrN, hN⟩ := exists_isNormalDomain_ball (I := J) (M := N) (f p)
  set L : N → TangentSpace J (f p) := riemannianLog J N (f p) (Metric.ball 0 rN)
  set Ψ : TangentSpace I p → TangentSpace J (f p) := (L ∘ f) ∘ riemannianExp I M p
  have hL : MDifferentiableAt J 𝓘(ℝ, TangentSpace J (f p)) L (f p) :=
    hN.mdifferentiableAt_riemannianLog hN.self_mem_image
  have hexp : MDifferentiableAt 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) 0 :=
    (contMDiffAt_riemannianExp (zero_mem_expDomain p)).mdifferentiableAt (by simp)
  have hLf : MDifferentiableAt I 𝓘(ℝ, TangentSpace J (f p)) (L ∘ f) p := hL.comp p hf
  have hΨ_diff : DifferentiableAt ℝ Ψ 0 :=
    mdifferentiableAt_iff_differentiableAt.1 (hLf.comp_of_eq 0 hexp (riemannianExp_zero p))
  have hfderiv : fderiv ℝ Ψ 0 v = mfderiv I J f p v := by
    let v₀ : TangentSpace 𝓘(ℝ, TangentSpace I p) (0 : TangentSpace I p) :=
      (NormedSpace.fromTangentSpace (0 : TangentSpace I p)).symm v
    calc fderiv ℝ Ψ 0 v
        = mvfderiv 𝓘(ℝ, TangentSpace I p) Ψ 0 v₀ := by
            rw [mvfderiv_eq_fderiv, ContinuousLinearMap.comp_apply,
              ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
      _ = mvfderiv I (L ∘ f) p (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) 0 v₀) :=
            mvfderiv_comp_apply_of_eq 0 hLf hexp (riemannianExp_zero p) v₀
      _ = mvfderiv I (L ∘ f) p v :=
            congrArg (mvfderiv I (L ∘ f) p) <|
              (congrArg (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) 0)
                (NormedSpace.fromTangentSpace_symm_apply (𝕜 := ℝ) (0 : TangentSpace I p) v)).trans
                (mfderiv_riemannianExp_apply_zero (I := I) p v)
      _ = mfderiv I J f p v := by
            rw [mvfderiv_comp_apply p hL hf v, hN.mvfderiv_riemannianLog_self,
              ContinuousLinearMap.id_apply]
  -- Near `0 ∈ T_p M`, `exp_p u` stays in the normal ball at `p`, lands in the normal ball at
  -- `f p`, and lies in the region where `f` preserves distance from `p`, so `‖Ψ u‖ = ‖u‖`.
  have hexp_cont : ContinuousAt (riemannianExp I M p) 0 :=
    continuousAt_riemannianExp (zero_mem_expDomain p)
  have hnorm_ev : ∀ᶠ u : TangentSpace I p in 𝓝 0, ‖Ψ u‖ = ‖u‖ := by
    have h1 : ∀ᶠ u in 𝓝 (0 : TangentSpace I p), u ∈ Metric.ball (0 : TangentSpace I p) rM :=
      Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hrM)
    have h2 : ∀ᶠ u in 𝓝 (0 : TangentSpace I p),
        edist (f p) (f (riemannianExp I M p u)) = edist p (riemannianExp I M p u) :=
      hexp_cont.eventually (by rwa [riemannianExp_zero])
    have h3 : ∀ᶠ u in 𝓝 (0 : TangentSpace I p),
        f (riemannianExp I M p u) ∈ eball (f p) (ENNReal.ofReal rN) := by
      have hballN : eball (f p) (ENNReal.ofReal rN) ∈ 𝓝 (f p) :=
        Metric.isOpen_eball.mem_nhds (Metric.mem_eball_self (ENNReal.ofReal_pos.2 hrN))
      exact (hf.continuousAt.comp_of_eq hexp_cont (riemannianExp_zero p)).preimage_mem_nhds
        (by simpa only [comp_apply, riemannianExp_zero] using hballN)
    filter_upwards [h1, h2, h3] with u hu1 hu2 hu3
    have hlog := hN.toReal_edist_eq_norm_riemannianLog_of_mem_eball subset_rfl hu3
    simp only [Ψ, L, comp_apply]
    rw [← hlog, hu2, hM.edist_riemannianExp_eq_of_mem_ball subset_rfl hu1, ← ofReal_norm,
      ENNReal.toReal_ofReal (norm_nonneg u)]
  rw [← hfderiv]
  exact hΨ_diff.norm_fderiv_zero_eq hnorm_ev v

/-- If `f : M → N` is differentiable at `p` and preserves extended distances from `p` on a
neighbourhood of `p`, then `df_p` preserves inner products of tangent vectors. -/
theorem inner_mfderiv_eq_of_eventually_edist_eq {f : M → N} {p : M}
    (hf : MDifferentiableAt I J f p) (hedist : ∀ᶠ x in 𝓝 p, edist (f p) (f x) = edist p x)
    (v w : TangentSpace I p) :
    inner ℝ (mfderiv I J f p v) (mfderiv I J f p w) = inner ℝ v w := by
  let L : TangentSpace I p →ₗᵢ[ℝ] TangentSpace J (f p) :=
    { toLinearMap := (mfderiv I J f p).toLinearMap
      norm_map' := hf.norm_mfderiv_eq_of_eventually_edist_eq hedist }
  exact L.inner_map_map v w

end MDifferentiableAt

/-! ### Local smoothness of distance-preserving maps -/

namespace TauCeti.Manifold

/-- **Local smoothness of metric isometries.** If `f : M → N` restricts to a metric isometry on an
open neighbourhood `U` of `p` and `f '' U` is a neighbourhood of `f p`, then `f` is smooth at
`p`. -/
theorem contMDiffAt_of_isometry_domRestrict {f : M → N} {U : Set M} {p : M} (hU : IsOpen U)
    (hp : p ∈ U) (hf : Isometry (U.domRestrict f)) (hfU : f '' U ∈ 𝓝 (f p)) :
    ContMDiffAt I J ∞ f p := by
  obtain ⟨r, hr, WM, hWM_nhds, hWM⟩ :=
    exists_mem_nhds_forall_isNormalDomain_ball (I := I) (M := M) p
  obtain ⟨WM', hWM'_sub, hWM'o, hpWM'⟩ := mem_nhds_iff.1 hWM_nhds
  set VM : Set M := U ∩ WM' ∩ eball p (ENNReal.ofReal (r / 2))
  have hr2 : 0 < ENNReal.ofReal (r / 2) := ENNReal.ofReal_pos.2 (half_pos hr)
  have hVMo : IsOpen VM := (hU.inter hWM'o).inter Metric.isOpen_eball
  have hpVM : p ∈ VM := ⟨⟨hp, hpWM'⟩, Metric.mem_eball_self hr2⟩
  -- Because `f` is isometric on `U`, the image of `VM` is still a neighbourhood of `f p`.
  obtain ⟨ε, hε, hε_sub⟩ := EMetric.mem_nhds_iff.1 (hVMo.mem_nhds hpVM)
  have hfVM : f '' VM ∈ 𝓝 (f p) := by
    refine mem_of_superset (inter_mem hfU (Metric.isOpen_eball.mem_nhds
      (Metric.mem_eball_self hε))) ?_
    rintro _ ⟨⟨x, hxU, rfl⟩, hdist⟩
    refine mem_image_of_mem f (hε_sub ?_)
    rw [Metric.mem_eball] at hdist ⊢
    have hiso := hf.edist_eq ⟨x, hxU⟩ ⟨p, hp⟩
    exact hiso.symm.trans_lt hdist
  obtain ⟨yN, Φ, hyN_mem, hfp_src, _, hΦ_eq⟩ :=
    exists_partialDiffeomorph_pi_toReal_edist_sq (I := J) (M := N) (f p) hfVM
  choose a ha_VM hfa using fun i ↦ hyN_mem i
  have ha_norm (i : Fin (Module.finrank ℝ F)) : IsNormalDomain I M (a i) (Metric.ball 0 r) :=
    (hWM (a i) (hWM'_sub (ha_VM i).1.2)).1
  have hf_cont : ContinuousOn f U := continuousOn_iff_continuous_domRestrict.2 hf.continuous
  set O : Set M := VM ∩ f ⁻¹' Φ.source
  have hOo : IsOpen O :=
    (hf_cont.mono fun _ (hz : _ ∈ VM) ↦ hz.1.1).isOpen_inter_preimage hVMo Φ.open_source
  have hpO : p ∈ O := ⟨hpVM, hfp_src⟩
  have hO_balls : O ⊆ ⋂ i, eball (a i) (ENNReal.ofReal r) := by
    intro z hz
    refine mem_iInter.2 fun i ↦ Metric.mem_eball'.2 ?_
    have ha_ed : edist (a i) p < ENNReal.ofReal (r / 2) := Metric.mem_eball.1 (ha_VM i).2
    have hz_ed : edist p z < ENNReal.ofReal (r / 2) := Metric.mem_eball'.1 hz.1.2
    calc edist (a i) z
        ≤ edist (a i) p + edist p z := edist_triangle _ _ _
      _ < ENNReal.ofReal (r / 2) + ENNReal.ofReal (r / 2) := ENNReal.add_lt_add ha_ed hz_ed
      _ = ENNReal.ofReal r := by
          rw [← ENNReal.ofReal_add (half_pos hr).le (half_pos hr).le, add_halves]
  set coord : M → Fin (Module.finrank ℝ F) → ℝ :=
    fun z i ↦ (edist (a i) z).toReal ^ 2
  have hcoord_smooth : ContMDiffOn I 𝓘(ℝ, Fin (Module.finrank ℝ F) → ℝ) ∞ coord O :=
    (contMDiffOn_pi_toReal_edist_sq ha_norm fun _ ↦ subset_rfl).mono hO_balls
  have hcoord_eq (z : M) (hz : z ∈ O) : coord z = Φ (f z) := by
    rw [hΦ_eq (f z) hz.2]
    ext i
    have hiso := hf.edist_eq ⟨a i, (ha_VM i).1.1⟩ ⟨z, hz.1.1.1⟩
    simp only [Set.domRestrict_apply, Subtype.edist_mk_mk, hfa i] at hiso
    simp only [coord, ← hiso]
  have hmaps : MapsTo coord O Φ.symm.source := fun z hz ↦ by
    rw [hcoord_eq z hz]
    exact Φ.map_source hz.2
  have hcomp : ContMDiffOn I J ∞ (Φ.symm ∘ coord) O :=
    Φ.symm.contMDiffOn.comp hcoord_smooth hmaps
  have hcongr : EqOn f (Φ.symm ∘ coord) O := fun z hz ↦ by
    simp only [comp_apply, hcoord_eq z hz]
    exact (Φ.left_inv hz.2).symm
  exact (hcomp.congr hcongr).contMDiffAt (hOo.mem_nhds hpO)

/-- If `f : M → N` restricts to a metric isometry on an open neighbourhood `U` of `p` and
`f '' U ∈ 𝓝 (f p)`, then `f` is a smooth local diffeomorphism at `p`. -/
theorem isLocalDiffeomorphAt_of_isometry_domRestrict {f : M → N} {U : Set M} {p : M}
    (hU : IsOpen U) (hp : p ∈ U) (hf : Isometry (U.domRestrict f)) (hfU : f '' U ∈ 𝓝 (f p)) :
    IsLocalDiffeomorphAt I J ∞ f p := by
  have : Nonempty M := ⟨p⟩
  have hinj : InjOn f U := fun x₁ hx₁ x₂ hx₂ hfx ↦
    congrArg Subtype.val (hf.injective (a₁ := ⟨x₁, hx₁⟩) (a₂ := ⟨x₂, hx₂⟩) hfx)
  have hf_cont : ContinuousOn f U := continuousOn_iff_continuous_domRestrict.2 hf.continuous
  set VN : Set N := interior (f '' U)
  set U' : Set M := U ∩ f ⁻¹' VN
  set g : N → M := invFunOn f U
  have hVNo : IsOpen VN := isOpen_interior
  have hU'o : IsOpen U' := hf_cont.isOpen_inter_preimage hU hVNo
  have hpU' : p ∈ U' := ⟨hp, mem_interior_iff_mem_nhds.2 hfU⟩
  have hg_mem {y : N} (hy : y ∈ VN) : g y ∈ U' :=
    ⟨invFunOn_mem (interior_subset hy),
      mem_preimage.2 (by simpa only [g, invFunOn_eq (interior_subset hy)] using hy)⟩
  have hg_isom : Isometry (VN.domRestrict g) := fun ⟨y₁, hy₁⟩ ⟨y₂, hy₂⟩ ↦ by
    have h := (hf.edist_eq ⟨g y₁, (hg_mem hy₁).1⟩ ⟨g y₂, (hg_mem hy₂).1⟩).symm
    simpa only [Set.domRestrict_apply, Subtype.edist_mk_mk, g,
      invFunOn_eq (interior_subset hy₁), invFunOn_eq (interior_subset hy₂)] using h
  have hU'_sub_im : U' ⊆ g '' VN := fun x hx ↦ ⟨f x, hx.2, hinj.leftInvOn_invFunOn hx.1⟩
  let Ψ : PartialDiffeomorph I J M N ∞ :=
    { toFun := f
      invFun := g
      source := U'
      target := VN
      map_source' := fun _ hx ↦ hx.2
      map_target' := fun _ hy ↦ hg_mem hy
      left_inv' := fun _ hx ↦ hinj.leftInvOn_invFunOn hx.1
      right_inv' := fun _ hy ↦ invFunOn_eq (interior_subset hy)
      open_source := hU'o
      open_target := hVNo
      contMDiffOn_toFun := fun x hx ↦
        (contMDiffAt_of_isometry_domRestrict hU hx.1 hf
          (mem_interior_iff_mem_nhds.1 hx.2)).contMDiffWithinAt
      contMDiffOn_invFun := fun y hy ↦
        (contMDiffAt_of_isometry_domRestrict hVNo hy hg_isom
          (mem_of_superset (hU'o.mem_nhds (hg_mem hy)) hU'_sub_im)).contMDiffWithinAt }
  exact TauCeti.isLocalDiffeomorphAt_of_eqOn (Φ := Ψ) hpU' (eqOn_refl f U')

/-- If `f : M → N` restricts around each point `p : M` to a metric isometry on an open
neighbourhood `U` with `f '' U ∈ 𝓝 (f p)`, then `f` is a smooth local Riemannian isometry. -/
theorem isLocalRiemannianIsometry_of_forall_exists_isometry_domRestrict {f : M → N}
    (hf : ∀ p : M, ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ Isometry (U.domRestrict f) ∧ f '' U ∈ 𝓝 (f p)) :
    TauCeti.IsLocalRiemannianIsometry I J f where
  contMDiff p :=
    let ⟨_, hUo, hpU, hfU_isom, hfU_nhds⟩ := hf p
    contMDiffAt_of_isometry_domRestrict hUo hpU hfU_isom hfU_nhds
  isInvertible_mfderiv p :=
    let ⟨_, hUo, hpU, hfU_isom, hfU_nhds⟩ := hf p
    (isLocalDiffeomorphAt_of_isometry_domRestrict (I := I) (J := J) hUo hpU hfU_isom hfU_nhds)
      |>.isInvertible_mfderiv (by simp)
  inner_mfderiv p :=
    let ⟨U, hUo, hpU, hfU_isom, hfU_nhds⟩ := hf p
    ((contMDiffAt_of_isometry_domRestrict (I := I) (J := J) hUo hpU hfU_isom hfU_nhds)
      |>.mdifferentiableAt (by simp))
      |>.inner_mfderiv_eq_of_eventually_edist_eq
        (eventually_of_mem (hUo.mem_nhds hpU) fun y hy ↦ hfU_isom.edist_eq ⟨p, hpU⟩ ⟨y, hy⟩)

end TauCeti.Manifold

/-! ### Global metric isometries and metric equivalences -/

namespace Isometry

open TauCeti.Manifold

/-- A metric isometry `f : M → N` whose range is a neighbourhood of `f p` is smooth at `p`. -/
theorem contMDiffAt_of_range_mem_nhds {f : M → N} (hf : Isometry f) {p : M}
    (hr : range f ∈ 𝓝 (f p)) : ContMDiffAt I J ∞ f p :=
  contMDiffAt_of_isometry_domRestrict isOpen_univ (mem_univ p)
    (hf.comp (fun _ _ ↦ rfl)) (by simpa only [image_univ] using hr)

/-- A metric isometry `f : M → N` whose range is a neighbourhood of `f p` is a smooth local
diffeomorphism at `p`. -/
theorem isLocalDiffeomorphAt_of_range_mem_nhds {f : M → N} (hf : Isometry f) {p : M}
    (hr : range f ∈ 𝓝 (f p)) : IsLocalDiffeomorphAt I J ∞ f p :=
  isLocalDiffeomorphAt_of_isometry_domRestrict isOpen_univ (mem_univ p)
    (hf.comp (fun _ _ ↦ rfl)) (by simpa only [image_univ] using hr)

/-- A metric isometry `f : M → N` with open range is smooth. -/
theorem contMDiff_of_isOpen_range {f : M → N} (hf : Isometry f) (hr : IsOpen (range f)) :
    ContMDiff I J ∞ f :=
  fun p ↦ hf.contMDiffAt_of_range_mem_nhds (hr.mem_nhds (mem_range_self p))

/-- A metric isometry `f : M → N` with open range is a smooth local diffeomorphism. -/
theorem isLocalDiffeomorph_of_isOpen_range {f : M → N} (hf : Isometry f)
    (hr : IsOpen (range f)) : IsLocalDiffeomorph I J ∞ f :=
  fun p ↦ hf.isLocalDiffeomorphAt_of_range_mem_nhds (hr.mem_nhds (mem_range_self p))

/-- A metric isometry `f : M → N` with open range is a smooth local Riemannian isometry. -/
theorem isLocalRiemannianIsometry_of_isOpen_range {f : M → N} (hf : Isometry f)
    (hr : IsOpen (range f)) : TauCeti.IsLocalRiemannianIsometry I J f :=
  isLocalRiemannianIsometry_of_forall_exists_isometry_domRestrict fun p ↦
    ⟨univ, isOpen_univ, mem_univ p, hf.comp (fun _ _ ↦ rfl),
      by simpa only [image_univ] using hr.mem_nhds (mem_range_self p)⟩

/-- A surjective metric isometry `f : M → N` is smooth. -/
theorem contMDiff_of_surjective {f : M → N} (hf : Isometry f) (hsurj : Surjective f) :
    ContMDiff I J ∞ f :=
  hf.contMDiff_of_isOpen_range (hsurj.range_eq.symm ▸ isOpen_univ)

/-- A surjective metric isometry `f : M → N` is a smooth local Riemannian isometry. -/
theorem isLocalRiemannianIsometry_of_surjective {f : M → N} (hf : Isometry f)
    (hsurj : Surjective f) : TauCeti.IsLocalRiemannianIsometry I J f :=
  hf.isLocalRiemannianIsometry_of_isOpen_range (hsurj.range_eq.symm ▸ isOpen_univ)

end Isometry

namespace IsometryEquiv

variable (I J) in
/-- **Myers–Steenrod smoothness theorem.** Every metric equivalence `e : M ≃ᵢ N` between smooth
boundaryless Riemannian manifolds is smooth. -/
protected theorem contMDiff (e : M ≃ᵢ N) : ContMDiff I J ∞ e :=
  e.isometry.contMDiff_of_surjective e.surjective

variable (I J) in
/-- Promote a metric equivalence `e : M ≃ᵢ N` between smooth boundaryless Riemannian manifolds to a
smooth `TauCeti.RiemannianIsometry`. -/
def toRiemannianIsometry (e : M ≃ᵢ N) : TauCeti.RiemannianIsometry I J M N where
  toDiffeomorph :=
    { toEquiv := e.toEquiv
      contMDiff_toFun := e.contMDiff I J
      contMDiff_invFun := e.symm.contMDiff J I }
  inner_mfderiv' :=
    (e.isometry.isLocalRiemannianIsometry_of_surjective (I := I) (J := J) e.surjective)
      |>.inner_mfderiv

/-- Promoting a metric equivalence to a smooth Riemannian isometry preserves the underlying map. -/
@[simp]
theorem coe_toRiemannianIsometry (e : M ≃ᵢ N) : ⇑(e.toRiemannianIsometry I J) = ⇑e :=
  (rfl)

/-- Applying `e.toRiemannianIsometry I J` evaluates `e`. -/
@[simp]
theorem toRiemannianIsometry_apply (e : M ≃ᵢ N) (x : M) : e.toRiemannianIsometry I J x = e x :=
  (rfl)

/-- Promoting the inverse metric equivalence gives the inverse smooth Riemannian isometry. -/
@[simp]
theorem toRiemannianIsometry_symm (e : M ≃ᵢ N) :
    e.symm.toRiemannianIsometry J I = (e.toRiemannianIsometry I J).symm := by
  ext y
  apply (EquivLike.injective (e.toRiemannianIsometry I J))
  simp

/-- Evaluating `(e.toRiemannianIsometry I J).symm` agrees with `e.symm`. -/
@[simp]
theorem coe_toRiemannianIsometry_symm (e : M ≃ᵢ N) :
    ⇑(e.toRiemannianIsometry I J).symm = ⇑e.symm := by
  rw [← toRiemannianIsometry_symm, coe_toRiemannianIsometry]

/-- Promoting the identity metric equivalence gives the identity smooth Riemannian isometry. -/
@[simp]
theorem toRiemannianIsometry_refl :
    (IsometryEquiv.refl M).toRiemannianIsometry I I = TauCeti.RiemannianIsometry.refl I M := by
  ext x
  simp only [toRiemannianIsometry_apply, TauCeti.RiemannianIsometry.refl_apply,
    IsometryEquiv.coe_eq_toEquiv, IsometryEquiv.refl, Equiv.refl_apply]

/-- Forgetting smoothness after `toRiemannianIsometry` recovers the original metric equivalence. -/
@[simp]
theorem toIsometryEquiv_toRiemannianIsometry (e : M ≃ᵢ N) :
    ((e.toRiemannianIsometry I J : TauCeti.RiemannianIsometry I J M N) : M ≃ᵢ N) = e := by
  ext x
  rfl

/-- Promoting `1 : M ≃ᵢ M` gives `1 : TauCeti.Isom I M`. -/
@[simp]
theorem toRiemannianIsometry_one :
    (1 : M ≃ᵢ M).toRiemannianIsometry I I = (1 : TauCeti.Isom I M) := by
  ext x
  simp

/-- Promoting a product in `M ≃ᵢ M` gives the product in `TauCeti.Isom I M`. -/
@[simp]
theorem toRiemannianIsometry_mul (e₁ e₂ : M ≃ᵢ M) :
    (e₁ * e₂).toRiemannianIsometry I I =
      e₁.toRiemannianIsometry I I * e₂.toRiemannianIsometry I I := by
  ext x
  simp

/-- Promoting an inverse in `M ≃ᵢ M` gives the inverse in `TauCeti.Isom I M`. -/
@[simp]
theorem toRiemannianIsometry_inv (e : M ≃ᵢ M) :
    e⁻¹.toRiemannianIsometry I I = (e.toRiemannianIsometry I I)⁻¹ :=
  eq_inv_of_mul_eq_one_left
    (by rw [← toRiemannianIsometry_mul, inv_mul_cancel, toRiemannianIsometry_one])

/-- Promoting a quotient in `M ≃ᵢ M` gives the quotient in `TauCeti.Isom I M`. -/
@[simp]
theorem toRiemannianIsometry_div (e₁ e₂ : M ≃ᵢ M) :
    (e₁ / e₂).toRiemannianIsometry I I =
      e₁.toRiemannianIsometry I I / e₂.toRiemannianIsometry I I := by
  simp [div_eq_mul_inv]

/-- Promoting a natural power in `M ≃ᵢ M` gives the natural power in `TauCeti.Isom I M`. -/
@[simp]
theorem toRiemannianIsometry_pow (e : M ≃ᵢ M) (n : ℕ) :
    (e ^ n).toRiemannianIsometry I I = e.toRiemannianIsometry I I ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih]

/-- Promoting an integer power in `M ≃ᵢ M` gives the integer power in `TauCeti.Isom I M`. -/
@[simp]
theorem toRiemannianIsometry_zpow (e : M ≃ᵢ M) (n : ℤ) :
    (e ^ n).toRiemannianIsometry I I = e.toRiemannianIsometry I I ^ n := by
  cases n with
  | ofNat n => simp
  | negSucc n => simp

variable
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners ℝ G H''} [K.Boundaryless]
  {P : Type*} [EMetricSpace P] [ChartedSpace H'' P]
  [RiemannianBundle (fun z : P ↦ TangentSpace K z)] [IsManifold K ∞ P]
  [IsContMDiffRiemannianBundle K ∞ G (fun z : P ↦ TangentSpace K z)]
  [IsRiemannianManifold K P]

variable (J) in
/-- Promoting a composite of metric equivalences agrees with composing the promoted smooth
Riemannian isometries. -/
theorem toRiemannianIsometry_trans (e₁ : M ≃ᵢ N) (e₂ : N ≃ᵢ P) :
    (e₁.trans e₂).toRiemannianIsometry I K =
      (e₁.toRiemannianIsometry I J).trans (e₂.toRiemannianIsometry J K) := by
  ext x
  simp

end IsometryEquiv

namespace Isometry

variable (I) in
/-- Every distance-preserving self-map of a compact smooth boundaryless Riemannian manifold is a
smooth Riemannian self-isometry. -/
def riemannianIsometryOfCompactSpace [CompactSpace M] {f : M → M} (hf : Isometry f) :
    TauCeti.Isom I M :=
  hf.isometryEquivOfCompactSpace.toRiemannianIsometry I I

/-- `hf.riemannianIsometryOfCompactSpace I` is `hf.isometryEquivOfCompactSpace` promoted via
`IsometryEquiv.toRiemannianIsometry`. -/
theorem riemannianIsometryOfCompactSpace_def [CompactSpace M] {f : M → M} (hf : Isometry f) :
    hf.riemannianIsometryOfCompactSpace I =
      hf.isometryEquivOfCompactSpace.toRiemannianIsometry I I :=
  (rfl)

/-- The underlying map of `hf.riemannianIsometryOfCompactSpace I` is `f`. -/
@[simp]
theorem coe_riemannianIsometryOfCompactSpace [CompactSpace M] {f : M → M} (hf : Isometry f) :
    ⇑(hf.riemannianIsometryOfCompactSpace I) = f := by
  simp [riemannianIsometryOfCompactSpace_def]

/-- Forgetting smoothness on `hf.riemannianIsometryOfCompactSpace I` recovers
`hf.isometryEquivOfCompactSpace`. -/
@[simp]
theorem toIsometryEquiv_riemannianIsometryOfCompactSpace [CompactSpace M] {f : M → M}
    (hf : Isometry f) :
    ((hf.riemannianIsometryOfCompactSpace I : TauCeti.Isom I M) : M ≃ᵢ M) =
      hf.isometryEquivOfCompactSpace := by
  simp [riemannianIsometryOfCompactSpace_def]

end Isometry

namespace TauCeti.RiemannianIsometry

/-- Promoting the underlying metric equivalence of a smooth Riemannian isometry recovers it. -/
@[simp]
theorem toRiemannianIsometry_toIsometryEquiv (Φ : RiemannianIsometry I J M N) :
    (Φ : M ≃ᵢ N).toRiemannianIsometry I J = Φ := by
  ext x
  rfl

variable (I J M N) in
/-- **Equivalence between smooth Riemannian isometries and metric equivalences.** -/
def isometryEquivEquiv : RiemannianIsometry I J M N ≃ (M ≃ᵢ N) where
  toFun Φ := (Φ : M ≃ᵢ N)
  invFun e := e.toRiemannianIsometry I J
  left_inv := toRiemannianIsometry_toIsometryEquiv
  right_inv := IsometryEquiv.toIsometryEquiv_toRiemannianIsometry

/-- `isometryEquivEquiv` sends a smooth Riemannian isometry to its underlying metric equivalence. -/
@[simp]
theorem isometryEquivEquiv_apply (Φ : RiemannianIsometry I J M N) :
    isometryEquivEquiv I J M N Φ = (Φ : M ≃ᵢ N) :=
  (rfl)

/-- `isometryEquivEquiv.symm` promotes a metric equivalence via `toRiemannianIsometry`. -/
@[simp]
theorem isometryEquivEquiv_symm_apply (e : M ≃ᵢ N) :
    (isometryEquivEquiv I J M N).symm e = e.toRiemannianIsometry I J :=
  (rfl)

/-- A map `f : M → N` between smooth boundaryless Riemannian manifolds is the underlying map of a
smooth Riemannian isometry if and only if it is a surjective metric isometry. -/
theorem exists_coe_eq_iff_isometry_and_surjective {f : M → N} :
    (∃ Φ : RiemannianIsometry I J M N, ⇑Φ = f) ↔ Isometry f ∧ Surjective f := by
  refine ⟨?_, fun ⟨hf, hsurj⟩ ↦ ?_⟩
  · rintro ⟨Φ, rfl⟩
    exact ⟨IsometryClass.isometry Φ, Φ.toDiffeomorph.surjective⟩
  · let e : M ≃ᵢ N :=
      { toEquiv := Equiv.ofBijective f ⟨hf.injective, hsurj⟩
        isometry_toFun := hf }
    exact ⟨e.toRiemannianIsometry I J, rfl⟩

/-- On a compact smooth boundaryless Riemannian manifold, a self-map `f : M → M` is the underlying
map of a smooth Riemannian self-isometry if and only if it preserves the Riemannian distance. -/
theorem exists_isom_coe_eq_iff_isometry [CompactSpace M] {f : M → M} :
    (∃ Φ : Isom I M, ⇑Φ = f) ↔ Isometry f :=
  exists_coe_eq_iff_isometry_and_surjective.trans
    ⟨And.left, fun hf ↦ ⟨hf, hf.surjective_of_compactSpace⟩⟩

/-- On a compact smooth boundaryless Riemannian manifold, the underlying maps of `Isom I M` are
precisely the metric isometries `M → M`. -/
theorem range_coe_isom [CompactSpace M] :
    range ((⇑) : Isom I M → M → M) = {f : M → M | Isometry f} :=
  Set.ext fun _ ↦ exists_isom_coe_eq_iff_isometry

variable (I M) in
/-- **Group isomorphism between `Isom I M` and `M ≃ᵢ M`.** -/
def isometryEquivMulEquiv : Isom I M ≃* (M ≃ᵢ M) where
  toEquiv := isometryEquivEquiv I I M M
  map_mul' _ _ := by
    ext x
    simp

/-- The underlying equivalence of `isometryEquivMulEquiv` is `isometryEquivEquiv`. -/
@[simp]
theorem toEquiv_isometryEquivMulEquiv :
    (isometryEquivMulEquiv I M : Isom I M ≃ (M ≃ᵢ M)) = isometryEquivEquiv I I M M :=
  (rfl)

-- See note [hom simp lemma priority]
/-- `isometryEquivMulEquiv` sends an element of `Isom I M` to its metric equivalence. -/
@[simp low]
theorem isometryEquivMulEquiv_apply (Φ : Isom I M) :
    isometryEquivMulEquiv I M Φ = (Φ : M ≃ᵢ M) :=
  (rfl)

-- See note [hom simp lemma priority]
/-- `isometryEquivMulEquiv.symm` promotes a self-metric equivalence via `toRiemannianIsometry`. -/
@[simp low]
theorem isometryEquivMulEquiv_symm_apply (e : M ≃ᵢ M) :
    (isometryEquivMulEquiv I M).symm e = e.toRiemannianIsometry I I :=
  (rfl)

end TauCeti.RiemannianIsometry

end Differential

/-! ### Identification of the weak Whitney topology with the compact-open topology -/

section ContinuousToIsometryEquiv

open scoped TauCeti.DiffeomorphWeakWhitney TauCeti.RiemannianIsometryWeakWhitney

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsRiemannianManifold I M] [CompactSpace M]
  {N : Type*} [PseudoEMetricSpace N] [ChartedSpace H' N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)] [IsManifold J ∞ N]
  [IsRiemannianManifold J N]

/-- Forgetting smoothness is continuous from the weak Whitney `C^∞` topology on
`TauCeti.RiemannianIsometry I J M N` to the compact-open topology on `M ≃ᵢ N`. -/
theorem TauCeti.RiemannianIsometry.continuous_toIsometryEquiv :
    Continuous (fun Φ : TauCeti.RiemannianIsometry I J M N ↦ (Φ : M ≃ᵢ N)) :=
  IsometryEquiv.continuous_iff.2 fun x ↦
    (Diffeomorph.continuous_eval_const x).comp
      TauCeti.RiemannianIsometry.isEmbedding_toDiffeomorph.continuous

end ContinuousToIsometryEquiv

section ChartEdistSqParam

open TauCeti TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {M : Type*} [EMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

/-- Smoothness at `((z₀ : E), fun i ↦ extChartAt I (a₀ i) (a₀ i))` of the local squared-distance
coordinate formula `q ↦ extChartAt J y (Φ.symm fun i ↦ (edist ...).toReal ^ 2)`. -/
private theorem contDiffAt_chart_edist_sq_param {x : M} {y : N}
    (z₀ : (extChartAt I x).target) {WMo : Set M} {r : ℝ} (hWMo : IsOpen WMo)
    (hWM_norm : ∀ q ∈ WMo, IsNormalDomain I M q (Metric.ball 0 r)) {d : ℕ}
    {a₀ : Fin d → M}
    (ha₀ : ∀ i, a₀ i ∈ WMo ∧ edist (a₀ i) ((extChartAt I x).symm z₀) < ENNReal.ofReal r)
    {Φ : PartialDiffeomorph J 𝓘(ℝ, Fin d → ℝ) N (Fin d → ℝ) ∞} {q₀ : N}
    (hq₀_src : q₀ ∈ Φ.source) (hq₀_ext : q₀ ∈ (extChartAt J y).source)
    (hcoord₀ :
      (fun i ↦ (edist (a₀ i) ((extChartAt I x).symm z₀)).toReal ^ 2) = Φ q₀) :
    ContDiffAt ℝ ∞
      (fun q : E × (Fin d → E) ↦
        extChartAt J y (Φ.symm fun i ↦
          (edist ((extChartAt I (a₀ i)).symm (q.2 i))
            ((extChartAt I x).symm q.1)).toReal ^ 2))
      ((z₀ : E), fun i ↦ extChartAt I (a₀ i) (a₀ i)) := by
  set b₀ : E := (z₀ : E)
  set ξ₀ : Fin d → E := fun i ↦ extChartAt I (a₀ i) (a₀ i)
  let coordTuple : E × (Fin d → E) → Fin d → ℝ := fun q i ↦
    (edist ((extChartAt I (a₀ i)).symm (q.2 i)) ((extChartAt I x).symm q.1)).toReal ^ 2
  have hcoord_b₀ξ₀ : coordTuple (b₀, ξ₀) = Φ q₀ := by
    simpa only [coordTuple, ξ₀, b₀, extChartAt_to_inv] using hcoord₀
  have h1 : ContMDiffAt 𝓘(ℝ, E × (Fin d → E)) I ∞
      (fun q : E × (Fin d → E) ↦ (extChartAt I x).symm q.1) (b₀, ξ₀) :=
    ((contMDiffOn_extChartAt_symm x).contMDiffAt
      ((isOpen_extChartAt_target x).mem_nhds z₀.2)).comp (b₀, ξ₀) contDiffAt_fst.contMDiffAt
  have htuple : ContMDiffAt 𝓘(ℝ, E × (Fin d → E)) 𝓘(ℝ, Fin d → ℝ) ∞ coordTuple (b₀, ξ₀) := by
    refine (contDiffAt_pi.2 fun i ↦ ?_).contMDiffAt
    have hproj : ContMDiffAt 𝓘(ℝ, E × (Fin d → E)) 𝓘(ℝ, E) ∞
        (fun q : E × (Fin d → E) ↦ q.2 i) (b₀, ξ₀) :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d ↦ E) i).contDiff.contDiffAt.comp
        (b₀, ξ₀) contDiffAt_snd).contMDiffAt
    have h2 : ContMDiffAt 𝓘(ℝ, E × (Fin d → E)) I ∞
        (fun q : E × (Fin d → E) ↦ (extChartAt I (a₀ i)).symm (q.2 i)) (b₀, ξ₀) :=
      ((contMDiffOn_extChartAt_symm (a₀ i)).contMDiffAt
        ((isOpen_extChartAt_target (a₀ i)).mem_nhds (mem_extChartAt_target (a₀ i)))).comp
        (b₀, ξ₀) hproj
    have hdSq := contMDiffAt_toReal_edist_sq hWMo hWM_norm (ha₀ i).1 (ha₀ i).2
    have hval : ((extChartAt I (a₀ i)).symm (ξ₀ i), (extChartAt I x).symm b₀) =
        (a₀ i, (extChartAt I x).symm z₀) :=
      Prod.ext (extChartAt_to_inv (a₀ i)) rfl
    exact contMDiffAt_iff_contDiffAt.mp (hdSq.comp_of_eq (h2.prodMk h1) hval)
  have hΦsymm : ContMDiffAt 𝓘(ℝ, Fin d → ℝ) J ∞ Φ.symm (coordTuple (b₀, ξ₀)) := by
    rw [hcoord_b₀ξ₀]
    exact Φ.symm.contMDiffOn.contMDiffAt (Φ.open_target.mem_nhds (Φ.map_source hq₀_src))
  have hval_N : Φ.symm (coordTuple (b₀, ξ₀)) = q₀ := by
    rw [hcoord_b₀ξ₀]
    exact Φ.left_inv hq₀_src
  have hq₀_chart : q₀ ∈ (chartAt H' y).source := by rwa [extChartAt_source] at hq₀_ext
  have hextJ : ContMDiffAt J 𝓘(ℝ, F) ∞ (extChartAt J y) q₀ := contMDiffAt_extChartAt' hq₀_chart
  exact contMDiffAt_iff_contDiffAt.mp (hextJ.comp_of_eq (hΦsymm.comp (b₀, ξ₀) htuple) hval_N)

end ChartEdistSqParam

section JetParam

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

/-- If a family `g : P → M → N` has coordinate representative locally equal to `Fmap (·, ξ p)` for
a `C^∞` map `Fmap` and a parameter map `ξ` continuous at `p₀`, then its chart `m`-jet stays inside
any open set `V` containing the `m`-jet at `(p₀, z₀)`. -/
private theorem tendsto_chartJet_of_local_param {P : Type*} [TopologicalSpace P]
    {g : P → M → N} {p₀ : P} {x : M} {y : N} {m : ℕ} {z₀ : (extChartAt I x).target}
    {V : Set (E [×m]→L[ℝ] F)} (hV : IsOpen V) {d : ℕ} {Fmap : E × (Fin d → E) → F}
    {ξ : P → Fin d → E} {Up : Set P} {Ub : Set E} (hUp : IsOpen Up) (hp₀ : p₀ ∈ Up)
    (hUb : IsOpen Ub) (hz₀ : (z₀ : E) ∈ Ub) (hξ : ContinuousAt ξ p₀)
    (hF : ContDiffAt ℝ ∞ Fmap ((z₀ : E), ξ p₀))
    (hagree : ∀ ⦃p : P⦄, p ∈ Up → ∀ ⦃b : E⦄, b ∈ Ub →
      g p ((extChartAt I x).symm b) ∈ (extChartAt J y).source ∧
        extChartAt J y (g p ((extChartAt I x).symm b)) = Fmap (b, ξ p))
    (hV₀ : iteratedFDerivWithin ℝ m (extChartAt J y ∘ g p₀ ∘ (extChartAt I x).symm)
      (extChartAt I x).target z₀ ∈ V) :
    ∀ᶠ q : P × (extChartAt I x).target in 𝓝 (p₀, z₀),
      g q.1 ((extChartAt I x).symm q.2) ∈ (extChartAt J y).source ∧
        iteratedFDerivWithin ℝ m (extChartAt J y ∘ g q.1 ∘ (extChartAt I x).symm)
          (extChartAt I x).target q.2 ∈ V := by
  obtain ⟨W_F, hWF_nhds, hFW⟩ := hF.contDiffOn (m := (m : WithTop ℕ∞)) (by simp) (by simp)
  obtain ⟨W_Fo, hWFo_sub, hWFo_open, h₀_W⟩ := _root_.mem_nhds_iff.1 hWF_nhds
  have hpart_cont : ContinuousAt
      (fun q : E × (Fin d → E) ↦ iteratedFDeriv ℝ m (fun b ↦ Fmap (b, q.2)) q.1)
      ((z₀ : E), ξ p₀) :=
    ((hFW.mono hWFo_sub).continuousOn_iteratedFDeriv_partial hWFo_open le_rfl).continuousAt
      (hWFo_open.mem_nhds h₀_W)
  let Θ : P × (extChartAt I x).target → E × (Fin d → E) := fun q ↦ (q.2, ξ q.1)
  have hΘ0 : Θ (p₀, z₀) = ((z₀ : E), ξ p₀) := rfl
  have hΘ_cont : ContinuousAt Θ (p₀, z₀) :=
    (continuous_subtype_val.comp continuous_snd).continuousAt.prodMk
      (hξ.comp continuous_fst.continuousAt)
  have hjet_eq {p : P} (hp : p ∈ Up) {z : (extChartAt I x).target} (hz : (z : E) ∈ Ub) :
      iteratedFDerivWithin ℝ m (extChartAt J y ∘ g p ∘ (extChartAt I x).symm)
          (extChartAt I x).target z =
        iteratedFDeriv ℝ m (fun b ↦ Fmap (b, (Θ (p, z)).2)) (Θ (p, z)).1 := by
    rw [iteratedFDerivWithin_of_isOpen m (isOpen_extChartAt_target x) z.2]
    have hev : (extChartAt J y ∘ g p ∘ (extChartAt I x).symm) =ᶠ[𝓝 (z : E)]
        fun b ↦ Fmap (b, (Θ (p, z)).2) :=
      eventually_of_mem (hUb.mem_nhds hz) fun b hb ↦ (hagree hp hb).2
    exact (hev.iteratedFDeriv ℝ m).eq_of_nhds
  have hV_at_0 : iteratedFDeriv ℝ m (fun b ↦ Fmap (b, ξ p₀)) (z₀ : E) ∈ V := by
    have h := hjet_eq hp₀ hz₀
    rw [hΘ0] at h
    rwa [← h]
  have hev_V : ∀ᶠ q : P × (extChartAt I x).target in 𝓝 (p₀, z₀),
      iteratedFDeriv ℝ m (fun b ↦ Fmap (b, (Θ q).2)) (Θ q).1 ∈ V :=
    (hpart_cont.comp_of_eq hΘ_cont hΘ0).preimage_mem_nhds (hV.mem_nhds hV_at_0)
  have hev_UpUb : ∀ᶠ q : P × (extChartAt I x).target in 𝓝 (p₀, z₀),
      q.1 ∈ Up ∧ (q.2 : E) ∈ Ub :=
    (hUp.prod (hUb.preimage continuous_subtype_val)).mem_nhds ⟨hp₀, hz₀⟩
  filter_upwards [hev_UpUb, hev_V] with ⟨p, z⟩ ⟨hp, hz⟩ hVz
  exact ⟨(hagree hp hz).1, (hjet_eq hp hz).symm ▸ hVz⟩

end JetParam

section WeakWhitney

open TauCeti TauCeti.Manifold
open scoped TauCeti.ManifoldWeakWhitney TauCeti.DiffeomorphWeakWhitney
  TauCeti.RiemannianIsometryWeakWhitney

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
  {M : Type*} [EMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]
  {N : Type*} [EMetricSpace N] [ChartedSpace H' N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)] [IsManifold J ∞ N]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]
  [IsRiemannianManifold J N]

/-- Near `(e₀, z₀)`, the coordinate representative `extChartAt J y ∘ e ∘ (extChartAt I x).symm`
equals `Fmap (·, ξ e)` for a `C^∞` map `Fmap` and a continuous parameter map `ξ`. -/
private theorem IsometryEquiv.exists_contDiffAt_chart_param (e₀ : M ≃ᵢ N) {x : M} {y : N}
    (z₀ : (extChartAt I x).target)
    (he₀z₀ : e₀ ((extChartAt I x).symm z₀) ∈ (extChartAt J y).source) :
    ∃ (d : ℕ) (Fmap : E × (Fin d → E) → F) (ξ : (M ≃ᵢ N) → Fin d → E)
      (Ue : Set (M ≃ᵢ N)) (Ub : Set E),
      IsOpen Ue ∧ e₀ ∈ Ue ∧ IsOpen Ub ∧ (z₀ : E) ∈ Ub ∧
      ContinuousAt ξ e₀ ∧ ContDiffAt ℝ ∞ Fmap ((z₀ : E), ξ e₀) ∧
      ∀ ⦃e : M ≃ᵢ N⦄, e ∈ Ue → ∀ ⦃b : E⦄, b ∈ Ub →
        e ((extChartAt I x).symm b) ∈ (extChartAt J y).source ∧
          extChartAt J y (e ((extChartAt I x).symm b)) = Fmap (b, ξ e) := by
  set p₀ : M := (extChartAt I x).symm z₀
  obtain ⟨r, hr, WM, hWM_nhds, hWM⟩ :=
    exists_mem_nhds_forall_isNormalDomain_ball (I := I) (M := M) p₀
  obtain ⟨WMo, hWMo_sub, hWMo_open, hp₀WMo⟩ := mem_nhds_iff.1 hWM_nhds
  have hr2 : 0 < ENNReal.ofReal (r / 2) := ENNReal.ofReal_pos.2 (half_pos hr)
  -- Pick a squared-distance chart `Φ` on `N` around `e₀ p₀` inside `(extChartAt J y).source` whose
  -- centres `yN i` pull back under `e₀.symm` into `WMo ∩ eball p₀ (r / 2)`.
  have hsN : (e₀.toHomeomorph '' (WMo ∩ eball p₀ (ENNReal.ofReal (r / 2)))) ∩
      (extChartAt J y).source ∈ 𝓝 (e₀ p₀) := by
    refine inter_mem ?_ ((isOpen_extChartAt_source y).mem_nhds he₀z₀)
    exact e₀.toHomeomorph.isOpenMap.image_mem_nhds
      ((hWMo_open.inter Metric.isOpen_eball).mem_nhds ⟨hp₀WMo, Metric.mem_eball_self hr2⟩)
  set d := Module.finrank ℝ F
  obtain ⟨yN, Φ, hyN_mem, he₀p₀_src, hΦ_sub, hΦ_eq⟩ :=
    exists_partialDiffeomorph_pi_toReal_edist_sq (I := J) (M := N) (e₀ p₀) hsN
  set a₀ : Fin d → M := fun i ↦ e₀.symm (yN i)
  have ha₀_mem (i : Fin d) : a₀ i ∈ WMo ∧ edist (a₀ i) p₀ < ENNReal.ofReal r := by
    obtain ⟨⟨q, ⟨hqW, hqball⟩, hqe⟩, -⟩ := hyN_mem i
    have hqa : q = a₀ i := by simp [a₀, ← hqe]
    refine ⟨hqa ▸ hqW, (hqa ▸ Metric.mem_eball.1 hqball).trans ?_⟩
    exact (ENNReal.ofReal_lt_ofReal_iff hr).2 (half_lt_self hr)
  let Fmap : E × (Fin d → E) → F := fun q ↦
    extChartAt J y (Φ.symm fun i ↦
      (edist ((extChartAt I (a₀ i)).symm (q.2 i)) ((extChartAt I x).symm q.1)).toReal ^ 2)
  let ξ : (M ≃ᵢ N) → Fin d → E := fun e i ↦ extChartAt I (a₀ i) (e.symm (yN i))
  have hcoord₀ : (fun i ↦ (edist (a₀ i) p₀).toReal ^ 2) = Φ (e₀ p₀) := by
    rw [hΦ_eq (e₀ p₀) he₀p₀_src]
    ext i
    have hiso : edist (yN i) (e₀ p₀) = edist (a₀ i) p₀ := by
      simpa only [a₀, e₀.apply_symm_apply] using e₀.edist_eq (e₀.symm (yN i)) p₀
    rw [hiso]
  have hF_smooth : ContDiffAt ℝ ∞ Fmap ((z₀ : E), ξ e₀) :=
    contDiffAt_chart_edist_sq_param z₀ hWMo_open (fun q hq ↦ (hWM q (hWMo_sub hq)).1) ha₀_mem
      he₀p₀_src he₀z₀ hcoord₀
  have hsymm_cont (i : Fin d) : Continuous (fun e : M ≃ᵢ N ↦ e.symm (yN i)) :=
    IsometryEquiv.continuous_iff.1 IsometryEquiv.continuous_symm (yN i)
  have hξ_cont : ContinuousAt ξ e₀ :=
    continuousAt_pi.2 fun i ↦
      (continuousAt_extChartAt (a₀ i)).comp_of_eq (hsymm_cont i).continuousAt rfl
  have heval_cont : Continuous (fun p : (M ≃ᵢ N) × (extChartAt I x).target ↦
      p.1 ((extChartAt I x).symm p.2)) :=
    continuous_fst.eval (((continuousOn_extChartAt_symm x).domRestrict).comp continuous_snd)
  obtain ⟨Ue₁, Uz, hUe₁o, hUzo, he₀Ue₁, hz₀Uz, hUeUz⟩ :=
    isOpen_prod_iff.1 (Φ.open_source.preimage heval_cont) e₀ z₀ he₀p₀_src
  obtain ⟨Ub', hUb'o, hUb'_eq⟩ := isOpen_induced_iff.1 hUzo
  set Ub : Set E := (extChartAt I x).target ∩ Ub'
  have hUbo : IsOpen Ub := (isOpen_extChartAt_target x).inter hUb'o
  have hb₀Ub : (z₀ : E) ∈ Ub := ⟨z₀.2, by rwa [← hUb'_eq] at hz₀Uz⟩
  set Ue : Set (M ≃ᵢ N) :=
    Ue₁ ∩ ⋂ i : Fin d, (fun e : M ≃ᵢ N ↦ e.symm (yN i)) ⁻¹' (extChartAt I (a₀ i)).source
  have hUeo : IsOpen Ue := hUe₁o.inter <| isOpen_iInter_of_finite fun i ↦
    (isOpen_extChartAt_source (a₀ i)).preimage (hsymm_cont i)
  have he₀Ue : e₀ ∈ Ue := ⟨he₀Ue₁, mem_iInter.2 fun i ↦ mem_extChartAt_source (a₀ i)⟩
  refine ⟨d, Fmap, ξ, Ue, Ub, hUeo, he₀Ue, hUbo, hb₀Ub, hξ_cont, hF_smooth, fun e he b hb ↦ ?_⟩
  have hzb : (⟨b, hb.1⟩ : (extChartAt I x).target) ∈ Uz := by rw [← hUb'_eq]; exact hb.2
  have hmemΦ : e ((extChartAt I x).symm b) ∈ Φ.source := hUeUz (mk_mem_prod he.1 hzb)
  refine ⟨(hΦ_sub hmemΦ).2, ?_⟩
  have hct : (fun i ↦
      (edist ((extChartAt I (a₀ i)).symm (ξ e i)) ((extChartAt I x).symm b)).toReal ^ 2) =
      Φ (e ((extChartAt I x).symm b)) := by
    rw [hΦ_eq _ hmemΦ]
    ext i
    have hi_src : e.symm (yN i) ∈ (extChartAt I (a₀ i)).source := mem_iInter.1 he.2 i
    simp only [ξ, (extChartAt I (a₀ i)).left_inv hi_src]
    have hiso : edist (yN i) (e ((extChartAt I x).symm b)) =
        edist (e.symm (yN i)) ((extChartAt I x).symm b) := by
      simpa only [e.apply_symm_apply] using e.edist_eq (e.symm (yN i)) ((extChartAt I x).symm b)
    rw [hiso]
  dsimp only [Fmap]
  rw [hct]
  exact congrArg (extChartAt J y) (Φ.left_inv hmemΦ).symm

/-- Promoting a metric equivalence `e : M ≃ᵢ N` between smooth boundaryless Riemannian manifolds
to a smooth map `C^∞⟮I, M; J, N⟯` is continuous from the compact-open topology to the weak Whitney
`C^∞` topology. -/
theorem IsometryEquiv.continuous_toContMDiffMap :
    Continuous fun e : M ≃ᵢ N ↦ (e.toRiemannianIsometry I J).toDiffeomorph.toContMDiffMap := by
  refine continuous_iff_continuousAt.2 fun e₀ ↦ ?_
  refine ContMDiffMap.tendsto_manifoldWeakWhitney_iff.2 fun x y m _ K hK V hV h₀ ↦ ?_
  simp only [ContMDiffMap.mem_chartJetSet, Diffeomorph.coe_coe,
    RiemannianIsometry.coe_toDiffeomorph, IsometryEquiv.coe_toRiemannianIsometry] at h₀ ⊢
  refine hK.eventually_forall_of_forall_eventually fun z₀ hz₀ ↦ ?_
  obtain ⟨d, Fmap, ξ, Ue, Ub, hUeo, he₀, hUbo, hz₀Ub, hξ, hF, hagree⟩ :=
    e₀.exists_contDiffAt_chart_param (I := I) (J := J) z₀ (h₀ z₀ hz₀).1
  exact tendsto_chartJet_of_local_param (I := I) (J := J) hV hUeo he₀ hUbo hz₀Ub hξ hF hagree
    (h₀ z₀ hz₀).2

variable [CompactSpace M]

/-- Promoting a metric equivalence `M ≃ᵢ N` on a compact Riemannian manifold `M` to a smooth
Riemannian isometry is continuous from the compact-open topology to the weak Whitney `C^∞`
topology. -/
theorem IsometryEquiv.continuous_toRiemannianIsometry :
    Continuous (IsometryEquiv.toRiemannianIsometry I J :
      (M ≃ᵢ N) → RiemannianIsometry I J M N) :=
  RiemannianIsometry.continuous_weakWhitney_iff.2
    (Diffeomorph.continuous_weakWhitney_iff.2 IsometryEquiv.continuous_toContMDiffMap)

namespace TauCeti.RiemannianIsometry

variable (I J M N) in
/-- **Homeomorphism between smooth Riemannian isometries and metric equivalences.** On a compact
smooth boundaryless Riemannian manifold `M`, the weak Whitney `C^∞` topology on
`RiemannianIsometry I J M N` agrees with the compact-open topology on `M ≃ᵢ N`. -/
def isometryEquivHomeomorph : RiemannianIsometry I J M N ≃ₜ (M ≃ᵢ N) where
  toEquiv := isometryEquivEquiv I J M N
  continuous_toFun := continuous_toIsometryEquiv
  continuous_invFun := IsometryEquiv.continuous_toRiemannianIsometry

/-- The underlying equivalence of `isometryEquivHomeomorph` is `isometryEquivEquiv`. -/
@[simp]
theorem toEquiv_isometryEquivHomeomorph :
    (isometryEquivHomeomorph I J M N).toEquiv = isometryEquivEquiv I J M N :=
  (rfl)

/-- `isometryEquivHomeomorph` sends a smooth Riemannian isometry to its metric equivalence. -/
@[simp]
theorem isometryEquivHomeomorph_apply (Φ : RiemannianIsometry I J M N) :
    isometryEquivHomeomorph I J M N Φ = (Φ : M ≃ᵢ N) :=
  (rfl)

/-- `isometryEquivHomeomorph.symm` promotes a metric equivalence via `toRiemannianIsometry`. -/
@[simp]
theorem isometryEquivHomeomorph_symm_apply (e : M ≃ᵢ N) :
    (isometryEquivHomeomorph I J M N).symm e = e.toRiemannianIsometry I J :=
  (rfl)

variable (I M) in
/-- **Topological group isomorphism between `Isom I M` and `M ≃ᵢ M`.** On a compact smooth
boundaryless Riemannian manifold `M`, the smooth isometry group `Isom I M` with the weak Whitney
`C^∞` topology is isomorphic as a topological group to the metric isometry group `M ≃ᵢ M` with the
compact-open topology. -/
def isometryEquivContinuousMulEquiv : Isom I M ≃ₜ* (M ≃ᵢ M) :=
  { isometryEquivMulEquiv I M, isometryEquivHomeomorph I I M M with }

/-- The underlying multiplicative equivalence of `isometryEquivContinuousMulEquiv` is
`isometryEquivMulEquiv`. -/
@[simp]
theorem toMulEquiv_isometryEquivContinuousMulEquiv :
    (isometryEquivContinuousMulEquiv I M : Isom I M ≃* (M ≃ᵢ M)) = isometryEquivMulEquiv I M :=
  (rfl)

/-- The underlying homeomorphism of `isometryEquivContinuousMulEquiv` is
`isometryEquivHomeomorph`. -/
@[simp]
theorem toHomeomorph_isometryEquivContinuousMulEquiv :
    (isometryEquivContinuousMulEquiv I M).toHomeomorph = isometryEquivHomeomorph I I M M :=
  (rfl)

-- See note [hom simp lemma priority]
/-- `isometryEquivContinuousMulEquiv` sends an element of `Isom I M` to its metric equivalence. -/
@[simp low]
theorem isometryEquivContinuousMulEquiv_apply (Φ : Isom I M) :
    isometryEquivContinuousMulEquiv I M Φ = (Φ : M ≃ᵢ M) :=
  (rfl)

-- See note [hom simp lemma priority]
/-- `isometryEquivContinuousMulEquiv.symm` promotes a self-metric equivalence via
`toRiemannianIsometry`. -/
@[simp low]
theorem isometryEquivContinuousMulEquiv_symm_apply (e : M ≃ᵢ M) :
    (isometryEquivContinuousMulEquiv I M).symm e = e.toRiemannianIsometry I I :=
  (rfl)

end TauCeti.RiemannianIsometry

end WeakWhitney

section CompactWeakWhitney

open TauCeti
open scoped TauCeti.RiemannianIsometryWeakWhitney

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [CompactSpace M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)] [IsManifold J ∞ N]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]

/-- **Compactness of the space of Riemannian isometries in the weak Whitney topology.** When `M` is
a compact Hausdorff smooth boundaryless Riemannian manifold, `RiemannianIsometry I J M N` (and in
particular `Isom I M`) is compact in the weak Whitney `C^∞` topology. -/
theorem TauCeti.RiemannianIsometry.compactSpace_weakWhitney :
    CompactSpace (RiemannianIsometry I J M N) := by
  cases isEmpty_or_nonempty (RiemannianIsometry I J M N) with
  | inl => infer_instance
  | inr h =>
    obtain ⟨Φ₀⟩ := h
    have : CompactSpace N := Φ₀.toDiffeomorph.toHomeomorph.compactSpace
    have : T2Space N := Φ₀.toDiffeomorph.toHomeomorph.symm.isEmbedding.t2Space
    have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞) (F := E)
      (V := fun x : M ↦ TangentSpace I x)
    have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := J) (n := ∞) (F := F)
      (V := fun y : N ↦ TangentSpace J y)
    let : EMetricSpace M := .ofRiemannianMetric I M
    let : EMetricSpace N := .ofRiemannianMetric J N
    exact (TauCeti.RiemannianIsometry.isometryEquivHomeomorph I J M N).symm.compactSpace

scoped[TauCeti.RiemannianIsometryWeakWhitney] attribute [instance]
  TauCeti.RiemannianIsometry.compactSpace_weakWhitney

end CompactWeakWhitney

end
