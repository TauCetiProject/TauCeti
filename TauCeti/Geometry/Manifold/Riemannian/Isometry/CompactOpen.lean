/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Smooth
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Topology
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.DistanceChart
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Segment
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Uniform

/-!
# Identification of the weak Whitney and compact-open topologies on Riemannian isometries

On a compact smooth boundaryless Riemannian manifold `M`, the weak Whitney `C^∞` topology on smooth
Riemannian isometries `TauCeti.RiemannianIsometry I J M N` agrees with the compact-open topology on
metric equivalences `M ≃ᵢ N`, and `TauCeti.RiemannianIsometry I J M N` (in particular
`TauCeti.Isom I M`) is compact in the weak Whitney topology when `M` is Hausdorff.

For a family of metric equivalences `e : M ≃ᵢ N`, expressing `e` locally via a squared-distance
chart `Φ` on `N` as `Φ.symm (fun i ↦ (edist (e.symm (y i)) ·).toReal ^ 2)` writes the coordinate
representative of `e` as a smooth function of the evaluation points `e.symm (y i)` and the source
chart coordinate. Since inversion and evaluation are continuous in the compact-open topology on
`M ≃ᵢ N`, all chart iterated derivatives vary continuously with `e`
(`IsometryEquiv.continuous_toContMDiffMap`). Combining this with continuity of the forgetful map and
the van Dantzig–van der Waerden theorem (`IsometryEquiv.instCompactSpace`) yields the topological
identifications and compactness.

## Main definitions

* `TauCeti.RiemannianIsometry.isometryEquivHomeomorph`: the homeomorphism
  `RiemannianIsometry I J M N ≃ₜ (M ≃ᵢ N)` between the weak Whitney topology and the compact-open
  topology when `M` is compact.
* `TauCeti.RiemannianIsometry.isometryEquivContinuousMulEquiv`: the topological group isomorphism
  `Isom I M ≃ₜ* (M ≃ᵢ M)` when `M` is compact.

## Main results

* `TauCeti.RiemannianIsometry.continuous_toIsometryEquiv`: forgetting smoothness is continuous from
  the weak Whitney `C^∞` topology to the compact-open topology.
* `IsometryEquiv.continuous_toContMDiffMap`, `IsometryEquiv.continuous_toRiemannianIsometry`:
  promoting metric equivalences is continuous from the compact-open topology into the weak Whitney
  `C^∞` topology.
* `TauCeti.RiemannianIsometry.compactSpace_weakWhitney`: `RiemannianIsometry I J M N` is compact
  in the weak Whitney topology when `M` is compact and Hausdorff.

## References

* S. B. Myers and N. E. Steenrod, *The group of isometries of a Riemannian manifold*, Ann. of
  Math. (2) 40 (1939), 400–416.
* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience, 1963,
  Ch. IV, Theorem 3.10.
* M. Taylor, *Measure Theory and Integration*, Graduate Studies in Mathematics 76, AMS, 2006,
  Appendix E; and *Finsler structures and smoothness of isometries*, Proc. Amer. Math. Soc. 134
  (2006), no. 8, 2419–2423.
* P. Petersen, *Riemannian Geometry*, 3rd ed., Springer GTM 171, 2016, §5.6.2.
-/

public section

open Bundle Filter Function Manifold Metric Set Topology
open scoped ContDiff ENNReal Manifold

noncomputable section

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
    ∃ (d : ℕ) (Fmap : E × (Fin d → E) → F) (ξ : (M ≃ᵢ N) → Fin d → E),
      ContinuousAt ξ e₀ ∧ ContDiffAt ℝ ∞ Fmap ((z₀ : E), ξ e₀) ∧
      ∀ᶠ q : (M ≃ᵢ N) × (extChartAt I x).target in 𝓝 (e₀, z₀),
        q.1 ((extChartAt I x).symm q.2) ∈ (extChartAt J y).source ∧
          extChartAt J y (q.1 ((extChartAt I x).symm q.2)) = Fmap (q.2, ξ q.1) := by
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
  set Ue : Set (M ≃ᵢ N) :=
    Ue₁ ∩ ⋂ i : Fin d, (fun e : M ≃ᵢ N ↦ e.symm (yN i)) ⁻¹' (extChartAt I (a₀ i)).source
  have hUeo : IsOpen Ue := hUe₁o.inter <| isOpen_iInter_of_finite fun i ↦
    (isOpen_extChartAt_source (a₀ i)).preimage (hsymm_cont i)
  have he₀Ue : e₀ ∈ Ue := ⟨he₀Ue₁, mem_iInter.2 fun i ↦ mem_extChartAt_source (a₀ i)⟩
  refine ⟨d, Fmap, ξ, hξ_cont, hF_smooth, ?_⟩
  filter_upwards [(hUeo.prod hUzo).mem_nhds ⟨he₀Ue, hz₀Uz⟩] with ⟨e, z⟩ ⟨he, hz⟩
  have hmemΦ : e ((extChartAt I x).symm z) ∈ Φ.source := hUeUz (mk_mem_prod he.1 hz)
  refine ⟨(hΦ_sub hmemΦ).2, ?_⟩
  have hct : (fun i ↦
      (edist ((extChartAt I (a₀ i)).symm (ξ e i)) ((extChartAt I x).symm z)).toReal ^ 2) =
      Φ (e ((extChartAt I x).symm z)) := by
    rw [hΦ_eq _ hmemΦ]
    ext i
    have hi_src : e.symm (yN i) ∈ (extChartAt I (a₀ i)).source := mem_iInter.1 he.2 i
    simp only [ξ, (extChartAt I (a₀ i)).left_inv hi_src]
    have hiso : edist (yN i) (e ((extChartAt I x).symm z)) =
        edist (e.symm (yN i)) ((extChartAt I x).symm z) := by
      simpa only [e.apply_symm_apply] using e.edist_eq (e.symm (yN i)) ((extChartAt I x).symm z)
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
  refine ContMDiffMap.tendsto_manifoldWeakWhitney_iff.2 fun x y m hm K hK V hV h₀ ↦ ?_
  simp only [ContMDiffMap.mem_chartJetSet, Diffeomorph.coe_coe,
    RiemannianIsometry.coe_toDiffeomorph, IsometryEquiv.coe_toRiemannianIsometry] at h₀ ⊢
  refine hK.eventually_forall_of_forall_eventually fun z₀ hz₀ ↦ ?_
  obtain ⟨d, Fmap, ξ, hξ, hF, hagree⟩ :=
    e₀.exists_contDiffAt_chart_param (I := I) (J := J) z₀ (h₀ z₀ hz₀).1
  refine (hagree.mono fun _ h ↦ h.1).and ?_
  exact (hF.continuousAt_iteratedFDerivWithin_extChartAt hξ
    (hagree.mono fun _ h ↦ h.2) m hm).eventually (hV.mem_nhds (h₀ z₀ hz₀).2)

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
  continuous_toFun := continuous_toIsometryEquiv.congr fun Φ ↦
    (isometryEquivEquiv_apply Φ).symm
  continuous_invFun := IsometryEquiv.continuous_toRiemannianIsometry.congr fun e ↦
    (isometryEquivEquiv_symm_apply e).symm

/-- The underlying equivalence of `isometryEquivHomeomorph` is `isometryEquivEquiv`. -/
@[simp]
theorem toEquiv_isometryEquivHomeomorph :
    (isometryEquivHomeomorph I J M N).toEquiv = isometryEquivEquiv I J M N :=
  (rfl)

/-- `isometryEquivHomeomorph` sends a smooth Riemannian isometry to its metric equivalence. -/
@[simp]
theorem isometryEquivHomeomorph_apply (Φ : RiemannianIsometry I J M N) :
    isometryEquivHomeomorph I J M N Φ = (Φ : M ≃ᵢ N) :=
  isometryEquivEquiv_apply Φ

/-- `isometryEquivHomeomorph.symm` promotes a metric equivalence via `toRiemannianIsometry`. -/
@[simp]
theorem isometryEquivHomeomorph_symm_apply (e : M ≃ᵢ N) :
    (isometryEquivHomeomorph I J M N).symm e = e.toRiemannianIsometry I J :=
  isometryEquivEquiv_symm_apply e

variable (I M) in
/-- **Topological group isomorphism between `Isom I M` and `M ≃ᵢ M`.** On a compact smooth
boundaryless Riemannian manifold `M`, the smooth isometry group `Isom I M` with the weak Whitney
`C^∞` topology is isomorphic as a topological group to the metric isometry group `M ≃ᵢ M` with the
compact-open topology. -/
def isometryEquivContinuousMulEquiv : Isom I M ≃ₜ* (M ≃ᵢ M) where
  toMulEquiv := isometryEquivMulEquiv I M
  continuous_toFun := (isometryEquivHomeomorph I I M M).continuous.congr fun Φ ↦ by simp
  continuous_invFun := (isometryEquivHomeomorph I I M M).continuous_symm.congr fun e ↦ by simp

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
    (isometryEquivContinuousMulEquiv I M).toHomeomorph = isometryEquivHomeomorph I I M M := by
  ext Φ x
  simp

-- See note [hom simp lemma priority]
/-- `isometryEquivContinuousMulEquiv` sends an element of `Isom I M` to its metric equivalence. -/
@[simp low]
theorem isometryEquivContinuousMulEquiv_apply (Φ : Isom I M) :
    isometryEquivContinuousMulEquiv I M Φ = (Φ : M ≃ᵢ M) :=
  isometryEquivMulEquiv_apply Φ

-- See note [hom simp lemma priority]
/-- `isometryEquivContinuousMulEquiv.symm` promotes a self-metric equivalence via
`toRiemannianIsometry`. -/
@[simp low]
theorem isometryEquivContinuousMulEquiv_symm_apply (e : M ≃ᵢ M) :
    (isometryEquivContinuousMulEquiv I M).symm e = e.toRiemannianIsometry I I :=
  isometryEquivMulEquiv_symm_apply e

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
