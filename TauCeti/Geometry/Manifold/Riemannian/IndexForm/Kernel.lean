/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.IndexForm.Piecewise
public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Conjugate.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.ExpKernel
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Smoothness
import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Smoothness
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Bootstrap
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Smoothness
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.ChartGram
import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongCurve.PrescribedValue
import TauCeti.Analysis.Distribution.DuBoisReymond

/-!
# Kernel and nullity of the geodesic index form

Let `γ` be a geodesic on `[a, b]` (`a < b`). Every Jacobi field along `γ` is index-orthogonal to
every continuous piecewise `C¹` section vanishing at `a` and `b`. Conversely, if a continuous
piecewise `C¹` section `V` along `γ` satisfies `I(V, W) = 0` for all smooth compactly supported
multiples of local sections `W` supported strictly inside `(a, b)`, then `V` is an unbroken `C²`
Jacobi field on `[a, b]` (Milnor, *Morse Theory*, Theorem 14.1):

1. On each `C¹` piece of `V`, testing against compactly supported smooth multiples of a chart-local
   frame and applying the du Bois-Reymond lemma gives `D_t V` a `C¹` lift via the dual chart frame;
   `CovariantDerivative.contMDiffOn_succ_of_alongCurveWithin` upgrades `V` to `C²` on the closed
   piece, and integration by parts forces the Jacobi equation there.
2. Broken-Jacobi integration by parts reduces `I(V, W)` to the negative sum of interior jump
   pairings; isolating each interior vertex with `exists_contDiff_smul_section_isolating_vertex`
   annihilates every jump, and `isJacobiFieldOn_Icc_of_partition` glues the pieces across `[a, b]`.

Restricting to `PiecewiseContMDiffSectionAlong.endpointZero` identifies the kernel of
`endpointZeroIndexForm` linearly with `endpointJacobiFieldSpace` for every `1 ≤ n ≤ ∞`
(`[ENat.LEInfty n]`). Thus its nullity is finite and equals `conjugateMultiplicity`, and
`endpointZeroIndexForm` is nondegenerate iff `a` and `b` are not conjugate along `γ` (along
`t ↦ exp_p(t v)` on a boundaryless manifold, iff `d(exp_p)_{b v}` is injective).

## Main definitions and results

* `TauCeti.Manifold.IsJacobiFieldOn.isPiecewiseContMDiffOn`: every Jacobi field on `[a, b]`
  (`a < b`) has a piecewise `C^n` tangent-bundle lift (`n ≤ ∞`), without boundarylessness.
* `TauCeti.Manifold.isJacobiFieldOn_Icc_of_indexForm_contDiff_smul_eq_zero`,
  `TauCeti.Manifold.isJacobiFieldOn_Icc_of_indexForm_contDiff_smul_eq_zero_of_piecewise`,
  `TauCeti.Manifold.isJacobiFieldOn_Icc_iff_forall_contMDiffOn_indexForm_eq_zero`, and
  `TauCeti.Manifold.isJacobiFieldOn_Icc_iff_forall_isPiecewiseContMDiffOn_indexForm_eq_zero`.
* `TauCeti.Manifold.endpointJacobiEquivIndexFormKer` and
  `TauCeti.Manifold.endpointZeroIndexFormKerEquivExpKer`: linear equivalences of
  `LinearMap.ker (endpointZeroIndexForm hγ hn)` with `endpointJacobiFieldSpace` and
  `ker(d(exp_p)_{b v})`.
* `TauCeti.Manifold.finrank_ker_endpointZeroIndexForm`,
  `TauCeti.Manifold.ker_endpointZeroIndexForm_ne_bot_iff_isConjugateOn`, and
  `TauCeti.Manifold.nondegenerate_endpointZeroIndexForm_iff`, with radial-exponential corollaries.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press (1963),
  Theorem 14.1, pp. 78–79.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Prop. 10.14.
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Chapter 10.
-/

public section

open Bundle CovariantDerivative Filter MeasureTheory Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-! ### Piecewise `C^n` regularity of Jacobi fields -/

/-- Every Jacobi field on `[a, b]` (`a < b`) has a piecewise `C^n` tangent-bundle lift on `[a, b]`
for every `n ≤ ∞`, without requiring `M` to be boundaryless. -/
theorem IsJacobiFieldOn.isPiecewiseContMDiffOn {n : ℕ∞ω} [ENat.LEInfty n]
    {γ : ℝ → M} {J : ∀ t, TangentSpace I (γ t)} {a b : ℝ} (hab : a < b)
    (h : IsJacobiFieldOn I γ J (Icc a b)) :
    IsPiecewiseContMDiffOn I.tangent n (fun r ↦ TotalSpace.mk' E (γ r) (J r)) a b :=
  .of_contMDiffOn hab (h.contMDiffOn_infty.of_le ENat.LEInfty.out)

/-! ### Variational bootstrap on a single piece -/

/-- Restricting `indexForm` from `[a, b]` to `[u, v] ⊆ [a, b]` when `W` vanishes outside
`(u, v)`. -/
private lemma indexForm_subinterval_eq_of_tsupport_subset
    {γ : ℝ → M} {V W : ∀ t, TangentSpace I (γ t)} {a u v b : ℝ}
    (hau : a ≤ u) (huv : u < v) (hvb : v ≤ b)
    (hV : IsPiecewiseContMDiffOn I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) a b)
    (hW : IsPiecewiseContMDiffOn I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (W r)) a b)
    (hW0 : ∀ t, t ∉ Ioo u v → W t = 0) :
    indexForm I γ V W u v = indexForm I γ V W a b := by
  have hleft : indexForm I γ V W a u = 0 := by
    rcases eq_or_lt_of_le hau with rfl | hau'
    · exact indexForm_same
    · exact (indexForm_congr (fun _ _ ↦ rfl) (fun _ _ ↦ HEq.rfl) fun t ht ↦ by
        rw [uIoo_of_lt hau'] at ht
        exact heq_of_eq (hW0 t fun h ↦ h.1.not_ge ht.2.le)).trans indexForm_zero_right
  have hright : indexForm I γ V W v b = 0 := by
    rcases eq_or_lt_of_le hvb with rfl | hvb'
    · exact indexForm_same
    · exact (indexForm_congr (fun _ _ ↦ rfl) (fun _ _ ↦ HEq.rfl) fun t ht ↦ by
        rw [uIoo_of_lt hvb'] at ht
        exact heq_of_eq (hW0 t fun h ↦ h.2.not_ge ht.1.le)).trans indexForm_zero_right
  have hi_au : IntervalIntegrable (indexFormIntegrand I γ V W) volume a u := by
    rcases eq_or_lt_of_le hau with rfl | hau'
    · exact IntervalIntegrable.refl
    · exact (hV.mono le_rfl hau' (huv.le.trans hvb)).intervalIntegrable_indexFormIntegrand
        (hW.mono le_rfl hau' (huv.le.trans hvb))
  have hi_uv := (hV.mono hau huv hvb).intervalIntegrable_indexFormIntegrand
    (hW.mono hau huv hvb)
  have hi_vb : IntervalIntegrable (indexFormIntegrand I γ V W) volume v b := by
    rcases eq_or_lt_of_le hvb with rfl | hvb'
    · exact IntervalIntegrable.refl
    · exact (hV.mono (hau.trans huv.le) hvb' le_rfl).intervalIntegrable_indexFormIntegrand
        (hW.mono (hau.trans huv.le) hvb' le_rfl)
  rw [← indexForm_add_adjacent_intervals (hi_au.trans hi_uv) hi_vb,
    ← indexForm_add_adjacent_intervals hi_au hi_uv, hleft, hright, zero_add, add_zero]

omit [FiniteDimensional ℝ E] [T2Space M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
variable (I) in
/-- Choosing a nondegenerate closed subinterval `[p, q] ⊆ [u, v]` that is a relative neighborhood
of `t₀ ∈ [u, v]` and maps under `γ` into the tangent-trivialization base set at `γ t₀`. -/
private lemma exists_subinterval_mapsTo_baseSet
    {γ : ℝ → M} {u v t₀ : ℝ}
    (huv : u < v) (hγ : ContinuousOn γ (Icc u v)) (ht₀ : t₀ ∈ Icc u v) :
    ∃ p q, u ≤ p ∧ p < q ∧ q ≤ v ∧ t₀ ∈ Icc p q ∧ Icc p q ∈ 𝓝[Icc u v] t₀ ∧
      MapsTo γ (Icc p q) (trivializationAt E (TangentSpace I) (γ t₀)).baseSet := by
  let e := trivializationAt E (TangentSpace I) (γ t₀)
  have hx₀ : γ t₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t₀)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1
    ((hγ t₀ ht₀).preimage_mem_nhdsWithin (e.open_baseSet.mem_nhds hx₀))
  let δ := ε / 2
  let p := max u (t₀ - δ)
  let q := min v (t₀ + δ)
  refine ⟨p, q, le_max_left _ _, ?_, min_le_left _ _, ?_, ?_, fun r hr ↦ ?_⟩
  · dsimp only [p, q, δ]
    exact max_lt (lt_min huv (by linarith [ht₀.1])) (lt_min (by linarith [ht₀.2]) (by linarith))
  · exact ⟨max_le ht₀.1 (by dsimp only [δ]; linarith), le_min ht₀.2 (by dsimp only [δ]; linarith)⟩
  · exact mem_nhdsWithin.2 ⟨Ioo (t₀ - δ) (t₀ + δ), isOpen_Ioo,
      ⟨by dsimp only [δ]; linarith, by dsimp only [δ]; linarith⟩,
      fun r hr ↦ ⟨max_le hr.2.1 hr.1.1.le, le_min hr.2.2 hr.1.2.le⟩⟩
  · refine hball ⟨Metric.mem_ball.2 ?_, (le_max_left _ _).trans hr.1, hr.2.trans (min_le_left _ _)⟩
    rw [Real.dist_eq, abs_lt]
    dsimp only [p, q, δ] at hr
    exact ⟨by linarith [le_max_right u (t₀ - ε / 2), hr.1],
      by linarith [min_le_right v (t₀ + ε / 2), hr.2]⟩

/-- For a local smooth section `Y` on an open set containing `γ '' [p, q]` (`[p, q] ⊆ [u, v]`) and
a smooth cutoff `ψ` supported in `(p, q)`, `indexForm I γ V (ψ • (Y ∘ γ)) u v` reduces to a single
interval integral over `[p, q]`. -/
private lemma indexForm_contDiff_smul_section_eq {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)}
    {u p q v : ℝ} (hup : u ≤ p) (hpq : p < q) (hqv : q ≤ v)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc u v))
    (hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) (Icc u v))
    {U : Set M} (hU : IsOpen U) (hγU : MapsTo γ (Icc p q) U)
    {Y : ∀ x, TangentSpace I x}
    (hY : ContMDiffOn I I.tangent ∞ (fun x ↦ TotalSpace.mk' E x (Y x)) U)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψs : tsupport ψ ⊆ Ioo p q) :
    indexForm I γ V (fun t ↦ ψ t • Y (γ t)) u v =
      ∫ t in p..q, (deriv ψ t *
          inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V (Icc u v) t) (Y (γ t)) +
        ψ t * (inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V (Icc u v) t)
            (alongCurveWithin (leviCivitaConnection I M) γ (fun r ↦ Y (γ r)) (Icc p q) t) -
          inner ℝ ((leviCivitaConnection I M).curvatureTensor (γ t) (V t)
            (curveVelocityWithin I γ (Icc u v) t) (curveVelocityWithin I γ (Icc u v) t))
            (Y (γ t)))) := by
  let W : ∀ t, TangentSpace I (γ t) := fun t ↦ ψ t • Y (γ t)
  have huv : u < v := (hup.trans_lt hpq).trans_le hqv
  have hYγ : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun t ↦ TotalSpace.mk' E (γ t) (Y (γ t))) (Icc p q) :=
    (hY.of_le (by simp)).comp (hγ.mono (Icc_subset_Icc hup hqv)) hγU
  have hW_uv := ((hψ.of_le (by simp)).contMDiff.contMDiffOn).smul_sectionAlong_of_tsupport hγ hU
    (fun _ ht ↦ hγU (Ioo_subset_Icc_self (hψs ht.2))) (hY.of_le (by simp))
  rw [← indexForm_subinterval_eq_of_tsupport_subset hup hpq hqv
    (.of_contMDiffOn huv hV) (.of_contMDiffOn huv hW_uv)
    (fun t ht ↦ by simp [image_eq_zero_of_notMem_tsupport fun h ↦ ht (hψs h)]),
    indexForm_eq_integral_indexFormIntegrandWithin (s := Icc u v)
      (uIoo_of_lt hpq ▸ Ioo_subset_Icc_self.trans (Icc_subset_Icc hup hqv))]
  refine intervalIntegral.integral_congr_uIoo fun t ht ↦ ?_
  rw [uIoo_of_lt hpq] at ht
  have hnhds_pq : Icc p q ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
  have hnhds_uv : Icc u v ∈ 𝓝 t := mem_of_superset hnhds_pq (Icc_subset_Icc hup hqv)
  have hDW : alongCurveWithin (leviCivitaConnection I M) γ W (Icc u v) t =
      deriv ψ t • Y (γ t) +
        ψ t • alongCurveWithin (leviCivitaConnection I M) γ (fun r ↦ Y (γ r)) (Icc p q) t := by
    rw [alongCurveWithin_of_mem_nhds _ γ W hnhds_uv,
      alongCurveWithin_of_mem_nhds _ γ (fun r ↦ Y (γ r)) hnhds_pq,
      alongCurve_smul _ γ (fun r ↦ Y (γ r)) ψ
        (hψ.contDiffAt.differentiableAt (by simp))
        (differentiableAt_sectionCoord γ (fun r ↦ Y (γ r))
          (((hYγ t (Ioo_subset_Icc_self ht)).contMDiffAt hnhds_pq).mdifferentiableAt one_ne_zero)
          (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)))]
  rw [indexFormIntegrandWithin_def, hDW, inner_add_right, real_inner_smul_right,
    real_inner_smul_right, real_inner_smul_right]
  ring

/-- On a chart-contained subinterval `[p, q] ⊆ [u, v]`, index-orthogonality to smooth compactly
supported multiples of local sections upgrades each chart-local frame pairing of `D_t V` to `C¹`. -/
private lemma contDiffOn_inner_chartLocalFrame_alongCurveWithin
    {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)} {u p q v : ℝ}
    (hup : u ≤ p) (hpq : p < q) (hqv : q ≤ v)
    (hγ : IsGeodesicCurveOn I γ (Icc u v))
    (hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) (Icc u v))
    {x₀ : M} (hγU : MapsTo γ (Icc p q) (trivializationAt E (TangentSpace I) x₀).baseSet)
    (horth : ∀ (ψ : ℝ → ℝ) (Y : ∀ x, TangentSpace I x) (U : Set M),
      ContDiff ℝ ∞ ψ → tsupport ψ ⊆ Ioo u v → IsOpen U → γ '' tsupport ψ ⊆ U →
      ContMDiffOn I I.tangent ∞ (fun x ↦ TotalSpace.mk' E x (Y x)) U →
      indexForm I γ V (fun t ↦ ψ t • Y (γ t)) u v = 0)
    (j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ 1 (fun r ↦ inner ℝ (Riemannian.Tensor.chartLocalFrame (I := I) x₀ j (γ r))
      (alongCurveWithin (leviCivitaConnection I M) γ V (Icc u v) r)) (Icc p q) := by
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  let cov := leviCivitaConnection I M
  let e := trivializationAt E (TangentSpace I) x₀
  let Y := Riemannian.Tensor.chartLocalFrame (I := I) x₀ j
  have huv : u < v := (hup.trans_lt hpq).trans_le hqv
  have hγ1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc u v) := hγ.contMDiffOn.of_le one_le_two
  have hDV0 := contMDiffOn_alongCurveWithin_leviCivitaConnection (n := 0) (m := ∞) (k := ∞)
    (by simp) (by simp) (uniqueDiffOn_Icc huv) (by simpa using hV)
  have hvel0 : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 0
      (fun r ↦ TotalSpace.mk' E (γ r) (curveVelocityWithin I γ (Icc u v) r)) (Icc u v) := by
    simpa only [funext (curveVelocityLiftWithin_apply (I := I) γ (Icc u v))] using
      hγ1.contMDiffOn_curveVelocityLiftWithin (m := 0) (by simp)
        (uniqueDiffOn_Icc huv).uniqueMDiffOn
  have hY := Riemannian.Tensor.contMDiffOn_chartLocalFrame (I := I) (n := ∞) x₀ j
  have hYγ : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 2
      (fun r ↦ TotalSpace.mk' E (γ r) (Y (γ r))) (Icc p q) :=
    (hY.of_le (by simp)).comp (hγ.contMDiffOn.mono (Icc_subset_Icc hup hqv)) hγU
  have hDY := contMDiffOn_alongCurveWithin_leviCivitaConnection (n := 0) (m := ∞) (k := ∞)
    (by simp) (by simp) (uniqueDiffOn_Icc hpq) (hYγ.of_le one_le_two)
  have hf_cont := (ContMDiffOn.inner_bundle (IB := I) (F := E)
    (E := fun x : M ↦ TangentSpace I x) (b := γ)
    (h := IsContMDiffRiemannianBundle.of_le (n := ∞) zero_le)
    (hDV0.mono (Icc_subset_Icc hup hqv)) (hYγ.of_le (by simp))).continuousOn
  have hg_cont := ((ContMDiffOn.inner_bundle (IB := I) (F := E)
      (E := fun x : M ↦ TangentSpace I x) (b := γ)
      (h := IsContMDiffRiemannianBundle.of_le (n := ∞) zero_le)
      (hDV0.mono (Icc_subset_Icc hup hqv)) hDY).continuousOn).sub
    (ContMDiffOn.inner_bundle (IB := I) (F := E) (E := fun x : M ↦ TangentSpace I x) (b := γ)
      (h := IsContMDiffRiemannianBundle.of_le (n := ∞) zero_le)
      ((cov.contMDiffOn_curvatureTensor (F := E) (V := TangentSpace I) (by simp)
        (hV.of_le zero_le_one) hvel0 hvel0).mono (Icc_subset_Icc hup hqv))
      (hYγ.of_le (by simp))).continuousOn
  refine (hf_cont.contDiffOn_one_Icc_of_integral_deriv_smul_add_eq_zero hg_cont
    fun ψ hψ hψs ↦ ?_).congr fun r _ ↦ real_inner_comm _ _
  simp only [Pi.sub_apply, smul_eq_mul]
  rw [← indexForm_contDiff_smul_section_eq hup hpq hqv hγ1 hV e.open_baseSet hγU hY hψ hψs]
  exact horth ψ Y e.baseSet hψ (hψs.trans (Ioo_subset_Ioo hup hqv)) e.open_baseSet
    ((image_mono (hψs.trans Ioo_subset_Icc_self)).trans hγU.image_subset) hY

/-- Regularity bootstrap on a single closed geodesic piece: if `V` has a `C¹` lift on `[u, v]`
(`u < v`) and is index-orthogonal to all smooth compactly supported multiples of local sections
supported in `(u, v)`, then `D_t V` has a `C¹` lift on `[u, v]`. -/
private lemma contMDiffOn_alongCurveWithin_of_indexForm_contDiff_smul_eq_zero
    {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)} {u v : ℝ} (huv : u < v)
    (hγ : IsGeodesicCurveOn I γ (Icc u v))
    (hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) (Icc u v))
    (horth : ∀ (ψ : ℝ → ℝ) (Y : ∀ x, TangentSpace I x) (U : Set M),
      ContDiff ℝ ∞ ψ → tsupport ψ ⊆ Ioo u v → IsOpen U → γ '' tsupport ψ ⊆ U →
      ContMDiffOn I I.tangent ∞ (fun x ↦ TotalSpace.mk' E x (Y x)) U →
      indexForm I γ V (fun t ↦ ψ t • Y (γ t)) u v = 0) :
    ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (γ r)
        (alongCurveWithin (leviCivitaConnection I M) γ V (Icc u v) r)) (Icc u v) := by
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  let cov := leviCivitaConnection I M
  have hγ1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc u v) := hγ.contMDiffOn.of_le one_le_two
  intro t₀ ht₀
  obtain ⟨p, q, hup, hpq, hqv, ht₀_pq, hnhds, hγU⟩ :=
    exists_subinterval_mapsTo_baseSet I huv hγ1.continuousOn ht₀
  have hsum_pq : ContMDiffWithinAt 𝓘(ℝ, ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (γ r)
        (∑ j, inner ℝ (Riemannian.Tensor.chartLocalFrame (I := I) (γ t₀) j (γ r))
            (alongCurveWithin cov γ V (Icc u v) r) •
          Riemannian.Tensor.chartDualFrame (I := I) (γ t₀) j (γ r))) (Icc p q) t₀ := by
    refine ContMDiffWithinAt.sum_sectionAlong Finset.univ _
      ((hγ1.mono (Icc_subset_Icc hup hqv)) t₀ ht₀_pq) fun j _ ↦ ?_
    have hdual : ContMDiffWithinAt 𝓘(ℝ, ℝ) I.tangent 1
        (fun r ↦ TotalSpace.mk' E (γ r)
          (Riemannian.Tensor.chartDualFrame (I := I) (γ t₀) j (γ r))) (Icc p q) t₀ :=
      ((Riemannian.Tensor.contMDiffAt_chartDualFrame (I := I) (n := ∞) (γ t₀)
        (hγU ht₀_pq) j).of_le (by simp)).comp_contMDiffWithinAt t₀
        ((hγ1.mono (Icc_subset_Icc hup hqv)) t₀ ht₀_pq)
    have hcoeff := contDiffOn_inner_chartLocalFrame_alongCurveWithin hup hpq hqv hγ hV hγU horth j
    exact (contMDiffWithinAt_iff_contDiffWithinAt.2 (hcoeff t₀ ht₀_pq)).smul_totalSpace hdual
  refine (hsum_pq.congr (fun r hr ↦ congrArg (TotalSpace.mk' E (γ r)) ?_)
    (congrArg (TotalSpace.mk' E (γ t₀)) ?_)).mono_of_mem_nhdsWithin hnhds
  · exact (Riemannian.Tensor.sum_inner_chartDualFrame_smul (γ t₀)
      (by simpa only [TangentBundle.trivializationAt_baseSet] using hγU hr) _).2.symm
  · exact (Riemannian.Tensor.sum_inner_chartDualFrame_smul (γ t₀)
      (by simpa only [TangentBundle.trivializationAt_baseSet] using hγU ht₀_pq) _).2.symm

/-- For a `C²` section `V` on `[u, v]` index-orthogonal to smooth compactly supported multiples of
local sections, each chart-local frame pairing of the Jacobi residual vanishes at
`t₀ ∈ [p, q] ⊆ [u, v]`. -/
private lemma inner_chartLocalFrame_jacobiResidual_eq_zero
    {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)} {u p q v t₀ : ℝ}
    (hup : u ≤ p) (hpq : p < q) (hqv : q ≤ v) (ht₀_pq : t₀ ∈ Icc p q)
    (hγ1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc u v))
    (hV2 : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 2 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) (Icc u v))
    (hR0 : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 0
      (fun r ↦ TotalSpace.mk' E (γ r)
        (alongCurveWithin (leviCivitaConnection I M) γ
            (alongCurveWithin (leviCivitaConnection I M) γ V (Icc u v)) (Icc u v) r +
          (leviCivitaConnection I M).curvatureTensor (γ r) (V r)
            (curveVelocityWithin I γ (Icc u v) r) (curveVelocityWithin I γ (Icc u v) r)))
      (Icc u v))
    (hγU : MapsTo γ (Icc p q) (trivializationAt E (TangentSpace I) (γ t₀)).baseSet)
    (horth : ∀ (ψ : ℝ → ℝ) (Y : ∀ x, TangentSpace I x) (U : Set M),
      ContDiff ℝ ∞ ψ → tsupport ψ ⊆ Ioo u v → IsOpen U → γ '' tsupport ψ ⊆ U →
      ContMDiffOn I I.tangent ∞ (fun x ↦ TotalSpace.mk' E x (Y x)) U →
      indexForm I γ V (fun t ↦ ψ t • Y (γ t)) u v = 0)
    (j : Fin (Module.finrank ℝ E)) :
    inner ℝ (Riemannian.Tensor.chartLocalFrame (I := I) (γ t₀) j (γ t₀))
      (alongCurveWithin (leviCivitaConnection I M) γ
          (alongCurveWithin (leviCivitaConnection I M) γ V (Icc u v)) (Icc u v) t₀ +
        (leviCivitaConnection I M).curvatureTensor (γ t₀) (V t₀)
          (curveVelocityWithin I γ (Icc u v) t₀) (curveVelocityWithin I γ (Icc u v) t₀)) = 0 := by
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have huv : u < v := (hup.trans_lt hpq).trans_le hqv
  let e := trivializationAt E (TangentSpace I) (γ t₀)
  let Y := Riemannian.Tensor.chartLocalFrame (I := I) (γ t₀) j
  have hY := Riemannian.Tensor.contMDiffOn_chartLocalFrame (I := I) (n := ∞) (γ t₀) j
  have hYγ : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (γ r) (Y (γ r))) (Icc p q) :=
    (hY.of_le (by simp)).comp (hγ1.mono (Icc_subset_Icc hup hqv)) hγU
  have hf_cont := (ContMDiffOn.inner_bundle (IB := I) (F := E)
    (E := fun x : M ↦ TangentSpace I x) (b := γ)
    (h := IsContMDiffRiemannianBundle.of_le (n := ∞) zero_le)
    (hYγ.of_le zero_le_one) (hR0.mono (Icc_subset_Icc hup hqv))).continuousOn
  refine hf_cont.eqOn_zero_Icc_of_integral_smul_eq_zero hpq (fun ψ hψ hψs ↦ ?_) ht₀_pq
  have hψ0 (t : ℝ) (ht : t ∉ Ioo p q) : ψ t = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ ht (hψs h)
  let W : ∀ t, TangentSpace I (γ t) := fun t ↦ ψ t • Y (γ t)
  have hW_uv := ((hψ.of_le (by simp)).contMDiff.contMDiffOn).smul_sectionAlong_of_tsupport hγ1
    e.open_baseSet (fun _ ht ↦ hγU (Ioo_subset_Icc_self (hψs ht.2))) (hY.of_le (by simp))
  have hI_pq : indexForm I γ V W p q = 0 :=
    (indexForm_subinterval_eq_of_tsupport_subset hup hpq hqv
      (.of_contMDiffOn huv (hV2.of_le one_le_two)) (.of_contMDiffOn huv hW_uv)
      fun t ht ↦ by simp [hψ0 t ht]).trans
      (horth ψ Y e.baseSet hψ (hψs.trans (Ioo_subset_Ioo hup hqv)) e.open_baseSet
        ((image_mono (hψs.trans Ioo_subset_Icc_self)).trans hγU.image_subset) hY)
  have hibp := indexForm_eq_inner_alongCurveWithin_sub_inner_sub_integral (s := Icc u v)
    (fun t ht ↦ hV2 t ((uIcc_of_le hpq.le ▸ ht : t ∈ Icc p q) |> Icc_subset_Icc hup hqv))
    (uIcc_of_le hpq.le ▸ hW_uv.mono (Icc_subset_Icc hup hqv))
    (uIcc_of_le hpq.le ▸ Icc_subset_Icc hup hqv)
  rw [hI_pq] at hibp
  have hibp' : ∫ t in p..q, inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ
        (alongCurveWithin (leviCivitaConnection I M) γ V (Icc u v)) (Icc u v) t +
      (leviCivitaConnection I M).curvatureTensor (γ t) (V t)
        (curveVelocityWithin I γ (Icc u v) t) (curveVelocityWithin I γ (Icc u v) t)) (W t) = 0 := by
    simpa [W, hψ0 p (by simp), hψ0 q (by simp)] using hibp.symm
  exact (intervalIntegral.integral_congr fun t _ ↦ by
    rw [smul_eq_mul, real_inner_comm, ← real_inner_smul_right]).trans hibp'

/-- **Variational Jacobi criterion on a single `C¹` piece.** If `γ` is a geodesic on `[u, v]` and
`V` has a `C¹` tangent-bundle lift on `[u, v]` that is index-orthogonal to all smooth compactly
supported multiples of local sections supported in `(u, v)`, then `V` is a `C²` Jacobi field on
`[u, v]`. -/
theorem isJacobiFieldOn_Icc_of_indexForm_contDiff_smul_eq_zero
    {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)} {u v : ℝ} (hγ : IsGeodesicCurveOn I γ (Icc u v))
    (hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) (Icc u v))
    (horth : ∀ (ψ : ℝ → ℝ) (Y : ∀ x, TangentSpace I x) (U : Set M),
      ContDiff ℝ ∞ ψ → tsupport ψ ⊆ Ioo u v → IsOpen U → γ '' tsupport ψ ⊆ U →
      ContMDiffOn I I.tangent ∞ (fun x ↦ TotalSpace.mk' E x (Y x)) U →
      indexForm I γ V (fun t ↦ ψ t • Y (γ t)) u v = 0) :
    IsJacobiFieldOn I γ V (Icc u v) := by
  rcases lt_trichotomy u v with huv | rfl | hvu
  · let cov := leviCivitaConnection I M
    have hγ1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc u v) := hγ.contMDiffOn.of_le one_le_two
    have hDV1 := contMDiffOn_alongCurveWithin_of_indexForm_contDiff_smul_eq_zero huv hγ hV horth
    have hV2 := contMDiffOn_succ_of_alongCurveWithin cov γ V le_rfl
      (fun t _ ↦ contMDiffCovariantDerivativeOn_leviCivitaConnection (m := ∞) (k := ∞)
        (trivializationAt E (TangentSpace I) (γ t)).open_baseSet (by simp) (by simp))
      (uniqueDiffOn_Icc huv) hγ.contMDiffOn hV hDV1
    refine ⟨hγ, hV2, fun t₀ ht₀ ↦ ?_⟩
    have hvel0 : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 0
        (fun r ↦ TotalSpace.mk' E (γ r) (curveVelocityWithin I γ (Icc u v) r)) (Icc u v) := by
      simpa only [funext (curveVelocityLiftWithin_apply (I := I) γ (Icc u v))] using
        hγ1.contMDiffOn_curveVelocityLiftWithin (m := 0) (by simp)
          (uniqueDiffOn_Icc huv).uniqueMDiffOn
    have hR0 := (contMDiffOn_alongCurveWithin_leviCivitaConnection (n := 0) (m := ∞) (k := ∞)
        (by simp) (by simp) (uniqueDiffOn_Icc huv) (by simpa using hDV1)).add_sectionAlong
      (cov.contMDiffOn_curvatureTensor (F := E) (V := TangentSpace I) (by simp)
        (hV.of_le zero_le_one) hvel0 hvel0)
    obtain ⟨p, q, hup, hpq, hqv, ht₀_pq, _, hγU⟩ :=
      exists_subinterval_mapsTo_baseSet I huv hγ1.continuousOn ht₀
    have hexp := (Riemannian.Tensor.sum_inner_chartDualFrame_smul (γ t₀)
      (by simpa only [TangentBundle.trivializationAt_baseSet] using hγU ht₀_pq)
      (alongCurveWithin cov γ (alongCurveWithin cov γ V (Icc u v)) (Icc u v) t₀ +
        cov.curvatureTensor (γ t₀) (V t₀)
          (curveVelocityWithin I γ (Icc u v) t₀) (curveVelocityWithin I γ (Icc u v) t₀))).2
    simpa only [cov,
      inner_chartLocalFrame_jacobiResidual_eq_zero hup hpq hqv ht₀_pq hγ1 hV2 hR0 hγU horth,
      zero_smul, Finset.sum_const_zero] using hexp.symm
  · have hud := hγ.uniqueDiffOn u ⟨le_rfl, le_rfl⟩
    rw [Icc_self] at hud
    exact absurd (UniqueDiffWithinAt.eq_deriv {u} hud (hasDerivWithinAt_id u _)
      ((hasDerivWithinAt_const u {u} u).congr (fun x hx ↦ hx) rfl)) one_ne_zero
  · exact ⟨hγ, Icc_eq_empty hvu.not_ge ▸ contMDiffOn_empty, by simp [Icc_eq_empty hvu.not_ge]⟩

/-! ### Piecewise variational characterization of Jacobi fields -/

/-- Vanishing of each interior covariant-derivative jump of a broken Jacobi field that is
index-orthogonal to smooth compactly supported multiples of global sections. -/
private lemma alongCurveWithin_jump_eq_zero_of_indexForm_contDiff_smul_eq_zero
    {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)} {a b : ℝ} {k : ℕ}
    (τ : Fin (k + 2) → ℝ) (hτa : τ 0 = a) (hτb : τ (Fin.last (k + 1)) = b)
    (hτ : ∀ i : Fin (k + 1), τ i.castSucc < τ i.succ) (hγ : IsGeodesicCurveOn I γ (Icc a b))
    (hJ_piece : ∀ i : Fin (k + 1), IsJacobiFieldOn I γ V (Icc (τ i.castSucc) (τ i.succ)))
    (horth : ∀ (ψ : ℝ → ℝ) (Y : ∀ x, TangentSpace I x) (U : Set M),
      ContDiff ℝ ∞ ψ → tsupport ψ ⊆ Ioo a b → IsOpen U → γ '' tsupport ψ ⊆ U →
      ContMDiffOn I I.tangent ∞ (fun x ↦ TotalSpace.mk' E x (Y x)) U →
      indexForm I γ V (fun t ↦ ψ t • Y (γ t)) a b = 0) (j : Fin k) :
    alongCurveWithin (leviCivitaConnection I M) γ V
        (Icc (τ j.castSucc.castSucc) (τ j.castSucc.succ)) (τ j.castSucc.succ) =
      alongCurveWithin (leviCivitaConnection I M) γ V
        (Icc (τ j.succ.castSucc) (τ j.succ.succ)) (τ j.castSucc.succ) := by
  have hmono := (Fin.strictMono_iff_lt_succ.mpr hτ).monotone
  have hsub (i : Fin (k + 1)) : Icc (τ i.castSucc) (τ i.succ) ⊆ Icc a b :=
    Icc_subset_Icc (hτa ▸ hmono (Fin.zero_le _)) (hτb ▸ hmono (Fin.le_last _))
  let c := τ j.castSucc.succ
  let Δ : TangentSpace I (γ c) :=
    alongCurveWithin (leviCivitaConnection I M) γ V (Icc (τ j.succ.castSucc) (τ j.succ.succ)) c -
      alongCurveWithin (leviCivitaConnection I M) γ V
        (Icc (τ j.castSucc.castSucc) (τ j.castSucc.succ)) c
  obtain ⟨φ, X, hφ, hφ_tsupp, hX, hWc, hφ0⟩ :=
    exists_contDiff_smul_section_isolating_vertex (I := I) (F := E) (n := ∞) τ hτ j Δ
  let W : ∀ t, TangentSpace I (γ t) := fun t ↦ φ t • X (γ t)
  have hI0 : indexForm I γ V W (τ 0) (τ (Fin.last (k + 1))) = 0 := by
    rw [hτa, hτb]
    exact horth φ X univ hφ (hτa ▸ hτb ▸ hφ_tsupp) isOpen_univ (subset_univ _)
      (contMDiffOn_univ.2 hX)
  have hW_τ (i : Fin (k + 1)) : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (γ r) (W r)) (Icc (τ i.castSucc) (τ i.succ)) :=
    ((hφ.of_le (by simp)).contMDiff.contMDiffOn).smul_sectionAlong_of_tsupport
      ((hγ.contMDiffOn.of_le one_le_two).mono (hsub i)) isOpen_univ (mapsTo_univ _ _)
      ((contMDiffOn_univ.2 hX).of_le (by simp))
  have hibp := indexForm_eq_inner_sub_sum_jump_of_isJacobiFieldOn τ (fun i ↦ (hτ i).le)
    hJ_piece hW_τ
  have hWj (m : Fin k) :
      inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V
          (Icc (τ m.succ.castSucc) (τ m.succ.succ)) (τ m.castSucc.succ) -
        alongCurveWithin (leviCivitaConnection I M) γ V
          (Icc (τ m.castSucc.castSucc) (τ m.castSucc.succ)) (τ m.castSucc.succ))
        (W (τ m.castSucc.succ)) = if m = j then inner ℝ Δ Δ else 0 := by
    split_ifs with hmj
    · subst hmj; simp [W, c, Δ, hWc]
    · simp [W, hφ0 m.castSucc.succ (by simpa using hmj)]
  have hφa : φ (τ 0) = 0 := hφ0 0 (Fin.succ_ne_zero _).symm
  have hφb : φ (τ (Fin.last (k + 1))) = 0 := hφ0 _ (by simp [Fin.ext_iff]; omega)
  simp only [hI0, hWj, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hibp
  exact (sub_eq_zero.mp (by simpa [W, hφa, hφb, sq_eq_zero_iff] using hibp.symm : Δ = 0)).symm

/-- **Milnor's piecewise variational Jacobi criterion.** A continuous piecewise `C¹` section `V`
along a geodesic `γ` on `[a, b]` that is index-orthogonal to all smooth compactly supported
multiples of local sections supported in `(a, b)` is an unbroken `C²` Jacobi field on `[a, b]`. -/
theorem isJacobiFieldOn_Icc_of_indexForm_contDiff_smul_eq_zero_of_piecewise
    {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)} {a b : ℝ} (hγ : IsGeodesicCurveOn I γ (Icc a b))
    (hV : IsPiecewiseContMDiffOn I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) a b)
    (horth : ∀ (ψ : ℝ → ℝ) (Y : ∀ x, TangentSpace I x) (U : Set M),
      ContDiff ℝ ∞ ψ → tsupport ψ ⊆ Ioo a b → IsOpen U → γ '' tsupport ψ ⊆ U →
      ContMDiffOn I I.tangent ∞ (fun x ↦ TotalSpace.mk' E x (Y x)) U →
      indexForm I γ V (fun t ↦ ψ t • Y (γ t)) a b = 0) :
    IsJacobiFieldOn I γ V (Icc a b) := by
  obtain ⟨k, τ, hτa, hτb, hτ, hpieces⟩ := hV.exists_partition
  have hmono := (Fin.strictMono_iff_lt_succ.mpr hτ).monotone
  have hsub (i : Fin (k + 1)) : Icc (τ i.castSucc) (τ i.succ) ⊆ Icc a b :=
    Icc_subset_Icc (hτa ▸ hmono (Fin.zero_le _)) (hτb ▸ hmono (Fin.le_last _))
  have hJ_piece (i : Fin (k + 1)) : IsJacobiFieldOn I γ V (Icc (τ i.castSucc) (τ i.succ)) := by
    refine isJacobiFieldOn_Icc_of_indexForm_contDiff_smul_eq_zero
      (hγ.mono (uniqueDiffOn_Icc (hτ i)) (hsub i)) (hpieces i) fun ψ Y U hψ hψs hU hγU hY ↦ ?_
    have hW_pw := IsPiecewiseContMDiffOn.of_contMDiffOn hV.lt
      (((hψ.of_le (by simp)).contMDiff.contMDiffOn).smul_sectionAlong_of_tsupport
        (hγ.contMDiffOn.of_le one_le_two) hU (fun _ ht ↦ hγU ⟨_, ht.2, rfl⟩) (hY.of_le (by simp)))
    rw [indexForm_subinterval_eq_of_tsupport_subset
      (hτa ▸ hmono (Fin.zero_le _)) (hτ i) (hτb ▸ hmono (Fin.le_last _)) hV hW_pw
      fun t ht ↦ by simp [image_eq_zero_of_notMem_tsupport fun h ↦ ht (hψs h)]]
    exact horth ψ Y U hψ (hψs.trans (Ioo_subset_Ioo (hτa ▸ hmono (Fin.zero_le _))
      (hτb ▸ hmono (Fin.le_last _)))) hU hγU hY
  exact isJacobiFieldOn_Icc_of_partition τ hτa hτb hτ hγ hJ_piece fun j ↦
    alongCurveWithin_jump_eq_zero_of_indexForm_contDiff_smul_eq_zero τ hτa hτb hτ hγ hJ_piece
      horth j

/-- **Unbroken `C^n` test-field characterization of Jacobi fields.** For `1 ≤ n ≤ ∞`
(`[ENat.LEInfty n]`), testing `indexForm I γ V W a b = 0` against unbroken `C^n` endpoint-zero
sections `W` along a geodesic `γ` on `[a, b]` already forces a continuous piecewise `C¹` section
`V` to be an unbroken Jacobi field on `[a, b]`. -/
theorem isJacobiFieldOn_Icc_iff_forall_contMDiffOn_indexForm_eq_zero
    {n : ℕ∞ω} [ENat.LEInfty n] (hn : 1 ≤ n) {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)} {a b : ℝ}
    (hγ_geo : IsGeodesicCurveOn I γ (Icc a b))
    (hV : IsPiecewiseContMDiffOn I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) a b) :
    IsJacobiFieldOn I γ V (Icc a b) ↔
      ∀ W : ∀ t, TangentSpace I (γ t),
        ContMDiffOn 𝓘(ℝ, ℝ) I.tangent n (fun r ↦ TotalSpace.mk' E (γ r) (W r)) (Icc a b) →
        W a = 0 → W b = 0 → indexForm I γ V W a b = 0 := by
  have hγ := hγ_geo.contMDiffOn_infty.of_le (m := n) ENat.LEInfty.out
  refine ⟨fun hJ W hW hWa hWb ↦
    hJ.indexForm_eq_zero_of_isPiecewiseContMDiffOn (.of_contMDiffOn hV.lt (hW.of_le hn))
      Subset.rfl hWa hWb, fun horth ↦ ?_⟩
  refine isJacobiFieldOn_Icc_of_indexForm_contDiff_smul_eq_zero_of_piecewise hγ_geo hV
    fun ψ Y U hψ hψs hU hγU hY ↦ horth _
      (((hψ.of_le ENat.LEInfty.out).contMDiff.contMDiffOn).smul_sectionAlong_of_tsupport hγ hU
        (fun _ ht ↦ hγU ⟨_, ht.2, rfl⟩) (hY.of_le ENat.LEInfty.out))
      (by simp [image_eq_zero_of_notMem_tsupport fun h ↦ (hψs h).1.ne rfl])
      (by simp [image_eq_zero_of_notMem_tsupport fun h ↦ (hψs h).2.ne rfl])

/-- **Variational characterization of Jacobi fields.** For `1 ≤ n ≤ ∞` (`[ENat.LEInfty n]`), a
continuous piecewise `C¹` section `V` along a geodesic `γ` on `[a, b]` is a Jacobi field on
`[a, b]` if and only if `I(V, W) = 0` for every piecewise `C^n` section `W` on `[a, b]` vanishing
at `a` and `b`. -/
theorem isJacobiFieldOn_Icc_iff_forall_isPiecewiseContMDiffOn_indexForm_eq_zero
    {n : ℕ∞ω} [ENat.LEInfty n] (hn : 1 ≤ n) {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)} {a b : ℝ}
    (hγ_geo : IsGeodesicCurveOn I γ (Icc a b))
    (hV : IsPiecewiseContMDiffOn I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) a b) :
    IsJacobiFieldOn I γ V (Icc a b) ↔
      ∀ W : ∀ t, TangentSpace I (γ t),
        IsPiecewiseContMDiffOn I.tangent n (fun r ↦ TotalSpace.mk' E (γ r) (W r)) a b →
        W a = 0 → W b = 0 → indexForm I γ V W a b = 0 :=
  ⟨fun hJ _ hW hWa hWb ↦
    hJ.indexForm_eq_zero_of_isPiecewiseContMDiffOn (hW.of_le hn) Subset.rfl hWa hWb,
    fun horth ↦ (isJacobiFieldOn_Icc_iff_forall_contMDiffOn_indexForm_eq_zero hn hγ_geo hV).2
      fun W hW ↦ horth W (.of_contMDiffOn hV.lt hW)⟩

/-! ### Kernel, nullity, and nondegeneracy of `endpointZeroIndexForm` -/

section EndpointKernel

variable {n : ℕ∞ω} [ENat.LEInfty n] {γ : ℝ → M} {a b : ℝ}

/-- Restrict a Jacobi field on `[a, b]` linearly to a bundled piecewise `C^n` interval section. -/
def jacobiToPiecewiseSection (hγ : IsPiecewiseContMDiffOn I n γ a b)
    (hγ_geo : IsGeodesicCurveOn I γ (Icc a b)) :
    jacobiFieldSpace hγ_geo →ₗ[ℝ]
      PiecewiseContMDiffSectionAlong (F := E) (V := TangentSpace I) hγ where
  toFun J :=
    .ofPiecewise J.val ((isJacobiFieldOn_of_mem_jacobiFieldSpace J).isPiecewiseContMDiffOn hγ.lt)
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/-- Evaluating `jacobiToPiecewiseSection` at an interval parameter returns the Jacobi field's
value there. -/
@[simp] theorem jacobiToPiecewiseSection_apply (hγ : IsPiecewiseContMDiffOn I n γ a b)
    (hγ_geo : IsGeodesicCurveOn I γ (Icc a b)) (J : jacobiFieldSpace hγ_geo) (t : Icc a b) :
    (jacobiToPiecewiseSection hγ hγ_geo J).val t = J.val t :=
  PiecewiseContMDiffSectionAlong.ofPiecewise_apply _ _ t

/-- Extending `jacobiToPiecewiseSection` by zero outside `[a, b]` recovers `J.val`. -/
@[simp] theorem extendByZero_jacobiToPiecewiseSection (hγ : IsPiecewiseContMDiffOn I n γ a b)
    (hγ_geo : IsGeodesicCurveOn I γ (Icc a b)) (J : jacobiFieldSpace hγ_geo) :
    (jacobiToPiecewiseSection hγ hγ_geo J).extendByZero = J.val := by
  ext t; by_cases ht : t ∈ Icc a b <;>
    simp [ht, ((mem_jacobiFieldSpace hγ_geo J.val).mp J.property).2]

/-- Restricting Jacobi fields on `[a, b]` to bundled interval sections is injective. -/
theorem jacobiToPiecewiseSection_injective (hγ : IsPiecewiseContMDiffOn I n γ a b)
    (hγ_geo : IsGeodesicCurveOn I γ (Icc a b)) :
    Function.Injective (jacobiToPiecewiseSection hγ hγ_geo) := fun _ _ h ↦
  jacobiFieldSpace_ext fun t ht ↦ by
    simpa only [jacobiToPiecewiseSection_apply] using congrArg (fun S ↦ S.val ⟨t, ht⟩) h

/-- Embed endpoint-zero Jacobi fields on `[a, b]` linearly into
`PiecewiseContMDiffSectionAlong.endpointZero`. -/
def endpointJacobiToEndpointZero (hγ : IsPiecewiseContMDiffOn I n γ a b)
    (hγ_geo : IsGeodesicCurveOn I γ (Icc a b)) :
    endpointJacobiFieldSpace hγ_geo a b →ₗ[ℝ]
      PiecewiseContMDiffSectionAlong.endpointZero (F := E) (V := TangentSpace I) (hγ := hγ) :=
  ((jacobiToPiecewiseSection hγ hγ_geo).comp (endpointJacobiFieldSpace hγ_geo a b).subtype)
    |>.codRestrict _ fun J ↦ by
      simpa [PiecewiseContMDiffSectionAlong.mem_endpointZero_iff] using
        (mem_endpointJacobiFieldSpace hγ_geo J.val).mp J.property

/-- Underlying bundled interval section of `endpointJacobiToEndpointZero`. -/
@[simp] theorem coe_endpointJacobiToEndpointZero (hγ : IsPiecewiseContMDiffOn I n γ a b)
    (hγ_geo : IsGeodesicCurveOn I γ (Icc a b)) (J : endpointJacobiFieldSpace hγ_geo a b) :
    (endpointJacobiToEndpointZero hγ hγ_geo J).val = jacobiToPiecewiseSection hγ hγ_geo J.val :=
  (rfl)

/-- Evaluating `endpointJacobiToEndpointZero` at an interval parameter returns the Jacobi field's
value there. -/
theorem endpointJacobiToEndpointZero_apply (hγ : IsPiecewiseContMDiffOn I n γ a b)
    (hγ_geo : IsGeodesicCurveOn I γ (Icc a b))
    (J : endpointJacobiFieldSpace hγ_geo a b) (t : Icc a b) :
    (endpointJacobiToEndpointZero hγ hγ_geo J).val.val t = J.val.val t :=
  jacobiToPiecewiseSection_apply hγ hγ_geo J.val t

/-- Embedding `endpointJacobiFieldSpace` into `PiecewiseContMDiffSectionAlong.endpointZero` is
injective. -/
theorem endpointJacobiToEndpointZero_injective (hγ : IsPiecewiseContMDiffOn I n γ a b)
    (hγ_geo : IsGeodesicCurveOn I γ (Icc a b)) :
    Function.Injective (endpointJacobiToEndpointZero hγ hγ_geo) := fun _ _ h ↦
  Subtype.ext (jacobiToPiecewiseSection_injective hγ hγ_geo (congrArg Subtype.val h))

/-- **Kernel criterion for `endpointZeroIndexForm` (Milnor, Theorem 14.1).** A fixed-endpoint
continuous piecewise `C^n` section (`1 ≤ n ≤ ∞`) lies in the kernel of `endpointZeroIndexForm` if
and only if its zero extension solves the Jacobi equation on `[a, b]`. -/
theorem mem_ker_endpointZeroIndexForm_iff (hγ : IsPiecewiseContMDiffOn I n γ a b)
    (hγ_geo : IsGeodesicCurveOn I γ (Icc a b)) (hn : 1 ≤ n)
    (V : PiecewiseContMDiffSectionAlong.endpointZero (F := E) (V := TangentSpace I) (hγ := hγ)) :
    V ∈ LinearMap.ker (endpointZeroIndexForm hγ hn) ↔
      IsJacobiFieldOn I γ V.val.extendByZero (Icc a b) := by
  rw [LinearMap.mem_ker, LinearMap.ext_iff]
  simp only [endpointZeroIndexForm_apply, piecewiseIndexForm_apply, LinearMap.zero_apply]
  rw [isJacobiFieldOn_Icc_iff_forall_isPiecewiseContMDiffOn_indexForm_eq_zero (n := n) hn hγ_geo
    (V.val.isPiecewiseContMDiffOn_extendByZero.of_le hn)]
  constructor
  · intro h W hW hWa hWb
    let W₀ : PiecewiseContMDiffSectionAlong.endpointZero
        (F := E) (V := TangentSpace I) (hγ := hγ) :=
      ⟨.ofPiecewise W hW, by simp [hWa, hWb]⟩
    refine (indexForm_congr (fun _ _ ↦ rfl) (fun _ _ ↦ HEq.rfl) fun t ht ↦ ?_).trans (h W₀)
    rw [uIoo_of_lt hγ.lt] at ht
    exact heq_of_eq (by simp [W₀, Ioo_subset_Icc_self ht])
  · intro h W
    obtain ⟨hWa, hWb⟩ := (PiecewiseContMDiffSectionAlong.mem_endpointZero_iff W.val).1 W.property
    exact h W.val.extendByZero W.val.isPiecewiseContMDiffOn_extendByZero
      (by simp [hγ.lt.le, hWa]) (by simp [hγ.lt.le, hWb])

/-- **Milnor's endpoint-Jacobi kernel equivalence.** For every `1 ≤ n ≤ ∞` (`[ENat.LEInfty n]`),
embedding Jacobi fields into piecewise `C^n` sections identifies `endpointJacobiFieldSpace`
linearly with the kernel of `endpointZeroIndexForm`. -/
def endpointJacobiEquivIndexFormKer (hγ : IsPiecewiseContMDiffOn I n γ a b)
    (hγ_geo : IsGeodesicCurveOn I γ (Icc a b)) (hn : 1 ≤ n) :
    endpointJacobiFieldSpace hγ_geo a b ≃ₗ[ℝ] LinearMap.ker (endpointZeroIndexForm hγ hn) := by
  refine LinearEquiv.ofBijective
    ((endpointJacobiToEndpointZero hγ hγ_geo).codRestrict
      (LinearMap.ker (endpointZeroIndexForm hγ hn)) fun J ↦ ?_)
    ⟨fun _ _ h ↦ endpointJacobiToEndpointZero_injective hγ hγ_geo (congrArg Subtype.val h),
      fun V ↦ ?_⟩
  · rw [mem_ker_endpointZeroIndexForm_iff hγ hγ_geo hn]
    simpa using isJacobiFieldOn_of_mem_jacobiFieldSpace J.val
  · have hJV := (mem_ker_endpointZeroIndexForm_iff hγ hγ_geo hn V.val).1 V.property
    obtain ⟨hVa, hVb⟩ :=
      (PiecewiseContMDiffSectionAlong.mem_endpointZero_iff V.val.val).1 V.val.property
    let J₀ : jacobiFieldSpace hγ_geo :=
      ⟨V.val.val.extendByZero, (mem_jacobiFieldSpace hγ_geo _).2
        ⟨hJV, fun _ ht ↦ V.val.val.extendByZero_apply_of_notMem ht⟩⟩
    refine ⟨⟨J₀, (mem_endpointJacobiFieldSpace hγ_geo J₀).2
      ⟨by simp [J₀, hγ.lt.le, hVa], by simp [J₀, hγ.lt.le, hVb]⟩⟩, Subtype.ext (Subtype.ext ?_)⟩
    ext t
    rw [LinearMap.codRestrict_apply, endpointJacobiToEndpointZero_apply]
    exact V.val.val.extendByZero_apply_of_mem t.property

/-- Underlying fixed-endpoint section of `endpointJacobiEquivIndexFormKer`. -/
@[simp] theorem coe_endpointJacobiEquivIndexFormKer (hγ : IsPiecewiseContMDiffOn I n γ a b)
    (hγ_geo : IsGeodesicCurveOn I γ (Icc a b)) (hn : 1 ≤ n)
    (J : endpointJacobiFieldSpace hγ_geo a b) :
    (endpointJacobiEquivIndexFormKer hγ hγ_geo hn J).val =
      endpointJacobiToEndpointZero hγ hγ_geo J := (rfl)

/-- Forward evaluation of `endpointJacobiEquivIndexFormKer`. -/
theorem endpointJacobiEquivIndexFormKer_apply (hγ : IsPiecewiseContMDiffOn I n γ a b)
    (hγ_geo : IsGeodesicCurveOn I γ (Icc a b)) (hn : 1 ≤ n)
    (J : endpointJacobiFieldSpace hγ_geo a b) (t : Icc a b) :
    (endpointJacobiEquivIndexFormKer hγ hγ_geo hn J).val.val.val t = J.val.val t :=
  endpointJacobiToEndpointZero_apply hγ hγ_geo J t

/-- Underlying section along `γ` of `(endpointJacobiEquivIndexFormKer hγ hγ_geo hn).symm V`. -/
@[simp] theorem coe_endpointJacobiEquivIndexFormKer_symm (hγ : IsPiecewiseContMDiffOn I n γ a b)
    (hγ_geo : IsGeodesicCurveOn I γ (Icc a b)) (hn : 1 ≤ n)
    (V : LinearMap.ker (endpointZeroIndexForm hγ hn)) :
    ((endpointJacobiEquivIndexFormKer hγ hγ_geo hn).symm V).val.val =
      V.val.val.extendByZero := by
  have h := congrArg (fun W : LinearMap.ker (endpointZeroIndexForm hγ hn) ↦ W.val.val.extendByZero)
    ((endpointJacobiEquivIndexFormKer hγ hγ_geo hn).apply_symm_apply V)
  rwa [coe_endpointJacobiEquivIndexFormKer, coe_endpointJacobiToEndpointZero,
    extendByZero_jacobiToPiecewiseSection] at h

/-- Inverse evaluation of `endpointJacobiEquivIndexFormKer` on `[a, b]`. -/
theorem endpointJacobiEquivIndexFormKer_symm_apply (hγ : IsPiecewiseContMDiffOn I n γ a b)
    (hγ_geo : IsGeodesicCurveOn I γ (Icc a b)) (hn : 1 ≤ n)
    (V : LinearMap.ker (endpointZeroIndexForm hγ hn)) {t : ℝ} (ht : t ∈ Icc a b) :
    ((endpointJacobiEquivIndexFormKer hγ hγ_geo hn).symm V).val.val t = V.val.val.val ⟨t, ht⟩ := by
  simp [ht]

/-- The kernel of `endpointZeroIndexForm` along a geodesic is finite-dimensional. -/
theorem finiteDimensional_ker_endpointZeroIndexForm (hγ : IsPiecewiseContMDiffOn I n γ a b)
    (hγ_geo : IsGeodesicCurveOn I γ (Icc a b)) (hn : 1 ≤ n) :
    FiniteDimensional ℝ (LinearMap.ker (endpointZeroIndexForm hγ hn)) := by
  have := finiteDimensional_jacobiFieldSpace hγ_geo isPreconnected_Icc (left_mem_Icc.2 hγ.lt.le)
  exact Module.Finite.equiv (endpointJacobiEquivIndexFormKer hγ hγ_geo hn)

/-- **Index-form nullity equals conjugate multiplicity.** For every `1 ≤ n ≤ ∞`
(`[ENat.LEInfty n]`), `finrank (ker endpointZeroIndexForm) = conjugateMultiplicity`. -/
theorem finrank_ker_endpointZeroIndexForm (hγ : IsPiecewiseContMDiffOn I n γ a b)
    (hγ_geo : IsGeodesicCurveOn I γ (Icc a b)) (hn : 1 ≤ n) :
    Module.finrank ℝ (LinearMap.ker (endpointZeroIndexForm hγ hn)) =
      conjugateMultiplicity hγ_geo isPreconnected_Icc (left_mem_Icc.2 hγ.lt.le) b := by
  rw [conjugateMultiplicity_eq_finrank]
  exact (endpointJacobiEquivIndexFormKer hγ hγ_geo hn).symm.finrank_eq

/-- Along a geodesic with nonzero velocity, the nullity of `endpointZeroIndexForm` is at most
`dim M - 1`. -/
theorem finrank_ker_endpointZeroIndexForm_le (hγ : IsPiecewiseContMDiffOn I n γ a b)
    (hγ_geo : IsGeodesicCurveOn I γ (Icc a b)) (hn : 1 ≤ n)
    (hv : curveVelocityWithin I γ (Icc a b) a ≠ 0) :
    Module.finrank ℝ (LinearMap.ker (endpointZeroIndexForm hγ hn)) ≤ Module.finrank ℝ E - 1 :=
  (finrank_ker_endpointZeroIndexForm hγ hγ_geo hn).le.trans <|
    conjugateMultiplicity_le hγ_geo isPreconnected_Icc
      (left_mem_Icc.2 hγ.lt.le) (right_mem_Icc.2 hγ.lt.le) hγ.lt.ne hv

/-- The kernel of `endpointZeroIndexForm` is nontrivial iff `a` and `b` are conjugate along `γ`. -/
theorem ker_endpointZeroIndexForm_ne_bot_iff_isConjugateOn
    (hγ : IsPiecewiseContMDiffOn I n γ a b) (hγ_geo : IsGeodesicCurveOn I γ (Icc a b))
    (hn : 1 ≤ n) :
    LinearMap.ker (endpointZeroIndexForm hγ hn) ≠ ⊥ ↔ IsConjugateOn I γ (Icc a b) a b := by
  let := finiteDimensional_ker_endpointZeroIndexForm hγ hγ_geo hn
  rw [← conjugateMultiplicity_pos_iff hγ_geo isPreconnected_Icc
      (left_mem_Icc.2 hγ.lt.le) (right_mem_Icc.2 hγ.lt.le) hγ.lt.ne,
    ← finrank_ker_endpointZeroIndexForm hγ hγ_geo hn,
    Module.finrank_pos_iff, Submodule.nontrivial_iff_ne_bot]

/-- The kernel of `endpointZeroIndexForm` is trivial iff `a` and `b` are not conjugate along `γ`. -/
theorem ker_endpointZeroIndexForm_eq_bot_iff_not_isConjugateOn
    (hγ : IsPiecewiseContMDiffOn I n γ a b) (hγ_geo : IsGeodesicCurveOn I γ (Icc a b))
    (hn : 1 ≤ n) :
    LinearMap.ker (endpointZeroIndexForm hγ hn) = ⊥ ↔ ¬ IsConjugateOn I γ (Icc a b) a b :=
  not_ne_iff.symm.trans (ker_endpointZeroIndexForm_ne_bot_iff_isConjugateOn hγ hγ_geo hn).not

/-- `endpointZeroIndexForm` is nondegenerate iff `a` and `b` are not conjugate along `γ`. -/
theorem nondegenerate_endpointZeroIndexForm_iff
    (hγ : IsPiecewiseContMDiffOn I n γ a b) (hγ_geo : IsGeodesicCurveOn I γ (Icc a b))
    (hn : 1 ≤ n) :
    (endpointZeroIndexForm hγ hn).Nondegenerate ↔ ¬ IsConjugateOn I γ (Icc a b) a b :=
  (isSymm_endpointZeroIndexForm hγ hn).isRefl.nondegenerate_iff_separatingLeft.trans <|
    LinearMap.separatingLeft_iff_ker_eq_bot.trans
      (ker_endpointZeroIndexForm_eq_bot_iff_not_isConjugateOn hγ hγ_geo hn)

end EndpointKernel

/-! ### Radial exponential corollaries -/

section RadialExponential

variable [I.Boundaryless] {n : ℕ∞ω} [ENat.LEInfty n] {p : M} {v : TangentSpace I p} {b : ℝ}

/-- Radial geodesic restriction of `t ↦ exp_p(t v)` to `[0, b]` (`0 < b ∈ geodesicInterval`). -/
private lemma isGeodesicCurveOn_riemannianExp_Icc (h0b : 0 < b)
    (hb : b ∈ geodesicInterval I M p v) :
    IsGeodesicCurveOn I (fun t : ℝ ↦ riemannianExp I M p (t • v)) (Icc 0 b) :=
  (isJacobiFieldOn_mfderiv_riemannianExp p v 0).isGeodesicCurveOn.mono (uniqueDiffOn_Icc h0b)
    (ordConnected_geodesicInterval.out zero_mem_geodesicInterval hb)

/-- Along the radial geodesic `t ↦ exp_p(t v)` on `[0, b]` (`0 < b`, `b ∈ geodesicInterval`), the
kernel of `endpointZeroIndexForm` is linearly equivalent to `ker(d(exp_p)_{b v})`. -/
def endpointZeroIndexFormKerEquivExpKer
    (hγ : IsPiecewiseContMDiffOn I n (fun t : ℝ ↦ riemannianExp I M p (t • v)) 0 b)
    (hb : b ∈ geodesicInterval I M p v) (hn : 1 ≤ n) :
    LinearMap.ker (endpointZeroIndexForm hγ hn) ≃ₗ[ℝ]
      LinearMap.ker (mfderiv 𝓘(ℝ, TangentSpace I p) I
        (riemannianExp I M p) (b • v)).toLinearMap :=
  (endpointJacobiEquivIndexFormKer hγ (isGeodesicCurveOn_riemannianExp_Icc hγ.lt hb) hn).symm.trans
    (endpointJacobiFieldEquivExpKer (isGeodesicCurveOn_riemannianExp_Icc hγ.lt hb)
      isPreconnected_Icc (ordConnected_geodesicInterval.out zero_mem_geodesicInterval hb)
      (left_mem_Icc.2 hγ.lt.le) (right_mem_Icc.2 hγ.lt.le) hγ.lt.ne')

/-- Forward evaluation of `endpointZeroIndexFormKerEquivExpKer` via the initial covariant
derivative of `V.val.val.extendByZero` at `0`. -/
@[simp] theorem endpointZeroIndexFormKerEquivExpKer_apply
    (hγ : IsPiecewiseContMDiffOn I n (fun t : ℝ ↦ riemannianExp I M p (t • v)) 0 b)
    (hb : b ∈ geodesicInterval I M p v) (hn : 1 ≤ n)
    (V : LinearMap.ker (endpointZeroIndexForm hγ hn)) :
    (endpointZeroIndexFormKerEquivExpKer hγ hb hn V).val =
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (b • v)).symm
        (tangentSpaceCast I (riemannianExp I M p ((0 : ℝ) • v)) p
          (alongCurveWithin (leviCivitaConnection I M)
            (fun t : ℝ ↦ riemannianExp I M p (t • v)) V.val.val.extendByZero (Icc 0 b) 0)) := by
  simp [endpointZeroIndexFormKerEquivExpKer]

/-- Inverse evaluation of `endpointZeroIndexFormKerEquivExpKer` on `[0, b]`. -/
@[simp] theorem endpointZeroIndexFormKerEquivExpKer_symm_apply
    (hγ : IsPiecewiseContMDiffOn I n (fun t : ℝ ↦ riemannianExp I M p (t • v)) 0 b)
    (hb : b ∈ geodesicInterval I M p v) (hn : 1 ≤ n)
    (w : LinearMap.ker (mfderiv 𝓘(ℝ, TangentSpace I p) I
      (riemannianExp I M p) (b • v)).toLinearMap) (t : Icc 0 b) :
    ((endpointZeroIndexFormKerEquivExpKer hγ hb hn).symm w).val.val.val t =
      mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) ((t : ℝ) • v) ((t : ℝ) • w.val) := by
  simp [endpointZeroIndexFormKerEquivExpKer, t.property]

/-- Along `t ↦ exp_p(t v)` on `[0, b]` (`0 < b`), the nullity of `endpointZeroIndexForm` equals
`dim ker(d(exp_p)_{b v})`. -/
theorem finrank_ker_endpointZeroIndexForm_riemannianExp
    (hγ : IsPiecewiseContMDiffOn I n (fun t : ℝ ↦ riemannianExp I M p (t • v)) 0 b)
    (hb : b ∈ geodesicInterval I M p v) (hn : 1 ≤ n) :
    Module.finrank ℝ (LinearMap.ker (endpointZeroIndexForm hγ hn)) =
      Module.finrank ℝ (LinearMap.ker (mfderiv 𝓘(ℝ, TangentSpace I p) I
        (riemannianExp I M p) (b • v)).toLinearMap) :=
  (endpointZeroIndexFormKerEquivExpKer hγ hb hn).finrank_eq

/-- Along `t ↦ exp_p(t v)` on `[0, b]` (`0 < b`), `endpointZeroIndexForm` is nondegenerate iff
`d(exp_p)_{b v}` is injective. -/
theorem nondegenerate_endpointZeroIndexForm_riemannianExp_iff
    (hγ : IsPiecewiseContMDiffOn I n (fun t : ℝ ↦ riemannianExp I M p (t • v)) 0 b)
    (hb : b ∈ geodesicInterval I M p v) (hn : 1 ≤ n) :
    (endpointZeroIndexForm hγ hn).Nondegenerate ↔
      Function.Injective (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (b • v)) := by
  rw [nondegenerate_endpointZeroIndexForm_iff hγ (isGeodesicCurveOn_riemannianExp_Icc hγ.lt hb) hn,
    isConjugateOn_iff_not_injective_mfderiv_riemannianExp
      (isGeodesicCurveOn_riemannianExp_Icc hγ.lt hb) isPreconnected_Icc
      (ordConnected_geodesicInterval.out zero_mem_geodesicInterval hb)
      (left_mem_Icc.2 hγ.lt.le) (right_mem_Icc.2 hγ.lt.le) hγ.lt.ne', not_not]

end RadialExponential

end TauCeti.Manifold
