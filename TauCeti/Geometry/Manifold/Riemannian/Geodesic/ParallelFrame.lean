/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.ConstantSpeed
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Parallel
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Uniform
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Reparametrization
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Smoothness
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Metric
import TauCeti.Topology.Order.Interval.Basic

/-!
# Parallel fields along geodesics

Along a geodesic, any tangent vector at `γ τ` extends to a smooth parallel field on
`[a, b]`, provided `τ ∈ [a, b]` and the interval is contained in the interior of the geodesic's
parameter set. Any indexed family extends with its pairwise inner products preserved; an
orthonormal basis extends to orthonormal bases along the interval. These fields provide the
parallel directions used to construct test fields for the index form.

Compact-interval fields have arbitrary auxiliary values outside the specified interval.
For an all-time geodesic, compatible fields on expanding compact intervals give one smooth
parallel field on the whole real line. Uniqueness and preservation of inner products use
`CovariantDerivative.IsMetricCompatible.eq_of_alongCurve_eq_zero` and
`CovariantDerivative.IsMetricCompatible.inner_eq_of_alongCurve_eq_zero`.

The construction uses radial parallel transport in normal domains
(`TauCeti.Manifold.IsNormalDomain.radialParallelLinearMap`). Compactness of the image of
`[a, b]` supplies a uniform normal-ball radius. A smaller time radius keeps each local piece
inside the geodesic's parameter domain. Restarting at `τ` locally identifies the geodesic with
`t ↦ exp_(γ τ) ((t - τ) • γ'(τ))`, and finitely many radial pieces are glued by uniqueness.

## Main results

* `TauCeti.Manifold.IsGeodesicCurveOn.exists_parallel`: smooth parallel fields on a compact
  interval, with initial data at any point of the interval.
* `TauCeti.Manifold.IsGeodesicCurveOn.exists_parallel_inner_eq`: parallel extension of any
  indexed family preserving pairwise inner products.
* `TauCeti.Manifold.IsGeodesicCurveOn.exists_parallel_orthonormalBasis`: parallel extension
  of an orthonormal basis, with a bundled basis at every point of the interval.
* `TauCeti.Manifold.IsGeodesicCurve.exists_parallel`,
  `TauCeti.Manifold.IsGeodesicCurve.exists_parallel_inner_eq` and
  `TauCeti.Manifold.IsGeodesicCurve.exists_parallel_orthonormalBasis`: the corresponding
  results on the whole real line for an all-time geodesic.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 4.
-/

public section

open Bundle CovariantDerivative Filter Set
open scoped ContDiff Manifold Topology InnerProductSpace

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

omit [I.Boundaryless] [T2Space M] in
/-- Gluing a parallel field on `[l, τ]` and a parallel field on `[m, r]`, `l ≤ m < τ ≤ r`, which
agree at `τ`, gives a parallel field on `[l, r]` equal to the first one on `[l, τ]`. -/
private theorem exists_parallel_glue {γ : ℝ → M}
    {l m τ r : ℝ} (hlm : l ≤ m) (hmτ : m < τ) (hτr : τ ≤ r) {P L : ∀ t, TangentSpace I (γ t)}
    (hP : ∀ t ∈ Icc l τ, ContMDiffAt 𝓘(ℝ) I.tangent ∞ (fun t ↦ TotalSpace.mk' E (γ t) (P t)) t ∧
      alongCurve (leviCivitaConnection I M) γ P t = 0)
    (hL : ∀ t ∈ Icc m r, ContMDiffAt 𝓘(ℝ) I.tangent ∞ (fun t ↦ TotalSpace.mk' E (γ t) (L t)) t ∧
      alongCurve (leviCivitaConnection I M) γ L t = 0) (hPL : P τ = L τ) :
    ∃ G : ∀ t, TangentSpace I (γ t), EqOn G P (Icc l τ) ∧ ∀ t ∈ Icc l r,
      ContMDiffAt 𝓘(ℝ) I.tangent ∞ (fun t ↦ TotalSpace.mk' E (γ t) (G t)) t ∧
      alongCurve (leviCivitaConnection I M) γ G t = 0 := by
  have hagree (t : ℝ) (ht : t ∈ Icc m τ) : P t = L t :=
    (isMetricCompatible_leviCivitaConnection I).eq_of_alongCurve_eq_zero_of_mdifferentiableAt
      isPreconnected_Icc
      (fun u hu ↦ (hP u ⟨hlm.trans hu.1, hu.2⟩).1.mdifferentiableAt (by simp))
      (fun u hu ↦ (hL u ⟨hu.1, hu.2.trans hτr⟩).1.mdifferentiableAt (by simp))
      (fun u hu ↦ (hP u ⟨hlm.trans hu.1, hu.2⟩).2)
      (fun u hu ↦ (hL u ⟨hu.1, hu.2.trans hτr⟩).2) ⟨hmτ.le, le_rfl⟩ ht hPL
  let G : ∀ t, TangentSpace I (γ t) := fun t ↦ if t ≤ τ then P t else L t
  have hlocal (t : ℝ) (X : ∀ t, TangentSpace I (γ t)) (hGX : ∀ᶠ u in 𝓝 t, G u = X u)
      (hX : ContMDiffAt 𝓘(ℝ) I.tangent ∞ (fun t ↦ TotalSpace.mk' E (γ t) (X t)) t ∧
        alongCurve (leviCivitaConnection I M) γ X t = 0) :
      ContMDiffAt 𝓘(ℝ) I.tangent ∞ (fun t ↦ TotalSpace.mk' E (γ t) (G t)) t ∧
        alongCurve (leviCivitaConnection I M) γ G t = 0 := by
    refine ⟨hX.1.congr_of_eventuallyEq
      (hGX.mono fun u ↦ congrArg (TotalSpace.mk' E (γ u))), ?_⟩
    rw [alongCurve_congr (leviCivitaConnection I M) γ G hGX]
    exact hX.2
  refine ⟨G, fun t ht ↦ ite_eq_left ht.2, fun t ht ↦ ?_⟩
  rcases lt_trichotomy t τ with hlt | rfl | hgt
  · exact hlocal t P ((eventually_lt_nhds hlt).mono fun u hu ↦ by simp [G, hu.le])
      (hP t ⟨ht.1, hlt.le⟩)
  · refine hlocal t L ((eventually_gt_nhds hmτ).mono fun u hu ↦ ?_) (hL t ⟨hmτ.le, hτr⟩)
    by_cases hu' : u ≤ t
    · simp only [G, hu', ↓reduceIte]
      exact hagree u ⟨hu.le, hu'⟩
    · simp only [G, hu', ↓reduceIte]
  · exact hlocal t L ((eventually_gt_nhds hgt).mono fun u hu ↦ by
      simp [G, not_le.2 hu])
      (hL t ⟨by linarith, ht.2⟩)

/-- Uniform local parallel fields on a compact subinterval of an open-interval geodesic. -/
private theorem IsGeodesicCurveOn.exists_pos_forall_exists_parallel {γ : ℝ → M}
    {c d : ℝ} (hγ : IsGeodesicCurveOn I γ (Ioo c d)) (a b : ℝ)
    (hab : a ≤ b) (hca : c < a) (hbd : b < d) :
    ∃ ρ > 0, ∀ τ ∈ Icc a b, ∀ z : TangentSpace I (γ τ), ∃ L : ∀ t, TangentSpace I (γ t),
      L τ = z ∧ ∀ t ∈ Icc (τ - ρ) (τ + ρ),
        ContMDiffAt 𝓘(ℝ) I.tangent ∞ (fun t ↦ TotalSpace.mk' E (γ t) (L t)) t ∧
        alongCurve (leviCivitaConnection I M) γ L t = 0 := by
  have hsub : Icc a b ⊆ Ioo c d :=
    fun t ht ↦ ⟨hca.trans_le ht.1, ht.2.trans_lt hbd⟩
  have hK : IsCompact (γ '' Icc a b) :=
    isCompact_Icc.image_of_continuousOn (hγ.contMDiffOn.continuousOn.mono hsub)
  obtain ⟨r, hr, _, _, hKU, hnd⟩ :=
    hK.exists_pos_exists_isOpen_superset_forall_isNormalDomain_ball (I := I)
  set C := ‖curveVelocity I γ a‖ with hC
  have hC0 : 0 ≤ C := norm_nonneg _
  set ρ := min (r / (2 * (C + 1))) (min (a - c) (d - b) / 2)
  have hρ : 0 < ρ := by positivity
  have hρN : ρ ≤ r / (2 * (C + 1)) := min_le_left _ _
  have hρa : ρ < a - c := by
    have := min_le_right (r / (2 * (C + 1))) (min (a - c) (d - b) / 2)
    linarith [min_le_left (a - c) (d - b)]
  have hρb : ρ < d - b := by
    have := min_le_right (r / (2 * (C + 1))) (min (a - c) (d - b) / 2)
    linarith [min_le_right (a - c) (d - b)]
  refine ⟨ρ, hρ, fun τ hτ z ↦ ?_⟩
  have hspeed := hγ.norm_curveVelocityWithin_eq isPreconnected_Ioo (hsub hτ)
    (hsub ⟨le_rfl, hab⟩)
  rw [curveVelocityWithin_of_mem_nhds (isOpen_Ioo.mem_nhds (hsub hτ)),
    curveVelocityWithin_of_mem_nhds (isOpen_Ioo.mem_nhds (hsub ⟨le_rfl, hab⟩))] at hspeed
  have hseg : ∀ t ∈ Icc (τ - ρ) (τ + ρ),
      (t - τ) • curveVelocity I γ τ ∈ Metric.ball (0 : TangentSpace I (γ τ)) r := by
    intro t ht
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, hspeed, ← hC]
    calc |t - τ| * C ≤ r / (2 * (C + 1)) * C :=
          mul_le_mul_of_nonneg_right
            ((abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩).trans hρN) hC0
      _ < r := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
  exact (hnd (γ τ) (hKU (mem_image_of_mem γ hτ))).exists_parallel_of_eqOn
    (curveVelocity I γ τ) (by constructor <;> linarith) hseg (s := Ioo c d) isOpen_Ioo
    (fun t ht ↦ ⟨by linarith [hτ.1, ht.1], by linarith [hτ.2, ht.2]⟩)
    (fun t ht ↦ hγ.eq_riemannianExp_sub_smul
      (by rw [interior_Ioo]; exact ordConnected_Ioo.uIcc_subset (hsub hτ) ht)) z

/-- Forward extension with a parallel overlap to the left of the initial parameter. -/
private theorem IsGeodesicCurveOn.exists_parallel_right {γ : ℝ → M}
    {c d : ℝ} (hγ : IsGeodesicCurveOn I γ (Ioo c d)) (a b : ℝ)
    (hab : a ≤ b) (hca : c < a) (hbd : b < d) (w : TangentSpace I (γ a)) :
    ∃ δ > 0, ∃ P : ∀ t, TangentSpace I (γ t), P a = w ∧ ∀ t ∈ Icc (a - δ) b,
      ContMDiffAt 𝓘(ℝ) I.tangent ∞ (fun t ↦ TotalSpace.mk' E (γ t) (P t)) t ∧
      alongCurve (leviCivitaConnection I M) γ P t = 0 := by
  obtain ⟨ρ, hρ, hloc⟩ := hγ.exists_pos_forall_exists_parallel a b hab hca hbd
  have hstep (k : ℕ) : ∃ P : ∀ t, TangentSpace I (γ t), P a = w ∧
      ∀ t ∈ Icc (a - ρ / 2) (min (a + k * (ρ / 2)) b),
        ContMDiffAt 𝓘(ℝ) I.tangent ∞ (fun t ↦ TotalSpace.mk' E (γ t) (P t)) t ∧
        alongCurve (leviCivitaConnection I M) γ P t = 0 := by
    induction k with
    | zero =>
      obtain ⟨L, hLa, hL⟩ := hloc a ⟨le_rfl, hab⟩ w
      refine ⟨L, hLa, fun t ht ↦ hL t ⟨by linarith [ht.1], ?_⟩⟩
      have := ht.2
      simp only [CharP.cast_eq_zero, zero_mul, add_zero, min_eq_left hab] at this
      linarith
    | succ k ih =>
      obtain ⟨P, hPa, hP⟩ := ih
      set τ := min (a + k * (ρ / 2)) b
      have hτ : τ ∈ Icc a b := ⟨le_min (by nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) hab,
        min_le_right _ _⟩
      obtain ⟨L, hLτ, hL⟩ := hloc τ hτ (P τ)
      obtain ⟨G, hGP, hG⟩ := exists_parallel_glue (le_max_left (a - ρ / 2) (τ - ρ))
        (max_lt (by linarith [hτ.1]) (by linarith)) (by linarith) hP
        (fun t ht ↦ hL t ⟨le_trans (le_max_right _ _) ht.1, ht.2⟩) hLτ.symm
      refine ⟨G, (hGP ⟨by linarith, hτ.1⟩).trans hPa, fun t ht ↦ hG t ⟨ht.1, ?_⟩⟩
      have h2 : min (a + ↑(k + 1) * (ρ / 2)) b ≤ τ + ρ / 2 := by
        rw [← min_add_add_right]
        exact min_le_min (by push_cast; linarith) (by linarith)
      linarith [ht.2]
  obtain ⟨k, hk⟩ := exists_nat_gt ((b - a) / (ρ / 2))
  obtain ⟨P, hPa, hP⟩ := hstep k
  have hkb : min (a + k * (ρ / 2)) b = b :=
    min_eq_right (by linarith [(div_lt_iff₀ (by positivity : (0 : ℝ) < ρ / 2)).mp hk])
  exact ⟨ρ / 2, by positivity, P, hPa,
    fun t ht ↦ hP t ⟨ht.1, by rw [hkb]; exact ht.2⟩⟩

/-- Along a geodesic on an open interval, every tangent vector at `γ τ`, with
`τ ∈ [a, b]`, extends to a smooth parallel field on `[a, b]`. -/
private theorem IsGeodesicCurveOn.exists_parallel_Ioo {γ : ℝ → M} {c d : ℝ}
    (hγ : IsGeodesicCurveOn I γ (Ioo c d)) {a b τ : ℝ} (hsub : Icc a b ⊆ Ioo c d)
    (hτ : τ ∈ Icc a b) (w : TangentSpace I (γ τ)) :
    ∃ P : ∀ t, TangentSpace I (γ t), P τ = w ∧ ∀ t ∈ Icc a b,
      ContMDiffAt 𝓘(ℝ) I.tangent ∞ (fun t ↦ TotalSpace.mk' E (γ t) (P t)) t ∧
      alongCurve (leviCivitaConnection I M) γ P t = 0 := by
  obtain ⟨δ, hδ, P, hPτ, hP⟩ := hγ.exists_parallel_right τ b hτ.2 (hsub hτ).1
    (hsub ⟨hτ.1.trans hτ.2, le_rfl⟩).2 w
  rcases hτ.1.eq_or_lt with rfl | haτ
  · exact ⟨P, hPτ, fun t ht ↦ hP t ⟨by linarith [ht.1], ht.2⟩⟩
  have hrev : IsGeodesicCurveOn I (fun t ↦ γ (0 - t)) (Ioo (-d) (-c)) := by
    simpa only [Function.comp_def, neg_one_mul, zero_sub, add_zero] using
      hγ.comp_affine (-1) 0 (uniqueDiffOn_Ioo (-d) (-c))
        (fun t ht ↦ ⟨by dsimp; linarith [ht.2], by dsimp; linarith [ht.1]⟩)
  -- Reflect both the curve and the interval, then identify the double reflection with γ.
  obtain ⟨ε, hε, L, hLτ, hL⟩ := hrev.exists_parallel_right (0 - τ) (0 - a)
    (by linarith [hτ.1]) (by linarith [(hsub hτ).2])
    (by linarith [(hsub ⟨le_rfl, hτ.1.trans hτ.2⟩).1]) w
  -- Transport the entire dependent existence statement to preserve its fibre structures.
  let ParallelOn (c : ℝ → M) : Prop :=
    ∃ Q : ∀ t, TangentSpace I (c t), Q τ = w ∧ ∀ t ∈ Icc a τ,
      ContMDiffAt 𝓘(ℝ) I.tangent ∞ (fun t ↦ TotalSpace.mk' E (c t) (Q t)) t ∧
      alongCurve (leviCivitaConnection I M) c Q t = 0
  have hback : ParallelOn (fun t ↦ γ (0 - (0 - t))) := by
    refine ⟨fun t ↦ L (0 - t), hLτ, fun t ht ↦ ?_⟩
    have hLt := hL (0 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hn : ContDiff ℝ ∞ (fun t : ℝ ↦ 0 - t) := contDiff_const.sub contDiff_id
    refine ⟨hLt.1.comp t hn.contMDiff.contMDiffAt, ?_⟩
    exact (alongCurve_comp_const_sub (leviCivitaConnection I M)
      (fun t ↦ γ (0 - t)) L 0 t).trans (by rw [hLt.2, neg_zero])
  have hdouble : (fun t ↦ γ (0 - (0 - t))) = γ := by
    funext t
    rw [zero_sub, zero_sub, neg_neg]
  obtain ⟨Q, hQτ, hQ⟩ := (congrArg ParallelOn hdouble).mp hback
  obtain ⟨G, hGQ, hG⟩ := exists_parallel_glue
    (le_max_left a (τ - δ)) (max_lt haτ (by linarith)) hτ.2 hQ
    (fun t ht ↦ hP t ⟨(le_max_right _ _).trans ht.1, ht.2⟩)
    (hQτ.trans hPτ.symm)
  exact ⟨G, (hGQ ⟨hτ.1, le_rfl⟩).trans hQτ, hG⟩

/-- Along a geodesic, any tangent vector at `γ τ`, with `τ ∈ [a, b] ⊆ interior s`,
extends to a smooth parallel field on `[a, b]`. -/
theorem IsGeodesicCurveOn.exists_parallel {γ : ℝ → M} {s : Set ℝ}
    (hγ : IsGeodesicCurveOn I γ s) {a b τ : ℝ} (hsub : Icc a b ⊆ interior s)
    (hτ : τ ∈ Icc a b) (w : TangentSpace I (γ τ)) :
    ∃ P : ∀ t, TangentSpace I (γ t), P τ = w ∧ ∀ t ∈ Icc a b,
      ContMDiffAt 𝓘(ℝ) I.tangent ∞ (fun t ↦ TotalSpace.mk' E (γ t) (P t)) t ∧
      alongCurve (leviCivitaConnection I M) γ P t = 0 := by
  have hab := hτ.1.trans hτ.2
  obtain ⟨c, d, hcd, hs⟩ := isOpen_interior.exists_Ioo_subset_of_uIcc_subset
    (a := a) (b := b) (by rwa [uIcc_of_le hab])
  exact (hγ.mono (uniqueDiffOn_Ioo c d) (hs.trans interior_subset)).exists_parallel_Ioo
    (by rwa [uIcc_of_le hab] at hcd) hτ w

/-- Any indexed family at `γ τ`, with `τ ∈ [a, b] ⊆ interior s`, along a geodesic on `s`
extends to smooth parallel fields on `[a, b]` preserving all pairwise inner products. -/
theorem IsGeodesicCurveOn.exists_parallel_inner_eq {γ : ℝ → M} {s : Set ℝ}
    (hγ : IsGeodesicCurveOn I γ s) {a b τ : ℝ} (hsub : Icc a b ⊆ interior s)
    (hτ : τ ∈ Icc a b) {ι : Type*} (e : ι → TangentSpace I (γ τ)) :
    ∃ P : ι → ∀ t, TangentSpace I (γ t), (∀ i, P i τ = e i) ∧
      (∀ i, ∀ t ∈ Icc a b,
        ContMDiffAt 𝓘(ℝ) I.tangent ∞ (fun t ↦ TotalSpace.mk' E (γ t) (P i t)) t ∧
        alongCurve (leviCivitaConnection I M) γ (P i) t = 0) ∧
      ∀ t ∈ Icc a b, ∀ i j, ⟪P i t, P j t⟫_ℝ = ⟪e i, e j⟫_ℝ := by
  choose P hPa hP using fun i ↦ hγ.exists_parallel hsub hτ (e i)
  refine ⟨P, hPa, hP, fun t ht i j ↦ ?_⟩
  have hγd (u : ℝ) (hu : u ∈ Icc a b) : MDifferentiableAt 𝓘(ℝ) I γ u :=
    (hγ.contMDiffAt_infty (mem_interior_iff_mem_nhds.mp (hsub hu))).mdifferentiableAt (by simp)
  have hcoord (k : ι) (u : ℝ) (hu : u ∈ Icc a b) :
      DifferentiableAt ℝ (sectionCoord ℝ (F := E) γ (P k) (γ u)) u :=
    differentiableAt_sectionCoord γ (P k) ((hP k u hu).1.mdifferentiableAt (by simp))
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ u))
  rw [(isMetricCompatible_leviCivitaConnection I).inner_eq_of_alongCurve_eq_zero
    isPreconnected_Icc hγd (hcoord i) (hcoord j) (fun u hu ↦ (hP i u hu).2)
    (fun u hu ↦ (hP j u hu).2) ht hτ, hPa, hPa]

/-- An orthonormal basis at `γ τ`, with `τ ∈ [a, b] ⊆ interior s`, along a geodesic on `s`
extends to smooth parallel fields forming an orthonormal basis at each point of `[a, b]`. -/
theorem IsGeodesicCurveOn.exists_parallel_orthonormalBasis {γ : ℝ → M}
    {s : Set ℝ} (hγ : IsGeodesicCurveOn I γ s) {a b τ : ℝ}
    (hsub : Icc a b ⊆ interior s) (hτ : τ ∈ Icc a b) {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℝ (TangentSpace I (γ τ))) :
    ∃ P : ι → ∀ t, TangentSpace I (γ t), (∀ i, P i τ = e i) ∧
      (∀ i, ∀ t ∈ Icc a b,
        ContMDiffAt 𝓘(ℝ) I.tangent ∞ (fun t ↦ TotalSpace.mk' E (γ t) (P i t)) t ∧
        alongCurve (leviCivitaConnection I M) γ (P i) t = 0) ∧
      ∀ t ∈ Icc a b, ∃ e' : OrthonormalBasis ι ℝ (TangentSpace I (γ t)),
        ∀ i, e' i = P i t := by
  classical
  obtain ⟨P, hPa, hP, hinner⟩ := hγ.exists_parallel_inner_eq hsub hτ e
  refine ⟨P, hPa, hP, fun t ht ↦ ?_⟩
  have hon : Orthonormal ℝ (fun i ↦ P i t) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [hinner t ht, orthonormal_iff_ite.mp e.orthonormal]
  have hcard : Fintype.card ι = Module.finrank ℝ (TangentSpace I (γ t)) := by
    rw [← Module.finrank_eq_card_basis e.toBasis]
    exact (TauCeti.finrank_tangentSpace (I := I) (γ τ)).trans
      (TauCeti.finrank_tangentSpace (I := I) (γ t)).symm
  refine ⟨OrthonormalBasis.mk hon (hon.linearIndependent.span_eq_top_of_card_eq_finrank' hcard).ge,
    fun i ↦ ?_⟩
  exact congrFun (OrthonormalBasis.coe_mk _ _) i

/-- Along an all-time geodesic, every tangent vector extends to a smooth parallel field on the
whole parameter line. -/
theorem IsGeodesicCurve.exists_parallel {γ : ℝ → M} (hγ : IsGeodesicCurve I γ)
    (a : ℝ) (w : TangentSpace I (γ a)) :
    ∃ P : ∀ t, TangentSpace I (γ t), P a = w ∧ ∀ t,
      ContMDiffAt 𝓘(ℝ) I.tangent ∞ (fun t ↦ TotalSpace.mk' E (γ t) (P t)) t ∧
      alongCurve (leviCivitaConnection I M) γ P t = 0 := by
  have hcompact (n : ℕ) : ∃ P : ∀ t, TangentSpace I (γ t), P a = w ∧
      ∀ t ∈ Icc (a - (n + 1)) (a + (n + 1)),
        ContMDiffAt 𝓘(ℝ) I.tangent ∞ (fun t ↦ TotalSpace.mk' E (γ t) (P t)) t ∧
        alongCurve (leviCivitaConnection I M) γ P t = 0 :=
    (isGeodesicCurveOn_univ.mpr hγ).exists_parallel (by simp)
      (by constructor <;> linarith [Nat.cast_nonneg (α := ℝ) n]) w
  choose P hPa hP using hcompact
  have ha (n : ℕ) : a ∈ Icc (a - (n + 1)) (a + (n + 1)) := by
    constructor <;> linarith [Nat.cast_nonneg (α := ℝ) n]
  have hagree (j k : ℕ) {u : ℝ} (hj : u ∈ Icc (a - (j + 1)) (a + (j + 1)))
      (hk : u ∈ Icc (a - (k + 1)) (a + (k + 1))) : P j u = P k u :=
    (isMetricCompatible_leviCivitaConnection I).eq_of_alongCurve_eq_zero_of_mdifferentiableAt
      isPreconnected_uIcc
      (fun t ht ↦ (hP j t (ordConnected_Icc.uIcc_subset (ha j) hj ht)).1.mdifferentiableAt
        (by simp))
      (fun t ht ↦ (hP k t (ordConnected_Icc.uIcc_subset (ha k) hk ht)).1.mdifferentiableAt
        (by simp))
      (fun t ht ↦ (hP j t (ordConnected_Icc.uIcc_subset (ha j) hj ht)).2)
      (fun t ht ↦ (hP k t (ordConnected_Icc.uIcc_subset (ha k) hk ht)).2)
      left_mem_uIcc right_mem_uIcc ((hPa j).trans (hPa k).symm)
  let n : ℝ → ℕ := fun t ↦ ⌈|t - a|⌉₊
  have hcover (t : ℝ) : t ∈ Ioo (a - (n t + 1)) (a + (n t + 1)) := by
    have hb : |t - a| ≤ (n t : ℝ) := Nat.le_ceil _
    constructor <;> linarith [neg_abs_le (t - a), le_abs_self (t - a)]
  let G : ∀ t, TangentSpace I (γ t) := fun t ↦ P (n t) t
  refine ⟨G, hPa (n a), fun t ↦ ?_⟩
  have heq : G =ᶠ[𝓝 t] P (n t) :=
    Filter.Eventually.mono (isOpen_Ioo.mem_nhds (hcover t)) fun u hu ↦
      hagree (n u) (n t) (Ioo_subset_Icc_self (hcover u)) (Ioo_subset_Icc_self hu)
  refine ⟨(hP (n t) t (Ioo_subset_Icc_self (hcover t))).1.congr_of_eventuallyEq
    (heq.mono fun u ↦ congrArg (TotalSpace.mk' E (γ u))), ?_⟩
  rw [alongCurve_congr (leviCivitaConnection I M) γ G heq]
  exact (hP (n t) t (Ioo_subset_Icc_self (hcover t))).2

/-- Any indexed family at one point of an all-time geodesic extends to smooth parallel fields
on the whole line, preserving pairwise inner products. -/
theorem IsGeodesicCurve.exists_parallel_inner_eq {γ : ℝ → M} (hγ : IsGeodesicCurve I γ)
    (a : ℝ) {ι : Type*} (e : ι → TangentSpace I (γ a)) :
    ∃ P : ι → ∀ t, TangentSpace I (γ t), (∀ i, P i a = e i) ∧
      (∀ i t, ContMDiffAt 𝓘(ℝ) I.tangent ∞
        (fun t ↦ TotalSpace.mk' E (γ t) (P i t)) t ∧
        alongCurve (leviCivitaConnection I M) γ (P i) t = 0) ∧
      ∀ t i j, ⟪P i t, P j t⟫_ℝ = ⟪e i, e j⟫_ℝ := by
  choose P hPa hP using fun i ↦ hγ.exists_parallel a (e i)
  refine ⟨P, hPa, hP, fun t i j ↦ ?_⟩
  have hcoord (k : ι) (u : ℝ) :
      DifferentiableAt ℝ (sectionCoord ℝ (F := E) γ (P k) (γ u)) u :=
    differentiableAt_sectionCoord γ (P k) ((hP k u).1.mdifferentiableAt (by simp))
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ u))
  rw [(isMetricCompatible_leviCivitaConnection I).inner_eq_of_alongCurve_eq_zero
    (s := univ) isPreconnected_univ
    (fun u _ ↦ hγ.contMDiff_infty.mdifferentiable (by simp) u)
    (fun u _ ↦ hcoord i u) (fun u _ ↦ hcoord j u) (fun u _ ↦ (hP i u).2)
    (fun u _ ↦ (hP j u).2) (mem_univ t) (mem_univ a), hPa, hPa]

/-- An orthonormal basis at one point of an all-time geodesic extends to smooth parallel fields
forming an orthonormal basis at every parameter on the whole line. -/
theorem IsGeodesicCurve.exists_parallel_orthonormalBasis {γ : ℝ → M}
    (hγ : IsGeodesicCurve I γ) (a : ℝ) {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℝ (TangentSpace I (γ a))) :
    ∃ P : ι → ∀ t, TangentSpace I (γ t), (∀ i, P i a = e i) ∧
      (∀ i t, ContMDiffAt 𝓘(ℝ) I.tangent ∞
        (fun t ↦ TotalSpace.mk' E (γ t) (P i t)) t ∧
        alongCurve (leviCivitaConnection I M) γ (P i) t = 0) ∧
      ∀ t, ∃ e' : OrthonormalBasis ι ℝ (TangentSpace I (γ t)), ∀ i, e' i = P i t := by
  classical
  obtain ⟨P, hPa, hP, hinner⟩ := hγ.exists_parallel_inner_eq a e
  refine ⟨P, hPa, hP, fun t ↦ ?_⟩
  have hon : Orthonormal ℝ (fun i ↦ P i t) :=
    orthonormal_iff_ite.mpr fun i j ↦ (hinner t i j).trans
      (orthonormal_iff_ite.mp e.orthonormal i j)
  have hcard : Fintype.card ι = Module.finrank ℝ (TangentSpace I (γ t)) := by
    rw [← Module.finrank_eq_card_basis e.toBasis]
    exact (TauCeti.finrank_tangentSpace (I := I) (γ a)).trans
      (TauCeti.finrank_tangentSpace (I := I) (γ t)).symm
  refine ⟨OrthonormalBasis.mk hon (hon.linearIndependent.span_eq_top_of_card_eq_finrank' hcard).ge,
    fun i ↦ ?_⟩
  exact congrFun (OrthonormalBasis.coe_mk _ _) i

end TauCeti.Manifold
