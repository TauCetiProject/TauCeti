/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Reparametrization
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Smoothness
public import TauCeti.Geometry.Manifold.IntegralCurve.Maximal

/-!
# Maximal intervals of geodesics

For initial data `(p, v)`, this file defines the set of times covered by open intervals carrying
geodesic witnesses with those initial data.  It proves local existence, uniqueness on overlapping
intervals, and that this set is an open interval containing zero.  The key homogeneity theorem
identifies the interval for `a • v` with the inverse scalar image of the interval for `v`; this is
the domain statement used later by the exponential map.

The interval is defined as a union of geodesic witnesses, so the definition itself does not choose
one geodesic on the union.  Its membership characterization is suitable for downstream arguments
that need an actual witness; a chosen maximal curve and finite-endpoint extension are separate
results.

## Main definitions and results

* `TauCeti.Manifold.geodesicInterval` is the maximal interval of geodesic existence.
* `TauCeti.Manifold.exists_geodesicCurveOnFrom_Ioo` gives local geodesic existence.
* `TauCeti.Manifold.isOpen_geodesicInterval` and
  `TauCeti.Manifold.ordConnected_geodesicInterval` give its interval structure.
* `TauCeti.Manifold.mem_geodesicInterval_iff` extracts a geodesic witness from membership.
* `TauCeti.Manifold.IsGeodesicCurveOnFrom.eqOn_of_inter` gives uniqueness on overlapping intervals.
* `TauCeti.Manifold.mem_geodesicInterval_smul_iff` is the precise nonzero scalar domain relation.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 3, §2.
* J. Lee, *Introduction to Riemannian Manifolds*, GTM 176, 2018, Ch. 5.
-/

-- Roadmap: HopfRinow

public section

open Bundle Filter Function Manifold Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable [FiniteDimensional ℝ E] [I.Boundaryless]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- A smooth Riemannian manifold has a geodesic with any prescribed initial data on a neighbourhood
of the initial parameter. -/
theorem exists_geodesicCurveOnFrom
    (p : M) (v : TangentSpace I p) :
    ∃ s ∈ 𝓝 (0 : ℝ), ∃ γ : ℝ → M, IsGeodesicCurveOnFrom I γ s p v := by
  let z₀ : TangentBundle I M := TotalSpace.mk' E p v
  have hv : CMDiff 1 (fun z : TangentBundle I M ↦
      (⟨z, geodesicSpray I M z⟩ : TangentBundle I.tangent (TangentBundle I M))) := by
    have h := contMDiff_geodesicSpray (I := I) (M := M) (n := (1 : ℕ∞ω))
      (m := ∞) (k := ∞) (by norm_num) (by norm_num)
    exact h.of_le (by norm_num)
  obtain ⟨γ, hγ₀, hγ⟩ :=
    exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless (I := I.tangent)
      (x₀ := z₀) (t₀ := 0) hv.contMDiffAt
  obtain ⟨s, hs, hγs⟩ := isMIntegralCurveAt_iff.mp hγ
  obtain ⟨u, hu, huopen, hu0⟩ := mem_nhds_iff.mp hs
  have hγu : IsMIntegralCurveOn γ (geodesicSpray I M) u := hγs.mono hu
  have hbase : ContMDiffOn 𝓘(ℝ, ℝ) I 2 (fun t ↦ (γ t).proj) u := by
    apply contMDiffOn_of_locally_contMDiffOn
    intro t ht
    have hγt : IsMIntegralCurveAt γ (geodesicSpray I M) t :=
      hγu.isMIntegralCurveAt (huopen.mem_nhds ht)
    have hγt2 : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 2 γ t :=
      IsMIntegralCurveAt.local_contMDiffAt_two hγt hv
    have hproj : ContMDiffAt I.tangent I 2 TotalSpace.proj (γ t) :=
      Bundle.contMDiffAt_proj (fun x : M ↦ TangentSpace I x) (IB := I) (n := (2 : ℕ∞ω))
    have hbase_t : ContMDiffAt 𝓘(ℝ, ℝ) I 2 ((fun z : TangentBundle I M => z.proj) ∘ γ) t :=
      hproj.comp t hγt2
    obtain ⟨u, hu, h'u⟩ := contMDiffAt_iff_contMDiffOn_nhds (n := (2 : ℕ∞ω))
      (by norm_num) |>.mp hbase_t
    obtain ⟨w, hwsub, hwopen, hwt⟩ := mem_nhds_iff.mp hu
    refine ⟨w, hwopen, hwt, ?_⟩
    exact (h'u.mono (inter_subset_right.trans hwsub)).congr
      (fun x _ => rfl)
  let hsu : UniqueDiffOn ℝ u := huopen.uniqueDiffOn
  let base : ℝ → M := fun t => (γ t).proj
  have hlift : EqOn γ (curveVelocityLiftWithin I base u) u := by
    intro r hr
    exact eq_curveVelocityLiftWithin_of_isMIntegralCurveOn (s := u) (t := r)
      (hsu r hr) hγu hr
  have hgeo : IsGeodesicCurveOn I base u :=
    (isMIntegralCurveOn_curveVelocityLiftWithin_iff hsu hbase).1
      (hγu.congr fun r hr => (hlift hr).symm)
  refine ⟨u, huopen.mem_nhds hu0, base, hgeo, hu0, ?_⟩
  simpa only [curveVelocityLiftWithin_apply, base, z₀] using (hlift hu0).symm.trans hγ₀

/-- A neighbourhood of zero contains an interval of geodesic existence. -/
theorem exists_geodesicCurveOnFrom_Ioo
    (p : M) (v : TangentSpace I p) :
    ∃ a b : ℝ, a < b ∧ 0 ∈ Ioo a b ∧
      ∃ γ : ℝ → M, IsGeodesicCurveOnFrom I γ (Ioo a b) p v := by
  obtain ⟨s, hs, γ, hγ⟩ := exists_geodesicCurveOnFrom (I := I) (M := M) p v
  obtain ⟨u, hu, huopen, hu0⟩ := mem_nhds_iff.mp hs
  obtain ⟨ε, hε, hεball⟩ := Metric.isOpen_iff.mp huopen 0 hu0
  rw [Real.ball_eq_Ioo] at hεball
  have hεball' : Ioo (-ε) ε ⊆ u := by
    simpa only [zero_sub, zero_add] using hεball
  have hγu : IsGeodesicCurveOnFrom I γ u p v := hγ.mono huopen.uniqueDiffOn hu hu0
  refine ⟨-ε, ε, by linarith, ⟨by linarith, by linarith⟩, γ, ?_⟩
  exact hγu.mono (uniqueDiffOn_Ioo _ _) hεball' ⟨by linarith, by linarith⟩

/-! ### The maximal interval -/

variable (I M) in
/-- The union of times covered by open-interval geodesic witnesses with initial data `(p, v)`. -/
def geodesicInterval (p : M) (v : TangentSpace I p) : Set ℝ :=
  {t | ∃ γ a b, IsGeodesicCurveOnFrom I γ (Ioo a b) p v ∧ t ∈ Ioo a b}

omit [I.Boundaryless] in
/-- Membership in `geodesicInterval` is witnessed by a geodesic on an open interval containing the
given time. -/
theorem mem_geodesicInterval_iff {p : M} {v : TangentSpace I p} {t : ℝ} :
    t ∈ geodesicInterval I M p v ↔
      ∃ γ a b, IsGeodesicCurveOnFrom I γ (Ioo a b) p v ∧ t ∈ Ioo a b := by
  rfl

omit [I.Boundaryless] in
/-- Every geodesic witness with initial data `(p, v)` is defined inside
`geodesicInterval I M p v`. -/
theorem IsGeodesicCurveOnFrom.subset_geodesicInterval
    {p : M} {v : TangentSpace I p} {γ : ℝ → M} {a b : ℝ}
    (h : IsGeodesicCurveOnFrom I γ (Ioo a b) p v) :
    Ioo a b ⊆ geodesicInterval I M p v := by
  intro t ht
  exact ⟨γ, a, b, h, ht⟩

/-- Geodesics with the same initial data agree on the overlap of their intervals. -/
theorem IsGeodesicCurveOnFrom.eqOn_of_inter
    [T2Space (TangentBundle I M)] {p : M} {v : TangentSpace I p}
    {γ γ' : ℝ → M} {a b a' b' : ℝ}
    (hγ : IsGeodesicCurveOnFrom I γ (Ioo a b) p v)
    (hγ' : IsGeodesicCurveOnFrom I γ' (Ioo a' b') p v) :
    EqOn γ γ' (Ioo (max a a') (min b b')) := by
  let u := Ioo (max a a') (min b b')
  have h0 : (0 : ℝ) ∈ u := ⟨max_lt hγ.zero_mem.1 hγ'.zero_mem.1,
    lt_min hγ.zero_mem.2 hγ'.zero_mem.2⟩
  have huγ : u ⊆ Ioo a b := fun t ht =>
    ⟨le_max_left _ _ |>.trans_lt ht.1, (lt_min_iff.mp ht.2).1⟩
  have huγ' : u ⊆ Ioo a' b' := fun t ht =>
    ⟨le_max_right _ _ |>.trans_lt ht.1, (lt_min_iff.mp ht.2).2⟩
  have hγuFrom : IsGeodesicCurveOnFrom I γ u p v :=
    hγ.mono (uniqueDiffOn_Ioo _ _) huγ h0
  have hγ'uFrom : IsGeodesicCurveOnFrom I γ' u p v :=
    hγ'.mono (uniqueDiffOn_Ioo _ _) huγ' h0
  have hγu : IsGeodesicCurveOn I γ u := hγuFrom.isGeodesicCurveOn
  have hγ'u : IsGeodesicCurveOn I γ' u := hγ'uFrom.isGeodesicCurveOn
  have hv : CMDiff 1 (fun z : TangentBundle I M ↦
      (⟨z, geodesicSpray I M z⟩ : TangentBundle I.tangent (TangentBundle I M))) := by
    have h := contMDiff_geodesicSpray (I := I) (M := M) (n := (1 : ℕ∞ω))
      (m := ∞) (k := ∞) (by norm_num) (by norm_num)
    exact h.of_le (by norm_num)
  have hγlift : IsMIntegralCurveOn (curveVelocityLiftWithin I γ u)
      (geodesicSpray I M) u :=
    (isMIntegralCurveOn_curveVelocityLiftWithin_iff (uniqueDiffOn_Ioo _ _)
      hγu.contMDiffOn).2 hγu
  have hγ'lift : IsMIntegralCurveOn (curveVelocityLiftWithin I γ' u)
      (geodesicSpray I M) u :=
    (isMIntegralCurveOn_curveVelocityLiftWithin_iff (uniqueDiffOn_Ioo _ _)
      hγ'u.contMDiffOn).2 hγ'u
  have heq : EqOn (curveVelocityLiftWithin I γ u) (curveVelocityLiftWithin I γ' u) u := by
    apply isMIntegralCurveOn_Ioo_eqOn_of_contMDiff h0
      (fun _ _ => BoundarylessManifold.isInteriorPoint) hv hγlift hγ'lift
    simpa only [curveVelocityLiftWithin_apply] using
      hγuFrom.initial_eq.trans hγ'uFrom.initial_eq.symm
  intro t ht
  simpa only [curveVelocityLiftWithin_proj] using congrArg TotalSpace.proj (heq ht)

omit [I.Boundaryless] in
/-- The maximal geodesic interval is open. -/
theorem isOpen_geodesicInterval {p : M} {v : TangentSpace I p} :
    IsOpen (geodesicInterval I M p v) := by
  rw [isOpen_iff_forall_mem_open]
  rintro t ⟨γ, a, b, hγ, ht⟩
  exact ⟨Ioo a b, hγ.subset_geodesicInterval, isOpen_Ioo, ht⟩

omit [I.Boundaryless] in
/-- The maximal geodesic interval is order-connected, hence an interval in `ℝ`. -/
theorem ordConnected_geodesicInterval {p : M} {v : TangentSpace I p} :
    (geodesicInterval I M p v).OrdConnected := by
  refine ⟨fun p hp q hq t ht ↦ ?_⟩
  rcases le_or_gt 0 t with h | h
  · obtain ⟨γ, a, b, hγ, hq'⟩ := hq
    exact hγ.subset_geodesicInterval ⟨hγ.zero_mem.1.trans_le h, ht.2.trans_lt hq'.2⟩
  · obtain ⟨γ, a, b, hγ, hp'⟩ := hp
    exact hγ.subset_geodesicInterval ⟨hp'.1.trans_le ht.1, h.trans hγ.zero_mem.2⟩

omit [I.Boundaryless] in
/-- The maximal geodesic interval is preconnected. -/
theorem isPreconnected_geodesicInterval {p : M} {v : TangentSpace I p} :
    IsPreconnected (geodesicInterval I M p v) :=
  ordConnected_geodesicInterval.isPreconnected

/-- The initial parameter belongs to the maximal geodesic interval. -/
@[simp] theorem zero_mem_geodesicInterval {p : M} {v : TangentSpace I p} :
    (0 : ℝ) ∈ geodesicInterval I M p v := by
  obtain ⟨a, b, hab, h0, γ, hγ⟩ :=
    exists_geodesicCurveOnFrom_Ioo (I := I) (M := M) p v
  exact ⟨γ, a, b, hγ, h0⟩

omit [I.Boundaryless] in
/-- The zero-velocity geodesic exists for all time. -/
@[simp] theorem geodesicInterval_zero {p : M} :
    geodesicInterval I M p (0 : TangentSpace I p) = univ := by
  apply eq_univ_of_forall
  intro t
  refine ⟨fun _ : ℝ => p, -(|t| + 1), |t| + 1, ?_, ⟨by
    linarith [neg_abs_le t], by linarith [le_abs_self t]⟩⟩
  exact ⟨isGeodesicCurveOn_const (uniqueDiffOn_Ioo (-(|t| + 1)) (|t| + 1)) p,
    ⟨by linarith [abs_nonneg t], by linarith [abs_nonneg t]⟩, by simp⟩

omit [I.Boundaryless] in
private theorem IsGeodesicCurveOnFrom.comp_mul_left_Ioo
    {p : M} {v : TangentSpace I p} {γ : ℝ → M} {b c : ℝ}
    (hγ : IsGeodesicCurveOnFrom I γ (Ioo b c) p v) {a : ℝ} (ha : a ≠ 0) :
    (fun s : ℝ => a * s) ⁻¹' Ioo b c =
        Ioo (min (b / a) (c / a)) (max (b / a) (c / a)) ∧
      MapsTo (fun s : ℝ => a * s) (Ioo (min (b / a) (c / a)) (max (b / a) (c / a)))
        (Ioo b c) ∧
      (0 : ℝ) ∈ Ioo (min (b / a) (c / a)) (max (b / a) (c / a)) ∧
      UniqueDiffOn ℝ (Ioo (min (b / a) (c / a)) (max (b / a) (c / a))) ∧
      IsGeodesicCurveOnFrom I (γ ∘ fun s : ℝ => a * s)
        (Ioo (min (b / a) (c / a)) (max (b / a) (c / a))) p (a • v) := by
  have hbc : b < c := hγ.zero_mem.1.trans hγ.zero_mem.2
  have hu : (fun s : ℝ => a * s) ⁻¹' Ioo b c =
      Ioo (min (b / a) (c / a)) (max (b / a) (c / a)) := by
    rcases lt_or_gt_of_ne ha with hneg | hpos
    · have hbc' : c / a < b / a := (div_lt_iff_of_neg hneg).2 (by
        rw [div_mul_cancel₀ _ (ne_of_lt hneg)]
        exact hbc)
      rw [preimage_const_mul_Ioo_of_neg _ _ hneg]
      simp only [min_eq_right hbc'.le, max_eq_left hbc'.le]
    · have hbc' : b / a < c / a :=
        (div_lt_div_iff₀ hpos hpos).2 (mul_lt_mul_of_pos_right hbc hpos)
      rw [preimage_const_mul_Ioo₀ _ _ hpos]
      simp only [min_eq_left hbc'.le, max_eq_right hbc'.le]
  have hmap : MapsTo (fun s : ℝ => a * s)
      (Ioo (min (b / a) (c / a)) (max (b / a) (c / a))) (Ioo b c) := by
    rw [← hu]
    exact fun _ hs => hs
  have h0u : (0 : ℝ) ∈ Ioo (min (b / a) (c / a)) (max (b / a) (c / a)) := by
    rw [← hu]
    simpa using hγ.zero_mem
  have huuniq : UniqueDiffOn ℝ (Ioo (min (b / a) (c / a)) (max (b / a) (c / a))) :=
    uniqueDiffOn_Ioo _ _
  exact ⟨hu, hmap, h0u, huuniq, hγ.comp_mul_left a huuniq hmap h0u⟩

omit [I.Boundaryless] in
/-- Nonzero rescaling of the initial velocity rescales the maximal interval by the inverse. -/
@[simp] theorem mem_geodesicInterval_smul_iff
    {p : M} {v : TangentSpace I p} {a t : ℝ} (ha : a ≠ 0) :
    t ∈ geodesicInterval I M p (a • v) ↔ a * t ∈ geodesicInterval I M p v := by
  constructor
  · rintro ⟨γ, b, c, hγ, ht⟩
    let u := Ioo (min (b / a⁻¹) (c / a⁻¹)) (max (b / a⁻¹) (c / a⁻¹))
    obtain ⟨hu, hmap, h0u, huuniq, hγ'⟩ :=
      hγ.comp_mul_left_Ioo (a := a⁻¹) (inv_ne_zero ha)
    have hu' : (fun s : ℝ => a⁻¹ * s) ⁻¹' Ioo b c = u := by
      simpa only [u] using hu
    have hγ' : IsGeodesicCurveOnFrom I (γ ∘ fun s : ℝ => a⁻¹ * s) u p v := by
      simpa [u, smul_smul, inv_mul_cancel₀ ha] using hγ'
    refine ⟨γ ∘ fun s : ℝ => a⁻¹ * s, _, _, hγ', ?_⟩
    -- The existential witness unfolds `u`; rewrite its membership as the preimage condition.
    change a * t ∈ u
    rw [← hu']
    simpa [← mul_assoc, inv_mul_cancel₀ ha] using ht
  · rintro ⟨γ, b, c, hγ, ht⟩
    let u := Ioo (min (b / a) (c / a)) (max (b / a) (c / a))
    obtain ⟨hu, hmap, h0u, huuniq, hγ'⟩ := hγ.comp_mul_left_Ioo ha
    have hu' : (fun s : ℝ => a * s) ⁻¹' Ioo b c = u := by
      simpa only [u] using hu
    refine ⟨γ ∘ fun s : ℝ => a * s, _, _, hγ', ?_⟩
    -- As above, expose the named witness interval before applying the preimage equality.
    change t ∈ u
    rw [← hu']
    exact ht

end Manifold

end TauCeti
