/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.RicciFlow.Scalar.Comparison
public import TauCeti.Geometry.Manifold.Riemannian.MaximumPrinciple.Strong
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Strict scalar positivity and backward Ricci-flat rigidity

For an actual Ricci flow with nonnegative scalar curvature, one positive seed gives strict
positivity everywhere at every later time on a connected manifold. A later scalar zero forces
all earlier scalar slices to vanish. The scalar evolution equation then forces the actual
Ricci tensor to vanish, and the Ricci metric equation makes the metric stationary.

No completeness or compactness is used for these statements when scalar nonnegativity on the
slab is supplied. The Ricci-flat dichotomy requires a nontrivial slab. A singleton slab is
stationary simply because `Set.Icc a a = {a}`; this alone does not imply Ricci-flatness.
On a closed manifold, nonnegative initial scalar curvature supplies it by
the geometric scalar comparison theorem.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Corollaries 4.14–4.15.
* P. Topping, *Lectures on the Ricci Flow*, Chapter 3.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public noncomputable section

open Bundle CovariantDerivative Set Filter
open scoped ContDiff Manifold Topology RealInnerProductSpace

namespace TauCeti.Manifold.ContMDiffNondegenerateMetricFamily

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [PreconnectedSpace M]
  (g : ContMDiffNondegenerateMetricFamily 𝓘(ℝ, E) M 𝓘(ℝ) ℝ)
  (r : ℝ → ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
    (TangentSpace 𝓘(ℝ, E) : M → Type _))
  (hr : ∀ s, g.metric s = (r s).toNondegenerateMetric)

include hr

/-- One positive scalar-curvature seed of a nonnegative Ricci flow gives strict positivity
everywhere at every later time, without completeness or compactness. -/
theorem scalarCurvature_positive_at_later_time_of_ricciFlow
    {a b : ℝ} (hab : a < b)
    (hflow : IsRicciFlowOn r (Ioo a b))
    (hnonneg : ∀ t ∈ Icc a b, ∀ x, 0 ≤ (r t).scalarCurvature x)
    (p : M) (hp : 0 < (r a).scalarCurvature p) :
    ∀ x, 0 < (r b).scalarCurvature x := by
  exact TauCeti.Manifold.heat_supersolution_positive_at_later_time
    (E := E) (M := M) (g := r) (hg := g.contMDiff_inner_of_eq (by simp) r hr) hab
    (fun t x ↦ (r t).scalarCurvature x)
    (fun t x ↦ deriv (fun s ↦ (r s).scalarCurvature x) t)
    (g.continuous_scalarCurvature r hr).continuousOn
    (fun t ht x ↦
      (g.hasDerivAt_scalarCurvature_sum_leviCivitaConnection_of_ricciFlow
        r hr (hflow.at r ht) x).differentiableAt.hasDerivAt)
    (fun t _ ↦ (r t).contMDiff_scalarCurvature.of_le (by simp)) hnonneg
    (fun t ht x ↦
      g.laplaceBeltrami_le_deriv_scalarCurvature_of_ricciFlow r hr (hflow.at r ht) x) p hp

/-- A later zero of nonnegative scalar curvature along an actual Ricci flow forces every
earlier scalar slice to vanish. -/
theorem scalarCurvature_eq_zero_of_zero_at_later_time_of_ricciFlow
    {a b : ℝ}
    (hflow : IsRicciFlowOn r (Ioo a b))
    (hnonneg : ∀ t ∈ Icc a b, ∀ x, 0 ≤ (r t).scalarCurvature x)
    {p : M} (hp : (r b).scalarCurvature p = 0) :
    ∀ t ∈ Ico a b, ∀ x, (r t).scalarCurvature x = 0 := by
  exact TauCeti.Manifold.heat_supersolution_eq_zero_of_zero_at_later_time
    (E := E) (M := M) (g := r) (hg := g.contMDiff_inner_of_eq (by simp) r hr)
    (fun t x ↦ (r t).scalarCurvature x)
    (fun t x ↦ deriv (fun s ↦ (r s).scalarCurvature x) t)
    (g.continuous_scalarCurvature r hr).continuousOn
    (fun t ht x ↦ (g.hasDerivAt_scalarCurvature_sum_leviCivitaConnection_of_ricciFlow
      r hr (hflow.at r ht) x).differentiableAt.hasDerivAt)
    (fun t _ ↦ (r t).contMDiff_scalarCurvature.of_le (by simp)) hnonneg
    (fun t ht x ↦
      g.laplaceBeltrami_le_deriv_scalarCurvature_of_ricciFlow r hr (hflow.at r ht) x) hp

/-- A later scalar zero forces the actual native Ricci tensor to vanish at every earlier
interior time. This uses the positive coefficient-square reaction in the scalar evolution. -/
private theorem ricciTensor_eq_zero_of_scalarCurvature_zero_at_later_time_interior_of_ricciFlow
    {a b : ℝ}
    (hflow : IsRicciFlowOn r (Ioo a b))
    (hnonneg : ∀ t ∈ Icc a b, ∀ x, 0 ≤ (r t).scalarCurvature x)
    {p : M} (hp : (r b).scalarCurvature p = 0)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : M) :
    let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
      ⟨(r t).toRiemannianMetric⟩
    (leviCivitaConnection 𝓘(ℝ, E) M).ricciTensor x = 0 := by
  classical
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨(r t).toRiemannianMetric⟩
  have hzero := g.scalarCurvature_eq_zero_of_zero_at_later_time_of_ricciFlow r hr hflow hnonneg hp
  have hlocal : (fun s ↦ (r s).scalarCurvature x) =ᶠ[𝓝 t] fun _ ↦ (0 : ℝ) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact hzero s ⟨hs.1.le, hs.2⟩ x
  have hd0 : HasDerivAt (fun s ↦ (r s).scalarCurvature x) 0 t :=
    (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hlocal
  have hslic : (r t).scalarCurvature = fun _ ↦ (0 : ℝ) :=
    funext (hzero t ⟨ht.1.le, ht.2⟩)
  have hΔ : laplaceBeltrami 𝓘(ℝ, E) (r t).scalarCurvature x = 0 := by
    rw [hslic, laplaceBeltrami_const]
  let b := stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, E) x)
  have hsum : (∑ i, ∑ j,
      ((leviCivitaConnection 𝓘(ℝ, E) M).ricciTensor x (b i) (b j)) ^ 2) = 0 := by
    have hd := (g.hasDerivAt_scalarCurvature_sum_leviCivitaConnection_of_ricciFlow
      r hr (hflow.at r ht) x).unique hd0
    rw [hΔ] at hd
    linarith
  apply LinearMap.BilinForm.ext_basis b.toBasis
  intro i j
  have hi := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ sq_nonneg
      ((leviCivitaConnection 𝓘(ℝ, E) M).ricciTensor x (b i) (b j)))).mp hsum i
        (Finset.mem_univ i)
  have hij := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ sq_nonneg
    ((leviCivitaConnection 𝓘(ℝ, E) M).ricciTensor x (b i) (b j)))).mp hi j
      (Finset.mem_univ j)
  simpa only [LinearMap.zero_apply, OrthonormalBasis.coe_toBasis] using sq_eq_zero_iff.mp hij

/-- A later scalar zero makes a nonnegative Ricci flow stationary on the whole closed slab.
The flow equation is assumed only on `Ioo a b`; the conclusion holds on `Icc a b`. -/
theorem metric_eq_of_scalarCurvature_zero_at_later_time_of_ricciFlow
    {a b : ℝ}
    (hflow : IsRicciFlowOn r (Ioo a b))
    (hnonneg : ∀ t ∈ Icc a b, ∀ x, 0 ≤ (r t).scalarCurvature x)
    {p : M} (hp : (r b).scalarCurvature p = 0) :
    ∀ s ∈ Icc a b, r s = r a := by
  intro s hs
  by_cases hab : a < b
  case neg =>
    have hsa : s = a := by linarith [hs.1, hs.2]
    exact congrArg r hsa
  ext x u v
  let f : ℝ → ℝ := fun t ↦ (r t).inner x u v
  have hd0 : ∀ t ∈ Ioo a b, HasDerivAt f 0 t := by
    intro t ht
    have hRic := g.ricciTensor_eq_zero_of_scalarCurvature_zero_at_later_time_interior_of_ricciFlow
      r hr hflow hnonneg hp ht x
    simpa only [hRic, LinearMap.zero_apply, mul_zero] using (hflow.at r ht).hasDerivAt r x u v
  have hf : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hd := g.hasDerivAt_apply_apply_comp (c := id) (t := t) mdifferentiableAt_id x u v
    simpa only [← metric_apply, hr, ContMDiffRiemannianMetric.toNondegenerateMetric_apply,
      id_eq, f]
      using hd.continuousAt
  obtain ⟨c, hc⟩ := exists_between hab
  have hconst : EqOn f (fun _ ↦ f c) (Ioo a b) := fun t ht ↦
    isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
      (fun t ht ↦ (hd0 t ht).differentiableAt.differentiableWithinAt)
      (fun t ht ↦ (hd0 t ht).deriv) ht hc
  have hclosed : EqOn f (fun _ ↦ f c) (Icc a b) := by
    rw [← closure_Ioo hab.ne]
    exact hconst.closure hf continuous_const
  exact (hclosed hs).trans (hclosed (left_mem_Icc.mpr hab.le)).symm

/-- On a nontrivial slab, a later scalar zero makes the native Ricci tensor vanish at every
time in `Icc a b`. The flow equation is assumed only on `Ioo a b`. -/
theorem ricciTensor_eq_zero_of_scalarCurvature_zero_at_later_time_of_ricciFlow
    {a b : ℝ} (hab : a < b)
    (hflow : IsRicciFlowOn r (Ioo a b))
    (hnonneg : ∀ t ∈ Icc a b, ∀ x, 0 ≤ (r t).scalarCurvature x)
    {p : M} (hp : (r b).scalarCurvature p = 0)
    {t : ℝ} (ht : t ∈ Icc a b) (x : M) :
    let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
      ⟨(r t).toRiemannianMetric⟩
    (leviCivitaConnection 𝓘(ℝ, E) M).ricciTensor x = 0 := by
  obtain ⟨c, hc⟩ := exists_between hab
  have hstationary := g.metric_eq_of_scalarCurvature_zero_at_later_time_of_ricciFlow r hr
    hflow hnonneg hp
  have htc : r t = r c :=
    (hstationary t ht).trans (hstationary c ⟨hc.1.le, hc.2.le⟩).symm
  have hRic := g.ricciTensor_eq_zero_of_scalarCurvature_zero_at_later_time_interior_of_ricciFlow
    r hr hflow hnonneg hp hc x
  have hRicEq := congrArg
    (fun q : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
        (TangentSpace 𝓘(ℝ, E) : M → Type _) ↦
      let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
        ⟨q.toRiemannianMetric⟩
      (leviCivitaConnection 𝓘(ℝ, E) M).ricciTensor x) htc
  exact hRicEq.trans hRic

/-- On a closed connected manifold, nonnegative initial scalar curvature and one positive
initial point give strict scalar positivity everywhere at every later time. -/
theorem scalarCurvature_positive_at_later_time_of_initial_nonneg_of_ricciFlow [CompactSpace M]
    {a b : ℝ} (hab : a < b)
    (hflow : IsRicciFlowOn r (Ioo a b))
    (hinit : ∀ x, 0 ≤ (r a).scalarCurvature x)
    (p : M) (hp : 0 < (r a).scalarCurvature p) :
    ∀ x, 0 < (r b).scalarCurvature x :=
  g.scalarCurvature_positive_at_later_time_of_ricciFlow r hr hab hflow
    (g.scalarCurvature_nonneg_of_ricciFlow r hr hflow hinit) p hp

/-- A Ricci flow on a closed connected manifold starting with nonnegative scalar curvature
has strictly positive scalar curvature at the final time, or is stationary on the entire slab.
For `a < b`, the stationary alternative is Ricci-flat at every time in `Icc a b`. -/
theorem scalarCurvature_positive_or_stationary_of_ricciFlow [CompactSpace M]
    {a b : ℝ} (hab : a < b)
    (hflow : IsRicciFlowOn r (Ioo a b))
    (hinit : ∀ x, 0 ≤ (r a).scalarCurvature x) :
    (∀ x, 0 < (r b).scalarCurvature x) ∨
      ((∀ s ∈ Icc a b, r s = r a) ∧
        ∀ t ∈ Icc a b,
          let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
            ⟨(r t).toRiemannianMetric⟩
          ∀ x, (leviCivitaConnection 𝓘(ℝ, E) M).ricciTensor x = 0) := by
  classical
  have hnonneg := g.scalarCurvature_nonneg_of_ricciFlow r hr hflow hinit
  by_cases hpositive : ∀ x, 0 < (r b).scalarCurvature x
  · exact Or.inl hpositive
  push Not at hpositive
  obtain ⟨p, hp⟩ := hpositive
  have hp0 : (r b).scalarCurvature p = 0 :=
    le_antisymm hp (hnonneg b (right_mem_Icc.mpr hab.le) p)
  exact Or.inr
    ⟨g.metric_eq_of_scalarCurvature_zero_at_later_time_of_ricciFlow r hr hflow hnonneg hp0,
    fun _ ht x ↦ g.ricciTensor_eq_zero_of_scalarCurvature_zero_at_later_time_of_ricciFlow r hr hab
      hflow hnonneg hp0 ht x⟩

end TauCeti.Manifold.ContMDiffNondegenerateMetricFamily
