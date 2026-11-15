/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential
public import TauCeti.Geometry.Manifold.Riemannian.Scaling

/-!
# Geodesics and the exponential map under constant rescaling of a metric

Let `g` be a Riemannian metric on `M` and `c` a positive constant. Multiplying `g` by the constant
function `c` leaves the Levi-Civita connection unchanged on differentiable vector fields
(`Bundle.ContMDiffRiemannianMetric.leviCivitaConnection_rescale_const_apply`), so it leaves the
Christoffel map in every tangent trivialization unchanged. Consequently, covariant differentiation
along curves, covariant acceleration, the geodesic equation, the geodesic spray, maximal geodesic
intervals, maximal geodesics, and the Riemannian exponential map and its domain are all unchanged
when passing from `g` to `c g`. Only tangent-vector norms—and therefore metric balls in tangent
spaces and Riemannian distances—scale by `√c`.

The file first records that two connections agreeing on vector fields differentiable at `x` have
the same Christoffel map at `x`, and hence the same along-curve derivative and covariant
acceleration at any parameter mapping to `x`. Specializing to the Levi-Civita connections of `g`
and `c g` yields the rescaling invariance of geodesics and of the exponential map.

## Main results

* `TauCeti.Manifold.christoffelMap_congr`: two connections agreeing on vector fields differentiable
  at `x` have the same model-space Christoffel map at `x`.
* `CovariantDerivative.alongCurveWithin_congr_covariantDerivative` and
  `CovariantDerivative.accelerationWithin_congr_covariantDerivative`: along-curve differentiation
  and covariant acceleration at `t` depend on the connection only through vector fields
  differentiable at `γ t`.
* `Bundle.ContMDiffRiemannianMetric.isGeodesicCurveOn_rescale_const_iff` and
  `Bundle.ContMDiffRiemannianMetric.isGeodesicCurveOnFrom_rescale_const_iff`: `c g` and `g` have
  the same parametrized geodesics.
* `Bundle.ContMDiffRiemannianMetric.geodesicSpray_rescale_const`: `c g` and `g` have the same
  geodesic spray.
* `Bundle.ContMDiffRiemannianMetric.geodesicInterval_rescale_const` and
  `Bundle.ContMDiffRiemannianMetric.maximalGeodesic_rescale_const`: `c g` and `g` have the same
  maximal geodesic intervals and maximal geodesics.
* `Bundle.ContMDiffRiemannianMetric.expDomain_rescale_const` and
  `Bundle.ContMDiffRiemannianMetric.riemannianExp_rescale_const`: `c g` and `g` have the same
  exponential domain and exponential map.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 5.
* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 2nd ed., World Scientific (2007),
  Chapter 4.
-/

public section

open Bundle CovariantDerivative Module Set TauCeti.Manifold
open scoped ContDiff Manifold Topology

noncomputable section

section ConnectionCongr

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]

/-- Two connections on the tangent bundle that agree on vector fields differentiable at `x` have
the same model-space Christoffel map at `x` in any trivialization. -/
theorem TauCeti.Manifold.christoffelMap_congr
    {ι : Type*} [Fintype ι] (b : Basis ι 𝕜 E)
    {e : Trivialization E (TotalSpace.proj : TangentBundle I M → M)} [MemTrivializationAtlas e]
    {cov₁ cov₂ : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x)}
    (hcov₁ : IsCovariantDerivativeOn E cov₁ e.baseSet)
    (hcov₂ : IsCovariantDerivativeOn E cov₂ e.baseSet) {x : M}
    (h : x ∈ e.baseSet →
      ∀ ⦃Y : Π y : M, TangentSpace I y⦄, MDiffAt (T% Y) x → cov₁ Y x = cov₂ Y x) :
    christoffelMap b hcov₁ x = christoffelMap b hcov₂ x := by
  by_cases hx : x ∈ e.baseSet
  · ext v u
    have hread : ∀ᶠ y in 𝓝 x, (e ⟨y, e.symm y v⟩).2 = v :=
      Filter.eventually_of_mem (e.open_baseSet.mem_nhds hx) fun y hy ↦
        congrArg Prod.snd (e.apply_mk_symm hy v)
    have hσ : MDiffAt (T% (fun y ↦ e.symm y v)) x :=
      (e.mdifferentiableAt_section_iff I _ hx).2
        (mdifferentiableAt_const.congr_of_eventuallyEq hread)
    have heq :
        e.symm x (christoffelMap b hcov₁ x v u) = e.symm x (christoffelMap b hcov₂ x v u) := by
      rw [← covariantDerivative_symm_apply_symm b hcov₁ hx,
        ← covariantDerivative_symm_apply_symm b hcov₂ hx, h hx hσ]
    simpa only [e.apply_mk_symm hx] using congrArg (fun w ↦ (e ⟨x, w⟩).2) heq
  · rw [christoffelMap_of_notMem b hcov₁ hx, christoffelMap_of_notMem b hcov₂ hx]

namespace CovariantDerivative

/-- Along-curve covariant differentiation at `t` depends on the connection only through its action
on vector fields differentiable at `γ t`. -/
theorem alongCurveWithin_congr_covariantDerivative
    {cov₁ cov₂ : _root_.CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
    {γ : 𝕜 → M} {V : ∀ r, TangentSpace I (γ r)} {s : Set 𝕜} {t : 𝕜}
    (h : ∀ ⦃Y : Π y : M, TangentSpace I y⦄, MDiffAt (T% Y) (γ t) → cov₁ Y (γ t) = cov₂ Y (γ t)) :
    alongCurveWithin cov₁ γ V s t = alongCurveWithin cov₂ γ V s t := by
  rw [alongCurveWithin_apply, alongCurveInChartWithin_apply,
    alongCurveWithin_apply, alongCurveInChartWithin_apply,
    christoffelMap_congr (finBasis 𝕜 E) _ _ fun _ _ hY ↦ h hY]

/-- Unrestricted along-curve covariant differentiation at `t` depends on the connection only
through its action on vector fields differentiable at `γ t`. -/
theorem alongCurve_congr_covariantDerivative
    {cov₁ cov₂ : _root_.CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
    {γ : 𝕜 → M} {V : ∀ r, TangentSpace I (γ r)} {t : 𝕜}
    (h : ∀ ⦃Y : Π y : M, TangentSpace I y⦄, MDiffAt (T% Y) (γ t) → cov₁ Y (γ t) = cov₂ Y (γ t)) :
    alongCurve cov₁ γ V t = alongCurve cov₂ γ V t := by
  rw [← alongCurveWithin_univ, ← alongCurveWithin_univ]
  exact alongCurveWithin_congr_covariantDerivative h

/-- Covariant acceleration within `s` at `t` depends on the connection only through its action on
vector fields differentiable at `γ t`. -/
theorem accelerationWithin_congr_covariantDerivative
    {cov₁ cov₂ : _root_.CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
    {γ : 𝕜 → M} {s : Set 𝕜} {t : 𝕜}
    (h : ∀ ⦃Y : Π y : M, TangentSpace I y⦄, MDiffAt (T% Y) (γ t) → cov₁ Y (γ t) = cov₂ Y (γ t)) :
    accelerationWithin cov₁ γ s t = accelerationWithin cov₂ γ s t := by
  rw [accelerationWithin_def, accelerationWithin_def]
  exact alongCurveWithin_congr_covariantDerivative h

/-- Unrestricted covariant acceleration at `t` depends on the connection only through its action on
vector fields differentiable at `γ t`. -/
theorem acceleration_congr_covariantDerivative
    {cov₁ cov₂ : _root_.CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
    {γ : 𝕜 → M} {t : 𝕜}
    (h : ∀ ⦃Y : Π y : M, TangentSpace I y⦄, MDiffAt (T% Y) (γ t) → cov₁ Y (γ t) = cov₂ Y (γ t)) :
    acceleration cov₁ γ t = acceleration cov₂ γ t := by
  rw [← accelerationWithin_univ, ← accelerationWithin_univ]
  exact accelerationWithin_congr_covariantDerivative h

end CovariantDerivative

end ConnectionCongr

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

section GeodesicEquation

variable [IsManifold I 2 M] {n : ℕ∞ω}

/-- Multiplying a `C¹` metric by a positive constant does not change covariant differentiation
along a curve for the Levi-Civita connection. -/
theorem alongCurveWithin_leviCivitaConnection_rescale_const
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
    {c : ℝ} (hc : 0 < c) (γ : ℝ → M) (V : ∀ r, TangentSpace I (γ r)) (s : Set ℝ) (t : ℝ) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      alongCurveWithin (leviCivitaConnection I M) γ V s t) =
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      alongCurveWithin (leviCivitaConnection I M) γ V s t) :=
  have : IsManifold I 1 M := IsManifold.of_le (n := 2) (by norm_num)
  alongCurveWithin_congr_covariantDerivative fun _ hY ↦
    leviCivitaConnection_rescale_const_apply g hn hc hY

/-- Multiplying a `C¹` metric by a positive constant does not change the covariant acceleration of
a curve for the Levi-Civita connection. -/
theorem accelerationWithin_leviCivitaConnection_rescale_const
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
    {c : ℝ} (hc : 0 < c) (γ : ℝ → M) (s : Set ℝ) (t : ℝ) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      accelerationWithin (leviCivitaConnection I M) γ s t) =
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      accelerationWithin (leviCivitaConnection I M) γ s t) :=
  have : IsManifold I 1 M := IsManifold.of_le (n := 2) (by norm_num)
  accelerationWithin_congr_covariantDerivative fun _ hY ↦
    leviCivitaConnection_rescale_const_apply g hn hc hY

/-- Multiplying a `C¹` metric by a positive constant does not change which curves are geodesics on
a parameter set. -/
theorem isGeodesicCurveOn_rescale_const_iff
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
    {c : ℝ} (hc : 0 < c) (γ : ℝ → M) (s : Set ℝ) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      IsGeodesicCurveOn I γ s) ↔
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      IsGeodesicCurveOn I γ s) := by
  have hacc (r : ℝ) := accelerationWithin_leviCivitaConnection_rescale_const g hn hc γ s r
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩ <;> obtain ⟨hu, hcγ, ha⟩ := h
  · let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
      IsContMDiffRiemannianBundle.of_le hn
    exact ⟨hu, hcγ, fun r hr ↦ (hacc r).symm.trans (ha r hr)⟩
  · let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
      IsContMDiffRiemannianBundle.of_le hn
    exact ⟨hu, hcγ, fun r hr ↦ (hacc r).trans (ha r hr)⟩

/-- Multiplying a `C¹` metric by a positive constant does not change all-time geodesics. -/
theorem isGeodesicCurve_rescale_const_iff
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
    {c : ℝ} (hc : 0 < c) (γ : ℝ → M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      IsGeodesicCurve I γ) ↔
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      IsGeodesicCurve I γ) := by
  have h₁ : (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      IsGeodesicCurve I γ) ↔
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      IsGeodesicCurveOn I γ univ) := by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
      IsContMDiffRiemannianBundle.of_le hn
    exact isGeodesicCurveOn_univ.symm
  have h₂ : (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      IsGeodesicCurve I γ) ↔
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      IsGeodesicCurveOn I γ univ) := by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
      IsContMDiffRiemannianBundle.of_le hn
    exact isGeodesicCurveOn_univ.symm
  exact h₁.trans ((isGeodesicCurveOn_rescale_const_iff g hn hc γ univ).trans h₂.symm)

/-- Multiplying a `C¹` metric by a positive constant does not change geodesics with prescribed
initial data. -/
theorem isGeodesicCurveOnFrom_rescale_const_iff
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
    {c : ℝ} (hc : 0 < c) (γ : ℝ → M) (s : Set ℝ) (p : M) (v : TangentSpace I p) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      IsGeodesicCurveOnFrom I γ s p v) ↔
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      IsGeodesicCurveOnFrom I γ s p v) := by
  have hgeo := isGeodesicCurveOn_rescale_const_iff g hn hc γ s
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩ <;> obtain ⟨hγ, h0, hi⟩ := h
  · let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
      IsContMDiffRiemannianBundle.of_le hn
    exact ⟨hgeo.1 hγ, h0, hi⟩
  · let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
      IsContMDiffRiemannianBundle.of_le hn
    exact ⟨hgeo.2 hγ, h0, hi⟩

/-- Multiplying a `C¹` metric by a positive constant leaves the geodesic spray unchanged. -/
theorem geodesicSpray_rescale_const
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
    {c : ℝ} (hc : 0 < c) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      geodesicSpray I M) =
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      geodesicSpray I M) := by
  have : IsManifold I 1 M := IsManifold.of_le (n := 2) (by norm_num)
  funext z
  have h₁ :=
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      geodesicSpray_apply (I := I) (M := M) z)
  have h₂ :=
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      geodesicSpray_apply (I := I) (M := M) z)
  exact h₁.trans ((congrArg (fun Γ : E →L[ℝ] E →L[ℝ] E ↦ (z.2, -Γ z.2 z.2))
    (christoffelMap_congr (finBasis ℝ E) _ _ fun _ _ hY ↦
      leviCivitaConnection_rescale_const_apply g hn hc hY)).trans h₂.symm)

end GeodesicEquation

section Exponential

variable [IsManifold I ∞ M]
  (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
  {c : ℝ} (hc : 0 < c)

/-- Multiplying a smooth metric by a positive constant leaves maximal geodesic intervals
unchanged. -/
theorem geodesicInterval_rescale_const (p : M) (v : TangentSpace I p) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      geodesicInterval I M p v) =
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      geodesicInterval I M p v) := by
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  let g' := g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc
  ext t
  have h₁ : t ∈ (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g'.toRiemannianMetric⟩;
      geodesicInterval I M p v) ↔
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g'.toRiemannianMetric⟩;
      ∃ γ a b, IsGeodesicCurveOnFrom I γ (Ioo a b) p v ∧ t ∈ Ioo a b) := by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g'.toRiemannianMetric⟩
    exact mem_geodesicInterval_iff
  have h₂ : t ∈ (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      geodesicInterval I M p v) ↔
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      ∃ γ a b, IsGeodesicCurveOnFrom I γ (Ioo a b) p v ∧ t ∈ Ioo a b) := by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    exact mem_geodesicInterval_iff
  rw [h₁, h₂]
  exact exists_congr fun γ ↦ exists_congr fun a ↦ exists_congr fun b ↦
    and_congr_left fun _ ↦
      isGeodesicCurveOnFrom_rescale_const_iff g (by simp) hc γ (Ioo a b) p v

/-- Multiplying a smooth metric by a positive constant leaves maximal geodesics unchanged. -/
theorem maximalGeodesic_rescale_const (p : M) (v : TangentSpace I p) (t : ℝ) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      maximalGeodesic I M p v t) =
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      maximalGeodesic I M p v t) := by
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  let g' := g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc
  have h₁ :=
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g'.toRiemannianMetric⟩;
      maximalGeodesic_def (I := I) (M := M) p v t)
  have h₂ :=
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      maximalGeodesic_def (I := I) (M := M) p v t)
  exact h₁.trans ((congrArg
    (fun S ↦ (maximalIntegralCurve S (TotalSpace.mk' E p v) t).proj)
    (geodesicSpray_rescale_const g (by simp) hc)).trans h₂.symm)

/-- Multiplying a smooth metric by a positive constant leaves the natural domain of the Riemannian
exponential map unchanged. -/
theorem expDomain_rescale_const (p : M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      expDomain I M p) =
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      expDomain I M p) := by
  let g' := g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc
  ext v
  have h₁ : v ∈ (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g'.toRiemannianMetric⟩;
      expDomain I M p) ↔
    (1 : ℝ) ∈ (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g'.toRiemannianMetric⟩;
      geodesicInterval I M p v) := by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g'.toRiemannianMetric⟩
    exact mem_expDomain_iff
  have h₂ : v ∈ (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      expDomain I M p) ↔
    (1 : ℝ) ∈ (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      geodesicInterval I M p v) := by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    exact mem_expDomain_iff
  rw [h₁, h₂, geodesicInterval_rescale_const g hc p v]

/-- Multiplying a smooth metric by a positive constant does not change geodesic completeness at a
point. -/
theorem isGeodesicallyCompleteAt_rescale_const_iff (p : M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      IsGeodesicallyCompleteAt I M p) ↔
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      IsGeodesicallyCompleteAt I M p) := by
  let g' := g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc
  have h₁ : (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g'.toRiemannianMetric⟩;
      IsGeodesicallyCompleteAt I M p) ↔
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g'.toRiemannianMetric⟩;
      expDomain I M p) = univ := by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g'.toRiemannianMetric⟩
    exact expDomain_eq_univ_iff.symm
  have h₂ : (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      IsGeodesicallyCompleteAt I M p) ↔
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      expDomain I M p) = univ := by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    exact expDomain_eq_univ_iff.symm
  rw [h₁, h₂, expDomain_rescale_const g hc p]

/-- Multiplying a smooth metric by a positive constant leaves the Riemannian exponential map
unchanged. -/
theorem riemannianExp_rescale_const (p : M) (v : TangentSpace I p) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      riemannianExp I M p v) =
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      riemannianExp I M p v) := by
  let g' := g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc
  have h₁ :=
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g'.toRiemannianMetric⟩;
      riemannianExp_def (I := I) (M := M) p v)
  have h₂ :=
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      riemannianExp_def (I := I) (M := M) p v)
  exact h₁.trans ((maximalGeodesic_rescale_const g hc p v 1).trans h₂.symm)

end Exponential

end Bundle.ContMDiffRiemannianMetric

end
