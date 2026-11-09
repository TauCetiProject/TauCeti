/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.PartitionOfUnity
public import TauCeti.Analysis.Sobolev.Wkp.ShiftedMollification
import TauCeti.Analysis.Sobolev.Wkp.Leibniz

/-!
# Smooth functions up to the boundary are dense in `W^{k,p}` of a bounded Lipschitz domain

For a bounded Lipschitz domain `Ω ⊆ ℝ × E`, every order `k` and `1 ≤ p < ∞`, the restrictions to
`Ω` of test functions on the whole space are dense in `W^{k,p}(Ω)` in the full Sobolev norm.
Thus functions smooth up to the boundary are dense at every order. At order one this also follows
from the extension operator (`TauCeti.W1p.denseRange_restrictL_ofTestFunctionₗ_top`); no extension
operator is used here, so the argument works at every order.

The proof is the segment-condition argument. A partition of unity adapted to the boundary charts
(`Set.IsLipschitzDomainWith.exists_contDiff_partitionOfUnity`) splits `u` into a piece with
compact support inside `Ω` and finitely many pieces supported in boundary chart cylinders. Inside
a chart cylinder `Ω` is the region above a Lipschitz graph, so translating a piece by a small
vector in the upward normal direction of the chart moves the region where it is defined across
the boundary. After this translation a mollification at a radius small relative to the
translation only sees values inside `Ω`. The approximation of each piece is
`TauCeti.Wkp.mem_closure_range_restrictL_ofTestFunctionₗ_top_of_shift`.

## Main declarations

* `TauCeti.Wkp.denseRange_restrictL_ofTestFunctionₗ_top_of_isLipschitzDomainWith`: density of
  restrictions of whole-space test functions in `W^{k,p}(Ω)` for bounded Lipschitz `Ω`.

## References

* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorem 3.22.
* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.3.3, Theorem 3.
-/

public section

noncomputable section

namespace TauCeti

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Distributions ENNReal NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {mu : Measure (WithLp 2 (ℝ × E))} [mu.IsAddHaarMeasure]
  {Ω : Opens (WithLp 2 (ℝ × E))} {L : ℝ≥0} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The upward normal direction of a chart, in the original coordinates. -/
private def chartNormal (e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) : WithLp 2 (ℝ × E) :=
  e.linearIsometryEquiv.symm (WithLp.toLp 2 ((1 : ℝ), (0 : E)))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem norm_chartNormal (e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) :
    ‖chartNormal e‖ = 1 := by
  simp [chartNormal]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Translating by `s` along the chart normal raises the normal chart coordinate by `s`. -/
private theorem chart_add_smul_chartNormal (e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E))
    (x : WithLp 2 (ℝ × E)) (s : ℝ) :
    e (x + s • chartNormal e) = e x + s • WithLp.toLp 2 ((1 : ℝ), (0 : E)) := by
  rw [add_comm x, ← vadd_eq_add, e.map_vadd, vadd_eq_add, map_smul, chartNormal,
    LinearIsometryEquiv.apply_symm_apply, add_comm]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **The segment condition in a chart.** Let `K` have its `δ`-thickening inside a chart
cylinder. If `(L + 1) r ≤ s` and `s + r ≤ δ`, `2 r ≤ δ`, then for every `x ∈ Ω` the closed ball
of radius `r` around `x + s n`, where `n` is the chart normal, either lies in `Ω` or misses `K`. -/
private theorem chart_ballCondition {e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {φ : E → ℝ}
    {a b : ℝ} (hc : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzChartWith L e φ a b)
    {K : Set (WithLp 2 (ℝ × E))} {δ : ℝ} (hKC : cthickening δ K ⊆ e ⁻¹' normalCylinder a b)
    {s r : ℝ} (hrs : (L + 1) * r ≤ s) (hsδ : s + r ≤ δ) (hrδ : 2 * r ≤ δ)
    {x : WithLp 2 (ℝ × E)} (hx : x ∈ Ω) :
    closedBall (x + s • chartNormal e) r ⊆ Ω ∨
      Disjoint (closedBall (x + s • chartNormal e) r) K := by
  by_cases hdis : Disjoint (closedBall (x + s • chartNormal e) r) K
  · exact Or.inr hdis
  left
  obtain ⟨y, hyB, hyK⟩ := not_disjoint_iff.1 hdis
  rw [mem_closedBall] at hyB
  have hr : 0 ≤ r := dist_nonneg.trans hyB
  have hs : 0 ≤ s := le_trans (by positivity) hrs
  have hn : dist x (x + s • chartNormal e) = s := by
    rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, norm_chartNormal,
      Real.norm_of_nonneg hs, mul_one]
  have hxC : e x ∈ normalCylinder a b := hKC (mem_cthickening_of_dist_le x y δ K hyK (by
    linarith [dist_triangle x (x + s • chartNormal e) y, dist_comm y (x + s • chartNormal e)]))
  have hxΩ := (hc.mem_iff hxC).1 hx
  intro z hz
  rw [mem_closedBall] at hz
  have hzC : e z ∈ normalCylinder a b := hKC (mem_cthickening_of_dist_le z y δ K hyK (by
    linarith [dist_triangle z (x + s • chartNormal e) y, dist_comm y (x + s • chartNormal e)]))
  refine (hc.mem_iff hzC).2 ?_
  -- In chart coordinates `e z = e x + s (1, 0) + w` with `‖w‖ ≤ r`.
  set w := e z - e (x + s • chartNormal e) with hw
  have hwr : ‖w‖ ≤ r := by
    rw [hw, ← dist_eq_norm, e.dist_map]
    exact hz
  have hez : e z = e x + s • WithLp.toLp 2 ((1 : ℝ), (0 : E)) + w := by
    rw [hw, chart_add_smul_chartNormal, add_sub_cancel]
  have hfst : (e z).fst = (e x).fst + s + w.fst := by
    rw [hez]
    simp
  have hsnd : (e z).snd = (e x).snd + w.snd := by
    rw [hez]
    simp
  have hw1 : -r ≤ w.fst := by
    have := WithLp.norm_fst_le (x := w)
    rw [Real.norm_eq_abs] at this
    linarith [neg_abs_le w.fst]
  have hw2 : ‖w.snd‖ ≤ r := (WithLp.norm_snd_le (x := w)).trans hwr
  have hLip : φ (e z).snd ≤ φ (e x).snd + L * r := by
    have h := hc.lipschitzWith.dist_le_mul (e z).snd (e x).snd
    rw [Real.dist_eq, hsnd, dist_eq_norm, add_sub_cancel_left] at h
    have hL : (L : ℝ) * ‖w.snd‖ ≤ L * r := mul_le_mul_of_nonneg_left hw2 L.coe_nonneg
    rw [hsnd]
    linarith [le_abs_self (φ ((e x).snd + w.snd) - φ (e x).snd)]
  rw [hfst]
  nlinarith

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The normal translations and bumps used in a chart. -/
private theorem tendsto_chart_shift (e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) {δ : ℝ} :
    Tendsto (fun j : ℕ => (δ / 2 * (1 / ((j : ℝ) + 1))) • chartNormal e) atTop (𝓝 0) := by
  have h := (tendsto_const_nhds (x := δ / 2)).mul tendsto_one_div_add_atTop_nhds_zero_nat
  rw [mul_zero] at h
  simpa using h.smul_const (chartNormal e)

/-- The closure of the restrictions of whole-space test functions. -/
private abbrev testClosure (mu : Measure (WithLp 2 (ℝ × E))) [mu.IsAddHaarMeasure]
    (Ω : Opens (WithLp 2 (ℝ × E))) (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ) :
    Submodule ℝ (Wkp mu Ω p k) :=
  (LinearMap.range ((Wkp.restrictL (le_top : Ω ≤ ⊤) k).toLinearMap ∘ₗ
    Wkp.ofTestFunctionₗ (mu := mu) (p := p) k)).topologicalClosure

private theorem mem_testClosure_iff {k : ℕ} {u : Wkp mu Ω p k} :
    u ∈ testClosure mu Ω p k ↔ u ∈ closure (range fun psi : 𝓓((⊤ : Opens (WithLp 2 (ℝ × E))), ℝ) =>
      Wkp.restrictL (le_top : Ω ≤ ⊤) k (Wkp.ofTestFunctionₗ (mu := mu) (p := p) k psi)) := by
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, LinearMap.coe_range]
  rfl

/-- A piece with compact support inside `Ω` lies in the closure of test-function restrictions. -/
private theorem mem_testClosure_of_subset (hp : p ≠ (∞ : ℝ≥0∞)) {K : Set (WithLp 2 (ℝ × E))}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (k : ℕ) (w : Wkp mu Ω p k)
    (hw : ∀ᵐ x ∂mu.restrict Ω, x ∉ K → Wkp.value k w x = 0) :
    w ∈ testClosure mu Ω p k := by
  rw [mem_testClosure_iff]
  obtain ⟨δ, hδ, hδΩ⟩ := hK.exists_cthickening_subset_open Ω.isOpen hKΩ
  let r : ℕ → ℝ := fun j => δ / 2 * (1 / ((j : ℝ) + 1))
  have hr : ∀ j, 0 < r j := fun j => by positivity
  have hrδ : ∀ j, 2 * r j ≤ δ := fun j => by
    have : 1 / ((j : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    have : δ / 2 * (1 / ((j : ℝ) + 1)) ≤ δ / 2 := mul_le_of_le_one_right (by positivity) this
    simp only [r]
    linarith
  let phi : ℕ → ContDiffBump (0 : WithLp 2 (ℝ × E)) := fun j =>
    ⟨r j / 2, r j, by linarith [hr j], half_lt_self (hr j)⟩
  have hphi : Tendsto (fun j => (phi j).rOut) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := δ / 2)).mul tendsto_one_div_add_atTop_nhds_zero_nat
    rwa [mul_zero] at h
  refine Wkp.mem_closure_range_restrictL_ofTestFunctionₗ_top_of_shift hp hK hphi
    (tendsto_const_nhds (x := (0 : WithLp 2 (ℝ × E)))) (fun j x _ => ?_) k w hw
  rw [add_zero]
  by_cases hdis : Disjoint (closedBall x (phi j).rOut) K
  · exact Or.inr hdis
  left
  obtain ⟨y, hyB, hyK⟩ := not_disjoint_iff.1 hdis
  intro z hz
  exact hδΩ (mem_cthickening_of_dist_le z y δ K hyK (by
    have := dist_triangle z x y
    rw [mem_closedBall] at hyB hz
    rw [dist_comm] at hyB
    have := hrδ j
    simp only [phi] at hyB hz
    linarith))

/-- A piece supported in a boundary chart cylinder lies in the closure of test-function
restrictions. -/
private theorem mem_testClosure_of_chart (hp : p ≠ (∞ : ℝ≥0∞))
    {e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {φ : E → ℝ} {a b : ℝ}
    (hc : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzChartWith L e φ a b)
    {K : Set (WithLp 2 (ℝ × E))} (hK : IsCompact K) (hKC : K ⊆ e ⁻¹' normalCylinder a b)
    (k : ℕ) (w : Wkp mu Ω p k) (hw : ∀ᵐ x ∂mu.restrict Ω, x ∉ K → Wkp.value k w x = 0) :
    w ∈ testClosure mu Ω p k := by
  rw [mem_testClosure_iff]
  obtain ⟨δ, hδ, hδC⟩ := hK.exists_cthickening_subset_open
    ((isOpen_normalCylinder a b).preimage e.continuous) hKC
  let s : ℕ → ℝ := fun j => δ / 2 * (1 / ((j : ℝ) + 1))
  have hs : ∀ j, 0 < s j := fun j => by positivity
  have hsδ : ∀ j, s j ≤ δ / 2 := fun j => by
    have : 1 / ((j : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    exact mul_le_of_le_one_right (by positivity) this
  have hL : (0 : ℝ) < L + 1 := by positivity
  let r : ℕ → ℝ := fun j => s j / (L + 1)
  have hr : ∀ j, 0 < r j := fun j => div_pos (hs j) hL
  have hrs : ∀ j, r j ≤ s j := fun j =>
    div_le_self (hs j).le (by linarith [L.coe_nonneg])
  let phi : ℕ → ContDiffBump (0 : WithLp 2 (ℝ × E)) := fun j =>
    ⟨r j / 2, r j, by linarith [hr j], half_lt_self (hr j)⟩
  have hphi : Tendsto (fun j => (phi j).rOut) atTop (𝓝 0) := by
    have h := ((tendsto_const_nhds (x := δ / 2)).mul
      tendsto_one_div_add_atTop_nhds_zero_nat).div_const ((L : ℝ) + 1)
    rwa [mul_zero, zero_div] at h
  refine Wkp.mem_closure_range_restrictL_ofTestFunctionₗ_top_of_shift hp hK hphi
    (tendsto_chart_shift e (δ := δ)) (fun j x hx => ?_) k w hw
  have hrj : (phi j).rOut = r j := rfl
  have hsj : s j = δ / 2 * (1 / ((j : ℝ) + 1)) := rfl
  refine chart_ballCondition hc hδC ?_ (by linarith [hrs j, hsδ j]) (by linarith [hrs j, hsδ j])
    hx
  simp only [phi, r]
  rw [mul_div_cancel₀ _ hL.ne']

/-- **Density of functions smooth up to the boundary, at every order.** On a bounded Lipschitz
domain `Ω ⊆ ℝ × E`, for every order `k` and `1 ≤ p < ∞`, the restrictions to `Ω` of test functions
on the whole space are dense in `W^{k,p}(Ω)`, in the full Sobolev norm. -/
theorem Wkp.denseRange_restrictL_ofTestFunctionₗ_top_of_isLipschitzDomainWith (hp : p ≠ (∞ : ℝ≥0∞))
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : Bornology.IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) (k : ℕ) :
    DenseRange fun psi : 𝓓((⊤ : Opens (WithLp 2 (ℝ × E))), ℝ) =>
      Wkp.restrictL (le_top : Ω ≤ ⊤) k (Wkp.ofTestFunctionₗ (mu := mu) (p := p) k psi) := by
  classical
  intro u
  rw [← mem_testClosure_iff]
  obtain ⟨t, e, φ, a, b, ψ₀, ψ, hchart, ⟨hψ₀, -, hψ₀c, hψ₀Ω⟩, hψ, hsum⟩ :=
    hΩ.exists_contDiff_partitionOfUnity hb
  -- The interior piece `ψ₀ u` and the chart pieces `ψ x u`.
  obtain ⟨w₀, hw₀⟩ := Wkp.exists_value_ae_eq_mul_of_hasCompactSupport k hψ₀ hψ₀c u
  have hpiece : ∀ x : t, ∃ w : Wkp mu Ω p k,
      (Wkp.value k w : WithLp 2 (ℝ × E) → ℝ) =ᵐ[mu.restrict Ω]
        fun y => ψ x y * Wkp.value k u y := fun x =>
    Wkp.exists_value_ae_eq_mul_of_hasCompactSupport k (hψ x x.2).1 (hψ x x.2).2.2.1 u
  choose w hw using hpiece
  have hvanish : ∀ {c : WithLp 2 (ℝ × E) → ℝ} {v : Wkp mu Ω p k},
      (Wkp.value k v : WithLp 2 (ℝ × E) → ℝ) =ᵐ[mu.restrict Ω]
        (fun y => c y * Wkp.value k u y) →
      ∀ᵐ y ∂mu.restrict Ω, y ∉ tsupport c → Wkp.value k v y = 0 := fun hv => by
    filter_upwards [hv] with y hy hyK
    rw [hy, image_eq_zero_of_notMem_tsupport hyK, zero_mul]
  -- `u` is the sum of its pieces.
  have hu : u = w₀ + ∑ x : t, w x := by
    apply Wkp.ext k
    apply Lp.ext
    filter_upwards [Lp.coeFn_add (Wkp.value k w₀) (Wkp.value k (∑ x : t, w x)),
      Wkp.value_finsetSum_ae k Finset.univ w, hw₀, ae_all_iff.2 hw,
      ae_restrict_mem Ω.isOpen.measurableSet] with y hadd hfin h₀ hx hyΩ
    rw [Wkp.value_add, hadd, Pi.add_apply, hfin, h₀]
    simp only [hx]
    rw [← Finset.sum_mul, ← add_mul, Finset.sum_coe_sort t (fun x => ψ x y),
      hsum y (subset_closure hyΩ), one_mul]
  rw [hu]
  refine Submodule.add_mem _ (mem_testClosure_of_subset hp hψ₀c hψ₀Ω k w₀ (hvanish hw₀))
    (Submodule.sum_mem _ fun x _ => ?_)
  obtain ⟨-, -, hc, hab⟩ := hchart x x.2
  obtain ⟨-, -, hcpt, hts⟩ := hψ x x.2
  refine mem_testClosure_of_chart hp hc hcpt (hts.trans (preimage_mono (normalCylinder_mono
    ?_ le_rfl))) k (w x) (hvanish (hw x))
  have : (0 : ℝ) ≤ 2 * L * b x := by
    have := hc.toIsLipschitzChart.radius_pos
    positivity
  linarith

end TauCeti
