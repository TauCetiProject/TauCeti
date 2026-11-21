/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.ShiftedMollification
import Mathlib.Geometry.Manifold.PartitionOfUnity
import TauCeti.Analysis.Normed.Module.Convex
import TauCeti.Analysis.Sobolev.Wkp.CompactSupport
import TauCeti.Analysis.Sobolev.Wkp.Leibniz

/-!
# Density of functions smooth up to the boundary on star-shaped and convex domains

Let `Ω` be an open subset of a finite-dimensional real inner product space `E` that is star-convex
with respect to every point of an open ball `ball x₀ ρ` of positive radius `ρ`. For `1 ≤ p < ∞`
and every natural order `k`, the restrictions to `Ω` of test functions on the whole space `E` are
dense in `W^{k,p}(Ω)` in the full Sobolev norm. Equivalently, elements of `W^{k,p}(Ω)` represented
almost everywhere by smooth compactly supported functions on `E` (or by globally smooth functions on
`E`) are dense. No boundedness hypothesis on `Ω` is required.

Unlike interior Meyers–Serrin approximants (`C^∞(Ω)`), whose derivatives may blow up near `∂Ω`,
restrictions of whole-space test functions extend smoothly to `closure Ω` with bounded derivatives
of every order. This allows uniform continuity estimates up to `closure Ω`, boundary trace
arguments, and polynomial-approximation bounds on star-shaped domains to pass from smooth functions
on `E` to `W^{k,p}(Ω)`.

Every nonempty open convex set contains an open ball and is star-convex with respect to each of its
points, while `W^{k,p}(∅)` is the zero space, so the same density holds on every open convex set
`Ω ⊆ E` without boundedness or nonemptiness hypotheses.

Both `p ≠ ∞` and the positive radius `0 < ρ` are sharp:
* At `p = ∞`, globally smooth representatives fail to be dense even on a nonempty bounded open
  interval (`TauCeti.Wkp.not_dense_contDiff_representatives_Ioo_top`).
* At `ρ ≤ 0`, the open ball `ball x₀ ρ` is empty, so the quantified condition
  `∀ y ∈ ball x₀ ρ, StarConvex ℝ y Ω` is vacuous. Weakening it to star-convexity about a single
  point also fails for `k ≥ 1`: the slit disk `ball 0 1 \ (Icc 0 1 ×ˢ {0})` in `ℝ²` is star-convex
  about `(-1 / 2, 0)`, yet `(x, y) ↦ if 0 < x ∧ 0 < y then x ^ (k + 1) else 0` is `Cᵏ` with bounded
  derivatives through order `k` on the slit disk while its jump across `(0, 1) × {0}` prevents
  `W^{k,p}` approximation by functions smooth on `ℝ²`.

## Main declarations

* `TauCeti.Wkp.denseRange_restrictL_ofTestFunctionₗ_top_of_forall_starConvex`: restrictions of
  whole-space test functions are dense in `W^{k,p}(Ω)` (`p < ∞`) when `Ω` is star-convex with
  respect to an open ball.
* `TauCeti.Wkp.dense_contDiff_hasCompactSupport_representatives_of_forall_starConvex`,
  `TauCeti.Wkp.dense_contDiff_representatives_of_forall_starConvex`: the corresponding density of
  smooth compactly supported and globally smooth representatives.
* `TauCeti.Wkp.denseRange_restrictL_ofTestFunctionₗ_top_of_convex`,
  `TauCeti.Wkp.dense_contDiff_hasCompactSupport_representatives_of_convex`,
  `TauCeti.Wkp.dense_contDiff_representatives_of_convex`: specializations to arbitrary open convex
  domains.

## References

* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorem 3.22.
* S. C. Brenner, L. R. Scott, *The Mathematical Theory of Finite Element Methods*, 3rd ed.,
  Definition 4.2.2 (p. 96) and Chapter 4, Exercises, no. 20 (p. 127).
* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.3.3.
-/

public section

noncomputable section

namespace TauCeti.Wkp

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Distributions Manifold Topology

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-- A Sobolev element vanishing outside a compact subset of `ball z (ρ / 2)` lies in
`restrictTestFunctionClosure`. -/
private theorem mem_restrictTestFunctionClosure_of_subset_ball (hp : p ≠ ⊤) {x₀ z : E} {ρ : ℝ}
    (hρ : 0 < ρ) (hstar : ∀ y ∈ ball x₀ ρ, StarConvex ℝ y (Omega : Set E))
    {K : Set E} (hK : IsCompact K) (hKB : K ⊆ ball z (ρ / 2))
    (k : ℕ) (w : Wkp mu Omega p k) (hw : ∀ᵐ x ∂mu.restrict Omega, x ∉ K → value k w x = 0) :
    w ∈ restrictTestFunctionClosure mu (le_top : Omega ≤ ⊤) p k := by
  rw [mem_restrictTestFunctionClosure_iff]
  obtain ⟨δ, hδ, hδB⟩ := hK.exists_cthickening_subset_open isOpen_ball hKB
  let c := min 1 (δ / (dist x₀ z + ρ / 2 + 1))
  have hc₀ : 0 < c := lt_min zero_lt_one (div_pos hδ (by positivity))
  let s : ℕ → ℝ := fun j => c * (1 / ((j : ℝ) + 1))
  have hs₀ : ∀ j, 0 < s j := fun j => by positivity
  have hs_le : ∀ j, s j ≤ c := fun j => mul_le_of_le_one_right hc₀.le
    (div_le_one_of_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) j]) (by positivity))
  let r : ℕ → ℝ := fun j => s j * (ρ / 2)
  have hr : ∀ j, 0 < r j := fun j => mul_pos (hs₀ j) (half_pos hρ)
  let phi : ℕ → ContDiffBump (0 : E) := fun j =>
    ⟨r j / 2, r j, half_pos (hr j), half_lt_self (hr j)⟩
  have hs_tendsto : Tendsto s atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds (x := c)).mul tendsto_one_div_add_atTop_nhds_zero_nat
  have hphi : Tendsto (fun j => (phi j).rOut) atTop (𝓝 0) := by
    simpa only [zero_mul] using hs_tendsto.mul_const (ρ / 2)
  have hh : Tendsto (fun j => s j • (x₀ - z)) atTop (𝓝 0) := by
    simpa only [zero_smul] using hs_tendsto.smul_const (x₀ - z)
  refine mem_closure_range_restrictL_ofTestFunctionₗ_top_of_shift hp hK hphi hh
    (fun j x hx => ?_) k w hw
  have hs₁ : s j ≤ 1 := (hs_le j).trans (min_le_left _ _)
  have hden : 0 < dist x₀ z + ρ / 2 + 1 := by positivity
  have hsδ : s j * (dist x₀ z + ρ / 2) ≤ δ :=
    calc s j * (dist x₀ z + ρ / 2)
        ≤ s j * (dist x₀ z + ρ / 2 + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (hs₀ j).le
      _ ≤ δ / (dist x₀ z + ρ / 2 + 1) * (dist x₀ z + ρ / 2 + 1) :=
          mul_le_mul_of_nonneg_right ((hs_le j).trans (min_le_right _ _)) hden.le
      _ = δ := div_mul_cancel₀ δ hden.ne'
  exact (closedBall_add_smul_sub_subset_interior_or_disjoint_of_forall_starConvex hstar hδB
    (hs₀ j) hs₁ hsδ (subset_closure hx)).imp_left fun h => h.trans interior_subset

/-- Any Sobolev element vanishing outside a compact set `K ⊆ E` lies in
`restrictTestFunctionClosure`. -/
private theorem mem_restrictTestFunctionClosure_of_isCompact (hp : p ≠ ⊤) {x₀ : E} {ρ : ℝ}
    (hρ : 0 < ρ) (hstar : ∀ y ∈ ball x₀ ρ, StarConvex ℝ y (Omega : Set E))
    {K : Set E} (hK : IsCompact K) (k : ℕ) (v : Wkp mu Omega p k)
    (hv : ∀ᵐ x ∂mu.restrict Omega, x ∉ K → value k v x = 0) :
    v ∈ restrictTestFunctionClosure mu (le_top : Omega ≤ ⊤) p k := by
  classical
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun z : E => ball z (ρ / 2)) (fun _ => isOpen_ball)
    (fun z _ => mem_iUnion.2 ⟨z, mem_ball_self (half_pos hρ)⟩)
  have hcover : K ⊆ ⋃ z : t, ball (z : E) (ρ / 2) := fun y hy => by
    obtain ⟨z, hzt, hyz⟩ := mem_iUnion₂.1 (ht hy)
    exact mem_iUnion.2 ⟨⟨z, hzt⟩, hyz⟩
  obtain ⟨ψ, hψ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, E) hK.isClosed
    (fun z : t => ball (z : E) (ρ / 2)) (fun _ => isOpen_ball) hcover
  have hψ_cont : ∀ z : t, ContDiff ℝ ∞ (ψ z) := fun z => (ψ z).contMDiff.contDiff
  have hψ_cpt : ∀ z : t, HasCompactSupport (ψ z) := fun z =>
    isCompact_of_isClosed_isBounded (isClosed_tsupport _) (isBounded_ball.subset (hψ z))
  choose w hw using fun z : t =>
    exists_value_ae_eq_mul_of_hasCompactSupport k (hψ_cont z) (hψ_cpt z) v
  have hv_eq : v = ∑ z : t, w z := by
    apply ext k
    apply Lp.ext
    filter_upwards [value_finsetSum_ae k Finset.univ w, ae_all_iff.2 hw, hv] with y hfin hwy hvy
    rw [hfin]
    simp only [hwy, ← Finset.sum_mul]
    by_cases hyK : y ∈ K
    · have hsum := ψ.sum_eq_one hyK
      rw [finsum_eq_sum_of_fintype] at hsum
      rw [hsum, one_mul]
    · rw [hvy hyK, mul_zero]
  rw [hv_eq]
  refine Submodule.sum_mem _ fun z _ =>
    mem_restrictTestFunctionClosure_of_subset_ball hp hρ hstar (hψ_cpt z).isCompact (hψ z) k (w z)
      ?_
  filter_upwards [hw z] with y hy hyB
  rw [hy, image_eq_zero_of_notMem_tsupport hyB, zero_mul]

/-- **Smooth-up-to-the-boundary density on star-shaped domains.** If an open set `Ω ⊆ E` is
star-convex with respect to every point of an open ball `ball x₀ ρ` of positive radius `ρ`, then
for `1 ≤ p < ∞` and every natural order `k`, restrictions to `Ω` of whole-space test functions are
dense in `W^{k,p}(Ω)` in the full Sobolev norm. No boundedness assumption on `Ω` is needed. -/
theorem denseRange_restrictL_ofTestFunctionₗ_top_of_forall_starConvex (hp : p ≠ ⊤) (k : ℕ)
    {x₀ : E} {ρ : ℝ} (hρ : 0 < ρ)
    (hstar : ∀ y ∈ ball x₀ ρ, StarConvex ℝ y (Omega : Set E)) :
    DenseRange fun psi : 𝓓((⊤ : Opens E), ℝ) =>
      restrictL (le_top : Omega ≤ ⊤) k (ofTestFunctionₗ (mu := mu) (p := p) k psi) := by
  intro u
  have hsub : {v : Wkp mu Omega p k | ∃ K : Set E, IsCompact K ∧
      ∀ᵐ x ∂mu.restrict Omega, x ∉ K → value k v x = 0} ⊆
        closure (range fun psi : 𝓓((⊤ : Opens E), ℝ) =>
          restrictL (le_top : Omega ≤ ⊤) k (ofTestFunctionₗ (mu := mu) (p := p) k psi)) := by
    rintro v ⟨K, hK, hv⟩
    exact (mem_restrictTestFunctionClosure_iff (le_top : Omega ≤ ⊤)).1
      (mem_restrictTestFunctionClosure_of_isCompact hp hρ hstar hK k v hv)
  have hcl := closure_minimal hsub isClosed_closure
  rw [(dense_exists_isCompact_value_ae_eq_zero (mu := mu) (Omega := Omega) hp k).closure_eq] at hcl
  exact hcl (mem_univ u)

/-- On an open set `Ω ⊆ E` that is star-convex with respect to every point of an open ball of
positive radius, elements of `W^{k,p}(Ω)` (`1 ≤ p < ∞`) represented by smooth compactly supported
functions on `E` are dense in the full Sobolev norm. -/
theorem dense_contDiff_hasCompactSupport_representatives_of_forall_starConvex (hp : p ≠ ⊤) (k : ℕ)
    {x₀ : E} {ρ : ℝ} (hρ : 0 < ρ)
    (hstar : ∀ y ∈ ball x₀ ρ, StarConvex ℝ y (Omega : Set E)) :
    Dense {u : Wkp mu Omega p k | ∃ f : E → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      (value k u : E → ℝ) =ᵐ[mu.restrict Omega] f} := by
  rw [← range_restrictL_ofTestFunctionₗ_top]
  exact denseRange_restrictL_ofTestFunctionₗ_top_of_forall_starConvex hp k hρ hstar

/-- On an open set `Ω ⊆ E` that is star-convex with respect to every point of an open ball of
positive radius, elements of `W^{k,p}(Ω)` (`1 ≤ p < ∞`) represented by globally smooth functions on
`E` are dense in the full Sobolev norm. -/
theorem dense_contDiff_representatives_of_forall_starConvex (hp : p ≠ ⊤) (k : ℕ)
    {x₀ : E} {ρ : ℝ} (hρ : 0 < ρ)
    (hstar : ∀ y ∈ ball x₀ ρ, StarConvex ℝ y (Omega : Set E)) :
    Dense {u : Wkp mu Omega p k | ∃ f : E → ℝ, ContDiff ℝ ∞ f ∧
      (value k u : E → ℝ) =ᵐ[mu.restrict Omega] f} := by
  refine Dense.mono ?_
    (dense_contDiff_hasCompactSupport_representatives_of_forall_starConvex hp k hρ hstar)
  rintro _ ⟨f, hf, _, hu⟩
  exact ⟨f, hf, hu⟩

/-- **Smooth-up-to-the-boundary density on convex open domains.** For every open convex set
`Ω ⊆ E`, `1 ≤ p < ∞`, and every natural order `k`, restrictions to `Ω` of whole-space test
functions are dense in `W^{k,p}(Ω)` in the full Sobolev norm. Neither boundedness nor nonemptiness
of `Ω` is required. -/
theorem denseRange_restrictL_ofTestFunctionₗ_top_of_convex (hp : p ≠ ⊤) (k : ℕ)
    (hΩ : Convex ℝ (Omega : Set E)) :
    DenseRange fun psi : 𝓓((⊤ : Opens E), ℝ) =>
      restrictL (le_top : Omega ≤ ⊤) k (ofTestFunctionₗ (mu := mu) (p := p) k psi) := by
  rcases (Omega : Set E).eq_empty_or_nonempty with hempty | ⟨x₀, hx₀⟩
  · intro u
    have hu0 : u = 0 := ext k (Lp.ext (by simp [EventuallyEq, hempty]))
    rw [hu0]
    exact subset_closure ⟨0, by simp⟩
  · obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 Omega.isOpen x₀ hx₀
    exact denseRange_restrictL_ofTestFunctionₗ_top_of_forall_starConvex hp k hρ
      fun _ hy => hΩ.starConvex (hball hy)

/-- On every open convex set `Ω ⊆ E`, elements of `W^{k,p}(Ω)` (`1 ≤ p < ∞`) represented by smooth
compactly supported functions on `E` are dense in the full Sobolev norm. -/
theorem dense_contDiff_hasCompactSupport_representatives_of_convex (hp : p ≠ ⊤) (k : ℕ)
    (hΩ : Convex ℝ (Omega : Set E)) :
    Dense {u : Wkp mu Omega p k | ∃ f : E → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      (value k u : E → ℝ) =ᵐ[mu.restrict Omega] f} := by
  rw [← range_restrictL_ofTestFunctionₗ_top]
  exact denseRange_restrictL_ofTestFunctionₗ_top_of_convex hp k hΩ

/-- On every open convex set `Ω ⊆ E`, elements of `W^{k,p}(Ω)` (`1 ≤ p < ∞`) represented by
globally smooth functions on `E` are dense in the full Sobolev norm. -/
theorem dense_contDiff_representatives_of_convex (hp : p ≠ ⊤) (k : ℕ)
    (hΩ : Convex ℝ (Omega : Set E)) :
    Dense {u : Wkp mu Omega p k | ∃ f : E → ℝ, ContDiff ℝ ∞ f ∧
      (value k u : E → ℝ) =ᵐ[mu.restrict Omega] f} := by
  refine Dense.mono ?_ (dense_contDiff_hasCompactSupport_representatives_of_convex hp k hΩ)
  rintro _ ⟨f, hf, _, hu⟩
  exact ⟨f, hf, hu⟩

end TauCeti.Wkp

end
