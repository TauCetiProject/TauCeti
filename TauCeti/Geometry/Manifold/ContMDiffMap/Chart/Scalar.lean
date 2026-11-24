/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Seminorm
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Compact chart seminorms on the scalar field

On the scalar field `𝕜`, with its identity chart, the compact chart seminorms of a map
`f : 𝕜 → F` are suprema of the norms of its ordinary iterated derivatives `iteratedDeriv m f`
over a compact subset `K` of `𝕜`. Here `K` is regarded as a compact coordinate set of the chart
at any point (`ContMDiffMap.selfChartCompacts`), since the chart target is all of `𝕜`.

## Main results

* `ContMDiffMap.chartDerivativeSeminorm_selfChartCompacts_le_iff`: a bound on a derivative
  seminorm on the scalar field is a bound on the ordinary iterated derivative.
* `ContMDiffMap.chartCkSeminorm_selfChartCompacts_le_iff`: a bound on the compact `C^k` seminorm
  on the scalar field is a bound on the ordinary iterated derivatives through order `k`.
-/

public section

open Set TopologicalSpace
open scoped Manifold

namespace ContMDiffMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : WithTop ℕ∞}

/-- A compact subset of `𝕜`, as a compact coordinate set of the identity chart at `x`, whose
target is all of `𝕜`. -/
def selfChartCompacts (x : 𝕜) (K : Compacts 𝕜) : Compacts (extChartAt 𝓘(𝕜) x).target :=
  ⟨Subtype.val ⁻¹' (K : Set 𝕜), by
    -- The chart target is all of `𝕜`, so it is closed.
    have hc : IsClosed (extChartAt 𝓘(𝕜) x).target := by simp
    exact hc.isClosedEmbedding_subtypeVal.isCompact_preimage K.isCompact⟩

@[simp]
theorem coe_selfChartCompacts (x : 𝕜) (K : Compacts 𝕜) :
    (selfChartCompacts x K : Set (extChartAt 𝓘(𝕜) x).target) = Subtype.val ⁻¹' (K : Set 𝕜) :=
  (rfl)

@[simp]
theorem mem_selfChartCompacts {x : 𝕜} {K : Compacts 𝕜} {z : (extChartAt 𝓘(𝕜) x).target} :
    z ∈ selfChartCompacts x K ↔ (z : 𝕜) ∈ K :=
  Iff.rfl

/-- In the identity chart of `𝕜`, the norm of a coordinate derivative is the norm of the
ordinary iterated derivative. -/
theorem norm_chartIteratedFDeriv_self (f : C^n⟮𝓘(𝕜), 𝕜; 𝓘(𝕜, F), F⟯) (x : 𝕜) (m : ℕ)
    (hm : m ≤ n) (z : (extChartAt 𝓘(𝕜) x).target) :
    ‖chartIteratedFDeriv f x m hm z‖ = ‖iteratedDeriv m f z‖ := by
  rw [chartIteratedFDeriv_self_target_apply, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  simp [iteratedFDerivWithin_univ]

/-- A nonnegative bound on a derivative seminorm on the scalar field is a bound on the ordinary
iterated derivative on the compact set. -/
theorem chartDerivativeSeminorm_selfChartCompacts_le_iff (f : C^n⟮𝓘(𝕜), 𝕜; 𝓘(𝕜, F), F⟯)
    (x : 𝕜) (K : Compacts 𝕜) (m : ℕ) (hm : m ≤ n) {r : ℝ} (hr : 0 ≤ r) :
    chartDerivativeSeminorm x (selfChartCompacts x K) m hm f ≤ r ↔
      ∀ z ∈ K, ‖iteratedDeriv m f z‖ ≤ r := by
  rw [chartDerivativeSeminorm_le_iff _ _ _ _ _ hr]
  constructor
  · intro h z hz
    have h := h ⟨z, by simp⟩ hz
    rwa [norm_chartIteratedFDeriv_self] at h
  · intro h z hz
    rw [norm_chartIteratedFDeriv_self]
    exact h z hz

/-- A nonnegative bound on the compact `C^k` seminorm on the scalar field is a bound on the
ordinary iterated derivatives through order `k` on the compact set. -/
theorem chartCkSeminorm_selfChartCompacts_le_iff (f : C^n⟮𝓘(𝕜), 𝕜; 𝓘(𝕜, F), F⟯) (x : 𝕜)
    (K : Compacts 𝕜) (k : ℕ) (hk : k ≤ n) {r : ℝ} (hr : 0 ≤ r) :
    chartCkSeminorm x (selfChartCompacts x K) k hk f ≤ r ↔
      ∀ m ≤ k, ∀ z ∈ K, ‖iteratedDeriv m f z‖ ≤ r := by
  rw [chartCkSeminorm_le_iff _ _ _ _ _ hr]
  constructor
  · intro h m hm z hz
    have h := h m hm ⟨z, by simp⟩ hz
    rwa [norm_chartIteratedFDeriv_self] at h
  · intro h m hm z hz
    rw [norm_chartIteratedFDeriv_self]
    exact h m hm z hz

/-- The norm of an ordinary iterated derivative at a point of the compact set is at most the
derivative seminorm. -/
theorem norm_iteratedDeriv_le_chartDerivativeSeminorm (f : C^n⟮𝓘(𝕜), 𝕜; 𝓘(𝕜, F), F⟯)
    (x : 𝕜) (K : Compacts 𝕜) (m : ℕ) (hm : m ≤ n) {z : 𝕜} (hz : z ∈ K) :
    ‖iteratedDeriv m f z‖ ≤ chartDerivativeSeminorm x (selfChartCompacts x K) m hm f :=
  (chartDerivativeSeminorm_selfChartCompacts_le_iff f x K m hm (apply_nonneg _ _)).mp le_rfl z hz

/-- The norm of an ordinary iterated derivative of order at most `k` at a point of the compact
set is at most the compact `C^k` seminorm. -/
theorem norm_iteratedDeriv_le_chartCkSeminorm (f : C^n⟮𝓘(𝕜), 𝕜; 𝓘(𝕜, F), F⟯)
    (x : 𝕜) (K : Compacts 𝕜) (k : ℕ) (hk : k ≤ n) {m : ℕ} (hm : m ≤ k) {z : 𝕜} (hz : z ∈ K) :
    ‖iteratedDeriv m f z‖ ≤ chartCkSeminorm x (selfChartCompacts x K) k hk f :=
  (chartCkSeminorm_selfChartCompacts_le_iff f x K k hk (apply_nonneg _ _)).mp le_rfl m hm z hz

end ContMDiffMap
