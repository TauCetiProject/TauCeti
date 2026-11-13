/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Topology.UniformSpace.UniformConvergence
import TauCeti.Topology.MetricSpace.Lipschitz.Limit
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Compact convergence through a terminal time

Compact-uniform convergence for times before `b` extends to compact subsets of `(-∞, b] × U`
if the limit is continuous in time on a final interval `[a, b]`, and the approximating maps
have eventual time-Lipschitz bounds there, locally on compact subsets of `U`. The convergence
uses the original filter, with no further subsequence extraction. The target may be a
pseudometric space.

This preserves a chosen geometric subsequence when extending the coordinate metric jets
through the terminal time in pointed compactness of ancient flows.

## Main results

* `TauCeti.tendstoUniformlyOn_Iic_of_time_lipschitz`: convergence through the terminal time
  from compact interior convergence and eventual compact-local time-Lipschitz bounds.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Theorem 9.64.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public section

open Set Filter
open scoped Topology

namespace TauCeti

variable {ι X Y : Type*} {l : Filter ι} [l.NeBot]
  [TopologicalSpace X] [PseudoMetricSpace Y]

/-- Compact-uniform interior convergence extends through the terminal time along the same
filter. The time-Lipschitz constants and eventual thresholds may depend on
the compact spatial set; they are only needed on the final interval `[a, b]`. -/
theorem tendstoUniformlyOn_Iic_of_time_lipschitz
    {f : ι → ℝ × X → Y} {g : ℝ × X → Y} {U : Set X}
    {a b : ℝ} (hab : a < b)
    (hconv : ∀ K : Set (ℝ × X), IsCompact K → K ⊆ Iio b ×ˢ U →
      TendstoUniformlyOn f g l K)
    (hg : ∀ x ∈ U, ContinuousOn (fun t : ℝ ↦ g (t, x)) (Icc a b))
    (htime : ∀ V : Set X, IsCompact V → V ⊆ U →
      ∃ L : ℝ, 0 ≤ L ∧ ∀ᶠ k in l,
        ∀ x ∈ V, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
          dist (f k (s, x)) (f k (t, x)) ≤ L * |s - t|)
    {K : Set (ℝ × X)} (hK : IsCompact K) (hKU : K ⊆ Iic b ×ˢ U) :
    TendstoUniformlyOn f g l K := by
  let V : Set X := Prod.snd '' K
  have hV : IsCompact V := hK.image continuous_snd
  have hVU : V ⊆ U := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hKU hz).2
  obtain ⟨L, hL, hLip⟩ := htime V hV hVU
  have hgLip (x : X) (hx : x ∈ V) :
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        dist (g (s, x)) (g (t, x)) ≤ L * |s - t| := by
    apply time_lipschitz_of_interior_tendsto (l := l) (f := fun k t ↦ f k (t, x))
      hab (hg x (hVU hx))
    · intro t ht
      exact (hconv {(t, x)} isCompact_singleton
        (singleton_subset_iff.mpr ⟨ht.2, hVU hx⟩)).tendsto_at (mem_singleton _)
    · exact hLip.mono (fun k hk ↦ hk x hx)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let δ : ℝ := min ((b - a) / 2) (ε / (4 * (L + 1)))
  have hδ : 0 < δ := lt_min (half_pos (sub_pos.mpr hab)) (by positivity)
  have hδlength : δ ≤ b - a :=
    (min_le_left _ _).trans (half_le_self (sub_nonneg.mpr hab.le))
  have hδsmall : 2 * L * δ < ε / 2 := by
    have hδbound : δ ≤ ε / (4 * (L + 1)) := min_le_right _ _
    have hd := (le_div_iff₀ (by positivity : 0 < 4 * (L + 1))).mp hδbound
    nlinarith
  let shift : ℝ × X → ℝ × X := fun z ↦ (min z.1 (b - δ), z.2)
  have hshift : Continuous shift := (continuous_fst.min continuous_const).prodMk continuous_snd
  have hshiftU : shift '' K ⊆ Iio b ×ˢ U := by
    rintro _ ⟨z, hz, rfl⟩
    simp only [shift, mem_prod, mem_Iio]
    exact ⟨lt_of_le_of_lt (min_le_right _ _) (by linarith), (hKU hz).2⟩
  have hshiftconv := (Metric.tendstoUniformlyOn_iff.mp
    (hconv (shift '' K) (hK.image hshift) hshiftU)) (ε / 2) (by positivity)
  filter_upwards [hLip, hshiftconv] with k hk hkc z hz
  have hxV : z.2 ∈ V := mem_image_of_mem Prod.snd hz
  have hnear_f : dist (f k z) (f k (shift z)) ≤ L * δ :=
    dist_apply_min_sub_le hL hδ.le hδlength (hKU hz).1 (hk z.2 hxV)
  have hnear_g : dist (g (shift z)) (g z) ≤ L * δ := by
    rw [dist_comm]
    exact dist_apply_min_sub_le hL hδ.le hδlength (hKU hz).1 (hgLip z.2 hxV)
  have hinterior := hkc (shift z) (mem_image_of_mem shift hz)
  have htriangle := dist_triangle (f k z) (f k (shift z)) (g z)
  have htriangle' := dist_triangle (f k (shift z)) (g (shift z)) (g z)
  rw [dist_comm] at hinterior ⊢
  linarith

end TauCeti
