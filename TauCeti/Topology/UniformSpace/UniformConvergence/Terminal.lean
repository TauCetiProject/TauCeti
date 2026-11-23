/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Topology.UniformSpace.UniformConvergence
public import Mathlib.Topology.EMetricSpace.Basic
public import TauCeti.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Uniform convergence through a terminal time

Uniform convergence on the rectangles `[a, c] × V` for `a < c < b` extends to `[a, b] × V`
under eventual common time-Lipschitz bounds and left-continuity of the limit at `b`. The rectangle
theorem requires no topology on `V` and no compactness. The compact-set theorem derives its
rectangles from compact interior convergence, allowing a separate final interval and bound for
each compact spatial set. Both statements preserve the original filter and allow pseudoemetric
targets, including infinite distances.

The native metric consumer is in
`TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Terminal`: it extends the actual coordinate
metric jets and obtains convergence in the native chart `C^k` topology.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Theorem 9.64.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public section

open Set Filter
open scoped Topology NNReal ENNReal

namespace TauCeti

variable {ι X Y : Type*} {l : Filter ι} [PseudoEMetricSpace Y]
  {f : ι → ℝ × X → Y} {g : ℝ × X → Y} {a b : ℝ} {V : Set X} {L : ℝ≥0}

-- Closedness in the pointwise function topology passes the frequently common bound to the
-- interior limit; the standalone interval extension then supplies the prescribed endpoint.
private theorem lipschitzOnWith_Icc_of_uniform_interior
    (hconv : ∀ c ∈ Ioo a b, TendstoUniformlyOn f g l (Icc a c ×ˢ V))
    (hg : ∀ x ∈ V, ContinuousWithinAt (fun t ↦ g (t, x)) (Iio b) b)
    (hL : ∃ᶠ i in l, ∀ x ∈ V, LipschitzOnWith L (fun t ↦ f i (t, x)) (Icc a b))
    (x : X) (hx : x ∈ V) : LipschitzOnWith L (fun t ↦ g (t, x)) (Icc a b) := by
  apply LipschitzOnWith.Icc_of_Ico ?_ (hg x hx)
  apply lipschitzOnWith_iff_restrict.mpr
  refine (isClosed_setOfPred_lipschitzWith L).mem_of_frequently_of_tendsto
    (hL.mono fun i hi ↦ ((hi x hx).mono Ico_subset_Icc_self).to_restrict) ?_
  apply tendsto_pi_nhds.mpr
  intro t
  obtain ⟨c, htc, hcb⟩ := exists_between t.property.2
  exact (hconv c ⟨t.property.1.trans_lt htc, hcb⟩).tendsto_at ⟨⟨t.property.1, htc.le⟩, hx⟩

-- The clamp stays in one earlier rectangle, while both end segments have uniformly small
-- image diameter. Choosing a finite radius also handles an infinite requested tolerance.
private theorem tendstoUniformlyOn_Icc_prod_of_clamp (hab : a < b)
    (hconv : ∀ c ∈ Ioo a b, TendstoUniformlyOn f g l (Icc a c ×ˢ V))
    (hgL : ∀ x ∈ V, LipschitzOnWith L (fun t ↦ g (t, x)) (Icc a b))
    (hL : ∀ᶠ i in l, ∀ x ∈ V, LipschitzOnWith L (fun t ↦ f i (t, x)) (Icc a b)) :
    TendstoUniformlyOn f g l (Icc a b ×ˢ V) := by
  rw [EMetric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨η, hη, hηε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
  have hηn : 0 < η := by exact_mod_cast hη
  have hcont : Continuous (fun t : ℝ ↦ (L : ℝ≥0∞) * edist t b) :=
    (ENNReal.continuous_const_mul (by simp)).comp (continuous_id.edist continuous_const)
  have hηthird : (0 : ℝ≥0∞) < ↑(η / 3) := by positivity
  have hnear : ∀ᶠ t in 𝓝 b, (L : ℝ≥0∞) * edist t b < (↑(η / 3) : ℝ≥0∞) :=
    hcont.continuousAt.eventually_lt continuousAt_const (by simpa using hηthird)
  have hbefore : ∀ᶠ t in 𝓝[<] b, t ∈ Ioo a b := Ioo_mem_nhdsLT hab
  obtain ⟨c, hc, hsmall⟩ := (hbefore.and
    (hnear.filter_mono nhdsWithin_le_nhds)).exists
  have hconv' := (EMetric.tendstoUniformlyOn_iff.mp (hconv c hc)) (↑(η / 3)) (by positivity)
  filter_upwards [hL, hconv'] with i hi hconv_i p hp
  have hmin : min p.1 c ∈ Icc a c :=
    ⟨le_min hp.1.1 hc.1.le, min_le_right _ _⟩
  have hfnear := ((hi p.2 hp.2).mono (Icc_subset_Icc hc.1.le le_rfl)).edist_apply_min_le
    hp.1.2
  have hgnear := ((hgL p.2 hp.2).mono (Icc_subset_Icc hc.1.le le_rfl)).edist_apply_min_le
    hp.1.2
  have hsum : (↑(η / 3) : ℝ≥0∞) + ↑(η / 3) + ↑(η / 3) = ↑η := by
    rw [← ENNReal.coe_add, ← ENNReal.coe_add]
    congr 1
    ring
  calc
    edist (g p) (f i p) ≤ edist (g p) (g (min p.1 c, p.2)) +
        edist (g (min p.1 c, p.2)) (f i (min p.1 c, p.2)) +
        edist (f i (min p.1 c, p.2)) (f i p) := edist_triangle4 _ _ _ _
    _ < ↑(η / 3) + ↑(η / 3) + ↑(η / 3) :=
      ENNReal.add_lt_add (ENNReal.add_lt_add (hgnear.trans_lt hsmall) (hconv_i _ ⟨hmin, hp.2⟩))
        (by simpa only [edist_comm] using hfnear.trans_lt hsmall)
    _ < ε := hsum ▸ hηε

/-- Uniform convergence on all earlier rectangles extends to the terminal rectangle under an
eventual common time-Lipschitz bound. The spatial set has no topological assumptions. -/
theorem tendstoUniformlyOn_Icc_prod_of_lipschitzOnWith (hab : a < b)
    (hconv : ∀ c ∈ Ioo a b, TendstoUniformlyOn f g l (Icc a c ×ˢ V))
    (hg : ∀ x ∈ V, ContinuousWithinAt (fun t ↦ g (t, x)) (Iio b) b)
    (hL : ∀ᶠ i in l, ∀ x ∈ V, LipschitzOnWith L (fun t ↦ f i (t, x)) (Icc a b)) :
    TendstoUniformlyOn f g l (Icc a b ×ˢ V) := by
  by_cases hl : l = ⊥
  · simp [hl, TendstoUniformlyOn]
  have : l.NeBot := ⟨hl⟩
  exact tendstoUniformlyOn_Icc_prod_of_clamp hab hconv
    (lipschitzOnWith_Icc_of_uniform_interior hconv hg hL.frequently) hL

/-- Compact-uniform interior convergence extends through the terminal time along the same
filter. Each compact spatial set may have its own final interval and eventual time bound. -/
theorem tendstoUniformlyOn_of_lipschitzOnWith_of_subset_Iic_prod [TopologicalSpace X]
    {U : Set X}
    (hconv : ∀ K : Set (ℝ × X), IsCompact K → K ⊆ Iio b ×ˢ U →
      TendstoUniformlyOn f g l K)
    (hg : ∀ x ∈ U, ContinuousWithinAt (fun t ↦ g (t, x)) (Iio b) b)
    (htime : ∀ V : Set X, IsCompact V → V ⊆ U →
      ∃ a < b, ∃ L : ℝ≥0, ∀ᶠ i in l,
        ∀ x ∈ V, LipschitzOnWith L (fun t ↦ f i (t, x)) (Icc a b))
    {K : Set (ℝ × X)} (hK : IsCompact K) (hKU : K ⊆ Iic b ×ˢ U) :
    TendstoUniformlyOn f g l K := by
  let V : Set X := Prod.snd '' K
  have hV : IsCompact V := hK.image continuous_snd
  have hVU : V ⊆ U := by
    rintro _ ⟨p, hp, rfl⟩
    exact (hKU hp).2
  obtain ⟨a, hab, L, hL⟩ := htime V hV hVU
  have hrect := tendstoUniformlyOn_Icc_prod_of_lipschitzOnWith hab
    (fun c hc ↦ hconv _ (isCompact_Icc.prod hV)
      (prod_mono (fun t ht ↦ ht.2.trans_lt hc.2) hVU))
    (fun x hx ↦ hg x (hVU hx)) hL
  have hpast := hconv (K ∩ Prod.fst ⁻¹' Iic a)
    (hK.inter_right (isClosed_Iic.preimage continuous_fst))
    (fun p hp ↦ ⟨hp.2.trans_lt hab, (hKU hp.1).2⟩)
  intro u hu
  filter_upwards [hpast u hu, hrect u hu] with i hipast hirect p hp
  by_cases ht : p.1 ≤ a
  · exact hipast p ⟨hp, ht⟩
  · exact hirect p ⟨⟨le_of_not_ge ht, (hKU hp).1⟩, mem_image_of_mem Prod.snd hp⟩

end TauCeti
