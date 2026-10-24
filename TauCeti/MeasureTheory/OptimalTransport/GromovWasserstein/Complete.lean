/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Lp.Metric
public import TauCeti.MeasureTheory.OptimalTransport.Chain
public import TauCeti.MeasureTheory.OptimalTransport.GromovWasserstein.Space

/-!
# Completeness of the measured-kernel Gromov–Wasserstein space

If the metric target `Z` is complete, the space of finite-size measured kernels modulo weak
isomorphism is complete for every `1 ≤ p ≤ ∞`. Neither separability of `Z` nor symmetry or
continuity of the kernels is required. Carrier universes remain independent of the target.

Optimal couplings of consecutive presentations are glued on the countable product of their
carriers. On the square of that common probability space, the pulled-back kernels have
summable `Lᵖ` jumps, hence a strongly measurable limit kernel with the same tail bounds.
Its finite moment follows by comparison with the first kernel. This also supplies a
quantitative convergence theorem for chains with summable GW jumps.

## References

* M. Bauer, F. Mémoli, T. Needham and M. Nishino, *The Z-Gromov–Wasserstein distance*,
  J. Mach. Learn. Res. 26 (2025), Theorem 39. The distance here uses the full distortion,
  without the factor of one half in that source.
-/

public section

noncomputable section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace TauCeti

universe u v

namespace GromovWassersteinPresentation

variable {p : ℝ≥0∞} {Z : Type v} [MetricSpace Z] [CompleteSpace Z] [Fact (1 ≤ p)]

/-- A sequence of presentations with summable GW jumps has a limit presentation, with the
distance from its `n`th term bounded by the corresponding tail. This includes `p = ∞`
and nonseparable complete targets. -/
theorem exists_edist_le_tsum
    (K : ℕ → GromovWassersteinPresentation.{u} p Z) {b : ℕ → ℝ≥0∞}
    (hb : ∑' n, b n ≠ ∞) (hK : ∀ n, edist (K n) (K (n + 1)) ≤ b n) :
    ∃ L : GromovWassersteinPresentation.{u} p Z,
      ∀ n, edist (K n) L ≤ ∑' k, b (n + k) := by
  -- Consecutive optimal couplings produce a common countable probability carrier.
  choose π hπ hopt using fun n ↦
    exists_isCoupling_gromovWassersteinDistortion_eq_of_standardBorelSpace
      (K n).measure (K (n + 1)).measure
      (K n).aestronglyMeasurable_kernel (K (n + 1)).aestronglyMeasurable_kernel p
  have : ∀ n, IsProbabilityMeasure (π n) := fun n ↦ (hπ n).isProbabilityMeasure
  let Ω := (n : ℕ) → (K n).Carrier
  have : ∀ n, Nonempty (K n).Carrier := fun n ↦ Measure.nonempty_of_neZero (K n).measure
  let P : Measure Ω := TauCeti.Measure.chainMeasure π
  have hev : ∀ n, MeasurePreserving (fun x : Ω ↦ x n) P (K n).measure := fun n ↦
    ⟨measurable_pi_apply n, by
      rw [TauCeti.Measure.map_eval_chainMeasure π n
        (fun k _ ↦ (hπ k).snd_eq.trans (hπ (k + 1)).fst_eq.symm), (hπ n).fst_eq]⟩
  have hadj : ∀ n, P.map (fun x : Ω ↦ (x n, x (n + 1))) = π n := fun n ↦
    TauCeti.Measure.map_adjacent_chainMeasure π n
      (fun k _ ↦ (hπ k).snd_eq.trans (hπ (k + 1)).fst_eq.symm)
  let f : ℕ → Ω × Ω → Z := fun n q ↦ (K n).kernel (q.1 n, q.2 n)
  have hf : ∀ n, AEStronglyMeasurable (f n) (P.prod P) := fun n ↦
    (K n).aestronglyMeasurable_kernel.comp_quasiMeasurePreserving
      ((hev n).prod (hev n)).quasiMeasurePreserving
  have hjump : ∀ n, eLpNorm (fun q ↦ dist (f n q) (f (n + 1) q)) p (P.prod P) ≤ b n := by
    intro n
    have heq := gromovWassersteinDistortion_map_prodMk (hev n) (hev (n + 1))
      (K n).aestronglyMeasurable_kernel (K (n + 1)).aestronglyMeasurable_kernel p
    rw [hadj n, hopt n] at heq
    simp_rw [edist_dist, ← Real.enorm_eq_ofReal dist_nonneg] at heq
    rw [eLpNorm_enorm _ ((hf n).dist (hf (n + 1)))] at heq
    exact heq.symm.le.trans (by simpa only [edist_eq] using hK n)
  -- The metric-valued limit theorem works inside the countable union of essential ranges.
  obtain ⟨g, hg, -, hbound⟩ :=
    exists_stronglyMeasurable_limit_of_summable_eLpNorm_dist Fact.out hf hb hjump
  have hbound' : ∀ n, eLpNorm (fun q ↦ edist (f n q) (g q)) p (P.prod P) ≤
      ∑' k, b (n + k) := by
    intro n
    simp_rw [edist_dist, ← Real.enorm_eq_ofReal dist_nonneg]
    rw [eLpNorm_enorm _ ((hf n).dist hg.aestronglyMeasurable)]
    exact hbound n
  -- A finite moment of the first kernel transfers to the limit by the triangle inequality.
  obtain ⟨z, hz⟩ := (K 0).finite_moment
  have hfz : MemLp (fun q ↦ edist (f 0 q) z) p (P.prod P) :=
    hz.comp_measurePreserving ((hev 0).prod (hev 0))
  have hfg : MemLp (fun q ↦ edist (f 0 q) (g q)) p (P.prod P) :=
    lt_of_le_of_lt (hbound' 0) (by simpa using hb.lt_top)
  have hgz : MemLp (fun q ↦ edist (g q) z) p (P.prod P) :=
    (hfg.add hfz).of_le_enorm (continuous_edist.comp_aestronglyMeasurable₂ hg.aestronglyMeasurable
        aestronglyMeasurable_const)
      (.of_forall fun q ↦ by
        simpa only [enorm_eq_self, Pi.add_apply, edist_comm] using
          edist_triangle (g q) (f 0 q) z)
  let L : GromovWassersteinPresentation.{u} p Z :=
    { Carrier := Ω
      measure := P
      kernel := g
      aestronglyMeasurable_kernel := hg.aestronglyMeasurable
      finite_moment := ⟨z, hgz⟩ }
  refine ⟨L, fun n ↦ ?_⟩
  rw [edist_eq]
  exact (gromovWassersteinEDist_le_eLpNorm (hev n) (MeasurePreserving.id P)
    (K n).aestronglyMeasurable_kernel hg.aestronglyMeasurable p).trans (hbound' n)

end GromovWassersteinPresentation

namespace GromovWassersteinSpace

/-- The measured-kernel GW quotient is complete over any complete metric target, at every
`1 ≤ p ≤ ∞`. No global separability assumption on the target is needed. -/
instance instCompleteSpace {p : ℝ≥0∞} {Z : Type v} [MetricSpace Z] [CompleteSpace Z]
    [Fact (1 ≤ p)] : CompleteSpace (GromovWassersteinSpace.{u} p Z) := by
  refine EMetric.complete_of_convergent_controlled_sequences (fun n ↦ 2⁻¹ ^ n)
    (fun n ↦ ENNReal.pow_pos (by simp) n) fun s hs ↦ ?_
  choose K hK using fun n ↦ mk_surjective (s n)
  have hb : ∑' n, (2 : ℝ≥0∞)⁻¹ ^ n ≠ ∞ := by
    simp [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two]
  have hjump : ∀ n, edist (K n) (K (n + 1)) ≤ (2 : ℝ≥0∞)⁻¹ ^ n := fun n ↦ by
    have h := (hs n n (n + 1) le_rfl (Nat.le_succ n)).le
    rwa [← hK n, ← hK (n + 1), edist_mk] at h
  obtain ⟨L, hL⟩ := GromovWassersteinPresentation.exists_edist_le_tsum K hb hjump
  refine ⟨mk L, tendsto_iff_edist_tendsto_0.2 ?_⟩
  have hle : ∀ n, edist (s n) (mk L) ≤ ∑' k, (2 : ℝ≥0∞)⁻¹ ^ (n + k) := fun n ↦ by
    rw [← hK n, edist_mk]
    simpa only [GromovWassersteinPresentation.edist_eq] using hL n
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [add_comm] using ENNReal.tendsto_sum_nat_add _ hb)
    (fun _ ↦ zero_le) hle

end GromovWassersteinSpace

end TauCeti
