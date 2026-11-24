/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Chart
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.CoulombGauge
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Quotient
public import TauCeti.Analysis.PDE.Vortex.Gauge.Slice
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.PDE.Vortex.FramedGauge.Proper
import TauCeti.Analysis.PDE.Vortex.FramedGauge.RealChart
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding
import TauCeti.Topology.Algebra.GroupAction.SliceChart

/-!
# The slice theorem for the Sobolev gauge group

For an integer `k ≥ 3`, the Sobolev framed gauge group `G_(k+1)`
(`TauCeti.Vortex.SobolevTopologicalGaugeGroup`) acts on the continuous fields of the affine space
`A_m^k = x_m + H^k(ℂ; iT*ℂ ⊕ ℂ)` (`TauCeti.Vortex.SobolevFieldSpace`). At a field `x` the Coulomb
slice `TauCeti.Vortex.SobolevFieldSpace.coulombSlice x` is cut out by the gauge-fixing condition
`d₀* (y - x) = 0`, with `d₀* = gaugeAdjoint x` the formal adjoint of the infinitesimal gauge action
at `x`. This file proves the slice theorem at `x`: near `x`, the Coulomb slice is a chart of the
quotient `A_m^k / G_(k+1)`.

**Local uniqueness.** The Coulomb slice meets every gauge orbit near `x` at most once near the
identity. There are a neighbourhood `U` of `x` in `A_m^k` and a neighbourhood `N` of `1` in
`G_(k+1)` such that if `y ∈ U` and `u ∈ N` satisfy `d₀* (u · y) = d₀* y`, then `u = 1`
(`TauCeti.Vortex.SobolevFieldSpace.exists_mem_nhds_forall_eq_one_of_gaugeAdjoint_smul_eq`). In
particular a field of `U` in the Coulomb slice of `x` is carried out of that slice by every gauge
of `N` other than `1`
(`TauCeti.Vortex.SobolevFieldSpace.exists_mem_nhds_forall_eq_one_of_smul_mem_coulombSlice`).
The gauges near `1` are the exponentials `exp (i F)` of small real phases
(`TauCeti.Vortex.isOpenEmbedding_expGauge`), and a small phase in `H^(k+1)` is uniformly small and
of class `C²` by the Sobolev embedding. Fields near `x` in `A_m^k` are uniformly close to `x`
(`TauCeti.Vortex.SobolevFieldSpace.tendstoUniformly_of_tendsto`) and of class `C¹`. The pointwise
statement for such fields and phases is
`TauCeti.Vortex.exists_pos_forall_eq_zero_of_gaugeAdjoint_phaseGauge_eq`.

**Properness.** A gauge carrying a field near `x` to a field near `x` is near `1`
(`TauCeti.Vortex.SobolevFieldSpace.exists_mem_nhds_forall_mem_of_smul_eq`), because gauges between
convergent fields converge (`TauCeti.Vortex.SobolevFieldSpace.tendsto_of_gaugeTransform_eq`).
With local uniqueness, two fields of the Coulomb slice near `x` in the same orbit are equal, and
the only gauge relating them is `1`
(`TauCeti.Vortex.SobolevFieldSpace.exists_mem_nhds_forall_eq_one_of_mem_coulombSlice_of_smul_eq`).

**The slice theorem.** Every field `y` near `x` is moved into the Coulomb slice by a gauge
`g y` near `1` depending continuously on `y`
(`SobolevFieldSpace.exists_mem_nhds_continuousOn_forall_smul_mem_coulombSlice`).
Together with the previous step this gives an open neighbourhood `U` of `x` in its Coulomb slice
such that `(u, s) ↦ u · s` is an open embedding of `G_(k+1) × U` into `A_m^k` and `s ↦ [s]` is an
open embedding of `U` into `A_m^k / G_(k+1)`
(`TauCeti.Vortex.SobolevFieldSpace.exists_isOpen_isOpenEmbedding_smul_and_quotientMk_coulombSlice`),
by the general criterion `TauCeti.MulAction.exists_isOpen_injOn_isLocalHomeomorphOn_smul_slice`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
* S. K. Donaldson and P. B. Kronheimer, *The Geometry of Four-Manifolds*, Oxford University Press,
  1990, Section 4.2.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open MeasureTheory Filter Topology BesselPotentialSpace TemperedDistribution

namespace SobolevFieldSpace

open SobolevTopologicalGaugeGroup

variable {f : ContDiffBump (0 : ℝ)} {m k : ℕ} [Fact (1 < k)] {hs : 1 < (k : ℝ) + 1}

omit [Fact (1 < k)] in
/-- The coordinates of a field of `A_m^k`, `k ≥ 3`, are differentiable. -/
private theorem differentiable_apply (hk : 3 ≤ k) (w : SobolevFieldSpace f m k) (i : Fin 4) :
    Differentiable ℝ fun v ↦ w v i := by
  have hw : ContDiff ℝ 1 w := w.contDiff (by exact_mod_cast (by omega : 1 + 1 < k))
  exact differentiable_euclidean.1 (hw.differentiable one_ne_zero) i

variable (hs) in
/-- **Local uniqueness of the Coulomb gauge.** Let `x` be a continuous field of `A_m^k`, `k ≥ 3`.
There are a neighbourhood `U` of `x` and a neighbourhood `N` of `1` in the Sobolev gauge group
`G_(k+1)` such that for `y ∈ U` and `u ∈ N`, if `u · y` and `y` have the same Coulomb defect at
`x`, `d₀* (u · y) = d₀* y`, then `u = 1`. -/
theorem exists_mem_nhds_forall_eq_one_of_gaugeAdjoint_smul_eq (hk : 3 ≤ k)
    (x : SobolevFieldSpace f m k) :
    ∃ U ∈ 𝓝 x, ∃ N ∈ 𝓝 (1 : SobolevTopologicalGaugeGroup hs), ∀ y ∈ U, ∀ u ∈ N,
      (∀ z, gaugeAdjoint x ⇑(u • y) z = gaugeAdjoint x y z) → u = 1 := by
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (by omega : 1 < k)
  obtain ⟨ε, hε, huniq⟩ :=
    exists_pos_forall_eq_zero_of_gaugeAdjoint_phaseGauge_eq hk1 x.mem_framedFieldSpace x.continuous
  -- Fields near `x` are uniformly close to `x`.
  have hU : ∀ᶠ y in 𝓝 x, ∀ z, |y z 2 - x z 2| ≤ ε ∧ |y z 3 - x z 3| ≤ ε := by
    have hT := tendstoUniformly_of_tendsto hk1 (tendsto_id (x := 𝓝 x))
    rw [Metric.tendstoUniformly_iff] at hT
    filter_upwards [hT ε hε] with y hy z
    have hd := (hy z).le
    rw [dist_comm, dist_eq_norm] at hd
    have hi (i : Fin 4) : |y z i - x z i| ≤ ε := by
      simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le (y z - x z) i).trans hd
    exact ⟨hi 2, hi 3⟩
  -- Gauges near `1` are exponentials of uniformly small phases.
  have hN : ∀ᶠ u in 𝓝 (1 : SobolevTopologicalGaugeGroup hs),
      ∃ F, expGauge hs F = u ∧ ∀ z, |continuousRep F z| ≤ ε := by
    rw [← AddChar.map_zero_eq_one (expGauge hs), ← (isOpenEmbedding_expGauge hs).map_nhds_eq,
      eventually_map]
    have hT := tendstoUniformly_continuousRep (finrank_real_complex_lt_two_mul hs)
      (0 : realSubmodule ℂ (zero_le_one.trans hs.le))
    rw [Metric.tendstoUniformly_iff] at hT
    filter_upwards [hT ε hε] with F hF
    refine ⟨F, rfl, fun z ↦ ?_⟩
    simpa [Real.dist_eq, abs_sub_comm] using (hF z).le
  refine ⟨_, hU, _, hN, fun y hy u hu hcoul ↦ ?_⟩
  obtain ⟨F, rfl, hF⟩ := hu
  have hd := finrank_real_complex_lt_two_mul hs
  have hφ := continuousRep_mem_realSobolevFunctions hd F
  -- The phase `F` is `C²` and square integrable.
  have hφ2 : ContDiff ℝ 2 (continuousRep F) := by
    have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
    exact contDiff_of_mem_realSobolevFunctions
      (finrank_real_complex_add_two_mul_lt_two_mul (n := 2) (by push_cast; linarith)) hφ
      (continuous_continuousRep hd F)
  have hact : ⇑(expGauge hs F • y) = phaseGauge y (continuousRep F) := by
    rw [coe_smul, toSubgroup_expGauge]
    exact gaugeTransform_exp (hφ2.differentiable two_ne_zero) y
  have h0 := huniq y.continuous (differentiable_apply hk y 0) (differentiable_apply hk y 1) hy hφ2
    (memLp_of_mem_realSobolevFunctions hφ) hF (by simpa only [hact] using hcoul)
  rw [continuousRep_injective hd (h0.trans (map_zero _).symm), AddChar.map_zero_eq_one]

variable (hs) in
/-- **The Coulomb slice meets nearby gauge orbits once.** Let `x` be a continuous field of `A_m^k`,
`k ≥ 3`. There are a neighbourhood `U` of `x` and a neighbourhood `N` of `1` in `G_(k+1)` such
that if `y ∈ U` and `u · y`, `u ∈ N`, both lie in the Coulomb slice `coulombSlice x` of `x`, then
`u = 1`. -/
theorem exists_mem_nhds_forall_eq_one_of_smul_mem_coulombSlice (hk : 3 ≤ k)
    (x : SobolevFieldSpace f m k) :
    ∃ U ∈ 𝓝 x, ∃ N ∈ 𝓝 (1 : SobolevTopologicalGaugeGroup hs), ∀ y ∈ U, ∀ u ∈ N,
      y ∈ coulombSlice x → u • y ∈ coulombSlice x → u = 1 := by
  obtain ⟨U, hU, N, hN, h⟩ := exists_mem_nhds_forall_eq_one_of_gaugeAdjoint_smul_eq hs hk x
  refine ⟨U, hU, N, hN, fun y hy u hu hy0 huy0 ↦ h y hy u hu fun z ↦ ?_⟩
  -- Fields of `A_m^k`, `k ≥ 3`, are differentiable, so `d₀*` is additive on them.
  have hd (w : SobolevFieldSpace f m k) (i : Fin 4) : DifferentiableAt ℝ (fun v ↦ w v i) z :=
    differentiable_apply hk w i z
  have e₁ := mem_coulombSlice.1 hy0 z
  have e₂ := mem_coulombSlice.1 huy0 z
  rw [gaugeAdjoint_sub _ (hd y 0) (hd y 1) (hd x 0) (hd x 1)] at e₁
  rw [gaugeAdjoint_sub _ (hd (u • y) 0) (hd (u • y) 1) (hd x 0) (hd x 1)] at e₂
  linarith

/-! ### The slice theorem -/

/-- **Gauges between nearby fields are near `1`.** Let `x` be a continuous field of `A_m^k`,
`k ≥ 3`. For every neighbourhood `N` of `1` in `G_(k+1)` there is a neighbourhood `U` of `x` such
that every gauge carrying a field of `U` to a field of `U` lies in `N`. This is the local form of
the properness of the action: gauges between convergent fields converge
(`tendsto_of_gaugeTransform_eq`). -/
theorem exists_mem_nhds_forall_mem_of_smul_eq (hk : 2 < k) (x : SobolevFieldSpace f m k)
    {N : Set (SobolevTopologicalGaugeGroup hs)} (hN : N ∈ 𝓝 1) :
    ∃ U ∈ 𝓝 x, ∀ y ∈ U, ∀ y' ∈ U, ∀ u : SobolevTopologicalGaugeGroup hs, u • y = y' → u ∈ N := by
  -- Index the gauges `u` with `u • y = y'` by such triples, filtered by `(y, y') → (x, x)`.
  let ι := {q : (SobolevFieldSpace f m k × SobolevFieldSpace f m k) ×
    SobolevTopologicalGaugeGroup hs // q.2 • q.1.1 = q.1.2}
  have hxy : Tendsto (fun i : ι ↦ i.val.1) (comap (fun i : ι ↦ i.val.1) (𝓝 (x, x)))
      (𝓝 (x, x)) :=
    tendsto_comap
  have hu := tendsto_of_gaugeTransform_eq (xs := fun i : ι ↦ i.val.1.1)
    (ys := fun i : ι ↦ i.val.1.2) (us := fun i : ι ↦ i.val.2) (x := x) (y := x) (u := 1)
    hk (fun i ↦ by rw [← coe_smul, i.property]) (by simp [gaugeTransform_one])
    ((continuous_fst.tendsto _).comp hxy) ((continuous_snd.tendsto _).comp hxy)
  obtain ⟨t, ht, hts⟩ := mem_comap.1 (hu hN)
  obtain ⟨U₁, hU₁, U₂, hU₂, hsub⟩ := mem_nhds_prod_iff.1 ht
  exact ⟨U₁ ∩ U₂, inter_mem hU₁ hU₂, fun y hy y' hy' u huy ↦
    hts (a := ⟨((y, y'), u), huy⟩) (hsub ⟨hy.1, hy'.2⟩)⟩

variable (hs) in
/-- **The Coulomb slice meets the nearby gauge orbits once.** Let `x` be a continuous field of
`A_m^k`, `k ≥ 3`. Near `x`, two fields of the Coulomb slice of `x` related by a gauge of `G_(k+1)`
are equal, and the gauge is `1`. -/
theorem exists_mem_nhds_forall_eq_one_of_mem_coulombSlice_of_smul_eq (hk : 3 ≤ k)
    (x : SobolevFieldSpace f m k) :
    ∃ V ∈ 𝓝 x, ∀ y ∈ coulombSlice x ∩ V, ∀ y' ∈ coulombSlice x ∩ V,
      ∀ u : SobolevTopologicalGaugeGroup hs, u • y = y' → u = 1 := by
  obtain ⟨U, hU, N, hN, h⟩ := exists_mem_nhds_forall_eq_one_of_smul_mem_coulombSlice hs hk x
  obtain ⟨U', hU', h'⟩ := exists_mem_nhds_forall_mem_of_smul_eq (by omega) x hN
  refine ⟨U ∩ U', inter_mem hU hU', fun y hy y' hy' u huy ↦ ?_⟩
  exact h y hy.2.1 u (h' y hy.2.2 y' hy'.2.2 u huy) hy.1 (huy ▸ hy'.1)

variable (hs) in
/-- **The slice theorem for the Sobolev gauge group.** Let `x` be a continuous field of `A_m^k`,
`k ≥ 3`. There is an open neighbourhood `U` of `x` in its Coulomb slice such that

* `(u, s) ↦ u · s` is an open embedding of `G_(k+1) × U` into `A_m^k`, identifying `G_(k+1) × U`
  with an open gauge-invariant neighbourhood of the orbit of `x`;
* `s ↦ [s]` is an open embedding of `U` into the Sobolev moduli space `A_m^k / G_(k+1)` of framed
  fields, a chart of the quotient around the orbit of `x`. -/
theorem exists_isOpen_isOpenEmbedding_smul_and_quotientMk_coulombSlice (hk : 3 ≤ k)
    (x : SobolevFieldSpace f m k) :
    ∃ U : Set (coulombSlice x), IsOpen U ∧ ⟨x, self_mem_coulombSlice x⟩ ∈ U ∧
      IsOpenEmbedding (fun p : SobolevTopologicalGaugeGroup hs × U ↦
        p.1 • (p.2 : SobolevFieldSpace f m k)) ∧
      IsOpenEmbedding (fun s : U ↦ Quotient.mk (MulAction.orbitRel (SobolevTopologicalGaugeGroup hs)
        (SobolevFieldSpace f m k)) (s : SobolevFieldSpace f m k)) := by
  obtain ⟨W, hW, g, hg, hgx, hgT⟩ :=
    exists_mem_nhds_continuousOn_forall_smul_mem_coulombSlice hs hk x
  obtain ⟨U, hU, hxU, hinj, hloc⟩ := MulAction.exists_isOpen_injOn_isLocalHomeomorphOn_smul_slice
    (self_mem_coulombSlice x) hW hg hgx hgT
    (exists_mem_nhds_forall_eq_one_of_mem_coulombSlice_of_smul_eq hs hk x)
  exact ⟨U, hU, hxU, MulAction.isOpenEmbedding_smul_slice hU hinj hloc,
    MulAction.isOpenEmbedding_quotientMk_slice hU hinj hloc⟩

end SobolevFieldSpace

end TauCeti.Vortex
