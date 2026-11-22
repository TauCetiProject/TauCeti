/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Quotient
public import TauCeti.Topology.Algebra.ProperAction.TransverseSlice
import TauCeti.Analysis.PDE.Vortex.FramedGauge.CoulombGauge
import TauCeti.Analysis.PDE.Vortex.FramedGauge.Proper
import TauCeti.Analysis.PDE.Vortex.FramedGauge.Slice

/-!
# The Coulomb slices chart the orbit space of framed plane vortex fields

For an integer `k ≥ 3`, the Sobolev framed gauge group `G_(k+1)`
(`TauCeti.Vortex.SobolevTopologicalGaugeGroup`) acts freely and continuously on the continuous
fields of the affine space `A_m^k = x_m + H^k(ℂ; iT*ℂ ⊕ ℂ)`
(`TauCeti.Vortex.SobolevFieldSpace`). At a field `x` the Coulomb slice is cut out by the
gauge-fixing condition `d₀* (y - x) = 0`, with `d₀* = gaugeAdjoint x` the formal `L²` adjoint of
the infinitesimal gauge action at `x`. This file proves the slice theorem: near `x`, the Coulomb
slice is a chart of the orbit space `A_m^k / G_(k+1)`.

* **Properness.** The action is proper in the sense of Mathlib's `ProperSMul`
  (`TauCeti.Vortex.SobolevFieldSpace.properSMul`): if gauges `uᵢ` carry fields `xᵢ` to fields
  `yᵢ`, and `xᵢ → x`, `yᵢ → y`, then the gauges converge to a gauge carrying `x` to `y`
  (`TauCeti.Vortex.SobolevFieldSpace.exists_gaugeTransform_eq_and_tendsto`), and this holds along
  every filter, in particular along ultrafilters.
* **The slice theorem.** There is an open neighbourhood `V` of `x` such that `y ↦ [y]` is an open
  embedding of the fields of `V` in the Coulomb slice of `x` into `A_m^k / G_(k+1)`
  (`TauCeti.Vortex.SobolevFieldSpace.`
  `exists_isOpen_isOpenEmbedding_quotientMk_gaugeAdjoint_sub_eq_zero`).
  So each gauge orbit near the orbit of `x` meets the slice near `x` exactly once, and the slice
  near `x` is homeomorphic to an open neighbourhood of `[x]`. The inputs are the existence of the
  Coulomb gauge near `x`, a continuous gauge moving each nearby field into the slice
  (`TauCeti.Vortex.SobolevFieldSpace.`
  `exists_mem_nhds_continuousOn_forall_gaugeAdjoint_smul_sub_eq_zero`),
  its local uniqueness near `1`
  (`TauCeti.Vortex.SobolevFieldSpace.exists_mem_nhds_forall_eq_one_of_gaugeAdjoint_sub_eq_zero`),
  and properness, which excludes gauges far from `1` between fields near `x`. The topological
  argument is `ProperSMul.exists_isOpen_isOpenEmbedding_quotientMk_inter`.

At a plane vortex, the vortices in its Coulomb slice form a `2m`-dimensional analytic
submanifold near it (`TauCeti.Vortex.coulombSliceChart`). The slice theorem is what carries such
charts from the slice to the orbit space; that transfer is not made here.

## Main results

* `TauCeti.Vortex.SobolevFieldSpace.properSMul`: the action of `G_(k+1)` on `A_m^k`, `k ≥ 3`, is
  proper.
* `TauCeti.Vortex.SobolevFieldSpace.`
  `exists_isOpen_isOpenEmbedding_quotientMk_gaugeAdjoint_sub_eq_zero`: near a field, its Coulomb
  slice embeds openly into the orbit space.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* S. K. Donaldson and P. B. Kronheimer, *The Geometry of Four-Manifolds*, Oxford University Press,
  1990, Section 4.2.
-/

public section

namespace TauCeti.Vortex

namespace SobolevFieldSpace

open Filter Topology SobolevTopologicalGaugeGroup

variable {f : ContDiffBump (0 : ℝ)} {m k : ℕ} [Fact (1 < k)]

variable (f m) in
/-- **The action of `G_(k+1)` on `A_m^k` is proper**, for an integer `k ≥ 3`: the map
`(u, x) ↦ (u · x, x)` is a proper map. -/
theorem properSMul (hs : 1 < (k : ℝ) + 1) (hk : 2 < k) :
    ProperSMul (SobolevTopologicalGaugeGroup hs) (SobolevFieldSpace f m k) := by
  refine properSMul_iff_continuousSMul_ultrafilter_tendsto.2 ⟨inferInstance, fun 𝒰 x₁ x₂ h ↦ ?_⟩
  -- The fields `x` and `u · x` along `𝒰` converge to `x₂` and `x₁`.
  have hx := h.snd_nhds
  have hy := h.fst_nhds
  simp only at hx hy
  obtain ⟨u, hu, hconv⟩ := exists_gaugeTransform_eq_and_tendsto hk (us := Prod.fst)
    (fun p ↦ (coe_smul p.1 p.2).symm) hx hy
  exact ⟨u, ext (by rw [coe_smul, hu]), hconv⟩

/-- **The slice theorem for framed plane vortex fields.** Let `x` be a continuous field of
`A_m^k`, `k ≥ 3`. There is an open neighbourhood `V` of `x` such that `y ↦ [y]` is an open
embedding into the orbit space `A_m^k / G_(k+1)` of the fields `y ∈ V` in the Coulomb slice
`d₀* (y - x) = 0` of `x`. -/
theorem exists_isOpen_isOpenEmbedding_quotientMk_gaugeAdjoint_sub_eq_zero
    (hs : 1 < (k : ℝ) + 1) (hk : 3 ≤ k) (x : SobolevFieldSpace f m k) :
    ∃ V : Set (SobolevFieldSpace f m k), IsOpen V ∧ x ∈ V ∧
      IsOpenEmbedding fun y : ↥(V ∩ {y | ∀ z, gaugeAdjoint x (⇑y - ⇑x) z = 0}) ↦
        Quotient.mk (MulAction.orbitRel (SobolevTopologicalGaugeGroup hs)
          (SobolevFieldSpace f m k)) (y : SobolevFieldSpace f m k) := by
  have := properSMul f m hs (by omega)
  obtain ⟨U₁, hU₁, γ, hγ, hγx, hγS⟩ :=
    exists_mem_nhds_continuousOn_forall_gaugeAdjoint_smul_sub_eq_zero hs hk x
  obtain ⟨U₂, hU₂, N, hN, huniq⟩ :=
    exists_mem_nhds_forall_eq_one_of_gaugeAdjoint_sub_eq_zero hs hk x
  obtain ⟨V, hV, hxV, -, hemb⟩ := ProperSMul.exists_isOpen_isOpenEmbedding_quotientMk_inter
    (S := {y : SobolevFieldSpace f m k | ∀ z, gaugeAdjoint x (⇑y - ⇑x) z = 0})
    (IsCancelSMul.stabilizer_eq_bot x) (Filter.inter_mem hU₁ hU₂) (hγ.mono Set.inter_subset_left)
    hγx (fun y hy ↦ hγS y hy.1) hN fun y hy ↦ huniq y hy.2
  exact ⟨V, hV, hxV, hemb⟩

end SobolevFieldSpace

end TauCeti.Vortex
