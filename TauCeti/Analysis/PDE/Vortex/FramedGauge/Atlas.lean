/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Divisor
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.SmoothChart
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.SymmetricPower
import TauCeti.Analysis.PDE.Vortex.FramedGauge.SobolevOrder

/-!
# The atlas and the divisor of the Sobolev moduli of framed plane vortices

For an integer `k ≥ 4`, the Sobolev framed gauge group `G_(k+1)`
(`TauCeti.Vortex.SobolevTopologicalGaugeGroup`) acts on the continuous fields of the affine space
`A_m^k = x_m + H^k(ℂ; iT*ℂ ⊕ ℂ)` (`TauCeti.Vortex.SobolevFieldSpace`), and the orbits of the
vortices form the subspace `TauCeti.Vortex.SobolevFieldSpace.vortexModuli` of the orbit space
`A_m^k / G_(k+1)`. At the orbit of a vortex lying in every `A_m^j`, the Coulomb slice chart is a
chart of this space with values in `ℝ^(2m)`
(`TauCeti.Vortex.SobolevFieldSpace.exists_openPartialHomeomorph_vortexModuli`). This file shows
that every vortex orbit has such a representative, so that the vortex moduli space is a charted
space modelled on `ℝ^(2m)`, locally homeomorphic to `ℝ^(2m)` at each point, and it describes the
inverse of the zero divisor of the orbits.

**Smooth representatives.** For `k ≥ 4` the Sobolev embedding makes a continuous field of `A_m^k`
of class `C²`, so a vortex of `A_m^k` is one of the `C²` vortices of `A_m^k`
(`TauCeti.Vortex.sobolevVortices`). By Taubes's existence and uniqueness theorems, each of these is
gauge equivalent under `G_(k+1)` to a smooth vortex lying in `A_m^s` for every `s`
(`TauCeti.Vortex.exists_sobolevGaugeGroup_smul_mem_framedFieldSpace`). So every vortex orbit is
the orbit of such a vortex
(`TauCeti.Vortex.SobolevFieldSpace.exists_mk_eq_forall_mem_framedFieldSpace`).

**The atlas.** The Coulomb slice chart at such a representative, cut down to a neighbourhood of
the orbit, is a chart at the orbit that is smooth in the field coordinates
(`TauCeti.Vortex.SobolevFieldSpace.exists_isSmoothVortexModuliChart_apply_eq_zero`). The charted
space `TauCeti.Vortex.SobolevFieldSpace.vortexModuliChartedSpace` chooses one such chart at each
orbit, and its atlas consists of all the charts smooth in the field coordinates
(`TauCeti.Vortex.SobolevFieldSpace.IsSmoothVortexModuliChart`). Any two of them are smoothly
compatible, so the vortex moduli space is a smooth manifold modelled on `ℝ^(2m)`
(`TauCeti.Vortex.SobolevFieldSpace.isManifold_vortexModuli`). It is Hausdorff, as a subspace of the
Hausdorff orbit space (`TauCeti.Vortex.SobolevFieldSpace.t2Space_quotient`). The dimension `2m` is
the index of the gauge-fixed deformation operator at a vortex.

**The divisor.** The zero divisor of a vortex orbit
(`TauCeti.Vortex.SobolevFieldSpace.vortexModuliDivisor`) is a bijection onto `Sym ℂ m`
(`TauCeti.Vortex.SobolevFieldSpace.vortexModuliDivisor_bijective`), by Taubes's existence and
uniqueness theorems, and in fact a homeomorphism
(`TauCeti.Vortex.SobolevFieldSpace.vortexModuliHomeomorph`). Its inverse sends a divisor to the
orbit of any vortex with that divisor
(`TauCeti.Vortex.SobolevFieldSpace.vortexModuliHomeomorph_symm_apply_mk`).

Whether the divisor is a diffeomorphism onto `Sym ℂ m`, with its smooth structure through the
coefficients of the monic polynomial with those roots, is not treated here.

## Main results

* `TauCeti.Vortex.SobolevFieldSpace.exists_mk_eq_forall_mem_framedFieldSpace`: for `k ≥ 4`, every
  vortex orbit in `A_m^k / G_(k+1)` is the orbit of a smooth vortex lying in `A_m^s` for every `s`.
* `TauCeti.Vortex.SobolevFieldSpace.exists_isSmoothVortexModuliChart_apply_eq_zero`: the vortex
  moduli space has a chart with values in `ℝ^(2m)` at each of its points, smooth in the field
  coordinates.
* `TauCeti.Vortex.SobolevFieldSpace.vortexModuliChartedSpace`: the vortex moduli space as a
  charted space modelled on `ℝ^(2m)`.
* `TauCeti.Vortex.SobolevFieldSpace.isManifold_vortexModuli`: its atlas is smooth.
* `TauCeti.Vortex.SobolevFieldSpace.vortexModuliDivisor_bijective`: the zero divisor of a vortex
  orbit is a bijection onto `Sym ℂ m`.
* `TauCeti.Vortex.SobolevFieldSpace.vortexModuliHomeomorph_symm_apply_mk`: the inverse of the
  divisor homeomorphism at the divisor of a vortex is the orbit of that vortex.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

namespace SobolevFieldSpace

open SobolevTopologicalGaugeGroup
open scoped ContDiff Manifold

variable {f : ContDiffBump (0 : ℝ)} {m k : ℕ} [Fact (1 < k)] {hs : 1 < (k : ℝ) + 1}

/-! ### Smooth representatives -/

/-- **Every vortex orbit has a smooth representative.** For `k ≥ 4`, every orbit of the vortex
moduli space in `A_m^k / G_(k+1)` is the orbit of a smooth vortex lying in `A_m^s` for every real
`s`. -/
theorem exists_mk_eq_forall_mem_framedFieldSpace (hk : 3 < k)
    {q : MulAction.orbitRel.Quotient (SobolevTopologicalGaugeGroup hs) (SobolevFieldSpace f m k)}
    (hq : q ∈ vortexModuli f m hs) :
    ∃ x : SobolevFieldSpace f m k, Quotient.mk _ x = q ∧ (∀ z, equation x z = 0) ∧
      ContDiff ℝ ∞ ⇑x ∧ ∀ s : ℝ, ⇑x ∈ framedFieldSpace f m s := by
  obtain ⟨y, hy, rfl⟩ := mem_vortexModuli_iff.1 hq
  obtain ⟨u, hc, hmem, -⟩ := exists_sobolevGaugeGroup_smul_mem_framedFieldSpace (hs := hs)
    ⟨_, toFramedFieldSpace_mem_sobolevVortices hk hy⟩
  have huy : ⇑((toSubgroup hs).symm u • y) =
      ((u • y.toFramedFieldSpace : framedFieldSpace f m k) : ℂ → EuclideanSpace ℝ (Fin 4)) := by
    rw [coe_smul, MulEquiv.apply_symm_apply, coe_sobolevGaugeGroup_smul, coe_toFramedFieldSpace]
  exact ⟨(toSubgroup hs).symm u • y, Quotient.sound (MulAction.mem_orbit y _),
    fun z ↦ (equation_smul_eq_zero_iff (by omega) _ y z).2 (hy z), huy ▸ hc, huy ▸ hmem⟩

/-! ### The atlas -/

/-- **The vortex moduli space has a smooth chart at each of its points.** For `k ≥ 4`, every orbit
`q` of the vortex moduli space in `A_m^k / G_(k+1)` lies in the source of a chart with values in
`ℝ^(2m)` sending `q` to `0` and smooth in the field coordinates: the Coulomb slice chart at a smooth
representative of `q`, cut down to a neighbourhood of `q`. -/
theorem exists_isSmoothVortexModuliChart_apply_eq_zero (hk : 3 < k) (q : vortexModuli f m hs) :
    ∃ e : OpenPartialHomeomorph (vortexModuli f m hs) (Fin (2 * m) → ℝ),
      IsSmoothVortexModuliChart f m hs e ∧ q ∈ e.source ∧ e q = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨_, hq⟩ := q
  obtain ⟨x, rfl, hsol, -, hmem⟩ := exists_mk_eq_forall_mem_framedFieldSpace hk hq
  exact exists_isSmoothVortexModuliChart (by omega) x (fun j ↦ hmem j) hsol

/-- **The vortex moduli space as a charted space modelled on `ℝ^(2m)`.** For `k ≥ 4`, the
charted space structure on the vortex moduli space in `A_m^k / G_(k+1)` whose atlas consists of the
charts smooth in the field coordinates (`IsSmoothVortexModuliChart`), and whose chart at an orbit
`q` is one of them sending `q` to `0` (`vortexModuliChartedSpace_chartAt_self`). -/
@[instance_reducible]
def vortexModuliChartedSpace (hk : 3 < k) :
    ChartedSpace (Fin (2 * m) → ℝ) (vortexModuli f m hs) where
  atlas := {e | IsSmoothVortexModuliChart f m hs e}
  chartAt q := (exists_isSmoothVortexModuliChart_apply_eq_zero hk q).choose
  mem_chart_source q := (exists_isSmoothVortexModuliChart_apply_eq_zero hk q).choose_spec.2.1
  chart_mem_atlas q := (exists_isSmoothVortexModuliChart_apply_eq_zero hk q).choose_spec.1

/-- The atlas of `vortexModuliChartedSpace` consists of the charts smooth in the field
coordinates. -/
theorem vortexModuliChartedSpace_atlas (hk : 3 < k) :
    (vortexModuliChartedSpace (f := f) (m := m) (hs := hs) hk).atlas =
      {e | IsSmoothVortexModuliChart f m hs e} :=
  (rfl)

/-- The chart of `vortexModuliChartedSpace` at an orbit sends that orbit to `0`. -/
theorem vortexModuliChartedSpace_chartAt_self (hk : 3 < k) (q : vortexModuli f m hs) :
    (vortexModuliChartedSpace (hs := hs) hk).chartAt q q = 0 :=
  (exists_isSmoothVortexModuliChart_apply_eq_zero hk q).choose_spec.2.2

/-- **The vortex moduli space is a smooth manifold of dimension `2m`.** For `k ≥ 4`, the atlas of
`vortexModuliChartedSpace` on the vortex moduli space in `A_m^k / G_(k+1)` is smooth: any two charts
smooth in the field coordinates have a smooth transition map
(`IsSmoothVortexModuliChart.contDiffOn_trans`). -/
theorem isManifold_vortexModuli (hk : 3 < k) :
    letI := vortexModuliChartedSpace (f := f) (m := m) (hs := hs) hk
    IsManifold 𝓘(ℝ, Fin (2 * m) → ℝ) ∞ (vortexModuli f m hs) := by
  let _i := vortexModuliChartedSpace (f := f) (m := m) (hs := hs) hk
  refine isManifold_of_contDiffOn _ _ _ fun e e' he he' ↦ ?_
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.range_id,
    Set.inter_univ, Set.preimage_id, Function.comp_id, Function.id_comp] using
    IsSmoothVortexModuliChart.contDiffOn_trans he he'

/-! ### The divisor of a vortex orbit -/

/-- **The divisor identifies the vortex moduli with `Sym ℂ m`** (Taubes). For `k ≥ 4`, the zero
divisor is a bijection from the vortex moduli space in `A_m^k / G_(k+1)` onto the effective
divisors of degree `m`, repeated points included. -/
theorem vortexModuliDivisor_bijective (hk : 3 < k) :
    Function.Bijective (vortexModuliDivisor (f := f) (m := m) hs hk) :=
  ⟨vortexModuliDivisor_injective hk, vortexModuliDivisor_surjective hk⟩

/-- The inverse of the divisor homeomorphism sends a divisor to the orbit of any continuous
vortex of `A_m^k` with that divisor. -/
theorem vortexModuliHomeomorph_symm_apply_mk (hk : 3 < k) {x : SobolevFieldSpace f m k}
    (hx : ∀ z, equation x z = 0) {D : Sym ℂ m}
    (hD : sobolevVortexDivisor ⟨_, toFramedFieldSpace_mem_sobolevVortices hk hx⟩ = D) :
    (vortexModuliHomeomorph f m hs hk).symm D =
      (⟨Quotient.mk _ x, mk_mem_vortexModuli hx⟩ : vortexModuli f m hs) :=
  (vortexModuliHomeomorph f m hs hk).symm_apply_eq.2 <| by
    rw [vortexModuliHomeomorph_apply, vortexModuliDivisor_mk hk hx, hD]

/-- The divisor of the orbit that the inverse of the divisor homeomorphism assigns to a divisor
is that divisor. -/
@[simp]
theorem vortexModuliDivisor_vortexModuliHomeomorph_symm (hk : 3 < k) (D : Sym ℂ m) :
    vortexModuliDivisor hs hk ((vortexModuliHomeomorph f m hs hk).symm D) = D := by
  rw [← vortexModuliHomeomorph_apply, Homeomorph.apply_symm_apply]

end SobolevFieldSpace

end TauCeti.Vortex
