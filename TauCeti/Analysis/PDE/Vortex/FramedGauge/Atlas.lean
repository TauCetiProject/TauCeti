/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ChartedSpace
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Divisor
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.OrbitChart
import Mathlib.Topology.LocalAtTarget
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
space modelled on `ℝ^(2m)`, locally homeomorphic to `ℝ^(2m)` at each point, and it descends the
zero divisor to the orbits.

**Smooth representatives.** For `k ≥ 4` the Sobolev embedding makes a continuous field of `A_m^k`
of class `C²`, so a vortex of `A_m^k` is one of the `C²` vortices of `A_m^k`
(`TauCeti.Vortex.sobolevVortices`). By Taubes's existence and uniqueness theorems, each of these is
gauge equivalent under `G_(k+1)` to a smooth vortex lying in `A_m^s` for every `s`
(`TauCeti.Vortex.exists_sobolevGaugeGroup_smul_mem_framedFieldSpace`). So every vortex orbit is
the orbit of such a vortex
(`TauCeti.Vortex.SobolevFieldSpace.exists_mk_eq_forall_mem_framedFieldSpace`).

**The atlas.** The Coulomb slice chart at such a representative is a chart at the orbit
(`TauCeti.Vortex.SobolevFieldSpace.exists_openPartialHomeomorph_vortexModuli_apply_eq_zero`). The
charted space `TauCeti.Vortex.SobolevFieldSpace.vortexModuliChartedSpace` chooses one such chart
at each orbit, so that the vortex moduli space is locally homeomorphic to `ℝ^(2m)`. It is
Hausdorff, as a subspace of the Hausdorff orbit space
(`TauCeti.Vortex.SobolevFieldSpace.t2Space_quotient`). The dimension `2m` is the index of the
gauge-fixed deformation operator at a vortex.

**The divisor.** The zero divisor is gauge invariant, so it descends to the vortex moduli space
(`TauCeti.Vortex.SobolevFieldSpace.vortexModuliDivisor`). It is a bijection onto `Sym ℂ m`
(`TauCeti.Vortex.SobolevFieldSpace.vortexModuliDivisor_bijective`), by Taubes's existence and
uniqueness theorems. It is continuous
(`TauCeti.Vortex.SobolevFieldSpace.continuous_vortexModuliDivisor`): convergence in `A_m^k`
implies uniform convergence of the fields, along which the zero divisor is continuous by Hurwitz's
theorem (`TauCeti.Vortex.SobolevFieldSpace.tendsto_of_tendsto`), and the quotient map onto the
vortex moduli space is open.

Whether the transition maps of the atlas are smooth, and whether the inverse of the divisor is
continuous, is not treated here.

## Main results

* `TauCeti.Vortex.SobolevFieldSpace.exists_mk_eq_forall_mem_framedFieldSpace`: for `k ≥ 4`, every
  vortex orbit in `A_m^k / G_(k+1)` is the orbit of a smooth vortex lying in `A_m^s` for every `s`.
* `TauCeti.Vortex.SobolevFieldSpace.exists_openPartialHomeomorph_vortexModuli_apply_eq_zero`: the
  vortex moduli space has a chart with values in `ℝ^(2m)` at each of its points.
* `TauCeti.Vortex.SobolevFieldSpace.vortexModuliChartedSpace`: the vortex moduli space as a
  charted space modelled on `ℝ^(2m)`.
* `TauCeti.Vortex.SobolevFieldSpace.vortexModuliDivisor`: the zero divisor of a vortex orbit, a
  continuous bijection onto `Sym ℂ m`.

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

open Filter Topology SobolevTopologicalGaugeGroup
open scoped ContDiff

variable {f : ContDiffBump (0 : ℝ)} {m k : ℕ}

/-- For `k ≥ 4`, a continuous vortex of `A_m^k` is one of the `C²` vortices of `A_m^k`, by the
Sobolev embedding of `H^k(ℂ)` into `C²`. -/
theorem toFramedFieldSpace_mem_sobolevVortices (hk : 3 < k) {x : SobolevFieldSpace f m k}
    (hx : ∀ z, equation x z = 0) : x.toFramedFieldSpace ∈ sobolevVortices f m k := by
  have hk' : (3 : ℝ) < k := by exact_mod_cast hk
  exact mem_sobolevVortices.2 ⟨contDiff_of_mem_framedFieldSpace (by push_cast; linarith)
    x.continuous x.mem_framedFieldSpace, hx⟩

variable [Fact (1 < k)] {hs : 1 < (k : ℝ) + 1}

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

/-- **The vortex moduli space is locally homeomorphic to `ℝ^(2m)` at each of its points.** For
`k ≥ 4`, every orbit `q` of the vortex moduli space in `A_m^k / G_(k+1)` lies in the source of a
chart with values in `ℝ^(2m)` sending `q` to `0`: the Coulomb slice chart at a smooth
representative of `q`. -/
theorem exists_openPartialHomeomorph_vortexModuli_apply_eq_zero (hk : 3 < k)
    (q : vortexModuli f m hs) :
    ∃ e : OpenPartialHomeomorph (vortexModuli f m hs) (Fin (2 * m) → ℝ),
      q ∈ e.source ∧ e q = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨_, hq⟩ := q
  obtain ⟨x, rfl, hsol, -, hmem⟩ := exists_mk_eq_forall_mem_framedFieldSpace hk hq
  exact exists_openPartialHomeomorph_vortexModuli (by omega) x (fun j ↦ hmem j) hsol

/-- **The vortex moduli space as a charted space modelled on `ℝ^(2m)`.** For `k ≥ 4`, the
charted space structure on the vortex moduli space in `A_m^k / G_(k+1)` whose chart at an orbit
`q` is a chart of `exists_openPartialHomeomorph_vortexModuli_apply_eq_zero`, sending `q` to `0`
(`vortexModuliChartedSpace_chartAt_self`); its atlas consists of these charts. -/
@[instance_reducible]
def vortexModuliChartedSpace (hk : 3 < k) :
    ChartedSpace (Fin (2 * m) → ℝ) (vortexModuli f m hs) where
  atlas := Set.range fun q ↦ (exists_openPartialHomeomorph_vortexModuli_apply_eq_zero hk q).choose
  chartAt q := (exists_openPartialHomeomorph_vortexModuli_apply_eq_zero hk q).choose
  mem_chart_source q :=
    (exists_openPartialHomeomorph_vortexModuli_apply_eq_zero hk q).choose_spec.1
  chart_mem_atlas q := ⟨q, rfl⟩

/-- The chart of `vortexModuliChartedSpace` at an orbit sends that orbit to `0`. -/
theorem vortexModuliChartedSpace_chartAt_self (hk : 3 < k) (q : vortexModuli f m hs) :
    (vortexModuliChartedSpace (hs := hs) hk).chartAt q q = 0 :=
  (exists_openPartialHomeomorph_vortexModuli_apply_eq_zero hk q).choose_spec.2

/-! ### The divisor of a vortex orbit -/

/-- **The zero divisor of a vortex orbit.** For `k ≥ 4`, the point of `Sym ℂ m` listing the zeros
of the section of any vortex in an orbit of the vortex moduli space in `A_m^k / G_(k+1)`, with
multiplicity. It does not depend on the vortex (`vortexModuliDivisor_mk`). -/
def vortexModuliDivisor (hk : 3 < k) (q : vortexModuli f m hs) : Sym ℂ m :=
  sobolevVortexDivisor
    ⟨_, toFramedFieldSpace_mem_sobolevVortices hk (mem_vortexModuli_iff.1 q.property).choose_spec.1⟩

/-- The divisor of the orbit of a continuous vortex of `A_m^k` is the zero divisor of that
vortex. -/
@[simp]
theorem vortexModuliDivisor_mk (hk : 3 < k) {x : SobolevFieldSpace f m k}
    (hx : ∀ z, equation x z = 0) :
    vortexModuliDivisor hk (⟨Quotient.mk _ x, mk_mem_vortexModuli hx⟩ : vortexModuli f m hs) =
      sobolevVortexDivisor ⟨_, toFramedFieldSpace_mem_sobolevVortices hk hx⟩ := by
  have hq := mem_vortexModuli_iff.1 (mk_mem_vortexModuli (hs := hs) hx)
  obtain ⟨u, hu, hux⟩ := orbitRel_iff.1 (Quotient.exact hq.choose_spec.2.symm)
  exact (sobolevVortexDivisor_eq_sobolevVortexDivisor_iff (hs := hs)).2
    ⟨⟨u, hu⟩, Subtype.ext (by rw [coe_sobolevGaugeGroup_smul]; exact hux)⟩

/-- **The divisor identifies the vortex moduli with `Sym ℂ m`** (Taubes). For `k ≥ 4`, the zero
divisor is a bijection from the vortex moduli space in `A_m^k / G_(k+1)` onto the effective
divisors of degree `m`, repeated points included. -/
theorem vortexModuliDivisor_bijective (hk : 3 < k) :
    Function.Bijective (vortexModuliDivisor (f := f) (m := m) (hs := hs) hk) := by
  refine ⟨?_, fun D ↦ ?_⟩
  · rintro ⟨_, hq⟩ ⟨_, hq'⟩ h
    obtain ⟨x, hx, rfl⟩ := mem_vortexModuli_iff.1 hq
    obtain ⟨y, hy, rfl⟩ := mem_vortexModuli_iff.1 hq'
    rw [vortexModuliDivisor_mk hk hx, vortexModuliDivisor_mk hk hy,
      sobolevVortexDivisor_eq_sobolevVortexDivisor_iff (hs := hs)] at h
    obtain ⟨u, hu⟩ := h
    refine Subtype.ext (Quotient.sound (orbitRel_iff.2 ⟨u, u.property, ?_⟩)).symm
    simpa only [coe_sobolevGaugeGroup_smul, coe_toFramedFieldSpace] using congrArg Subtype.val hu
  · obtain ⟨x, hxD, hxc, -⟩ := exists_contDiff_sobolevVortexDivisor_eq (f := f) (k := k) D
    have hx := (mem_sobolevVortices.1 x.property).2
    let y : SobolevFieldSpace f m k := ⟨_, x.val.property, hxc.continuous⟩
    exact ⟨⟨Quotient.mk _ y, mk_mem_vortexModuli hx⟩, (vortexModuliDivisor_mk hk hx).trans hxD⟩

/-- **The divisor of a vortex orbit depends continuously on the orbit.** For `k ≥ 4`, the zero
divisor is continuous on the vortex moduli space in `A_m^k / G_(k+1)`, with the topology of
`Sym ℂ m` as a quotient of `ℂᵐ`. -/
theorem continuous_vortexModuliDivisor (hk : 3 < k) :
    Continuous (vortexModuliDivisor (f := f) (m := m) (hs := hs) hk) := by
  have hk' : (1 : ℝ) < k := by exact_mod_cast (Fact.out : 1 < k)
  have hπ := (MulAction.isOpenQuotientMap_quotientMk (Γ := SobolevTopologicalGaugeGroup hs)
    (T := SobolevFieldSpace f m k)).restrictPreimage (vortexModuli f m hs)
  have hvort (x : Quotient.mk _ ⁻¹' vortexModuli f m hs) : ∀ z, equation x.val z = 0 :=
    (mk_mem_vortexModuli_iff (by omega)).1 x.property
  -- Read through the open quotient map, the divisor is the divisor of the field.
  have hcomp : vortexModuliDivisor hk ∘ (vortexModuli f m hs).restrictPreimage (Quotient.mk _) =
      fun x ↦ sobolevVortexDivisor ⟨_, toFramedFieldSpace_mem_sobolevVortices hk (hvort x)⟩ :=
    funext fun x ↦ vortexModuliDivisor_mk hk (hvort x)
  rw [← hπ.continuous_comp_iff, hcomp, continuous_iff_continuousAt]
  exact fun x₀ ↦ tendsto_of_tendsto hk' continuous_subtypeVal.continuousAt
    (isZeroMultiplicity_sectionValue_sobolevVortexDivisor
      ⟨_, toFramedFieldSpace_mem_sobolevVortices hk (hvort x₀)⟩)
    (.of_forall fun x ↦ isZeroMultiplicity_sectionValue_sobolevVortexDivisor
      ⟨_, toFramedFieldSpace_mem_sobolevVortices hk (hvort x)⟩)

end SobolevFieldSpace

end TauCeti.Vortex
