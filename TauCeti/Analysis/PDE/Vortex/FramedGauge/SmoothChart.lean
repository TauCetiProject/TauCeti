/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge.OrbitChart
import TauCeti.Analysis.Fredholm.LevelSet.Smooth
import TauCeti.Analysis.PDE.Vortex.FramedGauge.SmoothAction

/-!
# Smoothly compatible charts of the moduli space of framed plane vortices

For an integer `k ≥ 2`, the Sobolev framed gauge group `G_(k+2)` acts on the continuous fields of
`A_m^(k+1) = x_m + H^(k+1)(ℂ; iT*ℂ ⊕ ℂ)` (`TauCeti.Vortex.SobolevFieldSpace`), and the orbits of
the vortices form the moduli space `TauCeti.Vortex.SobolevFieldSpace.vortexModuli`. At the orbit
of a vortex lying in every `A_m^j`, the Coulomb slice gives a chart of this space with values in
`ℝ^(2m)` (`TauCeti.Vortex.SobolevFieldSpace.exists_isOpen_openPartialHomeomorph_vortexModuli_eq`).
This file shows that such charts, suitably cut down, are smoothly compatible: the vortex moduli
space carries a smooth atlas modelled on `ℝ^(2m)`.

**Smooth charts.** A chart `e` of the vortex moduli space is *smooth in the field coordinates*
(`TauCeti.Vortex.SobolevFieldSpace.IsSmoothVortexModuliChart`) when, in the real coordinates of
`A_m^(k+1)` (`TauCeti.Vortex.SobolevFieldSpace.realSubRef`),

* its inverse lifts to a smooth family of vortices `σ v` with `e.symm v = [σ v]`, and
* near every vortex `y` whose orbit lies in the source of `e`, the map `z ↦ e [z]` on vortices is
  the restriction of a map smooth at the coordinates of `y`.

The transition `e' ∘ e.symm` between two such charts is then `v ↦ F (σ v)` near each point, a
composite of smooth maps
(`TauCeti.Vortex.SobolevFieldSpace.IsSmoothVortexModuliChart.contDiffOn_trans`).

**Existence.** At a vortex `x₀` lying in every `A_m^j`, the Coulomb slice chart of
`exists_isOpen_openPartialHomeomorph_vortexModuli_eq`, cut down to an open neighbourhood of the
orbit of `x₀`, is smooth in the field coordinates
(`TauCeti.Vortex.SobolevFieldSpace.exists_isSmoothVortexModuliChart`):

* on the zero set of the slice equation, the Coulomb slice chart is the restriction of an affine
  map, and its inverse is smooth near the base point, by the implicit function theorem
  (`TauCeti.contDiffAt_coe_levelSetChartModel_symm_of_mem`);
* a vortex `z` near a vortex `y` is carried into the Coulomb slice of `x₀` by a fixed gauge `g`
  with `g · y` in the slice, followed by the smooth Coulomb gauge `exp (i Φ)` at `x₀`
  (`TauCeti.Vortex.SobolevFieldSpace.exists_isOpen_contDiffOn_coulombPhase`); the gauge action is
  smooth in the real coordinates
  (`TauCeti.Vortex.SobolevFieldSpace.contDiff_realSubRef_expGauge_smul_ofRealSubRef`), so
  `z ↦ e [z]` is the chart of the slice applied to a smooth function of `z`.

## Main definitions

* `TauCeti.Vortex.SobolevFieldSpace.IsSmoothVortexModuliChart`: a chart of the vortex moduli space
  that is smooth in the real coordinates of the fields.

## Main results

* `TauCeti.Vortex.SobolevFieldSpace.IsSmoothVortexModuliChart.contDiffOn_trans`: the transition
  between two such charts is smooth.
* `TauCeti.Vortex.SobolevFieldSpace.exists_isSmoothVortexModuliChart`: at the orbit of every vortex
  lying in every `A_m^j` there is such a chart, sending that orbit to `0`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* S. K. Donaldson and P. B. Kronheimer, *The Geometry of Four-Manifolds*, Oxford University Press,
  1990, Section 4.2.
-/

public section

namespace TauCeti.Vortex

namespace SobolevFieldSpace

open BesselPotentialSpace Filter Topology SobolevTopologicalGaugeGroup
open scoped ContDiff

variable {f : ContDiffBump (0 : ℝ)} {m k : ℕ}

/-! ### The Coulomb slice chart in the ambient coordinates -/

section SliceChart

variable (hk : 2 ≤ k) (x₀ : SobolevFieldSpace f m ((k : ℝ) + 1))
  (hmem : ∀ j : ℕ, ⇑x₀ ∈ framedFieldSpace f m j) (hsol : ∀ z, equation x₀ z = 0)

/-- **The Coulomb slice chart in the ambient coordinates.** The Coulomb slice chart at `x₀` is the
restriction of an affine map: it reads a zero `p` of the slice equation through a continuous linear
map applied to `p - u₀`, where `u₀` are the real coordinates of `x₀`. Its inverse, included into
the real coordinates, is smooth at every point of its target whose image lies in a fixed open
neighbourhood of `u₀`: the neighbourhood on which the implicit function theorem keeps an
invertible derivative. -/
private theorem exists_coulombSliceChart_apply_eq_and_contDiffAt_symm :
    (∃ Ψ : (Fin 4 → realSubmodule ℂ (k.cast_add_one_pos (α := ℝ)).le) →L[ℝ] (Fin (2 * m) → ℝ),
      ∀ p, coulombSliceChart hk x₀ hmem hsol p = Ψ ((p : Fin 4 → _) - x₀.realSubRef _)) ∧
    ∃ A : Set (Fin 4 → realSubmodule ℂ (k.cast_add_one_pos (α := ℝ)).le), IsOpen A ∧
      x₀.realSubRef _ ∈ A ∧ ∀ v ∈ (coulombSliceChart hk x₀ hmem hsol).target,
        ((coulombSliceChart hk x₀ hmem hsol).symm v).val ∈ A →
        ContDiffAt ℝ ∞ (fun v ↦ ((coulombSliceChart hk x₀ hmem hsol).symm v).val) v := by
  have hhol (w : ℂ) : equation x₀ w 1 = 0 ∧ equation x₀ w 2 = 0 := by simp [hsol w]
  have hfin := finiteDimensional_ker_realSobolevGaugeFixedOperator hk x₀ hmem hhol
  have hn := finrank_ker_realSobolevGaugeFixedOperator hk x₀ hmem hhol
  have hker : (realSobolevGaugeFixedOperator f m hk (x₀.realSubRef _)).ker.ClosedComplemented :=
    .of_finiteDimensional _
  have hf := hasStrictFDerivAt_realSobolevSliceEquation hk x₀
  have hf' := LinearMap.range_eq_top.2 (realSobolevGaugeFixedOperator_surjective hk x₀ hmem hsol)
  rw [coulombSliceChart_eq hk x₀ hmem hsol hker hfin hn]
  refine ⟨⟨((realSobolevGaugeFixedOperator f m hk (x₀.realSubRef _)).kerModelEquiv hfin hn :
    _ →L[ℝ] (Fin (2 * m) → ℝ)).comp (Classical.choose hker), fun p ↦ ?_⟩,
    hf.implicitCoordSource hf' hker, hf.isOpen_implicitCoordSource hf' hker,
    hf.mem_implicitCoordSource hf' hker, fun v hv hA ↦ ?_⟩
  · rw [levelSetChartModel_apply, levelSetChart_apply]
    rfl
  · exact contDiffAt_coe_levelSetChartModel_symm_of_mem hf hf' hker hfin hn _ hv hA
      ((contDiff_realSobolevSliceEquation hk x₀).contDiffAt.of_le le_top)

end SliceChart

/-! ### Smooth charts of the vortex moduli -/

section IsSmoothVortexModuliChart

variable [Fact (1 < k)] {hs : 1 < (k : ℝ) + 1}

variable (f m hs) in
/-- **A chart of the vortex moduli space that is smooth in the field coordinates.** A chart `e`
of the vortex moduli space in `A_m^k / G_(k+1)`, with values in `ℝ^(2m)`, such that, in the real
coordinates `realSubRef` of the fields of `A_m^k`:

* its inverse lifts to vortices `σ v`, `e.symm v = [σ v]`, depending smoothly on `v` in the
  target of `e`;
* near every vortex `y` whose orbit lies in the source of `e`, there is a map `F` smooth at the
  coordinates of `y` with `e [z] = F z` for every vortex `z` near `y` whose orbit lies in the
  source of `e`.

The transition between two such charts is smooth (`IsSmoothVortexModuliChart.contDiffOn_trans`),
and there is one at the orbit of every smooth vortex (`exists_isSmoothVortexModuliChart`). -/
def IsSmoothVortexModuliChart
    (e : OpenPartialHomeomorph (vortexModuli f m hs) (Fin (2 * m) → ℝ)) : Prop :=
  (∃ σ : (Fin (2 * m) → ℝ) → SobolevFieldSpace f m k,
      ContDiffOn ℝ ∞ (fun v ↦ (σ v).realSubRef (Nat.cast_nonneg k)) e.target ∧
      ∀ v ∈ e.target, ∃ hv : ∀ z, equation (σ v) z = 0,
        e.symm v = ⟨Quotient.mk _ (σ v), mk_mem_vortexModuli hv⟩) ∧
    ∀ (y : SobolevFieldSpace f m k) (hy : ∀ z, equation y z = 0),
      (⟨Quotient.mk _ y, mk_mem_vortexModuli hy⟩ : vortexModuli f m hs) ∈ e.source →
      ∃ F : (Fin 4 → realSubmodule ℂ (Nat.cast_nonneg k : (0 : ℝ) ≤ k)) →
          Fin (2 * m) → ℝ,
        ContDiffAt ℝ ∞ F (y.realSubRef (Nat.cast_nonneg k)) ∧
        ∀ᶠ z : SobolevFieldSpace f m k in 𝓝 y, ∀ hz : ∀ w, equation z w = 0,
          (⟨Quotient.mk _ z, mk_mem_vortexModuli hz⟩ : vortexModuli f m hs) ∈ e.source →
            e ⟨Quotient.mk _ z, mk_mem_vortexModuli hz⟩ =
              F (z.realSubRef (Nat.cast_nonneg k))

/-- **The transition between two smooth charts of the vortex moduli is smooth.** -/
theorem IsSmoothVortexModuliChart.contDiffOn_trans
    {e e' : OpenPartialHomeomorph (vortexModuli f m hs) (Fin (2 * m) → ℝ)}
    (he : IsSmoothVortexModuliChart f m hs e) (he' : IsSmoothVortexModuliChart f m hs e') :
    ContDiffOn ℝ ∞ (e.symm.trans e') (e.symm.trans e').source := by
  obtain ⟨⟨σ, hσc, hσ⟩, -⟩ := he
  intro v hv
  have hvt : v ∈ e.target := hv.1
  obtain ⟨hσv, hev⟩ := hσ v hvt
  obtain ⟨F, hF, hFev⟩ := he'.2 (σ v) hσv (hev ▸ hv.2)
  have hσd : ContDiffAt ℝ ∞ (fun v ↦ (σ v).realSubRef (Nat.cast_nonneg k)) v :=
    hσc.contDiffAt (e.open_target.mem_nhds hvt)
  -- `σ` is continuous at `v`, being smooth in the real chart of `A_m^(k+1)`.
  have hσcont : ContinuousAt σ v := by
    have h := (realSubRefHomeomorph (f := f) (m := m) (by exact_mod_cast (Fact.out : 1 < k))
      (h := Nat.cast_nonneg k)).symm.continuous.continuousAt.comp hσd.continuousAt
    simpa only [Function.comp_def, coe_realSubRefHomeomorph_symm, ofRealSubRef_realSubRef] using h
  -- Near `v`, the transition is `F` applied to the coordinates of `σ`.
  have hev' : (e.symm.trans e') =ᶠ[𝓝 v] fun w ↦ F ((σ w).realSubRef (Nat.cast_nonneg k)) := by
    filter_upwards [hσcont.eventually hFev, (e.symm.trans e').open_source.mem_nhds hv]
      with w hw hws
    obtain ⟨hσw, hew⟩ := hσ w hws.1
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, hew]
    exact hw hσw (hew ▸ hws.2)
  exact ((hF.comp v hσd).congr_of_eventuallyEq hev').contDiffWithinAt

end IsSmoothVortexModuliChart

/-! ### Existence of smooth charts -/

variable [Fact (1 < k + 1)] {hs : 1 < ((k + 1 : ℕ) : ℝ) + 1}

/-- **The chart is smooth near a vortex.** Let `e` be a chart of the vortex moduli space that, on
vortices `y` of an open set `V` in the Coulomb slice of `x₀`, is a smooth function `G` of the
coordinates of `y`, and let `Φ` be the smooth Coulomb phase at `x₀` on an open set `U` of
coordinates. If a vortex `y` is carried by a gauge `g` to a field `y₀ ∈ V` in the Coulomb slice
with coordinates in `U`, then near `y`, `z ↦ e [z]` is `G` applied to the coordinates of
`exp (i Φ (g · z)) · g · z`, a smooth function of the coordinates of `z`. -/
private theorem exists_contDiffAt_eventually_eq_of_smul_mem_coulombSlice
    (x₀ : SobolevFieldSpace f m (k + 1 : ℕ)) {V : Set (SobolevFieldSpace f m (k + 1 : ℕ))}
    (hV : IsOpen V) (e : OpenPartialHomeomorph (vortexModuli f m hs) (Fin (2 * m) → ℝ))
    {G : (Fin 4 → realSubmodule ℂ (Nat.cast_nonneg (k + 1) : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ))) →
      Fin (2 * m) → ℝ} (hG : ContDiff ℝ ∞ G)
    (he : ∀ y ∈ V, y ∈ coulombSlice x₀ → ∀ hy : ∀ z, equation y z = 0,
      (⟨Quotient.mk _ y, mk_mem_vortexModuli hy⟩ : vortexModuli f m hs) ∈ e.source →
        e ⟨Quotient.mk _ y, mk_mem_vortexModuli hy⟩ = G (y.realSubRef (Nat.cast_nonneg (k + 1))))
    {U : Set (Fin 4 → realSubmodule ℂ (Nat.cast_nonneg (k + 1) : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ)))}
    (hU : IsOpen U) {Φ : (Fin 4 → realSubmodule ℂ (Nat.cast_nonneg (k + 1) :
      (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ))) → realSubmodule ℂ (zero_le_one.trans hs.le)}
    (hΦ : ContDiffOn ℝ ∞ Φ U)
    (hΦS : ∀ y : SobolevFieldSpace f m (k + 1 : ℕ), y.realSubRef (Nat.cast_nonneg (k + 1)) ∈ U →
      expGauge hs (Φ (y.realSubRef (Nat.cast_nonneg (k + 1)))) • y ∈ coulombSlice x₀)
    (hΦ0 : ∀ y : SobolevFieldSpace f m (k + 1 : ℕ), y.realSubRef (Nat.cast_nonneg (k + 1)) ∈ U →
      y ∈ coulombSlice x₀ → Φ (y.realSubRef (Nat.cast_nonneg (k + 1))) = 0)
    (hk : 2 ≤ k) {y y₀ : SobolevFieldSpace f m (k + 1 : ℕ)} (hy₀V : y₀ ∈ V)
    (hy₀S : y₀ ∈ coulombSlice x₀) (hy₀U : y₀.realSubRef (Nat.cast_nonneg (k + 1)) ∈ U)
    (g : SobolevTopologicalGaugeGroup hs) (hg : g • y = y₀) :
    ∃ F : (Fin 4 → realSubmodule ℂ (Nat.cast_nonneg (k + 1) : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ))) →
        Fin (2 * m) → ℝ,
      ContDiffAt ℝ ∞ F (y.realSubRef (Nat.cast_nonneg (k + 1))) ∧
      ∀ᶠ z : SobolevFieldSpace f m (k + 1 : ℕ) in 𝓝 y, ∀ hz : ∀ w, equation z w = 0,
        (⟨Quotient.mk _ z, mk_mem_vortexModuli hz⟩ : vortexModuli f m hs) ∈ e.source →
          e ⟨Quotient.mk _ z, mk_mem_vortexModuli hz⟩ =
            F (z.realSubRef (Nat.cast_nonneg (k + 1))) := by
  have hX : 1 < ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (Fact.out : 1 < k + 1)
  set ρ : SobolevFieldSpace f m (k + 1 : ℕ) → _ := realSubRef (Nat.cast_nonneg (k + 1))
  set ι := ofRealSubRef (f := f) (m := m) hX (h := Nat.cast_nonneg (k + 1))
  have hρ : Continuous ρ := continuous_realSubRef _
  have hι : Continuous ι := by
    simpa using
      (realSubRefHomeomorph (f := f) (m := m) hX (h := Nat.cast_nonneg (k + 1))).symm.continuous
  have hιρ (z) : ι (ρ z) = z := ofRealSubRef_realSubRef hX z
  -- The coordinates `w` of `g · z` and `τ` of `exp (i Φ (g · z)) · g · z`, as functions of the
  -- coordinates of `z`.
  set w := fun u ↦ ρ (g • ι u)
  set τ := fun u ↦ ρ (expGauge hs (Φ (w u)) • ι (w u))
  have hw : ContDiff ℝ ∞ w := contDiff_realSubRef_smul_ofRealSubRef g
  have hwy : w (ρ y) = ρ y₀ := by simp only [w, hιρ, hg]
  have hτ : ContDiffAt ℝ ∞ τ (ρ y) :=
    contDiff_realSubRef_expGauge_smul_ofRealSubRef.contDiffAt.comp _
      (((hΦ.contDiffAt (hU.mem_nhds (hwy ▸ hy₀U))).comp _ hw.contDiffAt).prodMk hw.contDiffAt)
  have hτy : τ (ρ y) = ρ y₀ := by
    simp only [τ, hwy, hιρ, hΦ0 y₀ hy₀U hy₀S, AddChar.map_zero_eq_one, one_smul]
  refine ⟨G ∘ τ, hG.contDiffAt.comp _ hτ, ?_⟩
  -- Near `y`, the coordinates of `g · z` stay in `U` and the field of `τ` stays in `V`.
  have hwU : ∀ᶠ z in 𝓝 y, w (ρ z) ∈ U :=
    (hw.continuous.comp hρ).continuousAt.preimage_mem_nhds
      (by rw [Function.comp_apply, hwy]; exact hU.mem_nhds hy₀U)
  have hτV : ∀ᶠ z in 𝓝 y, ι (τ (ρ z)) ∈ V :=
    (hι.continuousAt.comp (hτ.continuousAt.comp hρ.continuousAt)).preimage_mem_nhds
      (hV.mem_nhds (by simpa only [Function.comp_apply, hτy, hιρ] using hy₀V))
  filter_upwards [hwU, hτV] with z hzU hzV hz hzs
  -- `t = exp (i Φ (g · z)) · g · z` is a vortex in `V ∩ coulombSlice x₀` in the orbit of `z`.
  set t := ι (τ (ρ z))
  have ht : t = (expGauge hs (Φ (w (ρ z))) * g) • z := by
    simp only [t, τ, w, hιρ, mul_smul]
  have hwz : w (ρ z) = ρ (g • z) := by simp only [w, hιρ]
  have htS : t ∈ coulombSlice x₀ := by
    rw [ht, mul_smul, hwz]
    exact hΦS (g • z) (hwz ▸ hzU)
  have htsol : ∀ w, equation t w = 0 := fun w ↦ by
    rw [ht]; exact (equation_smul_eq_zero_iff (by omega) _ z w).2 (hz w)
  have hq : (⟨Quotient.mk _ z, mk_mem_vortexModuli hz⟩ : vortexModuli f m hs) =
      ⟨Quotient.mk _ t, mk_mem_vortexModuli htsol⟩ :=
    Subtype.ext (Quotient.sound
      ⟨(expGauge hs (Φ (w (ρ z))) * g)⁻¹, by simp only [ht, inv_smul_smul]⟩)
  rw [hq] at hzs ⊢
  rw [he t hzV htS htsol hzs, Function.comp_apply]
  exact congrArg G (realSubRef_ofRealSubRef hX _)

/-- **The Coulomb slice chart, cut down to an open set of representatives.** Let `x₀` be a
continuous vortex of `A_m^(k+1)`, `k ≥ 2`, lying in `A_m^j` for every `j`, and `B` an open set of
fields containing `x₀`. There are an open set `W ⊆ B` and a chart `e` of the vortex moduli space,
sending the orbit of `x₀` to `0`, such that every orbit of the source of `e` is the orbit of a
vortex of `W` in the Coulomb slice of `x₀`, and on the orbit of such a vortex `y`, `e` is the
Coulomb slice chart `c` at the coordinates `p` of `y`. -/
private theorem exists_vortexModuliChart_forall_mem (hk : 2 ≤ k)
    (x₀ : SobolevFieldSpace f m (k + 1 : ℕ)) (hmem : ∀ j : ℕ, ⇑x₀ ∈ framedFieldSpace f m j)
    (hsol : ∀ z, equation x₀ z = 0) {B : Set (SobolevFieldSpace f m (k + 1 : ℕ))} (hB : IsOpen B)
    (hx₀B : x₀ ∈ B) :
    ∃ W ⊆ B, IsOpen W ∧ ∃ e : OpenPartialHomeomorph (vortexModuli f m hs) (Fin (2 * m) → ℝ),
      (⟨Quotient.mk _ x₀, mk_mem_vortexModuli hsol⟩ : vortexModuli f m hs) ∈ e.source ∧
      e ⟨Quotient.mk _ x₀, mk_mem_vortexModuli hsol⟩ = 0 ∧
      (∀ q ∈ e.source, ∃ y ∈ W, y ∈ coulombSlice x₀ ∧ ∃ hy : ∀ z, equation y z = 0,
        q = ⟨Quotient.mk _ y, mk_mem_vortexModuli hy⟩) ∧
      ∀ y ∈ W, ∀ (hS : y ∈ coulombSlice x₀) (hy : ∀ z, equation y z = 0),
        let p : {u | realSobolevSliceEquation f m hk (congrOrder (Nat.cast_succ k) x₀) u = 0} :=
          ⟨_, (realSobolevSliceEquation_realSubRef_congrOrder_eq_zero_iff hk x₀ y).2 ⟨hS, hy⟩⟩
        let c := coulombSliceChart hk (congrOrder (Nat.cast_succ k) x₀)
          (coe_congrOrder _ x₀ ▸ hmem) (coe_congrOrder _ x₀ ▸ hsol)
        (⟨Quotient.mk _ y, mk_mem_vortexModuli hy⟩ : vortexModuli f m hs) ∈ e.source →
          p ∈ c.source ∧ e ⟨Quotient.mk _ y, mk_mem_vortexModuli hy⟩ = c p := by
  have hs' : 1 < (k : ℝ) + 1 := by linarith [(Nat.ofNat_le_cast.2 hk : (2 : ℝ) ≤ k)]
  obtain ⟨V, hV, hx₀V, e, hsrc, heq⟩ :=
    exists_isOpen_openPartialHomeomorph_vortexModuli_eq (hs := hs) hk x₀ hmem hsol
  set c := coulombSliceChart hk (congrOrder (Nat.cast_succ k) x₀) (coe_congrOrder _ x₀ ▸ hmem)
    (coe_congrOrder _ x₀ ▸ hsol)
  -- The coordinates `φ` of the slice equation, and the chart `e'` of the orbits whose slice
  -- representative lies in `V ∩ B`.
  set φ := (congrOrder (f := f) (m := m) (s := ((k + 1 : ℕ) : ℝ)) (Nat.cast_succ k)).trans
    (realSubRefHomeomorph hs' (h := (k.cast_add_one_pos (α := ℝ)).le))
  have hφ (y) : φ y = (congrOrder (Nat.cast_succ k) y).realSubRef _ := by simp [φ]
  set T := c '' (c.source ∩ {p | φ.symm p.val ∈ V ∩ B})
  have hT : IsOpen T := (c.isOpen_image_iff_of_subset_source Set.inter_subset_left).2
    (c.open_source.inter ((hV.inter hB).preimage (φ.symm.continuous.comp continuous_subtypeVal)))
  refine ⟨V ∩ B, Set.inter_subset_right, hV.inter hB,
    e.restrOpen (e.source ∩ e ⁻¹' T) (e.isOpen_inter_preimage hT), ?_, ?_, fun q hq ↦ ?_,
    fun y hy hS hsol' hys ↦ ?_⟩
  · have h := heq x₀ hx₀V (self_mem_coulombSlice x₀) hsol
    dsimp only at h
    have hp₀ := mem_coulombSliceChart_source hk (congrOrder (Nat.cast_succ k) x₀)
      (coe_congrOrder _ x₀ ▸ hmem) (coe_congrOrder _ x₀ ▸ hsol)
    refine ⟨h.1.2 hp₀, h.1.2 hp₀, _, ⟨hp₀, ?_⟩, h.2.symm⟩
    have hx₀VB : φ.symm (φ x₀) ∈ V ∩ B := by rw [φ.symm_apply_apply]; exact ⟨hx₀V, hx₀B⟩
    rwa [hφ] at hx₀VB
  · have h := heq x₀ hx₀V (self_mem_coulombSlice x₀) hsol
    dsimp only at h
    rw [OpenPartialHomeomorph.coe_restrOpen, h.2]
    exact coulombSliceChart_apply_self hk _ _ _
  · rw [OpenPartialHomeomorph.restrOpen_source] at hq
    obtain ⟨y, ⟨hyV, hyS⟩, hyq⟩ := hsrc q hq.1
    have hy : ∀ z, equation y z = 0 := (mk_mem_vortexModuli_iff (by omega)).1 (hyq ▸ q.property)
    obtain rfl : q = ⟨Quotient.mk _ y, mk_mem_vortexModuli hy⟩ := Subtype.ext hyq.symm
    have h := heq y hyV hyS hy
    dsimp only at h
    -- The representative is the field of the point of `T` that `e` sends the orbit to.
    obtain ⟨p, ⟨hpc, hpB⟩, hpe⟩ := hq.2.2
    obtain rfl := c.injOn hpc (h.1.1 hq.1) (hpe.trans h.2)
    have hyB : φ.symm (φ y) ∈ V ∩ B := by rw [hφ]; exact hpB
    rw [φ.symm_apply_apply] at hyB
    exact ⟨y, hyB, hyS, hy, rfl⟩
  · have h := heq y hy.1 hS hsol'
    dsimp only at h
    exact ⟨h.1.1 hys.1, h.2⟩

/-- **Smooth charts of the vortex moduli.** Let `x₀` be a continuous vortex of `A_m^(k+1)`,
`k ≥ 2`, lying in `A_m^j` for every `j`. Then the vortex moduli space in `A_m^(k+1) / G_(k+2)` has a
chart at the orbit of `x₀` that is smooth in the field coordinates, sending that orbit to `0`. It
is the Coulomb slice chart at `x₀` of `exists_isOpen_openPartialHomeomorph_vortexModuli_eq`, cut
down to the orbits whose representative in the slice has coordinates where the inverse slice chart
and the Coulomb gauge at `x₀` are smooth. -/
theorem exists_isSmoothVortexModuliChart (hk : 2 ≤ k) (x₀ : SobolevFieldSpace f m (k + 1 : ℕ))
    (hmem : ∀ j : ℕ, ⇑x₀ ∈ framedFieldSpace f m j) (hsol : ∀ z, equation x₀ z = 0) :
    ∃ e : OpenPartialHomeomorph (vortexModuli f m hs) (Fin (2 * m) → ℝ),
      IsSmoothVortexModuliChart f m hs e ∧
      (⟨Quotient.mk _ x₀, mk_mem_vortexModuli hsol⟩ : vortexModuli f m hs) ∈ e.source ∧
      e ⟨Quotient.mk _ x₀, mk_mem_vortexModuli hsol⟩ = 0 := by
  have hs' : 1 < (k : ℝ) + 1 := by linarith [(Nat.ofNat_le_cast.2 hk : (2 : ℝ) ≤ k)]
  have hmem' : ∀ j : ℕ, ⇑(congrOrder (Nat.cast_succ k) x₀) ∈ framedFieldSpace f m j :=
    coe_congrOrder _ x₀ ▸ hmem
  have hsol' : ∀ z, equation (congrOrder (Nat.cast_succ k) x₀) z = 0 := coe_congrOrder _ x₀ ▸ hsol
  set c := coulombSliceChart hk (congrOrder (Nat.cast_succ k) x₀) hmem' hsol'
  obtain ⟨⟨Ψ, hΨ⟩, A, hA, hx₀A, hAc⟩ :=
    exists_coulombSliceChart_apply_eq_and_contDiffAt_symm hk _ hmem' hsol'
  obtain ⟨U, hU, hx₀U, Φ, hΦ, -, hΦS, hΦ0⟩ :=
    exists_isOpen_contDiffOn_coulombPhase hs (by omega) x₀
  -- The real coordinates `ρ` of `A_m^(k+1)`, the coordinates `φ` of the slice equation at the
  -- order `↑k + 1`, and their comparison `κ`.
  set ρ : SobolevFieldSpace f m (k + 1 : ℕ) → _ := realSubRef (Nat.cast_nonneg (k + 1))
  set φ := (congrOrder (f := f) (m := m) (s := ((k + 1 : ℕ) : ℝ)) (Nat.cast_succ k)).trans
    (realSubRefHomeomorph hs' (h := (k.cast_add_one_pos (α := ℝ)).le))
  set κ := ContinuousLinearEquiv.piCongrRight fun _ : Fin 4 ↦ realSubmoduleCongr ℂ
    (Nat.cast_succ k) (Nat.cast_nonneg (k + 1)) (k.cast_add_one_pos (α := ℝ)).le
  have hφ (y) : φ y = (congrOrder (Nat.cast_succ k) y).realSubRef _ := by simp [φ]
  have hφκ (y) : φ y = κ (ρ y) := (hφ y).trans (funext fun j ↦ realSubRef_congrOrder _ _ _ y j)
  have hρφ (u) : (φ.symm u).realSubRef (Nat.cast_nonneg (k + 1)) = κ.symm u :=
    κ.injective ((hφκ (φ.symm u)).symm.trans (by rw [φ.apply_symm_apply, κ.apply_symm_apply]))
  obtain ⟨W, hWB, hW, e, hx₀e, he0, hsrc, heq⟩ :=
    exists_vortexModuliChart_forall_mem (hs := hs) hk x₀ hmem hsol (B := φ ⁻¹' A ∩ ρ ⁻¹' U)
      ((hA.preimage φ.continuous).inter (hU.preimage (continuous_realSubRef _)))
      ⟨by rw [Set.mem_preimage, hφ]; exact hx₀A, hx₀U⟩
  -- A point `v` of the target of `e` is the orbit of a vortex `y ∈ W`, with `c.symm v = φ y`.
  have hvy : ∀ v ∈ e.target, ∃ y ∈ W, ∃ hy : ∀ z, equation y z = 0,
      e.symm v = ⟨Quotient.mk _ y, mk_mem_vortexModuli hy⟩ ∧ v ∈ c.target ∧
        (c.symm v : Fin 4 → _) = φ y := by
    intro v hv
    obtain ⟨y, hyW, hyS, hy, hqy⟩ := hsrc _ (e.map_target hv)
    have h := heq y hyW hyS hy (hqy ▸ e.map_target hv)
    have hcv : c _ = v := h.2.symm.trans (hqy ▸ e.right_inv hv)
    refine ⟨y, hyW, hy, hqy, hcv ▸ c.map_source h.1, ?_⟩
    rw [← hcv, c.left_inv h.1, hφ]
  refine ⟨e, ⟨⟨fun v ↦ φ.symm (c.symm v), fun v hv ↦ ?_, fun v hv ↦ ?_⟩, fun y hy hys ↦ ?_⟩,
    hx₀e, he0⟩
  · -- The lift of the inverse is smooth: in coordinates it is the inverse slice chart.
    obtain ⟨y, hyW, -, -, hvc, hcv⟩ := hvy v hv
    exact (κ.symm.contDiff.contDiffAt.comp v
      (hAc v hvc (hcv ▸ (hWB hyW).1))).contDiffWithinAt.congr (fun w _ ↦ hρφ _) (hρφ _)
  · obtain ⟨y, -, hy, hqy, -, hcv⟩ := hvy v hv
    obtain rfl : φ.symm (c.symm v : Fin 4 → _) = y := by rw [hcv, φ.symm_apply_apply]
    exact ⟨hy, hqy⟩
  · -- Near a vortex `y`, the chart is smooth: carry `y` into the slice by a gauge.
    obtain ⟨y₀, hy₀W, hy₀S, hy₀, hq⟩ := hsrc _ hys
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1
      (MulAction.orbitRel_apply.1 (Quotient.exact (congrArg Subtype.val hq).symm))
    refine exists_contDiffAt_eventually_eq_of_smul_mem_coulombSlice x₀ hW e
      (G := fun u ↦ Ψ (κ u - φ x₀)) (Ψ.contDiff.comp (κ.contDiff.sub contDiff_const))
      (fun y' hy'W hy'S hy' hy's ↦ ?_) hU hΦ hΦS hΦ0 hk hy₀W hy₀S (hWB hy₀W).2 g hg
    have h := heq y' hy'W hy'S hy' hy's
    rw [h.2, hΨ, ← hφκ, hφ, hφ]

end SobolevFieldSpace

end TauCeti.Vortex
