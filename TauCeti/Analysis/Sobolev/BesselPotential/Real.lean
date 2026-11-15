/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Basic
public import TauCeti.Analysis.Distribution.Sobolev
public import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
import Mathlib.MeasureTheory.Measure.OpenPos
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding

/-!
# Real elements of Bessel-potential spaces

For an order `s ≥ 0` every element `u` of the complex Bessel-potential space `H^s(E) = H^{s,2}(E)`
is an `L²` function (`BesselPotentialSpace.toTemperedDistribution_toLp_inclusion`). Those whose
`L²` function is real almost everywhere form a real subspace
`BesselPotentialSpace.realSubmodule`, which is closed, hence a real Hilbert space with the norm of
`H^s(E)`. This is the real Sobolev space `H^s(E; ℝ)` with the norm of `H^s(E)`, the natural model
space for real fields such as the phases of gauge transformations. The real submodule
`TemperedDistribution.realSobolevSubmodule` of `L²(E; ℝ)` has the same elements, read as real `L²`
functions, but carries the `L²` norm rather than the `H^s` norm.

When `s > dim E / 2`, the Sobolev embedding gives every element of `H^s(E)` a continuous
representative, and for a real element it is real valued. The real continuous representative
`BesselPotentialSpace.realContinuousRep` is a real linear map from `realSubmodule` to `C(E, ℝ)`. Its
values are exactly the continuous functions of `TemperedDistribution.realSobolevFunctions E s 2`
(`BesselPotentialSpace.realContinuousRep_mem_realSobolevFunctions`,
`BesselPotentialSpace.exists_realContinuousRep_eq`), and it is injective, so `realSubmodule`
identifies the continuous real `H^s` functions with a real Hilbert space.

## Main declarations

* `BesselPotentialSpace.realSubmodule`: the real elements of `H^s(E)`, `s ≥ 0`;
  `BesselPotentialSpace.isClosed_realSubmodule`: they form a closed subspace.
* `BesselPotentialSpace.realContinuousRep`: for `s > dim E / 2`, the continuous real
  representative of a real element, as a real linear map to `C(E, ℝ)`.
* `BesselPotentialSpace.coeFn_toLp_inclusion_ae_eq_realContinuousRep` and
  `BesselPotentialSpace.realContinuousRep_eq_of_ae_eq`: it represents the element, and is the only
  continuous function that does.
* `BesselPotentialSpace.exists_realContinuousRep_eq`: every continuous function of
  `realSobolevFunctions E s 2` is the representative of a real element.

## References

* L. Grafakos, *Modern Fourier Analysis*, 3rd ed., Graduate Texts in Mathematics 250, Springer,
  2014, Section 1.3 (Sobolev spaces and the Sobolev embedding theorem).
-/

public section

noncomputable section

open MeasureTheory Module TemperedDistribution
open scoped BesselPotentialSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {s : ℝ}

namespace BesselPotentialSpace

/-- **The real elements of `H^s(E)`**, `s ≥ 0`: the elements whose `L²` function is real valued
almost everywhere. -/
def realSubmodule (h : 0 ≤ s) : Submodule ℝ H^{s}(E) where
  carrier := {u | ∀ᵐ x ∂volume, ((inclusion h u).toLp x).im = 0}
  add_mem' {u v} hu hv := by
    simp only [Set.mem_ofPred_eq] at hu hv ⊢
    filter_upwards [coeFn_toLp_inclusion_add h u v, hu, hv] with x hx hux hvx
    rw [hx, Pi.add_apply, Complex.add_im, hux, hvx, add_zero]
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, map_zero, toLp_zero]
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure E)] with x hx
    rw [hx, Pi.zero_apply, Complex.zero_im]
  smul_mem' c u hu := by
    simp only [Set.mem_ofPred_eq, ← Complex.coe_smul] at hu ⊢
    filter_upwards [coeFn_toLp_inclusion_smul h (c : ℂ) u, hu] with x hx hux
    rw [hx, Pi.smul_apply, smul_eq_mul, Complex.im_ofReal_mul, hux, mul_zero]

/-- Membership in `realSubmodule`: the `L²` function is real almost everywhere. -/
theorem mem_realSubmodule {h : 0 ≤ s} {u : H^{s}(E)} :
    u ∈ realSubmodule h ↔ ∀ᵐ x ∂volume, ((inclusion h u).toLp x).im = 0 :=
  Iff.rfl

/-- The real elements of `H^s(E)` form a closed subspace. -/
theorem isClosed_realSubmodule (h : 0 ≤ s) :
    IsClosed (realSubmodule (E := E) h : Set H^{s}(E)) := by
  -- It is the zero set of `u ↦ Im u`, a continuous map from `H^s(E)` to `L²(E; ℝ)`.
  have hc : Continuous fun u : H^{s}(E) ↦
      Complex.imCLM.compLpL 2 (volume : Measure E) (inclusion h u).toLp := by
    simpa only [Function.comp_def, toLpₗᵢ_apply] using
      (Complex.imCLM.compLpL 2 (volume : Measure E)).continuous.comp
        ((toLpₗᵢ E ℂ 0 2).continuous.comp (inclusion h).continuous)
  convert (isClosed_singleton (x := (0 : Lp ℝ 2 (volume : Measure E)))).preimage hc using 1
  ext u
  simp only [SetLike.mem_coe, mem_realSubmodule, Set.mem_preimage, Set.mem_singleton_iff,
    Lp.eq_zero_iff_ae_eq_zero]
  refine Filter.eventually_congr ?_
  filter_upwards [Complex.imCLM.coeFn_compLpL (inclusion h u).toLp] with x hx
  rw [hx, Complex.imCLM_apply, Pi.zero_apply]

instance (h : 0 ≤ s) : CompleteSpace (realSubmodule (E := E) h) :=
  (isClosed_realSubmodule h).completeSpace_coe

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- An order `s > dim E / 2` is nonnegative. -/
theorem nonneg_of_finrank_lt_two_mul (hs : finrank ℝ E < 2 * s) : 0 ≤ s := by
  have : (0 : ℝ) ≤ finrank ℝ E := Nat.cast_nonneg _
  linarith

/-- A real element of `H^s(E)`, `s > dim E / 2`, agrees almost everywhere with a continuous real
function. -/
private theorem exists_continuous_ae_eq (hs : finrank ℝ E < 2 * s)
    (u : realSubmodule (E := E) (nonneg_of_finrank_lt_two_mul hs)) :
    ∃ g : E → ℝ, Continuous g ∧
      (inclusion (nonneg_of_finrank_lt_two_mul hs) (u : H^{s}(E))).toLp =ᵐ[volume]
        fun x ↦ (g x : ℂ) := by
  obtain ⟨g, hg⟩ := (memSobolev_toLp_inclusion (nonneg_of_finrank_lt_two_mul hs)
    (u : H^{s}(E))).exists_zeroAtInftyContinuousMap_ae_eq hs
  -- The imaginary part of the continuous representative vanishes almost everywhere, hence
  -- everywhere.
  have him : (fun x ↦ (g x).im) = fun _ ↦ (0 : ℝ) :=
    (Continuous.ae_eq_iff_eq volume (Complex.continuous_im.comp g.continuous)
      continuous_const).1 <| by
        filter_upwards [hg, u.2] with x hx hux
        have hgx : (g x).im = 0 := by rw [← hx, hux]
        simpa using hgx
  refine ⟨fun x ↦ (g x).re, Complex.continuous_re.comp g.continuous, ?_⟩
  filter_upwards [hg] with x hx
  rw [hx]
  exact Complex.ext rfl (by simpa using congrFun him x)

/-- Two continuous functions representing the same `L²` class are equal. -/
private theorem eq_of_ae_eq {f : Lp ℂ 2 (volume : Measure E)} {g g' : E → ℝ} (hg : Continuous g)
    (hg' : Continuous g') (hfg : f =ᵐ[volume] fun x ↦ (g x : ℂ))
    (hfg' : f =ᵐ[volume] fun x ↦ (g' x : ℂ)) : g = g' :=
  (Continuous.ae_eq_iff_eq volume hg hg').1 <| by
    filter_upwards [hfg, hfg'] with x hx hx'
    exact Complex.ofReal_injective (hx.symm.trans hx')

/-- **The continuous real representative** of a real element of `H^s(E)`, `s > dim E / 2`, as a
real linear map `realSubmodule → C(E, ℝ)`. -/
def realContinuousRep (hs : finrank ℝ E < 2 * s) :
    realSubmodule (E := E) (nonneg_of_finrank_lt_two_mul hs) →ₗ[ℝ] C(E, ℝ) where
  toFun u := ⟨(exists_continuous_ae_eq hs u).choose, (exists_continuous_ae_eq hs u).choose_spec.1⟩
  map_add' u v := by
    have h := nonneg_of_finrank_lt_two_mul hs
    obtain ⟨-, hu⟩ := (exists_continuous_ae_eq hs u).choose_spec
    obtain ⟨-, hv⟩ := (exists_continuous_ae_eq hs v).choose_spec
    obtain ⟨huv₀, huv⟩ := (exists_continuous_ae_eq hs (u + v)).choose_spec
    refine DFunLike.coe_injective (eq_of_ae_eq huv₀ (ContinuousMap.continuous _) huv ?_)
    filter_upwards [coeFn_toLp_inclusion_add h (u : H^{s}(E)) v, hu, hv] with x hx hux hvx
    rw [Submodule.coe_add, hx, Pi.add_apply, hux, hvx]
    simp
  map_smul' c u := by
    have h := nonneg_of_finrank_lt_two_mul hs
    obtain ⟨-, hu⟩ := (exists_continuous_ae_eq hs u).choose_spec
    obtain ⟨hcu₀, hcu⟩ := (exists_continuous_ae_eq hs (c • u)).choose_spec
    refine DFunLike.coe_injective (eq_of_ae_eq hcu₀ (ContinuousMap.continuous _) hcu ?_)
    filter_upwards [coeFn_toLp_inclusion_smul h (c : ℂ) (u : H^{s}(E)), hu] with x hx hux
    rw [Submodule.coe_smul, ← Complex.coe_smul, hx, Pi.smul_apply, hux]
    simp

/-- The continuous real representative of `u` represents `u` almost everywhere. -/
theorem coeFn_toLp_inclusion_ae_eq_realContinuousRep (hs : finrank ℝ E < 2 * s)
    (u : realSubmodule (E := E) (nonneg_of_finrank_lt_two_mul hs)) {h : 0 ≤ s} :
    (inclusion h (u : H^{s}(E))).toLp =ᵐ[volume] fun x ↦ (realContinuousRep hs u x : ℂ) :=
  (exists_continuous_ae_eq hs u).choose_spec.2

/-- The continuous real representative is the only continuous function representing `u`. -/
theorem realContinuousRep_eq_of_ae_eq (hs : finrank ℝ E < 2 * s)
    {u : realSubmodule (E := E) (nonneg_of_finrank_lt_two_mul hs)} {h : 0 ≤ s} {g : E → ℝ}
    (hg : Continuous g)
    (hug : (inclusion h (u : H^{s}(E))).toLp =ᵐ[volume] fun x ↦ (g x : ℂ)) :
    ⇑(realContinuousRep hs u) = g :=
  eq_of_ae_eq (realContinuousRep hs u).continuous hg
    (coeFn_toLp_inclusion_ae_eq_realContinuousRep hs u) hug

/-- The continuous real representative is injective. -/
theorem realContinuousRep_injective (hs : finrank ℝ E < 2 * s) :
    Function.Injective (realContinuousRep (E := E) hs) := by
  intro u v huv
  have h := nonneg_of_finrank_lt_two_mul hs
  refine Subtype.ext (toLp_inclusion_injective h (Lp.ext ?_))
  filter_upwards [coeFn_toLp_inclusion_ae_eq_realContinuousRep hs u (h := h),
    coeFn_toLp_inclusion_ae_eq_realContinuousRep hs v (h := h)] with x hx hx'
  rw [hx, hx', huv]

/-- The continuous real representative of a real element of `H^s(E)` is a real `H^s` function. -/
theorem realContinuousRep_mem_realSobolevFunctions (hs : finrank ℝ E < 2 * s)
    (u : realSubmodule (E := E) (nonneg_of_finrank_lt_two_mul hs)) :
    ⇑(realContinuousRep hs u) ∈ realSobolevFunctions E s 2 :=
  mem_realSobolevFunctions_of_ae_eq_ofReal
    (memSobolev_toLp_inclusion (nonneg_of_finrank_lt_two_mul hs) (u : H^{s}(E)))
    (coeFn_toLp_inclusion_ae_eq_realContinuousRep hs u)

/-- **Every continuous real `H^s` function is a continuous real representative**, for
`s > dim E / 2`. -/
theorem exists_realContinuousRep_eq (hs : finrank ℝ E < 2 * s) {g : E → ℝ} (hg : Continuous g)
    (hgs : g ∈ realSobolevFunctions E s 2) :
    ∃ u : realSubmodule (E := E) (nonneg_of_finrank_lt_two_mul hs),
      ⇑(realContinuousRep hs u) = g := by
  have h := nonneg_of_finrank_lt_two_mul hs
  obtain ⟨v, hvg, hvs⟩ := mem_realSobolevFunctions.1 hgs
  have hL := toLp_inclusion_toBesselPotentialSpace h hvs rfl
  have hae : (inclusion h hvs.toBesselPotentialSpace).toLp =ᵐ[volume] fun x ↦ (g x : ℂ) := by
    rw [hL]
    filter_upwards [Complex.ofRealCLM.coeFn_compLp (p := 2) (μ := volume) v, hvg] with x hx hx'
    rw [hx, Complex.ofRealCLM_apply, hx']
  have hmem : hvs.toBesselPotentialSpace ∈ realSubmodule h := by
    filter_upwards [hae] with x hx
    rw [hx, Complex.ofReal_im]
  exact ⟨⟨_, hmem⟩, realContinuousRep_eq_of_ae_eq hs hg hae⟩

end BesselPotentialSpace
