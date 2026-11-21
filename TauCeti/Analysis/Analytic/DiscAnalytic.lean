/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import TauCeti.RingTheory.PowerSeries.HasFPowerSeriesOnBall
public import TauCeti.RingTheory.PowerSeries.OpenDisc.Radius
public import TauCeti.Topology.MetricSpace.Ultra.EBall
import Mathlib.Analysis.Analytic.Uniqueness
import TauCeti.Analysis.Analytic.OfScalars
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.RingTheory.PowerSeries.OpenDisc.Eval

/-!
# Analytic functions on an open disc

Let `K` be a complete normed field, `a ∈ K` and `r ∈ ℝ≥0∞`. A function on the open disc
`D⁻(a, r) = Metric.eball a r` is *analytic on the disc* when it is given on the whole disc by a
single power series in `z - a` whose radius of convergence is at least `r`. These functions form
the `K`-subalgebra `TauCeti.discAnalytic K a r` of all functions `Metric.eball a r → K`; the radius
`r = ⊤` gives the entire functions.

This is stronger than local analyticity (`AnalyticOnNhd`): over a nonarchimedean field the open
disc is the disjoint union of smaller open discs, so a locally constant function that is not
constant, such as the indicator of a smaller disc, is locally analytic but, by the identity
principle below, not analytic on the disc. Analyticity on the whole disc is the
condition that makes primitives unique up to a single constant, which is what Coleman integration
needs on residue discs.

Over a complete ultrametric field every point `b` of the disc is a centre of it, and the Taylor
translate of the series to `b` converges on the whole disc. Hence the subalgebra does not depend
on the chosen centre, restriction to a smaller disc about an interior point preserves it, and a
function analytic on the disc that vanishes near one point vanishes everywhere. Over a nontrivially
normed field and for `0 < r`, membership is exactly Mathlib's `HasFPowerSeriesOnBall` on the ball
and the series is unique; derivatives of functions analytic on the disc are again analytic on the
disc.

## Main definitions

* `TauCeti.discAnalytic K a r`: the subalgebra of functions on `Metric.eball a r` given by one
  power series in `z - a` of radius at least `r`.
* `TauCeti.discAnalytic.series f`: a power series in `z - a` representing `f`, its coefficient
  sequence at the centre `a`.

## Main results

* `TauCeti.mem_discAnalytic_iff`: the defining property; `TauCeti.evalAt_sub_mem_discAnalytic`
  and `PowerSeries.IsRestricted.evalAt_sub_mem_discAnalytic`: series of radius at least `r`, in
  particular series restricted at a radius at least `r`, define elements.
* `TauCeti.domRestrict_mem_discAnalytic_iff`: for `0 < r`, the restriction of `F : K → K` to the
  disc is analytic on the disc exactly when `F` has a power series on the ball
  (`HasFPowerSeriesOnBall`).
* `TauCeti.discAnalytic.series_eq` and `TauCeti.existsUnique_series_of_mem_discAnalytic`: for
  `0 < r`, the representing series is unique.
* `TauCeti.comp_inclusion_mem_discAnalytic` and `TauCeti.comp_inclusion_mem_discAnalytic_iff`:
  over an ultrametric field, restriction to the disc of radius `r' ≤ r` about an interior point
  preserves analyticity, and analyticity on the disc does not depend on the centre.
* `TauCeti.discAnalytic.eq_zero_of_eventuallyEq_zero` and `TauCeti.discAnalytic.eq_of_eqOn`: the
  identity principle on the disc.
* `TauCeti.domRestrict_deriv_mem_discAnalytic`: the derivative of a function analytic on the disc
  is analytic on the disc.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4.
* A. Besser, *Heidelberg lectures on Coleman integration* (2010), §1.3.1.
* A. Besser, *Coleman integration using the Tannakian formalism*, Math. Ann. 322 (2002), §5.
-/

public section

open Filter Metric PowerSeries
open scoped ENNReal Topology

namespace TauCeti

section NormedField

variable {K : Type*} [NormedField K]

variable [CompleteSpace K]

variable (K) in
/-- **Analytic functions on an open disc.** The functions on the open disc `Metric.eball a r`
given on the whole disc by one power series `g` in `z - a` whose radius of convergence is at least
`r`. For `r = ⊤` these are the entire functions. -/
def discAnalytic (a : K) (r : ℝ≥0∞) : Subalgebra K (eball a r → K) where
  carrier := {f | ∃ g : K⟦X⟧, r ≤ g.radius ∧ ∀ z : eball a r, f z = g.evalAt ((z : K) - a)}
  mul_mem' := by
    rintro f₁ f₂ ⟨g₁, hg₁, h₁⟩ ⟨g₂, hg₂, h₂⟩
    refine ⟨g₁ * g₂, (le_min hg₁ hg₂).trans (min_radius_le_radius_mul g₁ g₂), fun z ↦ ?_⟩
    obtain ⟨R₀, hR₀, hf₁, hf₂⟩ :=
      exists_onOpenDisc_of_le_radius hg₁ hg₂ (mem_eball_iff_eNorm.mp z.property)
    rw [Pi.mul_apply, h₁, h₂, hf₁.evalAt_mul hf₂ hR₀]
  add_mem' := by
    rintro f₁ f₂ ⟨g₁, hg₁, h₁⟩ ⟨g₂, hg₂, h₂⟩
    refine ⟨g₁ + g₂, (le_min hg₁ hg₂).trans (min_radius_le_radius_add g₁ g₂), fun z ↦ ?_⟩
    obtain ⟨R₀, hR₀, hf₁, hf₂⟩ :=
      exists_onOpenDisc_of_le_radius hg₁ hg₂ (mem_eball_iff_eNorm.mp z.property)
    rw [Pi.add_apply, h₁, h₂, hf₁.evalAt_add hf₂ hR₀]
  algebraMap_mem' c := ⟨C c, by simp [radius_eq_top_iff.mpr (isEntire_C c)], fun z ↦ by simp⟩

/-- A function on the open disc is analytic on the disc exactly when it is the value at `z - a` of
one power series whose radius is at least `r`. -/
theorem mem_discAnalytic_iff {a : K} {r : ℝ≥0∞} {f : eball a r → K} :
    f ∈ discAnalytic K a r ↔
      ∃ g : K⟦X⟧, r ≤ g.radius ∧ ∀ z : eball a r, f z = g.evalAt ((z : K) - a) :=
  Iff.rfl

/-- **The coefficient sequence at the centre.** A power series in `z - a` of radius at least `r`
representing a function analytic on the open disc of radius `r` about `a`. For `0 < r` it is the
unique such series (`TauCeti.discAnalytic.series_eq`). -/
noncomputable def discAnalytic.series {a : K} {r : ℝ≥0∞} (f : discAnalytic K a r) : K⟦X⟧ :=
  f.property.choose

/-- The representing series of a function analytic on the disc has radius at least `r`. -/
theorem discAnalytic.le_radius_series {a : K} {r : ℝ≥0∞} (f : discAnalytic K a r) :
    r ≤ (discAnalytic.series f).radius :=
  f.property.choose_spec.1

/-- A function analytic on the disc is the value at `z - a` of its representing series. -/
theorem discAnalytic.apply_eq_evalAt_series {a : K} {r : ℝ≥0∞} (f : discAnalytic K a r)
    (z : eball a r) : (f : eball a r → K) z = (discAnalytic.series f).evalAt ((z : K) - a) :=
  f.property.choose_spec.2 z

/-- A power series whose radius is at least `r` defines a function analytic on the open disc of
radius `r` about any centre. -/
theorem evalAt_sub_mem_discAnalytic {a : K} {r : ℝ≥0∞} {g : K⟦X⟧} (hg : r ≤ g.radius) :
    (fun z : eball a r ↦ g.evalAt ((z : K) - a)) ∈ discAnalytic K a r :=
  ⟨g, hg, fun _ ↦ rfl⟩

/-- A power series restricted at a radius `ρ` with `r ≤ |ρ|`, for instance an element of a Tate
or dagger algebra at a radius at least `r`, defines a function analytic on the open disc of radius
`r`. -/
theorem _root_.PowerSeries.IsRestricted.evalAt_sub_mem_discAnalytic {a : K} {r : ℝ≥0∞}
    {g : K⟦X⟧} {ρ : ℝ} (hg : g.IsRestricted ρ) (hr : r ≤ ‖ρ‖ₑ) :
    (fun z : eball a r ↦ g.evalAt ((z : K) - a)) ∈ discAnalytic K a r :=
  TauCeti.evalAt_sub_mem_discAnalytic (hr.trans (le_radius_of_isRestricted hg))

end NormedField

section Ultrametric

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

variable [CompleteSpace K]

/-- **Restriction to a smaller disc.** Over a complete ultrametric field, if `b` lies in the open
disc of radius `r` about `a` and `r' ≤ r`, then the restriction of a function analytic on
`Metric.eball a r` to `Metric.eball b r'` is analytic there. -/
theorem comp_inclusion_mem_discAnalytic {a b : K} {r r' : ℝ≥0∞} {f : eball a r → K}
    (hf : f ∈ discAnalytic K a r) (hb : b ∈ eball a r) (hr : r' ≤ r) :
    f ∘ Set.inclusion (IsUltrametricDist.eball_subset_eball_of_mem hb hr) ∈
      discAnalytic K b r' := by
  obtain ⟨g, hg, hfg⟩ := hf
  refine ⟨taylor (b - a) g, hr.trans (le_radius_taylor_sub hg hb), fun z ↦ ?_⟩
  rw [Function.comp_apply, hfg, Set.coe_inclusion, evalAt_sub_eq_evalAt_taylor_sub hg hb
    (IsUltrametricDist.eball_subset_eball_of_mem hb hr z.property)]

/-- **Independence of the centre.** Over a complete ultrametric field, every point `b` of the open
disc `Metric.eball a r` is a centre of it, and a function on the disc is analytic on the disc about
`a` exactly when it is analytic on the disc about `b`. -/
theorem comp_inclusion_mem_discAnalytic_iff {a b : K} {r : ℝ≥0∞} {f : eball a r → K}
    (hb : b ∈ eball a r) :
    f ∘ Set.inclusion (IsUltrametricDist.eball_subset_eball_of_mem hb le_rfl) ∈
      discAnalytic K b r ↔ f ∈ discAnalytic K a r := by
  refine ⟨fun h ↦ ?_, fun h ↦ comp_inclusion_mem_discAnalytic h hb le_rfl⟩
  convert comp_inclusion_mem_discAnalytic h (mem_eball_comm.mp hb) le_rfl using 1
  ext z
  simp

end Ultrametric

section NontriviallyNormedField

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]

/-- **Comparison with `HasFPowerSeriesOnBall`.** For `0 < r`, the restriction of `F : K → K` to the
open disc of radius `r` about `a` is analytic on the disc exactly when `F` has a power series on
the ball of radius `r` about `a`. -/
theorem domRestrict_mem_discAnalytic_iff {a : K} {r : ℝ≥0∞} (hr : 0 < r) {F : K → K} :
    (eball a r).domRestrict F ∈ discAnalytic K a r ↔
      ∃ P : FormalMultilinearSeries K K K, HasFPowerSeriesOnBall F P a r := by
  refine ⟨fun ⟨g, hg, hF⟩ ↦ ⟨_, hasFPowerSeriesOnBall_of_forall_eq_evalAt_sub hr hg hF⟩,
    fun ⟨P, hP⟩ ↦ ⟨mk P.coeff, hP.le_radius_mk_coeff, fun z ↦ ?_⟩⟩
  exact (hP.evalAt_mk_coeff_sub z.property).symm

/-- For `0 < r`, a function analytic on the open disc of radius `r` about `a` determines its power
series in `z - a`. -/
theorem existsUnique_series_of_mem_discAnalytic {a : K} {r : ℝ≥0∞} (hr : 0 < r)
    {f : eball a r → K} (hf : f ∈ discAnalytic K a r) :
    ∃! g : K⟦X⟧, r ≤ g.radius ∧ ∀ z : eball a r, f z = g.evalAt ((z : K) - a) := by
  obtain ⟨g, hg, hfg⟩ := hf
  exact ⟨g, ⟨hg, hfg⟩, fun g' ⟨hg', hfg'⟩ ↦
    eq_of_forall_evalAt_sub_eq hr hg' hg fun z ↦ (hfg' z).symm.trans (hfg z)⟩

/-- For `0 < r`, the representing series of a function analytic on the disc is any series of
radius at least `r` that represents it. -/
theorem discAnalytic.series_eq {a : K} {r : ℝ≥0∞} (hr : 0 < r) (f : discAnalytic K a r)
    {g : K⟦X⟧} (hg : r ≤ g.radius)
    (hfg : ∀ z : eball a r, (f : eball a r → K) z = g.evalAt ((z : K) - a)) :
    discAnalytic.series f = g :=
  eq_of_forall_evalAt_sub_eq hr (discAnalytic.le_radius_series f) hg fun z ↦
    (discAnalytic.apply_eq_evalAt_series f z).symm.trans (hfg z)

/-- **Derivatives.** The derivative of a function whose restriction to an open disc is analytic on
the disc again restricts to a function analytic on the disc. -/
theorem domRestrict_deriv_mem_discAnalytic {a : K} {r : ℝ≥0∞} {F : K → K}
    (hF : (eball a r).domRestrict F ∈ discAnalytic K a r) :
    (eball a r).domRestrict (deriv F) ∈ discAnalytic K a r := by
  rcases eq_zero_or_pos r with rfl | hr
  · exact ⟨0, zero_le, fun z ↦ absurd z.property (by simp)⟩
  obtain ⟨g, hg, hFg⟩ := hF
  exact (domRestrict_mem_discAnalytic_iff hr).mpr
    ⟨_, (hasFPowerSeriesOnBall_of_forall_eq_evalAt_sub hr hg hFg).deriv_ofScalars⟩

variable [IsUltrametricDist K]

/-- **The identity principle on an open disc.** Over a complete ultrametric nontrivially normed
field, a function analytic on an open disc that vanishes on a neighbourhood of one point of the
disc vanishes on the whole disc. -/
theorem discAnalytic.eq_zero_of_eventuallyEq_zero {a : K} {r : ℝ≥0∞} {f : eball a r → K}
    (hf : f ∈ discAnalytic K a r) {z₀ : eball a r} (h : f =ᶠ[𝓝 z₀] 0) : f = 0 := by
  obtain ⟨g, hg, hfg⟩ := hf
  have hr : 0 < r := pos_of_gt z₀.property
  -- Expand at `z₀`: the translate `g₀` of `g` represents `f` about `z₀` on the whole disc.
  set g₀ := taylor ((z₀ : K) - a) g
  have hg₀ : r ≤ g₀.radius := le_radius_taylor_sub hg z₀.property
  have hfg₀ (z : eball a r) : f z = g₀.evalAt ((z : K) - (z₀ : K)) := by
    rw [hfg, evalAt_sub_eq_evalAt_taylor_sub hg z₀.property z.property]
  have hP := hasFPowerSeriesOnBall_of_forall_eq_evalAt_sub (a := (z₀ : K)) hr hg₀
    (F := fun z ↦ g₀.evalAt (z - (z₀ : K))) fun _ ↦ rfl
  -- The function `z ↦ g₀(z - z₀)` vanishes near `z₀` in `K`, so all coefficients of `g₀` vanish.
  have hzero : (fun z ↦ g₀.evalAt (z - (z₀ : K))) =ᶠ[𝓝 (z₀ : K)] 0 := by
    have hopen : eball a r ∈ 𝓝 (z₀ : K) := isOpen_eball.mem_nhds z₀.property
    rw [nhds_subtype, EventuallyEq, eventually_comap] at h
    filter_upwards [h, hopen] with z hz hzr
    rw [← hfg₀ ⟨z, hzr⟩]
    exact hz ⟨z, hzr⟩ rfl
  have hcoeff : (fun n ↦ coeff n g₀) = 0 := by
    simpa using hP.hasFPowerSeriesAt.eq_zero_of_eventually hzero
  have hg₀0 : g₀ = 0 := by
    ext n
    simpa using congrFun hcoeff n
  ext z
  rw [hfg₀, hg₀0, evalAt_zero, Pi.zero_apply]

/-- **The identity principle on an open disc.** Over a complete ultrametric nontrivially normed
field, two functions analytic on an open disc that agree on a nonempty open subset of the disc are
equal. -/
theorem discAnalytic.eq_of_eqOn {a : K} {r : ℝ≥0∞} {f g : eball a r → K}
    (hf : f ∈ discAnalytic K a r) (hg : g ∈ discAnalytic K a r) {U : Set (eball a r)}
    (hU : IsOpen U) (hne : U.Nonempty) (h : Set.EqOn f g U) : f = g := by
  obtain ⟨z₀, hz₀⟩ := hne
  refine sub_eq_zero.mp
    (discAnalytic.eq_zero_of_eventuallyEq_zero (sub_mem hf hg) (z₀ := z₀) ?_)
  filter_upwards [hU.mem_nhds hz₀] with z hz
  simp [h hz]

end NontriviallyNormedField

end TauCeti
