/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.CutoffCurrent
public import TauCeti.Analysis.Contour.Winding.Number.Basic
public import TauCeti.Analysis.Calculus.DifferentialForm.DiscMollification
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Integral.CircleIntegral
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.DifferentialForm.Regularity
import TauCeti.Analysis.Contour.Winding.Integer
import TauCeti.Analysis.Contour.Winding.Number.Circle.Loop
import TauCeti.Topology.Discrete
import TauCeti.Analysis.Contour.Winding.Number.Homotopy
import TauCeti.Analysis.Contour.Winding.RealIntegral.Basic

/-!
# Integer disc charges of the cutoff current

Let `(a, α)` be an abelian Higgs pair with `a = i b`, and let
`Θ = i F_a + d(χ(|α|²) τ)` be its cutoff current (`TauCeti.SeibergWitten.cutoffCurrent`), where
`χ` vanishes near `0`. A smooth disc `σ` whose boundary circle lies in the region where
`χ(|α|²) = 1` carries the charge

`I(σ) = (2π)⁻¹ ∫_D σ^* Θ`.

This file proves that this charge is an **integer**: it is the winding number of `α ∘ σ` around
the boundary circle (`exists_int_integral_cutoffCurrent_comp_closedBall`). The flux identity
`TauCeti.SeibergWitten.integral_cutoffCurrent_closedBall` already writes `∫_D Θ` as the winding
integral `∮ Im (α⁻¹ dα)`, with no contribution from the connection. Here that integral is
identified, through the real winding formula
`TauCeti.Contour.windingNumber_eq_real_integral_of_closed`, with `2π` times the winding number
`TauCeti.Contour.windingNumber`, which is an integer because the boundary loop is closed and
misses `0`. The pullback naturality of the cutoff current
(`TauCeti.SeibergWitten.cutoffCurrent_comp`) reduces the statement for a disc `σ : ℂ → E` in an
arbitrary real normed space to the case of a disc in the plane
(`exists_int_integral_cutoffCurrent_closedBall`).

If instead `χ = 1` near `|α|²` on the whole disc, the cutoff current vanishes there and the charge
is zero (`integral_cutoffCurrent_comp_closedBall_eq_zero`).

Since the charge is the winding number of the boundary loop, it is controlled by the zeros of
`α ∘ σ` and by the boundary circle:

* it does not depend on the cutoff: two cutoffs that are both `1` along the boundary circle give
  the same charge (`integral_cutoffCurrent_comp_closedBall_congr_cutoff`);
* it is additive over disjoint subdiscs: if finitely many pairwise disjoint closed subdiscs `Dᵢ`
  of `D` contain all the zeros of `α ∘ σ` in `D` in their interiors, and their boundary circles
  also lie in `{χ(|α|²) = 1}`, the charge of `D` is the sum of the charges of the `Dᵢ`
  (`integral_cutoffCurrent_comp_closedBall_eq_sum`). The cutoff current need not vanish between
  the subdiscs; replacing `χ` by a cutoff that is `1` wherever `|α ∘ σ|²` is at least its minimum
  over that region changes no charge and makes the current vanish there;
* in particular it vanishes as soon as `α ∘ σ` has no zero on the closed disc, even where
  `χ(|α|²) < 1` (`integral_cutoffCurrent_comp_closedBall_eq_zero_of_ne_zero`), so a disc of
  nonzero charge contains a zero of `α ∘ σ` in its interior
  (`exists_mem_ball_eq_zero_of_integral_cutoffCurrent_comp_ne_zero`);
* and it is unchanged on passing to a subdisc, concentric or not, containing all the zeros of
  `α ∘ σ`, provided the smaller boundary circle also lies in `{χ(|α|²) = 1}`
  (`integral_cutoffCurrent_comp_closedBall_eq_of_subset`,
  `integral_cutoffCurrent_comp_closedBall_eq_of_annulus`);
* it is invariant under homotopies of discs whose boundary circles stay in `{χ(|α|²) = 1}`
  (`integral_cutoffCurrent_comp_closedBall_eq_of_continuousOn`); the interiors of the discs may
  cross the zeros of `α` along the homotopy.
* it is multiplied by the degree under reparametrization: if a `C²` map `θ` sends the boundary
  circle of a disc `D₁` into that of `D`, the charge of `σ ∘ θ` on `D₁` is the charge of `σ` on
  `D` times the winding number of `θ` along the boundary of `D₁`
  (`exists_int_integral_cutoffCurrent_comp_comp_closedBall_eq_mul`), by the degree law
  `TauCeti.Contour.windingNumber_comp_eq_mul_of_mem_sphere` for boundary loops.

In Taubes's passage from Seiberg–Witten solutions to pseudoholomorphic curves, `α` is the
component of the rescaled spinor along the canonical unit spinor and the cutoff currents converge
to the current of the limiting curve. The integer charges of discs whose boundary stays where
`|α|` is bounded below are the quantities whose limits are compared there with the local
intersection numbers of discs with the limiting curve; that comparison is not part of this file.

What this file does prove is that these integers stabilize along a family of cutoff currents
whose coefficients `Θ(y)(v, w)` converge as distributions. If the boundary circles of all the
translated discs `σ + p`, `‖p‖ ≤ δ`, lie in `{χ(|α|²) = 1}`, homotopy invariance makes their
charges equal, so averaging over `p` against a weight `ρ` of integral one supported in that ball
does not change the charge of `σ`. By the
averaging identity for mollified discs
(`TauCeti.integral_mul_setIntegral_add_eq_sum_integral_discMollification_mul`), the averaged
charge is a finite sum of pairings of the coefficients `Θ(y)(e i, e j)` of the cutoff current
with fixed test functions, the coefficients of the mollified disc
(`integral_cutoffCurrent_comp_closedBall_eq_sum_integral_discMollification_mul`). For a smooth
compactly supported `ρ` these test functions are smooth and compactly supported. So when the
coefficients of a family of cutoff currents converge as distributions, the charges of `σ`
converge, and being integers they are eventually constant
(`exists_int_eventually_integral_cutoffCurrent_comp_closedBall_eq`).

## Main results

* `TauCeti.SeibergWitten.exists_int_integral_cutoffCurrent_closedBall`: the flux of the cutoff
  current through a disc in the plane whose boundary circle lies in `{χ(|α|²) = 1}` is `2π n`,
  with `n` the integer winding number of `α` around that circle.
* `TauCeti.SeibergWitten.exists_int_integral_cutoffCurrent_comp_closedBall`: the same for the
  pullback of the cutoff current by a `C²` disc `σ : ℂ → E`, with `n` the winding number of
  `α ∘ σ`.
* `TauCeti.SeibergWitten.integral_cutoffCurrent_comp_closedBall_eq_zero`: the charge of a disc on
  which `χ = 1` near `|α|²` vanishes.
* `TauCeti.SeibergWitten.integral_cutoffCurrent_comp_closedBall_congr_cutoff`: the charge is the
  same for any two cutoffs that are both `1` along the boundary circle.
* `TauCeti.SeibergWitten.integral_cutoffCurrent_comp_closedBall_eq_sum`: the charge is additive
  over finite families of disjoint subdiscs containing the zeros of `α ∘ σ`; the planar version
  is `TauCeti.SeibergWitten.integral_cutoffCurrent_closedBall_eq_sum`.
* `TauCeti.SeibergWitten.integral_cutoffCurrent_comp_closedBall_eq_zero_of_ne_zero` and
  `TauCeti.SeibergWitten.exists_mem_ball_eq_zero_of_integral_cutoffCurrent_comp_ne_zero`: a disc
  on which `α` does not vanish has charge zero, so a disc of nonzero charge meets the zeros of `α`.
* `TauCeti.SeibergWitten.integral_cutoffCurrent_comp_closedBall_eq_of_subset` and
  `TauCeti.SeibergWitten.integral_cutoffCurrent_comp_closedBall_eq_of_annulus`: the charge does
  not change on passing to a subdisc containing the zeros of `α ∘ σ`.
* `TauCeti.SeibergWitten.integral_cutoffCurrent_comp_closedBall_eq_of_continuousOn`: the charge is
  invariant under homotopies keeping the boundary circle in `{χ(|α|²) = 1}`.
* `TauCeti.SeibergWitten.exists_int_integral_cutoffCurrent_comp_comp_closedBall_eq_mul`: the
  degree law, the charge of `σ ∘ θ` is the degree of `θ` on the boundary circles times the
  charge of `σ`.
* `integral_cutoffCurrent_comp_closedBall_eq_sum_integral_discMollification_mul`:
  the charge of a disc whose translates have boundary in `{χ(|α|²) = 1}` is a pairing of the
  cutoff current with the mollified disc.
* `TauCeti.SeibergWitten.exists_int_eventually_integral_cutoffCurrent_comp_closedBall_eq`: along a
  family of cutoff currents whose coefficients converge as distributions, the integer charges of
  such a disc are eventually constant.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

noncomputable section

open ContinuousAlternatingMap Complex Filter Set MeasureTheory
open scoped Topology Real ContDiff

namespace TauCeti.SeibergWitten

variable {χ : ℝ → ℝ}

/-- A cutoff vanishing near `0` takes the value `1` on `|w|²` only for `w ≠ 0`. -/
private theorem ne_zero_of_cutoff_eq_one (hχ₀ : χ =ᶠ[𝓝 0] 0) {w : ℂ} (h : χ (normSq w) = 1) :
    w ≠ 0 := by
  rintro rfl
  rw [normSq_zero, hχ₀.eq_of_nhds, Pi.zero_apply] at h
  exact zero_ne_one h

/-- **Integrality of the disc charge in the plane.** For fields on the plane such that
`χ(|α|²) = 1` on the boundary circle of a closed disc, the integral of the cutoff current over the
disc is `2π n`, where the integer `n` is the winding number of `α` around the boundary circle. -/
theorem exists_int_integral_cutoffCurrent_closedBall {α : ℂ → ℂ}
    {b : ℂ → ℂ [⋀^Fin 1]→L[ℝ] ℝ} {z₀ : ℂ} {r : ℝ} (hr : 0 ≤ r) (hα : ContDiff ℝ 2 α)
    (hb : ContDiff ℝ 1 b) (hχ : ContDiff ℝ 1 χ) (hχ₀ : χ =ᶠ[𝓝 0] 0)
    (hbd : ∀ θ, χ (normSq (α (circleMap z₀ r θ))) = 1) :
    ∃ n : ℤ, Contour.windingNumber (α ∘ circleMap z₀ r) (-π) π 0 = n ∧
      ∫ z in Metric.closedBall z₀ r, cutoffCurrent χ b α z ![1, I] = 2 * π * n := by
  set γ := α ∘ circleMap z₀ r with hγ
  have hderiv : deriv γ = fun θ ↦ fderiv ℝ α (circleMap z₀ r θ) (circleMap 0 r θ * I) :=
    funext fun θ ↦ ((hα.differentiable two_ne_zero _).hasFDerivAt.comp_hasDerivAt θ
      (hasDerivAt_circleMap z₀ r θ)).deriv
  have hγ₀ (θ : ℝ) : γ θ ≠ 0 := ne_zero_of_cutoff_eq_one hχ₀ (hbd θ)
  have hγc : Continuous γ := hα.continuous.comp (continuous_circleMap z₀ r)
  -- The index integrand `γ⁻¹ γ'` of the boundary loop is continuous, hence integrable.
  have hint : IntervalIntegrable (fun θ ↦ (γ θ - 0)⁻¹ * deriv γ θ) volume (-π) π := by
    simp_rw [sub_zero, hderiv]
    exact ((hγc.inv₀ hγ₀).mul (((hα.continuous_fderiv two_ne_zero).comp
      (continuous_circleMap z₀ r)).clm_apply ((continuous_circleMap 0 r).mul
        continuous_const))).intervalIntegrable _ _
  have hclosed : γ (-π) = γ π := by
    simp only [hγ, Function.comp_apply, ← periodic_circleMap z₀ r (-π)]
    ring_nf
  have hdiff (θ : ℝ) (_ : θ ∈ Ioo (min (-π) π) (max (-π) π) \ ∅) : DifferentiableAt ℝ γ θ :=
    (hα.differentiable two_ne_zero).differentiableAt.comp θ (differentiable_circleMap z₀ r θ)
  obtain ⟨n, hn⟩ := Contour.exists_int_windingNumber_of_closed hclosed countable_empty
    hγc.continuousOn hdiff (fun θ _ ↦ hγ₀ θ)
  refine ⟨n, hn, ?_⟩
  -- The winding number of the boundary loop is `(2π)⁻¹` times its real winding integral.
  have hreal := Contour.windingNumber_eq_real_integral_of_closed hclosed countable_empty
    hγc.continuousOn hdiff (fun θ _ ↦ hγ₀ θ) hint
  rw [hn, ← ofReal_intCast, ofReal_inj] at hreal
  rw [integral_cutoffCurrent_closedBall hr hα hb hχ hχ₀ hbd]
  calc ∫ θ in -π..π, phaseForm α (circleMap z₀ r θ) (fun _ ↦ circleMap 0 r θ * I)
      = ∫ θ in -π..π, Contour.realWindingIntegrand (γ θ - 0) (deriv γ θ) := by
        refine intervalIntegral.integral_congr fun θ _ ↦ ?_
        rw [Contour.realWindingIntegrand_def, hderiv]
        simp [hγ]
    _ = 2 * π * n := by
        rw [hreal]
        field_simp

/-- **Integrality of the disc charge.** Let `σ : ℂ → E` be a `C²` disc such that
`χ(|α|²) = 1` along `σ` of the boundary circle of a closed disc. Then the integral over the disc
of the pullback by `σ` of the cutoff current is `2π n`, where the integer `n` is the winding
number of `α ∘ σ` around the boundary circle. -/
theorem exists_int_integral_cutoffCurrent_comp_closedBall {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {α : E → ℂ} {b : E → E [⋀^Fin 1]→L[ℝ] ℝ} {σ : ℂ → E} {z₀ : ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hα : ContDiff ℝ 2 α) (hb : ContDiff ℝ 1 b) (hχ : ContDiff ℝ 1 χ)
    (hχ₀ : χ =ᶠ[𝓝 0] 0) (hσ : ContDiff ℝ 2 σ)
    (hbd : ∀ θ, χ (normSq (α (σ (circleMap z₀ r θ)))) = 1) :
    ∃ n : ℤ, Contour.windingNumber (α ∘ σ ∘ circleMap z₀ r) (-π) π 0 = n ∧
      ∫ z in Metric.closedBall z₀ r,
        (cutoffCurrent χ b α (σ z)).compContinuousLinearMap (fderiv ℝ σ z) ![1, I] =
          2 * π * n := by
  have hpull : ContDiff ℝ 1 fun z ↦ (b (σ z)).compContinuousLinearMap (fderiv ℝ σ z) :=
    contDiff_iff_contDiffAt.2 fun z ↦ hσ.contDiffAt.differentialForm_pullback hb.contDiffAt
  simp_rw [← fun z ↦ cutoffCurrent_comp (y := z) hα.contDiffAt hb.contDiffAt hχ hχ₀ hσ.contDiffAt]
  exact exists_int_integral_cutoffCurrent_closedBall hr (hα.comp hσ) hpull hχ hχ₀ hbd

/-- **The charge of a disc in the vacuum vanishes.** If `χ = 1` near `|α|²` at every point of `σ`
of a closed disc, then the integral over the disc of the pullback by `σ` of the cutoff current
is zero. -/
theorem integral_cutoffCurrent_comp_closedBall_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {α : E → ℂ} {b : E → E [⋀^Fin 1]→L[ℝ] ℝ} {σ : ℂ → E} {z₀ : ℂ} {r : ℝ}
    (hα : ∀ z ∈ Metric.closedBall z₀ r, ContDiffAt ℝ 2 α (σ z))
    (hχ₀ : χ =ᶠ[𝓝 0] 0)
    (hvac : ∀ z ∈ Metric.closedBall z₀ r, χ =ᶠ[𝓝 (normSq (α (σ z)))] 1) :
    ∫ z in Metric.closedBall z₀ r,
      (cutoffCurrent χ b α (σ z)).compContinuousLinearMap (fderiv ℝ σ z) ![1, I] = 0 := by
  refine setIntegral_eq_zero_of_forall_eq_zero fun z hz ↦ ?_
  rw [cutoffCurrent_eq_zero (hα z hz)
    (ne_zero_of_cutoff_eq_one hχ₀ (hvac z hz).eq_of_nhds) (hvac z hz)]
  simp

/-! ### Independence of the cutoff and additivity over subdiscs -/

/-- **The disc charge does not depend on the cutoff.** If two `C¹` cutoffs `χ` and `χ'`, both
vanishing near `0`, take the value `1` along `α` of the boundary circle of a closed disc in the
plane, then their cutoff currents have the same integral over the disc: both integrals are `2π`
times the winding number of `α` around the circle. -/
theorem integral_cutoffCurrent_closedBall_congr_cutoff {χ' : ℝ → ℝ} {α : ℂ → ℂ}
    {b : ℂ → ℂ [⋀^Fin 1]→L[ℝ] ℝ} {z₀ : ℂ} {r : ℝ} (hr : 0 ≤ r) (hα : ContDiff ℝ 2 α)
    (hb : ContDiff ℝ 1 b) (hχ : ContDiff ℝ 1 χ) (hχ₀ : χ =ᶠ[𝓝 0] 0) (hχ' : ContDiff ℝ 1 χ')
    (hχ'₀ : χ' =ᶠ[𝓝 0] 0) (hbd : ∀ θ, χ (normSq (α (circleMap z₀ r θ))) = 1)
    (hbd' : ∀ θ, χ' (normSq (α (circleMap z₀ r θ))) = 1) :
    ∫ z in Metric.closedBall z₀ r, cutoffCurrent χ b α z ![1, I] =
      ∫ z in Metric.closedBall z₀ r, cutoffCurrent χ' b α z ![1, I] := by
  obtain ⟨m, hm, hI⟩ := exists_int_integral_cutoffCurrent_closedBall hr hα hb hχ hχ₀ hbd
  obtain ⟨n, hn, hI'⟩ := exists_int_integral_cutoffCurrent_closedBall hr hα hb hχ' hχ'₀ hbd'
  have hmn : m = n := by exact_mod_cast hm.symm.trans hn
  rw [hI, hI', hmn]

/-- **Additivity of the disc charge in the plane.** Let `D` be a closed disc in the plane and
`Dᵢ`, `i ∈ s`, finitely many pairwise disjoint closed subdiscs of `D`. Suppose that
`χ(|α|²) = 1` along the boundary circles of `D` and of every `Dᵢ`, and that `α` has no zero in
`D` outside the open discs `Dᵢ`. Then the integral of the cutoff current over `D` is the sum of
its integrals over the `Dᵢ`.

The cutoff current itself need not vanish between the subdiscs, where `χ(|α|²)` may be smaller
than `1`. -/
theorem integral_cutoffCurrent_closedBall_eq_sum {ι : Type*} {α : ℂ → ℂ}
    {b : ℂ → ℂ [⋀^Fin 1]→L[ℝ] ℝ} {z₀ : ℂ} {r : ℝ} {s : Finset ι} {c : ι → ℂ} {ρ : ι → ℝ}
    (hr : 0 ≤ r) (hρ : ∀ i ∈ s, 0 ≤ ρ i) (hα : ContDiff ℝ 2 α) (hb : ContDiff ℝ 1 b)
    (hχ : ContDiff ℝ 1 χ) (hχ₀ : χ =ᶠ[𝓝 0] 0)
    (hsub : ∀ i ∈ s, Metric.closedBall (c i) (ρ i) ⊆ Metric.closedBall z₀ r)
    (hdisj : (s : Set ι).PairwiseDisjoint fun i ↦ Metric.closedBall (c i) (ρ i))
    (hbd : ∀ θ, χ (normSq (α (circleMap z₀ r θ))) = 1)
    (hbds : ∀ i ∈ s, ∀ θ, χ (normSq (α (circleMap (c i) (ρ i) θ))) = 1)
    (hne : ∀ z ∈ Metric.closedBall z₀ r \ ⋃ i ∈ s, Metric.ball (c i) (ρ i), α z ≠ 0) :
    ∫ z in Metric.closedBall z₀ r, cutoffCurrent χ b α z ![1, I] =
      ∑ i ∈ s, ∫ z in Metric.closedBall (c i) (ρ i), cutoffCurrent χ b α z ![1, I] := by
  -- `α` has no zero on the compact set `K` made of the region between the subdiscs and all the
  -- boundary circles.
  set K := (Metric.closedBall z₀ r \ ⋃ i ∈ s, Metric.ball (c i) (ρ i)) ∪
    (Metric.sphere z₀ r ∪ ⋃ i ∈ s, Metric.sphere (c i) (ρ i))
  have hKc : IsCompact K :=
    ((isCompact_closedBall z₀ r).diff (isOpen_iUnion fun i ↦ isOpen_iUnion fun _ ↦
      Metric.isOpen_ball)).union ((isCompact_sphere z₀ r).union
        (s.isCompact_biUnion fun i _ ↦ isCompact_sphere (c i) (ρ i)))
  have hsphere {z₁ : ℂ} {R : ℝ} (hR : 0 ≤ R) (h : ∀ θ, χ (normSq (α (circleMap z₁ R θ))) = 1)
      (z : ℂ) (hz : z ∈ Metric.sphere z₁ R) : α z ≠ 0 := by
    obtain ⟨θ, rfl⟩ : z ∈ range (circleMap z₁ R) := by
      rwa [range_circleMap, abs_of_nonneg hR]
    exact ne_zero_of_cutoff_eq_one hχ₀ (h θ)
  have hKne (z : ℂ) (hz : z ∈ K) : α z ≠ 0 := by
    rcases hz with hz | hz | hz
    · exact hne z hz
    · exact hsphere hr hbd z hz
    · obtain ⟨i, hi, hz⟩ := mem_iUnion₂.1 hz
      exact hsphere (hρ i hi) (hbds i hi) z hz
  -- A cutoff `χ'` that is `1` near `|α|²` along `K` has a cutoff current vanishing on `K`, and
  -- every boundary circle is admissible for it.
  obtain ⟨χ', hχ', -, hχ'₁, -, hχ'U⟩ :=
    (hKc.image (continuous_normSq.comp hα.continuous)).exists_contDiff_cutoff_eventuallyEq_one
      isOpen_compl_singleton (image_subset_iff.2 fun z hz ↦ (normSq_pos.2 (hKne z hz)).ne')
  replace hχ' : ContDiff ℝ 1 χ' := hχ'.of_le (by simp)
  have hχ'₀ : χ' =ᶠ[𝓝 0] 0 := notMem_tsupport_iff_eventuallyEq.1 fun h ↦ hχ'U h rfl
  replace hχ'₁ (z : ℂ) (hz : z ∈ K) : χ' =ᶠ[𝓝 (normSq (α z))] 1 :=
    hχ'₁ _ (mem_image_of_mem _ hz)
  have hbd' {z₁ : ℂ} {R : ℝ} (hR : 0 ≤ R) (h : Metric.sphere z₁ R ⊆ K) (θ : ℝ) :
      χ' (normSq (α (circleMap z₁ R θ))) = 1 :=
    (hχ'₁ _ (h (circleMap_mem_sphere z₁ hR θ))).eq_of_nhds
  have hzero (z : ℂ) (hz : z ∈ K) : cutoffCurrent χ' b α z ![1, I] = 0 := by
    rw [cutoffCurrent_eq_zero hα.contDiffAt (hKne z hz) (hχ'₁ z hz)]
    simp
  have hΘ : Continuous fun z ↦ cutoffCurrent χ' b α z ![1, I] :=
    (contDiff_cutoffCurrent (m := 0) (n := 1) hα hb hχ' hχ'₀ (by norm_num)).continuous.eval
      continuous_const
  calc ∫ z in Metric.closedBall z₀ r, cutoffCurrent χ b α z ![1, I]
      = ∫ z in Metric.closedBall z₀ r, cutoffCurrent χ' b α z ![1, I] :=
        integral_cutoffCurrent_closedBall_congr_cutoff hr hα hb hχ hχ₀ hχ' hχ'₀ hbd
          (hbd' hr fun z hz ↦ Or.inr (Or.inl hz))
    _ = ∫ z in ⋃ i ∈ s, Metric.closedBall (c i) (ρ i), cutoffCurrent χ' b α z ![1, I] :=
        setIntegral_eq_of_subset_of_forall_sdiff_eq_zero Metric.isClosed_closedBall.measurableSet
          (iUnion₂_subset hsub) fun z hz ↦ hzero z (Or.inl ⟨hz.1, fun h ↦ hz.2
            (iUnion₂_mono (fun i _ ↦ Metric.ball_subset_closedBall) h)⟩)
    _ = ∑ i ∈ s, ∫ z in Metric.closedBall (c i) (ρ i), cutoffCurrent χ' b α z ![1, I] :=
        integral_biUnion_finset s (fun i _ ↦ Metric.isClosed_closedBall.measurableSet) hdisj
          fun i _ ↦ hΘ.continuousOn.integrableOn_compact (isCompact_closedBall (c i) (ρ i))
    _ = ∑ i ∈ s, ∫ z in Metric.closedBall (c i) (ρ i), cutoffCurrent χ b α z ![1, I] :=
        Finset.sum_congr rfl fun i hi ↦ (integral_cutoffCurrent_closedBall_congr_cutoff (hρ i hi)
          hα hb hχ hχ₀ hχ' hχ'₀ (hbds i hi)
            (hbd' (hρ i hi) fun z hz ↦ Or.inr (Or.inr (mem_iUnion₂.2 ⟨i, hi, hz⟩)))).symm

/-- **The disc charge does not depend on the cutoff.** Let `σ : ℂ → E` be a `C²` disc and let
`χ`, `χ'` be `C¹` cutoffs vanishing near `0` that both take the value `1` along `α ∘ σ` of the
boundary circle of a closed disc. Then the charges of the disc for the cutoff currents of `χ`
and of `χ'` agree. -/
theorem integral_cutoffCurrent_comp_closedBall_congr_cutoff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {χ' : ℝ → ℝ} {α : E → ℂ} {b : E → E [⋀^Fin 1]→L[ℝ] ℝ} {σ : ℂ → E} {z₀ : ℂ}
    {r : ℝ} (hr : 0 ≤ r) (hα : ContDiff ℝ 2 α) (hb : ContDiff ℝ 1 b) (hχ : ContDiff ℝ 1 χ)
    (hχ₀ : χ =ᶠ[𝓝 0] 0) (hχ' : ContDiff ℝ 1 χ') (hχ'₀ : χ' =ᶠ[𝓝 0] 0) (hσ : ContDiff ℝ 2 σ)
    (hbd : ∀ θ, χ (normSq (α (σ (circleMap z₀ r θ)))) = 1)
    (hbd' : ∀ θ, χ' (normSq (α (σ (circleMap z₀ r θ)))) = 1) :
    ∫ z in Metric.closedBall z₀ r,
        (cutoffCurrent χ b α (σ z)).compContinuousLinearMap (fderiv ℝ σ z) ![1, I] =
      ∫ z in Metric.closedBall z₀ r,
        (cutoffCurrent χ' b α (σ z)).compContinuousLinearMap (fderiv ℝ σ z) ![1, I] := by
  have hpull : ContDiff ℝ 1 fun z ↦ (b (σ z)).compContinuousLinearMap (fderiv ℝ σ z) :=
    contDiff_iff_contDiffAt.2 fun z ↦ hσ.contDiffAt.differentialForm_pullback hb.contDiffAt
  simp_rw [← fun z ↦ cutoffCurrent_comp (y := z) hα.contDiffAt hb.contDiffAt hχ hχ₀ hσ.contDiffAt,
    ← fun z ↦ cutoffCurrent_comp (y := z) hα.contDiffAt hb.contDiffAt hχ' hχ'₀ hσ.contDiffAt]
  exact integral_cutoffCurrent_closedBall_congr_cutoff hr (hα.comp hσ) hpull hχ hχ₀ hχ' hχ'₀ hbd
    hbd'

/-- **Additivity of the disc charge over disjoint subdiscs.** Let `σ : ℂ → E` be a `C²` disc, `D`
a closed disc in the parameter plane and `Dᵢ`, `i ∈ s`, finitely many pairwise disjoint closed
subdiscs of `D`. Suppose that `χ(|α|²) = 1` along `σ` of the boundary circles of `D` and of every
`Dᵢ`, and that `α ∘ σ` has no zero in `D` outside the open discs `Dᵢ`. Then the charge of `D` is
the sum of the charges of the `Dᵢ`. For the empty family this says that a disc on which `α ∘ σ`
has no zero has charge zero (`integral_cutoffCurrent_comp_closedBall_eq_zero_of_ne_zero`). -/
theorem integral_cutoffCurrent_comp_closedBall_eq_sum {E ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {α : E → ℂ} {b : E → E [⋀^Fin 1]→L[ℝ] ℝ} {σ : ℂ → E} {z₀ : ℂ} {r : ℝ}
    {s : Finset ι} {c : ι → ℂ} {ρ : ι → ℝ} (hr : 0 ≤ r) (hρ : ∀ i ∈ s, 0 ≤ ρ i)
    (hα : ContDiff ℝ 2 α) (hb : ContDiff ℝ 1 b) (hχ : ContDiff ℝ 1 χ) (hχ₀ : χ =ᶠ[𝓝 0] 0)
    (hσ : ContDiff ℝ 2 σ)
    (hsub : ∀ i ∈ s, Metric.closedBall (c i) (ρ i) ⊆ Metric.closedBall z₀ r)
    (hdisj : (s : Set ι).PairwiseDisjoint fun i ↦ Metric.closedBall (c i) (ρ i))
    (hbd : ∀ θ, χ (normSq (α (σ (circleMap z₀ r θ)))) = 1)
    (hbds : ∀ i ∈ s, ∀ θ, χ (normSq (α (σ (circleMap (c i) (ρ i) θ)))) = 1)
    (hne : ∀ z ∈ Metric.closedBall z₀ r \ ⋃ i ∈ s, Metric.ball (c i) (ρ i), α (σ z) ≠ 0) :
    ∫ z in Metric.closedBall z₀ r,
        (cutoffCurrent χ b α (σ z)).compContinuousLinearMap (fderiv ℝ σ z) ![1, I] =
      ∑ i ∈ s, ∫ z in Metric.closedBall (c i) (ρ i),
        (cutoffCurrent χ b α (σ z)).compContinuousLinearMap (fderiv ℝ σ z) ![1, I] := by
  have hpull : ContDiff ℝ 1 fun z ↦ (b (σ z)).compContinuousLinearMap (fderiv ℝ σ z) :=
    contDiff_iff_contDiffAt.2 fun z ↦ hσ.contDiffAt.differentialForm_pullback hb.contDiffAt
  simp_rw [← fun z ↦ cutoffCurrent_comp (y := z) hα.contDiffAt hb.contDiffAt hχ hχ₀ hσ.contDiffAt]
  exact integral_cutoffCurrent_closedBall_eq_sum hr hρ (hα.comp hσ) hpull hχ hχ₀ hsub hdisj hbd
    hbds hne

/-- **Restriction of the disc charge to a subdisc.** Let `σ : ℂ → E` be a `C²` disc and `D' ⊆ D`
closed discs in the parameter plane, not necessarily concentric, such that `χ(|α|²) = 1` along
`σ` of both boundary circles and `α ∘ σ` has no zero in `D` outside the open disc `D'`. Then `D'`
and `D` carry the same charge. -/
theorem integral_cutoffCurrent_comp_closedBall_eq_of_subset {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {α : E → ℂ} {b : E → E [⋀^Fin 1]→L[ℝ] ℝ} {σ : ℂ → E} {z₀ z₁ : ℂ}
    {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) (hα : ContDiff ℝ 2 α) (hb : ContDiff ℝ 1 b)
    (hχ : ContDiff ℝ 1 χ) (hχ₀ : χ =ᶠ[𝓝 0] 0) (hσ : ContDiff ℝ 2 σ)
    (hsub : Metric.closedBall z₁ r₁ ⊆ Metric.closedBall z₀ r₂)
    (hbd₁ : ∀ θ, χ (normSq (α (σ (circleMap z₁ r₁ θ)))) = 1)
    (hbd₂ : ∀ θ, χ (normSq (α (σ (circleMap z₀ r₂ θ)))) = 1)
    (hne : ∀ z ∈ Metric.closedBall z₀ r₂ \ Metric.ball z₁ r₁, α (σ z) ≠ 0) :
    ∫ z in Metric.closedBall z₁ r₁,
        (cutoffCurrent χ b α (σ z)).compContinuousLinearMap (fderiv ℝ σ z) ![1, I] =
      ∫ z in Metric.closedBall z₀ r₂,
        (cutoffCurrent χ b α (σ z)).compContinuousLinearMap (fderiv ℝ σ z) ![1, I] := by
  simpa using (integral_cutoffCurrent_comp_closedBall_eq_sum (s := {()}) (c := fun _ ↦ z₁)
    (ρ := fun _ ↦ r₁) hr₂ (by simpa using hr₁) hα hb hχ hχ₀ hσ (by simpa using hsub) (by simp)
    hbd₂ (by simpa using hbd₁) (by simpa using hne)).symm

/-- **A disc on which `α` does not vanish has charge zero.** Let `σ : ℂ → E` be a `C²` disc such
that `χ(|α|²) = 1` along `σ` of the boundary circle of a closed disc, and such that `α ∘ σ` has
no zero on the closed disc. Then the integral over the disc of the pullback by `σ` of the cutoff
current vanishes. Unlike `integral_cutoffCurrent_comp_closedBall_eq_zero`, the cutoff `χ(|α|²)`
may be smaller than `1` inside the disc. This is the empty family in
`integral_cutoffCurrent_comp_closedBall_eq_sum`. -/
theorem integral_cutoffCurrent_comp_closedBall_eq_zero_of_ne_zero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {α : E → ℂ} {b : E → E [⋀^Fin 1]→L[ℝ] ℝ}
    {σ : ℂ → E} {z₀ : ℂ} {r : ℝ} (hr : 0 ≤ r) (hα : ContDiff ℝ 2 α) (hb : ContDiff ℝ 1 b)
    (hχ : ContDiff ℝ 1 χ) (hχ₀ : χ =ᶠ[𝓝 0] 0) (hσ : ContDiff ℝ 2 σ)
    (hbd : ∀ θ, χ (normSq (α (σ (circleMap z₀ r θ)))) = 1)
    (hne : ∀ z ∈ Metric.closedBall z₀ r, α (σ z) ≠ 0) :
    ∫ z in Metric.closedBall z₀ r,
      (cutoffCurrent χ b α (σ z)).compContinuousLinearMap (fderiv ℝ σ z) ![1, I] = 0 := by
  simpa using integral_cutoffCurrent_comp_closedBall_eq_sum (s := (∅ : Finset Unit))
    (c := fun _ ↦ z₀) (ρ := fun _ ↦ r) hr (by simp) hα hb hχ hχ₀ hσ (by simp) (by simp) hbd
    (by simp) (by simpa using hne)

/-- **A disc of nonzero charge meets the zeros of `α`.** Let `σ : ℂ → E` be a `C²` disc such that
`χ(|α|²) = 1` along `σ` of the boundary circle of a closed disc. If the integral over the disc of
the pullback by `σ` of the cutoff current is nonzero, then `α ∘ σ` vanishes at some point of the
open disc. -/
theorem exists_mem_ball_eq_zero_of_integral_cutoffCurrent_comp_ne_zero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {α : E → ℂ} {b : E → E [⋀^Fin 1]→L[ℝ] ℝ}
    {σ : ℂ → E} {z₀ : ℂ} {r : ℝ} (hr : 0 ≤ r) (hα : ContDiff ℝ 2 α) (hb : ContDiff ℝ 1 b)
    (hχ : ContDiff ℝ 1 χ) (hχ₀ : χ =ᶠ[𝓝 0] 0) (hσ : ContDiff ℝ 2 σ)
    (hbd : ∀ θ, χ (normSq (α (σ (circleMap z₀ r θ)))) = 1)
    (hI : ∫ z in Metric.closedBall z₀ r,
      (cutoffCurrent χ b α (σ z)).compContinuousLinearMap (fderiv ℝ σ z) ![1, I] ≠ 0) :
    ∃ z ∈ Metric.ball z₀ r, α (σ z) = 0 := by
  by_contra! h
  refine hI (integral_cutoffCurrent_comp_closedBall_eq_zero_of_ne_zero hr hα hb hχ hχ₀ hσ hbd
    fun z hz ↦ ?_)
  rcases (Metric.mem_closedBall.1 hz).lt_or_eq with hlt | heq
  · exact h z (Metric.mem_ball.2 hlt)
  -- A point of the boundary circle is `circleMap z₀ r θ`, where `χ(|α|²) = 1`.
  obtain ⟨θ, rfl⟩ : z ∈ range (circleMap z₀ r) := by
    rw [range_circleMap, abs_of_nonneg hr]
    exact Metric.mem_sphere.2 heq
  exact ne_zero_of_cutoff_eq_one hχ₀ (hbd θ)

/-- **The disc charge only sees the zeros of `α`.** Let `σ : ℂ → E` be a `C²` disc, and let
`0 ≤ r₁ ≤ r₂` be radii such that `χ(|α|²) = 1` along `σ` of both circles of radii `r₁` and `r₂`
about `z₀`, and such that `α ∘ σ` has no zero on the closed annulus between them. Then the discs
of radii `r₁` and `r₂` carry the same charge. This is the concentric case of
`integral_cutoffCurrent_comp_closedBall_eq_of_subset`. -/
theorem integral_cutoffCurrent_comp_closedBall_eq_of_annulus {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {α : E → ℂ} {b : E → E [⋀^Fin 1]→L[ℝ] ℝ}
    {σ : ℂ → E} {z₀ : ℂ} {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (hr : r₁ ≤ r₂) (hα : ContDiff ℝ 2 α)
    (hb : ContDiff ℝ 1 b) (hχ : ContDiff ℝ 1 χ) (hχ₀ : χ =ᶠ[𝓝 0] 0) (hσ : ContDiff ℝ 2 σ)
    (hbd₁ : ∀ θ, χ (normSq (α (σ (circleMap z₀ r₁ θ)))) = 1)
    (hbd₂ : ∀ θ, χ (normSq (α (σ (circleMap z₀ r₂ θ)))) = 1)
    (hne : ∀ z ∈ Metric.closedBall z₀ r₂ \ Metric.ball z₀ r₁, α (σ z) ≠ 0) :
    ∫ z in Metric.closedBall z₀ r₁,
        (cutoffCurrent χ b α (σ z)).compContinuousLinearMap (fderiv ℝ σ z) ![1, I] =
      ∫ z in Metric.closedBall z₀ r₂,
        (cutoffCurrent χ b α (σ z)).compContinuousLinearMap (fderiv ℝ σ z) ![1, I] :=
  integral_cutoffCurrent_comp_closedBall_eq_of_subset hr₁ (hr₁.trans hr) hα hb hχ hχ₀ hσ
    (Metric.closedBall_subset_closedBall hr) hbd₁ hbd₂ hne

/-- **Homotopy invariance of the disc charge.** Let `σ p`, for `p` in a preconnected set `S` of
parameters, be `C²` discs such that `σ p z` depends jointly continuously on `p ∈ S` and on `z` in
the boundary circle of a closed disc, and such that `χ(|α|²) = 1` along each `σ p` of that circle.
Then all the discs `σ p` carry the same charge. Only the boundary circles enter: along the family,
the interiors of the discs may cross the zeros of `α`, and need not vary continuously. -/
theorem integral_cutoffCurrent_comp_closedBall_eq_of_continuousOn {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {α : E → ℂ} {b : E → E [⋀^Fin 1]→L[ℝ] ℝ}
    {P : Type*} [TopologicalSpace P] {S : Set P} (hS : IsPreconnected S) {σ : P → ℂ → E}
    {z₀ : ℂ} {r : ℝ} (hr : 0 ≤ r) (hα : ContDiff ℝ 2 α) (hb : ContDiff ℝ 1 b)
    (hχ : ContDiff ℝ 1 χ) (hχ₀ : χ =ᶠ[𝓝 0] 0) (hσ : ∀ p ∈ S, ContDiff ℝ 2 (σ p))
    (hσc : ContinuousOn (Function.uncurry σ) (S ×ˢ Metric.sphere z₀ r))
    (hbd : ∀ p ∈ S, ∀ θ, χ (normSq (α (σ p (circleMap z₀ r θ)))) = 1) {p q : P} (hp : p ∈ S)
    (hq : q ∈ S) :
    ∫ z in Metric.closedBall z₀ r,
        (cutoffCurrent χ b α (σ p z)).compContinuousLinearMap (fderiv ℝ (σ p) z) ![1, I] =
      ∫ z in Metric.closedBall z₀ r,
        (cutoffCurrent χ b α (σ q z)).compContinuousLinearMap (fderiv ℝ (σ q) z) ![1, I] := by
  obtain ⟨m, hm, hI₁⟩ := exists_int_integral_cutoffCurrent_comp_closedBall hr hα hb hχ hχ₀
    (hσ p hp) (hbd p hp)
  obtain ⟨n, hn, hI₂⟩ := exists_int_integral_cutoffCurrent_comp_closedBall hr hα hb hχ hχ₀
    (hσ q hq) (hbd q hq)
  -- The boundary loops `α ∘ σ p ∘ circleMap z₀ r` form a continuous family of closed curves
  -- avoiding `0`.
  have h := Contour.windingNumber_eq_of_continuousOn_uncurry
    (H := fun p ↦ α ∘ σ p ∘ circleMap z₀ r) (a := -π) (b := π) (w := 0) hS
    (hα.continuous.comp_continuousOn (hσc.comp
      (continuousOn_fst.prodMk ((continuous_circleMap z₀ r).comp_continuousOn continuousOn_snd))
      fun x hx ↦ ⟨hx.1, circleMap_mem_sphere z₀ hr x.2⟩))
    (fun p hp ↦ IsPiecewiseC1On.of_contDiffOn
      ((hα.comp ((hσ p hp).comp (contDiff_circleMap z₀ r))).contDiffOn.of_le one_le_two))
    (fun p _ ↦ by simp only [Function.comp_apply, ← periodic_circleMap z₀ r (-π)]; ring_nf)
    (fun p hp θ _ ↦ ne_zero_of_cutoff_eq_one hχ₀ (hbd p hp θ)) hp hq
  rw [hm, hn, Int.cast_inj] at h
  rw [hI₁, hI₂, h]

/-- **The degree law of the disc charge.** Let `θ : ℂ → ℂ` be a `C²` map sending the
boundary circle of the closed disc `D₁` of radius `r₁` about `z₁` into the boundary circle of the
closed disc `D` of radius `r > 0` about `z₀`, and let `σ : ℂ → E` be a `C²` disc such that
`χ(|α|²) = 1` along `σ` of the boundary circle of `D`. Then the charge of `σ ∘ θ` on `D₁` is the
charge of `σ` on `D` multiplied by the integer degree `n` of `θ` on the boundary circles, the
winding number of `θ` along the boundary circle of `D₁` around `z₀`. Neither `θ (D₁) ⊆ D` nor any
condition on `θ` inside `D₁` is needed, and `n` may be negative for orientation-reversing `θ`. -/
theorem exists_int_integral_cutoffCurrent_comp_comp_closedBall_eq_mul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {α : E → ℂ} {b : E → E [⋀^Fin 1]→L[ℝ] ℝ}
    {σ : ℂ → E} {θ : ℂ → ℂ} {z₀ z₁ : ℂ} {r r₁ : ℝ} (hr : 0 < r) (hr₁ : 0 ≤ r₁)
    (hα : ContDiff ℝ 2 α) (hb : ContDiff ℝ 1 b) (hχ : ContDiff ℝ 1 χ) (hχ₀ : χ =ᶠ[𝓝 0] 0)
    (hσ : ContDiff ℝ 2 σ) (hθ : ContDiff ℝ 2 θ)
    (hθs : ∀ z ∈ Metric.sphere z₁ r₁, θ z ∈ Metric.sphere z₀ r)
    (hbd : ∀ t, χ (normSq (α (σ (circleMap z₀ r t)))) = 1) :
    ∃ n : ℤ, Contour.windingNumber (θ ∘ circleMap z₁ r₁) (-π) π z₀ = n ∧
      ∫ z in Metric.closedBall z₁ r₁,
          (cutoffCurrent χ b α (σ (θ z))).compContinuousLinearMap (fderiv ℝ (σ ∘ θ) z) ![1, I] =
        n * ∫ z in Metric.closedBall z₀ r,
          (cutoffCurrent χ b α (σ z)).compContinuousLinearMap (fderiv ℝ σ z) ![1, I] := by
  set ℓ := θ ∘ circleMap z₁ r₁ with hℓ
  have hℓs (t : ℝ) : ℓ t ∈ Metric.sphere z₀ r := hθs _ (circleMap_mem_sphere z₁ hr₁ t)
  -- Every point of the target circle is `circleMap z₀ r t` for some `t`.
  have hsphere {w : ℂ} (hw : w ∈ Metric.sphere z₀ r) : ∃ t, circleMap z₀ r t = w := by
    rwa [← Set.mem_range, range_circleMap, abs_of_pos hr]
  have hbd' (t : ℝ) : χ (normSq (α ((σ ∘ θ) (circleMap z₁ r₁ t)))) = 1 := by
    obtain ⟨t', ht'⟩ := hsphere (hθs _ (circleMap_mem_sphere z₁ hr₁ t))
    rw [Function.comp_apply, ← ht']
    exact hbd t'
  obtain ⟨m, hm, hI⟩ := exists_int_integral_cutoffCurrent_comp_closedBall hr.le hα hb hχ hχ₀ hσ hbd
  obtain ⟨k, hk, hI₁⟩ :=
    exists_int_integral_cutoffCurrent_comp_closedBall hr₁ hα hb hχ hχ₀ (hσ.comp hθ) hbd'
  have hℓc : ContDiff ℝ 1 ℓ := (hθ.comp (contDiff_circleMap z₁ r₁)).of_le one_le_two
  have hclosed : ℓ (-π) = ℓ π := by
    simp only [hℓ, Function.comp_apply, ← periodic_circleMap z₁ r₁ (-π)]
    ring_nf
  obtain ⟨n, hn⟩ := (IsPiecewiseC1On.of_contDiffOn hℓc.contDiffOn).exists_int_windingNumber
    hclosed fun t _ h ↦ by
      have := Metric.mem_sphere.1 (hℓs t)
      rw [h, dist_self] at this
      exact hr.ne this
  -- The boundary loop of `σ ∘ θ` is `α ∘ σ` along `ℓ`, which winds `n` times around the circle.
  have hw := Contour.windingNumber_comp_eq_mul_of_mem_sphere (g := α ∘ σ) hr
    (fun w _ ↦ ((hα.comp hσ).of_le one_le_two).contDiffAt)
    (fun w hw ↦ by
      obtain ⟨t, rfl⟩ := hsphere hw
      exact ne_zero_of_cutoff_eq_one hχ₀ (hbd t))
    hℓc hℓs hclosed (-π)
  simp only [hℓ, Function.comp_assoc] at hk hw
  have hπ : -π + 2 * π = π := by ring
  rw [hπ, hk, hn, hm] at hw
  refine ⟨n, hn, ?_⟩
  simp only [Function.comp_apply] at hI₁
  rw [hI₁, hI]
  have hkm : (k : ℝ) = n * m := by exact_mod_cast hw
  rw [hkm]
  ring

/-! ### Mollified charges and their limits -/

/-- **The disc charge as a pairing with a test field.** Let `σ` be a `C²` disc such that the
boundary circle of every translated disc `σ + p`, `‖p‖ ≤ δ`, lies in `{χ(|α|²) = 1}`, and let `ρ`
be a continuous weight of integral one supported in the closed ball of radius `δ` about `0`.
Then the charge of `σ` is the pairing of the cutoff current `Θ` with the mollified disc: on a
basis `e`,

`∫_D σ^* Θ = ∑ s, ∫ ξ_s(y) Θ(y)(e (s 0), e (s 1)) dμ(y)`,

where `ξ_s` are the coefficients `TauCeti.discMollification e ρ σ z₀ r s`, smooth and compactly
supported when `ρ` is. -/
theorem integral_cutoffCurrent_comp_closedBall_eq_sum_integral_discMollification_mul
    {E κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Fintype κ] {μ : Measure E} [μ.IsAddHaarMeasure]
    {α : E → ℂ} {b : E → E [⋀^Fin 1]→L[ℝ] ℝ} {σ : ℂ → E} {z₀ : ℂ} {r δ : ℝ} {ρ : E → ℝ}
    (e : Module.Basis κ ℝ E) (hr : 0 ≤ r) (hα : ContDiff ℝ 2 α) (hb : ContDiff ℝ 1 b)
    (hχ : ContDiff ℝ 1 χ) (hχ₀ : χ =ᶠ[𝓝 0] 0) (hσ : ContDiff ℝ 2 σ) (hρ : Continuous ρ)
    (hρδ : tsupport ρ ⊆ Metric.closedBall 0 δ) (hρ₁ : ∫ p, ρ p ∂μ = 1)
    (hbd : ∀ p ∈ Metric.closedBall (0 : E) δ, ∀ θ,
      χ (normSq (α (σ (circleMap z₀ r θ) + p))) = 1) :
    ∫ z in Metric.closedBall z₀ r,
        (cutoffCurrent χ b α (σ z)).compContinuousLinearMap (fderiv ℝ σ z) ![1, I] =
      ∑ s : Fin 2 → κ, ∫ y, discMollification e ρ σ z₀ r s y *
        cutoffCurrent χ b α y (fun i ↦ e (s i)) ∂μ := by
  have hΘ : Continuous (cutoffCurrent χ b α) :=
    (contDiff_cutoffCurrent (m := 0) (n := 1) hα hb hχ hχ₀ (by norm_num)).continuous
  have hρc : HasCompactSupport ρ :=
    (isCompact_closedBall 0 δ).of_isClosed_subset (isClosed_tsupport ρ) hρδ
  -- A weight of integral one is nonzero, so `δ ≥ 0`.
  have hδ : 0 ≤ δ := by
    by_contra h
    have h₀ : tsupport ρ = ∅ :=
      subset_empty_iff.1 (hρδ.trans (Metric.closedBall_eq_empty.2 (not_le.1 h)).subset)
    rw [tsupport_eq_empty_iff] at h₀
    simp [h₀] at hρ₁
  -- All the translated discs `σ + p`, `‖p‖ ≤ δ`, carry the charge of `σ`.
  have hconst (p : E) (hp : p ∈ Metric.closedBall 0 δ) :
      ∫ z in Metric.closedBall z₀ r,
          cutoffCurrent χ b α (σ z + p) ![fderiv ℝ σ z 1, fderiv ℝ σ z I] =
        ∫ z in Metric.closedBall z₀ r,
          cutoffCurrent χ b α (σ z) ![fderiv ℝ σ z 1, fderiv ℝ σ z I] := by
    have h := integral_cutoffCurrent_comp_closedBall_eq_of_continuousOn
      (convex_closedBall (0 : E) δ).isPreconnected (σ := fun p z ↦ σ z + p) hr hα hb hχ hχ₀
      (fun _ _ ↦ hσ.add contDiff_const)
      ((hσ.continuous.comp continuous_snd).add continuous_fst).continuousOn hbd hp
      (Metric.mem_closedBall_self hδ)
    simpa only [fderiv_add_const, compContinuousLinearMap_apply_vecCons_two, add_zero] using h
  have hρc' (p : E) : ρ p * ∫ z in Metric.closedBall z₀ r,
        cutoffCurrent χ b α (σ z + p) ![fderiv ℝ σ z 1, fderiv ℝ σ z I] =
      ρ p * ∫ z in Metric.closedBall z₀ r,
        cutoffCurrent χ b α (σ z) ![fderiv ℝ σ z 1, fderiv ℝ σ z I] := by
    by_cases hp : p ∈ tsupport ρ
    · rw [hconst p (hρδ hp)]
    · rw [image_eq_zero_of_notMem_tsupport hp, zero_mul, zero_mul]
  rw [← integral_mul_setIntegral_add_eq_sum_integral_discMollification_mul (b := e) hΘ hρ hρc
    (hσ.of_le one_le_two)]
  simp_rw [hρc', integral_mul_const, hρ₁, one_mul, compContinuousLinearMap_apply_vecCons_two]

/-- **Stabilization of the disc charges.** Let `(bₖ, αₖ)` be a family of abelian Higgs pairs along
a filter `l`, with cutoff currents `Θₖ`, and let `σ` be a `C²` disc. Suppose that eventually
along `l` the boundary circles of all the translated discs `σ + p`, `‖p‖ ≤ δ`, lie in
`{χ(|αₖ|²) = 1}`, and that the coefficients of `Θₖ` converge as distributions: for every smooth
compactly supported `φ` and every pair of vectors `m`, the pairings `∫ φ(y) Θₖ(y)(m) dμ(y)`
converge. Then the integer charges of `σ` are eventually constant: there is an integer `n` with
`∫_D σ^* Θₖ = 2π n` eventually along `l`. -/
theorem exists_int_eventually_integral_cutoffCurrent_comp_closedBall_eq {ι E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {l : Filter ι} [l.NeBot]
    {α : ι → E → ℂ} {b : ι → E → E [⋀^Fin 1]→L[ℝ] ℝ} {σ : ℂ → E} {z₀ : ℂ} {r δ : ℝ}
    (hr : 0 ≤ r) (hδ : 0 < δ) (hα : ∀ k, ContDiff ℝ 2 (α k)) (hb : ∀ k, ContDiff ℝ 1 (b k))
    (hχ : ContDiff ℝ 1 χ) (hχ₀ : χ =ᶠ[𝓝 0] 0) (hσ : ContDiff ℝ 2 σ)
    (hbd : ∀ᶠ k in l, ∀ p ∈ Metric.closedBall (0 : E) δ, ∀ θ,
      χ (normSq (α k (σ (circleMap z₀ r θ) + p))) = 1)
    (hlim : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → ∀ m : Fin 2 → E,
      ∃ L, Tendsto (fun k ↦ ∫ y, φ y * cutoffCurrent χ (b k) (α k) y m ∂μ) l (𝓝 L)) :
    ∃ n : ℤ, ∀ᶠ k in l, ∫ z in Metric.closedBall z₀ r,
      (cutoffCurrent χ (b k) (α k) (σ z)).compContinuousLinearMap (fderiv ℝ σ z) ![1, I] =
        2 * π * n := by
  set e := Module.finBasis ℝ E
  let f : ContDiffBump (0 : E) := ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  set c := fun k ↦ ∫ z in Metric.closedBall z₀ r,
    (cutoffCurrent χ (b k) (α k) (σ z)).compContinuousLinearMap (fderiv ℝ σ z) ![1, I]
  -- The charges converge, to the limit of the pairings with the mollified disc.
  choose L hL using fun s : Fin 2 → Fin (Module.finrank ℝ E) ↦
    hlim (discMollification e (f.normed μ) σ z₀ r s)
      (contDiff_discMollification f.contDiff_normed (hσ.of_le one_le_two) s)
      (hasCompactSupport_discMollification f.hasCompactSupport_normed hσ.continuous s)
      fun i ↦ e (s i)
  have hc : Tendsto c l (𝓝 (∑ s, L s)) :=
    (tendsto_finsetSum _ fun s _ ↦ hL s).congr' (hbd.mono fun k hk ↦
      (integral_cutoffCurrent_comp_closedBall_eq_sum_integral_discMollification_mul e hr (hα k)
        (hb k) hχ hχ₀ hσ f.continuous_normed f.tsupport_normed_eq.subset f.integral_normed
        hk).symm)
  -- Eventually the charges lie in `2πℤ`.
  have hint : ∀ᶠ k in l, ∃ n : ℤ, c k = 2 * π * n := hbd.mono fun k hk ↦ by
    obtain ⟨n, -, hn⟩ := exists_int_integral_cutoffCurrent_comp_closedBall hr (hα k) (hb k) hχ
      hχ₀ hσ fun θ ↦ by simpa using hk 0 (Metric.mem_closedBall_self hδ.le) θ
    exact ⟨n, hn⟩
  exact hc.exists_eventually_eq_mul_intCast (by positivity) hint

end TauCeti.SeibergWitten
