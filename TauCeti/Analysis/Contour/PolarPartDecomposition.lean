/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.HomologyCauchy
public import TauCeti.Analysis.Contour.MeromorphicLaurent

/-!
# Polar-part decompositions

A **polar-part decomposition** of `f` on `U` at the finite singular set `S`: for each `s ∈ S` an
explicit finite Laurent tail `polarPart s z = ∑ k, coeff s k / (z - s)^(k+1)`, such that `f`
minus the total polar part extends to a function differentiable on all of `U`, and the residue at
each `s` is the first Laurent coefficient. This bundles exactly the data the generalized residue
theorem manipulates: the analytic remainder integrates to zero around any null-homologous closed
curve — even one passing through the poles — so the principal value of `∮ f` reduces to the polar
parts.

## Main definitions

* `Contour.PolarPartDecomposition f S U` — the decomposition data: polar parts, orders, Laurent
  coefficients, the residue identification, and the analytic remainder.
* `Contour.meromorphicPolarPartTotal` — the sum of the canonical per-point polar parts over `S`.
* `Contour.PolarPartDecomposition.ofMeromorphic` — every `f` differentiable on `U \ S` and
  meromorphic at each `s ∈ S` has a polar-part decomposition, built from the canonical Laurent
  data of `MeromorphicLaurent.lean`.

## Main results

* `Contour.PolarPartDecomposition.intervalIntegral_deriv_smul_analyticRemainder_eq_zero` — the
  contour integral of the analytic remainder along a closed null-homologous piecewise-`C¹` curve
  in `U` vanishes, by the homology Cauchy theorem.

## Provenance

The structure is migrated from `PolarPartDecomposition` of `HungerbuhlerWasem.lean` in the
AINTLIB `LeanModularForms` development; the remainder-integral theorem is its
`analyticRemainder_contourIntegral_zero`, which there re-runs Dixon's argument inline and here is
a direct application of `Contour.homologyCauchyTheorem`. The constructor is migrated from
`polarPartDecomposition_of_meromorphic` of `LaurentExtraction.lean` there, with the ℂ-indexed
case splits replaced by `S`-indexed data throughout. See N. Hungerbühler, M. Wasem, *Non-integer
valued winding numbers and a generalized Residue Theorem*, arXiv:1808.00997, §3.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Filter MeasureTheory Set Topology

open scoped Interval

/-- **Polar-part decomposition** of `f` on `U` at the finite singular set `S`: explicit finite
Laurent tails at the points of `S` whose removal from `f` leaves a function differentiable on all
of `U`, with the residue at each `s ∈ S` read off as the first Laurent coefficient. The data is
indexed by `S`, so a decomposition carries nothing beyond what its laws constrain; the polar part
is pinned for every `z` (at `z = s` the Laurent sum takes the junk value `0`, by division by
zero in `ℂ`). -/
structure PolarPartDecomposition (f : ℂ → ℂ) (S : Finset ℂ) (U : Set ℂ) where
  /-- The order of the polar part at each pole (`0` for no pole). -/
  order : S → ℕ
  /-- The Laurent coefficients of the polar part at each pole. -/
  coeff : (s : S) → Fin (order s) → ℂ
  /-- The polar part at each pole, as a function of `z`. -/
  polarPart : S → ℂ → ℂ
  /-- The polar part at `s` is the explicit Laurent sum `∑ k, coeff s k / (z - s)^(k+1)`. -/
  polarPart_eq : ∀ (s : S) (z : ℂ),
    polarPart s z = ∑ k : Fin (order s), coeff s k / (z - (s : ℂ)) ^ (k.val + 1)
  /-- The residue at `s ∈ S` is the first Laurent coefficient, or zero for an empty polar
  part. -/
  residue_eq : ∀ s : S,
    residue f s = if h : 0 < order s then coeff s ⟨0, h⟩ else 0
  /-- The function `f` minus the total polar part, extended to all of `U`. -/
  analyticRemainder : ℂ → ℂ
  /-- The analytic remainder is differentiable on all of `U`. -/
  analyticRemainder_differentiableOn : DifferentiableOn ℂ analyticRemainder U
  /-- Off the singular set, `f` is the analytic remainder plus the total polar part. -/
  f_eq : ∀ z ∈ U \ (↑S : Set ℂ),
    f z = analyticRemainder z + ∑ s ∈ S.attach, polarPart s z

namespace PolarPartDecomposition

variable {f : ℂ → ℂ} {S : Finset ℂ} {U : Set ℂ}

/-- **The analytic remainder integrates to zero** along any closed null-homologous
piecewise-`C¹` curve in `U` — even one passing through the poles of `f`, since the remainder
extends differentiably to all of `U`. The homology Cauchy theorem applied to the remainder. -/
theorem intervalIntegral_deriv_smul_analyticRemainder_eq_zero
    (decomp : PolarPartDecomposition f S U)
    (hU : IsOpen U) {γ : ℝ → ℂ} {a b : ℝ} (hγ_pc1 : IsPiecewiseC1On γ a b)
    (hγ : ∀ t ∈ uIcc a b, γ t ∈ U) (hclosed : γ a = γ b)
    (hnull : IsNullHomologous γ a b U) :
    ∫ t in a..b, deriv γ t • decomp.analyticRemainder (γ t) = 0 :=
  homologyCauchyTheorem hU γ a b hγ_pc1 hγ hclosed decomp.analyticRemainder_differentiableOn hnull

end PolarPartDecomposition

/-- **The total polar part** over the singular set: the sum of the canonical per-point polar
parts. -/
def meromorphicPolarPartTotal {f : ℂ → ℂ} {S : Finset ℂ}
    (hMero : ∀ s ∈ S, MeromorphicAt f s) (z : ℂ) : ℂ :=
  ∑ s ∈ S.attach, meromorphicPolarPartAt (hMero s.1 s.2) z

/-- The polar parts of the other poles are analytic at `s`. -/
private theorem otherPolar_analyticAt {f : ℂ → ℂ} {S : Finset ℂ}
    (hMero : ∀ s ∈ S, MeromorphicAt f s) {s : ℂ} (_hs : s ∈ S) :
    AnalyticAt ℂ (fun z => ∑ s' ∈ S.attach.filter (fun s' => s'.1 ≠ s),
      meromorphicPolarPartAt (hMero s'.1 s'.2) z) s := by
  refine Finset.analyticAt_fun_sum _ fun s' hs' => ?_
  exact meromorphicPolarPartAt_analyticAt_of_ne (hMero s'.1 s'.2)
    ((Finset.mem_filter.mp hs').2).symm

/-- Near each pole, `f` minus the total polar part has an analytic germ: the per-point analytic
part minus the other poles' (locally analytic) polar parts. -/
private theorem exists_analyticAt_sub_polarPartTotal {f : ℂ → ℂ} {S : Finset ℂ}
    (hMero : ∀ s ∈ S, MeromorphicAt f s) {s : ℂ} (hs : s ∈ S) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g s ∧
      ∀ᶠ z in 𝓝[≠] s, f z - meromorphicPolarPartTotal hMero z = g z := by
  refine ⟨fun z => meromorphicAnalyticPartAt (hMero s hs) z -
      ∑ s' ∈ S.attach.filter (fun s' => s'.1 ≠ s),
        meromorphicPolarPartAt (hMero s'.1 s'.2) z,
    (meromorphicAnalyticPartAt_analyticAt (hMero s hs)).sub
      (otherPolar_analyticAt hMero hs), ?_⟩
  filter_upwards [eventuallyEq_meromorphicAnalyticPartAt_add_meromorphicPolarPartAt
    (hMero s hs)] with z hz
  rw [hz]
  suffices h_total : meromorphicPolarPartTotal hMero z =
      meromorphicPolarPartAt (hMero s hs) z +
        ∑ s' ∈ S.attach.filter (fun s' => s'.1 ≠ s),
          meromorphicPolarPartAt (hMero s'.1 s'.2) z by
    rw [h_total]
    ring
  unfold meromorphicPolarPartTotal
  rw [← Finset.sum_filter_add_sum_filter_not S.attach (fun s' => s'.1 = s)]
  congr 1
  rw [show S.attach.filter (fun s' => s'.1 = s) = {⟨s, hs⟩} from by
    ext s'
    simp only [Finset.mem_filter, Finset.mem_attach, true_and, Finset.mem_singleton]
    exact ⟨fun h => Subtype.ext h, fun h => by rw [h]⟩]
  rw [Finset.sum_singleton]

/-- Off the singular set, the extended remainder is `f` minus the total polar part. -/
private theorem remainder_eventuallyEq_off {f : ℂ → ℂ} {S : Finset ℂ}
    (hMero : ∀ s ∈ S, MeromorphicAt f s) {z : ℂ} (hz : z ∉ (↑S : Set ℂ)) :
    (fun w => if w ∈ (↑S : Set ℂ) then
        limUnder (𝓝[≠] w) (fun u => f u - meromorphicPolarPartTotal hMero u)
      else f w - meromorphicPolarPartTotal hMero w) =ᶠ[𝓝 z]
      fun w => f w - meromorphicPolarPartTotal hMero w := by
  filter_upwards [(S.finite_toSet.isClosed.isOpen_compl).mem_nhds hz] with w hw
  rw [if_neg hw]

/-- A punctured neighbourhood eventually avoids a finite set. -/
private theorem eventually_notMem_nhdsNE (S : Finset ℂ) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, w ∉ (↑S : Set ℂ) := by
  have hcl : IsClosed ((↑S \ {z} : Set ℂ)) := (S.finite_toSet.subset sdiff_subset).isClosed
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds
    (hcl.isOpen_compl.mem_nhds (by simp)), self_mem_nhdsWithin] with w hwc hwne hwS
  exact hwc ⟨hwS, hwne⟩

/-- At a singular point, the limit-patched remainder is differentiable: on a punctured
neighbourhood it agrees with the analytic germ of `f` minus the total polar part
(`exists_analyticAt_sub_polarPartTotal`), and at the point itself it takes the germ's value. -/
private theorem remainder_differentiableAt_mem {f : ℂ → ℂ} {S : Finset ℂ}
    (hMero : ∀ s ∈ S, MeromorphicAt f s) {z : ℂ} (hzS : z ∈ (↑S : Set ℂ)) :
    DifferentiableAt ℂ (fun w => if w ∈ (↑S : Set ℂ) then
        limUnder (𝓝[≠] w) (fun u => f u - meromorphicPolarPartTotal hMero u)
      else f w - meromorphicPolarPartTotal hMero w) z := by
  obtain ⟨g, hg_an, hg_eq⟩ := exists_analyticAt_sub_polarPartTotal hMero hzS
  have h1 : ∀ᶠ w in 𝓝[≠] z, (if w ∈ (↑S : Set ℂ) then
      limUnder (𝓝[≠] w) (fun u => f u - meromorphicPolarPartTotal hMero u)
    else f w - meromorphicPolarPartTotal hMero w) = g w := by
    filter_upwards [eventually_notMem_nhdsNE S z, hg_eq] with w hwS hwg
    rw [if_neg hwS]
    exact hwg
  have h2 : (if z ∈ (↑S : Set ℂ) then
      limUnder (𝓝[≠] z) (fun u => f u - meromorphicPolarPartTotal hMero u)
    else f z - meromorphicPolarPartTotal hMero z) = g z := by
    rw [if_pos hzS]
    refine Filter.Tendsto.limUnder_eq ?_
    refine Filter.Tendsto.congr' ?_
      (hg_an.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    filter_upwards [hg_eq] with u hu using hu.symm
  have h_full : (fun w => if w ∈ (↑S : Set ℂ) then
      limUnder (𝓝[≠] w) (fun u => f u - meromorphicPolarPartTotal hMero u)
    else f w - meromorphicPolarPartTotal hMero w) =ᶠ[𝓝 z] g := by
    rw [Filter.EventuallyEq, ← nhdsNE_sup_pure z, Filter.eventually_sup]
    exact ⟨h1, Filter.eventually_pure.mpr h2⟩
  exact h_full.differentiableAt_iff.mpr hg_an.differentiableAt

namespace PolarPartDecomposition

/-- **The decomposition of a meromorphic integrand.** From `f` differentiable on `U \ S` and
meromorphic at each `s ∈ S`, the canonical Laurent data assembles into a
`PolarPartDecomposition f S U`: the orders are the canonical polar orders — so they are
evaluable by callers, in particular `1` at simple poles — and the analytic remainder is
`f` minus the total polar part, extended across the poles by its limits. -/
noncomputable def ofMeromorphic {f : ℂ → ℂ} {S : Finset ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f (U \ (↑S : Set ℂ))) (hMero : ∀ s ∈ S, MeromorphicAt f s) :
    PolarPartDecomposition f S U where
  order s := meromorphicPolarOrderAt f s
  coeff s k := meromorphicPolarCoeffAt (hMero s s.2) k
  polarPart s z := meromorphicPolarPartAt (hMero s s.2) z
  polarPart_eq s z := meromorphicPolarPartAt_eq_sum (hMero s s.2) z
  residue_eq s := by
    rcases Nat.eq_zero_or_pos (meromorphicPolarOrderAt f s) with h0 | hpos
    · rw [dif_neg (by omega)]
      refine residue_eq_zero_of_meromorphicOrderAt_nonneg ?_
      have hle := neg_meromorphicPolarOrderAt_le f (s : ℂ)
      rw [h0] at hle
      simpa using hle
    · rw [dif_pos hpos]
      exact (meromorphicPolarCoeffAt_zero_eq_residue (hMero s s.2) hpos).symm
  analyticRemainder := fun z => if z ∈ (↑S : Set ℂ) then
      limUnder (𝓝[≠] z) (fun u => f u - meromorphicPolarPartTotal hMero u)
    else f z - meromorphicPolarPartTotal hMero z
  analyticRemainder_differentiableOn := by
    intro z hzU
    by_cases hzS : z ∈ (↑S : Set ℂ)
    · exact (remainder_differentiableAt_mem hMero hzS).differentiableWithinAt
    · have h_diff : DifferentiableAt ℂ
          (fun w => f w - meromorphicPolarPartTotal hMero w) z := by
        refine ((hf z ⟨hzU, hzS⟩).differentiableAt ?_).sub ?_
        · exact (hU.sdiff S.finite_toSet.isClosed).mem_nhds ⟨hzU, hzS⟩
        · refine DifferentiableAt.fun_sum fun s' _ => ?_
          exact (meromorphicPolarPartAt_analyticAt_of_ne (hMero s'.1 s'.2)
            (fun h => hzS (by rw [h]; exact Finset.mem_coe.mpr s'.2))).differentiableAt
      exact (h_diff.congr_of_eventuallyEq
        (remainder_eventuallyEq_off hMero hzS)).differentiableWithinAt
  f_eq z hz := by
    rw [if_neg hz.2]
    unfold meromorphicPolarPartTotal
    ring

end PolarPartDecomposition

end TauCeti.Contour

end
