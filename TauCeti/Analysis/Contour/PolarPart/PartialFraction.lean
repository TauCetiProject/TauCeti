/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.PolarPart.SimplePole
public import TauCeti.Analysis.Contour.Residue.SimplePole
import Mathlib.Analysis.Complex.Liouville

/-!
# Partial fractions for functions with finitely many simple poles

A function on `ℂ` that is holomorphic away from a finite set `S`, has at most simple poles at the
points of `S`, and tends to `0` at infinity is the sum of its principal parts:

`f z = ∑ s ∈ S, residue f s / (z - s)` for `z ∉ S`.

Indeed, by the simple-pole decomposition `exists_simplePoleDecomposition`, `f` minus this sum
extends to an entire function; that function tends to `0` at infinity, so it vanishes by
Liouville's theorem.

The residues can be prescribed through the elementary limits `(z - s) * f z → c s`. A
punctured limit of this kind already makes `f` meromorphic with at most a simple pole at `s`
(`TauCeti.Contour.meromorphicAt_of_tendsto_sub_mul`), so the identification needs no meromorphy
hypothesis.
Conversely, every such sum is holomorphic off `S`, has these limits and tends to `0` at infinity.
This gives the characterization `eqOn_sum_div_sub_iff`.

This is how one identifies a function from its singularities and its behaviour at infinity. For
example, the pre-Schwarzian derivative `F'' / F'` of a conformal map `F` from the upper half-plane
onto a polygon continues by reflection to `ℂ` minus the prevertices. There it has simple poles
whose residues are determined by the interior angles, and it tends to `0` at infinity. So the
characterization identifies it with the Schwarz--Christoffel expression
`∑ i, e i / (z - a i)`, which is the derivation of the Schwarz--Christoffel formula.

## Main results

* `TauCeti.Contour.differentiableOn_sum_div_sub`, `TauCeti.Contour.tendsto_sum_div_sub_cobounded`
  and `TauCeti.Contour.tendsto_sub_mul_sum_div_sub` -- the sum `z ↦ ∑ s ∈ S, c s / (z - s)` is
  holomorphic off `S`, tends to `0` at infinity and has the limit `c s` of `(z - s) * _` at `s`.
* `TauCeti.Contour.eqOn_sum_residue_div_sub` -- a function with finitely many at most simple poles
  that tends to `0` at infinity is the sum of its principal parts.
* `TauCeti.Contour.eqOn_sum_div_sub_of_tendsto` -- the same with prescribed residues, stated
  through the limits of `(z - s) * f z`.
* `TauCeti.Contour.eqOn_sum_div_sub_iff` -- the resulting characterization of the functions
  `z ↦ ∑ s ∈ S, c s / (z - s)` off `S`.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 4, Section 3.1 (Liouville's theorem), and Ch. 6, Section 2
  (the derivation of the Schwarz--Christoffel formula).
-/

public section

noncomputable section

namespace TauCeti.Contour

open Bornology Filter Set Topology

/-- The complement of a finite set is a punctured neighbourhood of every point. -/
private theorem compl_mem_nhdsNE (S : Finset ℂ) (z₀ : ℂ) : (↑S : Set ℂ)ᶜ ∈ 𝓝[≠] z₀ :=
  mem_codiscrete_iff_forall_mem_nhdsNE.mp (compl_finite_mem_codiscreteWithin S.finite_toSet) z₀

/-- The complement of a finite set is a neighbourhood of infinity. -/
private theorem compl_mem_cobounded (S : Finset ℂ) : (↑S : Set ℂ)ᶜ ∈ cobounded ℂ :=
  isBounded_def.mp S.finite_toSet.isBounded

/-! ### The partial-fraction sum -/

/-- The partial-fraction sum `z ↦ ∑ s ∈ S, c s / (z - s)` is holomorphic off `S`. -/
theorem differentiableOn_sum_div_sub (S : Finset ℂ) (c : ℂ → ℂ) :
    DifferentiableOn ℂ (fun z => ∑ s ∈ S, c s / (z - s)) (↑S)ᶜ := by
  intro z hz
  refine DifferentiableAt.differentiableWithinAt (DifferentiableAt.fun_sum fun s hs => ?_)
  refine (differentiableAt_const _).div (differentiableAt_id.sub_const s) (sub_ne_zero.2 ?_)
  rintro rfl
  exact hz hs

/-- The partial-fraction sum `z ↦ ∑ s ∈ S, c s / (z - s)` tends to `0` at infinity. -/
theorem tendsto_sum_div_sub_cobounded (S : Finset ℂ) (c : ℂ → ℂ) :
    Tendsto (fun z => ∑ s ∈ S, c s / (z - s)) (cobounded ℂ) (𝓝 0) := by
  have h := tendsto_finsetSum S fun s _ =>
    (tendsto_inv₀_cobounded.comp (tendsto_sub_const_cobounded s)).const_mul (c s)
  simpa [div_eq_mul_inv] using h

/-- At a point `s ∈ S`, the partial-fraction sum `z ↦ ∑ t ∈ S, c t / (z - t)` has residue
`c s` in the sense of the elementary limit: `(z - s) * ∑ t ∈ S, c t / (z - t) → c s`. -/
theorem tendsto_sub_mul_sum_div_sub {S : Finset ℂ} (c : ℂ → ℂ) {s : ℂ} (hs : s ∈ S) :
    Tendsto (fun z => (z - s) * ∑ t ∈ S, c t / (z - t)) (𝓝[≠] s) (𝓝 (c s)) := by
  -- The terms with `t ≠ s` are continuous at `s`, so `(z - s)` kills them in the limit.
  have hrest : Tendsto (fun z => ∑ t ∈ S.erase s, c t / (z - t)) (𝓝 s)
      (𝓝 (∑ t ∈ S.erase s, c t / (s - t))) :=
    tendsto_finsetSum _ fun t ht =>
      (continuousAt_const.div (continuousAt_id.sub continuousAt_const)
        (sub_ne_zero.2 (Finset.ne_of_mem_erase ht).symm)).tendsto
  have hlin : Tendsto (fun z : ℂ => z - s) (𝓝[≠] s) (𝓝 0) := by
    simpa using ((continuous_sub_right s).tendsto s).mono_left nhdsWithin_le_nhds
  have hlim := (tendsto_const_nhds (x := c s)).add
    (hlin.mul (hrest.mono_left nhdsWithin_le_nhds))
  rw [zero_mul, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [← Finset.add_sum_erase S _ hs, mul_add, mul_div_cancel₀ _ (sub_ne_zero.2 hz)]

/-! ### Identification by Liouville's theorem -/

/-- **Partial fractions for simple poles.** If `f` is holomorphic off a finite set `S`, has at
most a simple pole at each point of `S` and tends to `0` at infinity, then off `S` it is the sum of
its principal parts, `f z = ∑ s ∈ S, residue f s / (z - s)`.

Points of `S` at which `f` is analytic are allowed; their residues vanish. -/
theorem eqOn_sum_residue_div_sub {f : ℂ → ℂ} {S : Finset ℂ}
    (hf : DifferentiableOn ℂ f (↑S)ᶜ) (hmero : ∀ s ∈ S, MeromorphicAt f s)
    (horder : ∀ s ∈ S, ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f s)
    (hlim : Tendsto f (cobounded ℂ) (𝓝 0)) :
    EqOn f (fun z => ∑ s ∈ S, residue f s / (z - s)) (↑S)ᶜ := by
  rw [compl_eq_univ_sdiff] at hf ⊢
  obtain ⟨g, hg, hfg⟩ := exists_simplePoleDecomposition isOpen_univ hf hmero horder
  -- The entire remainder `g` agrees with `f` minus the principal parts near infinity.
  have hgf : (fun z => f z - ∑ s ∈ S, residue f s / (z - s)) =ᶠ[cobounded ℂ] g := by
    filter_upwards [compl_mem_cobounded S] with z hz
    rw [hfg z (by rwa [← compl_eq_univ_sdiff]), add_sub_cancel_right]
  have hg0 : Tendsto g (cocompact ℂ) (𝓝 0) := by
    rw [← Metric.cobounded_eq_cocompact]
    simpa using (hlim.sub (tendsto_sum_div_sub_cobounded S (residue f))).congr' hgf
  intro z hz
  rw [hfg z hz, (differentiableOn_univ.mp hg).apply_eq_of_tendsto_cocompact z hg0, zero_add]

/-- **Partial fractions with prescribed residues.** If `f` is holomorphic off a finite set `S`,
`(z - s) * f z → c s` as `z → s` for each `s ∈ S`, and `f` tends to `0` at infinity, then
`f z = ∑ s ∈ S, c s / (z - s)` for every `z ∉ S`. -/
theorem eqOn_sum_div_sub_of_tendsto {f : ℂ → ℂ} {S : Finset ℂ} {c : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (↑S)ᶜ)
    (hpole : ∀ s ∈ S, Tendsto (fun z => (z - s) * f z) (𝓝[≠] s) (𝓝 (c s)))
    (hlim : Tendsto f (cobounded ℂ) (𝓝 0)) :
    EqOn f (fun z => ∑ s ∈ S, c s / (z - s)) (↑S)ᶜ := by
  have hopen : IsOpen (↑S : Set ℂ)ᶜ := S.finite_toSet.isClosed.isOpen_compl
  have hmero (s : ℂ) (hs : s ∈ S) : MeromorphicAt f s := by
    refine meromorphicAt_of_tendsto_sub_mul ?_ (hpole s hs)
    filter_upwards [compl_mem_nhdsNE S s] with z hz
    exact hf.differentiableAt (hopen.mem_nhds hz)
  intro z hz
  rw [eqOn_sum_residue_div_sub hf hmero
    (fun s hs => neg_one_le_meromorphicOrderAt_of_tendsto_sub_mul (hmero s hs) (hpole s hs))
    hlim hz]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [residue_eq_of_tendsto_sub_mul (hmero s hs) (hpole s hs)]

/-- **Characterization of partial-fraction sums.** Off a finite set `S`, a function `f` agrees
with `z ↦ ∑ s ∈ S, c s / (z - s)` if and only if it is holomorphic off `S`, satisfies
`(z - s) * f z → c s` as `z → s` for each `s ∈ S`, and tends to `0` at infinity. -/
theorem eqOn_sum_div_sub_iff {f : ℂ → ℂ} {S : Finset ℂ} {c : ℂ → ℂ} :
    EqOn f (fun z => ∑ s ∈ S, c s / (z - s)) (↑S)ᶜ ↔
      DifferentiableOn ℂ f (↑S)ᶜ ∧
        (∀ s ∈ S, Tendsto (fun z => (z - s) * f z) (𝓝[≠] s) (𝓝 (c s))) ∧
        Tendsto f (cobounded ℂ) (𝓝 0) := by
  refine ⟨fun h => ⟨(differentiableOn_sum_div_sub S c).congr h, fun s hs => ?_, ?_⟩,
    fun ⟨hf, hpole, hlim⟩ => eqOn_sum_div_sub_of_tendsto hf hpole hlim⟩
  · refine (tendsto_sub_mul_sum_div_sub c hs).congr' ?_
    filter_upwards [compl_mem_nhdsNE S s] with z hz
    rw [h hz]
  · refine (tendsto_sum_div_sub_cobounded S c).congr' ?_
    filter_upwards [compl_mem_cobounded S] with z hz
    exact (h hz).symm

end TauCeti.Contour

end
