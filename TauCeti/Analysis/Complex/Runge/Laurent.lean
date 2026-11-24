/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import TauCeti.Analysis.Complex.Laurent.Expansion
public import TauCeti.Analysis.Complex.Runge.SimpleFraction
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Polynomial
import TauCeti.Analysis.Calculus.FDeriv.Add
import TauCeti.Analysis.Complex.HolomorphicFunctions.Basic

/-!
# Runge approximation of negative Laurent series and exterior holomorphic functions

Let `K` be a compact subset of an open set `Ω ⊆ ℂ` that is filled in `Ω` (`TauCeti.IsFilledIn K Ω`),
and let `F` be a complex normed space. Building on simple-fraction Runge approximation
(`TauCeti.IsFilledIn.exists_differentiableOn_norm_inv_sub_lt`) and Laurent expansions on concentric
annuli (`TauCeti.HasLaurentSeriesOnAnnulus`), this file proves uniform approximation on `K` by
functions complex-differentiable on `Ω` for:

* scalar polynomials `z ↦ P.eval (z - a)⁻¹` and powers `z ↦ ((z - a)⁻¹) ^ n` when `a ∉ K`;
* vector-valued negative-power terms `z ↦ (z - a) ^ (-(n : ℤ)) • v` in `F` when `a ∉ K`;
* negative Laurent series `TauCeti.laurentNegPart b a : ℂ → F` (for complete `F`) whenever `K` is
  disjoint from the inner closed disk `Metric.closedBall a r`;
* arbitrary functions `f : ℂ → F` (for complete `F`) complex-differentiable on
  `(Metric.closedBall a r)ᶜ` with `Disjoint K (Metric.closedBall a r)` — in particular on the
  punctured plane `{a}ᶜ` when `a ∉ K` — as well as finite sums of such punctured-plane functions.

These approximation results supply the compact-exhaustion correction terms in the global
Mittag-Leffler and prescribed-isolated-singularities theorems.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorems 11.1 and 12.1.
-/

public section

open Filter Metric Polynomial Set
open scoped ENNReal Topology

namespace TauCeti

section NormedSpace

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {K Ω : Set ℂ}

/-- **Runge approximation for polynomials in `(z - a)⁻¹`.** On a compact set `K` filled in an open
set `Ω ⊆ ℂ`, any polynomial in `(z - a)⁻¹` with `a ∉ K` is uniformly approximable on `K` by
functions complex-differentiable on `Ω`. -/
theorem IsFilledIn.exists_differentiableOn_norm_eval_inv_sub_lt (hfill : IsFilledIn K Ω)
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) {a : ℂ} (ha : a ∉ K) (P : ℂ[X])
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ K, ‖P.eval (z - a)⁻¹ - g z‖ < ε := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let U : TopologicalSpace.Opens ℂ := ⟨Ω, hΩ⟩
  let ρ := ContinuousMap.compRightAlgHom ℂ ℂ
    (⟨Set.inclusion hKΩ, continuous_inclusion hKΩ⟩ : C(K, U))
  let φ := ρ.comp (holomorphicFunctions U).val
  let S := φ.range.topologicalClosure
  let w : C(K, ℂ) := ⟨fun z : K => ((z : ℂ) - a)⁻¹,
    (continuous_subtypeVal.sub continuous_const).inv₀ fun z =>
      sub_ne_zero.mpr fun h : (z : ℂ) = a => ha (h ▸ z.property)⟩
  have hw : w ∈ S := Metric.mem_closure_iff.mpr fun δ hδ => by
    obtain ⟨g₀, hg₀, hbound⟩ := hfill.exists_differentiableOn_norm_inv_sub_lt hΩ hK hKΩ ha hδ
    refine ⟨φ (HolomorphicFunctions.of U g₀ hg₀), ⟨_, rfl⟩, ?_⟩
    rw [dist_eq_norm, ContinuousMap.norm_lt_iff _ hδ]
    intro z
    simpa [w, φ, ρ, HolomorphicFunctions.of_apply] using hbound z.val z.property
  let q : S := Polynomial.aeval (⟨w, hw⟩ : S) P
  obtain ⟨g, hg, hdist⟩ := Metric.mem_closure_iff.mp q.property ε hε
  obtain ⟨g', rfl⟩ := hg
  refine ⟨HolomorphicFunctions.extend g', HolomorphicFunctions.differentiableOn_extend g',
    fun z hz => ?_⟩
  have hqz : (q : C(K, ℂ)) ⟨z, hz⟩ = P.eval (z - a)⁻¹ := by
    simp only [q, Polynomial.coe_aeval_mk_apply, Polynomial.aeval_continuousMap_apply, w,
      ContinuousMap.coe_mk]
  rw [HolomorphicFunctions.extend_apply g' ⟨z, hKΩ hz⟩, ← hqz]
  exact lt_of_le_of_lt ((q.val - φ g').norm_coe_le_norm ⟨z, hz⟩)
    (by simpa [dist_eq_norm] using hdist)

/-- **Runge approximation for powers of `(z - a)⁻¹`.** On a compact set `K` filled in `Ω`, every
power `((z - a)⁻¹) ^ n` with `a ∉ K` is uniformly approximable on `K` by functions
complex-differentiable on `Ω`. -/
theorem IsFilledIn.exists_differentiableOn_norm_inv_pow_sub_lt (hfill : IsFilledIn K Ω)
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) {a : ℂ} (ha : a ∉ K) (n : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ K, ‖((z - a)⁻¹) ^ n - g z‖ < ε := by
  simpa only [eval_pow, eval_X] using
    hfill.exists_differentiableOn_norm_eval_inv_sub_lt hΩ hK hKΩ ha (X ^ n) hε

/-- **Runge approximation for vector-valued negative-power monomials.** On a compact set `K` filled
in `Ω`, `(z - a) ^ (-(n : ℤ)) • v` (`a ∉ K`, `v : F`) is uniformly approximable on `K` by functions
`g : ℂ → F` complex-differentiable on `Ω`. -/
theorem IsFilledIn.exists_differentiableOn_norm_zpow_neg_smul_sub_lt (hfill : IsFilledIn K Ω)
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) {a : ℂ} (ha : a ∉ K) (n : ℕ) (v : F)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → F, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ K, ‖(z - a) ^ (-(n : ℤ)) • v - g z‖ < ε := by
  rcases eq_or_ne v 0 with rfl | hv
  · exact ⟨0, differentiableOn_const 0, fun _ _ => by simp [hε]⟩
  have hv_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  obtain ⟨q, hq, hbound⟩ :=
    hfill.exists_differentiableOn_norm_inv_pow_sub_lt hΩ hK hKΩ ha n (div_pos hε hv_pos)
  refine ⟨fun z => q z • v, hq.smul_const v, fun z hz => ?_⟩
  rw [zpow_neg, zpow_natCast, ← inv_pow, ← sub_smul, norm_smul]
  exact (mul_lt_mul_of_pos_right (hbound z hz) hv_pos).trans_eq (div_mul_cancel₀ ε hv_pos.ne')

end NormedSpace

section CompleteSpace

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] {K Ω : Set ℂ}

/-- **Runge approximation for `laurentNegPart`.** If `f : ℂ → F` admits a convergent Laurent series
on `Metric.eball a R \ Metric.closedBall a r` and `K` is a compact set filled in `Ω` and disjoint
from `Metric.closedBall a r`, then `laurentNegPart b a` is uniformly approximable on `K` by
functions complex-differentiable on `Ω`. -/
theorem IsFilledIn.exists_differentiableOn_norm_laurentNegPart_sub_lt
    {f : ℂ → F} {b : ℤ → F} {a : ℂ} {r : ℝ} {R : ℝ≥0∞}
    (hfill : IsFilledIn K Ω) (hL : HasLaurentSeriesOnAnnulus f b a r R)
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) (haK : Disjoint K (closedBall a r))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → F, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ K, ‖laurentNegPart b a z - g z‖ < ε := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨0, differentiableOn_const 0, by simp⟩
  have ha_notMem : a ∉ K := fun ha => haK.le_bot ⟨ha, mem_closedBall_self hL.r_nonneg⟩
  obtain ⟨z₀, hz₀K, hz₀min⟩ :=
    hK.exists_isMinOn hKne (continuous_id.dist continuous_const).continuousOn
  have hrs : r < dist z₀ a :=
    not_le.mp fun hle => haK.le_bot ⟨hz₀K, mem_closedBall.mpr hle⟩
  have hKext : K ⊆ (ball a (dist z₀ a))ᶜ := fun z hz hball =>
    (mem_ball.mp hball).not_ge (hz₀min hz)
  have hunif := Metric.tendstoUniformlyOn_iff.mp (hL.tendstoUniformlyOn_laurentNegPart hrs)
    (ε / 2) (half_pos hε)
  obtain ⟨t, ht⟩ := hunif.exists
  obtain ⟨g, hg, hgbound⟩ := exists_differentiableOn_norm_sum_sub_lt (Ω := Ω) (K := K)
    (f := fun k z => (z - a) ^ (-((k : ℤ) + 1)) • b (-((k : ℤ) + 1))) t (half_pos hε)
    fun k _ δ hδ => by
      simpa only [Nat.cast_add, Nat.cast_one] using
        hfill.exists_differentiableOn_norm_zpow_neg_smul_sub_lt hΩ hK hKΩ ha_notMem (k + 1)
          (b (-((k : ℤ) + 1))) hδ
  refine ⟨g, hg, fun z hz => ?_⟩
  have ht' : ‖laurentNegPart b a z -
      ∑ k ∈ t, (z - a) ^ (-((k : ℤ) + 1)) • b (-((k : ℤ) + 1))‖ < ε / 2 := by
    simpa only [dist_eq_norm] using ht z (hKext hz)
  calc ‖laurentNegPart b a z - g z‖
      ≤ ‖laurentNegPart b a z - ∑ k ∈ t, (z - a) ^ (-((k : ℤ) + 1)) • b (-((k : ℤ) + 1))‖ +
          ‖(∑ k ∈ t, (z - a) ^ (-((k : ℤ) + 1)) • b (-((k : ℤ) + 1))) - g z‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add ht' (hgbound z hz)
    _ = ε := add_halves ε

/-- **Runge approximation on the exterior of a closed disk.** If `K` is compact, filled in `Ω`, and
disjoint from `Metric.closedBall a r`, every function `f : ℂ → F` complex-differentiable on
`(Metric.closedBall a r)ᶜ` is uniformly approximable on `K` by functions complex-differentiable on
`Ω`. -/
theorem IsFilledIn.exists_differentiableOn_norm_sub_lt_of_differentiableOn_compl_closedBall
    (hfill : IsFilledIn K Ω) (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {a : ℂ} {r : ℝ} (haK : Disjoint K (closedBall a r))
    {f : ℂ → F} (hf : DifferentiableOn ℂ f (closedBall a r)ᶜ) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → F, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ K, ‖f z - g z‖ < ε := by
  rcases lt_or_ge r 0 with hr | hr
  · exact ⟨f, hf.mono (by simp [closedBall_eq_empty.mpr hr]), fun _ _ => by simp [hε]⟩
  have hf_ann : DifferentiableOn ℂ f (eball a ⊤ \ closedBall a r) := by
    rwa [eball_top, ← compl_eq_univ_sdiff]
  have hL : HasLaurentSeriesOnAnnulus f (circleLaurentCoeff f a (r + 1)) a r ⊤ :=
    hf_ann.hasLaurentSeriesOnAnnulus hr (by linarith) ENNReal.ofReal_lt_top
  obtain ⟨gn, hgn, hbound⟩ :=
    hfill.exists_differentiableOn_norm_laurentNegPart_sub_lt hL hΩ hK hKΩ haK hε
  have hgp : DifferentiableOn ℂ (laurentPosPart (circleLaurentCoeff f a (r + 1)) a) Ω :=
    hL.differentiableOn_laurentPosPart.mono (by simp)
  refine ⟨fun z => laurentPosPart (circleLaurentCoeff f a (r + 1)) a z + gn z,
    hgp.add hgn, fun z hz => ?_⟩
  have hz_ann : z ∈ eball a ⊤ \ closedBall a r :=
    ⟨by simp, fun h => haK.le_bot ⟨hz, h⟩⟩
  rw [hL.eq_laurentPosPart_add_laurentNegPart hz_ann, add_sub_add_left_eq_sub]
  exact hbound z hz

/-- **Runge approximation on a punctured plane.** If `K` is compact and filled in `Ω` and `a ∉ K`,
every function `f : ℂ → F` complex-differentiable on `{a}ᶜ` is uniformly approximable on `K` by
functions complex-differentiable on `Ω`. -/
theorem IsFilledIn.exists_differentiableOn_norm_sub_lt_of_differentiableOn_compl_singleton
    (hfill : IsFilledIn K Ω) (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {a : ℂ} (ha : a ∉ K) {f : ℂ → F} (hf : DifferentiableOn ℂ f {a}ᶜ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → F, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ K, ‖f z - g z‖ < ε := by
  refine hfill.exists_differentiableOn_norm_sub_lt_of_differentiableOn_compl_closedBall
    (a := a) (r := 0) hΩ hK hKΩ ?_ ?_ hε
  · simpa only [closedBall_zero, disjoint_singleton_right] using ha
  · simpa only [closedBall_zero] using hf

/-- **Runge approximation for finite sums of punctured-plane holomorphic functions.** If `K` is
compact and filled in `Ω` and `c : ι → ℂ` avoids `K` on `s : Finset ι`, any finite sum
`∑ i ∈ s, f i` with each `f i` complex-differentiable on `{c i}ᶜ` is uniformly approximable on `K`
by a function complex-differentiable on `Ω`. -/
theorem IsFilledIn.exists_differentiableOn_norm_sum_sub_lt_of_differentiableOn_compl_singleton
    {ι : Type*} (hfill : IsFilledIn K Ω) (s : Finset ι) (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) {c : ι → ℂ} (hc : ∀ i ∈ s, c i ∉ K)
    {f : ι → ℂ → F} (hf : ∀ i ∈ s, DifferentiableOn ℂ (f i) {c i}ᶜ) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → F, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ K, ‖(∑ i ∈ s, f i z) - g z‖ < ε :=
  exists_differentiableOn_norm_sum_sub_lt s hε fun i hi _ hδ =>
    hfill.exists_differentiableOn_norm_sub_lt_of_differentiableOn_compl_singleton
      hΩ hK hKΩ (hc i hi) (hf i hi) hδ

end CompleteSpace

end TauCeti
