/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ContinuousLog.Circle
import TauCeti.Analysis.Complex.AtInfinity
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Zero multiplicities and the winding degree at infinity

Suppose that near every point `z` a function `f : ℂ → ℂ` factors as
`f w = (w - z) ^ n z * v w`, with `v` continuous at `z` and `v z ≠ 0`. Such an `f` is continuous
(`TauCeti.continuous_of_eventually_eq_pow_mul`), but no holomorphy is assumed: this is the local
form that the similarity principle gives for solutions of `∂bar f = a f`, for instance for the
section of a plane vortex. The exponent `n z` is then the local multiplicity of `f` at `z`, and
`n z = 0` wherever `f z ≠ 0`. The zeros are isolated, so there are finitely many if `f` has none
near infinity (`TauCeti.finite_setOfPred_eq_zero_of_eventually_eq_pow_mul`).

This file proves the topological argument principle for such functions:

* `TauCeti.exists_continuous_eq_exp_mul_prod_pow`: if the zeros of `f` lie in a finite set `s`,
  then `f w = exp (L w) * ∏ z ∈ s, (w - z) ^ n z` for a continuous `L : ℂ → ℂ`. The quotient of
  `f` by the product extends continuously and without zeros across `s`, and the plane is simply
  connected.
* `TauCeti.natCast_finsum_eq_of_tendsto_mul_inv_zpow`: if `f z * ((z / |z|) ^ m)⁻¹ → 1` at
  infinity, then the zeros of `f` are finite in number and `∑ᶠ z, n z = m`. On a large circle the
  factorization above leaves `z ^ (∑ n - m)` with a continuous logarithm, which is impossible
  unless the exponent vanishes (`TauCeti.not_hasContinuousLogOn_zpow_sub_sphere`).

In particular the end framing of such a section determines its total number of zeros, counted
with multiplicity, and that number is the degree of the framing.
-/

public section

namespace TauCeti

open Complex Filter Metric Set Topology

variable {f : ℂ → ℂ} {n : ℂ → ℕ}

/-- A function with a local power factorization `(w - z) ^ n z * v w` at every point, with `v`
continuous at `z`, is continuous. -/
theorem continuous_of_eventually_eq_pow_mul
    (hn : ∀ z, ∃ v : ℂ → ℂ, ContinuousAt v z ∧ ∀ᶠ w in 𝓝 z, f w = (w - z) ^ n z * v w) :
    Continuous f :=
  continuous_iff_continuousAt.mpr fun z ↦ by
    obtain ⟨v, hvc, hfz⟩ := hn z
    exact (((continuousAt_id.sub continuousAt_const).pow _).mul hvc).congr
      (hfz.mono fun _ h ↦ h.symm)

/-- A function with a local power factorization at every point, and with no zeros near infinity,
has finitely many zeros. -/
theorem finite_setOfPred_eq_zero_of_eventually_eq_pow_mul
    (hn : ∀ z, ∃ v : ℂ → ℂ, ContinuousAt v z ∧ v z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, f w = (w - z) ^ n z * v w)
    (htail : ∀ᶠ w in cocompact ℂ, f w ≠ 0) : {w | f w = 0}.Finite := by
  have hf := continuous_of_eventually_eq_pow_mul fun z ↦ (hn z).imp fun _ hv ↦ ⟨hv.1, hv.2.2⟩
  have hdis : IsDiscrete {w | f w = 0} := by
    refine isDiscrete_iff_nhdsNE.mpr fun z _ ↦ ?_
    rw [← disjoint_iff, Filter.disjoint_principal_right]
    obtain ⟨v, hvc, hv0, hfz⟩ := hn z
    filter_upwards [nhdsWithin_le_nhds (hvc.eventually_ne hv0), nhdsWithin_le_nhds hfz,
      self_mem_nhdsWithin] with w hv hw hne
    simp [hw, hv, sub_ne_zero.mpr hne]
  obtain ⟨K, hK, hsub⟩ := Filter.mem_cocompact'.mp htail
  simp only [Set.compl_ofPred, not_not] at hsub
  exact (hK.of_isClosed_subset (isClosed_eq hf continuous_const) (by simpa using hsub)).finite hdis

/-- A local power factorization with a positive exponent forces a zero at its centre. -/
theorem support_subset_setOf_eq_zero_of_eventually_eq_pow_mul
    (hn : ∀ z, ∃ v : ℂ → ℂ, ∀ᶠ w in 𝓝 z, f w = (w - z) ^ n z * v w) :
    Function.support n ⊆ {w | f w = 0} := fun z hz ↦ by
  obtain ⟨v, hfz⟩ := hn z
  simp [hfz.self_of_nhds, zero_pow hz]

/-- The multiplicities of a function with local power factorizations and no zeros near infinity
have finite support. -/
theorem finite_support_of_eventually_eq_pow_mul
    (hn : ∀ z, ∃ v : ℂ → ℂ, ContinuousAt v z ∧ v z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, f w = (w - z) ^ n z * v w)
    (htail : ∀ᶠ w in cocompact ℂ, f w ≠ 0) : (Function.support n).Finite :=
  (finite_setOfPred_eq_zero_of_eventually_eq_pow_mul hn htail).subset
    (support_subset_setOf_eq_zero_of_eventually_eq_pow_mul fun z ↦ (hn z).imp fun _ hv ↦ hv.2.2)

/-- **Global factorization off the zeros.** A continuous function whose zeros lie in a finite set
`s`, and which factors as `(w - z) ^ n z * v w` near each `z ∈ s` with `v` continuous at `z` and
nonzero there, is `exp (L w) * ∏ z ∈ s, (w - z) ^ n z` for a continuous `L`. -/
theorem exists_continuous_eq_exp_mul_prod_pow (hf : Continuous f) (s : Finset ℂ)
    (hn : ∀ z ∈ s, ∃ v : ℂ → ℂ, ContinuousAt v z ∧ v z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, f w = (w - z) ^ n z * v w)
    (hs : ∀ w, f w = 0 → w ∈ s) :
    ∃ L : ℂ → ℂ, Continuous L ∧ ∀ w, f w = exp (L w) * ∏ z ∈ s, (w - z) ^ n z := by
  classical
  choose! v hvc hv0 hvf using hn
  set P : ℂ → ℂ := fun w ↦ ∏ z ∈ s, (w - z) ^ n z with hPdef
  -- `Q z` is the product with the factor at `z` removed
  set Q : ℂ → ℂ → ℂ := fun z w ↦ ∏ y ∈ s.erase z, (w - y) ^ n y with hQdef
  have hPQ : ∀ z ∈ s, ∀ w, P w = (w - z) ^ n z * Q z w := fun z hz w ↦
    (Finset.mul_prod_erase s (fun y ↦ (w - y) ^ n y) hz).symm
  have hQc : ∀ z, Continuous (Q z) := fun z ↦ by fun_prop
  have hQ0 : ∀ z, Q z z ≠ 0 := fun z ↦ Finset.prod_ne_zero_iff.mpr fun y hy ↦
    pow_ne_zero _ (sub_ne_zero.mpr (Finset.ne_of_mem_erase hy).symm)
  have hP0 : ∀ w ∉ s, P w ≠ 0 := fun w hw ↦ Finset.prod_ne_zero_iff.mpr fun y hy ↦
    pow_ne_zero _ (sub_ne_zero.mpr fun h ↦ hw (h ▸ hy))
  -- the quotient `f / P`, continued across `s` by the quotient of the local factors
  set g : ℂ → ℂ := fun w ↦ if w ∈ s then v w w / Q w w else f w / P w with hgdef
  have hgc : Continuous g := by
    refine continuous_iff_continuousAt.mpr fun w₀ ↦ ?_
    by_cases hw₀ : w₀ ∈ s
    · have hev : g =ᶠ[𝓝 w₀] fun w ↦ v w₀ w / Q w₀ w := by
        have hns : ∀ᶠ w in 𝓝 w₀, w ∉ s.erase w₀ :=
          (s.erase w₀).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)
        filter_upwards [hns, hvf w₀ hw₀] with w hw hfw
        by_cases hww : w = w₀
        · subst hww
          simp [hgdef, hw₀]
        · have hws : w ∉ s := fun h ↦ hw (Finset.mem_erase.mpr ⟨hww, h⟩)
          simp only [hgdef, hws, ite_false]
          rw [hfw, hPQ w₀ hw₀ w, mul_div_mul_left _ _ (pow_ne_zero _ (sub_ne_zero.mpr hww))]
      exact ((hvc w₀ hw₀).div (hQc w₀).continuousAt (hQ0 w₀)).congr hev.symm
    · have hev : g =ᶠ[𝓝 w₀] fun w ↦ f w / P w := by
        filter_upwards [s.finite_toSet.isClosed.isOpen_compl.mem_nhds hw₀] with w hw
        rw [mem_compl_iff, Finset.mem_coe] at hw
        simp only [hgdef, hw, ite_false]
      have hPc : Continuous P := by fun_prop
      exact (hf.continuousAt.div hPc.continuousAt (hP0 w₀ hw₀)).congr hev.symm
  have hfg : ∀ w, f w = g w * P w := fun w ↦ by
    by_cases hw : w ∈ s
    · simp only [hgdef, hw, ite_true]
      rw [(hvf w hw).self_of_nhds, hPQ w hw w]
      field_simp [hQ0 w]
    · simp only [hgdef, hw, ite_false]
      field_simp [hP0 w hw]
  have hg0 : ∀ w, g w ≠ 0 := fun w ↦ by
    by_cases hw : w ∈ s
    · simpa [hgdef, hw] using ⟨hv0 w hw, hQ0 w⟩
    · simpa [hgdef, hw] using ⟨fun h ↦ hw (hs w h), hP0 w hw⟩
  have hUc : IsSimplyConnected (univ : Set ℂ) :=
    (Homeomorph.Set.univ ℂ).toHomotopyEquiv.simplyConnectedSpace
  obtain ⟨L, hLc, hL⟩ := Complex.exists_continuousOn_eqOn_exp_comp hUc isOpen_univ
    hgc.continuousOn (by rintro ⟨w, -, hw⟩; exact hg0 w hw)
  refine ⟨L, continuousOn_univ.mp hLc, fun w ↦ ?_⟩
  rw [hfg w, ← hL (mem_univ w)]
  rfl

/-- **The argument principle for functions with continuous local power factorizations.** If `f`
factors as `(w - z) ^ n z * v w` near every `z` with `v` continuous at `z` and
nonzero there, and `f z * ((z / |z|) ^ m)⁻¹ → 1` at infinity, then the multiplicities add up to
the winding degree `m`. In particular `n` has finite support and `m ≥ 0`. -/
theorem natCast_finsum_eq_of_tendsto_mul_inv_zpow
    (hn : ∀ z, ∃ v : ℂ → ℂ, ContinuousAt v z ∧ v z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, f w = (w - z) ^ n z * v w)
    {m : ℤ} (hm : Tendsto (fun z ↦ f z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    ((∑ᶠ z, n z : ℕ) : ℤ) = m := by
  classical
  have htail : ∀ᶠ w in cocompact ℂ, f w ≠ 0 := by
    filter_upwards [hm.eventually_ne one_ne_zero] with w hw h0
    exact hw (by simp [h0])
  have hf := continuous_of_eventually_eq_pow_mul fun z ↦ (hn z).imp fun _ hv ↦ ⟨hv.1, hv.2.2⟩
  have hfin := finite_setOfPred_eq_zero_of_eventually_eq_pow_mul hn htail
  set s := hfin.toFinset with hsdef
  have hsupp : Function.support n ⊆ s := fun z hz ↦ by
    simpa [hsdef] using support_subset_setOf_eq_zero_of_eventually_eq_pow_mul
      (fun z ↦ (hn z).imp fun _ hv ↦ hv.2.2) hz
  obtain ⟨L, hLc, hL⟩ := exists_continuous_eq_exp_mul_prod_pow hf s (fun z _ ↦ hn z)
    (fun w hw ↦ by simpa [hsdef] using hw)
  rw [finsum_eq_sum_of_support_subset n hsupp]
  set N := ∑ z ∈ s, n z with hNdef
  -- `q w = (∏ z ∈ s, (w - z) ^ n z) / w ^ N` tends to one at infinity
  set q : ℂ → ℂ := fun w ↦ ∏ z ∈ s, (1 - z * w⁻¹) ^ n z with hqdef
  -- on a large circle both `q` and the framed section have principal logarithms
  obtain ⟨R₁, hR₁⟩ := exists_forall_hasContinuousLogOn_sphere hm fun w hw ↦ by
    have hw' : ((‖w‖ : ℝ) : ℂ) ≠ 0 := by simpa using hw
    have hu := continuousAt_id.div (continuous_ofReal.comp continuous_norm).continuousAt hw'
    exact hf.continuousAt.mul ((hu.zpow₀ m (Or.inl (div_ne_zero hw hw'))).inv₀
      (zpow_ne_zero _ (div_ne_zero hw hw')))
  obtain ⟨R₂, hR₂⟩ := exists_forall_hasContinuousLogOn_sphere (F := q)
      (tendsto_prod_one_sub_mul_inv_pow s n) fun w hw ↦ by
    rw [hqdef]
    fun_prop (disch := assumption)
  set ρ := max (max R₁ R₂) 1
  have hρ : 0 < ρ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hlogL : HasContinuousLogOn (fun w ↦ exp (L w)) (sphere 0 ρ) :=
    hasContinuousLogOn_iff.mpr ⟨L, hLc.continuousOn, fun _ _ ↦ rfl⟩
  have hρm : ((ρ : ℂ) ^ m) ≠ 0 := zpow_ne_zero _ (by exact_mod_cast hρ.ne')
  -- on that circle the framed section is `exp L * q * ρ ^ m * w ^ (N - m)`
  have hlog : HasContinuousLogOn (fun w ↦ (w - 0) ^ ((N : ℤ) - m)) (sphere 0 ρ) := by
    refine ((hR₁ ρ (le_max_of_le_left (le_max_left _ _))).div
      ((hlogL.mul (hR₂ ρ (le_max_of_le_left (le_max_right _ _)))).mul
        (hasContinuousLogOn_const hρm))).congr fun w hw ↦ ?_
    have hwρ : ‖w‖ = ρ := mem_sphere_zero_iff_norm.mp hw
    have hw0 : w ≠ 0 := fun h ↦ by
      simp only [h, norm_zero] at hwρ
      linarith
    have hprod : ∏ z ∈ s, (w - z) ^ n z = w ^ N * q w := by
      rw [hqdef, hNdef, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun z _ ↦ ?_
      rw [← mul_pow]
      congr 1
      field_simp
    have hq0 : q w ≠ 0 := (hR₂ ρ (le_max_of_le_left (le_max_right _ _))).ne_zero hw
    simp only [hL w, hprod, hwρ, sub_zero, div_zpow, zpow_sub₀ hw0, zpow_natCast]
    field_simp [exp_ne_zero (L w), hq0, hρm, zpow_ne_zero m hw0]
  by_contra hNm
  exact not_hasContinuousLogOn_zpow_sub_sphere hρ.le 0 (sub_ne_zero.mpr hNm) hlog

/-- The natural-number form of `TauCeti.natCast_finsum_eq_of_tendsto_mul_inv_zpow`: if
`f z * ((z / |z|) ^ m)⁻¹ → 1` at infinity, the local multiplicities of `f` add up to `m`. -/
theorem finsum_eq_of_tendsto_mul_inv_pow
    (hn : ∀ z, ∃ v : ℂ → ℂ, ContinuousAt v z ∧ v z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, f w = (w - z) ^ n z * v w)
    {m : ℕ} (hm : Tendsto (fun z ↦ f z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    ∑ᶠ z, n z = m := by
  exact_mod_cast natCast_finsum_eq_of_tendsto_mul_inv_zpow hn (m := m) (by simpa using hm)

end TauCeti
