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
import TauCeti.Algebra.BigOperators.Finprod
import TauCeti.Analysis.Normed.Module.LocalFactorization
import Mathlib.Data.Finsupp.Multiset

/-!
# Zero multiplicities and the winding degree at infinity

Suppose that near every point `z` a function `f : ℂ → ℂ` factors as
`f w = (w - z) ^ n z * v w`, with `v` continuous at `z` and `v z ≠ 0`. Such an `f` is continuous
(`TauCeti.continuous_of_eventually_eq_pow_mul`), but no holomorphy is assumed: this is the local
form that the similarity principle gives for solutions of `∂bar f = a f`, for instance for the
section of a plane vortex. The exponent `n z` is then the local multiplicity of `f` at `z`, and
`n z = 0` wherever `f z ≠ 0`. The exponent is unique, already among factors that are only
continuous at the point (`TauCeti.eq_of_eventually_sub_pow_smul_eq`). The zeros are isolated, so
there are finitely many if `f` has none near infinity
(`TauCeti.finite_setOfPred_eq_zero_of_eventually_eq_pow_mul`).

This file proves the topological argument principle for such functions:

* `TauCeti.exists_continuous_eq_exp_mul_prod_pow`: if the zeros of `f` lie in a finite set `s`,
  then `f w = exp (L w) * ∏ z ∈ s, (w - z) ^ n z` for a continuous `L : ℂ → ℂ`. The quotient of
  `f` by the product extends continuously and without zeros across `s`
  (`TauCeti.exists_continuous_ne_zero_eq_mul_prod_pow`), and its logarithm comes from Mathlib's
  `Complex.exists_continuousOn_eqOn_exp_comp` on the simply connected plane.
* `TauCeti.natCast_finsum_eq_of_tendsto_mul_inv_zpow`: if `f z * ((z / |z|) ^ m)⁻¹ → 1` at
  infinity, then `∑ᶠ z, n z = m`, a sum over the finitely many zeros of `f`. On a large circle the
  factorization above leaves `z ^ (∑ n - m)` with a continuous logarithm, which is impossible
  unless the exponent vanishes (`TauCeti.natCast_sum_eq_of_eq_exp_mul_prod_pow`, using
  `TauCeti.not_hasContinuousLogOn_zpow_sub_sphere`).

In particular the end framing of such a section determines its total number of zeros, counted
with multiplicity, and that number is the degree of the framing.

When the multiplicities are those of a multiset `D`, it is the zero divisor of `f`
(`TauCeti.HasZeroDivisor f D`). It exists when `f` has local power factorizations and no zeros
near infinity (`TauCeti.exists_hasZeroDivisor_of_eventually_eq_pow_mul`). A function has at most
one zero divisor (`TauCeti.HasZeroDivisor.unique`), its points are the zeros of `f`,
multiplication by a continuous nowhere-vanishing function does not change it, and under the
degree-`m` end framing it has degree `m` (`TauCeti.HasZeroDivisor.card_eq`). Precomposing `f`
with a translation or a nonzero scaling moves the divisor accordingly
(`TauCeti.HasZeroDivisor.comp_add`, `TauCeti.HasZeroDivisor.comp_const_mul`).
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

/-- **Zero-free quotient by the zeros.** A continuous function whose zeros lie in a finite set
`s`, and which factors as `(w - z) ^ n z * v w` near each `z ∈ s` with `v` continuous at `z` and
nonzero there, is `g w * ∏ z ∈ s, (w - z) ^ n z` for a continuous nowhere-zero `g`: the quotient
of `f` by the product, continued across `s` by the quotients of the local factors. -/
theorem exists_continuous_ne_zero_eq_mul_prod_pow (hf : Continuous f) (s : Finset ℂ)
    (hn : ∀ z ∈ s, ∃ v : ℂ → ℂ, ContinuousAt v z ∧ v z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, f w = (w - z) ^ n z * v w)
    (hs : ∀ w, f w = 0 → w ∈ s) :
    ∃ g : ℂ → ℂ, Continuous g ∧ (∀ w, g w ≠ 0) ∧ ∀ w, f w = g w * ∏ z ∈ s, (w - z) ^ n z := by
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
  set g : ℂ → ℂ := fun w ↦ if w ∈ s then v w w / Q w w else f w / P w with hgdef
  refine ⟨g, continuous_iff_continuousAt.mpr fun w₀ ↦ ?_, fun w ↦ ?_, fun w ↦ ?_⟩
  · by_cases hw₀ : w₀ ∈ s
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
  · by_cases hw : w ∈ s
    · simpa [hgdef, hw] using ⟨hv0 w hw, hQ0 w⟩
    · simpa [hgdef, hw] using ⟨fun h ↦ hw (hs w h), hP0 w hw⟩
  · -- the product in the goal is `P w` by the definition of `P`
    rw [show ∏ z ∈ s, (w - z) ^ n z = P w by rw [hPdef]]
    by_cases hw : w ∈ s
    · simp only [hgdef, hw, ite_true]
      rw [(hvf w hw).self_of_nhds, hPQ w hw w]
      field_simp [hQ0 w]
    · simp only [hgdef, hw, ite_false]
      field_simp [hP0 w hw]

/-- **Global factorization off the zeros.** A continuous function whose zeros lie in a finite set
`s`, and which factors as `(w - z) ^ n z * v w` near each `z ∈ s` with `v` continuous at `z` and
nonzero there, is `exp (L w) * ∏ z ∈ s, (w - z) ^ n z` for a continuous `L`. The logarithm of the
zero-free quotient `TauCeti.exists_continuous_ne_zero_eq_mul_prod_pow` comes from Mathlib's
`Complex.exists_continuousOn_eqOn_exp_comp` on the simply connected plane. -/
theorem exists_continuous_eq_exp_mul_prod_pow (hf : Continuous f) (s : Finset ℂ)
    (hn : ∀ z ∈ s, ∃ v : ℂ → ℂ, ContinuousAt v z ∧ v z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, f w = (w - z) ^ n z * v w)
    (hs : ∀ w, f w = 0 → w ∈ s) :
    ∃ L : ℂ → ℂ, Continuous L ∧ ∀ w, f w = exp (L w) * ∏ z ∈ s, (w - z) ^ n z := by
  obtain ⟨g, hgc, hg0, hfg⟩ := exists_continuous_ne_zero_eq_mul_prod_pow hf s hn hs
  have hUc : IsSimplyConnected (univ : Set ℂ) :=
    (Homeomorph.Set.univ ℂ).toHomotopyEquiv.simplyConnectedSpace
  obtain ⟨L, hLc, hL⟩ := Complex.exists_continuousOn_eqOn_exp_comp hUc isOpen_univ
    hgc.continuousOn (by rintro ⟨w, -, hw⟩; exact hg0 w hw)
  refine ⟨L, continuousOn_univ.mp hLc, fun w ↦ ?_⟩
  rw [hfg w, ← hL (mem_univ w), Function.comp_apply]

/-- **The winding degree of a global factorization.** If `f w = exp (L w) * ∏ z ∈ s, (w - z) ^ n z`
with `L` continuous, and `f z * ((z / |z|) ^ m)⁻¹ → 1` at infinity, then the multiplicities add up
to `m`. On a large circle the framed function is `exp L * q * ρ ^ m * w ^ (∑ n - m)` with `q`
close to one, so `w ^ (∑ n - m)` has a continuous logarithm there. -/
theorem natCast_sum_eq_of_eq_exp_mul_prod_pow (s : Finset ℂ) {L : ℂ → ℂ} (hLc : Continuous L)
    (hL : ∀ w, f w = exp (L w) * ∏ z ∈ s, (w - z) ^ n z)
    {m : ℤ} (hm : Tendsto (fun z ↦ f z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    ((∑ z ∈ s, n z : ℕ) : ℤ) = m := by
  have hf : Continuous f := by
    rw [show f = _ from funext hL]
    fun_prop
  set N := ∑ z ∈ s, n z with hNdef
  -- `q w = (∏ z ∈ s, (w - z) ^ n z) / w ^ N` tends to one at infinity
  set q : ℂ → ℂ := fun w ↦ ∏ z ∈ s, (1 - z * w⁻¹) ^ n z with hqdef
  -- on a large circle both `q` and the framed function have principal logarithms
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
  -- on that circle the framed function is `exp L * q * ρ ^ m * w ^ (N - m)`
  have hlog : HasContinuousLogOn (fun w ↦ (w - 0) ^ ((N : ℤ) - m)) (sphere 0 ρ) := by
    refine ((hR₁ ρ (le_max_of_le_left (le_max_left _ _))).div
      ((hlogL.mul (hR₂ ρ (le_max_of_le_left (le_max_right _ _)))).mul
        (hasContinuousLogOn_const hρm))).congr fun w hw ↦ ?_
    have hwρ : ‖w‖ = ρ := mem_sphere_zero_iff_norm.mp hw
    have hw0 : w ≠ 0 := fun h ↦ by
      simp only [h, norm_zero] at hwρ
      linarith
    have hq0 : q w ≠ 0 := (hR₂ ρ (le_max_of_le_left (le_max_right _ _))).ne_zero hw
    have hprod : ∏ z ∈ s, (w - z) ^ n z = w ^ N * q w := by
      rw [hNdef, hqdef, prod_sub_pow_eq_pow_sum_mul_prod_one_sub_mul_inv_pow s n hw0]
    simp only [hL w, hprod, hwρ, sub_zero, div_zpow, zpow_sub₀ hw0, zpow_natCast]
    field_simp [exp_ne_zero (L w), hq0, hρm, zpow_ne_zero m hw0]
  by_contra hNm
  exact not_hasContinuousLogOn_zpow_sub_sphere hρ.le 0 (sub_ne_zero.mpr hNm) hlog

/-- **The argument principle for functions with continuous local power factorizations.** If `f`
factors as `(w - z) ^ n z * v w` near every `z` with `v` continuous at `z` and
nonzero there, and `f z * ((z / |z|) ^ m)⁻¹ → 1` at infinity, then the multiplicities add up to
the winding degree `m`; in particular `m ≥ 0`. The same hypotheses force `n` to have finite
support (`TauCeti.finite_support_of_eventually_eq_pow_mul`), so the sum is a finite one. -/
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
  exact natCast_sum_eq_of_eq_exp_mul_prod_pow s hLc hL hm

/-- The natural-number form of `TauCeti.natCast_finsum_eq_of_tendsto_mul_inv_zpow`: if
`f z * ((z / |z|) ^ m)⁻¹ → 1` at infinity, the local multiplicities of `f` add up to `m`. -/
theorem finsum_eq_of_tendsto_mul_inv_pow
    (hn : ∀ z, ∃ v : ℂ → ℂ, ContinuousAt v z ∧ v z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, f w = (w - z) ^ n z * v w)
    {m : ℕ} (hm : Tendsto (fun z ↦ f z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    ∑ᶠ z, n z = m := by
  exact_mod_cast natCast_finsum_eq_of_tendsto_mul_inv_zpow hn (m := m) (by simpa using hm)

/-! ### Zero divisors -/

/-- `D` is the **zero divisor** of `f`: near every point `z`, `f` factors as
`f w = (w - z) ^ D(z) * v w` with `v` continuous at `z` and nonzero there, where `D(z)` is the
multiplicity of `z` in the multiset `D`. -/
def HasZeroDivisor (f : ℂ → ℂ) (D : Multiset ℂ) : Prop :=
  ∀ z, ∃ v : ℂ → ℂ, ContinuousAt v z ∧ v z ≠ 0 ∧ ∀ᶠ w in 𝓝 z, f w = (w - z) ^ D.count z * v w

/-- Unfolding `HasZeroDivisor`: the local factorizations of the function. -/
theorem hasZeroDivisor_iff {D : Multiset ℂ} :
    HasZeroDivisor f D ↔ ∀ z, ∃ v : ℂ → ℂ, ContinuousAt v z ∧ v z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, f w = (w - z) ^ D.count z * v w := Iff.rfl

/-- **Existence of the zero divisor.** A function with a local power factorization at every
point, and with no zeros near infinity, has a zero divisor: its multiplicities have finite
support. -/
theorem exists_hasZeroDivisor_of_eventually_eq_pow_mul
    (hn : ∀ z, ∃ v : ℂ → ℂ, ContinuousAt v z ∧ v z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, f w = (w - z) ^ n z * v w)
    (htail : ∀ᶠ w in cocompact ℂ, f w ≠ 0) : ∃ D, HasZeroDivisor f D := by
  classical
  refine ⟨Finsupp.toMultiset (Finsupp.ofSupportFinite n
    (finite_support_of_eventually_eq_pow_mul hn htail)), hasZeroDivisor_iff.2 fun z ↦ ?_⟩
  simpa only [Finsupp.count_toMultiset, Finsupp.ofSupportFinite_coe] using hn z

namespace HasZeroDivisor

variable {g : ℂ → ℂ} {D D' : Multiset ℂ}

/-- The multiplicity of `z` in the zero divisor is the exponent of any local factorization
`f w = (w - z) ^ n * v w` with `v` continuous at `z` and nonzero there. -/
theorem count_eq_of_eventually_eq_pow_mul (hD : HasZeroDivisor f D) {z : ℂ} {n : ℕ} {v : ℂ → ℂ}
    (hv : ContinuousAt v z) (hv₀ : v z ≠ 0) (h : ∀ᶠ w in 𝓝 z, f w = (w - z) ^ n * v w) :
    D.count z = n := by
  obtain ⟨u, hu, hu₀, hfu⟩ := hD z
  refine eq_of_eventually_sub_pow_smul_eq hu hu₀ hv hv₀ ?_
  filter_upwards [hfu, h] with w hwu hwv
  rw [smul_eq_mul, smul_eq_mul, ← hwu, ← hwv]

/-- **Uniqueness of the zero divisor.** The multiplicities are the exponents of the local
factorizations, which are unique. -/
theorem unique (hD : HasZeroDivisor f D) (hD' : HasZeroDivisor f D') : D = D' := by
  refine Multiset.ext.2 fun z ↦ ?_
  obtain ⟨v, hv, hv₀, hfv⟩ := hD' z
  exact hD.count_eq_of_eventually_eq_pow_mul hv hv₀ hfv

/-- The zeros of a function are the points of its zero divisor. -/
theorem apply_eq_zero_iff (hD : HasZeroDivisor f D) {z : ℂ} : f z = 0 ↔ z ∈ D := by
  obtain ⟨v, -, hv₀, hfv⟩ := hD z
  simp [hfv.self_of_nhds, hv₀]

/-- A function with a zero divisor is not identically zero: it does not vanish off the finitely
many points of the divisor. -/
theorem exists_ne_zero (hD : HasZeroDivisor f D) : ∃ w, f w ≠ 0 := by
  classical
  obtain ⟨w, hw⟩ := Infinite.exists_notMem_finset D.toFinset
  exact ⟨w, fun h ↦ hw (Multiset.mem_toFinset.2 (hD.apply_eq_zero_iff.1 h))⟩

/-- **The zero divisor of a framed function has degree `m`.** If
`f z * ((z / |z|) ^ m)⁻¹ → 1` at infinity, the zero divisor of `f` has `m` points, counted with
multiplicity. This is the topological argument principle
`TauCeti.finsum_eq_of_tendsto_mul_inv_pow`. -/
theorem card_eq (hD : HasZeroDivisor f D) {m : ℕ}
    (hm : Tendsto (fun z ↦ f z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    Multiset.card D = m := by
  rw [← finsum_eq_of_tendsto_mul_inv_pow (n := fun z ↦ D.count z) hD hm]
  simpa using (Multiset.finsum_count_eq_card (R := ℕ) D).symm

/-- Multiplying by a continuous nowhere-vanishing function preserves the zero divisor. -/
theorem of_eq_mul (hD : HasZeroDivisor f D) {u : ℂ → ℂ} (hu : Continuous u)
    (hu₀ : ∀ z, u z ≠ 0) (hg : ∀ z, g z = u z * f z) : HasZeroDivisor g D := fun z ↦ by
  obtain ⟨v, hv, hv₀, hfv⟩ := hD z
  refine ⟨fun w ↦ u w * v w, hu.continuousAt.mul hv, mul_ne_zero (hu₀ z) hv₀, ?_⟩
  filter_upwards [hfv] with w hw
  rw [hg, hw]
  ring

/-- **Translation law.** Precomposing with `w ↦ w + a` moves the zero divisor by `-a`. -/
theorem comp_add (hD : HasZeroDivisor f D) (a : ℂ) :
    HasZeroDivisor (fun w ↦ f (w + a)) (D.map (· - a)) := fun z ↦ by
  obtain ⟨v, hv, hv₀, hfv⟩ := hD (z + a)
  have hcount : (D.map (· - a)).count z = D.count (z + a) := by
    simpa using Multiset.count_map_eq_count' (· - a) D sub_left_injective (z + a)
  have ht : Tendsto (· + a) (𝓝 z) (𝓝 (z + a)) := (continuous_id.add continuous_const).tendsto z
  refine ⟨fun w ↦ v (w + a),
    hv.comp_of_eq (continuous_id.add continuous_const).continuousAt rfl, hv₀, ?_⟩
  filter_upwards [ht.eventually hfv] with w hw
  rw [hw, hcount, add_sub_add_right_eq_sub]

/-- **Scaling law.** Precomposing with `w ↦ c w`, `c ≠ 0`, scales the zero divisor by `c⁻¹`. -/
theorem comp_const_mul (hD : HasZeroDivisor f D) {c : ℂ} (hc : c ≠ 0) :
    HasZeroDivisor (fun w ↦ f (c * w)) (D.map (c⁻¹ * ·)) := fun z ↦ by
  obtain ⟨v, hv, hv₀, hfv⟩ := hD (c * z)
  have hcount : (D.map (c⁻¹ * ·)).count z = D.count (c * z) := by
    simpa [inv_mul_cancel_left₀ hc] using
      Multiset.count_map_eq_count' (c⁻¹ * ·) D (mul_right_injective₀ (inv_ne_zero hc)) (c * z)
  have ht : Tendsto (c * ·) (𝓝 z) (𝓝 (c * z)) := (continuous_const.mul continuous_id).tendsto z
  refine ⟨fun w ↦ c ^ D.count (c * z) * v (c * w),
    continuousAt_const.mul (hv.comp_of_eq (continuous_const.mul continuous_id).continuousAt rfl),
    mul_ne_zero (pow_ne_zero _ hc) hv₀, ?_⟩
  filter_upwards [ht.eventually hfv] with w hw
  rw [hw, hcount, ← mul_sub, mul_pow]
  ring

end HasZeroDivisor

end TauCeti
