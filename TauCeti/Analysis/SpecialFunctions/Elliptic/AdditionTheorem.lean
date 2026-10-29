/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Elliptic.Uniformization
import Mathlib.Analysis.Normed.Module.Connected

/-!
# The addition theorem for `℘` and the group law on `ℂ / Λ`

This file proves the addition theorem for the Weierstrass `℘`-function of a period lattice `Λ`:
for `z, w ∉ Λ` with `℘(z) ≠ ℘(w)`,

  `℘(z + w) = ((℘'(z) - ℘'(w)) / (℘(z) - ℘(w)))² / 4 - ℘(z) - ℘(w)`,

together with the companion formula for `℘'(z + w)`. In terms of the point map
`P(z) = (℘(z), ℘'(z) / 2)` to the Weierstrass curve `y² = x³ - (g₂ / 4) x - g₃ / 4`
(`PeriodPair.weierstrassPoint`), these say that `P(z + w)` is the chord-and-tangent sum of `P(z)`
and `P(w)`. Hence `P` is a group homomorphism from `ℂ` to the points of the curve with kernel `Λ`:
this is the injectivity half of the complex uniformization `ℂ / Λ ≃ E(ℂ)`.

## Main results

* `PeriodPair.hasDerivAt_derivWeierstrassP`: `℘'' = 6 ℘² - g₂ / 2` off the lattice.
* `PeriodPair.weierstrassP_add`, `PeriodPair.derivWeierstrassP_add`: the addition theorems for `℘`
  and `℘'`.
* `PeriodPair.weierstrassPoint_add`: `P(z + w) = P(z) + P(w)`.
* `PeriodPair.weierstrassPointHom`: the point map as a group homomorphism `ℂ →+ E(ℂ)`, and
  `PeriodPair.ker_weierstrassPointHom`: its kernel is `Λ`.

## Implementation notes

The addition theorem is proved by differentiation rather than by Liouville's theorem, which would
need the principal parts of `℘(z + w)` and of the slope at `z = -w`. Along a line `z + w = s`, the
function `℘(z) + ℘(w) - ((℘'(z) - ℘'(w)) / (℘(z) - ℘(w)))² / 4` has derivative zero by the
differential equation `℘'² = 4 ℘³ - g₂ ℘ - g₃` and its derivative `℘'' = 6 ℘² - g₂ / 2`; its limit
as `z → 0` is `-℘(s)`. The resulting polynomial identity extends to all `z, w, z + w ∉ Λ` by the
identity theorem, the complement of a countable set in `ℂ` being connected. The formula for `℘'`
follows by differentiating again. These give the group law in the chord case `℘(z) ≠ ℘(w)`. When
`℘(z) = ℘(w)`, it follows by cancelling `P(t)` in
`P(z + w) + P(t) = P(z + w + t) = P(z) + P(w + t) = P(z) + P(w) + P(t)`, where each equality is a
chord case for a suitable small `t`.

## References

* E. T. Whittaker and G. N. Watson, *A Course of Modern Analysis*, 4th ed., Cambridge University
  Press, 1927, §20.3.
* J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Graduate Texts in Mathematics
  106, Springer, 2009, §VI.3.
-/

public noncomputable section

open Complex Filter Topology WeierstrassCurve

namespace PeriodPair

variable (L : PeriodPair) {z w : ℂ}

private lemma countable_lattice : (L.lattice : Set ℂ).Countable :=
  countable_of_Lindelof_of_discrete (X := L.lattice)

/-- Every point has a punctured neighbourhood avoiding the lattice. -/
private lemma eventually_notMem_lattice (l₀ : ℂ) : ∀ᶠ u in 𝓝[≠] l₀, u ∉ L.lattice := by
  filter_upwards [nhdsWithin_le_nhds (L.compl_lattice_sdiff_singleton_mem_nhds l₀),
    self_mem_nhdsWithin] with u hu hne using fun h ↦ hu ⟨h, hne⟩

/-! ### The second derivative of `℘` -/

/-- Off the lattice, `℘` has derivative `℘'`. -/
lemma hasDerivAt_weierstrassP (hz : z ∉ L.lattice) : HasDerivAt ℘[L] (℘'[L] z) z := by
  simpa using (L.analyticOnNhd_weierstrassP z hz).differentiableAt.hasDerivAt

/-- **`℘'' = 6 ℘² - g₂ / 2`.** Off the lattice, `℘'` has derivative `6 ℘² - g₂ / 2`. -/
theorem hasDerivAt_derivWeierstrassP (hz : z ∉ L.lattice) :
    HasDerivAt ℘'[L] (6 * ℘[L] z ^ 2 - L.g₂ / 2) z := by
  have hopen := L.isClosed_lattice.isOpen_compl
  -- Differentiating `℘'² = 4 ℘³ - g₂ ℘ - g₃` gives `℘' (℘'' - 6 ℘² + g₂ / 2) = 0` off `Λ`.
  have hmul : ∀ u ∉ L.lattice,
      ℘'[L] u * (deriv ℘'[L] u - (6 * ℘[L] u ^ 2 - L.g₂ / 2)) = 0 := by
    intro u hu
    have h℘ := L.hasDerivAt_weierstrassP hu
    have h1 := ((L.analyticOnNhd_derivWeierstrassP u hu).differentiableAt.hasDerivAt).pow 2
    have h2 := (((h℘.pow 3).const_mul 4).sub (h℘.const_mul L.g₂)).sub_const L.g₃
    have heq : (fun v ↦ ℘'[L] v ^ 2) =ᶠ[𝓝 u]
        fun v ↦ 4 * ℘[L] v ^ 3 - L.g₂ * ℘[L] v - L.g₃ := by
      filter_upwards [hopen.mem_nhds hu] with v hv using L.derivWeierstrassP_sq v hv
    have := h1.unique (h2.congr_of_eventuallyEq heq)
    linear_combination this / 2
  have hk : ContinuousAt (fun u ↦ deriv ℘'[L] u - (6 * ℘[L] u ^ 2 - L.g₂ / 2)) z := by
    have := (L.analyticOnNhd_derivWeierstrassP.deriv z hz).continuousAt
    have := (L.analyticOnNhd_weierstrassP z hz).continuousAt
    fun_prop
  have hz' : deriv ℘'[L] z = 6 * ℘[L] z ^ 2 - L.g₂ / 2 := by
    rcases (L.analyticOnNhd_derivWeierstrassP z hz).eventually_eq_zero_or_eventually_ne_zero
      with h | h
    · -- `℘'` cannot vanish near `z`: it would then vanish on the connected set `Λᶜ`, but it has
      -- no zeros near `0`.
      have h0 := L.analyticOnNhd_derivWeierstrassP.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (L.countable_lattice.isConnected_compl_of_one_lt_rank (by simp)).isPreconnected hz h
      obtain ⟨u, hu, hul⟩ := ((L.eventually_derivWeierstrassP_ne_zero (zero_mem _)).and
        (L.eventually_notMem_lattice 0)).exists
      exact (hu (h0 hul)).elim
    · refine sub_eq_zero.mp (tendsto_nhds_unique
        (hk.tendsto.mono_left (nhdsWithin_le_nhds (s := {z}ᶜ))) (tendsto_const_nhds.congr' ?_))
      filter_upwards [h, L.eventually_notMem_lattice z] with u hu hul
      exact ((mul_eq_zero.mp (hmul u hul)).resolve_left hu).symm
  exact hz' ▸ (L.analyticOnNhd_derivWeierstrassP z hz).differentiableAt.hasDerivAt

/-- `℘'' = 6 ℘² - g₂ / 2` off the lattice. -/
lemma deriv_derivWeierstrassP (hz : z ∉ L.lattice) :
    deriv ℘'[L] z = 6 * ℘[L] z ^ 2 - L.g₂ / 2 :=
  (L.hasDerivAt_derivWeierstrassP hz).deriv

/-! ### The addition theorem for `℘` and `℘'` -/

/-- Along the line `z + w = s`, the function `℘(z) + ℘(w) - ((℘'(z) - ℘'(w)) / (2 (℘(z) - ℘(w))))²`
has derivative zero. -/
private lemma hasDerivAt_addition (s : ℂ) (hz : z ∉ L.lattice) (hsz : s - z ∉ L.lattice)
    (hne : ℘[L] z ≠ ℘[L] (s - z)) :
    HasDerivAt (fun u ↦ ℘[L] u + ℘[L] (s - u) -
      ((℘'[L] u - ℘'[L] (s - u)) / (2 * (℘[L] u - ℘[L] (s - u)))) ^ 2) 0 z := by
  have h1 := L.hasDerivAt_weierstrassP hz
  have h2 := (L.hasDerivAt_weierstrassP hsz).comp_const_sub s z
  have hD : 2 * (℘[L] z - ℘[L] (s - z)) ≠ 0 := mul_ne_zero two_ne_zero (sub_ne_zero.mpr hne)
  convert (h1.add h2).sub ((((L.hasDerivAt_derivWeierstrassP hz).sub
    ((L.hasDerivAt_derivWeierstrassP hsz).comp_const_sub s z)).div
      ((h1.sub h2).const_mul 2) hD).pow 2) using 1
  have hne' := sub_ne_zero.mpr hne
  simp only [Pi.sub_apply, Pi.div_apply, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  field_simp
  linear_combination -2 * (℘'[L] z - ℘'[L] (s - z)) *
    (L.derivWeierstrassP_sq z hz - L.derivWeierstrassP_sq _ hsz)

/-- `℘(z) = ℘_0(z) + 1 / z²` with `℘_0 = PeriodPair.weierstrassPExcept L 0` holomorphic at `0`. -/
private lemma weierstrassP_eq_weierstrassPExcept_zero (z : ℂ) :
    ℘[L] z = L.weierstrassPExcept 0 z + 1 / z ^ 2 := by
  simp [L.weierstrassPExcept_def ⟨0, zero_mem _⟩]

/-- `℘'(z) = ℘'_0(z) - 2 / z³` with `℘'_0 = PeriodPair.derivWeierstrassPExcept L 0` holomorphic
at `0`. -/
private lemma derivWeierstrassP_eq_derivWeierstrassPExcept_zero (z : ℂ) :
    ℘'[L] z = L.derivWeierstrassPExcept 0 z - 2 / z ^ 3 := by
  simp [L.derivWeierstrassPExcept_def ⟨0, zero_mem _⟩]

/-- Near `0`, `℘` avoids every function continuous at `0`, since `℘` has a pole there. -/
private lemma eventually_weierstrassP_ne {g : ℂ → ℂ} (hg : ContinuousAt g 0) :
    ∀ᶠ t in 𝓝[≠] 0, ℘[L] t ≠ g t := by
  have hcont : ContinuousAt (fun t ↦ 1 + t ^ 2 * (L.weierstrassPExcept 0 t - g t)) 0 := by
    have := (L.analyticAt_weierstrassPExcept 0).continuousAt
    fun_prop
  filter_upwards [nhdsWithin_le_nhds (hcont.eventually_ne
    (by simp : 1 + (0 : ℂ) ^ 2 * (L.weierstrassPExcept 0 0 - g 0) ≠ 0)), self_mem_nhdsWithin]
    with t ht (ht0 : t ≠ 0) heq
  apply ht
  rw [← heq, L.weierstrassP_eq_weierstrassPExcept_zero]
  field_simp
  ring

/-- As `z → 0`, `℘(z) + ℘(s - z) - ((℘'(z) - ℘'(s - z)) / (2 (℘(z) - ℘(s - z))))²` tends to
`-℘(s)`. -/
private lemma tendsto_addition (s : ℂ) (hs : s ∉ L.lattice) :
    Tendsto (fun z ↦ ℘[L] z + ℘[L] (s - z) -
      ((℘'[L] z - ℘'[L] (s - z)) / (2 * (℘[L] z - ℘[L] (s - z)))) ^ 2) (𝓝[≠] 0)
      (𝓝 (-℘[L] s)) := by
  -- With `a = ℘_0(z)`, `b = ℘'_0(z)`, `p = ℘(s - z)`, `q = ℘'(s - z)` and `D = 1 + z² (a - p)`,
  -- the function is `F(z) = a + p - (z⁴ (b - q)² - 4 z (b - q) - 8 (a - p) - 4 z² (a - p)²) /
  -- (4 D²)` for `z ≠ 0`, and `F` is continuous at `0` with `F(0) = -℘(s)`.
  set D : ℂ → ℂ := fun z ↦ 1 + z ^ 2 * (L.weierstrassPExcept 0 z - ℘[L] (s - z))
  set F : ℂ → ℂ := fun z ↦ L.weierstrassPExcept 0 z + ℘[L] (s - z) -
    (z ^ 4 * (L.derivWeierstrassPExcept 0 z - ℘'[L] (s - z)) ^ 2 -
      4 * z * (L.derivWeierstrassPExcept 0 z - ℘'[L] (s - z)) -
      8 * (L.weierstrassPExcept 0 z - ℘[L] (s - z)) -
      4 * z ^ 2 * (L.weierstrassPExcept 0 z - ℘[L] (s - z)) ^ 2) / (4 * D z ^ 2)
  have hs' : s - 0 ∉ L.lattice := by simpa using hs
  have hp : ContinuousAt (fun z ↦ ℘[L] (s - z)) 0 :=
    (L.analyticOnNhd_weierstrassP _ hs').continuousAt.comp (by fun_prop)
  have hq : ContinuousAt (fun z ↦ ℘'[L] (s - z)) 0 :=
    (L.analyticOnNhd_derivWeierstrassP _ hs').continuousAt.comp (by fun_prop)
  have ha := (L.analyticAt_weierstrassPExcept 0).continuousAt
  have hb := (L.analyticAt_derivWeierstrassPExcept 0).continuousAt
  have hD0 : D 0 = 1 := by simp [D]
  have hF : ContinuousAt F 0 :=
    (by fun_prop : ContinuousAt (fun z ↦ L.weierstrassPExcept 0 z + ℘[L] (s - z)) 0).sub
      ((by fun_prop : ContinuousAt (fun z ↦ z ^ 4 *
        (L.derivWeierstrassPExcept 0 z - ℘'[L] (s - z)) ^ 2 -
        4 * z * (L.derivWeierstrassPExcept 0 z - ℘'[L] (s - z)) -
        8 * (L.weierstrassPExcept 0 z - ℘[L] (s - z)) -
        4 * z ^ 2 * (L.weierstrassPExcept 0 z - ℘[L] (s - z)) ^ 2) 0).div
        (by fun_prop) (by simp [hD0]))
  have hF0 : F 0 = -℘[L] s := by
    simp only [F, hD0]
    norm_num
    ring
  refine hF0 ▸ (hF.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [L.eventually_weierstrassP_ne hp, self_mem_nhdsWithin] with z hne (hz0 : z ≠ 0)
  have key : ℘[L] z - ℘[L] (s - z) = D z / z ^ 2 := by
    simp only [D, L.weierstrassP_eq_weierstrassPExcept_zero z]
    field_simp
    ring
  have hDz : D z ≠ 0 := by
    have := sub_ne_zero.mpr hne
    rw [key] at this
    exact (div_ne_zero_iff.mp this).1
  simp only [F, key]
  rw [L.weierstrassP_eq_weierstrassPExcept_zero z,
    L.derivWeierstrassP_eq_derivWeierstrassPExcept_zero z]
  field_simp
  simp only [D]
  ring

/-- The addition theorem holds in the form `4 (℘(z) + ℘(s - z) + ℘(s)) (℘(z) - ℘(s - z))² =
(℘'(z) - ℘'(s - z))²` on a nonempty open set of `z` near `0`: the function of
`PeriodPair.hasDerivAt_addition` is constant on a convex open set accumulating at `0`, and its
limit at `0` is `-℘(s)`. -/
private lemma exists_isOpen_addition (s : ℂ) (hs : s ∉ L.lattice) :
    ∃ V : Set ℂ, IsOpen V ∧ V.Nonempty ∧ ∀ z ∈ V, z ∉ L.lattice ∧ s - z ∉ L.lattice ∧
      4 * (℘[L] z + ℘[L] (s - z) + ℘[L] s) * (℘[L] z - ℘[L] (s - z)) ^ 2 =
        (℘'[L] z - ℘'[L] (s - z)) ^ 2 := by
  set h : ℂ → ℂ := fun z ↦ ℘[L] z + ℘[L] (s - z) -
    ((℘'[L] z - ℘'[L] (s - z)) / (2 * (℘[L] z - ℘[L] (s - z)))) ^ 2
  -- Choose a radius `r` such that the punctured disc of radius `r` avoids `Λ` and `s - Λ`, and
  -- `℘(z) ≠ ℘(s - z)` on it; then take `V` to be its right half.
  have hp : ContinuousAt (fun z ↦ ℘[L] (s - z)) 0 :=
    (L.analyticOnNhd_weierstrassP (s - 0) (by simpa using hs)).continuousAt.comp (by fun_prop)
  have hev : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 →
      z ∉ L.lattice ∧ s - z ∉ L.lattice ∧ ℘[L] z ≠ ℘[L] (s - z) := by
    filter_upwards [eventually_nhdsWithin_iff.mp (L.eventually_notMem_lattice 0),
      (by fun_prop : ContinuousAt (fun z : ℂ ↦ s - z) 0).eventually
        (L.isClosed_lattice.isOpen_compl.mem_nhds (by simpa using hs)),
      eventually_nhdsWithin_iff.mp (L.eventually_weierstrassP_ne hp)] with z h₁ h₂ h₃ hz
      using ⟨h₁ hz, h₂, h₃ hz⟩
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  set V : Set ℂ := Metric.ball 0 r ∩ {z | 0 < z.re}
  have hVopen : IsOpen V := Metric.isOpen_ball.inter (isOpen_lt continuous_const continuous_re)
  have hV0 : V ⊆ {0}ᶜ := fun z hz h ↦ by simp_all [V]
  have hV : ∀ z ∈ V, z ∉ L.lattice ∧ s - z ∉ L.lattice ∧ ℘[L] z ≠ ℘[L] (s - z) := fun z hz ↦
    hball z hz.1 (hV0 hz)
  have hconst : ∀ z ∈ V, ∀ z' ∈ V, h z = h z' := fun z hz z' hz' ↦
    hVopen.is_const_of_deriv_eq_zero
      ((convex_ball _ _).inter (convex_halfSpace_re_gt 0)).isPreconnected
      (fun u hu ↦ (L.hasDerivAt_addition s (hV u hu).1 (hV u hu).2.1 (hV u hu).2.2)
        |>.differentiableAt.differentiableWithinAt)
      (fun u hu ↦ (L.hasDerivAt_addition s (hV u hu).1 (hV u hu).2.1 (hV u hu).2.2).deriv) hz hz'
  have hcl : (0 : ℂ) ∈ closure V := by
    refine Metric.mem_closure_iff.mpr fun ε hε ↦ ?_
    have hm : 0 < min ε r := lt_min hε hr
    refine ⟨(min ε r / 2 : ℝ), ⟨?_, ?_⟩, ?_⟩
    · simpa [abs_of_pos hm] using (half_lt_self hm).trans_le (min_le_right _ _)
    · simpa using hm
    · simpa [abs_of_pos hm] using (half_lt_self hm).trans_le (min_le_left _ _)
  have hval : ∀ z ∈ V, h z = -℘[L] s := by
    intro z hz
    have := mem_closure_iff_nhdsWithin_neBot.mp hcl
    refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_)
      ((L.tendsto_addition s hs).mono_left (nhdsWithin_mono _ hV0))
    filter_upwards [self_mem_nhdsWithin] with u hu using hconst z hz u hu
  refine ⟨V, hVopen, closure_nonempty_iff.mp ⟨0, hcl⟩, fun z hz ↦ ⟨(hV z hz).1, (hV z hz).2.1, ?_⟩⟩
  have h' := hval z hz
  have hne' := sub_ne_zero.mpr (hV z hz).2.2
  simp only [h] at h'
  field_simp at h'
  linear_combination h'

/-- The addition theorem in polynomial form, which also covers `℘(z) = ℘(w)`: by the identity
theorem it extends from the open set of `PeriodPair.exists_isOpen_addition` to the connected set
of all `z` with `z, s - z ∉ Λ`. -/
private lemma addition_poly (hz : z ∉ L.lattice) (hw : w ∉ L.lattice) (hzw : z + w ∉ L.lattice) :
    4 * (℘[L] z + ℘[L] w + ℘[L] (z + w)) * (℘[L] z - ℘[L] w) ^ 2 = (℘'[L] z - ℘'[L] w) ^ 2 := by
  set s := z + w
  obtain ⟨V, hVo, ⟨z₀, hz₀⟩, hV⟩ := L.exists_isOpen_addition s hzw
  set U : Set ℂ := (↑L.lattice ∪ (s - ·) ⁻¹' ↑L.lattice)ᶜ
  have hU : IsPreconnected U :=
    ((L.countable_lattice.union (L.countable_lattice.preimage sub_right_injective)
      ).isConnected_compl_of_one_lt_rank (by simp)).isPreconnected
  have hmem : ∀ {u}, u ∉ L.lattice → s - u ∉ L.lattice → u ∈ U := fun h₁ h₂ ↦ by
    simp [U, h₁, h₂]
  have han : AnalyticOnNhd ℂ (fun u ↦ 4 * (℘[L] u + ℘[L] (s - u) + ℘[L] s) *
      (℘[L] u - ℘[L] (s - u)) ^ 2 - (℘'[L] u - ℘'[L] (s - u)) ^ 2) U := by
    intro u hu
    simp only [U, Set.mem_compl_iff, Set.mem_union, Set.mem_preimage, SetLike.mem_coe,
      not_or] at hu
    have h₁ := L.analyticOnNhd_weierstrassP u hu.1
    have h₂ : AnalyticAt ℂ (fun u ↦ ℘[L] (s - u)) u :=
      (L.analyticOnNhd_weierstrassP (s - u) hu.2).comp (by fun_prop)
    have h₃ := L.analyticOnNhd_derivWeierstrassP u hu.1
    have h₄ : AnalyticAt ℂ (fun u ↦ ℘'[L] (s - u)) u :=
      (L.analyticOnNhd_derivWeierstrassP (s - u) hu.2).comp (by fun_prop)
    fun_prop
  have h0 := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU
    (hmem (hV z₀ hz₀).1 (hV z₀ hz₀).2.1)
    (by filter_upwards [hVo.mem_nhds hz₀] with u hu using sub_eq_zero.mpr (hV u hu).2.2)
  have h := sub_eq_zero.mp (h0 (hmem hz (by simpa [s] using hw)))
  simpa [s] using h

private lemma add_notMem_lattice_of_weierstrassP_ne (h : ℘[L] z ≠ ℘[L] w) :
    z + w ∉ L.lattice := fun hzw ↦ h <| by
  rw [show w = -z + ((⟨z + w, hzw⟩ : L.lattice) : ℂ) by simp, L.weierstrassP_add_coe,
    weierstrassP_neg]

/-- **The addition theorem for `℘`.** If `z, w ∉ Λ` and `℘(z) ≠ ℘(w)`, then
`℘(z + w) = ((℘'(z) - ℘'(w)) / (℘(z) - ℘(w)))² / 4 - ℘(z) - ℘(w)`. -/
theorem weierstrassP_add (hz : z ∉ L.lattice) (hw : w ∉ L.lattice) (h : ℘[L] z ≠ ℘[L] w) :
    ℘[L] (z + w) = ((℘'[L] z - ℘'[L] w) / (℘[L] z - ℘[L] w)) ^ 2 / 4 - ℘[L] z - ℘[L] w := by
  have := L.addition_poly hz hw (L.add_notMem_lattice_of_weierstrassP_ne h)
  have h' := sub_ne_zero.mpr h
  field_simp
  linear_combination this

/-- **The addition theorem for `℘'`.** If `z, w ∉ Λ` and `℘(z) ≠ ℘(w)`, then
`℘'(z + w) = -m (℘(z + w) - ℘(z)) - ℘'(z)` with `m = (℘'(z) - ℘'(w)) / (℘(z) - ℘(w))`: the points
`(℘(z), ℘'(z))`, `(℘(w), ℘'(w))` and `(℘(z + w), -℘'(z + w))` lie on a line of slope `m`. -/
theorem derivWeierstrassP_add (hz : z ∉ L.lattice) (hw : w ∉ L.lattice) (h : ℘[L] z ≠ ℘[L] w) :
    ℘'[L] (z + w) =
      -((℘'[L] z - ℘'[L] w) / (℘[L] z - ℘[L] w)) * (℘[L] (z + w) - ℘[L] z) - ℘'[L] z := by
  -- Differentiate `PeriodPair.weierstrassP_add` with respect to `z`.
  have hzw := L.add_notMem_lattice_of_weierstrassP_ne h
  have hev : (fun u ↦ ℘[L] (u + w)) =ᶠ[𝓝 z]
      fun u ↦ ((℘'[L] u - ℘'[L] w) / (℘[L] u - ℘[L] w)) ^ 2 / 4 - ℘[L] u - ℘[L] w := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz,
      (L.analyticOnNhd_weierstrassP z hz).continuousAt.eventually_ne h] with u hu hne
      using L.weierstrassP_add hu hw hne
  have h₁ := L.hasDerivAt_weierstrassP hz
  have h' := sub_ne_zero.mpr h
  have hd := ((((((L.hasDerivAt_derivWeierstrassP hz).sub_const (℘'[L] w)).div
    (h₁.sub_const (℘[L] w)) h').pow 2).div_const 4).sub h₁).sub_const (℘[L] w)
  have := ((L.hasDerivAt_weierstrassP hzw).comp_add_const z w).unique
    (hd.congr_of_eventuallyEq hev)
  rw [this, L.weierstrassP_add hz hw h]
  simp only [Pi.div_apply, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  field_simp
  linear_combination
    -(℘'[L] z - ℘'[L] w) * (L.derivWeierstrassP_sq z hz - L.derivWeierstrassP_sq w hw)

/-! ### The group law -/

/-- The chord case of the group law: for `z, w ∉ Λ` with `℘(z) ≠ ℘(w)`, the points `P(z)` and
`P(w)` have distinct `x`-coordinates, and their sum is `P(z + w)` by the addition theorems. -/
private lemma weierstrassPoint_add_of_weierstrassP_ne (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (h : ℘[L] z ≠ ℘[L] w) :
    L.weierstrassPoint (z + w) = L.weierstrassPoint z + L.weierstrassPoint w := by
  have hzw := L.add_notMem_lattice_of_weierstrassP_ne h
  have h' := sub_ne_zero.mpr h
  rw [L.weierstrassPoint_of_notMem hz, L.weierstrassPoint_of_notMem hw,
    L.weierstrassPoint_of_notMem hzw, Affine.Point.add_of_X_ne h, Affine.Point.some.injEq,
    Affine.slope_of_X_ne h]
  simp only [Affine.addY, Affine.negAddY, Affine.addX, Affine.negY, weierstrassCurve_a₁,
    weierstrassCurve_a₂, weierstrassCurve_a₃]
  constructor
  · rw [L.weierstrassP_add hz hw h]
    field_simp
    ring
  · rw [L.derivWeierstrassP_add hz hw h, L.weierstrassP_add hz hw h]
    field_simp
    ring

/-- For `w ∉ Λ`, `℘(w + t) ≠ ℘(w)` for all small `t ≠ 0`. Otherwise `℘` would be constant near
`w`, so `℘'(w) = ℘''(w) = 0` and `(℘(w), ℘'(w) / 2)` would be a singular point of the curve. -/
private lemma eventually_weierstrassP_add_ne (hw : w ∉ L.lattice) :
    ∀ᶠ t in 𝓝[≠] 0, ℘[L] (w + t) ≠ ℘[L] w := by
  have hw' : w + 0 ∉ L.lattice := by simpa using hw
  have hev : ∀ᶠ t in 𝓝 (0 : ℂ), w + t ∉ L.lattice :=
    (by fun_prop : ContinuousAt (fun t : ℂ ↦ w + t) 0).eventually
      (L.isClosed_lattice.isOpen_compl.mem_nhds hw')
  have han : AnalyticAt ℂ (fun t ↦ ℘[L] (w + t) - ℘[L] w) 0 :=
    ((L.analyticOnNhd_weierstrassP _ hw').comp (by fun_prop)).sub analyticAt_const
  rcases han.eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    -- The derivative `t ↦ ℘'(w + t)` of `t ↦ ℘(w + t) - ℘(w)` vanishes near `0`.
    have h' : (fun t ↦ ℘[L] (w + t) - ℘[L] w) =ᶠ[𝓝 0] 0 := h
    have hd : (fun t ↦ ℘'[L] (w + t)) =ᶠ[𝓝 0] 0 := by
      filter_upwards [h'.deriv, hev] with t ht htl
      rw [← ((L.hasDerivAt_weierstrassP htl).comp_const_add w t).sub_const (℘[L] w) |>.deriv, ht]
      simp
    have h₁ : ℘'[L] w = 0 := by simpa using hd.self_of_nhds
    have h₂ : 6 * ℘[L] w ^ 2 - L.g₂ / 2 = 0 := by
      simpa using ((L.hasDerivAt_derivWeierstrassP hw').comp_const_add w 0).unique
        ((hasDerivAt_const (0 : ℂ) (0 : ℂ)).congr_of_eventuallyEq hd)
    have hns := (Affine.nonsingular_iff _ _).mp (L.nonsingular_weierstrassP hw)
    simp only [weierstrassCurve_a₁, weierstrassCurve_a₂, weierstrassCurve_a₃, weierstrassCurve_a₄,
      h₁] at hns
    rcases hns.2 with h | h
    · exact h (by linear_combination -h₂ / 2)
    · exact h (by ring)
  · filter_upwards [h] with t ht using sub_ne_zero.mp ht

/-- **The addition law.** The point map `z ↦ (℘(z), ℘'(z) / 2)` (sending `Λ` to the point at
infinity) is additive: `P(z + w) = P(z) + P(w)` in the group of points of the Weierstrass curve. -/
@[simp]
theorem weierstrassPoint_add (z w : ℂ) :
    L.weierstrassPoint (z + w) = L.weierstrassPoint z + L.weierstrassPoint w := by
  by_cases hz : z ∈ L.lattice
  · rw [add_comm, L.weierstrassPoint_add_coe w ⟨z, hz⟩, L.weierstrassPoint_of_mem hz, zero_add]
  by_cases hw : w ∈ L.lattice
  · rw [L.weierstrassPoint_add_coe z ⟨w, hw⟩, L.weierstrassPoint_of_mem hw, add_zero]
  by_cases hzw : z + w ∈ L.lattice
  · rw [L.weierstrassPoint_of_mem hzw, show w = -z + ((⟨z + w, hzw⟩ : L.lattice) : ℂ) by simp,
      L.weierstrassPoint_add_coe, weierstrassPoint_neg, add_neg_cancel]
  rcases ne_or_eq (℘[L] z) (℘[L] w) with h | h
  · exact L.weierstrassPoint_add_of_weierstrassP_ne hz hw h
  -- If `℘(z) = ℘(w)`, cancel `P(t)` in `P(z + w) + P(t) = P(z + w + t) = P(z) + P(w + t) =
  -- P(z) + P(w) + P(t)`, where every equality is a chord case for a suitable small `t ≠ 0`.
  have hev : ∀ᶠ t in 𝓝 (0 : ℂ), w + t ∉ L.lattice := by
    have hw' : w + 0 ∉ L.lattice := by simpa using hw
    exact (by fun_prop : ContinuousAt (fun t : ℂ ↦ w + t) 0).eventually
      (L.isClosed_lattice.isOpen_compl.mem_nhds hw')
  obtain ⟨t, ht, ht₁, ht₂, ht₃, ht₄⟩ := ((L.eventually_notMem_lattice 0).and
    ((L.eventually_weierstrassP_ne continuousAt_const).and
    ((L.eventually_weierstrassP_ne continuousAt_const).and
    ((L.eventually_weierstrassP_add_ne hw).and (nhdsWithin_le_nhds hev))))).exists
  have e₁ := L.weierstrassPoint_add_of_weierstrassP_ne hzw ht (Ne.symm ht₁)
  have e₂ := L.weierstrassPoint_add_of_weierstrassP_ne hz ht₄ (h ▸ ht₃.symm)
  have e₃ := L.weierstrassPoint_add_of_weierstrassP_ne hw ht (Ne.symm ht₂)
  rw [add_assoc, e₂, e₃, ← add_assoc] at e₁
  exact (add_right_cancel e₁).symm

/-- The point map `z ↦ (℘(z), ℘'(z) / 2)` as a group homomorphism from `ℂ` to the points of the
Weierstrass curve of `L`. -/
def weierstrassPointHom : ℂ →+ L.weierstrassCurve.toAffine.Point where
  toFun := L.weierstrassPoint
  map_zero' := L.weierstrassPoint_zero
  map_add' := L.weierstrassPoint_add

@[simp]
lemma weierstrassPointHom_apply (z : ℂ) : L.weierstrassPointHom z = L.weierstrassPoint z := (rfl)

/-- The kernel of the point map is the period lattice. -/
lemma ker_weierstrassPointHom : L.weierstrassPointHom.ker = L.lattice.toAddSubgroup := by
  ext z
  simp

end PeriodPair
