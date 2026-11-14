/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Kernel.Dimension
public import TauCeti.Analysis.PDE.Vortex.Kernel.Existence
import TauCeti.Analysis.Analytic.Order
import TauCeti.Analysis.Calculus.IteratedDeriv.Leibniz
import TauCeti.Analysis.Complex.Wirtinger.DolbeaultLemma
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Isomorphism of the gauge-fixed vortex kernel with principal-part data

Let `x` be a smooth field on the plane whose holomorphicity rows `∂bar_a α = 0` vanish, with
`|α| → 1` at infinity, and let `D` be the zero divisor of its section `α = 2 (p + i q)`. For any
integrating factor `ν` solving `∂bar ν = (b₂ - i b₁) / 2`, the entire function `f = e^(-ν) α` has
zero multiplicities given by `D`, and every variation `y` in the `C²` square-integrable kernel
`gaugeFixedKernel x` of the gauge-fixed operator `L_x = d₀* ⊕ d₁` decomposes as
`δα = α G + e^ν H` with `G` continuous and `H` entire. Recording the Taylor derivatives
`H⁽ʲ⁾(z)` for `j < count z D` defines the real-linear principal-part map `principalPartMap` from
`gaugeFixedKernel x` to `D → ℂ`, proved injective in `TauCeti.Analysis.PDE.Vortex.PrincipalPart`.

This file proves that `principalPartMap` is surjective onto `D → ℂ` and hence a real-linear
isomorphism (`gaugeFixedKernelEquivPrincipalPart`). By
`TauCeti.IsZeroMultiplicity.exists_differentiable_eq_prod_pow_mul`, the entire section factor is
`f(w) = (∏_{a ∈ D} (w - a)^{D(a)}) g(w)` with `g` entire and zero-free. A smooth `L²` kernel
element with a single pole `c / (w - z)^{j+1}` at a zero `z` of multiplicity `n = D(z)`
(`TauCeti.Vortex.exists_gaugeFixedOperator_eq_zero_sectionValue_eq_mul_div_pow_add`) therefore has
holomorphic numerator `H(w) = c (w - z)^p R(w)`, where `p = n - 1 - j` and
`R(w) = (∏_{a ≠ z} (w - a)^{D(a)}) g(w)`:

* at every other zero `a ≠ z`, `R` vanishes to order `D(a)`, so all principal-part data of `y` at
  `a` vanish;
* at `z` itself, `H` vanishes to order `p`, and its `p`-th derivative at `z` is `p! c R(z)` with
  `R(z) ≠ 0` (`TauCeti.iteratedDeriv_pow_sub_smul_self`).

Distinct zeros thus decouple completely, and at each zero `z` the map from pole residues to
derivatives `H⁽ᵖ⁾(z)`, `p < D(z)`, is triangular with nonzero diagonal. Back-substitution produces
a smooth (`C^∞`) kernel element realizing any prescribed principal-part tuple
(`exists_contDiff_mem_gaugeFixedKernel_principalPart_eq`).

Combining surjectivity on smooth kernel elements with injectivity on all `C²` square-integrable
kernel elements shows simultaneously that every element of `gaugeFixedKernel x` is smooth
(`contDiff_of_mem_gaugeFixedKernel`) and that `gaugeFixedKernel x` has exact real dimension
`2 |D|` (`finrank_gaugeFixedKernel_eq_two_mul_card`), hence `2 m` when `α` carries the degree-`m`
end framing `α(z) (z / |z|)⁻ᵐ → 1` (`finrank_gaugeFixedKernel_eq_two_mul`). The comparison with
the weak `L²` and Sobolev `H^s` kernels of `L_x` is proved in
`TauCeti.Analysis.PDE.Vortex.Kernel.Weak`; no Fredholm operator bundle is constructed here.

## Main declarations

* `TauCeti.Vortex.exists_contDiff_mem_gaugeFixedKernel_principalPart_eq`: every tuple in `D → ℂ`
  is the principal-part data of a smooth element of `gaugeFixedKernel x`.
* `TauCeti.Vortex.principalPartMap_surjective` and `TauCeti.Vortex.principalPartMap_bijective`:
  surjectivity and bijectivity of `principalPartMap` on `gaugeFixedKernel x`.
* `TauCeti.Vortex.gaugeFixedKernelEquivPrincipalPart`: the real-linear equivalence
  `gaugeFixedKernel x ≃ₗ[ℝ] (Multiset.ToType D → ℂ)`.
* `TauCeti.Vortex.contDiff_of_mem_gaugeFixedKernel`: every element of `gaugeFixedKernel x` is
  smooth.
* `TauCeti.Vortex.finiteDimensional_gaugeFixedKernel_of_tendsto_normSq`,
  `TauCeti.Vortex.finrank_gaugeFixedKernel_eq_two_mul_card`, and
  `TauCeti.Vortex.finrank_gaugeFixedKernel_eq_two_mul`: finite-dimensionality and exact real
  dimension `2 |D|` (and `2 m` under degree-`m` framing) of `gaugeFixedKernel x`.

## References

* T. M. Samols, *Vortex scattering*, Comm. Math. Phys. 145 (1992), 149–179.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public noncomputable section

namespace TauCeti.Vortex

open Complex Filter MeasureTheory
open scoped ContDiff Topology

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)} {D : Multiset ℂ}

/-- Every variation `y ∈ gaugeFixedKernel x` at a differentiable field satisfying the
holomorphicity rows admits a decomposition `δα = α G + e^ν H` with `G` continuous and `H` entire,
supplying the domain hypothesis of `TauCeti.Vortex.principalPartMap`. -/
theorem exists_continuous_and_differentiable_sectionValue_eq_of_mem_gaugeFixedKernel
    (hx : Differentiable ℝ x) (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    {ν : ℂ → ℂ} (hν : Differentiable ℝ ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2)
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ gaugeFixedKernel x) :
    ∃ G : ℂ → ℂ, Continuous G ∧ ∃ H : ℂ → ℂ, Differentiable ℂ H ∧
      ∀ w, sectionValue y w = sectionValue x w * G w + exp (ν w) * H w := by
  obtain ⟨hyc, -, hker⟩ := mem_gaugeFixedKernel.1 hy
  have hxi (i : Fin 4) : Differentiable ℝ fun w ↦ x w i :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).differentiable.comp hx
  have hyi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ y w i := contDiff_euclidean.1 hyc i
  have hlin (w : ℂ) : linearizedEquation x y w 1 = 0 ∧ linearizedEquation x y w 2 = 0 := by
    refine ⟨?_, ?_⟩
    · rw [← gaugeFixedOperator_apply_two, hker w, PiLp.zero_apply]
    · rw [← gaugeFixedOperator_apply_three, hker w, PiLp.zero_apply]
  obtain ⟨G, hG, H, hH, hGH⟩ := exists_sectionValue_eq_mul_add_exp_mul (k := 2) (by norm_num)
    (hxi 2) (hxi 3) hhol hν hνeq (hyi 0) (hyi 1) ((hyi 2).differentiable (by norm_num))
    ((hyi 3).differentiable (by norm_num)) hlin
  exact ⟨G, hG.continuous, H, hH, hGH⟩

/-- A single-pole kernel element of order `j + 1 = D(z) - p` at `z` has section variation
`δα = α ξ + e^ν (c (w - z)^p R(w))` across the whole plane, where `R` is the complementary
divisor product times the entire zero-free cofactor `g`. -/
private theorem exists_contDiff_mem_gaugeFixedKernel_sectionValue_eq (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) {ν g : ℂ → ℂ}
    (hν : Continuous ν) (hg : Differentiable ℂ g)
    (hfg : ∀ w, exp (-ν w) * sectionValue x w = (∏ a ∈ D.toFinset, (w - a) ^ D.count a) * g w)
    {z : ℂ} {p : ℕ} (hp_lt : p < D.count z) (c : ℂ) :
    ∃ y : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ y ∧ y ∈ gaugeFixedKernel x ∧
      ∃ ξ : ℂ → ℂ, ContDiff ℝ ∞ ξ ∧ ∀ w, sectionValue y w = sectionValue x w * ξ w +
        exp (ν w) * (c * ((w - z) ^ p *
          ((∏ a ∈ D.toFinset.erase z, (w - a) ^ D.count a) * g w))) := by
  have hxi (i : Fin 4) : ContDiff ℝ ∞ fun w ↦ x w i := contDiff_euclidean.1 hx i
  choose N v hv hv₀ hvf using fun a ↦
    exists_contDiffAt_sectionValue_eq_pow_mul (k := ⊤) le_top (by simpa using hxi 0)
      (by simpa using hxi 1) ((hxi 2).differentiable (by simp))
      ((hxi 3).differentiable (by simp)) hhol hD.exists_ne_zero a
  have hN : N = fun a ↦ D.count a :=
    (isZeroMultiplicity_iff.2 fun a ↦ ⟨v a, (hv a).continuousAt, hv₀ a, hvf a⟩).unique hD
  set j : ℕ := D.count z - 1 - p
  have hj_lt : j < D.count z := by omega
  have hjp : (j + 1) + p = D.count z := by omega
  obtain ⟨y, hy, hy₂, hker, ξ, hξ, hyξ⟩ :=
    exists_gaugeFixedOperator_eq_zero_sectionValue_eq_mul_div_pow_add hx hhol hlim
      (by simpa using hv z) (hN ▸ hvf z) hj_lt c
  set R : ℂ → ℂ := fun w ↦ (∏ a ∈ D.toFinset.erase z, (w - a) ^ D.count a) * g w
  have hz_mem : z ∈ D.toFinset :=
    Multiset.mem_toFinset.2 (Multiset.count_pos.1 (Nat.zero_lt_of_lt hp_lt))
  have hsec (w : ℂ) : sectionValue x w = (w - z) ^ (j + 1) * (exp (ν w) * ((w - z) ^ p * R w)) := by
    have hprod : (w - z) ^ (j + 1) * ((w - z) ^ p * R w) = exp (-ν w) * sectionValue x w := by
      rw [← mul_assoc, ← pow_add, hjp, hfg w,
        ← Finset.mul_prod_erase D.toFinset (fun a ↦ (w - a) ^ D.count a) hz_mem, mul_assoc]
    calc sectionValue x w
        = exp (ν w) * (exp (-ν w) * sectionValue x w) := by
          rw [← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul]
      _ = exp (ν w) * ((w - z) ^ (j + 1) * ((w - z) ^ p * R w)) := by rw [hprod]
      _ = (w - z) ^ (j + 1) * (exp (ν w) * ((w - z) ^ p * R w)) := by ring
  have hcont_lhs : Continuous (sectionValue y) :=
    (contDiff_sectionValue (contDiff_euclidean.1 hy 2) (contDiff_euclidean.1 hy 3)).continuous
  have hR_cont : Continuous R := by
    have := hg.continuous
    unfold R
    fun_prop
  have hcont_rhs : Continuous fun w ↦
      sectionValue x w * ξ w + exp (ν w) * (c * ((w - z) ^ p * R w)) :=
    ((contDiff_sectionValue (hxi 2) (hxi 3)).continuous.mul hξ.continuous).add
      (hν.cexp.mul
        (continuous_const.mul (((continuous_id.sub continuous_const).pow p).mul hR_cont)))
  refine ⟨y, hy, mem_gaugeFixedKernel.2 ⟨hy.of_le (by simp), hy₂, hker⟩, ξ, hξ,
    fun w ↦ congrFun
      (Continuous.ext_on (dense_compl_singleton z) hcont_lhs hcont_rhs fun w' hw' ↦ ?_) w⟩
  have hne : (w' - z) ^ (j + 1) ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hw')
  rw [hyξ w' hw', mul_add, add_comm (sectionValue x w' * _), add_right_inj, hsec w']
  field_simp

/-- **Elementary triangular generator at a single zero and order.** For `p < count z D` and any
`d ∈ ℂ`, there is a smooth `y ∈ gaugeFixedKernel x` whose principal-part data vanish at every
other zero `a ≠ z`, vanish at `z` in all orders `< p`, and take the value `d` at `(z, p)`. -/
private theorem exists_contDiff_mem_gaugeFixedKernel_principalPart_single (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) {ν : ℂ → ℂ}
    (hν : Differentiable ℝ ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2)
    {z : ℂ} {p : ℕ} (hp_lt : p < D.count z) (d : ℂ) :
    ∃ y : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ y ∧ y ∈ gaugeFixedKernel x ∧
      principalPart x ν y z p = d ∧ (∀ k < p, principalPart x ν y z k = 0) ∧
      ∀ a, a ≠ z → ∀ k < D.count a, principalPart x ν y a k = 0 := by
  have hxi (i : Fin 4) : ContDiff ℝ ∞ fun w ↦ x w i := contDiff_euclidean.1 hx i
  have hf_diff : Differentiable ℂ fun w ↦ exp (-ν w) * sectionValue x w :=
    differentiable_exp_neg_mul_sectionValue ((hxi 2).differentiable (by simp))
      ((hxi 3).differentiable (by simp)) hhol hν hνeq
  obtain ⟨g, hg, hg₀, hfg⟩ :=
    (hD.mul_left_of_continuous hν.continuous.neg.cexp fun _ ↦ exp_ne_zero _)
      |>.exists_differentiable_eq_prod_pow_mul hf_diff
  set R : ℂ → ℂ := fun w ↦ (∏ a ∈ D.toFinset.erase z, (w - a) ^ D.count a) * g w
  have hR : Differentiable ℂ R := by
    unfold R
    fun_prop
  have hRz : R z ≠ 0 := mul_ne_zero
    (Finset.prod_ne_zero_iff.2 fun a ha ↦
      pow_ne_zero _ (sub_ne_zero.2 (Finset.ne_of_mem_erase ha).symm)) (hg₀ z)
  have hp_ne : (p.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 p.factorial_ne_zero
  set c : ℂ := d / ((p.factorial : ℂ) * R z)
  obtain ⟨y, hy, hyk, ξ, hξ, hyH⟩ :=
    exists_contDiff_mem_gaugeFixedKernel_sectionValue_eq hx hhol hlim hD hν.continuous hg hfg
      hp_lt c
  set H : ℂ → ℂ := fun w ↦ c * ((w - z) ^ p * R w)
  have hH : Differentiable ℂ H :=
    (differentiable_const c).mul (((differentiable_id.sub_const z).pow p).mul hR)
  have hH_smul : H = fun w ↦ (w - z) ^ p • (c * R w) := by
    ext w; simp only [H, smul_eq_mul]; ring
  have hcR : Differentiable ℂ fun w ↦ c * R w := (differentiable_const c).mul hR
  refine ⟨y, hy, hyk, ?_, fun k hk ↦ ?_, fun a ha k hk ↦ ?_⟩
  · rw [principalPart_eq_iteratedDeriv hD hν.continuous hξ.continuous hH hyH hp_lt, hH_smul,
      iteratedDeriv_pow_sub_smul_self hcR.contDiff.contDiffAt, nsmul_eq_mul]
    dsimp only [c]
    field_simp
  · rw [principalPart_eq_iteratedDeriv hD hν.continuous hξ.continuous hH hyH (hk.trans hp_lt)]
    have hord : (p : ℕ∞) ≤ analyticOrderAt H z :=
      (hH.analyticAt z).natCast_le_analyticOrderAt_of_eventually_eq_pow_smul
        hcR.continuous.continuousAt (Eventually.of_forall (congrFun hH_smul))
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hH.analyticAt z)).1 hord k hk
  · rw [principalPart_eq_iteratedDeriv hD hν.continuous hξ.continuous hH hyH hk]
    have ha_erase : a ∈ D.toFinset.erase z :=
      Finset.mem_erase.2 ⟨ha, Multiset.mem_toFinset.2 (Multiset.count_pos.1 (Nat.zero_lt_of_lt hk))⟩
    set Q : ℂ → ℂ := fun w ↦
      c * ((w - z) ^ p * ((∏ b ∈ (D.toFinset.erase z).erase a, (w - b) ^ D.count b) * g w))
    have hQ : Continuous Q := by
      have := hg.continuous
      unfold Q
      fun_prop
    have hord : (D.count a : ℕ∞) ≤ analyticOrderAt H a :=
      (hH.analyticAt a).natCast_le_analyticOrderAt_of_eventually_eq_pow_smul hQ.continuousAt
        (Eventually.of_forall fun w ↦ by
          simp only [H, R, Q, smul_eq_mul,
            ← Finset.mul_prod_erase (D.toFinset.erase z) (fun b ↦ (w - b) ^ D.count b) ha_erase]
          ring)
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hH.analyticAt a)).1 hord k hk

/-- Back-substitution across the orders `k < m ≤ count z D` at a single zero `z`, vanishing at all
other zeros `a ≠ z`. -/
private theorem exists_contDiff_mem_gaugeFixedKernel_principalPart_at (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) {ν : ℂ → ℂ}
    (hν : Differentiable ℝ ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2)
    (z : ℂ) (φ : Multiset.ToType D → ℂ) {m : ℕ} (hm : m ≤ D.count z) :
    ∃ y : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ y ∧ y ∈ gaugeFixedKernel x ∧
      (∀ k (hk : k < D.count z), k < m → principalPart x ν y z k = φ ⟨z, ⟨k, hk⟩⟩) ∧
      ∀ a, a ≠ z → ∀ k < D.count a, principalPart x ν y a k = 0 := by
  have hdec (y : ℂ → EuclideanSpace ℝ (Fin 4)) (hy : y ∈ gaugeFixedKernel x) :=
    exists_continuous_and_differentiable_sectionValue_eq_of_mem_gaugeFixedKernel
      (hx.differentiable (by simp)) hhol hν hνeq hy
  set Φ := principalPartMap hD hν.continuous hdec
  induction m with
  | zero =>
    refine ⟨0, contDiff_zero_fun, (gaugeFixedKernel x).zero_mem, fun _ _ hk ↦ by omega,
      fun a _ k hk ↦ ?_⟩
    simpa [Φ] using congrFun (map_zero Φ) (D.mkToType a ⟨k, hk⟩)
  | succ m ih =>
    have hm_lt : m < D.count z := Nat.lt_of_succ_le hm
    obtain ⟨y₀, hy₀c, hy₀k, hy₀z, hy₀a⟩ := ih (Nat.le_of_succ_le hm)
    obtain ⟨y₁, hy₁c, hy₁k, hy₁m, hy₁lt, hy₁a⟩ :=
      exists_contDiff_mem_gaugeFixedKernel_principalPart_single hx hhol hlim hD hν hνeq hm_lt
        (φ (D.mkToType z ⟨m, hm_lt⟩) - principalPart x ν y₀ z m)
    refine ⟨y₀ + y₁, hy₀c.add hy₁c, (gaugeFixedKernel x).add_mem hy₀k hy₁k,
      fun k hk hkm ↦ ?_, fun a ha k hk ↦ ?_⟩
    · have hadd : principalPart x ν (y₀ + y₁) z k =
          principalPart x ν y₀ z k + principalPart x ν y₁ z k := by
        simpa [Φ] using congrFun (map_add Φ ⟨y₀, hy₀k⟩ ⟨y₁, hy₁k⟩) (D.mkToType z ⟨k, hk⟩)
      rcases Nat.lt_succ_iff_lt_or_eq.1 hkm with hlt | rfl
      · rw [hadd, hy₀z k hk hlt, hy₁lt k hlt, add_zero]
      · rw [hadd, hy₁m, add_sub_cancel]
    · have hadd : principalPart x ν (y₀ + y₁) a k =
          principalPart x ν y₀ a k + principalPart x ν y₁ a k := by
        simpa [Φ] using congrFun (map_add Φ ⟨y₀, hy₀k⟩ ⟨y₁, hy₁k⟩) (D.mkToType a ⟨k, hk⟩)
      rw [hadd, hy₀a a ha k hk, hy₁a a ha k hk, add_zero]

/-- **Existence of smooth kernel elements with arbitrary principal-part data.** Let `x` be a smooth
field on the plane with `∂bar_a α = 0` and `|α|² → 1` at infinity, let `D` be the zero divisor of
`α`, and let `∂bar ν = (b₂ - i b₁) / 2`. Every tuple `φ : D → ℂ` is realized as the principal-part
data of a smooth element of `gaugeFixedKernel x`. -/
theorem exists_contDiff_mem_gaugeFixedKernel_principalPart_eq (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) {ν : ℂ → ℂ}
    (hν : Differentiable ℝ ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2)
    (φ : Multiset.ToType D → ℂ) :
    ∃ y : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ y ∧ y ∈ gaugeFixedKernel x ∧
      ∀ i : Multiset.ToType D, principalPart x ν y i.1 i.2 = φ i := by
  classical
  have hdec (y : ℂ → EuclideanSpace ℝ (Fin 4)) (hy : y ∈ gaugeFixedKernel x) :=
    exists_continuous_and_differentiable_sectionValue_eq_of_mem_gaugeFixedKernel
      (hx.differentiable (by simp)) hhol hν hνeq hy
  set Φ := principalPartMap hD hν.continuous hdec
  choose Y hYc hYk hYz hYa using fun z ↦
    exists_contDiff_mem_gaugeFixedKernel_principalPart_at hx hhol hlim hD hν hνeq z φ le_rfl
  have hsum_contDiff : ContDiff ℝ ∞ (∑ z ∈ D.toFinset, Y z) := by
    rw [Finset.sum_fn]
    exact ContDiff.sum fun z _ ↦ hYc z
  refine ⟨∑ z ∈ D.toFinset, Y z, hsum_contDiff,
    Submodule.sum_mem _ fun z _ ↦ hYk z, fun i ↦ ?_⟩
  have ha_mem : i.1 ∈ D.toFinset :=
    Multiset.mem_toFinset.2 (Multiset.count_pos.1 (Nat.zero_lt_of_lt i.2.2))
  have hsum : principalPart x ν (∑ z ∈ D.toFinset, Y z) i.1 i.2 =
      ∑ z ∈ D.toFinset, principalPart x ν (Y z) i.1 i.2 := by
    simpa [Φ, Submodule.coe_sum] using
      congrFun (map_sum Φ (fun z ↦ (⟨Y z, hYk z⟩ : gaugeFixedKernel x)) D.toFinset) i
  rw [hsum, Finset.sum_eq_single i.1 (fun z _ hza ↦ hYa z i.1 hza.symm i.2 i.2.2)
    (fun h ↦ absurd ha_mem h)]
  exact hYz i.1 i.2 i.2.2 i.2.2

/-- **Surjectivity of the principal-part map on `gaugeFixedKernel x`.** -/
theorem principalPartMap_surjective (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) {ν : ℂ → ℂ}
    (hν : Differentiable ℝ ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2)
    (hdec : ∀ y ∈ gaugeFixedKernel x, ∃ G : ℂ → ℂ, Continuous G ∧
      ∃ H : ℂ → ℂ, Differentiable ℂ H ∧
        ∀ w, sectionValue y w = sectionValue x w * G w + exp (ν w) * H w) :
    Function.Surjective (principalPartMap hD hν.continuous hdec) := fun φ ↦ by
  obtain ⟨y, -, hyk, hyφ⟩ :=
    exists_contDiff_mem_gaugeFixedKernel_principalPart_eq hx hhol hlim hD hν hνeq φ
  exact ⟨⟨y, hyk⟩, funext fun i ↦ by simpa only [principalPartMap_apply] using hyφ i⟩

/-- **Bijectivity of the principal-part map on `gaugeFixedKernel x`.** -/
theorem principalPartMap_bijective (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) {ν : ℂ → ℂ}
    (hν : ContDiff ℝ 2 ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2)
    (hdec : ∀ y ∈ gaugeFixedKernel x, ∃ G : ℂ → ℂ, Continuous G ∧
      ∃ H : ℂ → ℂ, Differentiable ℂ H ∧
        ∀ w, sectionValue y w = sectionValue x w * G w + exp (ν w) * H w) :
    Function.Bijective (principalPartMap hD hν.continuous hdec) := by
  have hx₂ : ContDiff ℝ 2 x := hx.of_le (by simp)
  have hxi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ x w i := contDiff_euclidean.1 hx₂ i
  have hlin (y) (hy : y ∈ gaugeFixedKernel x) :
      ContDiff ℝ 2 (fun w ↦ y w 0) ∧ ContDiff ℝ 2 (fun w ↦ y w 1) ∧
        Differentiable ℝ (fun w ↦ y w 2) ∧ Differentiable ℝ (fun w ↦ y w 3) ∧
        ∀ w, linearizedEquation x y w 1 = 0 ∧ linearizedEquation x y w 2 = 0 := by
    obtain ⟨hyc, -, hker⟩ := mem_gaugeFixedKernel.1 hy
    have hyi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ y w i := contDiff_euclidean.1 hyc i
    refine ⟨hyi 0, hyi 1, (hyi 2).differentiable (by norm_num),
      (hyi 3).differentiable (by norm_num), fun w ↦ ⟨?_, ?_⟩⟩
    · rw [← gaugeFixedOperator_apply_two, hker w, PiLp.zero_apply]
    · rw [← gaugeFixedOperator_apply_three, hker w, PiLp.zero_apply]
  refine ⟨principalPartMap_injective (k := 2) (by norm_num) (hxi 0) (hxi 1)
    ((hxi 2).differentiable (by norm_num)) ((hxi 3).differentiable (by norm_num)) hhol hD hν hνeq
    hlin hdec fun y hy η hη hyη ↦ ?_,
    principalPartMap_surjective hx hhol hlim hD (hν.differentiable (by norm_num)) hνeq hdec⟩
  obtain ⟨hyc, hy₂, hker⟩ := mem_gaugeFixedKernel.1 hy
  exact eq_zero_of_gaugeFixedOperator_eq_zero_of_sectionValue_eq_mul_of_tendsto
    (hx.of_le (by simp)) hhol hlim hyc.continuous hy₂ hker hη hyη

/-- **The principal-part linear equivalence.** At a smooth field `x` with `∂bar_a α = 0`,
`|α|² → 1` at infinity, and section zero divisor `D`, the principal-part map for any `C²`
integrating factor `ν` is a real-linear isomorphism `gaugeFixedKernel x ≃ₗ[ℝ] (D → ℂ)`. -/
def gaugeFixedKernelEquivPrincipalPart (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) {ν : ℂ → ℂ}
    (hν : ContDiff ℝ 2 ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2) :
    gaugeFixedKernel x ≃ₗ[ℝ] (Multiset.ToType D → ℂ) :=
  LinearEquiv.ofBijective
    (principalPartMap hD hν.continuous fun _ hy ↦
      exists_continuous_and_differentiable_sectionValue_eq_of_mem_gaugeFixedKernel
        (hx.differentiable (by simp)) hhol (hν.differentiable (by norm_num)) hνeq hy)
    (principalPartMap_bijective hx hhol hlim hD hν hνeq _)

/-- `gaugeFixedKernelEquivPrincipalPart` evaluates at `(z, k)` to `principalPart x ν y z k`. -/
@[simp]
theorem gaugeFixedKernelEquivPrincipalPart_apply (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) {ν : ℂ → ℂ}
    (hν : ContDiff ℝ 2 ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2)
    (y : gaugeFixedKernel x) (i : Multiset.ToType D) :
    gaugeFixedKernelEquivPrincipalPart hx hhol hlim hD hν hνeq y i =
      principalPart x ν y i.1 i.2 := by
  simp [gaugeFixedKernelEquivPrincipalPart]

private theorem exists_isZeroMultiplicity_sectionValue_of_tendsto_normSq (hx : ContDiff ℝ 2 x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    ∃ D : Multiset ℂ, IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z := by
  have htail : ∀ᶠ w in cocompact ℂ, sectionValue x w ≠ 0 := by
    filter_upwards [hlim.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with w hw hz
    rw [sectionValue_eq_zero_iff] at hz
    simp [hz] at hw
  have hxi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ x w i := contDiff_euclidean.1 hx i
  choose n v hvc hv₀ hvf using
    exists_contDiffAt_sectionValue_eq_pow_mul (k := 2) (by norm_num) (hxi 0) (hxi 1)
      ((hxi 2).differentiable (by norm_num)) ((hxi 3).differentiable (by norm_num)) hhol
      htail.exists
  have hmult : IsZeroMultiplicity (sectionValue x) n :=
    isZeroMultiplicity_iff.2 fun z ↦ ⟨v z, (hvc z).continuousAt, hv₀ z, hvf z⟩
  obtain ⟨D, rfl⟩ := hmult.exists_eq_count htail
  exact ⟨D, hmult⟩

/-- **Smoothness of the gauge-fixed kernel.** At a smooth field `x` with `∂bar_a α = 0` and
`|α|² → 1` at infinity, every `C²` square-integrable solution `y ∈ gaugeFixedKernel x` of
`L_x y = 0` is smooth (`C^∞`). -/
theorem contDiff_of_mem_gaugeFixedKernel (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ gaugeFixedKernel x) :
    ContDiff ℝ ∞ y := by
  have hx₂ : ContDiff ℝ 2 x := hx.of_le (by simp)
  have hxi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ x w i := contDiff_euclidean.1 hx₂ i
  obtain ⟨D, hmult⟩ := exists_isZeroMultiplicity_sectionValue_of_tendsto_normSq hx₂ hhol hlim
  obtain ⟨ν, hν, hνeq⟩ :=
    exists_contDiff_conjWirtingerDeriv_apply_one_eq (by norm_num)
      (contDiff_connectionCoeff (hxi 0) (hxi 1))
  set e := gaugeFixedKernelEquivPrincipalPart hx hhol hlim hmult hν hνeq
  obtain ⟨y', hy'c, hy'k, hy'φ⟩ :=
    exists_contDiff_mem_gaugeFixedKernel_principalPart_eq hx hhol hlim hmult
      (hν.differentiable (by norm_num)) hνeq (e ⟨y, hy⟩)
  have heq : (⟨y', hy'k⟩ : gaugeFixedKernel x) = ⟨y, hy⟩ :=
    e.injective (funext fun i ↦ by simp [e, hy'φ i])
  have hyy' : y' = y := congrArg Subtype.val heq
  exact hyy' ▸ hy'c

/-- **Finite-dimensionality of the gauge-fixed kernel under `|α|² → 1`.** At a `C²` field `x`
with `∂bar_a α = 0` and `|α|² → 1` at infinity, `gaugeFixedKernel x` is finite-dimensional over
`ℝ`. -/
theorem finiteDimensional_gaugeFixedKernel_of_tendsto_normSq (hx : ContDiff ℝ 2 x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    FiniteDimensional ℝ (gaugeFixedKernel x) := by
  obtain ⟨D, hmult⟩ := exists_isZeroMultiplicity_sectionValue_of_tendsto_normSq hx hhol hlim
  exact finiteDimensional_of_gaugeFixedOperator_eq_zero (μ := volume) hx hhol hlim hmult
    fun _ hy ↦ mem_gaugeFixedKernel.1 hy

/-- **The exact real dimension `2 |D|` of the gauge-fixed kernel.** At a smooth field `x` with
`∂bar_a α = 0`, `|α|² → 1` at infinity, and section zero divisor `D`, the real dimension of
`gaugeFixedKernel x` is `2 |D|`. -/
theorem finrank_gaugeFixedKernel_eq_two_mul_card (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) :
    Module.finrank ℝ (gaugeFixedKernel x) = 2 * Multiset.card D := by
  have hxi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ x w i :=
    contDiff_euclidean.1 (hx.of_le (by simp)) i
  obtain ⟨ν, hν, hνeq⟩ :=
    exists_contDiff_conjWirtingerDeriv_apply_one_eq (by norm_num)
      (contDiff_connectionCoeff (hxi 0) (hxi 1))
  rw [(gaugeFixedKernelEquivPrincipalPart hx hhol hlim hD hν hνeq).finrank_eq,
    Module.finrank_pi_fintype, Finset.sum_const, Complex.finrank_real_complex, smul_eq_mul,
    Finset.card_univ, Multiset.card_coe, mul_comm]

/-- **The exact real dimension `2 m` of the gauge-fixed kernel at a degree-`m` framed field.** Let
`x` be a smooth field satisfying the holomorphicity rows `∂bar_a α = 0` whose section carries the
degree-`m` end framing `α(z) (z / |z|)⁻ᵐ → 1`. Then `gaugeFixedKernel x` has real dimension `2 m`,
matching the real dimension of the divisor space `Sym^m ℂ`. -/
theorem finrank_gaugeFixedKernel_eq_two_mul {m : ℕ} (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    Module.finrank ℝ (gaugeFixedKernel x) = 2 * m := by
  have hxi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ x w i :=
    contDiff_euclidean.1 (hx.of_le (by simp)) i
  obtain ⟨D, hD⟩ := exists_sym_isZeroMultiplicity_sectionValue (k := 2) (by norm_num)
    (hxi 0) (hxi 1) ((hxi 2).differentiable (by norm_num)) ((hxi 3).differentiable (by norm_num))
    hhol hframe
  rw [finrank_gaugeFixedKernel_eq_two_mul_card hx hhol
    (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe) hD, Sym.card_coe]

end TauCeti.Vortex
