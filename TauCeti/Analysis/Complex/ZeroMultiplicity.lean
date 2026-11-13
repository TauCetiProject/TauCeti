/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ContinuousLog.ArgumentPrinciple
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import TauCeti.Analysis.Analytic.Order
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Topology.Algebra.Polynomial

/-!
# Zero multiplicities of functions with local power factorizations

A function `n : ℂ → ℕ` is a **zero multiplicity function** of `f : ℂ → ℂ`
(`TauCeti.IsZeroMultiplicity f n`) if near every point `z` the function factors as

`f w = (w - z) ^ n z * v w`,  with `v` continuous at `z` and `v z ≠ 0`.

No holomorphy is assumed. This is the local form that the similarity principle
(`TauCeti.exists_contDiffAt_pow_mul_of_conjWirtingerDeriv_apply_one_eq_mul`) gives for solutions
of `∂bar f = a f`, for instance for the section of a plane vortex, and it is the hypothesis of the
topological argument principle `TauCeti.finsum_eq_of_tendsto_mul_inv_pow`. The exponent of such a
factorization is unique (`TauCeti.eq_of_eventually_sub_pow_mul_eq`), so `f` has at most one zero
multiplicity function (`TauCeti.IsZeroMultiplicity.unique`); it is positive exactly at the zeros of
`f`.

Near `z`, `f` vanishes to every order `k ≤ n z`: `‖f w‖ ≤ C ‖w - z‖ ^ k`
(`TauCeti.IsZeroMultiplicity.exists_eventually_norm_le_mul_pow`).

This file proves how zero multiplicities transform:

* under an affine change of variable `w ↦ c w + a` with `c ≠ 0`, the multiplicity is pulled back
  (`TauCeti.IsZeroMultiplicity.comp_mul_add`);
* under products, multiplicities add (`TauCeti.IsZeroMultiplicity.mul`); the functions with
  multiplicity zero are the continuous functions without zeros
  (`TauCeti.isZeroMultiplicity_zero_iff`), so multiplying by such a function does not change the
  multiplicity;
* a nonzero polynomial has its root multiplicities as zero multiplicity function
  (`TauCeti.isZeroMultiplicity_eval_rootMultiplicity`), in particular `∏ (w - a)` over a multiset
  `D` has multiplicity `count · D` (`TauCeti.isZeroMultiplicity_prod_sub`).

If `f` has no zeros near infinity, its multiplicities are the counts of a multiset of points,
which they determine: the divisor of zeros of `f` (`TauCeti.IsZeroMultiplicity.exists_eq_count`).
Then `f` is `exp L` times the product of the linear factors of its divisor, for a continuous `L`
(`TauCeti.IsZeroMultiplicity.exists_continuous_eq_exp_mul_prod_pow`).
When moreover `f(z) (z / |z|)⁻ᵐ → 1` at infinity, that divisor has `m` points
(`TauCeti.IsZeroMultiplicity.card_eq_of_tendsto_mul_inv_pow`).

Divisibility of a holomorphic function `H` by `f` near `z` is measured by the analytic order of
`H`: if `H = f u` near `z` with `u` continuous at `z`, then `H` vanishes to order at least `n z`
(`TauCeti.IsZeroMultiplicity.natCast_le_analyticOrderAt_of_eventually_eq_mul`); conversely, if `H`
vanishes to order at least `n` and `f = (w - z) ^ n v` with `v` of class `Cᵏ` at `z` and nonzero
there, then `H = f K` near `z` with `K` of class `Cᵏ` at `z`
(`TauCeti.exists_contDiffAt_eventually_eq_mul_of_natCast_le_analyticOrderAt`).
Consequently, if `f G₁ + E H₁ = f G₂ + E H₂` near `z` with `G₁`, `G₂`, `E` continuous at `z`,
`E z ≠ 0` and `H₁`, `H₂` holomorphic at `z`, then `H₁` and `H₂` have the same derivatives at `z` of
order below `n z` (`TauCeti.IsZeroMultiplicity.iteratedDeriv_eq_of_eventually_mul_add_mul_eq`).
-/

public section

namespace TauCeti

open Filter Polynomial Topology

/-- `n` is a **zero multiplicity function** of `f`: near every point `z`, `f` factors as
`f w = (w - z) ^ n z * v w` with `v` continuous at `z` and `v z ≠ 0`. -/
def IsZeroMultiplicity (f : ℂ → ℂ) (n : ℂ → ℕ) : Prop :=
  ∀ z, ∃ v : ℂ → ℂ, ContinuousAt v z ∧ v z ≠ 0 ∧ ∀ᶠ w in 𝓝 z, f w = (w - z) ^ n z * v w

variable {f g : ℂ → ℂ} {n n' : ℂ → ℕ}

/-- The defining local factorizations of a zero multiplicity function. -/
theorem isZeroMultiplicity_iff :
    IsZeroMultiplicity f n ↔
      ∀ z, ∃ v : ℂ → ℂ, ContinuousAt v z ∧ v z ≠ 0 ∧ ∀ᶠ w in 𝓝 z, f w = (w - z) ^ n z * v w :=
  Iff.rfl

namespace IsZeroMultiplicity

/-- **Uniqueness of zero multiplicities.** A function has at most one zero multiplicity
function. -/
theorem unique (h : IsZeroMultiplicity f n) (h' : IsZeroMultiplicity f n') : n = n' :=
  funext fun z ↦ by
    obtain ⟨v, hv, hv₀, hf⟩ := isZeroMultiplicity_iff.1 h z
    obtain ⟨v', hv', hv₀', hf'⟩ := isZeroMultiplicity_iff.1 h' z
    exact eq_of_eventually_sub_pow_mul_eq hv hv₀ hv' hv₀' <| by
      filter_upwards [hf, hf'] with w hw hw'
      rw [← hw, ← hw']

/-- A function with a zero multiplicity function is continuous. -/
theorem continuous (h : IsZeroMultiplicity f n) : Continuous f :=
  continuous_of_eventually_eq_pow_mul fun z ↦
    (isZeroMultiplicity_iff.1 h z).imp fun _ hv ↦ ⟨hv.1, hv.2.2⟩

/-- A function with a zero multiplicity function is not identically zero. -/
theorem exists_ne_zero (h : IsZeroMultiplicity f n) : ∃ w, f w ≠ 0 := by
  obtain ⟨v, hv, hv₀, hf⟩ := isZeroMultiplicity_iff.1 h 0
  obtain ⟨w, ⟨hw, hvw⟩, hw₀⟩ := (((hf.and (hv.eventually_ne hv₀)).filter_mono
    nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := {0}ᶜ))).exists
  exact ⟨w, by rw [hw]; exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.2 hw₀)) hvw⟩

/-- The multiplicity vanishes exactly off the zeros of `f`. -/
theorem eq_zero_iff (h : IsZeroMultiplicity f n) {z : ℂ} : n z = 0 ↔ f z ≠ 0 := by
  obtain ⟨v, -, hv₀, hf⟩ := isZeroMultiplicity_iff.1 h z
  rw [hf.self_of_nhds, sub_self]
  rcases eq_or_ne (n z) 0 with hz | hz <;> simp [hz, hv₀]

/-- The multiplicity is positive exactly at the zeros of `f`. -/
theorem pos_iff (h : IsZeroMultiplicity f n) {z : ℂ} : 0 < n z ↔ f z = 0 := by
  rw [Nat.pos_iff_ne_zero, Ne, h.eq_zero_iff, not_not]

/-- A function vanishes at `z` at least to every order `k` up to its multiplicity there:
`‖f w‖ ≤ C ‖w - z‖ ^ k` near `z`. -/
theorem exists_eventually_norm_le_mul_pow (h : IsZeroMultiplicity f n) {z : ℂ} {k : ℕ}
    (hk : k ≤ n z) : ∃ C, ∀ᶠ w in 𝓝 z, ‖f w‖ ≤ C * ‖w - z‖ ^ k := by
  obtain ⟨v, hv, -, hf⟩ := isZeroMultiplicity_iff.1 h z
  refine ⟨‖v z‖ + 1, ?_⟩
  filter_upwards [hf, hv.norm.eventually (ge_mem_nhds (lt_add_one ‖v z‖)),
    Metric.ball_mem_nhds z one_pos] with w hw hvw hwz
  have hd : ‖w - z‖ ≤ 1 := (mem_ball_iff_norm.1 hwz).le
  rw [hw, norm_mul, norm_pow, mul_comm]
  exact mul_le_mul hvw (pow_le_pow_of_le_one (norm_nonneg _) hd hk) (by positivity)
    (by positivity)

/-- **Affine change of variable.** If `c ≠ 0`, the zero multiplicity of `w ↦ f (c w + a)` at `z`
is that of `f` at `c z + a`. -/
theorem comp_mul_add (h : IsZeroMultiplicity f n) {c : ℂ} (hc : c ≠ 0) (a : ℂ) :
    IsZeroMultiplicity (fun w ↦ f (c * w + a)) fun z ↦ n (c * z + a) := by
  refine isZeroMultiplicity_iff.2 fun z ↦ ?_
  obtain ⟨v, hv, hv₀, hf⟩ := isZeroMultiplicity_iff.1 h (c * z + a)
  have hφ : Continuous fun w : ℂ ↦ c * w + a := by fun_prop
  refine ⟨fun w ↦ c ^ n (c * z + a) * v (c * w + a),
    continuousAt_const.mul (hv.comp_of_eq hφ.continuousAt rfl),
    mul_ne_zero (pow_ne_zero _ hc) hv₀, ?_⟩
  filter_upwards [(hφ.tendsto z).eventually hf] with w hw
  rw [hw, show c * w + a - (c * z + a) = c * (w - z) by ring, mul_pow]
  ring

/-- **Multiplicities add under products.** -/
theorem mul (h : IsZeroMultiplicity f n) (h' : IsZeroMultiplicity g n') :
    IsZeroMultiplicity (fun w ↦ f w * g w) (n + n') := by
  refine isZeroMultiplicity_iff.2 fun z ↦ ?_
  obtain ⟨v, hv, hv₀, hf⟩ := isZeroMultiplicity_iff.1 h z
  obtain ⟨v', hv', hv₀', hg⟩ := isZeroMultiplicity_iff.1 h' z
  refine ⟨fun w ↦ v w * v' w, hv.mul hv', mul_ne_zero hv₀ hv₀', ?_⟩
  filter_upwards [hf, hg] with w hw hw'
  rw [hw, hw', Pi.add_apply, pow_add]
  ring

/-- If `f` has no zeros near infinity, its zero multiplicities are the counts of a multiset of
points, the divisor of zeros of `f`. -/
theorem exists_eq_count (h : IsZeroMultiplicity f n) (htail : ∀ᶠ w in cocompact ℂ, f w ≠ 0) :
    ∃ D : Multiset ℂ, n = fun z ↦ D.count z := by
  classical
  have hfin := finite_support_of_eventually_eq_pow_mul (isZeroMultiplicity_iff.1 h) htail
  refine ⟨(Finsupp.ofSupportFinite n hfin).toMultiset, funext fun z ↦ ?_⟩
  simp [Finsupp.ofSupportFinite_coe]

/-- **Global factorization through the divisor of zeros.** If the zero multiplicities of `f` are
the counts of a multiset `D`, then `f w = exp (L w) * ∏ z ∈ D.toFinset, (w - z) ^ count z D` for a
continuous `L`. -/
theorem exists_continuous_eq_exp_mul_prod_pow {D : Multiset ℂ}
    (h : IsZeroMultiplicity f fun z ↦ D.count z) :
    ∃ L : ℂ → ℂ, Continuous L ∧
      ∀ w, f w = Complex.exp (L w) * ∏ z ∈ D.toFinset, (w - z) ^ D.count z :=
  TauCeti.exists_continuous_eq_exp_mul_prod_pow h.continuous D.toFinset
    (fun z _ ↦ isZeroMultiplicity_iff.1 h z)
    fun _ hw ↦ Multiset.mem_toFinset.2 (Multiset.count_pos.1 (h.pos_iff.2 hw))

/-- **The degree of the divisor of zeros.** If `f(z) (z / |z|)⁻ᵐ → 1` at infinity and the zero
multiplicities of `f` are the counts of `D`, then `D` has `m` points. -/
theorem card_eq_of_tendsto_mul_inv_pow {D : Multiset ℂ}
    (h : IsZeroMultiplicity f fun z ↦ D.count z) {m : ℕ}
    (hm : Tendsto (fun z ↦ f z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    Multiset.card D = m := by
  classical
  rw [← finsum_eq_of_tendsto_mul_inv_pow (isZeroMultiplicity_iff.1 h) hm,
    finsum_eq_sum_of_support_subset _ (s := D.toFinset) fun z hz ↦ ?_,
    Multiset.toFinset_sum_count_eq]
  simpa [Multiset.count_eq_zero] using hz

/-- A holomorphic function divisible near `z` by `f`, with a quotient continuous at `z`, vanishes
at `z` to order at least the zero multiplicity of `f` there. -/
theorem natCast_le_analyticOrderAt_of_eventually_eq_mul (h : IsZeroMultiplicity f n)
    {H u : ℂ → ℂ} {z : ℂ} (hH : AnalyticAt ℂ H z) (hu : ContinuousAt u z)
    (heq : ∀ᶠ w in 𝓝 z, H w = f w * u w) : (n z : ℕ∞) ≤ analyticOrderAt H z := by
  obtain ⟨v, hv, -, hfv⟩ := h z
  refine hH.natCast_le_analyticOrderAt_of_eventually_eq_pow_smul (u := fun w ↦ v w * u w)
    (hv.mul hu) ?_
  filter_upwards [heq, hfv] with w hw hwv
  rw [hw, hwv, smul_eq_mul, mul_assoc]

/-- **Uniqueness of the holomorphic part modulo `f`.** If `f G₁ + E H₁ = f G₂ + E H₂` near `z`, with
`G₁`, `G₂`, `E` continuous at `z`, `E z ≠ 0` and `H₁`, `H₂` holomorphic at `z`, then the
derivatives of `H₁` and `H₂` at `z` of order below the zero multiplicity `n z` of `f` agree. -/
theorem iteratedDeriv_eq_of_eventually_mul_add_mul_eq (h : IsZeroMultiplicity f n)
    {E G₁ G₂ H₁ H₂ : ℂ → ℂ} {z : ℂ} (hE : ContinuousAt E z) (hE₀ : E z ≠ 0)
    (hG₁ : ContinuousAt G₁ z) (hG₂ : ContinuousAt G₂ z) (hH₁ : AnalyticAt ℂ H₁ z)
    (hH₂ : AnalyticAt ℂ H₂ z)
    (heq : ∀ᶠ w in 𝓝 z, f w * G₁ w + E w * H₁ w = f w * G₂ w + E w * H₂ w) {j : ℕ}
    (hj : j < n z) : iteratedDeriv j H₁ z = iteratedDeriv j H₂ z := by
  -- `H₁ - H₂ = f u` with `u = (G₂ - G₁) / E` continuous at `z`.
  have hord : (n z : ℕ∞) ≤ analyticOrderAt (H₁ - H₂) z :=
    h.natCast_le_analyticOrderAt_of_eventually_eq_mul (u := fun w ↦ (G₂ w - G₁ w) / E w)
      (hH₁.sub hH₂) ((hG₂.sub hG₁).div hE hE₀) <| by
        filter_upwards [heq, hE.eventually_ne hE₀] with w hw hEw
        rw [Pi.sub_apply, eq_comm, mul_div_assoc', div_eq_iff hEw]
        linear_combination -hw
  have hzero := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hH₁.sub hH₂)).1 hord j hj
  rwa [iteratedDeriv_sub hH₁.contDiffAt hH₂.contDiffAt, sub_eq_zero] at hzero

end IsZeroMultiplicity

/-- **Zero multiplicity zero.** The functions with zero multiplicity function `0` are the
continuous functions without zeros. -/
theorem isZeroMultiplicity_zero_iff :
    IsZeroMultiplicity g 0 ↔ Continuous g ∧ ∀ z, g z ≠ 0 := by
  refine ⟨fun h ↦ ⟨h.continuous, fun z ↦ h.eq_zero_iff.1 rfl⟩, fun ⟨hg, hg₀⟩ ↦ ?_⟩
  exact isZeroMultiplicity_iff.2 fun z ↦
    ⟨g, hg.continuousAt, hg₀ z, Eventually.of_forall fun w ↦ by simp⟩

/-- Multiplying by a continuous function without zeros does not change the zero
multiplicities. -/
theorem IsZeroMultiplicity.mul_left_of_continuous (h : IsZeroMultiplicity f n)
    (hg : Continuous g) (hg₀ : ∀ z, g z ≠ 0) : IsZeroMultiplicity (fun w ↦ g w * f w) n := by
  simpa using (isZeroMultiplicity_zero_iff.2 ⟨hg, hg₀⟩).mul h

/-- The zero multiplicities of a nonzero complex polynomial are its root multiplicities. -/
theorem isZeroMultiplicity_eval_rootMultiplicity {p : ℂ[X]} (hp : p ≠ 0) :
    IsZeroMultiplicity (fun w ↦ p.eval w) fun z ↦ p.rootMultiplicity z := by
  refine isZeroMultiplicity_iff.2 fun z ↦ ?_
  refine ⟨fun w ↦ (p /ₘ (X - C z) ^ p.rootMultiplicity z).eval w,
    (Polynomial.continuous _).continuousAt, eval_divByMonic_pow_rootMultiplicity_ne_zero z hp,
    Eventually.of_forall fun w ↦ ?_⟩
  conv_lhs => rw [← pow_mul_divByMonic_rootMultiplicity_eq p z]
  simp

/-- The zero multiplicities of `w ↦ ∏_{a ∈ D} (w - a)` are the counts of the multiset `D`. -/
theorem isZeroMultiplicity_prod_sub (D : Multiset ℂ) :
    IsZeroMultiplicity (fun w ↦ (D.map fun a ↦ w - a).prod) fun z ↦ D.count z := by
  classical
  have hmonic : (D.map fun a ↦ X - C a).prod.Monic :=
    monic_multiset_prod_of_monic _ _ fun a _ ↦ monic_X_sub_C a
  convert isZeroMultiplicity_eval_rootMultiplicity hmonic.ne_zero using 1
  · funext w
    simp [eval_multiset_prod, Multiset.map_map]
  · funext z
    rw [← count_roots, roots_multiset_prod_X_sub_C]

/-- **Dividing by a local power factorization.** If `H` is holomorphic at `z` and vanishes there
to order at least `n`, and `f = (w - z) ^ n v` near `z` with `v` of class `Cᵏ` at `z` and nonzero
there, then `H = f K` near `z` for a function `K` of class `Cᵏ` at `z`. -/
theorem exists_contDiffAt_eventually_eq_mul_of_natCast_le_analyticOrderAt {k : WithTop ℕ∞}
    {v H : ℂ → ℂ} {z : ℂ} {n : ℕ} (hH : AnalyticAt ℂ H z) (hn : (n : ℕ∞) ≤ analyticOrderAt H z)
    (hv : ContDiffAt ℝ k v z) (hv₀ : v z ≠ 0) (hf : ∀ᶠ w in 𝓝 z, f w = (w - z) ^ n * v w) :
    ∃ K : ℂ → ℂ, ContDiffAt ℝ k K z ∧ ∀ᶠ w in 𝓝 z, H w = f w * K w := by
  obtain ⟨g, hg, hHg⟩ := (natCast_le_analyticOrderAt hH).1 hn
  refine ⟨fun w ↦ g w / v w, by
    simpa only [div_eq_mul_inv, Pi.inv_apply] using
      ((hg.contDiffAt (n := k)).restrict_scalars ℝ).mul (hv.inv hv₀), ?_⟩
  filter_upwards [hHg, hf, hv.continuousAt.eventually_ne hv₀] with w hw hwf hwv
  rw [hw, hwf, smul_eq_mul]
  field_simp

end TauCeti
