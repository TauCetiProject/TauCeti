/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import TauCeti.Analysis.Calculus.IteratedDeriv.Leibniz
import TauCeti.Order.WithBot

/-!
# The residue of a meromorphic function

For `f : ℂ → E` valued in a complex normed space and `z₀ : ℂ`, the **residue**
`TauCeti.Contour.residue f z₀` is the order-`(−1)` Laurent coefficient of `f` at `z₀` — the
quantity summed in Cauchy's residue theorem. It is built directly on Mathlib's
`meromorphicOrderAt` / analytic-part API rather than a parallel order-of-vanishing notion: writing
`f z = (z − z₀) ^ n • g z` near `z₀` with `g` analytic and `g z₀ ≠ 0` (where
`n = meromorphicOrderAt f z₀`), the order-`(−1)` coefficient is the Taylor coefficient of `g` at
index `−1 − n`, i.e. `((−1 − n)!)⁻¹ • iteratedDeriv (−1 − n) g z₀`. The residue is `0` at a point
where `f` is analytic (`n ≥ 0`), and at a **simple pole** (`n = −1`) it is the leading Laurent
coefficient `meromorphicTrailingCoeffAt f z₀ = lim_{z→z₀} (z − z₀) • f z`.

As an unconditional value it is junk (`0`) when `f` is not meromorphic at `z₀`.

## Main definitions

* `TauCeti.Contour.residue` — the residue of `f` at `z₀`.

## Main results

* `TauCeti.Contour.residue_eq_of_order_lt_zero` — the characteristic value: from a reduced local
  presentation `f =ᶠ[𝓝[≠] z₀] (· − z₀) ^ n • g` with `g` analytic, `g z₀ ≠ 0`, and `n < 0`, the
  residue is `((−1 − n)!)⁻¹ • iteratedDeriv (−1 − n) g z₀`, independently of the presentation.
* `TauCeti.Contour.residue_eq_of_eventuallyEq_zpow_smul` — the same value from any presentation
  `f =ᶠ[𝓝[≠] z₀] (· − z₀) ^ n • g` with `g` analytic and `n ≤ −1`, dropping `g z₀ ≠ 0` (for a
  complete codomain).
* `TauCeti.Contour.residue_add`, `TauCeti.Contour.residue_sub`, `TauCeti.Contour.residue_sum` —
  additivity of the residue, over functions meromorphic at `z₀`, including over finite sums. The
  hypotheses are essential: two functions that are not meromorphic can sum to one that is.
* `TauCeti.Contour.residue_const_smul` and `TauCeti.Contour.residue_const_mul` — homogeneity, in
  the unapplied and (scalar) applied forms. These are unconditional, the junk value scaling
  correctly.
* `TauCeti.Contour.residue_congr_nhdsNE` — the residue depends only on the germ of `f` on a
  punctured neighborhood of `z₀`.
* `TauCeti.Contour.residue_eq_zero_of_analyticAt` — the residue vanishes where `f` is analytic.
* `TauCeti.Contour.residue_eq_meromorphicTrailingCoeffAt_of_order_eq_neg_one` — at a simple pole the
  residue is the leading Laurent (trailing) coefficient.
* `TauCeti.Contour.residue_div_sub_pow_of_analyticAt` — the Cauchy-kernel computation
  `Res_{z₀} (g / (· − z₀) ^ (k + 1)) = g^{(k)}(z₀) / k !` for `g : ℂ → ℂ` analytic at `z₀`.

## Provenance

Adapted from the AINTLIB `LeanModularForms` project (the residue material of
`ForMathlib/GeneralizedResidueTheory/Residue.lean` and
`ForMathlib/GeneralizedResidueTheory/Residue/GeneralizedTheoremBase.lean`), reformulated for raw
functions `ℂ → E` and defined against Mathlib's `meromorphicOrderAt` / `meromorphicTrailingCoeffAt`
API.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997.
-/

public section

noncomputable section

open Filter Topology

namespace TauCeti.Contour

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The **residue** of `f` at `z₀`: the order-`(−1)` Laurent coefficient. When `f` is meromorphic at
`z₀` with a pole (`meromorphicOrderAt f z₀ = n < 0`), it is the Taylor coefficient
`((−1 − n)!)⁻¹ • iteratedDeriv (−1 − n) g z₀` of the analytic part `g` (with
`f z = (z − z₀) ^ n • g z` near `z₀`); it is `0` when `f` is analytic at `z₀` (`n ≥ 0`) and junk
(`0`) when `f` is not meromorphic at `z₀`. See `residue_eq_of_order_lt_zero` for the characteristic
value from an arbitrary presentation and `residue_eq_meromorphicTrailingCoeffAt_of_order_eq_neg_one`
for the simple-pole value. -/
noncomputable def residue (f : ℂ → E) (z₀ : ℂ) : E :=
  haveI : Decidable (MeromorphicAt f z₀ ∧ meromorphicOrderAt f z₀ < 0) := Classical.propDecidable _
  if h : MeromorphicAt f z₀ ∧ meromorphicOrderAt f z₀ < 0 then
    ((-1 - (meromorphicOrderAt f z₀).untop₀).toNat.factorial : ℂ)⁻¹ •
      iteratedDeriv (-1 - (meromorphicOrderAt f z₀).untop₀).toNat
        ((meromorphicOrderAt_ne_top_iff h.1).1 h.2.ne_top).choose z₀
  else 0

/-- Unfolding `residue` at a pole: the analytic part chosen by the definition presents `f` at its
meromorphic order, and the residue is its Taylor coefficient at index `−1 − order`. -/
private lemma exists_residue_eq_of_meromorphicOrderAt_lt_zero {f : ℂ → E} {z₀ : ℂ}
    (hf : MeromorphicAt f z₀) (hlt : meromorphicOrderAt f z₀ < 0) :
    ∃ g : ℂ → E, AnalyticAt ℂ g z₀ ∧ g z₀ ≠ 0 ∧
      f =ᶠ[𝓝[≠] z₀] (fun z ↦ (z - z₀) ^ (meromorphicOrderAt f z₀).untop₀ • g z) ∧
      residue f z₀ = ((-1 - (meromorphicOrderAt f z₀).untop₀).toNat.factorial : ℂ)⁻¹ •
        iteratedDeriv (-1 - (meromorphicOrderAt f z₀).untop₀).toNat g z₀ := by
  have h := (meromorphicOrderAt_ne_top_iff hf).1 hlt.ne_top
  exact ⟨_, h.choose_spec.1, h.choose_spec.2.1, h.choose_spec.2.2,
    by rw [residue, dite_eq_left ⟨hf, hlt⟩]⟩

/-- **Characteristic value of the residue at a pole.** If `f z = (z − z₀) ^ n • g z` near `z₀` (on
the punctured neighborhood) with `g` analytic at `z₀`, `g z₀ ≠ 0`, and `n < 0`, then the residue is
the Taylor coefficient of `g` at index `−1 − n`. This is the standard reduced analytic presentation;
the order equality `meromorphicOrderAt f z₀ = n` is derived from it, and the value is independent of
the chosen presentation `g`. -/
theorem residue_eq_of_order_lt_zero {f g : ℂ → E} {z₀ : ℂ} {n : ℤ}
    (hlt : n < 0) (hg : AnalyticAt ℂ g z₀) (hg_ne : g z₀ ≠ 0)
    (hfg : f =ᶠ[𝓝[≠] z₀] fun z ↦ (z - z₀) ^ n • g z) :
    residue f z₀ = ((-1 - n).toNat.factorial : ℂ)⁻¹ • iteratedDeriv (-1 - n).toNat g z₀ := by
  have hf : MeromorphicAt f z₀ :=
    MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt.mpr ⟨n, g, hg, hfg⟩
  have hn : meromorphicOrderAt f z₀ = n :=
    (meromorphicOrderAt_eq_int_iff hf).mpr ⟨g, hg, hg_ne, hfg⟩
  obtain ⟨g₀, hg₀, -, hfg₀, hres⟩ :=
    exists_residue_eq_of_meromorphicOrderAt_lt_zero hf (by rw [hn]; exact_mod_cast hlt)
  rw [hn, WithTop.untop₀_coe] at hfg₀ hres
  have hne : g₀ =ᶠ[𝓝[≠] z₀] g := by
    filter_upwards [hfg₀, hfg, self_mem_nhdsWithin] with z h₁ h₂ hz
    exact (smul_right_inj (zpow_ne_zero n (sub_ne_zero.mpr hz))).1 (h₁.symm.trans h₂)
  rw [hres, ((hg₀.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hg.continuousAt).1
    hne).iteratedDeriv_eq]

/-- If `f` is not meromorphic at `z₀`, its residue is `0` by definition. -/
@[simp]
theorem residue_of_not_meromorphicAt {f : ℂ → E} {z₀ : ℂ} (h : ¬ MeromorphicAt f z₀) :
    residue f z₀ = 0 := by
  rw [residue, dite_eq_right]
  exact fun h' ↦ absurd h'.1 h

/-- The residue vanishes at a point where `f` has nonnegative meromorphic order (in particular where
`f` is analytic): there is no order-`(−1)` Laurent coefficient. -/
@[simp]
theorem residue_eq_zero_of_meromorphicOrderAt_nonneg {f : ℂ → E} {z₀ : ℂ}
    (h : 0 ≤ meromorphicOrderAt f z₀) : residue f z₀ = 0 := by
  rw [residue, dite_eq_right]
  exact fun h' ↦ absurd h'.2 h.not_gt

/-- The residue vanishes where `f` is analytic. -/
@[simp]
theorem residue_eq_zero_of_analyticAt {f : ℂ → E} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀) :
    residue f z₀ = 0 :=
  residue_eq_zero_of_meromorphicOrderAt_nonneg hf.meromorphicOrderAt_nonneg

/-- The residue depends only on the germ of `f` on a punctured neighborhood of `z₀`: functions
agreeing near (but not necessarily at) `z₀` have the same residue. -/
theorem residue_congr_nhdsNE {f g : ℂ → E} {z₀ : ℂ} (h : f =ᶠ[𝓝[≠] z₀] g) :
    residue f z₀ = residue g z₀ := by
  have hord : meromorphicOrderAt f z₀ = meromorphicOrderAt g z₀ := meromorphicOrderAt_congr h
  rcases lt_or_ge (meromorphicOrderAt g z₀) 0 with hlt | hge
  · obtain ⟨g₀, hg₀, hg₀_ne, hgg₀, hres⟩ := exists_residue_eq_of_meromorphicOrderAt_lt_zero
      (meromorphicAt_of_meromorphicOrderAt_ne_zero hlt.ne) hlt
    rw [hres, residue_eq_of_order_lt_zero (by simpa [← not_le] using hlt) hg₀ hg₀_ne
      (h.trans hgg₀)]
  · rw [residue_eq_zero_of_meromorphicOrderAt_nonneg (hord ▸ hge),
      residue_eq_zero_of_meromorphicOrderAt_nonneg hge]

/-- At a **simple pole** (`meromorphicOrderAt f z₀ = −1`), the residue is the leading Laurent
coefficient `meromorphicTrailingCoeffAt f z₀`, i.e. `lim_{z→z₀} (z − z₀) • f z`: the Taylor
coefficient at index `−1 − (−1) = 0` of the analytic part `g` is just `g z₀`, which is the trailing
coefficient. -/
@[simp]
theorem residue_eq_meromorphicTrailingCoeffAt_of_order_eq_neg_one {f : ℂ → E} {z₀ : ℂ}
    (hord : meromorphicOrderAt f z₀ = -1) :
    residue f z₀ = meromorphicTrailingCoeffAt f z₀ := by
  obtain ⟨g, hg, -, hfg, hres⟩ := exists_residue_eq_of_meromorphicOrderAt_lt_zero
    (meromorphicAt_of_meromorphicOrderAt_ne_zero (by rw [hord]; decide)) (by rw [hord]; decide)
  have huntop : (meromorphicOrderAt f z₀).untop₀ = -1 := by rw [hord]; rfl
  rw [hres, hg.meromorphicTrailingCoeffAt_of_eq_nhdsNE hfg, huntop]
  simp

/-- The pole case (`meromorphicOrderAt f z₀ < 0`) of `residue_eq_of_eventuallyEq_zpow_smul`: the
presentation factor `g` is the reduced analytic part times `(· − z₀) ^ (order − n)`, whose Taylor
coefficients are those of the analytic part shifted by `order − n`. -/
private theorem residue_eq_of_eventuallyEq_zpow_smul_of_order_lt_zero [CompleteSpace E]
    {f g : ℂ → E} {z₀ : ℂ} {n : ℤ}
    (hg : AnalyticAt ℂ g z₀) (hfg : f =ᶠ[𝓝[≠] z₀] fun z ↦ (z - z₀) ^ n • g z)
    (hf : MeromorphicAt f z₀)
    (hord_eq : meromorphicOrderAt f z₀ = (n : WithTop ℤ) + meromorphicOrderAt g z₀)
    (ha : meromorphicOrderAt f z₀ < 0) :
    residue f z₀ = ((-1 - n).toNat.factorial : ℂ)⁻¹ • iteratedDeriv (-1 - n).toNat g z₀ := by
  obtain ⟨g₀, hg₀_an, -, hf_eq, hres⟩ := exists_residue_eq_of_meromorphicOrderAt_lt_zero hf ha
  set a := (meromorphicOrderAt f z₀).untop₀
  have hcoe : (a : WithTop ℤ) = meromorphicOrderAt f z₀ := WithTop.coe_untop₀_of_ne_top ha.ne_top
  have ha_lt : a < 0 := by simpa [a, ← not_le] using ha
  have hna : n ≤ a := by
    rw [← WithTop.coe_le_coe, hcoe, hord_eq]
    exact le_add_of_nonneg_right hg.meromorphicOrderAt_nonneg
  have hg_eqNE : g =ᶠ[𝓝[≠] z₀] fun z ↦ (z - z₀) ^ (a - n).toNat • g₀ z := by
    filter_upwards [hfg, hf_eq, self_mem_nhdsWithin] with z hz1 hz2 hz3
    have hzne : z - z₀ ≠ 0 := sub_ne_zero.mpr hz3
    rw [← smul_right_inj (zpow_ne_zero n hzne), ← hz1, hz2, smul_smul, ← zpow_natCast,
      ← zpow_add₀ hzne, Int.toNat_of_nonneg (by omega), add_sub_cancel]
  have hana : AnalyticAt ℂ (fun z ↦ (z - z₀) ^ (a - n).toNat • g₀ z) z₀ := by fun_prop
  -- Split the Taylor index `-1 - n` as the shift `a - n` plus the index `-1 - a` for `g₀`.
  have hidx : (-1 - n).toNat = (a - n).toNat + (-1 - a).toNat := by omega
  rw [hres, ((hg.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hana.continuousAt).1
    hg_eqNE).iteratedDeriv_eq, hidx,
    inv_factorial_smul_iteratedDeriv_pow_sub_smul _ _ hg₀_an.contDiffAt]

/-- The pole-free case of `residue_eq_of_eventuallyEq_zpow_smul`: when
`meromorphicOrderAt f z₀ ≥ 0`, `f` has no pole so its residue is `0`, and `g` vanishes to
order `> -1 - n`, so the Taylor coefficient on the right is `0` as well. -/
private theorem residue_eq_of_eventuallyEq_zpow_smul_of_order_nonneg [CompleteSpace E]
    {f g : ℂ → E} {z₀ : ℂ} {n : ℤ}
    (hn : n ≤ -1) (hg : AnalyticAt ℂ g z₀)
    (hord_eq : meromorphicOrderAt f z₀ = (n : WithTop ℤ) + meromorphicOrderAt g z₀)
    (ha : 0 ≤ meromorphicOrderAt f z₀) :
    residue f z₀ = ((-1 - n).toNat.factorial : ℂ)⁻¹ • iteratedDeriv (-1 - n).toNat g z₀ := by
  rw [residue_eq_zero_of_meromorphicOrderAt_nonneg ha,
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hg).1 ?_ _ (Nat.lt_succ_self _),
    smul_zero]
  rcases eq_or_ne (analyticOrderAt g z₀) ⊤ with htop | htop
  · rw [htop]
    exact le_top
  · lift analyticOrderAt g z₀ to ℕ using htop with m hm
    rw [Nat.cast_le]
    have hcompute : meromorphicOrderAt g z₀ = ((m : ℤ) : WithTop ℤ) := by
      rw [hg.meromorphicOrderAt_eq, ← hm]
      simp
    rw [hord_eq, hcompute, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_le_coe] at ha
    omega

/-- **Generalized characteristic value of the residue.** If `f z = (z − z₀) ^ n • g z` near `z₀` (on
the punctured neighborhood) with `g` analytic at `z₀` and `n ≤ −1`, then the residue is the Taylor
coefficient `((−1 − n)!)⁻¹ • iteratedDeriv (−1 − n) g z₀`. Unlike `residue_eq_of_order_lt_zero` this
drops the hypothesis `g z₀ ≠ 0`, so the presentation exponent `n` need not be the meromorphic order
of `f`: `g` may vanish at `z₀`, raising the true pole order above `n`; only when `g`'s vanishing
order is at least `-n` is `f` analytic (residue `0`). -/
theorem residue_eq_of_eventuallyEq_zpow_smul [CompleteSpace E] {f g : ℂ → E} {z₀ : ℂ} {n : ℤ}
    (hn : n ≤ -1) (hg : AnalyticAt ℂ g z₀) (hfg : f =ᶠ[𝓝[≠] z₀] fun z ↦ (z - z₀) ^ n • g z) :
    residue f z₀ = ((-1 - n).toNat.factorial : ℂ)⁻¹ • iteratedDeriv (-1 - n).toNat g z₀ := by
  have hf : MeromorphicAt f z₀ :=
    MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt.mpr ⟨n, g, hg, hfg⟩
  have hord_eq : meromorphicOrderAt f z₀ = (n : WithTop ℤ) + meromorphicOrderAt g z₀ := by
    -- The presentation is, by definition, the `Pi` scalar product of `(· - z₀) ^ n` and `g`.
    rw [meromorphicOrderAt_congr hfg,
      show (fun z ↦ (z - z₀) ^ n • g z) = ((· - z₀) ^ n) • g from rfl,
      meromorphicOrderAt_smul (by fun_prop) hg.meromorphicAt, meromorphicOrderAt_zpow_id_sub_const]
  rcases lt_or_ge (meromorphicOrderAt f z₀) 0 with ha | ha
  · exact residue_eq_of_eventuallyEq_zpow_smul_of_order_lt_zero hg hfg hf hord_eq ha
  · exact residue_eq_of_eventuallyEq_zpow_smul_of_order_nonneg hn hg hord_eq ha

/-- Any meromorphic `f` admits an analytic presentation `f z = (z − z₀) ^ m • φ z` near `z₀` at any
exponent `m` at or below its meromorphic order (padding the reduced presentation with a nonnegative
power of `z − z₀`). The factor `φ` is analytic but may vanish at `z₀` when `m` is strictly below the
order. Brings two meromorphic functions to a common exponent before adding their residues, and is
the factorisation entry point for the canonical Laurent data (`MeromorphicLaurent.lean`). -/
lemma exists_analyticAt_eventuallyEq_zpow_smul {f : ℂ → E} {z₀ : ℂ} {m : ℤ}
    (hf : MeromorphicAt f z₀) (hm : (m : WithTop ℤ) ≤ meromorphicOrderAt f z₀) :
    ∃ φ : ℂ → E, AnalyticAt ℂ φ z₀ ∧ f =ᶠ[𝓝[≠] z₀] fun z ↦ (z - z₀) ^ m • φ z := by
  rcases eq_or_ne (meromorphicOrderAt f z₀) ⊤ with htop | htop
  · refine ⟨fun _ ↦ 0, analyticAt_const, ?_⟩
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 htop] with z hz
    simp [hz]
  · obtain ⟨g₀, hg₀_an, -, hf_eq⟩ := (meromorphicOrderAt_ne_top_iff hf).1 htop
    set a := (meromorphicOrderAt f z₀).untop₀
    have hma : m ≤ a := by rwa [← WithTop.coe_le_coe, WithTop.coe_untop₀_of_ne_top htop]
    refine ⟨fun z ↦ (z - z₀) ^ (a - m).toNat • g₀ z, by fun_prop, ?_⟩
    filter_upwards [hf_eq, self_mem_nhdsWithin] with z hz1 hz2
    rw [hz1, smul_smul, ← zpow_natCast, ← zpow_add₀ (sub_ne_zero.mpr hz2),
      Int.toNat_of_nonneg (by omega), add_sub_cancel]

/-- **Additivity of the residue.** The residue is additive on functions meromorphic at `z₀`. -/
@[simp]
theorem residue_add [CompleteSpace E] {f g : ℂ → E} {z₀ : ℂ} (hf : MeromorphicAt f z₀)
    (hg : MeromorphicAt g z₀) :
    residue (f + g) z₀ = residue f z₀ + residue g z₀ := by
  obtain ⟨m, hm1, hm⟩ :=
    (min (meromorphicOrderAt f z₀) (meromorphicOrderAt g z₀)).exists_le_and_coe_le (-1)
  rw [le_min_iff] at hm
  obtain ⟨φf, hφf_an, hφf_eq⟩ := exists_analyticAt_eventuallyEq_zpow_smul hf hm.1
  obtain ⟨φg, hφg_an, hφg_eq⟩ := exists_analyticAt_eventuallyEq_zpow_smul hg hm.2
  have hφfg_eq : (f + g) =ᶠ[𝓝[≠] z₀] fun z ↦ (z - z₀) ^ m • (φf + φg) z := by
    filter_upwards [hφf_eq, hφg_eq] with z hz1 hz2
    simp only [Pi.add_apply, hz1, hz2, smul_add]
  rw [residue_eq_of_eventuallyEq_zpow_smul hm1 hφf_an hφf_eq,
    residue_eq_of_eventuallyEq_zpow_smul hm1 hφg_an hφg_eq,
    residue_eq_of_eventuallyEq_zpow_smul hm1 (hφf_an.add hφg_an) hφfg_eq,
    iteratedDeriv_add hφf_an.contDiffAt hφg_an.contDiffAt, smul_add]

/-- **Scaling of the residue.** The residue commutes with scalar multiplication.

No meromorphy hypothesis is needed: the identity holds for every `f`, through the junk value where
`f` is not meromorphic at `z₀`. Contrast `residue_add`, whose hypotheses are essential — two
functions that are not meromorphic can sum to one that is. -/
@[simp]
theorem residue_const_smul {f : ℂ → E} {z₀ : ℂ} (c : ℂ) :
    residue (c • f) z₀ = c • residue f z₀ := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [zero_smul, zero_smul]
    exact residue_eq_zero_of_analyticAt analyticAt_const
  by_cases hf : MeromorphicAt f z₀
  · rcases lt_or_ge (meromorphicOrderAt f z₀) 0 with hlt | hge
    · obtain ⟨g, hg, hg_ne, hfg, hres⟩ := exists_residue_eq_of_meromorphicOrderAt_lt_zero hf hlt
      have hcfg : c • f =ᶠ[𝓝[≠] z₀]
          fun z ↦ (z - z₀) ^ (meromorphicOrderAt f z₀).untop₀ • (c • g) z := by
        filter_upwards [hfg] with z hz
        rw [Pi.smul_apply, hz, Pi.smul_apply, smul_comm]
      have hcg : AnalyticAt ℂ (c • g) z₀ := hg.const_smul
      rw [hres, residue_eq_of_order_lt_zero (by simpa [← not_le] using hlt) hcg
        (smul_ne_zero hc hg_ne) hcfg, iteratedDeriv_const_smul_field, smul_comm]
    · rw [residue_eq_zero_of_meromorphicOrderAt_nonneg hge, smul_zero,
        residue_eq_zero_of_meromorphicOrderAt_nonneg
          (by rwa [meromorphicOrderAt_const_smul_eq_meromorphicOrderAt hc])]
  · rw [residue_of_not_meromorphicAt hf, smul_zero, residue_of_not_meromorphicAt
      (by rwa [meromorphicAt_const_smul_iff_meromorphicAt hc])]

/-- **Scaling of the residue (applied `*`).** Scaling a scalar function `f` by a constant scales its
residue by that constant; the applied companion to `residue_const_smul`. -/
@[simp]
theorem residue_const_mul {f : ℂ → ℂ} {z₀ : ℂ} (c : ℂ) :
    residue (fun z ↦ c * f z) z₀ = c * residue f z₀ :=
  -- `fun z ↦ c * f z` is `c • f` by `Pi.smul_apply` and `smul_eq_mul`, both definitional.
  residue_const_smul c

/-- **Subtractivity of the residue.** The residue distributes over subtraction of meromorphic
functions; the `−1` scaling case of `residue_add` and `residue_const_smul`. -/
@[simp]
theorem residue_sub [CompleteSpace E] {f g : ℂ → E} {z₀ : ℂ} (hf : MeromorphicAt f z₀)
    (hg : MeromorphicAt g z₀) :
    residue (f - g) z₀ = residue f z₀ - residue g z₀ := by
  rw [sub_eq_add_neg, residue_add hf hg.neg, ← neg_one_smul ℂ g, residue_const_smul, neg_one_smul,
    sub_eq_add_neg]

/-- **The residue of a finite sum.** For a finite family of functions meromorphic at `z₀`, the
residue of the sum is the sum of the residues — the form consumed by the residue theorem. -/
@[simp]
theorem residue_sum [CompleteSpace E] {ι : Type*} (s : Finset ι) {f : ι → ℂ → E} {z₀ : ℂ}
    (hf : ∀ i ∈ s, MeromorphicAt (f i) z₀) :
    residue (∑ i ∈ s, f i) z₀ = ∑ i ∈ s, residue (f i) z₀ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact residue_eq_zero_of_analyticAt analyticAt_const
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      residue_add (hf a (Finset.mem_insert_self a s))
        (MeromorphicAt.sum fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)]

/-- **The residue of the Cauchy kernel.** If `g` is analytic at `z₀`, then the function
`g z / (z - z₀) ^ (k + 1)` has residue the Taylor coefficient `iteratedDeriv k g z₀ / k !` at `z₀`:
the whole Laurent principal part comes from the first `k + 1` Taylor terms of `g`, and only the one
of index `k` sits at order `−1`. This is the residue behind Cauchy's integral formula for the
`k`-th derivative; the constant case is `TauCeti.Contour.residue_const_div_sub_pow`. -/
@[simp]
theorem residue_div_sub_pow_of_analyticAt {g : ℂ → ℂ} {z₀ : ℂ} (hg : AnalyticAt ℂ g z₀) (k : ℕ) :
    residue (fun z ↦ g z / (z - z₀) ^ (k + 1)) z₀
      = iteratedDeriv k g z₀ / (k.factorial : ℂ) := by
  have hfg : (fun z ↦ g z / (z - z₀) ^ (k + 1)) =ᶠ[𝓝[≠] z₀]
      fun z ↦ (z - z₀) ^ (-(k + 1 : ℕ) : ℤ) • g z :=
    Filter.Eventually.of_forall fun z ↦ by
      simp only [smul_eq_mul, zpow_neg, zpow_natCast, div_eq_inv_mul]
  have hidx : (-1 - (-(k + 1 : ℕ) : ℤ)).toNat = k := by omega
  rw [residue_eq_of_eventuallyEq_zpow_smul (by omega) hg hfg, hidx, smul_eq_mul, inv_mul_eq_div]

/-- **The residue of a Laurent monomial**: `residue (a / (z - z₀)^(k+1)) z₀` is `a` for `k = 0`
and `0` for higher-order terms. -/
@[simp]
theorem residue_const_div_sub_pow (a z₀ : ℂ) (k : ℕ) :
    residue (fun z ↦ a / (z - z₀) ^ (k + 1)) z₀ = if k = 0 then a else 0 := by
  rw [residue_div_sub_pow_of_analyticAt analyticAt_const, iteratedDeriv_const]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · simp [hk.ne']

/-- **The residue from a Laurent expansion.** If `f z = g z + ∑ k, a k / (z - z₀)^(k+1)` near
`z₀` with `g` analytic at `z₀`, then `residue f z₀` is the first Laurent coefficient `a 0` (or
`0` for an empty expansion): the analytic part and the higher-order terms contribute nothing. -/
theorem residue_of_laurent_expansion {f g : ℂ → ℂ} {z₀ : ℂ} {N : ℕ} {a : Fin N → ℂ}
    (hg : AnalyticAt ℂ g z₀)
    (hf_eq : ∀ᶠ z in 𝓝[≠] z₀, f z = g z + ∑ k : Fin N, a k / (z - z₀) ^ (k.val + 1)) :
    residue f z₀ = if h : 0 < N then a ⟨0, h⟩ else 0 := by
  have hmono : ∀ k : Fin N, MeromorphicAt (fun z ↦ a k / (z - z₀) ^ (k.val + 1)) z₀ :=
    fun k ↦ by fun_prop
  have hf_eq' : f =ᶠ[𝓝[≠] z₀]
      g + ∑ k : Fin N, fun z ↦ a k / (z - z₀) ^ (k.val + 1) := by
    filter_upwards [hf_eq] with z hz
    simpa [Finset.sum_apply] using hz
  rw [residue_congr_nhdsNE hf_eq',
    residue_add hg.meromorphicAt (MeromorphicAt.sum fun k _ ↦ hmono k),
    residue_eq_zero_of_analyticAt hg, zero_add, residue_sum _ fun k _ ↦ hmono k]
  simp only [residue_const_div_sub_pow]
  rcases Nat.eq_zero_or_pos N with rfl | hpos
  · simp
  · rw [dite_eq_left hpos, Finset.sum_eq_single ⟨0, hpos⟩ (fun k _ hk ↦ ite_eq_right fun h0 ↦
      hk (Fin.ext h0)) (by simp), ite_eq_left rfl]

end TauCeti.Contour

end
