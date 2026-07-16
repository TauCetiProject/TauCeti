/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.Residue

/-!
# Canonical Laurent data of a meromorphic function

For `f` meromorphic at `s`, this file extracts its **canonical Laurent data**: the polar order
`meroPolarOrderAt` — computed from `meromorphicOrderAt`, not chosen — together with Laurent
coefficients, the finite polar part, and the analytic part, satisfying
`f = analytic part + ∑ k, coeff k / (z - s)^(k+1)` near `s`. Because the tail length is the
computable canonical order, downstream facts about it are provable (it is `1` at a simple pole)
rather than opaque to a `Classical.choose` witness — which is what lets condition (A′) of the
generalized residue theorem be discharged at simple poles by flatness of order one.

## Main definitions

* `Contour.meroPolarOrderAt hMero` — the canonical polar order: the negative part of
  `meromorphicOrderAt f s` (`0` at an analytic-or-removable point).
* `Contour.meroPolarCoeffAt hMero k` — the `k`-th Laurent coefficient at `s`.
* `Contour.meroPolarPartAt hMero` — the finite polar part `∑ k, coeff k / (z - s)^(k+1)`.
* `Contour.meroAnalyticPartAt hMero` — the analytic part at `s`.

## Main results

* `Contour.mero_laurent_data_exists` — the Laurent decomposition with tail length pinned to the
  canonical order.
* `Contour.eventuallyEq_meroAnalyticPartAt_add_meroPolarPartAt` — `f` equals analytic part plus
  polar part near `s`.
* `Contour.meroPolarPartAt_eq_sum` — the polar part as its explicit Laurent sum.
* `Contour.meroPolarCoeffAt_zero_eq_residue` — the leading coefficient is the residue.
* `Contour.meroPolarOrderAt_eq_one` — the canonical order at a simple pole is `1`.

## Provenance

Migrated from the per-point Laurent-extraction block of
`HungerbuhlerWasem/LaurentExtraction.lean` in the AINTLIB `LeanModularForms` development
(`meroPolarOrderAt` through `meroPolarCoeffAt_zero_eq_residue`); the residue identification is
by `Contour.residue_of_laurent_expansion` against the Taylor-coefficient residue. See
N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
Theorem*, arXiv:1808.00997, §3.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Filter Set Topology

/-- **The canonical polar order** of a meromorphic function at `s`: the negative part of
`meromorphicOrderAt f s`. For a pole of order `k` this is `k` (in particular `1` at a simple
pole, `meroPolarOrderAt_eq_one`); at an analytic-or-removable point — including locally
vanishing `f` — it is `0`. Computed from `f` alone, so callers can evaluate it, unlike a
`Classical.choose`-extracted tail length. -/
def meroPolarOrderAt {f : ℂ → ℂ} {s : ℂ} (_hMero : MeromorphicAt f s) : ℕ :=
  (-(meromorphicOrderAt f s).untop₀).toNat

/-- The canonical polar order, computed from `meromorphicOrderAt`. -/
theorem meroPolarOrderAt_eq_of_order_eq {f : ℂ → ℂ} {s : ℂ}
    (hMero : MeromorphicAt f s) {n : ℤ} (h : meromorphicOrderAt f s = n) :
    meroPolarOrderAt hMero = (-n).toNat := by
  rw [meroPolarOrderAt, h, WithTop.untop₀_coe]

/-- **At a simple pole the canonical polar order is `1`.** With flatness of order one
(`IsPwC1ImmersionOn.flatOfOrder_one`), this discharges condition (A′) of the generalized residue
theorem at simple poles. -/
theorem meroPolarOrderAt_eq_one {f : ℂ → ℂ} {s : ℂ}
    (hMero : MeromorphicAt f s) (h : meromorphicOrderAt f s = -1) :
    meroPolarOrderAt hMero = 1 := by
  rw [meroPolarOrderAt_eq_of_order_eq hMero h]
  rfl

/-- Peel one vanishing factor off an analytic function: `g z = g s + (z - s) * g₁ z` with `g₁`
analytic at `s`. -/
private theorem analyticAt_peel_one {g : ℂ → ℂ} {s : ℂ} (hg : AnalyticAt ℂ g s) :
    ∃ g₁ : ℂ → ℂ, AnalyticAt ℂ g₁ s ∧
      ∀ᶠ z in 𝓝 s, g z = g s + (z - s) * g₁ z := by
  have h_diff : AnalyticAt ℂ (fun z => g z - g s) s := hg.sub analyticAt_const
  have h_value : (fun z => g z - g s) s = 0 := by simp
  have h_ord_ne : analyticOrderAt (fun z => g z - g s) s ≠ 0 := fun h_eq =>
    (h_diff.analyticOrderAt_eq_zero).mp h_eq h_value
  have h_ge : (1 : ℕ∞) ≤ analyticOrderAt (fun z => g z - g s) s :=
    Order.one_le_iff_ne_zero.mpr h_ord_ne
  obtain ⟨g₁, hg₁_an, hg₁_eq⟩ :=
    (natCast_le_analyticOrderAt h_diff).mp (by exact_mod_cast h_ge)
  refine ⟨g₁, hg₁_an, ?_⟩
  filter_upwards [hg₁_eq] with z hz
  have heq : g z - g s = (z - s) * g₁ z := by simpa using hz
  linear_combination heq

/-- Taylor decomposition of an analytic function to order `k`:
`g z = ∑ j < k, c j * (z - s)^j + (z - s)^k * R z` with `R` analytic at `s`. -/
private theorem analyticAt_taylor_decomp {g : ℂ → ℂ} {s : ℂ}
    (hg : AnalyticAt ℂ g s) (k : ℕ) :
    ∃ (c : Fin k → ℂ) (R : ℂ → ℂ), AnalyticAt ℂ R s ∧
      ∀ᶠ z in 𝓝 s, g z = (∑ j : Fin k, c j * (z - s) ^ j.val) + (z - s) ^ k * R z := by
  induction k with
  | zero =>
      refine ⟨Fin.elim0, g, hg, ?_⟩
      filter_upwards with z
      simp
  | succ k ih =>
      obtain ⟨c, R, hR_an, hR_eq⟩ := ih
      obtain ⟨R', hR'_an, hR'_eq⟩ := analyticAt_peel_one hR_an
      refine ⟨Fin.snoc c (R s), R', hR'_an, ?_⟩
      filter_upwards [hR_eq, hR'_eq] with z hR_eq_z hR'_eq_z
      rw [hR_eq_z, hR'_eq_z, Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_last, Fin.val_castSucc]
      ring

private theorem pow_div_pow_neg {w : ℂ} (hw : w ≠ 0) {k j : ℕ} (hjk : j < k) :
    w ^ j * (w ^ k)⁻¹ = (w ^ (k - j))⁻¹ := by
  have h_exp : (k - j) + j = k := by omega
  rw [show (w ^ k)⁻¹ = (w ^ ((k - j) + j))⁻¹ by rw [h_exp], pow_add]
  field_simp

private theorem reindex_sum_fin_neg {k : ℕ} (c : Fin k → ℂ) (w : ℂ) :
    (∑ j : Fin k, c j / w ^ (k - j.val)) =
      ∑ i : Fin k,
        c ⟨k - 1 - i.val, by have := i.isLt; omega⟩ / w ^ (i.val + 1) := by
  let σ : Fin k → Fin k := fun j => ⟨k - 1 - j.val, by have := j.isLt; omega⟩
  have hσ_invol : Function.Involutive σ := fun j => by
    ext
    have := j.isLt
    simp only [σ]
    omega
  have h_sum_eq : (∑ i : Fin k, c (σ i) / w ^ (k - (σ i).val)) =
      ∑ j : Fin k, c j / w ^ (k - j.val) :=
    Equiv.sum_comp ⟨σ, σ, hσ_invol.leftInverse, hσ_invol.rightInverse⟩
      (fun j => c j / w ^ (k - j.val))
  rw [← h_sum_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  simp only [σ]
  omega

/-- Laurent data of length exactly `k` from a `(z - s)^(-k)`-factorisation with analytic
cofactor: Taylor-expand the cofactor to order `k` and divide. -/
private theorem laurent_data_of_zpow_factor {f g₀ : ℂ → ℂ} {s : ℂ} (k : ℕ)
    (hg₀_an : AnalyticAt ℂ g₀ s)
    (hg₀_eq : ∀ᶠ z in 𝓝[≠] s, f z = (z - s) ^ (-(k : ℤ)) • g₀ z) :
    ∃ (a : Fin k → ℂ) (g : ℂ → ℂ),
      AnalyticAt ℂ g s ∧
      ∀ᶠ z in 𝓝[≠] s, f z = g z + ∑ i : Fin k, a i / (z - s) ^ (i.val + 1) := by
  obtain ⟨c, R, hR_an, hR_eq⟩ := analyticAt_taylor_decomp hg₀_an k
  refine ⟨fun i : Fin k => c ⟨k - 1 - i.val, by have := i.isLt; omega⟩, R, hR_an, ?_⟩
  filter_upwards [hg₀_eq, nhdsWithin_le_nhds hR_eq, self_mem_nhdsWithin]
    with z hf_eq hR_eq_z hz_ne
  have hz_sub : (z - s) ≠ 0 := sub_ne_zero.mpr hz_ne
  rw [hf_eq, hR_eq_z, smul_eq_mul, zpow_neg, zpow_natCast, mul_add]
  have h1 : ((z - s) ^ k)⁻¹ * ((z - s) ^ k * R z) = R z := by field_simp
  rw [h1, add_comm]
  congr 1
  rw [Finset.mul_sum, show ∑ j : Fin k, ((z - s) ^ k)⁻¹ * (c j * (z - s) ^ j.val) =
      ∑ j : Fin k, c j / (z - s) ^ (k - j.val) from
    Finset.sum_congr rfl fun j _ => by
      rw [div_eq_mul_inv, show ((z - s) ^ k)⁻¹ * (c j * (z - s) ^ j.val) =
          c j * ((z - s) ^ j.val * ((z - s) ^ k)⁻¹) by ring,
        pow_div_pow_neg hz_sub j.isLt]]
  exact reindex_sum_fin_neg c (z - s)

/-- Factorisation of a meromorphic `f` at the canonical polar order:
`f = (z - s)^(-meroPolarOrderAt) • g₀` near `s` with `g₀` analytic (nonnegative powers of
`z - s` are absorbed into the cofactor; `g₀ = 0` when `f` vanishes near `s`). -/
private theorem exists_zpow_factor_at_canonical_order {f : ℂ → ℂ} {s : ℂ}
    (hMero : MeromorphicAt f s) :
    ∃ g₀ : ℂ → ℂ, AnalyticAt ℂ g₀ s ∧
      ∀ᶠ z in 𝓝[≠] s, f z = (z - s) ^ (-(meroPolarOrderAt hMero : ℤ)) • g₀ z := by
  by_cases h_top : meromorphicOrderAt f s = ⊤
  · have h0 : meroPolarOrderAt hMero = 0 := by
      rw [meroPolarOrderAt, h_top, WithTop.untop₀_top, neg_zero, Int.toNat_zero]
    refine ⟨fun _ => 0, analyticAt_const, ?_⟩
    filter_upwards [meromorphicOrderAt_eq_top_iff.mp h_top] with z hz
    rw [hz, smul_zero]
  · obtain ⟨n, h_ord⟩ := WithTop.ne_top_iff_exists.mp h_top
    obtain ⟨g, hg_an, _, hg_eq⟩ := (meromorphicOrderAt_eq_int_iff hMero).mp h_ord.symm
    have h_val : (meroPolarOrderAt hMero : ℤ) = max (-n) 0 := by
      rw [meroPolarOrderAt_eq_of_order_eq hMero h_ord.symm]
      omega
    rcases le_or_gt 0 n with hn | hn
    · -- no pole: absorb `(z - s)^n` into the analytic cofactor
      refine ⟨fun z => (z - s) ^ n.toNat * g z,
        ((analyticAt_id.sub analyticAt_const).pow _).mul hg_an, ?_⟩
      filter_upwards [hg_eq] with z hz
      rw [hz, show -(meroPolarOrderAt hMero : ℤ) = 0 by omega, zpow_zero, one_smul,
        smul_eq_mul, show n = (n.toNat : ℤ) by omega, zpow_natCast, Int.toNat_natCast]
    · -- a pole of order `-n = meroPolarOrderAt hMero`
      refine ⟨g, hg_an, ?_⟩
      rw [show -(meroPolarOrderAt hMero : ℤ) = n by omega]
      exact hg_eq

/-- **Canonical Laurent data of a meromorphic function**: near `s`,
`f = g + ∑ k, a k / (z - s)^(k+1)` with `g` analytic at `s`, where the tail length is the
canonical polar order `meroPolarOrderAt hMero` — pinned, not existentially chosen, so it is
provable (`1` at a simple pole). -/
theorem mero_laurent_data_exists {f : ℂ → ℂ} {s : ℂ} (hMero : MeromorphicAt f s) :
    ∃ (a : Fin (meroPolarOrderAt hMero) → ℂ) (g : ℂ → ℂ),
      AnalyticAt ℂ g s ∧
      ∀ᶠ z in 𝓝[≠] s,
        f z = g z + ∑ k : Fin (meroPolarOrderAt hMero), a k / (z - s) ^ (k.val + 1) := by
  obtain ⟨g₀, hg₀_an, hg₀_eq⟩ := exists_zpow_factor_at_canonical_order hMero
  exact laurent_data_of_zpow_factor _ hg₀_an hg₀_eq

/-- The `k`-th canonical Laurent coefficient of `f` at `s`. -/
def meroPolarCoeffAt {f : ℂ → ℂ} {s : ℂ} (hMero : MeromorphicAt f s)
    (k : Fin (meroPolarOrderAt hMero)) : ℂ :=
  (mero_laurent_data_exists hMero).choose k

/-- The canonical finite polar part of `f` at `s`: the Laurent tail of length
`meroPolarOrderAt hMero`. -/
def meroPolarPartAt {f : ℂ → ℂ} {s : ℂ} (hMero : MeromorphicAt f s) (z : ℂ) : ℂ :=
  ∑ k : Fin (meroPolarOrderAt hMero), meroPolarCoeffAt hMero k / (z - s) ^ (k.val + 1)

/-- The canonical analytic part of `f` at `s`. -/
def meroAnalyticPartAt {f : ℂ → ℂ} {s : ℂ} (hMero : MeromorphicAt f s) : ℂ → ℂ :=
  (mero_laurent_data_exists hMero).choose_spec.choose

/-- The analytic part is analytic at `s`. -/
theorem meroAnalyticPartAt_analyticAt {f : ℂ → ℂ} {s : ℂ}
    (hMero : MeromorphicAt f s) : AnalyticAt ℂ (meroAnalyticPartAt hMero) s :=
  (mero_laurent_data_exists hMero).choose_spec.choose_spec.1

/-- **The canonical Laurent decomposition**: near `s`, `f` is the analytic part plus the polar
part. -/
theorem eventuallyEq_meroAnalyticPartAt_add_meroPolarPartAt {f : ℂ → ℂ} {s : ℂ}
    (hMero : MeromorphicAt f s) :
    ∀ᶠ z in 𝓝[≠] s, f z = meroAnalyticPartAt hMero z + meroPolarPartAt hMero z :=
  (mero_laurent_data_exists hMero).choose_spec.choose_spec.2

/-- The polar part as its explicit Laurent sum — the characteristic unfolding of
`meroPolarPartAt`. -/
theorem meroPolarPartAt_eq_sum {f : ℂ → ℂ} {s : ℂ}
    (hMero : MeromorphicAt f s) (z : ℂ) :
    meroPolarPartAt hMero z =
      ∑ k : Fin (meroPolarOrderAt hMero),
        meroPolarCoeffAt hMero k / (z - s) ^ (k.val + 1) := by
  unfold meroPolarPartAt
  rfl

/-- The polar part is differentiable away from its pole. -/
theorem meroPolarPartAt_differentiableAt {f : ℂ → ℂ} {s : ℂ}
    (hMero : MeromorphicAt f s) {z : ℂ} (hz : z ≠ s) :
    DifferentiableAt ℂ (meroPolarPartAt hMero) z := by
  unfold meroPolarPartAt
  refine DifferentiableAt.fun_sum fun k _ => ?_
  exact (differentiableAt_const _).div
    ((differentiableAt_id.sub (differentiableAt_const _)).pow _)
    (pow_ne_zero _ (sub_ne_zero.mpr hz))

/-- The polar part is analytic away from its pole. -/
theorem meroPolarPartAt_analyticAt_of_ne {f : ℂ → ℂ} {s : ℂ}
    (hMero : MeromorphicAt f s) {w : ℂ} (hw : w ≠ s) :
    AnalyticAt ℂ (meroPolarPartAt hMero) w := by
  unfold meroPolarPartAt
  refine Finset.analyticAt_fun_sum _ fun k _ => ?_
  exact analyticAt_const.div ((analyticAt_id.sub analyticAt_const).pow _)
    (pow_ne_zero _ (sub_ne_zero.mpr hw))

/-- **The leading canonical Laurent coefficient is the residue.** -/
theorem meroPolarCoeffAt_zero_eq_residue {f : ℂ → ℂ} {s : ℂ}
    (hMero : MeromorphicAt f s) (h_pos : 0 < meroPolarOrderAt hMero) :
    meroPolarCoeffAt hMero ⟨0, h_pos⟩ = residue f s := by
  have hres := residue_of_laurent_expansion
    (mero_laurent_data_exists hMero).choose_spec.choose_spec.1
    (mero_laurent_data_exists hMero).choose_spec.choose_spec.2
  rw [dif_pos h_pos] at hres
  exact hres.symm

end TauCeti.Contour

end
