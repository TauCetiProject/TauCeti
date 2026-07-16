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
`meromorphicPolarOrderAt` — computed from `meromorphicOrderAt`, not chosen — together with Laurent
coefficients, the finite polar part, and the analytic part, satisfying
`f = analytic part + ∑ k, coeff k / (z - s)^(k+1)` near `s`. Because the tail length is the
computable canonical order, downstream facts about it are provable (it is `1` at a simple pole)
rather than opaque to a `Classical.choose` witness — which is what lets condition (A′) of the
generalized residue theorem be discharged at simple poles by flatness of order one.

## Main definitions

* `Contour.meromorphicPolarOrderAt f s` — the canonical polar order: the negative part of
  `meromorphicOrderAt f s` (`0` at an analytic-or-removable point).
* `Contour.meromorphicPolarCoeffAt hMero k` — the `k`-th Laurent coefficient at `s`.
* `Contour.meromorphicPolarPartAt hMero` — the finite polar part `∑ k, coeff k / (z - s)^(k+1)`.
* `Contour.meromorphicAnalyticPartAt hMero` — the analytic part at `s`.

## Main results

* `Contour.exists_laurent_data_of_meromorphicAt` — the Laurent decomposition with tail length
  pinned to the canonical order.
* `Contour.eventuallyEq_meromorphicAnalyticPartAt_add_meromorphicPolarPartAt` — `f` equals
  analytic part plus polar part near `s`.
* `Contour.meromorphicPolarPartAt_eq_sum` — the polar part as its explicit Laurent sum.
* `Contour.meromorphicPolarCoeffAt_zero_eq_residue` — the leading coefficient is the residue.
* `Contour.meromorphicPolarOrderAt_eq_one` — the canonical order at a simple pole is `1`.

## Provenance

Migrated from the per-point Laurent-extraction block of
`HungerbuhlerWasem/LaurentExtraction.lean` in the AINTLIB `LeanModularForms` development
(`meroPolarOrderAt` through `meroPolarCoeffAt_zero_eq_residue`, here with `meromorphic` spelled
out); the residue identification is by `Contour.residue_of_laurent_expansion` against the
Taylor-coefficient residue. See
N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
Theorem*, arXiv:1808.00997, §3.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Filter Set Topology

/-- **The canonical polar order** of a meromorphic function at `s`: the negative part of
`meromorphicOrderAt f s`. For a pole of order `k` this is `k` (in particular `1` at a simple
pole, `meromorphicPolarOrderAt_eq_one`); at an analytic-or-removable point — including locally
vanishing `f` — it is `0`. Computed from `f` alone, so callers can evaluate it, unlike a
`Classical.choose`-extracted tail length. -/
def meromorphicPolarOrderAt (f : ℂ → ℂ) (s : ℂ) : ℕ :=
  (-(meromorphicOrderAt f s).untop₀).toNat

/-- The canonical polar order, computed from `meromorphicOrderAt`. -/
theorem meromorphicPolarOrderAt_eq_of_order_eq {f : ℂ → ℂ} {s : ℂ}
    {n : ℤ} (h : meromorphicOrderAt f s = n) :
    meromorphicPolarOrderAt f s = (-n).toNat := by
  rw [meromorphicPolarOrderAt, h, WithTop.untop₀_coe]

/-- **At a simple pole the canonical polar order is `1`.** With flatness of order one
(`IsPwC1ImmersionOn.flatOfOrder_one`), this discharges condition (A′) of the generalized residue
theorem at simple poles. -/
theorem meromorphicPolarOrderAt_eq_one {f : ℂ → ℂ} {s : ℂ}
    (h : meromorphicOrderAt f s = -1) :
    meromorphicPolarOrderAt f s = 1 := by
  rw [meromorphicPolarOrderAt_eq_of_order_eq h]
  rfl

/-- Taylor decomposition of an analytic function to order `k`:
`g z = ∑ j < k, c j * (z - s)^j + (z - s)^k * R z` with `R` analytic at `s`. Mathlib's
`AnalyticAt.exists_eventuallyEq_sum_add_pow_mul` at the translate `g (· + s)`. -/
private theorem analyticAt_taylor_decomp {g : ℂ → ℂ} {s : ℂ}
    (hg : AnalyticAt ℂ g s) (k : ℕ) :
    ∃ (c : Fin k → ℂ) (R : ℂ → ℂ), AnalyticAt ℂ R s ∧
      ∀ᶠ z in 𝓝 s, g z = (∑ j : Fin k, c j * (z - s) ^ j.val) + (z - s) ^ k * R z := by
  have h1 : AnalyticAt ℂ (fun w : ℂ => w + s) 0 := analyticAt_id.add analyticAt_const
  have hg0 : AnalyticAt ℂ (fun w => g (w + s)) 0 := by
    have := AnalyticAt.comp (f := fun w : ℂ => w + s) (x := (0 : ℂ)) (by simpa using hg) h1
    exact this
  obtain ⟨F, hF_an, hF_eq⟩ := hg0.exists_eventuallyEq_sum_add_pow_mul k
  have h2 : AnalyticAt ℂ (fun z : ℂ => z - s) s := analyticAt_id.sub analyticAt_const
  have hF_comp : AnalyticAt ℂ (fun z => F (z - s)) s := by
    have := AnalyticAt.comp (f := fun z : ℂ => z - s) (x := s) (by simpa using hF_an) h2
    exact this
  refine ⟨fun j => iteratedDeriv j.val (fun w => g (w + s)) 0 / j.val.factorial,
    fun z => F (z - s), hF_comp, ?_⟩
  have h_tend : Filter.Tendsto (fun z : ℂ => z - s) (𝓝 s) (𝓝 0) := by
    simpa using (continuous_sub_right s).tendsto s
  filter_upwards [h_tend.eventually hF_eq] with z hz
  have hz' : g z = ∑ i ∈ Finset.range k,
      ((z - s) ^ i / (i.factorial : ℂ)) • iteratedDeriv i (fun w => g (w + s)) 0 +
        (z - s) ^ k • F (z - s) := by simpa using hz
  rw [hz', smul_eq_mul, mul_comm ((z - s) ^ k)]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun j => iteratedDeriv j (fun w => g (w + s)) 0 /
    (j.factorial : ℂ) * (z - s) ^ j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul]
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

/-- **Canonical Laurent data of a meromorphic function**: near `s`,
`f = g + ∑ k, a k / (z - s)^(k+1)` with `g` analytic at `s`, where the tail length is the
canonical polar order `meromorphicPolarOrderAt f s` — pinned, not existentially chosen, so it is
provable (`1` at a simple pole). -/
theorem exists_laurent_data_of_meromorphicAt {f : ℂ → ℂ} {s : ℂ} (hMero : MeromorphicAt f s) :
    ∃ (a : Fin (meromorphicPolarOrderAt f s) → ℂ) (g : ℂ → ℂ),
      AnalyticAt ℂ g s ∧
      ∀ᶠ z in 𝓝[≠] s,
        f z = g z + ∑ k : Fin (meromorphicPolarOrderAt f s), a k / (z - s) ^ (k.val + 1) := by
  have hm : (-(meromorphicPolarOrderAt f s : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f s := by
    rcases eq_or_ne (meromorphicOrderAt f s) ⊤ with h | h
    · rw [h]; exact le_top
    · rw [← WithTop.coe_untop₀_of_ne_top h]
      rw [show (-(meromorphicPolarOrderAt f s : ℤ) : WithTop ℤ) =
          ((-(meromorphicPolarOrderAt f s : ℤ) : ℤ) : WithTop ℤ) by push_cast; ring,
        WithTop.coe_le_coe, meromorphicPolarOrderAt]
      omega
  obtain ⟨g₀, hg₀_an, hg₀_eq⟩ := exists_analyticAt_eventuallyEq_zpow_smul hMero hm
  exact laurent_data_of_zpow_factor _ hg₀_an hg₀_eq

/-- The `k`-th canonical Laurent coefficient of `f` at `s`. -/
def meromorphicPolarCoeffAt {f : ℂ → ℂ} {s : ℂ} (hMero : MeromorphicAt f s)
    (k : Fin (meromorphicPolarOrderAt f s)) : ℂ :=
  (exists_laurent_data_of_meromorphicAt hMero).choose k

/-- The canonical finite polar part of `f` at `s`: the Laurent tail of length
`meromorphicPolarOrderAt f s`. -/
def meromorphicPolarPartAt {f : ℂ → ℂ} {s : ℂ} (hMero : MeromorphicAt f s) (z : ℂ) : ℂ :=
  ∑ k : Fin (meromorphicPolarOrderAt f s), meromorphicPolarCoeffAt hMero k / (z - s) ^ (k.val + 1)

/-- The canonical analytic part of `f` at `s`. -/
def meromorphicAnalyticPartAt {f : ℂ → ℂ} {s : ℂ} (hMero : MeromorphicAt f s) : ℂ → ℂ :=
  (exists_laurent_data_of_meromorphicAt hMero).choose_spec.choose

/-- The analytic part is analytic at `s`. -/
theorem meromorphicAnalyticPartAt_analyticAt {f : ℂ → ℂ} {s : ℂ}
    (hMero : MeromorphicAt f s) : AnalyticAt ℂ (meromorphicAnalyticPartAt hMero) s :=
  (exists_laurent_data_of_meromorphicAt hMero).choose_spec.choose_spec.1

/-- **The canonical Laurent decomposition**: near `s`, `f` is the analytic part plus the polar
part. -/
theorem eventuallyEq_meromorphicAnalyticPartAt_add_meromorphicPolarPartAt {f : ℂ → ℂ} {s : ℂ}
    (hMero : MeromorphicAt f s) :
    ∀ᶠ z in 𝓝[≠] s, f z = meromorphicAnalyticPartAt hMero z + meromorphicPolarPartAt hMero z :=
  (exists_laurent_data_of_meromorphicAt hMero).choose_spec.choose_spec.2

/-- The polar part as its explicit Laurent sum — the characteristic unfolding of
`meromorphicPolarPartAt`. -/
theorem meromorphicPolarPartAt_eq_sum {f : ℂ → ℂ} {s : ℂ}
    (hMero : MeromorphicAt f s) (z : ℂ) :
    meromorphicPolarPartAt hMero z =
      ∑ k : Fin (meromorphicPolarOrderAt f s),
        meromorphicPolarCoeffAt hMero k / (z - s) ^ (k.val + 1) := by
  unfold meromorphicPolarPartAt
  rfl

/-- The polar part is analytic away from its pole. -/
theorem meromorphicPolarPartAt_analyticAt_of_ne {f : ℂ → ℂ} {s : ℂ}
    (hMero : MeromorphicAt f s) {w : ℂ} (hw : w ≠ s) :
    AnalyticAt ℂ (meromorphicPolarPartAt hMero) w := by
  unfold meromorphicPolarPartAt
  refine Finset.analyticAt_fun_sum _ fun k _ => ?_
  exact analyticAt_const.div ((analyticAt_id.sub analyticAt_const).pow _)
    (pow_ne_zero _ (sub_ne_zero.mpr hw))

/-- **The leading canonical Laurent coefficient is the residue.** -/
theorem meromorphicPolarCoeffAt_zero_eq_residue {f : ℂ → ℂ} {s : ℂ}
    (hMero : MeromorphicAt f s) (h_pos : 0 < meromorphicPolarOrderAt f s) :
    meromorphicPolarCoeffAt hMero ⟨0, h_pos⟩ = residue f s := by
  have hres := residue_of_laurent_expansion
    (exists_laurent_data_of_meromorphicAt hMero).choose_spec.choose_spec.1
    (exists_laurent_data_of_meromorphicAt hMero).choose_spec.choose_spec.2
  rw [dif_pos h_pos] at hres
  exact hres.symm

end TauCeti.Contour

end
