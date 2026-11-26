/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.Residue.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import TauCeti.Analysis.Meromorphic.PrincipalPart

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
* `Contour.exists_laurent_data_of_meromorphicOrderAt_eq_neg_succ` — at a pole of given order,
  the top coefficient in the Laurent decomposition is the meromorphic trailing coefficient.
* `Contour.exists_meromorphicOrderAt_eq_neg_succ_of_lt_zero` — a negative meromorphic order is
  `-(m + 1)` for some `m : ℕ`.
* `Contour.eventuallyEq_meromorphicAnalyticPartAt_add_meromorphicPolarPartAt` — `f` equals
  analytic part plus polar part near `s`.
* `Contour.meromorphicPolarPartAt_eq_sum` — the polar part as its explicit Laurent sum.
* `Contour.meromorphicPolarCoeffAt_zero_eq_residue` — the leading coefficient is the residue.
* `Contour.meromorphicPolarOrderAt_eq_one` — the canonical order at a simple pole is `1`.
* `Contour.meromorphicPolarOrderAt_le_iff` — `meromorphicPolarOrderAt f s ≤ k` iff
  `meromorphicOrderAt f s ≥ -k`.
* `Contour.meromorphicPolarOrderAt_div_sub_pow_le` and
  `Contour.meromorphicPolarOrderAt_div_sub_pow_le_of_tendsto_zero` — dividing a meromorphic
  function of order at least `m` (in particular, one tending to `0` along `𝓝[≠] s`) by
  `(z - s) ^ n` gives canonical polar order at most `n - m` (resp. `n - 1`).
* `Contour.hasDerivAt_sum_div_sub_pow` and `Contour.hasDerivAt_meromorphicPolarPartAt` — termwise
  derivative of a finite Laurent principal part away from its pole.
* `Contour.laurent_coeff_unique`, `Contour.laurent_coeff_eq_meromorphicPolarCoeffAt` —
  uniqueness of finite principal-part expansions: any Laurent witness of `f` at `s` has the
  canonical coefficients, compared through zero-padding.

## Provenance

Migrated from the per-point Laurent-extraction block of
`HungerbuhlerWasem/LaurentExtraction.lean` in the AINTLIB `LeanModularForms` development
(`meroPolarOrderAt` through `meroPolarCoeffAt_zero_eq_residue`, here with `meromorphic` spelled
out); the residue identification is by `Contour.residue_of_laurent_expansion` against the
Taylor-coefficient residue. The coefficient-uniqueness block is new glue relative to the
source: AINTLIB transfers condition (B)'s Laurent data through a dedicated constructor
(`ofMeromorphicWithCondB`), while here uniqueness identifies **any** witness with the
canonical coefficients. See
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
theorem meromorphicPolarOrderAt_eq_one {f : ℂ → ℂ} {s : ℂ} (h : meromorphicOrderAt f s = -1) :
    meromorphicPolarOrderAt f s = 1 := by
  rw [meromorphicPolarOrderAt_eq_of_order_eq h]
  rfl

/-- The canonical polar order bounds the meromorphic order from below:
`-(meromorphicPolarOrderAt f s) ≤ meromorphicOrderAt f s`. In particular, polar order `0` means
the meromorphic order is nonnegative. -/
theorem neg_meromorphicPolarOrderAt_le (f : ℂ → ℂ) (s : ℂ) :
    (-(meromorphicPolarOrderAt f s : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f s := by
  rcases eq_or_ne (meromorphicOrderAt f s) ⊤ with h | h
  · rw [h]; exact le_top
  · rw [← WithTop.coe_untop₀_of_ne_top h]
    rw [show (-(meromorphicPolarOrderAt f s : ℤ) : WithTop ℤ) =
        ((-(meromorphicPolarOrderAt f s : ℤ) : ℤ) : WithTop ℤ) by norm_cast,
      WithTop.coe_le_coe, meromorphicPolarOrderAt]
    omega

/-- **A positive canonical polar order pins the meromorphic order**:
`meromorphicOrderAt f s = -(meromorphicPolarOrderAt f s)` whenever the polar order is
positive. -/
theorem meromorphicOrderAt_eq_neg_of_meromorphicPolarOrderAt_pos {f : ℂ → ℂ} {s : ℂ}
    (h_pos : 0 < meromorphicPolarOrderAt f s) :
    meromorphicOrderAt f s = (-(meromorphicPolarOrderAt f s : ℤ) : WithTop ℤ) := by
  rcases eq_or_ne (meromorphicOrderAt f s) ⊤ with h | h
  · rw [meromorphicPolarOrderAt, h] at h_pos
    simp at h_pos
  · rw [← WithTop.coe_untop₀_of_ne_top h]
    rw [meromorphicPolarOrderAt] at h_pos ⊢
    norm_cast
    omega

/-- **A pole of order `> 1` in the canonical sense is a pole of order `> 1` for
`meromorphicOrderAt`** — the guard of condition (B)'s clauses. -/
theorem meromorphicOrderAt_lt_neg_one_of_one_lt_meromorphicPolarOrderAt {f : ℂ → ℂ} {s : ℂ}
    (h : 1 < meromorphicPolarOrderAt f s) :
    meromorphicOrderAt f s < (-1 : ℤ) := by
  rw [meromorphicOrderAt_eq_neg_of_meromorphicPolarOrderAt_pos (by omega)]
  exact_mod_cast WithTop.coe_lt_coe.mpr (by omega)

/-- The canonical polar order is at most `k` exactly when the meromorphic order is at least
`-k`. In particular, polar order `0` means the meromorphic order is nonnegative (analytic or
removable points). -/
@[simp]
theorem meromorphicPolarOrderAt_le_iff {f : ℂ → ℂ} {s : ℂ} {k : ℕ} :
    meromorphicPolarOrderAt f s ≤ k ↔
      ((-(k : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f s := by
  constructor
  · intro h
    have hneg : -(k : ℤ) ≤ -(meromorphicPolarOrderAt f s : ℤ) := by omega
    refine (WithTop.coe_le_coe.mpr hneg).trans ?_
    rw [WithTop.LinearOrderedAddCommGroup.coe_neg]
    exact neg_meromorphicPolarOrderAt_le f s
  · intro h
    by_contra hlt
    have hpos : 0 < meromorphicPolarOrderAt f s := by omega
    have heq := meromorphicOrderAt_eq_neg_of_meromorphicPolarOrderAt_pos hpos
    rw [heq, ← WithTop.LinearOrderedAddCommGroup.coe_neg, WithTop.coe_le_coe] at h
    omega

/-- The canonical polar order is at most one exactly when the meromorphic order is at least
`-1`. This includes analytic and removable points (polar order zero) as well as genuine simple
poles (polar order one). -/
theorem meromorphicPolarOrderAt_le_one_iff {f : ℂ → ℂ} {s : ℂ} :
    meromorphicPolarOrderAt f s ≤ 1 ↔
      ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f s := by
  simp

/-- Dividing a meromorphic function `f` whose meromorphic order at `s` is at least `m` by
`(z - s) ^ n` gives canonical polar order at most `n - m` at `s`. -/
theorem meromorphicPolarOrderAt_div_sub_pow_le {f : ℂ → ℂ} {s : ℂ} {m n : ℕ}
    (hf : MeromorphicAt f s) (hm : ((m : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f s) :
    meromorphicPolarOrderAt (fun z : ℂ ↦ f z / (z - s) ^ n) s ≤ n - m := by
  rw [meromorphicPolarOrderAt_le_iff]
  have hd : MeromorphicAt (fun z : ℂ ↦ (z - s) ^ n) s :=
    ((MeromorphicAt.id s).sub (.const s s)).pow n
  rw [fun_meromorphicOrderAt_div hf hd, fun_meromorphicOrderAt_pow_id_sub_const]
  cases hx : meromorphicOrderAt f s with
  | top => simp
  | coe j =>
    rw [hx] at hm
    have hmj : (m : ℤ) ≤ j := WithTop.coe_le_coe.mp hm
    norm_cast
    omega

/-- Dividing a meromorphic function `f` that tends to `0` along `𝓝[≠] s` (in particular, an
analytic function vanishing at `s`) by `(z - s) ^ n` lowers the canonical polar order at `s` to
at most `n - 1`. In particular, for `g` analytic at `s` with `g s = c`,
`z ↦ (g z - c) / (z - s) ^ (k + 1)` has polar order at most `k` at `s`. -/
theorem meromorphicPolarOrderAt_div_sub_pow_le_of_tendsto_zero {f : ℂ → ℂ} {s : ℂ} {n : ℕ}
    (hf : MeromorphicAt f s) (h0 : Tendsto f (𝓝[≠] s) (𝓝 0)) :
    meromorphicPolarOrderAt (fun z : ℂ ↦ f z / (z - s) ^ n) s ≤ n - 1 := by
  have hpos : (0 : WithTop ℤ) < meromorphicOrderAt f s :=
    (tendsto_zero_iff_meromorphicOrderAt_pos hf).mp h0
  refine meromorphicPolarOrderAt_div_sub_pow_le (m := 1) hf ?_
  cases hx : meromorphicOrderAt f s with
  | top => exact le_top
  | coe j =>
    rw [hx] at hpos
    have hj : (0 : ℤ) < j := WithTop.coe_lt_coe.mp hpos
    exact WithTop.coe_le_coe.mpr (by omega)

/-- Taylor decomposition of an analytic function to order `k`:
`g z = ∑ j < k, c j * (z - s)^j + (z - s)^k * R z` with `R` analytic at `s`. Mathlib's
`AnalyticAt.exists_eventuallyEq_sum_add_pow_mul` at the translate `g (· + s)`. -/
private theorem analyticAt_taylor_decomp {g : ℂ → ℂ} {s : ℂ} (hg : AnalyticAt ℂ g s) (k : ℕ) :
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
    (hg₀_an : AnalyticAt ℂ g₀ s) (hg₀_eq : ∀ᶠ z in 𝓝[≠] s, f z = (z - s) ^ (-(k : ℤ)) • g₀ z) :
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
  obtain ⟨g₀, hg₀_an, hg₀_eq⟩ :=
    exists_analyticAt_eventuallyEq_zpow_smul hMero (neg_meromorphicPolarOrderAt_le f s)
  exact laurent_data_of_zpow_factor _ hg₀_an hg₀_eq

/-- At a pole of order `m + 1`, the finite Laurent expansion has `m + 1` polar coefficients,
and its highest-order coefficient is the meromorphic trailing coefficient. -/
theorem exists_laurent_data_of_meromorphicOrderAt_eq_neg_succ {f : ℂ → ℂ} {s : ℂ} {m : ℕ}
    (hord : meromorphicOrderAt f s = (-(↑(m + 1) : ℤ) : WithTop ℤ)) :
    ∃ (c : Fin (m + 1) → ℂ) (g : ℂ → ℂ), AnalyticAt ℂ g s ∧
      (∀ᶠ z in 𝓝[≠] s, f z = g z + ∑ i, c i / (z - s) ^ (i.val + 1)) ∧
      c (Fin.last m) = meromorphicTrailingCoeffAt f s := by
  have hf : MeromorphicAt f s := meromorphicAt_of_meromorphicOrderAt_ne_zero fun hz ↦ by
    have h := congrArg WithTop.untop₀ (hz.symm.trans hord)
    simp only [WithTop.untop₀_zero, WithTop.untop₀_neg, WithTop.untop₀_coe] at h
    omega
  have hlen : meromorphicPolarOrderAt f s = m + 1 := by
    simp [meromorphicPolarOrderAt_eq_of_order_eq hord]
  obtain ⟨c, g, hg, heq⟩ := hlen ▸ exists_laurent_data_of_meromorphicAt hf
  refine ⟨c, g, hg, heq, ?_⟩
  let G (z : ℂ) := (z - s) ^ (m + 1) * g z + ∑ i, c i * (z - s) ^ (m - i.val)
  have hG : ContinuousAt G s := by
    refine (((continuousAt_id.sub continuousAt_const).pow _).mul hg.continuousAt).add ?_
    exact (continuous_finsetSum _ fun i _ ↦ by fun_prop).continuousAt
  have hGs : G s = c (Fin.last m) := by
    simp only [G, sub_self, zero_pow (Nat.succ_ne_zero m), zero_mul, zero_add,
      Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last, tsub_self, pow_zero, mul_one]
    have hz : (∑ i : Fin m, c i.castSucc * (0 : ℂ) ^ (m - i.val)) = 0 :=
      Finset.sum_eq_zero fun i _ ↦ by rw [zero_pow (by omega), mul_zero]
    rw [hz, zero_add]
  have hlim := hf.tendsto_nhds_meromorphicTrailingCoeffAt
  rw [hord, WithTop.untop₀_neg, WithTop.untop₀_coe, neg_neg, zpow_natCast] at hlim
  have hlim' : Tendsto ((· - s) ^ (m + 1) • f) (𝓝[≠] s) (𝓝 (G s)) := by
    refine hG.continuousWithinAt.tendsto.congr' ?_
    filter_upwards [heq, self_mem_nhdsWithin] with z hz (hzs : z ≠ s)
    simp only [G, Pi.smul_apply', Pi.pow_apply, smul_eq_mul, hz, mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hm : m + 1 = (i.val + 1) + (m - i.val) := by omega
    rw [congrArg (fun n : ℕ ↦ (z - s) ^ n) hm, pow_add]
    field_simp [pow_ne_zero _ (sub_ne_zero.mpr hzs)]
  exact hGs.symm.trans (tendsto_nhds_unique hlim' hlim)

/-- A negative meromorphic order is `-(m + 1)` for some `m : ℕ`: this is the form of the pole
order taken by `exists_laurent_data_of_meromorphicOrderAt_eq_neg_succ`. -/
theorem exists_meromorphicOrderAt_eq_neg_succ_of_lt_zero {𝕜 E : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : 𝕜 → E} {s : 𝕜}
    (h : meromorphicOrderAt f s < 0) :
    ∃ m : ℕ, meromorphicOrderAt f s = (-(↑(m + 1) : ℤ) : WithTop ℤ) := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp h.ne_top
  have hn' : n < 0 := WithTop.coe_lt_coe.mp (hn ▸ h)
  obtain ⟨m, rfl⟩ := Int.eq_negSucc_of_lt_zero hn'
  exact ⟨m, by simpa [Int.negSucc_eq] using hn.symm⟩

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
theorem meromorphicPolarPartAt_eq_sum {f : ℂ → ℂ} {s : ℂ} (hMero : MeromorphicAt f s) (z : ℂ) :
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

/-- Termwise derivative of a finite Laurent principal part
`w ↦ ∑ i : Fin m, a i / (w - s) ^ (i.val + 1)` at any point `z ≠ s`. -/
theorem hasDerivAt_sum_div_sub_pow {m : ℕ} (a : Fin m → ℂ) {s z : ℂ} (hz : z ≠ s) :
    HasDerivAt (fun w : ℂ ↦ ∑ i : Fin m, a i / (w - s) ^ (i.val + 1))
      (∑ i : Fin m, a i * (-((i.val + 1 : ℕ) : ℂ) / (z - s) ^ (i.val + 2))) z := by
  have hzs : z - s ≠ 0 := sub_ne_zero.mpr hz
  refine HasDerivAt.fun_sum fun i _ ↦ ?_
  have hp : HasDerivAt (fun w : ℂ ↦ (w - s) ^ (i.val + 1))
      (((i.val + 1 : ℕ) : ℂ) * (z - s) ^ i.val) z := by
    simpa only [add_tsub_cancel_right, mul_one, id_eq] using
      HasDerivAt.fun_pow ((hasDerivAt_id z).sub_const s) (i.val + 1)
  have hmul : HasDerivAt (fun w : ℂ ↦ a i / (w - s) ^ (i.val + 1))
      (a i * (-(((i.val + 1 : ℕ) : ℂ) * (z - s) ^ i.val) /
        ((z - s) ^ (i.val + 1)) ^ 2)) z := by
    simpa [div_eq_mul_inv] using (hp.inv (pow_ne_zero _ hzs)).const_mul (a i)
  refine hmul.congr_deriv (congrArg (a i * ·) ?_)
  have hsq : ((z - s) ^ (i.val + 1)) ^ 2 = (z - s) ^ (i.val + 2) * (z - s) ^ i.val := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  rw [hsq, neg_div, mul_div_mul_right _ _ (pow_ne_zero _ hzs), ← neg_div]

/-- Termwise derivative of the canonical polar part `meromorphicPolarPartAt hMero` away from its
pole `s`. -/
theorem hasDerivAt_meromorphicPolarPartAt {f : ℂ → ℂ} {s : ℂ} (hMero : MeromorphicAt f s)
    {z : ℂ} (hz : z ≠ s) :
    HasDerivAt (meromorphicPolarPartAt hMero)
      (∑ k : Fin (meromorphicPolarOrderAt f s),
        meromorphicPolarCoeffAt hMero k * (-((k.val + 1 : ℕ) : ℂ) / (z - s) ^ (k.val + 2))) z := by
  unfold meromorphicPolarPartAt
  exact hasDerivAt_sum_div_sub_pow (meromorphicPolarCoeffAt hMero) hz

/-- **The leading canonical Laurent coefficient is the residue.** -/
theorem meromorphicPolarCoeffAt_zero_eq_residue {f : ℂ → ℂ} {s : ℂ}
    (hMero : MeromorphicAt f s) (h_pos : 0 < meromorphicPolarOrderAt f s) :
    meromorphicPolarCoeffAt hMero ⟨0, h_pos⟩ = residue f s := by
  have hres := residue_of_laurent_expansion
    (exists_laurent_data_of_meromorphicAt hMero).choose_spec.choose_spec.1
    (exists_laurent_data_of_meromorphicAt hMero).choose_spec.choose_spec.2
  rw [dite_eq_left h_pos] at hres
  exact hres.symm

/-! ### Uniqueness of the Laurent coefficients

Any finite principal-part expansion of `f` at `s` with analytic remainder has the canonical
coefficients: the sector condition (B) of the generalized residue theorem carries its own
Laurent witness, and uniqueness is what lets its resonance constraints transfer to the
canonical polar data. Internally the coefficients are total functions `ℕ → ℂ` summed over
`Finset.range`, so expansions of different lengths compare after zero-padding. -/

/-- A finite principal part agreeing with a function continuous at `s` is zero: all its
coefficients vanish. It is the polynomial `∑ k < N, c k X ^ (k + 1)` in `(z - s)⁻¹`, which
`TauCeti.eq_zero_of_eval_inv_sub_eventuallyEq` shows to be zero. -/
private theorem laurent_coeff_eq_zero_of_eventuallyEq {s : ℂ} {g : ℂ → ℂ} (hg : ContinuousAt g s)
    {N : ℕ} {c : ℕ → ℂ}
    (h_eq : ∀ᶠ z in 𝓝[≠] s, ∑ k ∈ Finset.range N, c k / (z - s) ^ (k + 1) = g z) :
    ∀ k < N, c k = 0 := by
  have hP := eq_zero_of_eval_inv_sub_eventuallyEq
    (P := ∑ k ∈ Finset.range N, Polynomial.C (c k) * Polynomial.X ^ (k + 1)) (by simp) hg <| by
      filter_upwards [h_eq] with z hz
      simp [Polynomial.eval_finsetSum, ← hz, div_eq_mul_inv]
  intro k hk
  simpa [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, hk] using
    congrArg (·.coeff (k + 1)) hP

/-- A `Fin`-indexed principal-part sum as a `Finset.range` sum of its zero-padding, extended
to any length `L ≥ N`. -/
private theorem sum_fin_div_pow_eq_sum_range {s : ℂ} {N L : ℕ} (hNL : N ≤ L)
    (a : Fin N → ℂ) (z : ℂ) :
    ∑ k : Fin N, a k / (z - s) ^ (k.val + 1)
      = ∑ k ∈ Finset.range L,
        (if hk : k < N then a ⟨k, hk⟩ else 0) / (z - s) ^ (k + 1) := by
  have h₁ : ∑ k : Fin N, a k / (z - s) ^ (k.val + 1)
      = ∑ k ∈ Finset.range N,
        (if hk : k < N then a ⟨k, hk⟩ else 0) / (z - s) ^ (k + 1) := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun k _ => by rw [dite_eq_left k.isLt]
  rw [h₁]
  exact Finset.sum_subset
    (fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hNL))
    fun k _ hk => by
    rw [dite_eq_right (Finset.mem_range.not.mp hk), zero_div]

/-- **Uniqueness of finite principal-part expansions**: two expansions of the same function
near `s` with remainders continuous at `s` have the same coefficients, compared through
their zero-paddings. -/
theorem laurent_coeff_unique {s : ℂ} {N M : ℕ} {a : Fin N → ℂ} {b : Fin M → ℂ}
    {g h : ℂ → ℂ} (hg : ContinuousAt g s) (hh : ContinuousAt h s) (h_eq : ∀ᶠ z in 𝓝[≠] s,
      g z + ∑ k : Fin N, a k / (z - s) ^ (k.val + 1)
        = h z + ∑ k : Fin M, b k / (z - s) ^ (k.val + 1)) (k : ℕ) :
    (if hk : k < N then a ⟨k, hk⟩ else 0) = (if hk : k < M then b ⟨k, hk⟩ else 0) := by
  rcases lt_or_ge k (max N M) with hk_lt | hk_ge
  · have h_diff : ∀ᶠ z in 𝓝[≠] s,
        ∑ j ∈ Finset.range (max N M),
          ((if hj : j < N then a ⟨j, hj⟩ else 0) - (if hj : j < M then b ⟨j, hj⟩ else 0))
            / (z - s) ^ (j + 1)
          = h z - g z := by
      filter_upwards [h_eq] with z hz
      rw [sum_fin_div_pow_eq_sum_range (le_max_left N M) a z,
        sum_fin_div_pow_eq_sum_range (le_max_right N M) b z] at hz
      rw [Finset.sum_congr rfl fun j _ =>
        sub_div (if hj : j < N then a ⟨j, hj⟩ else 0)
          (if hj : j < M then b ⟨j, hj⟩ else 0) ((z - s) ^ (j + 1)),
        Finset.sum_sub_distrib]
      linear_combination hz
    exact sub_eq_zero.mp
      (laurent_coeff_eq_zero_of_eventuallyEq (hh.sub hg) h_diff k hk_lt)
  · rw [dite_eq_right (by omega : ¬ k < N), dite_eq_right (by omega : ¬ k < M)]

/-- **Any Laurent witness has the canonical coefficients**: an eventual finite principal-part
expansion of a meromorphic `f` at `s` with remainder continuous at `s` agrees, coefficient by
coefficient through zero-padding, with the canonical polar data. This is what transfers the
sector condition (B)'s resonance constraints from its own Laurent witness to
`meromorphicPolarCoeffAt`. -/
theorem laurent_coeff_eq_meromorphicPolarCoeffAt {f : ℂ → ℂ} {s : ℂ}
    (hMero : MeromorphicAt f s) {N : ℕ} {a : Fin N → ℂ} {g : ℂ → ℂ} (hg : ContinuousAt g s)
    (h_eq : ∀ᶠ z in 𝓝[≠] s, f z = g z + ∑ k : Fin N, a k / (z - s) ^ (k.val + 1)) (k : ℕ) :
    (if hk : k < N then a ⟨k, hk⟩ else 0)
      = (if hk : k < meromorphicPolarOrderAt f s then
          meromorphicPolarCoeffAt hMero ⟨k, hk⟩ else 0) := by
  refine laurent_coeff_unique hg
    (meromorphicAnalyticPartAt_analyticAt hMero).continuousAt ?_ k
  filter_upwards [h_eq, eventuallyEq_meromorphicAnalyticPartAt_add_meromorphicPolarPartAt
    hMero] with z hz hz'
  rw [← hz, hz', meromorphicPolarPartAt_eq_sum]

end TauCeti.Contour

end
