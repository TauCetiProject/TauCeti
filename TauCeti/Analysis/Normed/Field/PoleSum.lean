/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Topology.Algebra.Monoid

/-!
# Finite sums of poles that extend continuously vanish

Let `𝕜` be a nontrivially normed field. A finite sum of pole terms

`S(w) = ∑ i, c i / (w - p i) ^ (e i + 1)`,

with pairwise distinct pairs `(p i, e i)` of a pole `p i` and an order `e i + 1`, can agree off its
poles with a function continuous at the poles only when every coefficient `c i` vanishes
(`TauCeti.eq_zero_of_sum_div_sub_pow_eq`). Indeed, if some coefficient at a pole `a` is nonzero,
take one of highest order `e i₀ + 1` there: multiplying by `(w - a) ^ (e i₀ + 1)` and letting
`w → a`, the sum tends to `c i₀`, since every other term tends to zero
(`TauCeti.tendsto_sub_pow_mul_div_sub_pow`), while the continuous function times
`(w - a) ^ (e i₀ + 1)` tends to zero.

This is the uniqueness of the principal parts of a function at finitely many points, stated without
any holomorphy: the remainder is only required to be continuous at the poles. It is used to show
that kernel elements of the linearized vortex operator with independent prescribed principal parts
are linearly independent.
-/

public section

open Filter Topology

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [Fintype ι]

/-- **A pole of lower order is killed by a power of `w - a`.** For `M ≥ 1`, the pole term
`c / (w - b) ^ (n + 1)` times `(w - a) ^ M` tends to zero as `w → a`, `w ≠ a`, unless `b = a` and
the order `n + 1` is at least `M`. -/
theorem tendsto_sub_pow_mul_div_sub_pow {a b c : 𝕜} {n M : ℕ} (hM : M ≠ 0)
    (h : b = a → n + 1 < M) :
    Tendsto (fun w ↦ (w - a) ^ M * (c / (w - b) ^ (n + 1))) (𝓝[≠] a) (𝓝 0) := by
  by_cases hb : b = a
  · subst hb
    have hlt := h rfl
    have hlim := (by fun_prop : Continuous fun w : 𝕜 ↦ c * (w - b) ^ (M - (n + 1))).tendsto b
    rw [sub_self, zero_pow (by omega), mul_zero] at hlim
    refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hw₀ : w - b ≠ 0 := sub_ne_zero.2 hw
    rw [← Nat.sub_add_cancel hlt.le, pow_add, Nat.add_sub_cancel]
    field_simp
  · have hcont : ContinuousAt (fun w ↦ (w - a) ^ M * (c / (w - b) ^ (n + 1))) a :=
      by fun_prop (disch := exact pow_ne_zero _ (sub_ne_zero.2 (Ne.symm hb)))
    have hlim := hcont.tendsto
    rw [sub_self, zero_pow hM, zero_mul] at hlim
    exact hlim.mono_left nhdsWithin_le_nhds

/-- **Finite sums of poles that extend continuously vanish.** Let `(p i, e i)` be pairwise
distinct pairs of a point `p i` of `𝕜` and a natural number `e i`. If the sum of the pole terms
`c i / (w - p i) ^ (e i + 1)` agrees, off the points `p i`, with a function `g` continuous at the
points `p i`, then every coefficient `c i` is zero. -/
theorem eq_zero_of_sum_div_sub_pow_eq {p : ι → 𝕜} {e : ι → ℕ}
    (hpe : Function.Injective fun i ↦ (p i, e i)) {c : ι → 𝕜} {g : 𝕜 → 𝕜}
    (hg : ∀ i, ContinuousAt g (p i))
    (h : ∀ w ∉ Set.range p, ∑ i, c i / (w - p i) ^ (e i + 1) = g w) : c = 0 := by
  classical
  by_contra hc
  obtain ⟨i₁, hi₁⟩ := Function.ne_iff.1 hc
  set a := p i₁ with ha
  -- A coefficient of highest order among the nonzero coefficients at the pole `a`.
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun i ↦ p i = a ∧ c i ≠ 0) e
    ⟨i₁, Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl, hi₁⟩⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi₀ hmax
  obtain ⟨hpi₀, hci₀⟩ := hi₀
  -- Every pole term times `(w - a) ^ (e i₀ + 1)` has a limit at `a`: `c i₀` for `i₀`, zero
  -- otherwise.
  have hterm (i : ι) : Tendsto (fun w ↦ (w - a) ^ (e i₀ + 1) * (c i / (w - p i) ^ (e i + 1)))
      (𝓝[≠] a) (𝓝 (if i = i₀ then c i₀ else 0)) := by
    by_cases hii₀ : i = i₀
    · subst hii₀
      simp only [↓reduceIte]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with w hw
      rw [hpi₀, mul_div_cancel₀ _ (pow_ne_zero _ (sub_ne_zero.2 hw))]
    simp only [hii₀, ↓reduceIte]
    by_cases hci : c i = 0
    · simp [hci]
    -- A nonzero coefficient at `a` other than `i₀` has lower order.
    refine tendsto_sub_pow_mul_div_sub_pow (Nat.succ_ne_zero _) fun hpi ↦ ?_
    have hlt : e i < e i₀ := lt_of_le_of_ne (hmax i ⟨hpi, hci⟩) fun he ↦
      hii₀ (hpe (by simp [hpi, hpi₀, he]))
    omega
  have hsum := tendsto_finsetSum Finset.univ fun i _ ↦ hterm i
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hsum
  -- Near `a`, the sum of the pole terms is `g`, so the same product tends to zero.
  have hfin : (Set.range p \ {a}).Finite := (Set.finite_range p).sdiff
  have hev : ∀ᶠ w in 𝓝[≠] a, w ∉ Set.range p := by
    filter_upwards [nhdsWithin_le_nhds (hfin.isClosed.isOpen_compl.mem_nhds fun h ↦ h.2 rfl),
      self_mem_nhdsWithin] with w hw hwa
    exact fun hwp ↦ hw ⟨hwp, hwa⟩
  have hg₀ : Tendsto (fun w ↦ (w - a) ^ (e i₀ + 1) * g w) (𝓝[≠] a) (𝓝 0) := by
    have := hg i₁
    rw [← ha] at this
    have hlim := (by fun_prop : ContinuousAt (fun w ↦ (w - a) ^ (e i₀ + 1) * g w) a).tendsto
    rw [sub_self, zero_pow (Nat.succ_ne_zero _), zero_mul] at hlim
    exact hlim.mono_left nhdsWithin_le_nhds
  refine hci₀ (tendsto_nhds_unique (hsum.congr' ?_) hg₀)
  filter_upwards [hev] with w hw
  rw [← h w hw, Finset.mul_sum]

end TauCeti
