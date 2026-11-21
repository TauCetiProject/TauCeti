/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import TauCeti.Analysis.ExteriorPower.WedgeForms
public import TauCeti.NumberTheory.DiophantineApproximation.Subspace.Span
public import TauCeti.NumberTheory.DiophantineApproximation.Subspace.SuccessiveMinima

import TauCeti.Analysis.SpecialFunctions.Log.Base
import TauCeti.LinearAlgebra.Span.Basic
import TauCeti.NumberTheory.DiophantineApproximation.Subspace.Balance
import TauCeti.NumberTheory.NumberField.Global.Approximation.Evertse
import TauCeti.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# Wedge domains of an approximation domain

Let `x 0, …, x (N - 1)` be linearly independent vectors of an approximation domain
`approxDomain S₀ L c Q` of `K^ι`, `N = card ι`, with `x l` in the dilate by `μ l` at the infinite
places, for positive nondecreasing `μ`; typically `x` realizes the successive minima `μ` over `K`.
Schmidt's argument passes to the `p`-th exterior power, read in Plücker coordinates
`Set.powersetCard ι p → K`, where it looks for an approximation domain of the wedge forms
`wedgeForms (L v) p` containing many Plücker vectors and of controlled weight. This is the domain
the book calls `S(Q)`.

Evertse's lemma (`NumberField.exists_evertse`) with weights `Q ^ c v i` corrects `x`
triangularly to vectors `y` and attaches to every place a bijection `σ v` between the indices of
the minima and the forms, such that `|L v (σ v i) (y j)|_v ≤ C₀ · Q ^ c v (σ v i) · min (μ i) (μ j)`
at the infinite places and `|L v i (y j)|_v ≤ Q ^ c v i` at the places of `S₀`. Passing to
determinants (`AbsoluteValue.apply_wedgeForms_plucker_le`), the Plücker vector of `y J`, for a
`p`-subset `J` meeting the first `k` indices, satisfies at an infinite place `v` the bound
`C · Q ^ (∑ t ∈ T, c v t) · g v T` for each wedge form `T`, where `g v T = wedgeGain k μ (σ v) T`
is the product of the `μ (σ v⁻¹ t)` over `t ∈ T`, times the gain `μ (k - 1) / μ k` when `T` lies
in the top block of `σ v`. The constant and the gain are absorbed into the exponent:
`wedgeExponent c p k σ μ C Q` is `∑ t ∈ T, c v t + logb Q (C · g v T)` at the archimedean
absolute values and `∑ t ∈ T, c v t` at the nonarchimedean ones, where no constant and no gain
occur. Then, for `0 < Q` and `Q ≠ 1` (so that `logb Q` inverts `Q ^ ·`), these Plücker vectors
lie in `approxDomain S₀ (fun v ↦ wedgeForms (L v) p) (wedgeExponent c p k σ μ C Q) Q`
(`TauCeti.NumberField.exists_plucker_mem_approxDomain_wedgeForms`), with `C` depending only on
`K` and `ι`.

The weight of the wedge exponents is exact. For `0 < p`, each index lies in
`e = (N - 1).choose (p - 1)` of the `p`-subsets, and if also `k + p = N`, exactly one subset is
the top block. So, for `0 < p` and `k + p = N`, when `C` and the minima `μ l`, `l < N`, are
nonzero, `approxWeight S₀ (wedgeExponent …)` is `e · approxWeight S₀ c` plus `[K : ℚ]` times
`logb Q (C ^ M · (∏ l, μ l) ^ e · μ (k - 1) / μ k)`, with `M = N.choose p`
(`TauCeti.NumberField.approxWeight_wedgeExponent`); this additive identity needs no condition on
`Q`. When `μ` are the successive minima, `0 < p`, `k + p = N`, `0 < Q`, `Q ≠ 1` and `0 < C`,
Minkowski's second theorem bounds `Q ^ approxWeight S₀ c · ∏ l, μ l ^ [K : ℚ]` by a constant, so
`Q ^ approxWeight` of the wedge exponents is at most a constant times
`(μ (k - 1) / μ k) ^ [K : ℚ]` (`TauCeti.NumberField.rpow_approxWeight_wedgeExponent_le`): a
large jump between consecutive minima makes the wedge domain small.

The exponents above carry a bijection at every infinite place, because the minima enter every
infinite place. `TauCeti.NumberField.exists_balance` first moves the minima of a minimal family to
one infinite place `w₀`: the local factors become `C₂ · μ l ^ (d / mult w₀)` at `w₀`, `d = [K : ℚ]`,
and `C₂` at the other infinite places, for a constant `C₂ ≥ 1` depending only on `K`. Then only the
bijection at `w₀` matters: there is `C`, depending only on `K` and `ι`, such that, for `0 < Q` and
`Q ≠ 1`, the Plücker vectors of the corrected family indexed by `p`-subsets meeting the first `k`
indices lie in the approximation domain of the wedge forms with the exponents
`wedgeExponentAt c p k w₀ σ μ C Q`, which are `∑ t ∈ T, c v t + logb Q C` at the archimedean
`v ≠ w₀` and carry the minima, raised to `d / mult w₀`, at `w₀` alone
(`TauCeti.NumberField.exists_plucker_mem_approxDomain_wedgeExponentAt`). The corrected family still
spans `V(Q)` by its first `finrank K V(Q)` members. For `0 < p` and positive minima `μ l`, `l < N`,
moving the minima does not change the weight, since `mult w₀ · (d / mult w₀) = d` is the total
multiplicity of the infinite places (`TauCeti.NumberField.approxWeight_wedgeExponentAt`), so the
same jump bound holds for `0 < p`, `k + p = N`, `0 < Q`, `Q ≠ 1` and `0 < C`
(`TauCeti.NumberField.rpow_approxWeight_wedgeExponentAt_le`). When `μ k ≠ 0`, on a set of forms in
the top block containing the form `σ k`, in particular on the top block itself for `0 < p` and
`k + p = card ι`, the gain cancels the minimum `μ k`, so the minima attached to it are a product
with `μ k` replaced by `μ (k - 1)` (`TauCeti.wedgeGain_eq_prod_update`).

## Main definitions

* `TauCeti.NumberField.wedgeExponent`: the exponents of the wedge domain `S(Q)`.
* `TauCeti.NumberField.wedgeExponentAt`: the exponents of the wedge domain with the minima at one
  infinite place.

## Main results

* `TauCeti.NumberField.exists_plucker_mem_approxDomain_wedgeForms`: for `0 < Q` and `Q ≠ 1`, the
  Plücker vectors of the corrected minimal vectors indexed by `p`-subsets meeting the first `k`
  indices lie in the wedge domain.
* `TauCeti.NumberField.approxWeight_wedgeExponent` and
  `TauCeti.NumberField.rpow_approxWeight_wedgeExponent`: for `0 < p`, `k + p = card ι` and a
  nonzero constant and minima, the exact weight of the wedge domain; for the power, the constant
  and the minima are positive, `0 < Q` and `Q ≠ 1`.
* `TauCeti.NumberField.rpow_approxWeight_wedgeExponent_le`: for the successive minima, `0 < p`,
  `k + p = card ι`, `0 < C`, `0 < Q` and `Q ≠ 1`, `Q` raised to the weight of the wedge domain is at
  most a constant times `(μ (k - 1) / μ k) ^ [K : ℚ]`.
* `TauCeti.NumberField.exists_plucker_mem_approxDomain_wedgeExponentAt`: with the minima at one
  infinite place and for `0 < Q` and `Q ≠ 1`, the Plücker vectors of a corrected minimal family
  indexed by `p`-subsets meeting the first `k` indices lie in the wedge domain at that place.
* `TauCeti.NumberField.approxWeight_wedgeExponentAt`: for `0 < p` and positive minima, its weight
  is that of the wedge domain `wedgeExponent` with one bijection.
* `TauCeti.NumberField.rpow_approxWeight_wedgeExponentAt_le`: for the successive minima, `0 < p`,
  `k + p = card ι`, `0 < C`, `0 < Q` and `Q ≠ 1`, `Q` raised to its weight is at most a constant
  times `(μ (k - 1) / μ k) ^ [K : ℚ]`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  7.5.30, (7.42)–(7.45), and Lemma 7.5.31.
* J.-H. Evertse, *An improvement of the quantitative Subspace theorem*, Compositio Math. 101
  (1996), 225–311.
* J.-H. Evertse and H. P. Schlickewei, *A quantitative version of the absolute subspace theorem*,
  J. reine angew. Math. 548 (2002), 21–127, §9.
-/

public section

noncomputable section

open Finset Module NumberField NumberField.mixedEmbedding Set.powersetCard

namespace TauCeti.NumberField

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι]

open scoped Classical in
/-- **The exponents of the wedge domain** `S(Q)` (Bombieri–Gubler 7.5.30). Given exponents `c`,
an exterior degree `p`, a jump index `k`, bijections `σ v` from the indices of the minima to the
forms, minima `μ` and a constant `C`, the exponent of the wedge form `T` at `v` is
`∑ t ∈ T, c v t` at a nonarchimedean `v` and, at an archimedean `v`,
`∑ t ∈ T, c v t + logb Q (C · g)`, where `g = wedgeGain k μ (σ v) T` is the product of the
`μ ((σ v).symm t)` over `t ∈ T`, multiplied by `μ (k - 1) / μ k` when every `(σ v).symm t` is at
least `k`. -/
def wedgeExponent (c : AbsoluteValue K ℝ → ι → ℝ) (p k : ℕ)
    (σ : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι) (μ : ℕ → ℝ) (C Q : ℝ) :
    AbsoluteValue K ℝ → Set.powersetCard ι p → ℝ :=
  fun v T ↦ ∑ t ∈ (T : Finset ι), c v t +
    if IsNonarchimedean v then 0 else
      Real.logb Q (C * wedgeGain k μ (σ v) T)

open scoped Classical in
/-- The wedge exponent of `T` at `v`, before deciding whether `v` is archimedean. -/
theorem wedgeExponent_def (c : AbsoluteValue K ℝ → ι → ℝ) (p k : ℕ)
    (σ : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι) (μ : ℕ → ℝ) (C Q : ℝ)
    (v : AbsoluteValue K ℝ) (T : Set.powersetCard ι p) :
    wedgeExponent c p k σ μ C Q v T = ∑ t ∈ (T : Finset ι), c v t +
      if IsNonarchimedean v then 0 else Real.logb Q (C * wedgeGain k μ (σ v) T) :=
  (rfl)

variable {c : AbsoluteValue K ℝ → ι → ℝ} {p k : ℕ}
  {σ : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι} {μ : ℕ → ℝ} {C Q : ℝ}
  {v : AbsoluteValue K ℝ}

/-- At a nonarchimedean absolute value the wedge exponent of `T` is `∑ t ∈ T, c v t`. -/
@[simp]
theorem wedgeExponent_of_isNonarchimedean (hv : IsNonarchimedean v) (T : Set.powersetCard ι p) :
    wedgeExponent c p k σ μ C Q v T = ∑ t ∈ (T : Finset ι), c v t := by
  simp [wedgeExponent_def, hv]

/-- At an archimedean absolute value the wedge exponent of `T` is `∑ t ∈ T, c v t` plus the
logarithm to base `Q` of the constant times the product of the minima attached to `T`, with the
gain `μ (k - 1) / μ k` when `T` lies in the top block. -/
@[simp]
theorem wedgeExponent_of_not_isNonarchimedean (hv : ¬IsNonarchimedean v)
    (T : Set.powersetCard ι p) :
    wedgeExponent c p k σ μ C Q v T = ∑ t ∈ (T : Finset ι), c v t +
      Real.logb Q (C * wedgeGain k μ (σ v) T) := by
  simp [wedgeExponent_def, hv]

/-- For `0 < p`, the wedge exponents depend only on the minima `μ l`, `l < card ι`. -/
theorem wedgeExponent_congr (hp : 0 < p) {μ' : ℕ → ℝ} (h : ∀ l < Fintype.card ι, μ l = μ' l) :
    wedgeExponent c p k σ μ C Q = wedgeExponent c p k σ μ' C Q := by
  ext v T
  rw [wedgeExponent_def, wedgeExponent_def,
    wedgeGain_congr h (σ v) (card_pos.1 (by rw [card_eq T]; exact hp))]

/-- At an archimedean absolute value, for `0 < Q ≠ 1`, `0 < C`, `0 < p` and positive minima
`μ l`, `l < card ι`, `Q` raised to the wedge exponent of `T` is the constant times the product of
the minima attached to `T` (with the gain on the top block) times the product of the bounds
`Q ^ c v t` over `t ∈ T`. -/
theorem rpow_wedgeExponent_of_not_isNonarchimedean (hv : ¬IsNonarchimedean v) (hQ : 0 < Q)
    (hQ₁ : Q ≠ 1) (hC : 0 < C) (hμ : ∀ l < Fintype.card ι, 0 < μ l) (hp : 0 < p)
    (T : Set.powersetCard ι p) :
    Q ^ wedgeExponent c p k σ μ C Q v T =
      C * wedgeGain k μ (σ v) T * ∏ t ∈ (T : Finset ι), Q ^ c v t := by
  have hT : (T : Finset ι).Nonempty := card_pos.1 (by rw [card_eq]; exact hp)
  rw [wedgeExponent_of_not_isNonarchimedean hv,
    Real.rpow_sum_add_logb hQ hQ₁ (mul_pos hC (wedgeGain_pos hμ (σ v) hT))]

/-! ### The Plücker vectors of the corrected minimal vectors -/

variable [NumberField K]

/-- **Evertse's lemma for a basis of an approximation module.** There is `C₁ ≥ 0`, depending only
on `K` and `ι`, such that linearly independent vectors `x l` of `approxModule S₀ L c Q`, `0 < Q`,
with `|L v i (x l)|_v ≤ μ v l · Q ^ c v i` at the infinite places, for minima `μ v` that are
nondecreasing at each infinite place `v`, have triangular corrections `y j`, integral outside `S₀`,
and bijections `σ v` with `|L v (σ v i) (y j)|_v ≤ C₁ · Q ^ c v (σ v i) · min (μ v i) (μ v j)` at
the infinite places and `|L v i (y j)|_v ≤ Q ^ c v i` at the places of `S₀`. -/
private theorem exists_evertse_approxModule :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ (S₀ : Finset (FinitePlace K))
      (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) (c : AbsoluteValue K ℝ → ι → ℝ) (Q : ℝ)
      (x : Fin (Fintype.card ι) → ι → K) (μ : AbsoluteValue K ℝ → ℕ → ℝ),
      (∀ v : InfinitePlace K, LinearIndependent K (L v.val)) →
      (∀ v ∈ S₀, LinearIndependent K (L v.val)) → 0 < Q → LinearIndependent K x →
      (∀ v : InfinitePlace K, MonotoneOn (μ v.val) (Set.Iio (Fintype.card ι))) →
      (∀ (v : InfinitePlace K), ∀ l < Fintype.card ι, 0 < μ v.val l) →
      (∀ l, x l ∈ approxModule S₀ L c Q) →
      (∀ (v : InfinitePlace K) (i : ι) (l : Fin (Fintype.card ι)),
        v (L v.val i (x l)) ≤ μ v.val l * Q ^ c v.val i) →
      ∃ (y : Fin (Fintype.card ι) → ι → K) (σ : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι),
        (∀ j, y j - x j ∈ Submodule.span K (x '' Set.Iio j)) ∧
        (∀ v : FinitePlace K, v ∉ S₀ → ∀ j i, v (y j i) ≤ 1) ∧
        (∀ (v : InfinitePlace K) i j, v (L v.val (σ v.val i) (y j)) ≤
          C₁ * Q ^ c v.val (σ v.val i) * min (μ v.val i) (μ v.val j)) ∧
        ∀ v ∈ S₀, ∀ i j, v (L v.val i (y j)) ≤ Q ^ c v.val i := by
  classical
  set N := Fintype.card ι
  obtain ⟨C₀, hC₀⟩ := exists_evertse (K := K) N
  refine ⟨max 0 C₀, le_max_left _ _, ?_⟩
  intro S₀ L c Q x μ hLinf hLfin hQ₀ hx hμm hμp hxΛ hxinf
  have hna (v : FinitePlace K) : IsNonarchimedean v.val := v.add_le
  have hxΛ' (l : Fin N) := mem_approxModule.1 (hxΛ l)
  -- Evertse's lemma with the forms indexed by `Fin N`, weights `Q ^ c v i`, and minima `μ v` at
  -- the infinite places and `1` at the places of `S₀`.
  let e : Fin N ≃ ι := (Fintype.equivFin ι).symm
  let b : Basis (Fin N) K (ι → K) :=
    basisOfLinearIndependentOfCardEqFinrank' x hx (by simp [N])
  have hb : ⇑b = x := coe_basisOfLinearIndependentOfCardEqFinrank' x hx _
  let μ' : AbsoluteValue K ℝ → Fin N → ℝ := fun v j ↦ if IsNonarchimedean v then 1 else μ v j
  obtain ⟨ξ, π, hξ, hinf, hfin⟩ := hC₀ (ι → K) S₀ (fun v m ↦ L v (e m)) b
    (fun v m ↦ Q ^ c v (e m)) μ' (fun v ↦ (hLinf v).comp e e.injective)
    (fun v hv ↦ (hLfin v hv).comp e e.injective) (fun _ _ ↦ Real.rpow_pos_of_pos hQ₀ _)
    (fun _ _ _ ↦ Real.rpow_pos_of_pos hQ₀ _)
    (fun v i j hij ↦ by
      simpa [μ', v.not_isNonarchimedean] using hμm v i.isLt j.isLt (Fin.le_iff_val_le_val.1 hij))
    (fun v _ ↦ by simp [μ', hna v, monotone_const])
    (fun v m j ↦ by
      simp only [μ', v.not_isNonarchimedean, ↓reduceIte, hb]
      exact (hxinf v (e m) j).trans_eq (mul_comm _ _))
    (fun v hv m j ↦ by
      simpa [μ', hna v, hb, abs_of_pos hQ₀] using (hxΛ' j).1 v hv (e m))
  simp only [hb] at hinf hfin
  refine ⟨fun j ↦ x j + ∑ l ∈ univ.filter (· < j), ξ j l • x l, fun v ↦ (π v).trans e,
    fun j ↦ ?_, fun v hv j i ↦ ?_, fun w i j ↦ ?_, fun v hv i j ↦ ?_⟩
  · rw [add_sub_cancel_left]
    exact Submodule.sum_mem _ fun l hl ↦ Submodule.smul_mem _ _
      (Submodule.subset_span ⟨l, (mem_filter.1 hl).2, rfl⟩)
  · -- The corrections are integral outside `S₀`.
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine (v.add_le _ _).trans (max_le ((hxΛ' j).2 v hv i) (sum_induction _ (fun z ↦ v z ≤ 1)
      (fun a b ha hb ↦ (v.add_le a b).trans (max_le ha hb)) (by simp) fun l _ ↦ ?_))
    rw [map_mul]
    exact (mul_le_of_le_one_left (apply_nonneg _ _) (hξ j l v hv)).trans ((hxΛ' l).2 v hv i)
  · have h := hinf w i j
    simp only [μ', w.not_isNonarchimedean, ↓reduceIte] at h
    calc _ ≤ C₀ * (Q ^ c w.val (e (π w.val i)) * min (μ w.val i) (μ w.val j)) := h
      _ ≤ max 0 C₀ * (Q ^ c w.val (e (π w.val i)) * min (μ w.val i) (μ w.val j)) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_nonneg
          (Real.rpow_pos_of_pos hQ₀ _).le (le_min (hμp w _ i.isLt).le (hμp w _ j.isLt).le))
      _ = _ := by rw [Equiv.trans_apply, mul_assoc]
  · have h := hfin v hv ((π v.val).symm (e.symm i)) j
    simp only [μ', hna v, ↓reduceIte, min_self, mul_one, Equiv.apply_symm_apply] at h
    exact h

/-- The Plücker vectors of a corrected family, as produced by `exists_evertse_approxModule` with
minima `μ v` at the infinite places, lie in the approximation domain of the wedge forms for any
exponents `E` that are the sums `∑ t ∈ T, c v t` at the places of `S₀` and that dominate the
wedge bounds at the infinite places. -/
private theorem plucker_mem_approxDomain_wedgeForms [LinearOrder ι] {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)} {c : AbsoluteValue K ℝ → ι → ℝ} {Q : ℝ}
    (hQ : 0 < Q) {y : Fin (Fintype.card ι) → ι → K}
    {σ : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι} {μ : AbsoluteValue K ℝ → ℕ → ℝ} {C₁ : ℝ}
    (hC₁ : 0 ≤ C₁) (hμm : ∀ v : InfinitePlace K, MonotoneOn (μ v.val) (Set.Iio (Fintype.card ι)))
    (hμp : ∀ (v : InfinitePlace K), ∀ l < Fintype.card ι, 0 < μ v.val l)
    (hint : ∀ v : FinitePlace K, v ∉ S₀ → ∀ j i, v (y j i) ≤ 1)
    (hinf : ∀ (v : InfinitePlace K) i j, v (L v.val (σ v.val i) (y j)) ≤
      C₁ * Q ^ c v.val (σ v.val i) * min (μ v.val i) (μ v.val j))
    (hfin : ∀ v ∈ S₀, ∀ i j, v (L v.val i (y j)) ≤ Q ^ c v.val i) {k p : ℕ}
    {E : AbsoluteValue K ℝ → Set.powersetCard ι p → ℝ}
    (hEinf : ∀ (v : InfinitePlace K) (T : Set.powersetCard ι p),
      (Fintype.card ι).factorial * max 1 C₁ ^ Fintype.card ι *
        ((∏ t ∈ (T : Finset ι), Q ^ c v.val t) * wedgeGain k (μ v.val) (σ v.val) T) ≤
          Q ^ E v.val T)
    (hEfin : ∀ v ∈ S₀, ∀ T : Set.powersetCard ι p, E v.val T = ∑ t ∈ (T : Finset ι), c v.val t)
    {J : Set.powersetCard (Fin (Fintype.card ι)) p} (hJ : ∃ j ∈ J, (j : ℕ) < k) :
    plucker (y ∘ ofFinEmbEquiv.symm J) ∈ approxDomain S₀ (fun v ↦ wedgeForms (L v) p) E Q := by
  have hna (v : FinitePlace K) : IsNonarchimedean v.val := v.add_le
  rw [mem_approxDomain]
  refine ⟨fun w T ↦ ?_, fun v hv T ↦ ?_, fun v hv s ↦ ?_⟩
  · -- At an infinite place: the refined determinant bound, with the gain on the top block.
    exact (AbsoluteValue.apply_wedgeForms_plucker_le w.val (L w.val) (σ w.val) (hμm w) (hμp w)
      (ν := fun t ↦ Q ^ c w.val t) (fun _ ↦ (Real.rpow_pos_of_pos hQ _).le) hC₁ (hinf w) J hJ
      T).trans (hEinf w T)
  · -- At a place of `S₀`: the wedge of row bounds, with no constant.
    rw [hEfin v hv T, Real.rpow_sum_of_pos hQ]
    exact AbsoluteValue.apply_wedgeForms_plucker_le_prod v.val (hna v) (L v.val) _
      (fun i j ↦ hfin v hv i _) T
  · -- Outside `S₀`: a minor of a matrix of integral entries is integral.
    rw [plucker_apply]
    exact Matrix.abv_det_le_one_of_isNonarchimedean (hna v) fun _ _ ↦ hint v hv _ _

/-- **The Plücker vectors of the corrected minimal vectors lie in the wedge domain**
(Bombieri–Gubler 7.5.30, (7.44)–(7.45)). There is `C > 0`, depending only on `K` and `ι`, with
the following property. Let the forms `L v` be linearly independent at the infinite places and at
`S₀`, let `0 < Q ≠ 1`, and let `x 0, …, x (card ι - 1)` be linearly independent vectors of
`approxModule S₀ L c Q` with `|L v i (x l)|_v ≤ μ l · Q ^ c v i` at every infinite place, for
positive nondecreasing `μ`. Then there are vectors `y` with `y j - x j` in the span of the `x l`
with `l < j`, and bijections `σ v` from the indices of the minima to the forms, such that for
every `k` and every `p`-subset `J` meeting `{0, …, k - 1}`, the Plücker vector of the `y j`,
`j ∈ J`, lies in the approximation domain of the wedge forms with the wedge exponents. -/
theorem exists_plucker_mem_approxDomain_wedgeForms [LinearOrder ι] :
    ∃ C : ℝ, 0 < C ∧ ∀ (S₀ : Finset (FinitePlace K)) (L : AbsoluteValue K ℝ → ι → Dual K (ι → K))
      (c : AbsoluteValue K ℝ → ι → ℝ) (Q : ℝ) (x : Fin (Fintype.card ι) → ι → K) (μ : ℕ → ℝ),
      (∀ v : InfinitePlace K, LinearIndependent K (L v.val)) →
      (∀ v ∈ S₀, LinearIndependent K (L v.val)) → 0 < Q → Q ≠ 1 → LinearIndependent K x →
      MonotoneOn μ (Set.Iio (Fintype.card ι)) → (∀ l < Fintype.card ι, 0 < μ l) →
      (∀ l, x l ∈ approxModule S₀ L c Q) →
      (∀ (v : InfinitePlace K) (i : ι) (l : Fin (Fintype.card ι)),
        v (L v.val i (x l)) ≤ μ l * Q ^ c v.val i) →
      ∃ (y : Fin (Fintype.card ι) → ι → K) (σ : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι),
        (∀ j, y j - x j ∈ Submodule.span K (x '' Set.Iio j)) ∧
        ∀ (k p : ℕ) (J : Set.powersetCard (Fin (Fintype.card ι)) p), (∃ j ∈ J, (j : ℕ) < k) →
          plucker (y ∘ ofFinEmbEquiv.symm J) ∈
            approxDomain S₀ (fun v ↦ wedgeForms (L v) p) (wedgeExponent c p k σ μ C Q) Q := by
  obtain ⟨C₁, hC₁, hE⟩ := exists_evertse_approxModule (K := K) (ι := ι)
  refine ⟨(Fintype.card ι).factorial * max 1 C₁ ^ Fintype.card ι, by positivity, ?_⟩
  intro S₀ L c Q x μ hLinf hLfin hQ₀ hQ₁ hx hμm hμp hxΛ hxinf
  obtain ⟨y, σ, hspan, hint, hinf, hfin⟩ := hE S₀ L c Q x (fun _ ↦ μ) hLinf hLfin hQ₀ hx
    (fun _ ↦ hμm) (fun _ ↦ hμp) hxΛ hxinf
  refine ⟨y, σ, hspan, fun k p J hJ ↦ plucker_mem_approxDomain_wedgeForms (μ := fun _ ↦ μ) hQ₀ hC₁
    (fun _ ↦ hμm) (fun _ ↦ hμp) hint hinf hfin (fun w T ↦ le_of_eq ?_)
    (fun v _ T ↦ wedgeExponent_of_isNonarchimedean v.add_le T) hJ⟩
  rw [rpow_wedgeExponent_of_not_isNonarchimedean w.not_isNonarchimedean hQ₀ hQ₁ (by positivity) hμp
    (hJ.elim fun j hj ↦ Set.powersetCard.coe_nonempty_iff.1 ⟨j, hj.1⟩)]
  ring

/-! ### The weight of the wedge domain -/

omit [NumberField K] in
/-- The wedge exponents of all wedge forms at an archimedean absolute value sum to
`e · ∑ i, c v i + logb Q (C ^ M · (∏ l, μ l) ^ e · μ (k - 1) / μ k)`. -/
private theorem sum_wedgeExponent_of_not_isNonarchimedean (hv : ¬IsNonarchimedean v)
    (hp : 0 < p) (hkp : k + p = Fintype.card ι) (hμ : ∀ l < Fintype.card ι, μ l ≠ 0)
    (hC : C ≠ 0) :
    ∑ T : Set.powersetCard ι p, wedgeExponent c p k σ μ C Q v T =
      (Fintype.card ι - 1).choose (p - 1) * ∑ i, c v i +
        Real.logb Q (C ^ (Fintype.card ι).choose p *
          (∏ l : Fin (Fintype.card ι), μ l) ^ (Fintype.card ι - 1).choose (p - 1) *
            (μ (k - 1) / μ k)) := by
  classical
  have hk : k < Fintype.card ι := by omega
  simp_rw [wedgeExponent_of_not_isNonarchimedean hv]
  rw [sum_add_distrib, Set.powersetCard.sum_sum hp, nsmul_eq_mul, ← prod_wedgeGain (σ v) hp hkp,
    Real.logb_prod]
  intro T _
  refine mul_ne_zero hC ?_
  have hP : ∏ t ∈ (T : Finset ι), μ ((σ v).symm t) ≠ 0 :=
    prod_ne_zero_iff.2 fun t _ ↦ hμ _ ((σ v).symm t).isLt
  by_cases hT : ∀ t ∈ (T : Finset ι), k ≤ ((σ v).symm t : ℕ)
  · rw [wedgeGain_of_forall_le hT]
    exact mul_ne_zero (div_ne_zero (hμ _ (by omega)) (hμ _ hk)) hP
  · rwa [wedgeGain_of_not_forall_le hT]

omit [NumberField K] in
/-- The wedge exponents of all wedge forms at a nonarchimedean absolute value sum to
`e · ∑ i, c v i`. -/
private theorem sum_wedgeExponent_of_isNonarchimedean (hv : IsNonarchimedean v) (hp : 0 < p) :
    ∑ T : Set.powersetCard ι p, wedgeExponent c p k σ μ C Q v T =
      (Fintype.card ι - 1).choose (p - 1) * ∑ i, c v i := by
  simp_rw [wedgeExponent_of_isNonarchimedean hv]
  rw [Set.powersetCard.sum_sum hp, nsmul_eq_mul]

/-- **The weight of the wedge domain** (Bombieri–Gubler 7.5.30). For `0 < p` and `k + p = card ι`,
with the minima `μ l`, `l < card ι`, and the constant nonzero, the weight of the wedge exponents is
`e · approxWeight S₀ c + [K : ℚ] · logb Q (C ^ M · (∏ l, μ l) ^ e · μ (k - 1) / μ k)`, where
`e = (card ι - 1).choose (p - 1)` is the number of `p`-subsets containing a given index and
`M = (card ι).choose p` is the number of `p`-subsets. -/
theorem approxWeight_wedgeExponent (S₀ : Finset (FinitePlace K)) (c : AbsoluteValue K ℝ → ι → ℝ)
    (hp : 0 < p) (hkp : k + p = Fintype.card ι) (σ : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι)
    (hμ : ∀ l < Fintype.card ι, μ l ≠ 0) (hC : C ≠ 0) (Q : ℝ) :
    approxWeight S₀ (wedgeExponent c p k σ μ C Q) =
      (Fintype.card ι - 1).choose (p - 1) * approxWeight S₀ c +
        finrank ℚ K * Real.logb Q (C ^ (Fintype.card ι).choose p *
          (∏ l : Fin (Fintype.card ι), μ l) ^ (Fintype.card ι - 1).choose (p - 1) *
            (μ (k - 1) / μ k)) := by
  have hna (v : FinitePlace K) : IsNonarchimedean v.val := v.add_le
  simp only [approxWeight_def]
  simp_rw [sum_wedgeExponent_of_not_isNonarchimedean (InfinitePlace.not_isNonarchimedean _) hp hkp
    hμ hC, sum_wedgeExponent_of_isNonarchimedean (hna _) hp]
  -- Both sides are linear in the local sums `∑ i, c v i` and in the common logarithm.
  have key (E X : ℝ) (m a : InfinitePlace K → ℝ) (b : FinitePlace K → ℝ) :
      ∑ v, m v * (E * a v + X) + ∑ v ∈ S₀, E * b v =
        E * (∑ v, m v * a v + ∑ v ∈ S₀, b v) + (∑ v, m v) * X := by
    have h : ∑ v, m v * (E * a v + X) = E * ∑ v, m v * a v + (∑ v, m v) * X := by
      rw [mul_sum, sum_mul, ← sum_add_distrib]
      exact sum_congr rfl fun v _ ↦ by ring
    rw [h, ← mul_sum]
    ring
  rw [← InfinitePlace.sum_mult_eq, Nat.cast_sum]
  exact key _ _ (fun v ↦ (v.mult : ℝ)) (fun v ↦ ∑ i, c v.val i) fun v ↦ ∑ i, c v.val i

/-- **The weight of the wedge domain, multiplicatively** (Bombieri–Gubler 7.5.30). For
`0 < Q ≠ 1`, `0 < p`, `k + p = card ι`, positive minima `μ l`, `l < card ι`, and `0 < C`,
`Q ^ approxWeight` of the wedge exponents is `Q ^ (e · approxWeight S₀ c)` times
`(C ^ M · (∏ l, μ l) ^ e · μ (k - 1) / μ k) ^ [K : ℚ]`, with `e = (card ι - 1).choose (p - 1)`
and `M = (card ι).choose p`. -/
theorem rpow_approxWeight_wedgeExponent (S₀ : Finset (FinitePlace K))
    (c : AbsoluteValue K ℝ → ι → ℝ) (hp : 0 < p) (hkp : k + p = Fintype.card ι)
    (σ : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι) (hμ : ∀ l < Fintype.card ι, 0 < μ l)
    (hC : 0 < C) (hQ : 0 < Q) (hQ₁ : Q ≠ 1) :
    Q ^ approxWeight S₀ (wedgeExponent c p k σ μ C Q) =
      Q ^ ((Fintype.card ι - 1).choose (p - 1) * approxWeight S₀ c) *
        (C ^ (Fintype.card ι).choose p *
          (∏ l : Fin (Fintype.card ι), μ l) ^ (Fintype.card ι - 1).choose (p - 1) *
            (μ (k - 1) / μ k)) ^ finrank ℚ K := by
  rw [approxWeight_wedgeExponent S₀ c hp hkp σ (fun l hl ↦ (hμ l hl).ne') hC.ne',
    Real.rpow_add hQ]
  set X := C ^ (Fintype.card ι).choose p *
    (∏ l : Fin (Fintype.card ι), μ l) ^ (Fintype.card ι - 1).choose (p - 1) *
      (μ (k - 1) / μ k) with hX_def
  -- `X` is the product over the wedge forms of the constant times the minima attached to them.
  have hX : 0 < X := by
    rw [hX_def, ← prod_wedgeGain (Fintype.equivFin ι).symm hp hkp μ C]
    exact prod_pos fun T _ ↦ mul_pos hC
      (wedgeGain_pos hμ _ (card_pos.1 (by rw [card_eq]; exact hp)))
  rw [mul_comm (finrank ℚ K : ℝ), Real.rpow_mul hQ.le (Real.logb Q X), Real.rpow_logb hQ hQ₁ hX,
    Real.rpow_natCast]

/-- **The wedge domain of the successive minima is small after a large jump** (Bombieri–Gubler
7.5.30, toward Lemma 7.5.31). Let `μ` be the successive minima over `K` of an approximation domain
of level `0 < Q ≠ 1` with forms independent at the infinite places and at `S₀`. For `0 < p`,
`k + p = card ι` and `0 < C`, `Q ^ approxWeight` of the wedge exponents is at most
`A ^ e · C ^ (M · [K : ℚ]) · (μ (k - 1) / μ k) ^ [K : ℚ]`, where
`A = 2 ^ ([K : ℚ] · card ι) · ∏ v ∈ S₀, N 𝔭_v ^ card ι / approxConst S₀ L` is the constant of
Minkowski's second theorem for the domain, `e = (card ι - 1).choose (p - 1)` and
`M = (card ι).choose p`. -/
theorem rpow_approxWeight_wedgeExponent_le {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLinf : ∀ v : InfinitePlace K, LinearIndependent K (L v.val))
    (hLfin : ∀ v ∈ S₀, LinearIndependent K (L v.val)) (c : AbsoluteValue K ℝ → ι → ℝ)
    (hp : 0 < p) (hkp : k + p = Fintype.card ι) (σ : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι)
    (hC : 0 < C) (hQ₀ : 0 < Q) (hQ₁ : Q ≠ 1) :
    Q ^ approxWeight S₀ (wedgeExponent c p k σ
        ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q) ≤
      ((2 : ℝ) ^ (finrank ℚ K * Fintype.card ι) *
          (∏ v ∈ S₀, (v.maximalIdeal.asIdeal.absNorm : ℝ) ^ Fintype.card ι) /
            approxConst S₀ L) ^ (Fintype.card ι - 1).choose (p - 1) *
        C ^ ((Fintype.card ι).choose p * finrank ℚ K) *
          ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) (k - 1) /
            (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) k) ^ finrank ℚ K := by
  set μ := (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)
  have hμ (l : ℕ) (hl : l < Fintype.card ι) : 0 < μ l :=
    successiveMinimum_approx_pos hLinf hLfin c hQ₀ hl
  set A := (2 : ℝ) ^ (finrank ℚ K * Fintype.card ι) *
    (∏ v ∈ S₀, (v.maximalIdeal.asIdeal.absNorm : ℝ) ^ Fintype.card ι) / approxConst S₀ L
  set e := (Fintype.card ι - 1).choose (p - 1)
  set d := finrank ℚ K
  -- Minkowski's second theorem: `Q ^ weight · ∏ l, μ l ^ d ≤ A`.
  have hmink : Q ^ approxWeight S₀ c * (∏ l : Fin (Fintype.card ι), μ l) ^ d ≤ A := by
    have h := prod_successiveMinimum_approx_le hLinf hLfin c hQ₀
    rw [Real.rpow_neg hQ₀.le, ← div_eq_mul_inv] at h
    rw [← prod_pow, mul_comm]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hQ₀ _)).1 h
  have hP : 0 ≤ Q ^ approxWeight S₀ c * (∏ l : Fin (Fintype.card ι), μ l) ^ d :=
    mul_nonneg (Real.rpow_pos_of_pos hQ₀ _).le
      (pow_nonneg (prod_nonneg fun (l : Fin _) _ ↦ (hμ l l.isLt).le) _)
  rw [rpow_approxWeight_wedgeExponent S₀ c hp hkp σ hμ hC hQ₀ hQ₁, mul_comm (e : ℝ),
    Real.rpow_mul hQ₀.le, Real.rpow_natCast]
  calc (Q ^ approxWeight S₀ c) ^ e *
        (C ^ (Fintype.card ι).choose p * (∏ l : Fin (Fintype.card ι), μ l) ^ e *
          (μ (k - 1) / μ k)) ^ d
      = (Q ^ approxWeight S₀ c * (∏ l : Fin (Fintype.card ι), μ l) ^ d) ^ e *
          C ^ ((Fintype.card ι).choose p * d) * (μ (k - 1) / μ k) ^ d := by
        ring
    _ ≤ A ^ e * C ^ ((Fintype.card ι).choose p * d) * (μ (k - 1) / μ k) ^ d := by
        have hr : 0 ≤ μ (k - 1) / μ k := div_nonneg
          (Submodule.successiveMinimum_nonneg (approxModule S₀ L c Q) (approxBody L c Q) _)
          (Submodule.successiveMinimum_nonneg (approxModule S₀ L c Q) (approxBody L c Q) _)
        gcongr

/-! ### The wedge domain with the minima at one infinite place -/

open scoped Classical in
/-- **The exponents of the wedge domain with the minima at one infinite place** `w₀`. Given
exponents `c`, an exterior degree `p`, a jump index `k`, one bijection `σ` from the indices of the
minima to the forms, minima `μ` and a constant `C`, the exponent of the wedge form `T` at `v` is
`∑ t ∈ T, c v t` at a nonarchimedean `v`, `∑ t ∈ T, c v t + logb Q C` at an archimedean `v ≠ w₀`,
and `∑ t ∈ T, c v t + logb Q (C · g ^ (d / mult w₀))` at `w₀`, where `d = [K : ℚ]` and
`g = wedgeGain k μ σ T` is the product of the `μ (σ.symm t)` over `t ∈ T`, multiplied by
`μ (k - 1) / μ k` when every `σ.symm t` is at least `k`.

The wedge bound holds for the constant `C` of `exists_plucker_mem_approxDomain_wedgeExponentAt`, not
for an arbitrary one: for that `C` and for `0 < Q` and `Q ≠ 1`, the Plücker vectors of the family
corrected after `exists_balance` moves the minima to `w₀`, indexed by `p`-subsets meeting the first
`k` indices, lie in the approximation domain with these exponents. That family has the local factors
`C₂ · μ l ^ (d / mult w₀)` at `w₀` and `C₂` at the other infinite places, so the minima enter at
`w₀` alone and one bijection suffices. The balancing factor `C₂` contributes `C₂ ^ p` to the bound
of a `p`-fold wedge, and this is absorbed into that `C`, which is uniform in `p ≤ card ι`. -/
def wedgeExponentAt (c : AbsoluteValue K ℝ → ι → ℝ) (p k : ℕ) (w₀ : InfinitePlace K)
    (σ : Fin (Fintype.card ι) ≃ ι) (μ : ℕ → ℝ) (C Q : ℝ) :
    AbsoluteValue K ℝ → Set.powersetCard ι p → ℝ :=
  fun v T ↦ ∑ t ∈ (T : Finset ι), c v t +
    if IsNonarchimedean v then 0 else
      Real.logb Q (C * if v = w₀.val then wedgeGain k μ σ T ^ ((finrank ℚ K : ℝ) / w₀.mult)
        else 1)

open scoped Classical in
/-- The exponent of `T` at `v` of the wedge domain at `w₀`, before deciding whether `v` is
archimedean or equal to `w₀`. -/
theorem wedgeExponentAt_def (c : AbsoluteValue K ℝ → ι → ℝ) (p k : ℕ) (w₀ : InfinitePlace K)
    (σ : Fin (Fintype.card ι) ≃ ι) (μ : ℕ → ℝ) (C Q : ℝ) (v : AbsoluteValue K ℝ)
    (T : Set.powersetCard ι p) :
    wedgeExponentAt c p k w₀ σ μ C Q v T = ∑ t ∈ (T : Finset ι), c v t +
      if IsNonarchimedean v then 0 else
        Real.logb Q (C * if v = w₀.val then wedgeGain k μ σ T ^ ((finrank ℚ K : ℝ) / w₀.mult)
          else 1) :=
  (rfl)

section WedgeExponentAt

variable {w₀ : InfinitePlace K} {τ : Fin (Fintype.card ι) ≃ ι}

/-- At a nonarchimedean absolute value `v`, the exponent of `T` at `v` is `∑ t ∈ T, c v t`. -/
@[simp]
theorem wedgeExponentAt_of_isNonarchimedean (hv : IsNonarchimedean v)
    (T : Set.powersetCard ι p) :
    wedgeExponentAt c p k w₀ τ μ C Q v T = ∑ t ∈ (T : Finset ι), c v t := by
  simp [wedgeExponentAt_def, hv]

/-- At `w₀` the exponent of `T` is `∑ t ∈ T, c w₀ t` plus the logarithm to base `Q` of the
constant times the `d / mult w₀`-th power of the product of the minima attached to `T`, with the
gain `μ (k - 1) / μ k` when `T` lies in the top block. -/
@[simp]
theorem wedgeExponentAt_self (T : Set.powersetCard ι p) :
    wedgeExponentAt c p k w₀ τ μ C Q w₀.val T = ∑ t ∈ (T : Finset ι), c w₀.val t +
      Real.logb Q (C * wedgeGain k μ τ T ^ ((finrank ℚ K : ℝ) / w₀.mult)) := by
  simp [wedgeExponentAt_def, w₀.not_isNonarchimedean]

/-- At an archimedean absolute value other than `w₀` the exponent of `T` is
`∑ t ∈ T, c v t + logb Q C`: the minima do not enter. -/
@[simp]
theorem wedgeExponentAt_of_not_isNonarchimedean_of_ne (hv : ¬IsNonarchimedean v) (hw : v ≠ w₀.val)
    (T : Set.powersetCard ι p) :
    wedgeExponentAt c p k w₀ τ μ C Q v T = ∑ t ∈ (T : Finset ι), c v t + Real.logb Q C := by
  simp [wedgeExponentAt_def, hv, hw]

/-- For `0 < p`, the exponents of the wedge domain at `w₀` depend only on the minima `μ l`,
`l < card ι`. -/
theorem wedgeExponentAt_congr (hp : 0 < p) {μ' : ℕ → ℝ} (h : ∀ l < Fintype.card ι, μ l = μ' l) :
    wedgeExponentAt c p k w₀ τ μ C Q = wedgeExponentAt c p k w₀ τ μ' C Q := by
  ext v T
  rw [wedgeExponentAt_def, wedgeExponentAt_def,
    wedgeGain_congr h τ (card_pos.1 (by rw [card_eq T]; exact hp))]

/-- At `w₀`, for `0 < Q ≠ 1`, `0 < C`, `0 < p` and positive minima `μ l`, `l < card ι`, `Q`
raised to the exponent of `T` is the constant times the `d / mult w₀`-th power of the product of
the minima attached to `T` (with the gain on the top block) times the product of the bounds
`Q ^ c w₀ t` over `t ∈ T`. -/
theorem rpow_wedgeExponentAt_self (hQ : 0 < Q) (hQ₁ : Q ≠ 1) (hC : 0 < C)
    (hμ : ∀ l < Fintype.card ι, 0 < μ l) (hp : 0 < p) (T : Set.powersetCard ι p) :
    Q ^ wedgeExponentAt c p k w₀ τ μ C Q w₀.val T =
      C * wedgeGain k μ τ T ^ ((finrank ℚ K : ℝ) / w₀.mult) *
        ∏ t ∈ (T : Finset ι), Q ^ c w₀.val t := by
  have hT : (T : Finset ι).Nonempty := card_pos.1 (by rw [card_eq]; exact hp)
  rw [wedgeExponentAt_self,
    Real.rpow_sum_add_logb hQ hQ₁ (mul_pos hC (Real.rpow_pos_of_pos (wedgeGain_pos hμ τ hT) _))]

/-- At an archimedean absolute value `v ≠ w₀`, for `0 < Q ≠ 1` and `0 < C`, `Q` raised to the
exponent of `T` is the constant times the product of the bounds `Q ^ c v t` over `t ∈ T`. -/
theorem rpow_wedgeExponentAt_of_not_isNonarchimedean_of_ne (hv : ¬IsNonarchimedean v)
    (hw : v ≠ w₀.val) (hQ : 0 < Q) (hQ₁ : Q ≠ 1) (hC : 0 < C) (T : Set.powersetCard ι p) :
    Q ^ wedgeExponentAt c p k w₀ τ μ C Q v T = C * ∏ t ∈ (T : Finset ι), Q ^ c v t := by
  rw [wedgeExponentAt_of_not_isNonarchimedean_of_ne hv hw, Real.rpow_sum_add_logb hQ hQ₁ hC]

/-- The wedge bound at an infinite place for minima `μ'` that are `C₂ · μ l ^ (d / mult w₀)` at
`w₀` and the constant `C₂ ≥ 1` at the other infinite places is dominated by `Q` raised to the
exponent `wedgeExponentAt` with the constant multiplied by `C₂ ^ card ι`. -/
private theorem le_rpow_wedgeExponentAt {w₀ : InfinitePlace K} {μ' : AbsoluteValue K ℝ → ℕ → ℝ}
    {C₀ C₂ : ℝ} (hμp : ∀ l < Fintype.card ι, 0 < μ l) (hC₀ : 0 < C₀)
    (hC₂ : 1 ≤ C₂) (hw₀ : ∀ l, μ' w₀.val l = C₂ * μ l ^ ((finrank ℚ K : ℝ) / w₀.mult))
    (hne : ∀ v : InfinitePlace K, v ≠ w₀ → ∀ l, μ' v.val l = C₂) (hQ : 0 < Q) (hQ₁ : Q ≠ 1)
    (hp : 0 < p) (σ : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι) (v : InfinitePlace K)
    (T : Set.powersetCard ι p) :
    C₀ * ((∏ t ∈ (T : Finset ι), Q ^ c v.val t) * wedgeGain k (μ' v.val) (σ v.val) T) ≤
      Q ^ wedgeExponentAt c p k w₀ (σ w₀.val) μ (C₀ * C₂ ^ Fintype.card ι) Q v.val T := by
  have hC₂₀ : 0 < C₂ := zero_lt_one.trans_le hC₂
  have hpow : C₂ ^ p ≤ C₂ ^ Fintype.card ι := by
    refine pow_le_pow_right₀ hC₂ ?_
    rw [← card_eq T]
    exact card_le_univ _
  have hP : 0 ≤ ∏ t ∈ (T : Finset ι), Q ^ c v.val t :=
    prod_nonneg fun _ _ ↦ (Real.rpow_pos_of_pos hQ _).le
  by_cases hv : v = w₀
  · subst hv
    have hT : (T : Finset ι).Nonempty := card_pos.1 (by rw [card_eq]; exact hp)
    have hμ₀ (l : ℕ) (hl : l < Fintype.card ι) : 0 ≤ μ l := (hμp l hl).le
    rw [rpow_wedgeExponentAt_self hQ hQ₁ (by positivity) hμp hp]
    rw [funext hw₀, wedgeGain_const_mul_rpow hC₂₀.ne' hμ₀ _ hT, card_eq]
    have hG : 0 ≤ wedgeGain k μ (σ v.val) T ^ ((finrank ℚ K : ℝ) / v.mult) :=
      Real.rpow_nonneg (wedgeGain_nonneg hμ₀ _ hT) _
    convert mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow hC₀.le) hG) hP using 1
    ring
  · rw [rpow_wedgeExponentAt_of_not_isNonarchimedean_of_ne v.not_isNonarchimedean
      (fun h ↦ hv (Subtype.ext h)) hQ hQ₁ (by positivity)]
    rw [funext (hne v hv), wedgeGain_const hC₂₀.ne', card_eq]
    calc _ = (C₀ * C₂ ^ p) * ∏ t ∈ (T : Finset ι), Q ^ c v.val t := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC₀.le) hP

/-- **The Plücker vectors of the balanced minimal vectors lie in the wedge domain at `w₀`**
(Bombieri–Gubler 7.5.30, (7.44)–(7.45), with the minima at one infinite place after
Evertse–Schlickewei 2002, §9). There is `C > 0`, depending only on `K` and `ι`, with the following
property. Let the forms `L v` be linearly independent at the infinite places and at `S₀`, let
`0 < Q ≠ 1`, let `μ` be the successive minima over `K` of `approxDomain S₀ L c Q`, and let `w₀` be
an infinite place. Then there are `card ι` linearly independent vectors `y`, whose first
`finrank K V(Q)` members span `V(Q) = approxSpan S₀ L c Q`, and one bijection `σ` from the
indices of the minima to the forms, such that for every `k` and every `p`-subset `J` meeting
`{0, …, k - 1}`, the Plücker vector of the `y j`, `j ∈ J`, lies in the approximation domain of
the wedge forms with the exponents `wedgeExponentAt c p k w₀ σ μ C Q`. -/
theorem exists_plucker_mem_approxDomain_wedgeExponentAt [LinearOrder ι] :
    ∃ C : ℝ, 0 < C ∧ ∀ (S₀ : Finset (FinitePlace K)) (L : AbsoluteValue K ℝ → ι → Dual K (ι → K))
      (c : AbsoluteValue K ℝ → ι → ℝ) (Q : ℝ) (w₀ : InfinitePlace K),
      (∀ v : InfinitePlace K, LinearIndependent K (L v.val)) →
      (∀ v ∈ S₀, LinearIndependent K (L v.val)) → 0 < Q → Q ≠ 1 →
      ∃ (y : Fin (Fintype.card ι) → ι → K) (σ : Fin (Fintype.card ι) ≃ ι),
        LinearIndependent K y ∧
        approxSpan S₀ L c Q =
          Submodule.span K (y '' {l | (l : ℕ) < finrank K (approxSpan S₀ L c Q)}) ∧
        ∀ (k p : ℕ) (J : Set.powersetCard (Fin (Fintype.card ι)) p), (∃ j ∈ J, (j : ℕ) < k) →
          plucker (y ∘ ofFinEmbEquiv.symm J) ∈ approxDomain S₀ (fun v ↦ wedgeForms (L v) p)
            (wedgeExponentAt c p k w₀ σ
              ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q) Q := by
  have := Classical.decEq (AbsoluteValue K ℝ)
  obtain ⟨C₁, hC₁, hE⟩ := exists_evertse_approxModule (K := K) (ι := ι)
  set N := Fintype.card ι
  set C₂ := unitConst K ^ ((finrank ℚ K : ℝ)⁻¹)
  have hC₂ : 1 ≤ C₂ := Real.one_le_rpow (one_le_unitConst K) (by positivity)
  have hC₂₀ : 0 < C₂ := zero_lt_one.trans_le hC₂
  refine ⟨N.factorial * max 1 C₁ ^ N * C₂ ^ N, by positivity, ?_⟩
  intro S₀ L c Q w₀ hLinf hLfin hQ₀ hQ₁
  -- The minimal vectors with their minima moved to `w₀`.
  obtain ⟨x, hx, hxspan, hxΛ⟩ := exists_balance hLinf hLfin c hQ₀ w₀
  set μ := (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)
  have hμp (l : ℕ) (hl : l < N) : 0 < μ l := successiveMinimum_approx_pos hLinf hLfin c hQ₀ hl
  have hμm := monotoneOn_successiveMinimum_approx S₀ L c hQ₀
  -- Evertse's lemma with the balanced minima `C₂ · μ l ^ a` at `w₀` and `C₂` elsewhere.
  set a : ℝ := (finrank ℚ K : ℝ) / w₀.mult
  let μ' : AbsoluteValue K ℝ → ℕ → ℝ := fun v l ↦ C₂ * if v = w₀.val then μ l ^ a else 1
  have hμ'w₀ (l : ℕ) : μ' w₀.val l = C₂ * μ l ^ a := by simp [μ']
  have hμ'ne {v : InfinitePlace K} (hv : v ≠ w₀) (l : ℕ) : μ' v.val l = C₂ := by
    simp [μ', Subtype.val_injective.ne hv]
  have hμ' (v : InfinitePlace K) : MonotoneOn (μ' v.val) (Set.Iio N) ∧
      (∀ l < N, 0 < μ' v.val l) ∧
      ∀ (i : ι) (l : Fin N), v (L v.val i (x l)) ≤ μ' v.val l * Q ^ c v.val i := by
    rcases eq_or_ne v w₀ with rfl | hv
    · rw [funext hμ'w₀]
      refine ⟨fun i hi j hj hij ↦ ?_, fun l hl ↦ ?_, fun i l ↦ (hxΛ l).2.2 i⟩
      · exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (hμp i hi).le (hμm hi hj hij) (by positivity)) hC₂₀.le
      · exact mul_pos hC₂₀ (Real.rpow_pos_of_pos (hμp l hl) _)
    · rw [funext (hμ'ne hv)]
      exact ⟨monotoneOn_const, fun _ _ ↦ hC₂₀, fun i l ↦ (hxΛ l).2.1 v hv i⟩
  choose hμ'm hμ'p hxinf using hμ'
  obtain ⟨y, σ, hspan, hint, hinf, hfin⟩ := hE S₀ L c Q x μ' hLinf hLfin hQ₀ hx hμ'm hμ'p
    (fun l ↦ (hxΛ l).1) hxinf
  -- The correction is unitriangular, so it keeps the spans of the initial segments.
  have hyx (R : ℕ) : Submodule.span K (y '' {l | (l : ℕ) < R}) =
      Submodule.span K (x '' {l | (l : ℕ) < R}) :=
    TauCeti.Submodule.span_image_eq_span_image_of_isLowerSet (fun j _ ↦ hspan j) fun _ _ hba hb ↦
      (Fin.le_iff_val_le_val.1 hba).trans_lt hb
  refine ⟨y, σ w₀.val, linearIndependent_of_top_le_span_of_card_eq_finrank ?_ (by simp),
    (hyx _).symm ▸ hxspan, fun k p J hJ ↦ ?_⟩
  · have huniv : {l : Fin N | (l : ℕ) < N} = Set.univ := Set.eq_univ_of_forall fun l ↦ l.isLt
    rw [← Set.image_univ, ← huniv, hyx, huniv, Set.image_univ,
      hx.span_eq_top_of_card_eq_finrank' (by simp)]
  -- The wedge bounds at the infinite places, with the minima at `w₀` alone.
  have hp : 0 < p := hJ.elim fun j hj ↦ Set.powersetCard.coe_nonempty_iff.1 ⟨j, hj.1⟩
  refine plucker_mem_approxDomain_wedgeForms hQ₀ hC₁ hμ'm hμ'p hint hinf hfin (fun v T ↦ ?_)
    (fun v _ T ↦ wedgeExponentAt_of_isNonarchimedean v.add_le T) hJ
  exact le_rpow_wedgeExponentAt (c := c) (k := k) (w₀ := w₀) (μ' := μ') hμp
    (by positivity : 0 < (N.factorial : ℝ) * max 1 C₁ ^ N) hC₂ hμ'w₀ (fun v hv ↦ hμ'ne hv) hQ₀ hQ₁
    hp σ v T

/-- **The weight of the wedge domain at `w₀`.** Moving the minima to `w₀` does not change the
weight: for `0 < p` and positive minima, the exponents `wedgeExponentAt c p k w₀ σ μ C Q` have the
weight of `wedgeExponent c p k (fun _ ↦ σ) μ C Q`, since `mult w₀ · (d / mult w₀) = d` is the sum
of the multiplicities of the infinite places. -/
theorem approxWeight_wedgeExponentAt (S₀ : Finset (FinitePlace K)) (c : AbsoluteValue K ℝ → ι → ℝ)
    (hp : 0 < p) (w₀ : InfinitePlace K) (σ : Fin (Fintype.card ι) ≃ ι)
    (hμ : ∀ l < Fintype.card ι, 0 < μ l) (C Q : ℝ) :
    approxWeight S₀ (wedgeExponentAt c p k w₀ σ μ C Q) =
      approxWeight S₀ (wedgeExponent c p k (fun _ ↦ σ) μ C Q) := by
  have := Classical.decEq (InfinitePlace K)
  rcases eq_or_ne C 0 with rfl | hC
  · simp [approxWeight_def, wedgeExponentAt_def, wedgeExponent_def]
  set a : ℝ := (finrank ℚ K : ℝ) / w₀.mult
  set G : Set.powersetCard ι p → ℝ := fun T ↦ wedgeGain k μ σ T
  have hG (T : Set.powersetCard ι p) : 0 < G T :=
    wedgeGain_pos hμ σ (card_pos.1 (by rw [card_eq T]; exact hp))
  set B : InfinitePlace K → Set.powersetCard ι p → ℝ :=
    fun v T ↦ ∑ t ∈ (T : Finset ι), c v.val t + Real.logb Q C
  -- Both exponents split off `logb Q (G T)`, weighted `a` at `w₀` alone and `1` everywhere.
  have hAt (v : InfinitePlace K) (T : Set.powersetCard ι p) :
      wedgeExponentAt c p k w₀ σ μ C Q v.val T =
        B v T + (if v = w₀ then a else 0) * Real.logb Q (G T) := by
    by_cases hv : v = w₀
    · subst hv
      rw [wedgeExponentAt_self, Real.logb_mul hC (Real.rpow_pos_of_pos (hG T) _).ne',
        Real.logb_rpow_eq_mul_logb_of_pos (hG T), ite_eq_left rfl, ← add_assoc]
    · rw [wedgeExponentAt_of_not_isNonarchimedean_of_ne v.not_isNonarchimedean
        fun h ↦ hv (Subtype.ext h), ite_eq_right hv, zero_mul, add_zero]
  have hW (v : InfinitePlace K) (T : Set.powersetCard ι p) :
      wedgeExponent c p k (fun _ ↦ σ) μ C Q v.val T = B v T + 1 * Real.logb Q (G T) := by
    rw [wedgeExponent_of_not_isNonarchimedean v.not_isNonarchimedean,
      Real.logb_mul hC (hG T).ne', one_mul, add_assoc]
  have hfin (v : FinitePlace K) (T : Set.powersetCard ι p) :
      wedgeExponentAt c p k w₀ σ μ C Q v.val T = wedgeExponent c p k (fun _ ↦ σ) μ C Q v.val T := by
    rw [wedgeExponentAt_of_isNonarchimedean v.add_le, wedgeExponent_of_isNonarchimedean v.add_le]
  -- Weights of total multiplicity `[K : ℚ]` contribute `[K : ℚ]` times the sum of the
  -- `logb Q (G T)`.
  have hsplit (w : InfinitePlace K → ℝ)
      (hw : ∑ v : InfinitePlace K, (v.mult : ℝ) * w v = finrank ℚ K) :
      ∑ v : InfinitePlace K, (v.mult : ℝ) *
          ∑ T : Set.powersetCard ι p, (B v T + w v * Real.logb Q (G T)) =
        ∑ v : InfinitePlace K, (v.mult : ℝ) * ∑ T : Set.powersetCard ι p, B v T +
          finrank ℚ K * ∑ T : Set.powersetCard ι p, Real.logb Q (G T) := by
    rw [← hw, sum_mul]
    simp only [sum_add_distrib, ← mul_sum, mul_add, mul_assoc]
  -- The weight `a` at `w₀` alone carries the total multiplicity `[K : ℚ]` of the infinite places.
  have hw₀ : ∑ v : InfinitePlace K, (v.mult : ℝ) * (if v = w₀ then a else 0) = finrank ℚ K := by
    simp only [mul_ite, mul_zero, sum_ite_eq', mem_univ, ↓reduceIte]
    exact mul_div_cancel₀ _ (Nat.cast_ne_zero.2 InfinitePlace.mult_ne_zero)
  have hw₁ : ∑ v : InfinitePlace K, (v.mult : ℝ) * 1 = finrank ℚ K := by
    simp only [mul_one, ← Nat.cast_sum, InfinitePlace.sum_mult_eq]
  rw [approxWeight_def, approxWeight_def]
  simp only [hAt, hW, hfin]
  rw [hsplit _ hw₀, hsplit _ hw₁]

/-- **The wedge domain at `w₀` of the successive minima is small after a large jump.** Let `μ` be
the successive minima over `K` of an approximation domain of level `0 < Q ≠ 1` with forms
independent at the infinite places and at `S₀`. For `0 < p`, `k + p = card ι` and `0 < C`,
`Q ^ approxWeight` of the exponents `wedgeExponentAt c p k w₀ σ μ C Q` is at most
`A ^ e · C ^ (M · [K : ℚ]) · (μ (k - 1) / μ k) ^ [K : ℚ]`, with the constants of
`rpow_approxWeight_wedgeExponent_le`. -/
theorem rpow_approxWeight_wedgeExponentAt_le {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLinf : ∀ v : InfinitePlace K, LinearIndependent K (L v.val))
    (hLfin : ∀ v ∈ S₀, LinearIndependent K (L v.val)) (c : AbsoluteValue K ℝ → ι → ℝ)
    (hp : 0 < p) (hkp : k + p = Fintype.card ι) (w₀ : InfinitePlace K)
    (σ : Fin (Fintype.card ι) ≃ ι) (hC : 0 < C) (hQ₀ : 0 < Q) (hQ₁ : Q ≠ 1) :
    Q ^ approxWeight S₀ (wedgeExponentAt c p k w₀ σ
        ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q) ≤
      ((2 : ℝ) ^ (finrank ℚ K * Fintype.card ι) *
          (∏ v ∈ S₀, (v.maximalIdeal.asIdeal.absNorm : ℝ) ^ Fintype.card ι) /
            approxConst S₀ L) ^ (Fintype.card ι - 1).choose (p - 1) *
        C ^ ((Fintype.card ι).choose p * finrank ℚ K) *
          ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) (k - 1) /
            (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) k) ^ finrank ℚ K := by
  rw [approxWeight_wedgeExponentAt S₀ c hp w₀ σ
    fun _ ↦ successiveMinimum_approx_pos hLinf hLfin c hQ₀]
  exact rpow_approxWeight_wedgeExponent_le hLinf hLfin c hp hkp (fun _ ↦ σ) hC hQ₀ hQ₁

end WedgeExponentAt

end TauCeti.NumberField
