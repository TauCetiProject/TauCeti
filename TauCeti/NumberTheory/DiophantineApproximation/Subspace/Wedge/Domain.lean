/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import TauCeti.LinearAlgebra.ExteriorPower.LinearForms
public import TauCeti.NumberTheory.DiophantineApproximation.Subspace.SuccessiveMinima

import TauCeti.Data.Set.PowersetCard
import TauCeti.Analysis.ExteriorPower.WedgeForms
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
`C · Q ^ (∑ t ∈ T, c v t) · g v T` for each wedge form `T`, where `g v T` is the product of the
`μ (σ v⁻¹ t)` over `t ∈ T`, times the gain `μ (k - 1) / μ k` when `T` lies in the top block of
`σ v`. The constant and the gain are absorbed into the exponent: `wedgeExponent c p k σ μ C Q`
is `∑ t ∈ T, c v t + logb Q (C · g v T)` at the archimedean absolute values and `∑ t ∈ T, c v t`
at the nonarchimedean ones, where no constant and no gain occur. Then these Plücker vectors lie
in `approxDomain S₀ (fun v ↦ wedgeForms (L v) p) (wedgeExponent c p k σ μ C Q) Q`
(`TauCeti.NumberField.exists_plucker_mem_approxDomain_wedgeForms`), with `C` depending only on
`K` and `ι`.

The weight of the wedge exponents is exact. Each index lies in `e = (N - 1).choose (p - 1)` of
the `p`-subsets and, for `k + p = N`, exactly one subset is the top block, so
`approxWeight S₀ (wedgeExponent …)` is `e · approxWeight S₀ c` plus `[K : ℚ]` times
`logb Q (C ^ M · (∏ l, μ l) ^ e · μ (k - 1) / μ k)`, with `M = N.choose p`
(`TauCeti.NumberField.approxWeight_wedgeExponent`). When `μ` are the successive minima,
Minkowski's second theorem bounds `Q ^ approxWeight S₀ c · ∏ l, μ l ^ [K : ℚ]` by a constant, so
`Q ^ approxWeight` of the wedge exponents is at most a constant times
`(μ (k - 1) / μ k) ^ [K : ℚ]` (`TauCeti.NumberField.rpow_approxWeight_wedgeExponent_le`): a
large jump between consecutive minima makes the wedge domain small.

## Main definitions

* `TauCeti.NumberField.wedgeExponent`: the exponents of the wedge domain `S(Q)`.

## Main results

* `TauCeti.NumberField.exists_plucker_mem_approxDomain_wedgeForms`: the Plücker vectors of the
  corrected minimal vectors lie in the wedge domain.
* `TauCeti.NumberField.approxWeight_wedgeExponent` and
  `TauCeti.NumberField.rpow_approxWeight_wedgeExponent`: the exact weight of the wedge domain.
* `TauCeti.NumberField.rpow_approxWeight_wedgeExponent_le`: for the successive minima, the
  wedge domain has weight at most a constant times `(μ (k - 1) / μ k) ^ [K : ℚ]`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  7.5.30, (7.42)–(7.45), and Lemma 7.5.31.
* J.-H. Evertse, *An improvement of the quantitative Subspace theorem*, Compositio Math. 101
  (1996), 225–311.
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
`∑ t ∈ T, c v t + logb Q (C · g)`, where `g` is the product of the `μ ((σ v).symm t)` over
`t ∈ T`, multiplied by `μ (k - 1) / μ k` when every `(σ v).symm t` is at least `k`. -/
def wedgeExponent (c : AbsoluteValue K ℝ → ι → ℝ) (p k : ℕ)
    (σ : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι) (μ : ℕ → ℝ) (C Q : ℝ) :
    AbsoluteValue K ℝ → Set.powersetCard ι p → ℝ :=
  fun v T ↦ ∑ t ∈ (T : Finset ι), c v t +
    if IsNonarchimedean v then 0 else
      Real.logb Q (C * ((if ∀ t ∈ (T : Finset ι), k ≤ ((σ v).symm t : ℕ) then μ (k - 1) / μ k
        else 1) * ∏ t ∈ (T : Finset ι), μ ((σ v).symm t)))

variable {c : AbsoluteValue K ℝ → ι → ℝ} {p k : ℕ}
  {σ : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι} {μ : ℕ → ℝ} {C Q : ℝ}
  {v : AbsoluteValue K ℝ}

/-- At a nonarchimedean absolute value the wedge exponent of `T` is `∑ t ∈ T, c v t`. -/
@[simp]
theorem wedgeExponent_of_isNonarchimedean (hv : IsNonarchimedean v) (T : Set.powersetCard ι p) :
    wedgeExponent c p k σ μ C Q v T = ∑ t ∈ (T : Finset ι), c v t := by
  simp [wedgeExponent, hv]

/-- At an archimedean absolute value the wedge exponent of `T` is `∑ t ∈ T, c v t` plus the
logarithm to base `Q` of the constant times the product of the minima attached to `T`, with the
gain `μ (k - 1) / μ k` when `T` lies in the top block. -/
@[simp]
theorem wedgeExponent_of_not_isNonarchimedean (hv : ¬IsNonarchimedean v)
    (T : Set.powersetCard ι p) :
    wedgeExponent c p k σ μ C Q v T = ∑ t ∈ (T : Finset ι), c v t +
      Real.logb Q (C * ((if ∀ t ∈ (T : Finset ι), k ≤ ((σ v).symm t : ℕ) then μ (k - 1) / μ k
        else 1) * ∏ t ∈ (T : Finset ι), μ ((σ v).symm t))) := by
  simp [wedgeExponent, hv]

/-- The product of the minima attached to a nonempty set of forms, with the gain on the top
block, is positive when the first `card ι` minima are. -/
private theorem wedgeGain_pos (hμ : ∀ l < Fintype.card ι, 0 < μ l) (τ : ι ≃ Fin (Fintype.card ι))
    {T : Finset ι} (hT : T.Nonempty) :
    0 < (if ∀ t ∈ T, k ≤ (τ t : ℕ) then μ (k - 1) / μ k else 1) * ∏ t ∈ T, μ (τ t) := by
  refine mul_pos ?_ (prod_pos fun t _ ↦ hμ _ (τ t).isLt)
  split_ifs with h
  · obtain ⟨t, ht⟩ := hT
    have hk : k < Fintype.card ι := (h t ht).trans_lt (τ t).isLt
    exact div_pos (hμ _ (by omega)) (hμ _ hk)
  · exact one_pos

/-- At a nonarchimedean absolute value, `Q` raised to the wedge exponent of `T` is the product of
the bounds `Q ^ c v t` over `t ∈ T`. -/
theorem rpow_wedgeExponent_of_isNonarchimedean (hv : IsNonarchimedean v) (hQ : 0 < Q)
    (T : Set.powersetCard ι p) :
    Q ^ wedgeExponent c p k σ μ C Q v T = ∏ t ∈ (T : Finset ι), Q ^ c v t := by
  rw [wedgeExponent_of_isNonarchimedean hv, Real.rpow_sum_of_pos hQ]

/-- At an archimedean absolute value, `Q` raised to the wedge exponent of `T` is the constant
times the product of the minima attached to `T` (with the gain on the top block) times the
product of the bounds `Q ^ c v t` over `t ∈ T`. -/
theorem rpow_wedgeExponent_of_not_isNonarchimedean (hv : ¬IsNonarchimedean v) (hQ : 0 < Q)
    (hQ₁ : Q ≠ 1) (hC : 0 < C) (hμ : ∀ l < Fintype.card ι, 0 < μ l) (hp : 0 < p)
    (T : Set.powersetCard ι p) :
    Q ^ wedgeExponent c p k σ μ C Q v T =
      C * ((if ∀ t ∈ (T : Finset ι), k ≤ ((σ v).symm t : ℕ) then μ (k - 1) / μ k else 1) *
        ∏ t ∈ (T : Finset ι), μ ((σ v).symm t)) * ∏ t ∈ (T : Finset ι), Q ^ c v t := by
  have hT : (T : Finset ι).Nonempty := card_pos.1 (by rw [card_eq]; exact hp)
  rw [wedgeExponent_of_not_isNonarchimedean hv, Real.rpow_add hQ, Real.rpow_sum_of_pos hQ,
    Real.rpow_logb hQ hQ₁ (mul_pos hC (wedgeGain_pos hμ (σ v).symm hT)), mul_comm]

/-! ### The Plücker vectors of the corrected minimal vectors -/

variable [NumberField K]

/-- **Evertse's lemma for a basis of an approximation module.** There is `C₁ ≥ 0`, depending only
on `K` and `ι`, such that linearly independent vectors `x l` of `approxModule S₀ L c Q`, `0 < Q`,
with `|L v i (x l)|_v ≤ μ l · Q ^ c v i` at the infinite places, for nondecreasing `μ`, have
triangular corrections `y j`, integral outside `S₀`, and bijections `σ v` with
`|L v (σ v i) (y j)|_v ≤ C₁ · Q ^ c v (σ v i) · min (μ i) (μ j)` at the infinite places and
`|L v i (y j)|_v ≤ Q ^ c v i` at the places of `S₀`. -/
private theorem exists_evertse_approxModule :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ (S₀ : Finset (FinitePlace K))
      (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) (c : AbsoluteValue K ℝ → ι → ℝ) (Q : ℝ)
      (x : Fin (Fintype.card ι) → ι → K) (μ : ℕ → ℝ),
      (∀ v : InfinitePlace K, LinearIndependent K (L v.val)) →
      (∀ v ∈ S₀, LinearIndependent K (L v.val)) → 0 < Q → LinearIndependent K x →
      MonotoneOn μ (Set.Iio (Fintype.card ι)) → (∀ l < Fintype.card ι, 0 < μ l) →
      (∀ l, x l ∈ approxModule S₀ L c Q) →
      (∀ (v : InfinitePlace K) (i : ι) (l : Fin (Fintype.card ι)),
        v (L v.val i (x l)) ≤ μ l * Q ^ c v.val i) →
      ∃ (y : Fin (Fintype.card ι) → ι → K) (σ : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι),
        (∀ j, y j - x j ∈ Submodule.span K (x '' Set.Iio j)) ∧
        (∀ v : FinitePlace K, v ∉ S₀ → ∀ j i, v (y j i) ≤ 1) ∧
        (∀ (v : InfinitePlace K) i j, v (L v.val (σ v.val i) (y j)) ≤
          C₁ * Q ^ c v.val (σ v.val i) * min (μ i) (μ j)) ∧
        ∀ v ∈ S₀, ∀ i j, v (L v.val i (y j)) ≤ Q ^ c v.val i := by
  classical
  set N := Fintype.card ι
  obtain ⟨C₀, hC₀⟩ := exists_evertse (K := K) N
  refine ⟨max 0 C₀, le_max_left _ _, ?_⟩
  intro S₀ L c Q x μ hLinf hLfin hQ₀ hx hμm hμp hxΛ hxinf
  have hna (v : FinitePlace K) : IsNonarchimedean v.val := v.add_le
  have hxΛ' (l : Fin N) := mem_approxModule.1 (hxΛ l)
  -- Evertse's lemma with the forms indexed by `Fin N`, weights `Q ^ c v i`, and minima `μ` at the
  -- infinite places and `1` at the places of `S₀`.
  let e : Fin N ≃ ι := (Fintype.equivFin ι).symm
  let b : Basis (Fin N) K (ι → K) :=
    basisOfLinearIndependentOfCardEqFinrank' x hx (by simp [N])
  have hb : ⇑b = x := coe_basisOfLinearIndependentOfCardEqFinrank' x hx _
  let μ' : AbsoluteValue K ℝ → Fin N → ℝ := fun v j ↦ if IsNonarchimedean v then 1 else μ j
  obtain ⟨ξ, π, hξ, hinf, hfin⟩ := hC₀ (ι → K) S₀ (fun v m ↦ L v (e m)) b
    (fun v m ↦ Q ^ c v (e m)) μ' (fun v ↦ (hLinf v).comp e e.injective)
    (fun v hv ↦ (hLfin v hv).comp e e.injective) (fun _ _ ↦ Real.rpow_pos_of_pos hQ₀ _)
    (fun _ _ _ ↦ Real.rpow_pos_of_pos hQ₀ _)
    (fun v i j hij ↦ by
      simpa [μ', v.not_isNonarchimedean] using hμm i.isLt j.isLt (Fin.le_iff_val_le_val.1 hij))
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
    calc _ ≤ C₀ * (Q ^ c w.val (e (π w.val i)) * min (μ i) (μ j)) := h
      _ ≤ max 0 C₀ * (Q ^ c w.val (e (π w.val i)) * min (μ i) (μ j)) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_nonneg
          (Real.rpow_pos_of_pos hQ₀ _).le (le_min (hμp _ i.isLt).le (hμp _ j.isLt).le))
      _ = _ := by rw [Equiv.trans_apply, mul_assoc]
  · have h := hfin v hv ((π v.val).symm (e.symm i)) j
    simp only [μ', hna v, ↓reduceIte, min_self, mul_one, Equiv.apply_symm_apply] at h
    exact h

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
  have hna (v : FinitePlace K) : IsNonarchimedean v.val := v.add_le
  obtain ⟨y, σ, hspan, hint, hinf, hfin⟩ := hE S₀ L c Q x μ hLinf hLfin hQ₀ hx hμm hμp hxΛ hxinf
  refine ⟨y, σ, hspan, fun k p J hJ ↦ ?_⟩
  have hp : 0 < p := by
    obtain ⟨j, hj, -⟩ := hJ
    rw [← card_eq J]
    exact card_pos.2 ⟨j, hj⟩
  rw [mem_approxDomain]
  refine ⟨fun w T ↦ ?_, fun v hv T ↦ ?_, fun v hv s ↦ ?_⟩
  · -- At an infinite place: the refined determinant bound, with the gain on the top block.
    refine (AbsoluteValue.apply_wedgeForms_plucker_le w.val (L w.val) (σ w.val) hμm hμp
      (ν := fun t ↦ Q ^ c w.val t) (fun _ ↦ (Real.rpow_pos_of_pos hQ₀ _).le) hC₁ (hinf w) J hJ
      T).trans_eq ?_
    rw [rpow_wedgeExponent_of_not_isNonarchimedean w.not_isNonarchimedean hQ₀ hQ₁
      (by positivity) hμp hp]
    -- The two gains decide the same top-block condition, through possibly different instances.
    split_ifs <;> ring
  · -- At a place of `S₀`: the wedge of row bounds, with no constant.
    rw [rpow_wedgeExponent_of_isNonarchimedean (hna v) hQ₀]
    exact AbsoluteValue.apply_wedgeForms_plucker_le_prod v.val (hna v) (L v.val) _
      (fun i j ↦ hfin v hv i _) T
  · -- Outside `S₀`: a minor of a matrix of integral entries is integral.
    rw [plucker_apply]
    exact Matrix.abv_det_le_one_of_isNonarchimedean (hna v) fun _ _ ↦ hint v hv _ _

/-! ### The weight of the wedge domain -/

omit [NumberField K] in
/-- The product over the wedge forms of the constant times the minima attached to them is
`C ^ M · (∏ l, μ l) ^ e · μ (k - 1) / μ k`, since each index lies in `e` subsets and exactly one
subset is the top block. -/
private theorem prod_wedgeGain (σ : Fin (Fintype.card ι) ≃ ι) (hp : 0 < p)
    (hkp : k + p = Fintype.card ι) (μ : ℕ → ℝ) (C : ℝ) :
    ∏ T : Set.powersetCard ι p, C * ((if ∀ t ∈ (T : Finset ι), k ≤ (σ.symm t : ℕ) then
        μ (k - 1) / μ k else 1) * ∏ t ∈ (T : Finset ι), μ (σ.symm t)) =
      C ^ (Fintype.card ι).choose p *
        (∏ l : Fin (Fintype.card ι), μ l) ^ (Fintype.card ι - 1).choose (p - 1) *
          (μ (k - 1) / μ k) := by
  rw [prod_mul_distrib, prod_mul_distrib, prod_const, card_univ, Set.powersetCard.fintypeCard,
    Set.powersetCard.prod_prod hp fun t ↦ μ (σ.symm t), Equiv.prod_comp σ.symm fun l ↦ μ l]
  have hite : ∏ T : Set.powersetCard ι p, (if ∀ t ∈ (T : Finset ι), k ≤ (σ.symm t : ℕ) then
      μ (k - 1) / μ k else 1) = μ (k - 1) / μ k := by
    classical
    simp_rw [forall_le_symm_iff_eq_map_topBlock σ hkp]
    simp
  rw [hite]
  ring

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
  refine mul_ne_zero hC (mul_ne_zero ?_ (prod_ne_zero_iff.2 fun t _ ↦ hμ _ ((σ v).symm t).isLt))
  split_ifs
  · exact div_ne_zero (hμ _ (by omega)) (hμ _ hk)
  · exact one_ne_zero

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
`A ^ e · C ^ (M · [K : ℚ]) · (μ (k - 1) / μ k) ^ [K : ℚ]`, where `A = approxUpperConst S₀ L` is
the constant of Minkowski's second theorem for the domain, `e = (card ι - 1).choose (p - 1)` and
`M = (card ι).choose p`. -/
theorem rpow_approxWeight_wedgeExponent_le {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLinf : ∀ v : InfinitePlace K, LinearIndependent K (L v.val))
    (hLfin : ∀ v ∈ S₀, LinearIndependent K (L v.val)) (c : AbsoluteValue K ℝ → ι → ℝ)
    (hp : 0 < p) (hkp : k + p = Fintype.card ι) (σ : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι)
    (hC : 0 < C) (hQ₀ : 0 < Q) (hQ₁ : Q ≠ 1) :
    Q ^ approxWeight S₀ (wedgeExponent c p k σ
        ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q) ≤
      approxUpperConst S₀ L ^ (Fintype.card ι - 1).choose (p - 1) *
        C ^ ((Fintype.card ι).choose p * finrank ℚ K) *
          ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) (k - 1) /
            (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) k) ^ finrank ℚ K := by
  set μ := (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)
  have hμ (l : ℕ) (hl : l < Fintype.card ι) : 0 < μ l :=
    successiveMinimum_approx_pos hLinf hLfin c hQ₀ hl
  set A := approxUpperConst S₀ L
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

end TauCeti.NumberField
