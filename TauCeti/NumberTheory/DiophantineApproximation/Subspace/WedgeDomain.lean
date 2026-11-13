/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import TauCeti.Analysis.ExteriorPower.WedgeForms
public import TauCeti.NumberTheory.DiophantineApproximation.Subspace.Volume

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.Algebra.BigOperators.Finset.Powerset
import TauCeti.LinearAlgebra.LinearIndependent.Basic
import TauCeti.NumberTheory.NumberField.Global.Approximation.Evertse
import TauCeti.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# Wedge domains

Let `K` be a number field of degree `d`, `S₀` a finite set of finite places, and
`approxDomain S₀ L c Q` an approximation domain in `Kᴺ`, `N = #ι`. Let `x 0, …, x (N - 1)` be
vectors of its lattice `approxModule S₀ L c Q`, linearly independent over `K`, with
`|L v i (x l)|_v ≤ μ l * Q ^ c v i` at every infinite place for a positive nondecreasing `μ`; for
instance a family realizing the successive minima `μ` of the domain over `K`. For `k + p = N`,
Schmidt's proof of the Subspace Theorem passes to the `p`-th exterior power, through the wedge
forms `wedgeForms (L v) p` of the system, and needs the Plücker vectors of the `p`-subfamilies of
`x` meeting the first `k` indices to lie in one approximation domain `S(Q)` for these forms, whose
weight is small when `μ (k - 1) / μ k` is.

Evertse's lemma (`NumberField.exists_evertse`, with weights `ν v i = Q ^ c v i`) makes this true
after a triangular correction of `x`. It produces vectors `y j ∈ x j + span (x l, l < j)` and
permutations `σ v` of the forms with
`|L v (σ v i) (y j)|_v ≤ C * Q ^ c v (σ v i) * min (μ i) (μ j)` at the infinite places. Passing to
the wedges (`AbsoluteValue.apply_wedgeForms_plucker_le`) bounds the wedge indexed by a `p`-subset
`T` of forms on the Plücker vector of `y_J` by `Q ^ (∑ t ∈ T, c v t)` times
`C' * ∏ t ∈ T, μ (σ v⁻¹ t)`, and by a further factor `μ (k - 1) / μ k` when `T` is the top block
`σ v {k, …, N - 1}`. At the places of `S₀` the row bounds pass to the wedges without loss, and
away from `S₀` the Plücker coordinates of `y` stay integral.

`TauCeti.NumberField.wedgeExponent` records these bounds as exponents, absorbing the constant and
the minima into a logarithm to base `Q`: `S(Q)` is the approximation domain of `wedgeForms` with
exponents `wedgeExponent c σ μ C k p Q`, which move with `Q` but keep the geometry of numbers of
approximation domains applicable with constants uniform in `Q`. Its weight is exact: each index
of the forms lies in `e = (N - 1).choose (p - 1)` of the `p`-subsets and exactly one subset is
the top block, so the weight of `S(Q)` is `e` times the weight of `c` plus `d` times the
logarithm to base `Q` of `C ^ M * (∏ l, μ l) ^ e * (μ (k - 1) / μ k)`, with `M = N.choose p`.

## Main definitions

* `TauCeti.NumberField.wedgeExponent`: the exponents of the wedge domain `S(Q)`.

## Main results

* `TauCeti.NumberField.exists_plucker_mem_approxDomain_wedgeForms`: Bombieri–Gubler
  (7.44)–(7.45), the Plücker vectors of the corrected family lie in `S(Q)`, with a constant
  depending only on `K` and `N`.
* `TauCeti.NumberField.approxWeight_wedgeExponent` and
  `TauCeti.NumberField.rpow_approxWeight_wedgeExponent`: the weight of `S(Q)`.

## Implementation notes

The exponents are indexed by the underlying absolute value of a place, like every exponent family
of an approximation domain, and are told apart by `IsNonarchimedean`: at an infinite place the
correction `Real.logb Q (…)` is added, at a finite place it is not. Bombieri and Gubler normalize
the domain by (7.42) instead; absorbing the constant into the exponent makes that unnecessary.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  7.5.30 and (7.44)–(7.45).
-/

public section

noncomputable section

open Finset Module NumberField Set.powersetCard

namespace TauCeti.NumberField

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι]

open scoped Classical in
/-- **The exponents of the wedge domain** `S(Q)` (Bombieri–Gubler 7.5.30). At a `p`-subset `T`
of the forms, the exponent is `∑ t ∈ T, c v t`, plus, at an archimedean `v`, the logarithm to base
`Q` of `C * ∏ t ∈ T, μ (σ v⁻¹ t)`, multiplied by `μ (k - 1) / μ k` when every `σ v⁻¹ t` is at least
`k`, that is when `T` is the image of the top block `{k, …, N - 1}` under `σ v`. -/
def wedgeExponent (c : AbsoluteValue K ℝ → ι → ℝ)
    (σ : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι) (μ : ℕ → ℝ) (C : ℝ) (k p : ℕ) (Q : ℝ)
    (v : AbsoluteValue K ℝ) (T : Set.powersetCard ι p) : ℝ :=
  ∑ t ∈ (T : Finset ι), c v t + if IsNonarchimedean v then 0 else
    Real.logb Q (C * ((if ∀ t ∈ (T : Finset ι), k ≤ ((σ v).symm t : ℕ) then μ (k - 1) / μ k
      else 1) * ∏ t ∈ (T : Finset ι), μ ((σ v).symm t)))

/-- The exponent of the wedge domain at an infinite place. -/
@[simp]
theorem wedgeExponent_infinitePlace (c : AbsoluteValue K ℝ → ι → ℝ)
    (σ : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι) (μ : ℕ → ℝ) (C : ℝ) (k p : ℕ) (Q : ℝ)
    (w : InfinitePlace K) (T : Set.powersetCard ι p) :
    wedgeExponent c σ μ C k p Q w.1 T = ∑ t ∈ (T : Finset ι), c w.1 t +
      Real.logb Q (C * ((if ∀ t ∈ (T : Finset ι), k ≤ ((σ w.1).symm t : ℕ) then
        μ (k - 1) / μ k else 1) * ∏ t ∈ (T : Finset ι), μ ((σ w.1).symm t))) := by
  simp [wedgeExponent, w.not_isNonarchimedean]

variable [NumberField K]

/-- The exponent of the wedge domain at a finite place is the sum of the exponents of `c`. -/
@[simp]
theorem wedgeExponent_finitePlace (c : AbsoluteValue K ℝ → ι → ℝ)
    (σ : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι) (μ : ℕ → ℝ) (C : ℝ) (k p : ℕ) (Q : ℝ)
    (v : FinitePlace K) (T : Set.powersetCard ι p) :
    wedgeExponent c σ μ C k p Q v.1 T = ∑ t ∈ (T : Finset ι), c v.1 t := by
  have hv : IsNonarchimedean (v.1 : K → ℝ) := v.add_le
  simp [wedgeExponent, hv]

/-- Evertse's lemma for a family in an approximation domain: the correction `y` of `x` is
triangular, linearly independent and integral away from `S₀`, and after permuting the forms by
`σ v` it satisfies `|L v (σ v i) (y j)|_v ≤ C * Q ^ c v (σ v i) * min (μ i) (μ j)` at the infinite
places and `|L v i (y j)|_v ≤ Q ^ c v i` at the places of `S₀`. -/
private theorem exists_evertse_approxModule :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (S₀ : Finset (FinitePlace K))
      (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) (c : AbsoluteValue K ℝ → ι → ℝ) (Q : ℝ)
      (μ : ℕ → ℝ) (x : Fin (Fintype.card ι) → ι → K),
      (∀ v : InfinitePlace K, LinearIndependent K (L v.1)) →
      (∀ v ∈ S₀, LinearIndependent K (L v.1)) → 0 < Q →
      MonotoneOn μ (Set.Iio (Fintype.card ι)) → (∀ l < Fintype.card ι, 0 < μ l) →
      LinearIndependent K x → (∀ l, x l ∈ approxModule S₀ L c Q) →
      (∀ (v : InfinitePlace K) i l, v (L v.1 i (x l)) ≤ μ l * Q ^ c v.1 i) →
      ∃ (y : Fin (Fintype.card ι) → ι → K) (σ : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι),
        LinearIndependent K y ∧ (∀ j, y j - x j ∈ Submodule.span K (x '' Set.Iio j)) ∧
        (∀ v : FinitePlace K, v ∉ S₀ → ∀ j t, v (y j t) ≤ 1) ∧
        (∀ (w : InfinitePlace K) i j,
          w (L w.1 (σ w.1 i) (y j)) ≤ C * Q ^ c w.1 (σ w.1 i) * min (μ i) (μ j)) ∧
        ∀ v ∈ S₀, ∀ i j, v (L v.1 i (y j)) ≤ Q ^ c v.1 i := by
  classical
  obtain ⟨C₀, hC₀⟩ := exists_evertse (K := K) (Fintype.card ι)
  refine ⟨max C₀ 1, le_max_right _ _,
    fun S₀ L c Q μ x hLinf hLfin hQ hμm hμp hx hxΛ hxinf ↦ ?_⟩
  -- The data of Evertse's lemma: the forms reindexed by `Fin #ι`, the weights `Q ^ c v i`, and
  -- the minima `μ` at the infinite places, `1` at the finite ones.
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hcard : Fintype.card (Fin (Fintype.card ι)) = finrank K (ι → K) := by simp
  let b : Basis (Fin (Fintype.card ι)) K (ι → K) :=
    Basis.mk hx (hx.span_eq_top_of_card_eq_finrank' hcard).ge
  let μ' : AbsoluteValue K ℝ → Fin (Fintype.card ι) → ℝ :=
    fun v j ↦ if IsNonarchimedean v then 1 else μ j
  have hμ'inf (w : InfinitePlace K) (j) : μ' w.1 j = μ j := by
    simp [μ', w.not_isNonarchimedean]
  have hμ'fin (v : FinitePlace K) (j) : μ' v.1 j = 1 := by
    have hv : IsNonarchimedean (v.1 : K → ℝ) := v.add_le
    simp [μ', hv]
  obtain ⟨ξ, π, hξ, hbinf, hbfin⟩ := hC₀ (ι → K) S₀ (fun v i ↦ L v (e i)) b
    (fun v i ↦ Q ^ c v (e i)) μ' (fun w ↦ (hLinf w).comp e e.injective)
    (fun v hv ↦ (hLfin v hv).comp e e.injective) (fun _ _ ↦ Real.rpow_pos_of_pos hQ _)
    (fun _ _ _ ↦ Real.rpow_pos_of_pos hQ _)
    (fun w i j hij ↦ by
      simp only [hμ'inf]
      exact hμm i.isLt j.isLt (by exact_mod_cast hij))
    (fun v _ i j _ ↦ by simp only [hμ'fin, le_refl])
    (fun w i j ↦ by
      rw [hμ'inf, Basis.mk_apply, mul_comm]
      exact hxinf w (e i) j)
    (fun v hv i j ↦ by
      rw [hμ'fin, mul_one, Basis.mk_apply, ← abs_of_pos hQ]
      exact (mem_approxModule.1 (hxΛ j)).1 v hv (e i))
  simp only [b, Basis.coe_mk] at hbinf hbfin
  set y : Fin (Fintype.card ι) → ι → K := fun j ↦ x j + ∑ l ∈ univ.filter (· < j), ξ j l • x l
    with hy
  -- The corrected family is triangular over `x`, hence linearly independent.
  have hyx (j) : y j - x j ∈ Submodule.span K (x '' Set.Iio j) := by
    rw [hy, add_sub_cancel_left]
    exact Submodule.sum_mem _ fun l hl ↦ Submodule.smul_mem _ _
      (Submodule.subset_span ⟨l, (mem_filter.1 hl).2, rfl⟩)
  refine ⟨y, fun v ↦ (π v).trans e, hx.of_sub_mem_span_image_Iio hyx, hyx, fun v hv j t ↦ ?_,
    fun w i j ↦ ?_, fun v hv i j ↦ ?_⟩
  · -- Away from `S₀` the corrected vectors stay integral.
    have hsum : v (∑ l ∈ univ.filter (· < j), ξ j l * x l t) ≤ 1 :=
      Finset.sum_induction _ (fun a ↦ v a ≤ 1)
        (fun a b ha hb ↦ (v.add_le a b).trans (max_le ha hb)) (by simp) fun l _ ↦ by
          rw [map_mul]
          exact (mul_le_of_le_one_left (apply_nonneg _ _) (hξ j l v hv)).trans
            ((mem_approxModule.1 (hxΛ l)).2 v hv t)
    simp only [hy, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact (v.add_le _ _).trans (max_le ((mem_approxModule.1 (hxΛ j)).2 v hv t) hsum)
  · have h := hbinf w i j
    rw [hμ'inf, hμ'inf] at h
    refine h.trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _)
      (mul_nonneg (Real.rpow_nonneg hQ.le _) (le_min (hμp _ i.isLt).le (hμp _ j.isLt).le))
  · have h := hbfin v hv ((π v.1).symm (e.symm i)) j
    simp only [Equiv.apply_symm_apply, hμ'fin, min_self, mul_one] at h
    exact h

/-- **The Plücker vectors of a corrected family lie in the wedge domain** (Bombieri–Gubler
(7.44)–(7.45)). There is a constant `C > 0`, depending only on `K` and `#ι`, with the following
property. Let `0 < Q ≠ 1`, let the forms `L v` be linearly independent at the infinite places and
the places of `S₀`, let `μ` be positive and nondecreasing below `#ι`, and let `x` be `#ι` vectors
of `approxModule S₀ L c Q`, linearly independent over `K`, with `|L v i (x l)|_v ≤ μ l * Q ^ c v i`
at every infinite place. Then there are vectors `y j ∈ x j + span (x l, l < j)`, linearly
independent, and permutations `σ v` such that for all `k` and `p` the Plücker vector of every
`p`-subfamily of `y` meeting the first `k` indices lies in the approximation domain of the wedge
forms with exponents `wedgeExponent c σ μ C k p Q`. -/
theorem exists_plucker_mem_approxDomain_wedgeForms [LinearOrder ι] :
    ∃ C : ℝ, 0 < C ∧ ∀ (S₀ : Finset (FinitePlace K))
      (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) (c : AbsoluteValue K ℝ → ι → ℝ) (Q : ℝ)
      (μ : ℕ → ℝ) (x : Fin (Fintype.card ι) → ι → K),
      (∀ v : InfinitePlace K, LinearIndependent K (L v.1)) →
      (∀ v ∈ S₀, LinearIndependent K (L v.1)) → 0 < Q → Q ≠ 1 →
      MonotoneOn μ (Set.Iio (Fintype.card ι)) → (∀ l < Fintype.card ι, 0 < μ l) →
      LinearIndependent K x → (∀ l, x l ∈ approxModule S₀ L c Q) →
      (∀ (v : InfinitePlace K) i l, v (L v.1 i (x l)) ≤ μ l * Q ^ c v.1 i) →
      ∃ (y : Fin (Fintype.card ι) → ι → K) (σ : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι),
        LinearIndependent K y ∧ (∀ j, y j - x j ∈ Submodule.span K (x '' Set.Iio j)) ∧
        ∀ k p (J : Set.powersetCard (Fin (Fintype.card ι)) p),
          (∃ j ∈ J, (j : ℕ) < k) →
          plucker (y ∘ ofFinEmbEquiv.symm J) ∈
            approxDomain S₀ (fun v ↦ wedgeForms (L v) p) (wedgeExponent c σ μ C k p Q) Q := by
  obtain ⟨C₁, hC₁, hE⟩ := exists_evertse_approxModule (K := K) (ι := ι)
  refine ⟨(Fintype.card ι).factorial * C₁ ^ Fintype.card ι, by positivity,
    fun S₀ L c Q μ x hLinf hLfin hQ hQ1 hμm hμp hx hxΛ hxinf ↦ ?_⟩
  obtain ⟨y, σ, hylin, hyx, hyint, hinf, hfin⟩ :=
    hE S₀ L c Q μ x hLinf hLfin hQ hμm hμp hx hxΛ hxinf
  refine ⟨y, σ, hylin, hyx, fun k p J hJ ↦ ?_⟩
  obtain ⟨j₀, hj₀J, hj₀k⟩ := hJ
  have hp : 0 < p := by
    rw [← Set.powersetCard.card_eq J]
    exact card_pos.2 ⟨j₀, hj₀J⟩
  refine mem_approxDomain.2 ⟨fun w T ↦ ?_, fun v hv T ↦ ?_, fun v hv T ↦ ?_⟩
  · -- At an infinite place: the row bounds pass to the wedges, with the top-block gain.
    have hmain := AbsoluteValue.apply_wedgeForms_plucker_le w.1 (L w.1) (σ w.1) hμm hμp
      (ν := fun t ↦ Q ^ c w.1 t) (fun _ ↦ Real.rpow_nonneg hQ.le _) (by positivity) (hinf w) J
      ⟨j₀, hj₀J, hj₀k⟩ T
    rw [max_eq_right hC₁] at hmain
    refine hmain.trans_eq ?_
    rw [wedgeExponent_infinitePlace, Real.rpow_add hQ, Real.rpow_sum_of_pos hQ,
      Real.rpow_logb hQ hQ1]
    · -- The two sides differ only in the order of the factors and in the `Decidable` instance of
      -- the top-block condition.
      rw [mul_left_comm]
      congr
    · refine mul_pos (by positivity) (mul_pos ?_ (prod_pos fun t _ ↦ hμp _ (Fin.is_lt _)))
      split_ifs with hT
      · -- A nonempty top block forces `k < #ι`.
        obtain ⟨t₀, ht₀⟩ := card_pos.1 ((Set.powersetCard.card_eq T).symm ▸ hp)
        have hk := (hT t₀ ht₀).trans_lt ((σ w.1).symm t₀).is_lt
        exact div_pos (hμp _ (by omega)) (hμp _ hk)
      · exact one_pos
  · -- At a place of `S₀`: the row bounds pass to the wedges without loss.
    rw [wedgeExponent_finitePlace, Real.rpow_sum_of_pos hQ]
    exact AbsoluteValue.apply_wedgeForms_plucker_le_prod v.1 v.add_le (L v.1) _
      (fun i j ↦ hfin v hv i _) T
  · -- Away from `S₀`: the Plücker coordinates are minors of an integral matrix.
    rw [plucker_apply]
    exact (Matrix.abv_det_le_prod_of_le _ v.add_le (b := fun _ ↦ 1)
      fun i j ↦ hyint v hv _ _).trans_eq prod_const_one

/-- **The weight of the wedge domain** (Bombieri–Gubler 7.5.30). For `k + p = #ι` with `p ≠ 0`,
`C > 0` and `μ` positive below `#ι`, the weight of `wedgeExponent c σ μ C k p Q` is
`e = (#ι - 1).choose (p - 1)` times the weight of `c` plus `[K : ℚ]` times the logarithm to base
`Q` of `C ^ M * (∏ l, μ l) ^ e * (μ (k - 1) / μ k)`, where `M = (#ι).choose p` is the number of
`p`-subsets. -/
theorem approxWeight_wedgeExponent (S₀ : Finset (FinitePlace K)) (c : AbsoluteValue K ℝ → ι → ℝ)
    (σ : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι) {μ : ℕ → ℝ}
    (hμ : ∀ l < Fintype.card ι, 0 < μ l) {C : ℝ} (hC : 0 < C) {k p : ℕ} (hp : p ≠ 0)
    (h : k + p = Fintype.card ι) (Q : ℝ) :
    approxWeight S₀ (wedgeExponent c σ μ C k p Q) =
      (Fintype.card ι - 1).choose (p - 1) * approxWeight S₀ c +
        finrank ℚ K * Real.logb Q (C ^ (Fintype.card ι).choose p *
          (∏ l : Fin (Fintype.card ι), μ l) ^ (Fintype.card ι - 1).choose (p - 1) *
            (μ (k - 1) / μ k)) := by
  set e := (Fintype.card ι - 1).choose (p - 1) with he_def
  set A := C ^ (Fintype.card ι).choose p * (∏ l : Fin (Fintype.card ι), μ l) ^ e *
    (μ (k - 1) / μ k)
  -- Every index lies in `e` of the `p`-subsets.
  obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero hp
  have he : e = (Fintype.card ι - 1).choose q := by rw [he_def, hq, Nat.succ_sub_one]
  have hmem (s : Finset ι) : s ∈ Finset.powersetCard (q + 1) univ ↔ s ∈ Set.powersetCard ι p := by
    simp [Set.powersetCard.mem_iff, hq]
  have hsum (f : ι → ℝ) : ∑ T : Set.powersetCard ι p, ∑ t ∈ (T : Finset ι), f t =
      e * ∑ t, f t := by
    rw [← Finset.sum_subtype _ hmem (fun s ↦ ∑ t ∈ s, f t), sum_powersetCard_succ_sum, card_univ,
      nsmul_eq_mul, he]
  have hprod (g : ι → ℝ) : ∏ T : Set.powersetCard ι p, ∏ t ∈ (T : Finset ι), g t =
      (∏ t, g t) ^ e := by
    rw [← Finset.prod_subtype _ hmem (fun s ↦ ∏ t ∈ s, g t), prod_powersetCard_succ_prod,
      card_univ, he]
  have hM : Fintype.card (Set.powersetCard ι p) = (Fintype.card ι).choose p := by
    rw [← Nat.card_eq_fintype_card, Set.powersetCard.card, Nat.card_eq_fintype_card]
  have hinf (w : InfinitePlace K) :
      ∑ T, wedgeExponent c σ μ C k p Q w.1 T = e * ∑ i, c w.1 i + Real.logb Q A := by
    classical
    simp_rw [wedgeExponent_infinitePlace]
    rw [sum_add_distrib, hsum, ← Real.logb_prod _ _ fun T _ ↦ ?_]
    · congr 2
      -- Exactly one `p`-subset, the image of the top block, carries the gain.
      simp_rw [forall_le_symm_iff_eq_map_topBlock _ h]
      rw [prod_mul_distrib, prod_mul_distrib, prod_const, card_univ, hM, Fintype.prod_ite_eq',
        hprod, Equiv.prod_comp (σ w.1).symm (fun l ↦ μ l)]
      ring
    · refine mul_ne_zero hC.ne'
        (mul_ne_zero ?_ (prod_ne_zero_iff.2 fun t _ ↦ (hμ _ (Fin.is_lt _)).ne'))
      split_ifs
      · exact div_ne_zero (hμ _ (by omega)).ne' (hμ _ (by omega)).ne'
      · exact one_ne_zero
  have hfin (v : FinitePlace K) : ∑ T, wedgeExponent c σ μ C k p Q v.1 T = e * ∑ i, c v.1 i := by
    simp_rw [wedgeExponent_finitePlace]
    exact hsum _
  have hd : ∑ v : InfinitePlace K, (v.mult : ℝ) = finrank ℚ K := by
    exact_mod_cast InfinitePlace.sum_mult_eq
  simp only [approxWeight_def, hinf, hfin, ← hd, mul_add, sum_add_distrib,
    mul_left_comm _ (e : ℝ), ← mul_sum, ← sum_mul]
  ring

/-- **The weight of the wedge domain**, multiplicatively: for `0 < Q ≠ 1`,
`Q ^ weight (S(Q)) = Q ^ (e * weight c) * (C ^ M * (∏ l, μ l) ^ e * (μ (k - 1) / μ k)) ^ [K : ℚ]`,
with `e = (#ι - 1).choose (p - 1)` and `M = (#ι).choose p`. -/
theorem rpow_approxWeight_wedgeExponent (S₀ : Finset (FinitePlace K))
    (c : AbsoluteValue K ℝ → ι → ℝ) (σ : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι)
    {μ : ℕ → ℝ} (hμ : ∀ l < Fintype.card ι, 0 < μ l) {C : ℝ} (hC : 0 < C) {k p : ℕ}
    (hp : p ≠ 0) (h : k + p = Fintype.card ι) {Q : ℝ} (hQ : 0 < Q) (hQ1 : Q ≠ 1) :
    Q ^ approxWeight S₀ (wedgeExponent c σ μ C k p Q) =
      Q ^ ((Fintype.card ι - 1).choose (p - 1) * approxWeight S₀ c) *
        (C ^ (Fintype.card ι).choose p *
          (∏ l : Fin (Fintype.card ι), μ l) ^ (Fintype.card ι - 1).choose (p - 1) *
            (μ (k - 1) / μ k)) ^ finrank ℚ K := by
  have hpos : 0 < C ^ (Fintype.card ι).choose p *
      (∏ l : Fin (Fintype.card ι), μ l) ^ (Fintype.card ι - 1).choose (p - 1) *
        (μ (k - 1) / μ k) :=
    mul_pos (mul_pos (pow_pos hC _) (pow_pos (prod_pos fun (l : Fin (Fintype.card ι)) _ ↦
      hμ l l.is_lt) _))
      (div_pos (hμ _ (by omega)) (hμ _ (by omega)))
  rw [approxWeight_wedgeExponent S₀ c σ hμ hC hp h, Real.rpow_add hQ, mul_comm (finrank ℚ K : ℝ),
    Real.rpow_mul_natCast hQ.le, Real.rpow_logb hQ hQ1 hpos]

end TauCeti.NumberField
