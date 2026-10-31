/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Resultant.Coleman
public import TauCeti.RingTheory.PowerSeries.Entire.Majorant
import TauCeti.Algebra.Order.BigOperators.Antitone
import TauCeti.Algebra.Order.BigOperators.ProdSubProd

/-!
# Coefficient bounds for Coleman's transform

Let `R` be an ultrametric seminormed commutative ring with `‖1‖ = 1`. Let `P = ∑ aⱼ Tʲ` and
`B = ∑ bₗ Tˡ` be polynomials over `R` with `B(0) = 0`, let `ρ` be a nonnegative antitone sequence
with `‖aⱼ‖ ≤ ∏ i < j, ρᵢ`, and let `β` satisfy `‖bₗ‖ ρₜˡ ≤ βₜ` for all `t` and all `l ≥ 1`. Then
every bounded Coleman transform `D_(n,m)(B, P)` satisfies

`‖coeff k D_(n,m)(B, P)‖ ≤ ∏ t < k, βₜ` (`Polynomial.norm_coeff_colemanDBounded_le`).

If `P = ∏ (1 - αᵢ T)` with `‖αᵢ‖ ≤ ρᵢ`, then `D(B, P) = ∏ (1 - B(αᵢ) T)` and the bound is the
ultrametric estimate for the elementary symmetric functions of the `B(αᵢ)`. The theorem asserts
the same bound for every `P` obeying the coefficient bounds, over any coefficient ring, with no
access to roots. It is uniform in the ranks `n` and `m`, so it applies to all truncations of an
entire series `F` with Newton majorant `ρ` along an entire series `B` with `B(0) = 0`, with
`βₜ = β_B(ρₜ)` the Coleman majorant (`PowerSeries.norm_coeff_colemanDBounded_trunc_le`). These
products are the coefficient bounds of an entire series, so they control the limit of the finite
transforms that defines Coleman's transform with entire functional input.

The estimate is read off the Leibniz expansion of the Sylvester matrix defining the resultant,
term by term. In a nonzero term, the permutation `σ` of the `n + m` columns moves each of the
first `n` columns `x` (carrying coefficients of `1 - T B(X)`) down to a row `σ x ≥ x`, picking
`b_(σ x - x) T` when `σ x > x`, and moves each of the last `m` columns up, picking
`a_(x - σ x)`. Count both kinds of moves across each gap between consecutive rows: a column moved
across `j` gaps is charged `ρ₀, …, ρⱼ₋₁` in order on the `a` side, while on the `b` side every gap
it crosses is charged `ρ_r`, where `r` is its rank by decreasing target row. At each gap the two
counts agree, and the `a` charges are never larger than the `b` charges after sorting, so
`∏ ‖a‖ ≤ ∏ ρ_r ^ (σ x - x)` (`Finset.prod_le_prod_of_card_filter_lt_le`). The ranks enumerate the
moved columns, so each term is bounded by `∏ t < k, βₜ`.

## Main results

* `Polynomial.norm_coeff_colemanDBounded_le`: the uniform coefficient bound for the bounded
  Coleman transform of polynomials.
* `PowerSeries.norm_coeff_colemanDBounded_trunc_le`: the bound `∏ i < k, β_B(ρᵢ)` for the
  transforms of truncations of power series.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127** (1997),
  417–479, Appendix A3.
-/

public section

open Equiv Finset

namespace Polynomial

section Crossing

/-! ### Charging moves across the gaps between rows

For a permutation `σ` of `Fin L`, a point `x` with `σ x < x` crosses the gaps `c` with
`σ x < c ≤ x`, at depth `x - c`, and a point with `x < σ x` crosses the gaps `c` with
`x < c ≤ σ x`. The points with `x < σ x` are ranked by decreasing image. -/

variable {L : ℕ} (σ : Perm (Fin L))

/-- The rank of `x` among the points moved forward by `σ`, ordered by decreasing image. -/
private def upRank (x : Fin L) : ℕ :=
  #{y : Fin L | (y : ℕ) < σ y ∧ (σ x : ℕ) < σ y}

/-- Distinct forward-moved points have distinct ranks, since their images are distinct. -/
private theorem upRank_injOn : Set.InjOn (upRank σ) {x : Fin L | (x : ℕ) < σ x} := by
  intro x hx y hy hxy
  by_contra hne
  have hσ : (σ x : ℕ) ≠ σ y := fun h ↦ hne (σ.injective (Fin.ext h))
  -- the point with the smaller image has the larger rank
  have key {x y : Fin L} (hy : (y : ℕ) < σ y) (h : (σ x : ℕ) < σ y) : upRank σ y < upRank σ x :=
    card_lt_card <| (ssubset_iff_of_subset fun z hz ↦ by
      simp only [mem_filter, mem_univ, true_and] at hz ⊢
      exact ⟨hz.1, h.trans hz.2⟩).2
        ⟨y, by simp only [mem_filter, mem_univ, true_and]; exact ⟨hy, h⟩,
          by simp only [mem_filter, mem_univ, lt_irrefl, and_false, not_false_eq_true]⟩
  rcases lt_or_gt_of_ne hσ with h | h
  · exact (key hy h).ne hxy.symm
  · exact (key hx h).ne hxy

/-- On a set of forward-moved points closed under passing to larger images, the ranks enumerate
`range` of its size. -/
private theorem image_upRank {S : Finset (Fin L)} (hS : ∀ x ∈ S, (x : ℕ) < σ x)
    (hclosed : ∀ x ∈ S, ∀ y : Fin L, (y : ℕ) < σ y → (σ x : ℕ) < σ y → y ∈ S) :
    S.image (upRank σ) = range #S := by
  have hinj : Set.InjOn (upRank σ) S := (upRank_injOn σ).mono fun x hx ↦ hS x hx
  refine eq_of_subset_of_card_le (fun r hr ↦ ?_) (by rw [card_range, card_image_of_injOn hinj])
  obtain ⟨x, hx, rfl⟩ := mem_image.1 hr
  refine mem_range.2 ((card_le_card fun y hy ↦ ?_).trans_lt
    (card_erase_lt_of_mem hx))
  simp only [mem_filter, mem_univ, true_and] at hy
  exact mem_erase.2 ⟨fun h ↦ (h ▸ hy.2).false, hclosed x hx y hy.1 hy.2⟩

/-- On a set of forward-moved points closed under passing to larger images, exactly `t` points
have rank below `t`, for `t` at most its size. -/
private theorem card_filter_upRank_lt {S : Finset (Fin L)} (hS : ∀ x ∈ S, (x : ℕ) < σ x)
    (hclosed : ∀ x ∈ S, ∀ y : Fin L, (y : ℕ) < σ y → (σ x : ℕ) < σ y → y ∈ S) {t : ℕ}
    (ht : t ≤ #S) : #{x ∈ S | upRank σ x < t} = t := by
  have himage := image_upRank σ hS hclosed
  have hfi : {x ∈ S | upRank σ x < t}.image (upRank σ) = range t := by
    ext r
    simp only [mem_image, mem_filter, mem_range]
    constructor
    · rintro ⟨x, ⟨-, hx⟩, rfl⟩
      exact hx
    · intro hr
      obtain ⟨x, hx, rfl⟩ := mem_image.1 (himage ▸ mem_range.2 (hr.trans_le ht))
      exact ⟨x, ⟨hx, hr⟩, rfl⟩
  rw [← card_image_of_injOn ((upRank_injOn σ).mono fun x hx ↦ hS x (mem_filter.1 hx).1), hfi,
    card_range]

/-- The products of a sequence along the ranks of the forward-moved points are its products over
an initial segment. -/
private theorem prod_upRank (β : ℕ → ℝ) :
    ∏ x ∈ {x : Fin L | (x : ℕ) < σ x}, β (upRank σ x) =
      ∏ t ∈ range #{x : Fin L | (x : ℕ) < σ x}, β t := by
  rw [← image_upRank σ (fun x hx ↦ (mem_filter.1 hx).2) fun x _ y hy _ ↦ by simpa using hy,
    prod_image fun x hx y hy ↦ upRank_injOn σ (by simpa using hx) (by simpa using hy)]

/-- At every gap, as many points move forward across it as move backward. -/
private theorem card_cross_forward (c : ℕ) :
    #{x : Fin L | (x : ℕ) < c ∧ c ≤ σ x} = #{x : Fin L | (σ x : ℕ) < c ∧ c ≤ x} := by
  have hσ : #{x : Fin L | (σ x : ℕ) < c} = #{x : Fin L | (x : ℕ) < c} :=
    card_equiv σ fun x ↦ by simp
  have h₁ := card_filter_add_card_filter_not (s := {x : Fin L | (x : ℕ) < c})
    fun x ↦ (σ x : ℕ) < c
  have h₂ := card_filter_add_card_filter_not (s := {x : Fin L | (σ x : ℕ) < c})
    fun x ↦ (x : ℕ) < c
  simp only [filter_filter, not_lt] at h₁ h₂
  have h₃ : #{x : Fin L | (σ x : ℕ) < c ∧ (x : ℕ) < c} =
      #{x : Fin L | (x : ℕ) < c ∧ (σ x : ℕ) < c} := by
    simp only [and_comm]
  omega

/-- **Charges at one gap.** If `σ` moves the points below `N` forward and the others backward,
then for every `t`, at most as many backward moves cross the gap `c` at depth below `t` as
forward moves of rank below `t`. -/
private theorem card_cross_backward_le {N : ℕ} (hfwd : ∀ x : Fin L, (x : ℕ) < N → (x : ℕ) ≤ σ x)
    (hbwd : ∀ x : Fin L, N ≤ (x : ℕ) → (σ x : ℕ) ≤ x) (c t : ℕ) :
    #{x : Fin L | ((σ x : ℕ) < c ∧ c ≤ x) ∧ (x : ℕ) - c < t} ≤
      #{x : Fin L | ((x : ℕ) < c ∧ c ≤ σ x) ∧ upRank σ x < t} := by
  -- the forward-moved points landing beyond the gap
  set P : Finset (Fin L) := {y : Fin L | (y : ℕ) < σ y ∧ c ≤ σ y}
  have hPpos : ∀ x ∈ P, (x : ℕ) < σ x := fun x hx ↦ (mem_filter.1 hx).2.1
  have hPclosed : ∀ x ∈ P, ∀ y : Fin L, (y : ℕ) < σ y → (σ x : ℕ) < σ y → y ∈ P :=
    fun x hx y hy hxy ↦ by
      simp only [P, mem_filter, mem_univ, true_and] at hx ⊢
      exact ⟨hy, hx.2.trans hxy.le⟩
  have himage : P.image (upRank σ) = range #P := image_upRank σ hPpos hPclosed
  have hrank : ∀ x ∈ P, upRank σ x < #P := fun x hx ↦
    mem_range.1 (himage ▸ mem_image_of_mem _ hx)
  have hflow := card_cross_forward σ c
  rcases le_or_gt #P t with hPt | htP
  · -- every forward move across the gap has rank below `t`
    calc #{x : Fin L | ((σ x : ℕ) < c ∧ c ≤ x) ∧ (x : ℕ) - c < t}
        ≤ #{x : Fin L | (σ x : ℕ) < c ∧ c ≤ x} := card_le_card fun x hx ↦ by
          simp only [mem_filter] at hx ⊢
          exact ⟨hx.1, hx.2.1⟩
      _ = #{x : Fin L | ((x : ℕ) < c ∧ c ≤ σ x) ∧ upRank σ x < t} := by
        rw [← hflow]
        congr 1
        refine filter_congr fun x _ ↦ ⟨fun hx ↦ ⟨hx, ?_⟩, And.left⟩
        refine (hrank x ?_).trans_le hPt
        simp only [P, mem_filter, mem_univ, true_and]
        exact ⟨by omega, hx.2⟩
  -- otherwise the `t` highest-landing forward moves all cross the gap, except those starting
  -- beyond it, of which there are at most `N - c`
  have hP : #{x ∈ P | upRank σ x < t} = t := card_filter_upRank_lt σ hPpos hPclosed htP.le
  have hhigh : #(P.filter fun x : Fin L ↦ c ≤ (x : ℕ)) ≤ N - c := by
    refine (card_le_card_of_injOn (fun x : Fin L ↦ (x : ℕ)) (t := Ico c N) (fun x hx ↦ ?_)
      fun x _ y _ h ↦ Fin.ext h).trans_eq (Nat.card_Ico c N)
    simp only [P, coe_filter, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx
    have : (x : ℕ) < N := by
      by_contra! hN
      have := hbwd x hN
      omega
    simp [hx.2, this]
  have hlow : #{x : Fin L | ((σ x : ℕ) < c ∧ c ≤ x) ∧ (x : ℕ) - c < t} ≤ c + t - max c N := by
    refine (card_le_card_of_injOn (fun x : Fin L ↦ (x : ℕ)) (t := Ico (max c N) (c + t))
      (fun x hx ↦ ?_) fun x _ y _ h ↦ Fin.ext h).trans_eq (Nat.card_Ico _ _)
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx
    have : N ≤ (x : ℕ) := by
      by_contra! hN
      have := hfwd x hN
      omega
    simp only [coe_Ico, Set.mem_Ico, max_le_iff]
    omega
  have hsplit : #{x ∈ P | upRank σ x < t} ≤
      #{x : Fin L | ((x : ℕ) < c ∧ c ≤ σ x) ∧ upRank σ x < t} +
        #(P.filter fun x : Fin L ↦ c ≤ (x : ℕ)) := by
    refine (card_le_card fun x hx ↦ ?_).trans (card_union_le _ _)
    simp only [P, mem_filter, mem_univ, true_and, mem_union] at hx ⊢
    by_cases hxc : (x : ℕ) < c
    · exact Or.inl ⟨⟨hxc, hx.1.2⟩, hx.2⟩
    · exact Or.inr ⟨hx.1, not_lt.1 hxc⟩
  omega

/-- **Crossing estimate.** If `σ` moves the points below `N` forward and the others backward, and
`ρ` is a nonnegative antitone sequence, then the product over the backward moves of
`∏ i < x - σ x, ρ i` is at most the product over the forward moves of
`ρ (rank x) ^ (σ x - x)`. -/
private theorem prod_prod_range_le_prod_pow_upRank {N : ℕ}
    (hfwd : ∀ x : Fin L, (x : ℕ) < N → (x : ℕ) ≤ σ x)
    (hbwd : ∀ x : Fin L, N ≤ (x : ℕ) → (σ x : ℕ) ≤ x) {ρ : ℕ → ℝ} (hρ₀ : ∀ i, 0 ≤ ρ i)
    (hρ : Antitone ρ) :
    ∏ x : Fin L, ∏ i ∈ range ((x : ℕ) - σ x), ρ i ≤
      ∏ x : Fin L, ρ (upRank σ x) ^ ((σ x : ℕ) - x) := by
  -- distribute both sides over the gaps crossed
  have hl (x : Fin L) : ∏ i ∈ range ((x : ℕ) - σ x), ρ i = ∏ c ∈ Ioc (σ x : ℕ) x, ρ (x - c) :=
    prod_nbij' (fun i ↦ x - i) (fun c ↦ x - c) (fun i hi ↦ by simp at hi ⊢; omega)
      (fun c hc ↦ by simp at hc ⊢; omega) (fun i hi ↦ by simp at hi; omega)
      (fun c hc ↦ by simp at hc; omega) fun i hi ↦ by simp at hi; congr 1; omega
  have hr (x : Fin L) :
      ρ (upRank σ x) ^ ((σ x : ℕ) - x) = ∏ c ∈ Ioc (x : ℕ) (σ x), ρ (upRank σ x) := by
    rw [prod_const, Nat.card_Ioc]
  simp_rw [hl, hr]
  rw [prod_comm' (t' := range (L + 1)) (s' := fun c ↦ {x : Fin L | (σ x : ℕ) < c ∧ c ≤ x})
      fun x c ↦ by simp only [mem_univ, mem_Ioc, mem_filter, mem_range, true_and]; omega,
    prod_comm' (t' := range (L + 1)) (s' := fun c ↦ {x : Fin L | (x : ℕ) < c ∧ c ≤ σ x})
      fun x c ↦ by simp only [mem_univ, mem_Ioc, mem_filter, mem_range, true_and]; omega]
  refine prod_le_prod₀ (fun c _ ↦ prod_nonneg fun x _ ↦ hρ₀ _) fun c _ ↦ ?_
  -- compare the depths and the ranks at the gap `c`
  set D : Finset (Fin L) := {x | (σ x : ℕ) < c ∧ c ≤ x}
  set U : Finset (Fin L) := {x | (x : ℕ) < c ∧ c ≤ σ x}
  have hD : Set.InjOn (fun x : Fin L ↦ (x : ℕ) - c) D := fun x hx y hy h ↦ by
    simp only [D, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx hy h
    exact Fin.ext (by omega)
  have hU : Set.InjOn (upRank σ) U := (upRank_injOn σ).mono fun x hx ↦ by
    simp only [U, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
    omega
  rw [← prod_image (f := fun i ↦ ρ i) fun x hx y hy h ↦ hD hx hy h,
    ← prod_image (f := fun i ↦ ρ i) fun x hx y hy h ↦ hU hx hy h]
  refine prod_le_prod_of_card_filter_lt_le hρ₀ hρ ?_ fun k ↦ ?_
  · rw [card_image_of_injOn hD, card_image_of_injOn hU, card_cross_forward σ c]
  · rw [filter_image, filter_image, card_image_of_injOn (hD.mono (filter_subset _ _)),
      card_image_of_injOn (hU.mono (filter_subset _ _)), filter_filter, filter_filter]
    exact card_cross_backward_le σ hfwd hbwd c k

end Crossing

section Sylvester

variable {S : Type*} [Semiring S]

/-- An entry of the Sylvester matrix in one of the first `n` columns, which carry the
coefficients of the second polynomial. -/
private theorem sylvester_apply_of_lt (f g : S[X]) {n m : ℕ} (i x : Fin (n + m))
    (hx : (x : ℕ) < n) :
    sylvester f g n m i x =
      if (x : ℕ) ≤ i ∧ (i : ℕ) ≤ x + m then g.coeff (i - x) else 0 := by
  obtain ⟨x, rfl⟩ : ∃ y : Fin n, Fin.castAdd m y = x := ⟨⟨x, hx⟩, rfl⟩
  simp [sylvester]

/-- An entry of the Sylvester matrix in one of the last `m` columns, which carry the
coefficients of the first polynomial. -/
private theorem sylvester_apply_of_le (f g : S[X]) {n m : ℕ} (i x : Fin (n + m))
    (hx : n ≤ (x : ℕ)) :
    sylvester f g n m i x =
      if (x : ℕ) ≤ i + n ∧ (i : ℕ) ≤ x then f.coeff (i + n - x) else 0 := by
  obtain ⟨x, rfl⟩ : ∃ y : Fin m, Fin.natAdd n y = x :=
    ⟨⟨x - n, by omega⟩, Fin.ext (by simp; omega)⟩
  simp only [sylvester, Matrix.of_apply, Fin.addCases_right, Set.mem_Icc, Fin.val_natAdd]
  congr 1
  · exact propext (by omega)
  · congr 1; omega

end Sylvester

variable {R : Type*} [SeminormedCommRing R] [NormOneClass R] [IsUltrametricDist R]

/-- **Coleman's coefficient bound.** Let `P` and `B` be polynomials over an ultrametric seminormed
ring with `‖1‖ = 1` and `B(0) = 0`. If `ρ` is a nonnegative antitone sequence with
`‖coeff j P‖ ≤ ∏ i < j, ρ i` for `j ≤ n`, and `‖coeff l B‖ * ρ t ^ l ≤ β t` for every `t` and every
`l ≥ 1`, then the `k`-th coefficient of Coleman's transform `D_(n,m)(B, P)` has norm at most
`∏ t < k, β t`, for all ranks `n` and degree bounds `m`. -/
theorem norm_coeff_colemanDBounded_le {B P : R[X]} {n m : ℕ} {ρ β : ℕ → ℝ}
    (hB₀ : B.coeff 0 = 0) (hρ₀ : ∀ i, 0 ≤ ρ i) (hρ : Antitone ρ)
    (hP : ∀ j ≤ n, ‖P.coeff j‖ ≤ ∏ i ∈ range j, ρ i)
    (hβ : ∀ t j, ‖B.coeff (j + 1)‖ * ρ t ^ (j + 1) ≤ β t) (k : ℕ) :
    ‖(colemanDBounded B P n m).coeff k‖ ≤ ∏ t ∈ range k, β t := by
  have hβ₀ (t : ℕ) : 0 ≤ β t :=
    (mul_nonneg (norm_nonneg _) (pow_nonneg (hρ₀ t) _)).trans (hβ t 0)
  have hprod : 0 ≤ ∏ t ∈ range k, β t := prod_nonneg fun t _ ↦ hβ₀ t
  rw [colemanDBounded_def, resultant, Matrix.det_apply, finsetSum_coeff]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hprod fun σ _ ↦ ?_
  rw [coeff_smul, norm_units_zsmul]
  set M := sylvester ((P.reflect n).map C) (1 - C X * B.map C) n m with hM_def
  by_cases hzero : ∃ x, M (σ x) x = 0
  · obtain ⟨x, hx⟩ := hzero
    have : ∏ i, M (σ i) i = 0 := prod_eq_zero (mem_univ x) hx
    rw [this, coeff_zero, norm_zero]
    exact hprod
  -- Hence each of the first `n` columns `x` is moved to a row in `[x, x + m]` and each of the last
  -- `m` columns to a row in `[x - n, x]`, since the other entries vanish.
  have hband (x : Fin (n + m)) : ((x : ℕ) < n → (x : ℕ) ≤ σ x ∧ (σ x : ℕ) ≤ x + m) ∧
      (n ≤ (x : ℕ) → (x : ℕ) ≤ σ x + n ∧ (σ x : ℕ) ≤ x) := by
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩ <;> by_contra hc <;> refine hzero ⟨x, ?_⟩
    · rw [hM_def, sylvester_apply_of_lt _ _ _ _ h, ite_eq_right hc]
    · rw [hM_def, sylvester_apply_of_le _ _ _ _ h, ite_eq_right hc]
  -- Otherwise every entry of the term is a monomial: `1` or `-b_(σ x - x) T` in the first `n`
  -- columns, according as `σ x = x` or not, and `a_(x - σ x)` in the last `m` columns.
  set c : Fin (n + m) → R := fun x ↦
    if (x : ℕ) < σ x then -B.coeff (σ x - x) else if (x : ℕ) < n then 1 else P.coeff (x - σ x)
  set e : Fin (n + m) → ℕ := fun x ↦ if (x : ℕ) < σ x then 1 else 0
  have hM (x : Fin (n + m)) : M (σ x) x = C (c x) * X ^ e x := by
    rcases lt_or_ge (x : ℕ) n with h | h
    · rw [hM_def, sylvester_apply_of_lt _ _ _ _ h, ite_eq_left ((hband x).1 h)]
      simp only [coeff_sub, coeff_one, coeff_C_mul, coeff_map, c, e, ite_eq_left h]
      by_cases hx : (x : ℕ) < σ x
      · rw [ite_eq_right (by omega), ite_eq_left hx, ite_eq_left hx, zero_sub, pow_one, map_neg,
          neg_mul, mul_comm]
      · have : (σ x : ℕ) - x = 0 := by omega
        simp [hx, this, hB₀]
    · have hσx : ¬(x : ℕ) < σ x := by have := (hband x).2 h; omega
      rw [hM_def, sylvester_apply_of_le _ _ _ _ h, ite_eq_left ((hband x).2 h)]
      simp only [coeff_map, coeff_reflect, c, e, ite_eq_right hσx, ite_eq_right (not_lt.2 h)]
      rw [revAt_le (by have := (hband x).2 h; omega)]
      simp only [pow_zero, mul_one]
      have := (hband x).2 h
      congr 2
      omega
  simp_rw [hM]
  rw [prod_mul_distrib, ← map_prod, prod_pow_eq_pow_sum, coeff_C_mul_X_pow]
  split_ifs with hk
  swap
  · rw [norm_zero]
    exact hprod
  have hsum : ∑ x, e x = #{x : Fin (n + m) | (x : ℕ) < σ x} := by
    simp [e, sum_boole]
  -- the weight of each column of the term, apart from the factors `ρ` of the `a`'s
  set w : Fin (n + m) → ℝ := fun x ↦ if (x : ℕ) < σ x then ‖B.coeff (σ x - x)‖ else 1
  have hw₀ (x : Fin (n + m)) : 0 ≤ w x := by
    simp only [w]
    split_ifs <;> positivity
  have hc (x : Fin (n + m)) : ‖c x‖ ≤ w x * ∏ i ∈ range ((x : ℕ) - σ x), ρ i := by
    simp only [c, w]
    by_cases hx : (x : ℕ) < σ x
    · simp [hx, Nat.sub_eq_zero_of_le hx.le]
    by_cases hn : (x : ℕ) < n
    · have : (x : ℕ) - σ x = 0 := by have := (hband x).1 hn; omega
      simp [hx, hn, this]
    · rw [ite_eq_right hx, ite_eq_right hn, ite_eq_right hx, one_mul]
      exact hP _ (by have := (hband x).2 (not_lt.1 hn); omega)
  have hwρ (x : Fin (n + m)) : w x * ρ (upRank σ x) ^ ((σ x : ℕ) - x) ≤
      if (x : ℕ) < σ x then β (upRank σ x) else 1 := by
    simp only [w]
    by_cases hx : (x : ℕ) < σ x
    · obtain ⟨j, hj⟩ : ∃ j, (σ x : ℕ) - x = j + 1 := ⟨σ x - x - 1, by omega⟩
      rw [ite_eq_left hx, ite_eq_left hx, hj]
      exact hβ _ j
    · rw [ite_eq_right hx, ite_eq_right hx, Nat.sub_eq_zero_of_le (not_lt.1 hx), pow_zero,
        one_mul]
  calc ‖∏ x : Fin (n + m), c x‖ ≤ ∏ x : Fin (n + m), ‖c x‖ := TauCeti.norm_prod_le_prod_norm _ _
    _ ≤ ∏ x : Fin (n + m), (w x * ∏ i ∈ range ((x : ℕ) - σ x), ρ i) :=
        prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun x _ ↦ hc x
    _ = (∏ x : Fin (n + m), w x) * ∏ x : Fin (n + m), ∏ i ∈ range ((x : ℕ) - σ x), ρ i :=
        prod_mul_distrib
    _ ≤ (∏ x : Fin (n + m), w x) * ∏ x : Fin (n + m), ρ (upRank σ x) ^ ((σ x : ℕ) - x) :=
        mul_le_mul_of_nonneg_left (prod_prod_range_le_prod_pow_upRank σ
          (fun x hx ↦ ((hband x).1 hx).1) (fun x hx ↦ ((hband x).2 hx).2) hρ₀ hρ)
          (prod_nonneg fun x _ ↦ hw₀ x)
    _ = ∏ x : Fin (n + m), w x * ρ (upRank σ x) ^ ((σ x : ℕ) - x) := prod_mul_distrib.symm
    _ ≤ ∏ x : Fin (n + m), if (x : ℕ) < σ x then β (upRank σ x) else 1 :=
        prod_le_prod₀ (fun x _ ↦ mul_nonneg (hw₀ x) (pow_nonneg (hρ₀ _) _)) fun x _ ↦ hwρ x
    _ = ∏ x ∈ {x : Fin (n + m) | (x : ℕ) < σ x}, β (upRank σ x) := (prod_filter _ _).symm
    _ = ∏ t ∈ range k, β t := by rw [prod_upRank, hk, hsum]

end Polynomial

namespace PowerSeries

open Finset

variable {R : Type*} [NormedCommRing R] [NormOneClass R] [IsUltrametricDist R]

/-- **Coleman's bound for truncations.** Let `ρ` be a nonnegative antitone Newton majorant of a
power series `F`, `‖coeff j F‖ ≤ ∏ i < j, ρ i`, and let `B` be restricted at every radius `ρ i`
with `B(0) = 0`. Then the Coleman transforms of the truncations of `F` along the truncations of
`B` satisfy `‖coeff k D_(n,m)(trunc a B, trunc b F)‖ ≤ ∏ i < k, β_B(ρ i)`, uniformly in the ranks,
degree bounds and truncation orders. In particular this bounds
`D_(N,M)(trunc (M + 1) B, trunc (N + 1) F)`. -/
theorem norm_coeff_colemanDBounded_trunc_le {F B : R⟦X⟧} {ρ : ℕ → ℝ} (hρ₀ : ∀ i, 0 ≤ ρ i)
    (hρ : Antitone ρ) (hF : ∀ j, ‖coeff j F‖ ≤ ∏ i ∈ range j, ρ i)
    (hB : ∀ i, B.IsRestricted (ρ i)) (hB₀ : coeff 0 B = 0) (n m a b k : ℕ) :
    ‖(Polynomial.colemanDBounded (trunc a B) (trunc b F) n m).coeff k‖ ≤
      ∏ i ∈ range k, colemanMajorant B (ρ i) := by
  refine Polynomial.norm_coeff_colemanDBounded_le (by simp [coeff_trunc, hB₀]) hρ₀ hρ
    (fun j _ ↦ ?_) (fun t j ↦ ?_) k
  · rw [coeff_trunc]
    split_ifs
    · exact hF j
    · simpa using prod_nonneg fun i _ ↦ hρ₀ i
  · rw [coeff_trunc]
    split_ifs
    · exact norm_coeff_succ_mul_pow_le_colemanMajorant (hB t) j
    · simpa using colemanMajorant_nonneg B (hρ₀ t)

end PowerSeries
