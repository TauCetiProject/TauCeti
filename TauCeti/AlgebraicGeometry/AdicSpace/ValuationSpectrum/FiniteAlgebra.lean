/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# Fibres of the valuation spectrum of a finite algebra over a field

Let `K` be a field, `L` a finite `K`-algebra and `v` a point of `Spv K`. The points of `Spv L`
lying over `v` are the valuations of `L` whose restriction to `K` is equivalent to `v`. This file
proves that there are only finitely many of them, at most `[L : K]`. For a finite field extension
`L / K` this is the classical bound on the number of extensions of a valuation ring of `K` to `L`;
here `L` may have several prime ideals, each carrying its own extensions, and may be nonreduced.

This is the bound behind the finiteness of the fibres of `Spv B → Spv A` for a finite `A`-algebra
`B`: the points of `Spv B` over `x ∈ Spv A` correspond to the points of `Spv (κ(𝔭) ⊗[A] B)` over
the residue valuation of `x`, where `𝔭` is the support of `x`, and `κ(𝔭) ⊗[A] B` is a finite
`κ(𝔭)`-algebra.

The proof shows that pairwise distinct points `w₁, …, wᵣ` of the fibre are separated by elements
`e₁, …, eᵣ` of `L` with `wᵢ(eᵢ) = 1`, `wⱼ(eᵢ) < 1` for `j ≠ i`, and `w(eᵢ) ≤ 1` on the whole fibre.
Such elements are linearly independent over `K`: in a relation `∑ aᵢ eᵢ = 0`, the term whose
coefficient has the largest `v`-value strictly dominates the others at the matching point.

The separating elements come from two sources. Points with different supports are separated by
an idempotent, since `L` is artinian. Points `w₁ ≠ w₂` with the same (maximal) support are
incomparable: there is `x` with `w₂(x) ≤ 1 < w₁(x)`. Then a normalized polynomial relation
`∑ cₙ xⁿ = 0` over `K`, with `v(c_D) = 1` and `v(cₙ) < 1` for `n > D`, produces the element
`u = ∑_{n > D} cₙ xⁿ⁻ᴰ`, which satisfies `w(u) ≤ 1` on the fibre, `w(u) = 1` when `w(x) > 1` and
`w(u) < 1` when `w(x) ≤ 1`. Incomparability itself is proved with the same element.

## Main results

* `TauCeti.ValuationSpectrum.finite_comap_preimage_singleton`: the fibre of
  `Spv L → Spv K` over any point is finite.
* `TauCeti.ValuationSpectrum.ncard_comap_preimage_singleton_le_finrank`: it has at most
  `[L : K]` points.

## References

* [A. J. Engler and A. Prestel, *Valued Fields*][engler2005], Section 3.3: for a finite field
  extension the fundamental inequality `∑ eᵢ fᵢ ≤ [L : K]` bounds the number of extensions of a
  valuation ring, and this file proves that bound by linear independence of elements separating
  the extensions.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Definition 4.1, for `Spv`.
-/

public section

open Polynomial

namespace TauCeti

namespace ValuationSpectrum

variable {K L : Type*} [Field K] [CommRing L] [Algebra K L]

/-- On the fibre over `v`, the valuation of a point compares images of elements of `K` as `v`
compares the elements themselves. -/
private theorem valuation_algebraMap_le_iff {v : Spv K} {w : Spv L}
    (hw : comap (algebraMap K L) w = v) (a b : K) :
    w.valuation (algebraMap K L a) ≤ w.valuation (algebraMap K L b) ↔
      v.valuation a ≤ v.valuation b := by
  rw [valuation_le_iff, valuation_le_iff, ← hw, comap_vle]

private theorem valuation_algebraMap_le_one_iff {v : Spv K} {w : Spv L}
    (hw : comap (algebraMap K L) w = v) (a : K) :
    w.valuation (algebraMap K L a) ≤ 1 ↔ v.valuation a ≤ 1 := by
  simpa using valuation_algebraMap_le_iff hw a 1

private theorem valuation_algebraMap_lt_one_iff {v : Spv K} {w : Spv L}
    (hw : comap (algebraMap K L) w = v) (a : K) :
    w.valuation (algebraMap K L a) < 1 ↔ v.valuation a < 1 := by
  simpa [not_le] using (valuation_algebraMap_le_iff hw 1 a).not

/-- A nonzero polynomial over `K` can be rescaled so that its coefficients have `v`-value at most
`1`, its coefficient in some degree `D` is `1`, and its coefficients of degree above `D` have
`v`-value below `1`. -/
private theorem exists_normalized (v : Spv K) {P : K[X]} (hP : P ≠ 0) :
    ∃ c : K, ∃ D : ℕ, (C c * P).coeff D = 1 ∧ (∀ n, v.valuation ((C c * P).coeff n) ≤ 1) ∧
      ∀ n, D < n → v.valuation ((C c * P).coeff n) < 1 := by
  classical
  set f : ℕ → _ := fun n ↦ v.valuation (P.coeff n)
  obtain ⟨n₀, -, hn₀⟩ := Finset.exists_max_image (Finset.range (P.natDegree + 1)) f
    ⟨0, by simp⟩
  have hmax₀ : ∀ k, f k ≤ f n₀ := fun k ↦ by
    by_cases hk : k ≤ P.natDegree
    · exact hn₀ k (by simpa [Nat.lt_succ_iff] using hk)
    · simp [f, coeff_eq_zero_of_natDegree_lt (not_le.mp hk)]
  -- the largest degree at which the coefficient has maximal `v`-value
  set S := (Finset.range (P.natDegree + 1)).filter fun n ↦ ∀ k, f k ≤ f n
  have hpos : ∀ n, (∀ k, f k ≤ f n) → f n ≠ 0 := fun n hn h ↦ by
    have := hn P.natDegree
    rw [h, le_zero_iff] at this
    exact leadingCoeff_ne_zero.mpr hP ((map_eq_zero _).mp this)
  have hmemS : ∀ n, (∀ k, f k ≤ f n) → n ∈ S := fun n hn ↦ by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le ?_), hn⟩
    exact le_natDegree_of_ne_zero fun h ↦ hpos n hn (by simp [f, h])
  have hS : S.Nonempty := ⟨n₀, hmemS n₀ hmax₀⟩
  set D := S.max' hS
  have hD : ∀ k, f k ≤ f D := (Finset.mem_filter.mp (S.max'_mem hS)).2
  have hcD : P.coeff D ≠ 0 := fun h ↦ hpos D hD (by simp [f, h])
  have hfD : 0 < f D := pos_iff_ne_zero.mpr (hpos D hD)
  refine ⟨(P.coeff D)⁻¹, D, by simp [hcD], fun n ↦ ?_, fun n hn ↦ ?_⟩
  · rw [coeff_C_mul, map_mul, map_inv₀]
    exact inv_mul_le_one_of_le₀ (hD n) hfD.le
  · rw [coeff_C_mul, map_mul, map_inv₀]
    refine (inv_mul_lt_one₀ hfD).mpr (lt_of_not_ge fun h ↦ ?_)
    exact (S.le_max' n (hmemS n fun k ↦ (hD k).trans h)).not_gt hn

/-- **Linear independence of separated elements.** If points `wᵢ` of `Spv L` over `v` and
elements `eᵢ ∈ L` satisfy `wᵢ(eᵢ) = 1` and `wⱼ(eᵢ) < 1` for `j ≠ i`, then the `eᵢ` are linearly
independent over `K`: in a relation, the term whose coefficient has the largest `v`-value
dominates all others at the matching point. -/
private theorem linearIndependent_of_valuation (v : Spv K) {ι : Type*} (w : ι → Spv L)
    (hw : ∀ i, comap (algebraMap K L) (w i) = v) (e : ι → L) (he : ∀ i, (w i).valuation (e i) = 1)
    (hlt : ∀ i j, i ≠ j → (w j).valuation (e i) < 1) : LinearIndependent K e := by
  classical
  rw [linearIndependent_iff']
  intro t g hsum
  by_contra! H
  obtain ⟨i, hit, hgi⟩ := H
  obtain ⟨i₀, hi₀t, hmax⟩ := Finset.exists_max_image t (fun j ↦ v.valuation (g j)) ⟨i, hit⟩
  have hg₀ : g i₀ ≠ 0 := fun h ↦ hgi <| by
    have := hmax i hit
    rwa [h, map_zero, le_zero_iff, map_eq_zero] at this
  have hc : (w i₀).valuation (algebraMap K L (g i₀)) ≠ 0 := ((isUnit_iff_ne_zero.mpr hg₀).map
    (algebraMap K L) |>.map (w i₀).valuation).ne_zero
  have hrest : (w i₀).valuation (∑ j ∈ t.erase i₀, g j • e j) <
      (w i₀).valuation (g i₀ • e i₀) := by
    rw [Algebra.smul_def, map_mul, he, mul_one]
    refine Valuation.map_sum_lt _ hc fun j hj ↦ ?_
    rw [Algebra.smul_def, map_mul]
    calc (w i₀).valuation (algebraMap K L (g j)) * (w i₀).valuation (e j)
        ≤ (w i₀).valuation (algebraMap K L (g i₀)) * (w i₀).valuation (e j) :=
          mul_le_mul_left ((valuation_algebraMap_le_iff (hw i₀) _ _).mpr
            (hmax j (Finset.mem_of_mem_erase hj))) _
      _ < (w i₀).valuation (algebraMap K L (g i₀)) :=
          mul_lt_of_lt_one_right (pos_iff_ne_zero.mpr hc) (hlt j i₀ (Finset.ne_of_mem_erase hj))
  have := congrArg (w i₀).valuation hsum
  rw [← Finset.add_sum_erase _ _ hi₀t, Valuation.map_add_eq_of_lt_left _ hrest, map_zero,
    Algebra.smul_def, map_mul, he, mul_one] at this
  exact hc this

variable [Module.Finite K L]

/-- **The detecting element.** For every `x ∈ L` there is `u ∈ L` such that, at every point `w` of
`Spv L` over `v`, `w(u) < 1` if `w(x) ≤ 1` and `w(u) = 1` if `w(x) > 1`. It is built from a
polynomial relation for `x` over `K`, normalized by `exists_normalized`. -/
private theorem exists_detector (v : Spv K) (x : L) :
    ∃ u : L, ∀ w : Spv L, comap (algebraMap K L) w = v →
      (w.valuation x ≤ 1 → w.valuation u < 1) ∧ (1 < w.valuation x → w.valuation u = 1) := by
  have hint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  obtain ⟨c, D, hcD, hle, hlt⟩ := exists_normalized v (minpoly.ne_zero hint)
  set P := C c * minpoly K x
  have hPx : aeval x P = 0 := by simp [P]
  set M := P.natDegree
  set a : ℕ → L := fun n ↦ algebraMap K L (P.coeff n)
  refine ⟨∑ k ∈ Finset.range M, a (D + 1 + k) * x ^ (k + 1), fun w hw ↦ ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩⟩
  · -- every term has a coefficient of value `< 1`
    refine Valuation.map_sum_lt _ one_ne_zero fun k _ ↦ ?_
    rw [map_mul, map_pow]
    exact mul_lt_one_of_lt_of_le ((valuation_algebraMap_lt_one_iff hw _).mpr (hlt _ (by omega)))
      (pow_le_one' hx _)
  · -- `x ^ D * u = -(c₀ + c₁ x + ⋯ + c_D x ^ D)`, dominated by its last term
    have hsplit : x ^ D * ∑ k ∈ Finset.range M, a (D + 1 + k) * x ^ (k + 1) =
        -∑ n ∈ Finset.range (D + 1), a n * x ^ n := by
      have h := hPx
      rw [aeval_eq_sum_range' (n := D + 1 + M) (by omega), ← Finset.sum_range_add_sum_Ico _
        (by omega : D + 1 ≤ D + 1 + M), Finset.sum_Ico_eq_sum_range] at h
      simp only [Nat.add_sub_cancel_left, Algebra.smul_def] at h
      rw [eq_neg_iff_add_eq_zero, add_comm, Finset.mul_sum, ← h]
      congr 1
      exact Finset.sum_congr rfl fun k _ ↦ by
        simp only [a]
        ring
    have hx0 : w.valuation x ≠ 0 := (zero_lt_one.trans hx).ne'
    have hlow : w.valuation (∑ n ∈ Finset.range D, a n * x ^ n) < w.valuation x ^ D :=
      Valuation.map_sum_lt _ (pow_ne_zero _ hx0) fun n hn ↦ by
        rw [map_mul, map_pow]
        calc w.valuation (a n) * w.valuation x ^ n ≤ 1 * w.valuation x ^ n :=
              mul_le_mul_left ((valuation_algebraMap_le_one_iff hw _).mpr (hle n)) _
          _ < w.valuation x ^ D := by
              rw [one_mul]
              exact pow_lt_pow_right₀ hx (Finset.mem_range.mp hn)
    have htop : w.valuation (a D * x ^ D) = w.valuation x ^ D := by
      rw [map_mul, map_pow, show a D = 1 by simp [a, hcD], map_one, one_mul]
    have hsum : w.valuation (∑ n ∈ Finset.range (D + 1), a n * x ^ n) = w.valuation x ^ D := by
      rw [Finset.sum_range_succ, Valuation.map_add_eq_of_lt_right _ (htop ▸ hlow), htop]
    have := congrArg w.valuation hsplit
    rw [map_mul, map_pow, Valuation.map_neg, hsum] at this
    exact (mul_eq_left₀ (pow_ne_zero _ hx0)).mp this

/-- An element that is a unit modulo the maximal support `𝔮` of the points under consideration
has an inverse modulo `𝔮`, whose valuation is the inverse at each of these points. -/
private theorem exists_valuation_mul_eq_one {q : Ideal L} (hq : q.IsMaximal) {b : L}
    (hb : b ∉ q) : ∃ y : L, ∀ w : Spv L, w.supp = q → w.valuation y * w.valuation b = 1 := by
  obtain ⟨y, i, hi, hyi⟩ := hq.exists_inv hb
  refine ⟨y, fun w hw ↦ ?_⟩
  rw [← map_mul, ← w.valuation.map_add_supp (y * b) (s := i)
    (by rwa [← supp_eq_valuation_supp, hw]), hyi, map_one]

/-- **Incomparability.** Two distinct points of `Spv L` over `v` with the same support are
incomparable: some `x` has `w₂(x) ≤ 1 < w₁(x)`. -/
private theorem exists_valuation_le_one_lt (v : Spv K) {w₁ w₂ : Spv L}
    (h₁ : comap (algebraMap K L) w₁ = v) (h₂ : comap (algebraMap K L) w₂ = v)
    (hsupp : w₁.supp = w₂.supp) (hne : w₁ ≠ w₂) :
    ∃ x : L, w₂.valuation x ≤ 1 ∧ 1 < w₁.valuation x := by
  have : IsArtinianRing L := .of_finite K L
  have hq : w₁.supp.IsMaximal := inferInstance
  by_contra! H
  -- if `w₂(x) ≤ 1 → w₁(x) ≤ 1` for all `x`, the converse holds as well
  have H' : ∀ x, w₁.valuation x ≤ 1 → w₂.valuation x ≤ 1 := by
    intro x hx
    by_contra! hx'
    obtain ⟨u, hu⟩ := exists_detector v x
    have hu₁ := (hu w₁ h₁).1 hx
    have hu₂ := (hu w₂ h₂).2 hx'
    have hu_mem : u ∉ w₁.supp := by
      rw [hsupp, supp_eq_valuation_supp, Valuation.mem_supp_iff, hu₂]
      exact one_ne_zero
    obtain ⟨y, hy⟩ := exists_valuation_mul_eq_one hq hu_mem
    have hy₂ : w₂.valuation y = 1 := by simpa [hu₂] using hy w₂ hsupp.symm
    have := hy w₁ rfl
    have hlt : w₁.valuation u * w₁.valuation y < 1 := mul_lt_one_of_lt_of_le hu₁ (H y hy₂.le)
    exact hlt.ne (mul_comm (w₁.valuation y) _ ▸ this)
  -- two points with the same maximal support and the same valuation ring coincide
  refine hne (ext' fun a b ↦ ?_)
  rw [← valuation_le_iff, ← valuation_le_iff]
  by_cases hb : b ∈ w₁.supp
  · have hb₂ : b ∈ w₂.supp := hsupp ▸ hb
    rw [supp_eq_valuation_supp, Valuation.mem_supp_iff] at hb hb₂
    rw [hb, hb₂, le_zero_iff, le_zero_iff, ← Valuation.mem_supp_iff, ← Valuation.mem_supp_iff,
      ← supp_eq_valuation_supp, ← supp_eq_valuation_supp, hsupp]
  · obtain ⟨y, hy⟩ := exists_valuation_mul_eq_one hq hb
    have key : ∀ w : Spv L, w.supp = w₁.supp →
        (w.valuation a ≤ w.valuation b ↔ w.valuation (a * y) ≤ 1) := fun w hw ↦ by
      have hyb := hy w hw
      have hy0 : w.valuation y ≠ 0 := left_ne_zero_of_mul_eq_one hyb
      rw [map_mul, ← hyb, mul_comm (w.valuation y) (w.valuation b)]
      exact (mul_le_mul_iff_left₀ (pos_iff_ne_zero.mpr hy0)).symm
    rw [key w₁ rfl, key w₂ hsupp.symm]
    exact ⟨H' _, H _⟩

/-- **Separation.** Two distinct points `w₁ ≠ w₂` of `Spv L` over `v` are separated by an element
`u` with `w₁(u) = 1`, `w₂(u) < 1` and `w(u) ≤ 1` at every point `w` over `v`. -/
private theorem exists_separating (v : Spv K) {w₁ w₂ : Spv L}
    (h₁ : comap (algebraMap K L) w₁ = v) (h₂ : comap (algebraMap K L) w₂ = v) (hne : w₁ ≠ w₂) :
    ∃ u : L, (∀ w : Spv L, comap (algebraMap K L) w = v → w.valuation u ≤ 1) ∧
      w₁.valuation u = 1 ∧ w₂.valuation u < 1 := by
  have : IsArtinianRing L := .of_finite K L
  by_cases hsupp : w₁.supp = w₂.supp
  · obtain ⟨x, hx₂, hx₁⟩ := exists_valuation_le_one_lt v h₁ h₂ hsupp hne
    obtain ⟨u, hu⟩ := exists_detector v x
    refine ⟨u, fun w hw ↦ ?_, (hu w₁ h₁).2 hx₁, (hu w₂ h₂).1 hx₂⟩
    rcases le_or_gt (w.valuation x) 1 with hx | hx
    · exact ((hu w hw).1 hx).le
    · exact ((hu w hw).2 hx).le
  · -- an idempotent separates the supports, and idempotents have valuation `0` or `1`
    obtain ⟨r, hr₁, hr, hr₂⟩ := IsArtinianRing.exists_notMem_forall_mem_of_ne w₁.supp
    have hval : ∀ w : Spv L, w.valuation r = 0 ∨ w.valuation r = 1 := fun w ↦ by
      exact IsIdempotentElem.iff_eq_zero_or_one.mp (hr.map w.valuation)
    have hr₂' : w₂.valuation r = 0 := by
      rw [← Valuation.mem_supp_iff, ← supp_eq_valuation_supp]
      exact hr₂ _ inferInstance (Ne.symm hsupp)
    refine ⟨r, fun w _ ↦ (hval w).elim (fun h ↦ h ▸ zero_le) (fun h ↦ h.le), ?_,
      hr₂' ▸ zero_lt_one⟩
    refine (hval w₁).resolve_left fun h ↦ hr₁ ?_
    rw [supp_eq_valuation_supp, Valuation.mem_supp_iff, h]

/-- Every finite set of points of `Spv L` over `v` has at most `[L : K]` elements: the product of
the elements separating a point from the others has value `1` there and value `< 1` at the
others, so these products are linearly independent. -/
private theorem card_le_finrank_of_subset (v : Spv K) (s : Finset (Spv L))
    (hs : ↑s ⊆ comap (algebraMap K L) ⁻¹' {v}) : s.card ≤ Module.finrank K L := by
  classical
  have hfib : ∀ w ∈ s, comap (algebraMap K L) w = v := fun w hw ↦ hs hw
  choose! u hu₀ hu₁ hu₂ using fun w₁ w₂ (h : w₁ ∈ s ∧ w₂ ∈ s ∧ w₁ ≠ w₂) ↦
    exists_separating v (hfib w₁ h.1) (hfib w₂ h.2.1) h.2.2
  have hpair : ∀ w : s, ∀ w' ∈ s.erase w, w.1 ∈ s ∧ w' ∈ s ∧ w.1 ≠ w' := fun w w' hw' ↦
    ⟨w.2, Finset.mem_of_mem_erase hw', (Finset.ne_of_mem_erase hw').symm⟩
  rw [← Fintype.card_coe s]
  refine (linearIndependent_of_valuation v (fun w : s ↦ w.1) (fun w ↦ hfib w w.2)
    (fun w ↦ ∏ w' ∈ s.erase w, u w w') (fun w ↦ ?_) fun w w' hne ↦ ?_).fintype_card_le_finrank
  · rw [map_prod]
    exact Finset.prod_eq_one fun w'' hw'' ↦ hu₁ w w'' (hpair w w'' hw'')
  · have hmem : w'.1 ∈ s.erase w := Finset.mem_erase.mpr ⟨fun h ↦ hne (Subtype.ext h.symm), w'.2⟩
    rw [map_prod, ← Finset.mul_prod_erase _ _ hmem]
    exact mul_lt_one_of_lt_of_le (hu₂ w w' (hpair w w' hmem)) <| Finset.prod_le_one
      fun w'' hw'' ↦ hu₀ w w'' (hpair w w'' (Finset.mem_of_mem_erase hw'')) w' (hfib w' w'.2)

/-- **Finiteness of fibres.** For a finite algebra `L` over a field `K`, only finitely many points
of `Spv L` lie over a given point of `Spv K`. -/
theorem finite_comap_preimage_singleton (v : Spv K) :
    (comap (algebraMap K L) ⁻¹' {v}).Finite := by
  by_contra h
  obtain ⟨t, ht, hcard⟩ := Set.Infinite.exists_subset_card_eq h (Module.finrank K L + 1)
  have := card_le_finrank_of_subset v t ht
  omega

/-- **The fibre bound.** For a finite algebra `L` over a field `K`, at most `[L : K]` points of
`Spv L` lie over a given point of `Spv K`. -/
theorem ncard_comap_preimage_singleton_le_finrank (v : Spv K) :
    (comap (algebraMap K L) ⁻¹' {v}).ncard ≤ Module.finrank K L := by
  rw [Set.ncard_eq_toFinset_card _ (finite_comap_preimage_singleton v)]
  exact card_le_finrank_of_subset v _ (by simp)

end ValuationSpectrum

end TauCeti
