/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.SingularMinor

/-!
# Mass bounds for vanishing leading minors

For a matrix representation over a finite field, consider the matrices of pairings between a
fixed frame and the translates of another frame. Under a nonnegative weight of positive type,
small stabilizer masses for the column and dual row actions give a small mass for the elements
at which any proper leading principal minor of the pairing matrix vanishes. This allows one
to discard the complement of the locus where all those minors are invertible before estimating
a second moment.

The bounds are those of `New.Filling.sum_leadingMinor_eq_zero_le` and
`New.Filling.sum_not_isOpenElement_le` in [grh-lean, MomentBounds.lean][source]. The proof uses
the singular-minor inequality on each truncated pair of frames, and needs only one place to
bound the locus where the test fails at every place.

[source]: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Spanning/Unfolding/MomentBounds.lean
-/

public section

open Finset Matrix
open scoped InnerProductSpace

namespace TauCeti.PositiveType

/-- A principal submatrix of the pairing matrix satisfies the singular-minor inequality with
its own size in the error exponent. The stabilizer bounds are stated on the full coefficient
spaces of the two frames; extend a coefficient vector on the selected columns by zero. -/
theorem card_mul_sum_det_submatrix_eq_zero_le {G F ι ν μ H : Type*}
    [Group G] [Fintype G] [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [DecidableEq ι] [Fintype ν] [Fintype μ] [DecidableEq μ]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : G →* GL ι F) (A B : Matrix ι ν F) (e : μ ↪ ν)
    {Θ : G → ℝ} (hΘ : ∀ s, 0 ≤ Θ s) {u : G → H}
    (hu : ∀ a b, ⟪u a, u b⟫_ℂ = Θ (a⁻¹ * b)) {Y : ℝ} (hY : 0 ≤ Y)
    (hcol : ∀ v, v ≠ 0 → ∑ s with (π s : Matrix ι ι F) *ᵥ (A *ᵥ v) = A *ᵥ v, Θ s ≤ Y)
    (hrow : ∀ v, v ≠ 0 → ∑ s with (B *ᵥ v) ᵥ* (π s : Matrix ι ι F) = B *ᵥ v, Θ s ≤ Y) :
    Fintype.card F * ∑ s with ((Bᵀ * (π s : Matrix ι ι F) * A).submatrix e e).det = 0, Θ s ≤
      2 * ∑ s, Θ s +
        Fintype.card F ^ Fintype.card μ * √((Fintype.card F : ℝ) ^ Fintype.card ι) * Y := by
  classical
  have he {v : μ → F} (hv : v ≠ 0) : Function.extend e v 0 ≠ 0 := by
    intro h
    apply hv
    funext j
    simpa only [e.injective.extend_apply, Pi.zero_apply] using congrFun h (e j)
  have h := card_mul_sum_det_eq_zero_le π (A.submatrix id e) (B.submatrix id e) hΘ hu hY
    (fun v hv ↦ by simpa only [Matrix.mulVec_extend_zero e.injective] using hcol _ (he hv))
    (fun v hv ↦ by simpa only [Matrix.mulVec_extend_zero e.injective] using hrow _ (he hv))
  have hmatrix (s : G) : (Bᵀ * (π s : Matrix ι ι F) * A).submatrix e e =
      (B.submatrix id e)ᵀ * (π s : Matrix ι ι F) * A.submatrix id e := by
    rw [Matrix.submatrix_mul _ _ e id e Function.bijective_id,
      Matrix.submatrix_mul _ _ e id id Function.bijective_id, Matrix.submatrix_id_id,
      Matrix.transpose_submatrix]
  simpa only [hmatrix] using h

-- Squaring keeps the comparison of the field-size exponents in natural numbers.
private theorem pow_mul_sqrt_pow_le_of_rank_budget {q b : ℝ} {r l k : ℕ}
    (hq₀ : 0 ≤ q) (hb : 1 ≤ b) (hq : q ≤ b ^ 11) (hr : 11 * (2 * l + r) ≤ 12 * k) :
    q ^ l * √(q ^ r) ≤ b ^ (6 * k) := by
  refine (sq_le_sq₀ (by positivity) (by positivity)).mp ?_
  rw [mul_pow, Real.sq_sqrt (pow_nonneg hq₀ _), ← pow_mul, ← pow_add, ← pow_mul]
  rw [mul_comm l 2, show 6 * k * 2 = 12 * k by omega]
  calc
    q ^ (2 * l + r) ≤ (b ^ 11) ^ (2 * l + r) := pow_le_pow_left₀ hq₀ hq _
    _ = b ^ (11 * (2 * l + r)) := (pow_mul _ _ _).symm
    _ ≤ b ^ (12 * k) := pow_le_pow_right₀ hb hr

/-- At a field size between `b^10` and `b^11`, a leading principal minor accounts for
at most `3 / b^10` of the mass when the two stabilizer masses are at most `1 / b^(6*k)` of
it. The rank budget holds for `r = k + 2*n - 1` and `44*n ≤ k`. -/
theorem sum_leadingMinor_eq_zero_le {G F H : Type*} [Group G] [Fintype G]
    [Field F] [Fintype F] [DecidableEq F] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {r n k l : ℕ} (π : G →* GL (Fin r) F) (A B : Matrix (Fin r) (Fin n) F)
    (hl : l ≤ n) (hr : 11 * (2 * l + r) ≤ 12 * k) {b : ℝ} (hb : 1 ≤ b)
    (hq₁ : b ^ 10 ≤ Fintype.card F) (hq₂ : (Fintype.card F : ℝ) ≤ b ^ 11)
    {Θ : G → ℝ} (hΘ : ∀ s, 0 ≤ Θ s) {u : G → H}
    (hu : ∀ a c, ⟪u a, u c⟫_ℂ = Θ (a⁻¹ * c))
    (hcol : ∀ v, v ≠ 0 → ∑ s with (π s : Matrix (Fin r) (Fin r) F) *ᵥ (A *ᵥ v) = A *ᵥ v,
      Θ s ≤ (∑ s, Θ s) / b ^ (6 * k))
    (hrow : ∀ v, v ≠ 0 → ∑ s with (B *ᵥ v) ᵥ* (π s : Matrix (Fin r) (Fin r) F) = B *ᵥ v,
      Θ s ≤ (∑ s, Θ s) / b ^ (6 * k)) :
    ∑ s with ((Bᵀ * (π s : Matrix (Fin r) (Fin r) F) * A).submatrix
        (Fin.castLE hl) (Fin.castLE hl)).det = 0, Θ s ≤ (3 / b ^ 10) * ∑ s, Θ s := by
  classical
  have hm : 0 ≤ ∑ s, Θ s := sum_nonneg fun s _ ↦ hΘ s
  have hbpos : 0 < b := zero_lt_one.trans_le hb
  have h := card_mul_sum_det_submatrix_eq_zero_le π A B ⟨Fin.castLE hl, Fin.castLE_injective hl⟩
    hΘ hu (div_nonneg hm (by positivity)) hcol hrow
  simp only [Function.Embedding.coeFn_mk, Fintype.card_fin] at h
  have herr := pow_mul_sqrt_pow_le_of_rank_budget (Nat.cast_nonneg (Fintype.card F)) hb hq₂ hr
  have hterm := mul_le_mul_of_nonneg_right herr (div_nonneg hm (by positivity : 0 ≤ b ^ (6 * k)))
  rw [mul_div_cancel₀ _ (pow_ne_zero _ hbpos.ne')] at hterm
  rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hbpos 10), mul_comm]
  exact (mul_le_mul_of_nonneg_right hq₁ (sum_nonneg fun s _ ↦ hΘ s)).trans (by linarith)

/-- In the same field-size range, the mass of elements with at least one vanishing proper
leading principal minor is at most `b⁻⁴` of the total. In a test over several places,
elements failing at every place are a subset of those failing at this one. -/
theorem sum_exists_leadingMinor_eq_zero_le {G F H : Type*} [Group G] [Fintype G]
    [Field F] [Fintype F] [DecidableEq F] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {r n k : ℕ} (π : G →* GL (Fin r) F) (A B : Matrix (Fin r) (Fin n) F)
    (hr : 11 * (2 * n + r) ≤ 12 * k) {b : ℝ} (hb : 2 ≤ b) (hn : (n : ℝ) ≤ b)
    (hq₁ : b ^ 10 ≤ Fintype.card F) (hq₂ : (Fintype.card F : ℝ) ≤ b ^ 11)
    {Θ : G → ℝ} (hΘ : ∀ s, 0 ≤ Θ s) {u : G → H}
    (hu : ∀ a c, ⟪u a, u c⟫_ℂ = Θ (a⁻¹ * c))
    (hcol : ∀ v, v ≠ 0 → ∑ s with (π s : Matrix (Fin r) (Fin r) F) *ᵥ (A *ᵥ v) = A *ᵥ v,
      Θ s ≤ (∑ s, Θ s) / b ^ (6 * k))
    (hrow : ∀ v, v ≠ 0 → ∑ s with (B *ᵥ v) ᵥ* (π s : Matrix (Fin r) (Fin r) F) = B *ᵥ v,
      Θ s ≤ (∑ s, Θ s) / b ^ (6 * k)) :
    ∑ s with (∃ l : Fin n, ((Bᵀ * (π s : Matrix (Fin r) (Fin r) F) * A).submatrix
      (Fin.castLE l.isLt.le) (Fin.castLE l.isLt.le)).det = 0), Θ s ≤ (∑ s, Θ s) / b ^ 4 := by
  classical
  let Z (s : G) := Bᵀ * (π s : Matrix (Fin r) (Fin r) F) * A
  let bad (l : Fin n) := univ.filter fun s : G ↦
    ((Z s).submatrix (Fin.castLE l.isLt.le) (Fin.castLE l.isLt.le)).det = 0
  have h₁ : 1 ≤ b := by linarith
  have hcoeff : (n : ℝ) * (3 / b ^ 10) ≤ 1 / b ^ 4 := by
    rw [← mul_div_assoc, div_le_div_iff₀ (by positivity : 0 < b ^ 10) (by positivity)]
    have hpow : (3 : ℝ) ≤ b ^ 5 := (by norm_num : (3 : ℝ) ≤ 2 ^ 5).trans
      (pow_le_pow_left₀ (by norm_num) hb 5)
    calc
      (n : ℝ) * 3 * b ^ 4 ≤ b * b ^ 5 * b ^ 4 := by gcongr
      _ = 1 * b ^ 10 := by ring
  simpa only [bad, Z, Finset.mem_filter, Finset.mem_univ, true_and] using (calc
    ∑ s ∈ univ.filter (fun s : G ↦ ∃ l : Fin n, s ∈ bad l), Θ s
        ≤ ∑ l : Fin n, ∑ s ∈ bad l, Θ s := by
          have hsum (l : Fin n) : ∑ s ∈ bad l, Θ s = ∑ s, if s ∈ bad l then Θ s else 0 :=
            (sum_ite_mem_eq (bad l) Θ).symm
          simp only [hsum, sum_filter]
          rw [Finset.sum_comm]
          refine sum_le_sum fun s _ ↦ ?_
          by_cases h : ∃ l : Fin n, s ∈ bad l
          · obtain ⟨l, hl⟩ := h
            have hsingle : (if s ∈ bad l then Θ s else 0) ≤
                ∑ j : Fin n, if s ∈ bad j then Θ s else 0 :=
              single_le_sum (f := fun j ↦ if s ∈ bad j then Θ s else 0)
                (fun j _ ↦ by split <;> simp [hΘ]) (mem_univ l)
            simpa only [ite_eq_left hl, ite_eq_left (⟨l, hl⟩ : ∃ j, s ∈ bad j)] using hsingle
          · rw [ite_eq_right h]
            exact sum_nonneg fun j _ ↦ by split <;> simp [hΘ]
    _ ≤ ∑ _l : Fin n, (3 / b ^ 10) * ∑ s, Θ s := by
          refine sum_le_sum fun l _ ↦ sum_leadingMinor_eq_zero_le π A B l.isLt.le ?_
            h₁ hq₁ hq₂ hΘ hu hcol hrow
          exact (by omega : 11 * (2 * (l : ℕ) + r) ≤ 11 * (2 * n + r)).trans hr
    _ = ((n : ℝ) * (3 / b ^ 10)) * ∑ s, Θ s := by simp [mul_assoc]
    _ ≤ (∑ s, Θ s) / b ^ 4 := by
          simpa only [one_div_mul_eq_div] using
            mul_le_mul_of_nonneg_right hcoeff (sum_nonneg fun s _ ↦ hΘ s))

end TauCeti.PositiveType
