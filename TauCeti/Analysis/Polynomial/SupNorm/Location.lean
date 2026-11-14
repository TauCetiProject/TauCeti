/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Polynomial.MahlerMeasure
public import TauCeti.RingTheory.Polynomial.RootEnumeration
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Root location and separated-disc evaluation estimates

If a complex polynomial `p` of degree at most `n` has no root in the open disc of radius `r ≤ 1`
around `z`, then each root factor `‖z - α‖` is bounded below by a fixed multiple of `max 1 ‖α‖`:
roots of modulus at most `2 (‖z‖ + 1)` use `r ≤ ‖z - α‖`, while larger roots satisfy
`‖α‖ / 2 ≤ ‖α‖ - ‖z‖ ≤ ‖z - α‖`. Multiplying over the roots bounds `p.mahlerMeasure`, and hence
`p.supNorm`, by `‖p.eval z‖` up to `(r / (4 (‖z‖ + 1))) ^ (-n)`
(`Polynomial.mahlerMeasure_le_of_forall_isRoot_le_norm_sub`,
`Polynomial.supNorm_le_of_forall_isRoot_le_norm_sub`). Contrapositively, a value strictly below
`(r / (4 (‖z‖ + 1))) ^ n * p.supNorm` forces a complex root within `r` of `z`
(`Polynomial.exists_isRoot_norm_sub_lt_of_norm_eval_lt`).

When this small-value condition holds simultaneously at `n` points `β₀, …, βₙ₋₁` whose open
`r`-discs are pairwise disjoint, `p` acquires one root `αᵢ` in each disc; these `n` distinct roots
exhaust the degree bound, so `p` has degree `n`, simple roots enumerated by `α`, and any isolated
real disc of a real polynomial contains a real root
(`Polynomial.exists_isRootEnumeration_of_forall_norm_eval_lt`,
`Polynomial.IsRootEnumeration.im_eq_zero_of_norm_sub_lt`). Conversely, when all other roots stay at
distance at least `1` from `z` and all roots are bounded by `B ≥ 1`, `p.supNorm * ‖z - αᵢ‖` is
bounded above by `(2 B) ^ n * ‖p.eval z‖`
(`Polynomial.IsRootEnumeration.supNorm_mul_norm_sub_le_two_mul_pow_mul_norm_eval`).

## References

* E. Wirsing, *Approximation mit algebraischen Zahlen beschränkten Grades*, J. reine angew. Math.
  **206** (1961), 67–77, §2.
* Y. Bugeaud, *Approximation by Algebraic Numbers*, Cambridge University Press (2004), §3.4,
  Lemma 3.4 and Theorem 3.4.
-/

public section

open scoped ComplexConjugate

namespace Polynomial

/-! ### Value lower bounds away from the roots -/

/-- If `0 ≤ r ≤ 1` and `r ≤ ‖z - α‖`, then `‖z - α‖` controls `max 1 ‖α‖` with constant
`r / (2 (‖z‖ + 1))`. -/
private theorem div_two_mul_norm_add_one_mul_max_le_norm_sub {z α : ℂ} {r : ℝ} (hr₀ : 0 ≤ r)
    (hr₁ : r ≤ 1) (h : r ≤ ‖z - α‖) :
    r / (2 * (‖z‖ + 1)) * max 1 ‖α‖ ≤ ‖z - α‖ := by
  set D : ℝ := 2 * (‖z‖ + 1)
  have hD : 0 < D := by positivity
  rcases le_or_gt ‖α‖ D with hα | hα
  · have hmax : max 1 ‖α‖ ≤ D := max_le (by linarith [norm_nonneg z]) hα
    calc r / D * max 1 ‖α‖ ≤ r / D * D := by gcongr
      _ = r := div_mul_cancel₀ r hD.ne'
      _ ≤ ‖z - α‖ := h
  · -- Far from the origin, `‖z - α‖ ≥ ‖α‖ - ‖z‖ > ‖α‖ / 2`.
    have hmax : max 1 ‖α‖ = ‖α‖ := max_eq_right (by linarith [norm_nonneg z])
    have hrd : r / D ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hD zero_lt_two]
      linarith [norm_nonneg z]
    have htri : ‖α‖ - ‖z‖ ≤ ‖z - α‖ := by
      simpa [norm_sub_rev] using norm_sub_norm_le α z
    rw [hmax]
    calc r / D * ‖α‖ ≤ 1 / 2 * ‖α‖ := by gcongr
      _ ≤ ‖α‖ - ‖z‖ := by linarith
      _ ≤ ‖z - α‖ := htri

/-- Multiplying the single-factor estimate over a multiset of roots bounds the product of
`max 1 ‖α‖` by the product of `‖z - α‖`. -/
private theorem multiset_prod_max_le_norm_prod_sub (s : Multiset ℂ) (z : ℂ) {r : ℝ}
    (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) (h : ∀ α ∈ s, r ≤ ‖z - α‖) :
    (r / (2 * (‖z‖ + 1))) ^ Multiset.card s * (s.map fun α ↦ max 1 ‖α‖).prod ≤
      ‖(s.map fun α ↦ z - α).prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons α s ih =>
    simp only [Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons, pow_succ, norm_mul]
    have hα := div_two_mul_norm_add_one_mul_max_le_norm_sub hr₀ hr₁
      (h α (Multiset.mem_cons_self α s))
    have hs := ih fun β hβ ↦ h β (Multiset.mem_cons_of_mem hβ)
    have hpos : 0 ≤ (s.map fun β ↦ max 1 ‖β‖).prod :=
      Multiset.prod_nonneg fun x hx ↦ by
        obtain ⟨β, -, rfl⟩ := Multiset.mem_map.1 hx
        positivity
    calc (r / (2 * (‖z‖ + 1))) ^ Multiset.card s * (r / (2 * (‖z‖ + 1))) *
          (max 1 ‖α‖ * (s.map fun β ↦ max 1 ‖β‖).prod)
        = (r / (2 * (‖z‖ + 1)) * max 1 ‖α‖) *
            ((r / (2 * (‖z‖ + 1))) ^ Multiset.card s * (s.map fun β ↦ max 1 ‖β‖).prod) := by ring
      _ ≤ ‖z - α‖ * ‖(s.map fun β ↦ z - β).prod‖ :=
          mul_le_mul hα hs (by positivity) (norm_nonneg _)

/-- If `p ∈ ℂ[X]` has no root within `r` (`0 ≤ r ≤ 1`) of `z`, then its Mahler measure is bounded
in terms of `‖p.eval z‖`: `(r / (2 (‖z‖ + 1))) ^ deg p * M(p) ≤ ‖p(z)‖`. -/
theorem mahlerMeasure_le_of_forall_isRoot_le_norm_sub (p : ℂ[X]) (z : ℂ) {r : ℝ}
    (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) (hroot : ∀ α : ℂ, p.IsRoot α → r ≤ ‖z - α‖) :
    (r / (2 * (‖z‖ + 1))) ^ p.natDegree * p.mahlerMeasure ≤ ‖p.eval z‖ := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  have hcards : Multiset.card p.roots = p.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have heval : p.eval z = p.leadingCoeff * (p.roots.map fun α ↦ z - α).prod := by
    conv_lhs => rw [(IsAlgClosed.splits p).eq_prod_roots]
    simp [eval_multiset_prod]
  rw [heval, norm_mul, mahlerMeasure_eq_leadingCoeff_mul_prod_roots, ← hcards]
  have hprod := multiset_prod_max_le_norm_prod_sub p.roots z hr₀ hr₁
    fun α hα ↦ hroot α ((mem_roots hp).1 hα)
  calc (r / (2 * (‖z‖ + 1))) ^ Multiset.card p.roots *
        (‖p.leadingCoeff‖ * (p.roots.map fun α ↦ max 1 ‖α‖).prod)
      = ‖p.leadingCoeff‖ *
          ((r / (2 * (‖z‖ + 1))) ^ Multiset.card p.roots *
            (p.roots.map fun α ↦ max 1 ‖α‖).prod) := by ring
    _ ≤ ‖p.leadingCoeff‖ * ‖(p.roots.map fun α ↦ z - α).prod‖ := by gcongr

/-- If `p ∈ ℂ[X]` of degree at most `n` has no root within `r` (`0 ≤ r ≤ 1`) of `z`, then
`(r / (4 (‖z‖ + 1))) ^ n * p.supNorm ≤ ‖p.eval z‖`. -/
theorem supNorm_le_of_forall_isRoot_le_norm_sub (p : ℂ[X]) (z : ℂ) {n : ℕ}
    (hn : p.natDegree ≤ n) {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1)
    (hroot : ∀ α : ℂ, p.IsRoot α → r ≤ ‖z - α‖) :
    (r / (4 * (‖z‖ + 1))) ^ n * p.supNorm ≤ ‖p.eval z‖ := by
  have hle1 : r / (4 * (‖z‖ + 1)) ≤ 1 :=
    div_le_one_of_le₀ (by linarith [norm_nonneg z]) (by positivity)
  have hpow : (r / (4 * (‖z‖ + 1))) ^ n ≤ (r / (4 * (‖z‖ + 1))) ^ p.natDegree :=
    pow_le_pow_of_le_one (by positivity) hle1 hn
  have hsup : p.supNorm ≤ 2 ^ p.natDegree * p.mahlerMeasure :=
    p.supNorm_le_choose_natDegree_div_two_mul_mahlerMeasure.trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.choose_le_two_pow _ _)
        p.mahlerMeasure_nonneg)
  calc (r / (4 * (‖z‖ + 1))) ^ n * p.supNorm
      ≤ (r / (4 * (‖z‖ + 1))) ^ p.natDegree * (2 ^ p.natDegree * p.mahlerMeasure) :=
        mul_le_mul hpow hsup p.supNorm_nonneg (by positivity)
    _ = (r / (2 * (‖z‖ + 1))) ^ p.natDegree * p.mahlerMeasure := by
        rw [← mul_assoc, ← mul_pow]
        congr 2
        field_simp
        ring
    _ ≤ ‖p.eval z‖ := p.mahlerMeasure_le_of_forall_isRoot_le_norm_sub z hr₀ hr₁ hroot

/-- **Root location from a small value.** If `p ∈ ℂ[X]` of degree at most `n` satisfies
`‖p.eval z‖ < (r / (4 (‖z‖ + 1))) ^ n * p.supNorm` for `0 ≤ r ≤ 1`, then `p` has a complex root
strictly within `r` of `z`. -/
theorem exists_isRoot_norm_sub_lt_of_norm_eval_lt (p : ℂ[X]) (z : ℂ) {n : ℕ}
    (hn : p.natDegree ≤ n) {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1)
    (hlt : ‖p.eval z‖ < (r / (4 * (‖z‖ + 1))) ^ n * p.supNorm) :
    ∃ α : ℂ, p.IsRoot α ∧ ‖z - α‖ < r := by
  by_contra! h
  exact hlt.not_ge (p.supNorm_le_of_forall_isRoot_le_norm_sub z hn hr₀ hr₁ h)

/-! ### Complete root enumeration from separated small values -/

/-- If a nonzero `p ∈ ℂ[X]` of degree at most `Fintype.card ι` is small relative to `p.supNorm` at
points `β : ι → ℂ` pairwise at distance at least `2 r` (`0 ≤ r ≤ 1`), then `p` has degree
`Fintype.card ι` and an injective root enumeration `α : ι → ℂ` with `‖β i - α i‖ < r` for every
`i`. -/
theorem exists_isRootEnumeration_of_forall_norm_eval_lt {ι : Type*} [Fintype ι] (p : ℂ[X])
    (hp : p ≠ 0) (hn : p.natDegree ≤ Fintype.card ι) {β : ι → ℂ} {r : ℝ} (hr₀ : 0 ≤ r)
    (hr₁ : r ≤ 1) (hsep : Pairwise fun i j ↦ 2 * r ≤ ‖β i - β j‖)
    (heval : ∀ i, ‖p.eval (β i)‖ < (r / (4 * (‖β i‖ + 1))) ^ Fintype.card ι * p.supNorm) :
    ∃ α : ι → ℂ, Function.Injective α ∧ p.IsRootEnumeration α ∧ p.natDegree = Fintype.card ι ∧
      ∀ i, ‖β i - α i‖ < r := by
  classical
  choose α hroot hdist using fun i ↦
    p.exists_isRoot_norm_sub_lt_of_norm_eval_lt (β i) hn hr₀ hr₁ (heval i)
  -- Disjoint open `r`-balls make the chosen roots pairwise distinct.
  have hinj : Function.Injective α := fun i j hij ↦ by_contra fun hne ↦ by
    have htri := norm_sub_le (β i - α i) (β j - α j)
    rw [hij, sub_sub_sub_cancel_right] at htri
    linarith [hsep hne, hij ▸ hdist i, hdist j]
  let f : ι → p.rootSet ℂ := fun i ↦ ⟨α i, (mem_rootSet_of_ne hp).2 (hroot i)⟩
  have hf_inj : Function.Injective f := fun i j h ↦ hinj (Subtype.ext_iff.1 h)
  have hcard_ge : Fintype.card ι ≤ Fintype.card (p.rootSet ℂ) :=
    Fintype.card_le_of_injective f hf_inj
  have hcard_le : Fintype.card (p.rootSet ℂ) ≤ p.natDegree := by
    simpa [rootSet_def] using
      (Multiset.toFinset_card_le (p.aroots ℂ)).trans p.card_roots_map_le_natDegree
  have hdeg : p.natDegree = Fintype.card ι := by omega
  let e : Fin p.natDegree ≃ ι := (Fintype.equivFinOfCardEq hdeg.symm).symm
  have hcard : Fintype.card (Fin p.natDegree) = Fintype.card (p.rootSet ℂ) := by
    rw [Fintype.card_fin]
    omega
  have hg_bij : Function.Bijective (f ∘ e) :=
    (Fintype.bijective_iff_injective_and_card (f ∘ e)).2 ⟨hf_inj.comp e.injective, hcard⟩
  have henum : p.IsRootEnumeration (α ∘ e) :=
    isRootEnumeration_numbering (Equiv.ofBijective (f ∘ e) hg_bij)
  rw [isRootEnumeration_comp_equiv_iff] at henum
  exact ⟨α, hinj, henum, hdeg, hdist⟩

namespace IsRootEnumeration

/-- If `α : ι → ℂ` is a root enumeration of a real polynomial `p` and `α i` is the unique entry
strictly within `r` of a real point `x`, then `α i` is real: complex conjugation permutes the roots
while preserving distance to `x`. -/
theorem im_eq_zero_of_norm_sub_lt {ι : Type*} [Fintype ι] {p : ℝ[X]} {α : ι → ℂ}
    (hα : p.IsRootEnumeration α) {i : ι} {x r : ℝ}
    (hxi : ‖(x : ℂ) - α i‖ < r) (hfar : ∀ j ≠ i, r ≤ ‖(x : ℂ) - α j‖) :
    (α i).im = 0 := by
  have hmem : α i ∈ p.rootSet ℂ := hα.range_eq_rootSet ▸ Set.mem_range_self i
  rw [mem_rootSet] at hmem
  have hconj : conj (α i) ∈ p.rootSet ℂ := by
    rw [mem_rootSet]
    exact ⟨hmem.1, by rw [aeval_conj, hmem.2, map_zero]⟩
  obtain ⟨j, hj⟩ := hα.range_eq_rootSet.symm ▸ hconj
  have hxj : ‖(x : ℂ) - α j‖ < r := by
    have heq : (x : ℂ) - α j = conj ((x : ℂ) - α i) := by simp [← hj]
    rwa [heq, RCLike.norm_conj]
  have hji : j = i := by_contra fun hne ↦ (hfar j hne).not_gt hxj
  exact Complex.conj_eq_iff_im.1 (hj.symm.trans (congrArg α hji))

/-- **Value lower bound near an isolated simple root.** Let `α : ι → ℂ` enumerate the roots of
`p ∈ ℂ[X]`. If all roots have norm at most `B ≥ 1` and all entries `α j` with `j ≠ i` stay at
distance at least `1` from `z`, then
`p.supNorm * ‖z - α i‖ ≤ (2 * B) ^ Fintype.card ι * ‖p.eval z‖`. -/
theorem supNorm_mul_norm_sub_le_two_mul_pow_mul_norm_eval {ι : Type*} [Fintype ι] {p : ℂ[X]}
    {α : ι → ℂ} (hα : p.IsRootEnumeration α) (i : ι) {z : ℂ} {B : ℝ}
    (hB : 1 ≤ B) (hαB : ∀ j, ‖α j‖ ≤ B) (hfar : ∀ j ≠ i, 1 ≤ ‖z - α j‖) :
    p.supNorm * ‖z - α i‖ ≤ (2 * B) ^ Fintype.card ι * ‖p.eval z‖ := by
  classical
  have hdeg_eq : p.natDegree = Fintype.card ι :=
    IsAlgClosed.card_roots_eq_natDegree.symm.trans (by simpa using hα.card_roots)
  have hfac : p = C p.leadingCoeff * ∏ j, (X - C (α j)) := by
    simpa using hα.eq_C_mul_prod_X_sub_C (by simpa using hdeg_eq.le)
  have heval : ‖p.eval z‖ =
      ‖p.leadingCoeff‖ * (‖z - α i‖ * ∏ j ∈ Finset.univ.erase i, ‖z - α j‖) := by
    conv_lhs => rw [hfac]
    simp only [eval_mul, eval_C, eval_prod, eval_sub, eval_X, norm_mul, norm_prod]
    rw [← Finset.mul_prod_erase Finset.univ (fun j ↦ ‖z - α j‖) (Finset.mem_univ i)]
  have hprod1 : 1 ≤ ∏ j ∈ Finset.univ.erase i, ‖z - α j‖ := by
    simpa using Finset.prod_le_prod₀ (s := Finset.univ.erase i) (f := fun _ ↦ (1 : ℝ))
      (g := fun j ↦ ‖z - α j‖) (fun _ _ ↦ zero_le_one)
      fun j hj ↦ hfar j (Finset.ne_of_mem_erase hj)
  have hlc : ‖p.leadingCoeff‖ * ‖z - α i‖ ≤ ‖p.eval z‖ := by
    rw [heval, ← mul_assoc]
    exact le_mul_of_one_le_right (by positivity) hprod1
  -- Bound `p.supNorm` via `p.mahlerMeasure` and the root bound `B`.
  have hroots : p.roots = Finset.univ.val.map α := by
    simpa [isRootEnumeration_iff] using hα
  have hmahler : p.mahlerMeasure ≤ ‖p.leadingCoeff‖ * B ^ Fintype.card ι := by
    rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots, hroots, Multiset.map_map,
      ← Finset.prod_eq_multiset_prod]
    gcongr
    calc ∏ j : ι, max 1 ‖α j‖ ≤ ∏ _j : ι, B :=
          Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) fun j _ ↦ max_le hB (hαB j)
      _ = B ^ Fintype.card ι := by simp
  have hsup : p.supNorm ≤ (2 * B) ^ Fintype.card ι * ‖p.leadingCoeff‖ := by
    calc p.supNorm ≤ 2 ^ p.natDegree * p.mahlerMeasure :=
          p.supNorm_le_choose_natDegree_div_two_mul_mahlerMeasure.trans
            (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.choose_le_two_pow _ _)
              p.mahlerMeasure_nonneg)
      _ ≤ 2 ^ Fintype.card ι * (‖p.leadingCoeff‖ * B ^ Fintype.card ι) := by rw [hdeg_eq]; gcongr
      _ = (2 * B) ^ Fintype.card ι * ‖p.leadingCoeff‖ := by rw [mul_pow]; ring
  calc p.supNorm * ‖z - α i‖ ≤ (2 * B) ^ Fintype.card ι * ‖p.leadingCoeff‖ * ‖z - α i‖ := by gcongr
    _ = (2 * B) ^ Fintype.card ι * (‖p.leadingCoeff‖ * ‖z - α i‖) := by ring
    _ ≤ (2 * B) ^ Fintype.card ι * ‖p.eval z‖ := by gcongr

end IsRootEnumeration

end Polynomial
