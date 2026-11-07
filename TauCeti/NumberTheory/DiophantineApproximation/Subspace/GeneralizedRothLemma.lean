/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DiophantineApproximation.Roth.IndexEstimate
public import TauCeti.RingTheory.MvPolynomial.FormIndex.Dehomogenize
public import TauCeti.RingTheory.MvPolynomial.FormIndex.Specialization

import TauCeti.NumberTheory.Height.Basic

/-!
# The generalized Roth lemma for the index along linear forms

**Bombieri–Gubler's generalized Roth lemma** (`MvPolynomial.formIndex_le_of_degree_ratio`, Lemma
7.5.19) bounds the index `MvPolynomial.formIndex d M P` of a nonzero multihomogeneous polynomial
`P` in `m ≥ 1` blocks of variables `Fin m × ι` over a number field `K` along a family of linear
forms `M : Fin m → ι → K`. Assuming partial block degrees `e h ≤ d h` with rapidly decreasing
weights `d (h + 1) ≤ σ d h` (`0 < σ ≤ 1 / 2`) and large projective heights of the forms,

`(card ι - 1) σ⁻¹ (h(P) + 4 m d 0 [K : ℚ]) ≤ d h · h(M h)`

for every block `h : Fin m` (on a nontrivial index type `ι`), the index satisfies

`formIndex d M P ≤ 2 m σ ^ (1 / 2 ^ (m - 1))`.

In Schmidt's proof of the Subspace Theorem, `P` is the multihomogeneous auxiliary polynomial built
by Siegel's lemma, and `M h` is the normal form of the hyperplane `V(Q_h)` at `m` widely spaced
levels `Q_0, …, Q_{m-1}` sharing the same subspace direction; the small-index bound produced here,
combined with `MvPolynomial.exists_eval_hasseDeriv_ne_zero_of_ne_zero`, yields a low-order Hasse
derivative of `P` that does not vanish identically on `∏ h, V(Q_h)`.

## Proof outline

1. Because `[Nontrivial ι]` gives `card ι - 1 ≥ 1` and `4 m d 0 [K : ℚ] > 0`, the height hypothesis
   forces `h(M h) > 0` and hence `M h ≠ 0` in every block `h`.
2. By `Height.exists_logHeight_le_mul_logHeight₁_div`, each block `h` admits two distinct
   coordinates `i₀ h ≠ i₁ h` with `M h (i₀ h) ≠ 0` such that
   `h(M h) ≤ (card ι - 1) h₁(M h (i₁ h) / M h (i₀ h))`.
3. Sequential minimal-exponent slicing (`MvPolynomial.exists_elimination`) eliminates all variables
   outside `{i₀ h, i₁ h}`, producing a nonzero multihomogeneous polynomial `Q` on `Fin m × Fin 2` of
   multidegree `e' ≤ e ≤ d` whose nonzero coefficients all occur among those of `P` (so
   `h(Q) ≤ h(P)`) and whose index along `![-α h, 1]` at `α h = - (M h (i₁ h) / M h (i₀ h))` is at
   least `formIndex d M P`.
4. Dehomogenizing `Q` via `MvPolynomial.blockDehomogenize` preserves nonvanishing and height
   (`MvPolynomial.IsMultiHomogeneous.logHeight_blockDehomogenize`) and equates the form index with
   the affine weighted index `weightedIndex d α (blockDehomogenize Q)`
   (`MvPolynomial.IsMultiHomogeneous.formIndex_eq_weightedIndex_blockDehomogenize`).
5. Applying Roth's lemma (`TauCeti.weightedIndex_le_of_logHeight_le`) to `blockDehomogenize Q` at
   `α` concludes the proof.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  Lemma 7.5.19.
* Ralf Stephan, `DiophantineApproximation/GeneralizedRothLemma.lean` in `rwst/Subspace-Theorems`,
  commit `09835cb23557ae5ae0cf55a9c4ab9055f5d60338` (Apache 2.0).
-/

public section

namespace MvPolynomial

open Height Module
open scoped ENNReal

section AdmissibleAbsValues

variable {K κ : Type*} [Field K] [AdmissibleAbsValues K]

/-- On a multihomogeneous polynomial `P` in two-coordinate blocks, `blockDehomogenize` induces a
bijection on nonzero coefficients and therefore preserves `mulHeight`. -/
theorem IsMultiHomogeneous.mulHeight_blockDehomogenize [Finite κ] [DecidableEq κ]
    {e : κ → ℕ} {P : MvPolynomial (κ × Fin 2) K} (hP : IsMultiHomogeneous e P) :
    (blockDehomogenize P).mulHeight = P.mulHeight :=
  le_antisymm
    (mulHeight_le_of_forall_exists_coeff_eq fun _ hm ↦
      let ⟨n, _, hn⟩ := IsMultiHomogeneous.exists_coeff_eq_of_mem_support_blockDehomogenize hP hm
      ⟨n, hn⟩)
    (mulHeight_le_of_forall_exists_coeff_eq fun _ hn ↦
      let ⟨m, _, _, hm⟩ := IsMultiHomogeneous.coeff_blockDehomogenize_eq_of_mem_support hP hn
      ⟨m, hm.symm⟩)

/-- On a multihomogeneous polynomial `P` in two-coordinate blocks, `blockDehomogenize` preserves
`logHeight`. -/
theorem IsMultiHomogeneous.logHeight_blockDehomogenize [Finite κ] [DecidableEq κ]
    {e : κ → ℕ} {P : MvPolynomial (κ × Fin 2) K} (hP : IsMultiHomogeneous e P) :
    (blockDehomogenize P).logHeight = P.logHeight := by
  rw [logHeight_eq_log_mulHeight, logHeight_eq_log_mulHeight,
    IsMultiHomogeneous.mulHeight_blockDehomogenize hP]

end AdmissibleAbsValues

section NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **Generalized Roth lemma for the index along linear forms** (Bombieri–Gubler, Lemma 7.5.19).
Let `P ≠ 0` be a multihomogeneous polynomial of multidegree `e ≤ d` in `m ≥ 1` blocks of variables
`Fin m × ι` over a number field `K`, with `[Nontrivial ι]`, positive weights `d` satisfying
`d (h + 1) ≤ σ d h` for `0 < σ ≤ 1 / 2`, and linear forms `M : Fin m → ι → K` satisfying
`(card ι - 1) σ⁻¹ (h(P) + 4 m d 0 [K : ℚ]) ≤ d h · h(M h)` for every `h`. Then
`formIndex d M P ≤ 2 m σ ^ (1 / 2 ^ (m - 1))`. -/
theorem formIndex_le_of_degree_ratio {m : ℕ} [NeZero m] {ι : Type*} [Fintype ι] [Nontrivial ι]
    {d e : Fin m → ℕ} {M : Fin m → ι → K} {P : MvPolynomial (Fin m × ι) K}
    (hP : P ≠ 0) (hPhom : IsMultiHomogeneous e P) (hed : ∀ h, e h ≤ d h)
    (hd : ∀ h, 0 < d h) {σ : ℝ} (hσ₀ : 0 < σ) (hσ : σ ≤ 1 / 2)
    (hratio : ∀ h h' : Fin m, (h' : ℕ) = h + 1 → (d h' : ℝ) ≤ σ * d h)
    (hM : ∀ h, (Fintype.card ι - 1 : ℝ) * σ⁻¹ * (P.logHeight + 4 * m * d 0 * finrank ℚ K) ≤
      d h * Height.logHeight (M h)) :
    formIndex d M P ≤ ENNReal.ofReal (2 * m * σ ^ ((1 : ℝ) / 2 ^ (m - 1))) := by
  have hc : 0 < (Fintype.card ι - 1 : ℝ) := by
    have : (1 : ℝ) < Fintype.card ι := Nat.one_lt_cast.mpr Fintype.one_lt_card
    linarith
  have hMne (h : Fin m) : M h ≠ 0 := by
    intro h0
    have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr (NeZero.pos m)
    have hd0 : (0 : ℝ) < d 0 := Nat.cast_pos.mpr (hd 0)
    have hK0 : (0 : ℝ) < finrank ℚ K := Nat.cast_pos.mpr finrank_pos
    have hP0 : 0 ≤ P.logHeight := MvPolynomial.logHeight_nonneg P
    have hlhs : 0 < (Fintype.card ι - 1 : ℝ) * σ⁻¹ *
        (P.logHeight + 4 * m * d 0 * finrank ℚ K) := by positivity
    have hrhs := hM h
    rw [h0, Height.logHeight_zero, mul_zero] at hrhs
    linarith
  choose i₀ i₁ hne hi₀ hdiv using fun h ↦ exists_logHeight_le_mul_logHeight₁_div (hMne h)
  obtain ⟨Q, e', hQne, he', hQhom, hQcoeff, hidx⟩ :=
    exists_elimination (d := d) hne hi₀ hP hPhom
  set α : Fin m → K := fun h ↦ - (M h (i₁ h) / M h (i₀ h))
  set F : MvPolynomial (Fin m) K := blockDehomogenize Q
  have hFne : F ≠ 0 := (IsMultiHomogeneous.blockDehomogenize_eq_zero hQhom).not.mpr hQne
  have hFdeg (h : Fin m) : F.degreeOf h ≤ d h :=
    (IsMultiHomogeneous.degreeOf_blockDehomogenize_le hQhom h).trans ((he' h).trans (hed h))
  have hFlog : F.logHeight ≤ P.logHeight :=
    (IsMultiHomogeneous.logHeight_blockDehomogenize hQhom).le.trans
      (logHeight_le_of_forall_exists_coeff_eq fun u hu ↦
        let ⟨n, _, hn⟩ := hQcoeff u hu
        ⟨n, hn⟩)
  have hα (h : Fin m) :
      σ⁻¹ * (F.logHeight + 4 * m * d 0 * finrank ℚ K) ≤ d h * logHeight₁ (α h) := by
    refine le_of_mul_le_mul_left ?_ hc
    have hdiv' : Height.logHeight (M h) ≤ (Fintype.card ι - 1 : ℝ) * logHeight₁ (α h) := by
      simpa [α, Nat.card_eq_fintype_card] using hdiv h
    calc (Fintype.card ι - 1 : ℝ) * (σ⁻¹ * (F.logHeight + 4 * m * d 0 * finrank ℚ K))
        ≤ (Fintype.card ι - 1 : ℝ) * (σ⁻¹ * (P.logHeight + 4 * m * d 0 * finrank ℚ K)) := by
          gcongr
      _ = (Fintype.card ι - 1 : ℝ) * σ⁻¹ * (P.logHeight + 4 * m * d 0 * finrank ℚ K) := by
          ring
      _ ≤ d h * Height.logHeight (M h) := hM h
      _ ≤ d h * ((Fintype.card ι - 1 : ℝ) * logHeight₁ (α h)) := by gcongr
      _ = (Fintype.card ι - 1 : ℝ) * (d h * logHeight₁ (α h)) := by ring
  calc formIndex d M P
      ≤ formIndex d (fun h ↦ ![-α h, 1]) Q := hidx
    _ = weightedIndex d α F :=
        IsMultiHomogeneous.formIndex_eq_weightedIndex_blockDehomogenize hQhom d α
    _ ≤ ENNReal.ofReal (2 * m * σ ^ ((1 : ℝ) / 2 ^ (m - 1))) :=
        TauCeti.weightedIndex_le_of_logHeight_le hFne hd hFdeg hσ₀ hσ hratio α hα

end NumberField

end MvPolynomial

end

namespace MvPolynomial

open Height Module
open scoped ENNReal

/-- `[Nontrivial ι]` cannot be omitted in `formIndex_le_of_degree_ratio`: on a one-element index
type `Unit`, `Fintype.card Unit - 1 = 0` makes the height lower bound vacuous (`0 ≤ 0`), while
`P = X (0, ())` along `M 0 () = 1` has `formIndex ![1] M P = 1 > 2 * 1 * (1 / 16)`. -/
example :
    let d : Fin 1 → ℕ := ![1]
    let M : Fin 1 → Unit → ℚ := fun _ _ ↦ 1
    let P : MvPolynomial (Fin 1 × Unit) ℚ := X (0, ())
    let σ : ℝ := 1 / 16
    P ≠ 0 ∧ IsMultiHomogeneous d P ∧ (∀ h, 0 < d h) ∧ 0 < σ ∧ σ ≤ 1 / 2 ∧
      (∀ h, (Fintype.card Unit - 1 : ℝ) * σ⁻¹ * (P.logHeight + 4 * 1 * d 0 * finrank ℚ ℚ) ≤
        d h * Height.logHeight (M h)) ∧
      ¬ formIndex d M P ≤ ENNReal.ofReal (2 * 1 * σ ^ ((1 : ℝ) / 2 ^ (1 - 1))) := by
  intro d M P σ
  refine ⟨X_ne_zero _, ?_, fun h ↦ by fin_cases h; decide, by norm_num [σ], by norm_num [σ],
    fun h ↦ by simp [M], ?_⟩
  · have hd : d = Pi.single (0 : Fin 1) 1 := funext fun h ↦ by fin_cases h; rfl
    rw [hd]
    exact isMultiHomogeneous_X (0 : Fin 1) ()
  · have hM : ∀ h : Fin 1, M h () ≠ 0 := fun _ ↦ one_ne_zero
    have hsub : substFormInv M (fun _ ↦ ()) P = X (0, ()) := by
      simp [P, M, Finset.univ_unique]
    have hidx : formIndex d M P = 1 := by
      rw [formIndex_eq_iInf hM, hsub, ← pow_one (X (0, ()) : MvPolynomial (Fin 1 × Unit) ℚ),
        X_pow_eq_monomial, support_monomial, ite_eq_right one_ne_zero, Finset.iInf_singleton]
      simp [d]
    rw [hidx, not_le]
    have hlt : 2 * 1 * σ ^ ((1 : ℝ) / 2 ^ (1 - 1)) < 1 := by norm_num [σ]
    simpa using ENNReal.ofReal_lt_ofReal_iff zero_lt_one |>.mpr hlt

/-- The factor `card ι - 1` in `Height.exists_logHeight_le_mul_logHeight₁_div` cannot be improved to
`1`: for `x = ![6, 3, 2] : Fin 3 → ℚ`, `Height.mulHeight x = 6`, while every coordinate ratio
`x i₁ / x i₀` has `mulHeight₁ ≤ 3 < 6`. -/
example :
    let x : Fin 3 → ℚ := ![6, 3, 2]
    Height.mulHeight x = 6 ∧ ∀ i₀ i₁ : Fin 3, mulHeight₁ (x i₁ / x i₀) ≤ 3 := by
  intro x
  refine ⟨?_, fun i₀ i₁ ↦ ?_⟩
  · let y : Fin 3 → ℤ := ![6, 3, 2]
    have hxy : x = ((↑) : ℤ → ℚ) ∘ y := by ext i; fin_cases i <;> simp [x, y]
    have hgcd : Finset.univ.gcd y = 1 := by decide
    rw [hxy, Rat.mulHeight_eq_max_abs_of_gcd_eq_one hgcd]
    have hsup : (⨆ i, |y i|) = 6 :=
      le_antisymm (ciSup_le fun i ↦ by fin_cases i <;> decide)
        (Finite.le_ciSup_of_le 0 (by decide))
    exact_mod_cast hsup
  · fin_cases i₀ <;> fin_cases i₁ <;>
      · rw [Rat.mulHeight₁_eq_max]
        norm_num [x]

/-- Non-vacuous instantiation of `formIndex_le_of_degree_ratio` over `ℚ` with `m = 1`, `ι = Fin 3`,
`d = ![1]`, `σ = 1 / 4`, `M 0 = ![2 ^ 50, 1, 1]`, and `P = X (0, 1)`. -/
example :
    let M : Fin 1 → Fin 3 → ℚ := fun _ ↦ ![2 ^ 50, 1, 1]
    let P : MvPolynomial (Fin 1 × Fin 3) ℚ := X (0, 1)
    formIndex ![1] M P ≤ ENNReal.ofReal (1 / 2) := by
  intro M P
  have hP : P ≠ 0 := X_ne_zero _
  have hPhom : IsMultiHomogeneous ![1] P := by
    have hd : (![1] : Fin 1 → ℕ) = Pi.single 0 1 := funext fun h ↦ by fin_cases h; rfl
    rw [hd]
    exact isMultiHomogeneous_X (0 : Fin 1) (1 : Fin 3)
  have hPlog : P.logHeight = 0 := by
    dsimp only [P]
    rw [← pow_one (X (0, 1) : MvPolynomial (Fin 1 × Fin 3) ℚ), X_pow_eq_monomial,
      logHeight_monomial]
  have hMlog : 50 * Real.log 2 ≤ Height.logHeight (M 0) := by
    have hdiv := Height.logHeight₁_div_le_logHeight (M 0) 0 1
    have hval : M 0 0 / M 0 1 = (2 : ℚ) ^ 50 := by simp [M]
    rw [hval, Height.logHeight₁_pow] at hdiv
    push_cast at hdiv
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (by positivity)) hdiv
    rw [Height.logHeight₁_eq_log_mulHeight₁]
    refine Real.log_le_log zero_lt_two ?_
    rw [Rat.mulHeight₁_eq_max]
    norm_num
  have hbound :
      formIndex ![1] M P ≤ ENNReal.ofReal (2 * (1 : ℕ) * (1 / 4 : ℝ) ^ ((1 : ℝ) / 2 ^ (1 - 1))) :=
    formIndex_le_of_degree_ratio hP hPhom (fun _ ↦ le_rfl)
      (fun h ↦ by fin_cases h; decide) (by norm_num) (by norm_num)
      (fun h h' hh' ↦ by omega) fun h ↦ by
        rw [Subsingleton.elim h 0]
        have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
        simp only [Fintype.card_fin, hPlog, Module.finrank_self, Matrix.cons_val_zero, Nat.cast_one]
        norm_num
        linarith
  exact hbound.trans_eq (by norm_num)

end MvPolynomial
