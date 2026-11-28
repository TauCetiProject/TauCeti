/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.AlgebraicClosure.PolynomialApproximation
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import TauCeti.Analysis.Polynomial.RootLocation
import TauCeti.RingTheory.Valuation.ValuationSubring

/-!
# Simultaneous p-adic polynomial specialization at the powers of roots of unity

One tuple of roots of unity can be chosen so that each of its first `m` positive powers
satisfies the same polynomial valuation bounds. The order cutoff depends on the number
of variables, the power bound, the input radius and the valuation budget, but not on
polynomial degrees or the number of polynomials. The bounds on all coordinate valuations
also ensure that none of the prescribed powers of a coordinate is one.

The power substitution is the one in `New.Selmer.exists_rootsOfUnity_ellVal_eval_le` in
`grh/src/New/Congruences/Selmer/GeneralTheorem.lean` of lsernau/grh-lean (revision `72fead1`).
-/

public section

open Filter Finset MvPolynomial
open scoped NNReal Polynomial

namespace TauCeti

universe u v

variable {p : ℕ} [Fact p.Prime]

local notation "K" => PadicAlgCl p
local notation "V" =>
  AddValuation.ofNorm (R := PadicAlgCl p) (p : ℝ)
    (Nat.one_lt_cast.mpr (Nat.Prime.one_lt (Fact.out : p.Prime)))
local notation "O" => Valuation.valuationSubring (AddValuation.toValuation (V))

/-- Divide the input radius by `m + 1` before pulling it back along any of the power maps. -/
private theorem exists_shifted_pow_eq {x : O} {r : ℚ≥0} {k m : ℕ} (hk : k ∈ Icc 1 m)
    (hx : ((r : ℝ) : WithTop ℝ) ≤ V (x : K)) :
    ∃ y : O, (1 + y) ^ k - 1 = x ∧ (((r / (m + 1) : ℚ≥0) : ℝ) : WithTop ℝ) ≤ V (y : K) := by
  let t : ℝ := ((r / (m + 1) : ℚ≥0) : ℝ)
  have hk₀ : 0 < k := (mem_Icc.mp hk).1
  have hk₁ : (k : ℝ) ≤ (m : ℝ) + 1 := by
    exact_mod_cast (mem_Icc.mp hk).2.trans (Nat.le_succ m)
  have ht : t * k ≤ r := by
    calc
      _ ≤ t * ((m : ℝ) + 1) := mul_le_mul_of_nonneg_left hk₁ (by positivity)
      _ = _ := by simp [t]; field_simp
  have hp : (1 : ℝ) < p := Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt
  let f : K[X] := Polynomial.X ^ k - Polynomial.C (1 + (x : K))
  have hf : f.Monic := Polynomial.monic_X_pow_sub_C _ hk₀.ne'
  have hdegree : f.natDegree = k := Polynomial.natDegree_X_pow_sub_C _
  obtain ⟨a, ha, hdist⟩ := (IsAlgClosed.splits f).exists_mem_roots_norm_sub_pow_le
    (by simpa only [hdegree] using hk₀.ne') 1
  have ha' : a ^ k = 1 + (x : K) := Polynomial.mem_nthRoots hk₀ |>.mp ha
  rw [hf, norm_one, one_mul, hdegree, norm_sub_rev] at hdist
  have hnorm : ‖a - 1‖ ≤ (p : ℝ) ^ (-t) := by
    apply (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) hk₀.ne').mp
    rw [← Real.rpow_mul_natCast (by positivity), neg_mul]
    exact (by simpa [f] using hdist : ‖a - 1‖ ^ k ≤ ‖(x : K)‖).trans
      ((AddValuation.coe_le_ofNorm_iff hp).mp ((WithTop.coe_le_coe.mpr ht).trans hx))
  have hy := (AddValuation.coe_le_ofNorm_iff hp).mpr hnorm
  let y : O := ⟨a - 1, ((V).mem_toValuation_valuationSubring_iff _).mpr
    ((WithTop.coe_nonneg.mpr (by positivity : 0 ≤ t)).trans hy)⟩
  refine ⟨y, Subtype.ext ?_, hy⟩
  -- Calculate in the field, keeping the subtype's integrality proof out of the rewrites.
  have hy' : (y : K) = a - 1 := rfl
  have hfield : (1 + (y : K)) ^ k - 1 = (x : K) := by
    rw [hy', add_comm (1 : K), sub_add_cancel, ha', add_comm (1 : K), add_sub_cancel_right]
  exact hfield

/-- A shifted primitive root provides a test coordinate of small positive valuation. -/
private theorem exists_testCoordinate {ρ : ℚ≥0} (hρ : 0 < ρ) :
    ∃ r : ℚ≥0, 0 < r ∧ r ≤ ρ ∧ ∃ y : O, V (y : K) = ((r : ℝ) : WithTop ℝ) := by
  obtain ⟨h, hh, hr⟩ := ((eventually_ge_atTop 1).and
    (eventually_primePowerRootRadius_le (ℓ := p) hρ)).exists
  let : NeZero (p ^ h) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot K (p ^ h)
  have hval := ofNorm_sub_one_eq_primePowerRootRadius hh hζ
  have hpos := primePowerRootRadius_pos (ℓ := p) h
  refine ⟨primePowerRootRadius p h, by exact_mod_cast hpos, hr,
    ⟨ζ - 1, ((V).mem_toValuation_valuationSubring_iff _).mpr ?_⟩, hval⟩
  rw [hval]
  exact WithTop.coe_nonneg.mpr hpos.le

/-- Charge once for each input polynomial and coordinate test, for each requested power. -/
private theorem sum_testEvaluations_le {σ ι : Type*} [Fintype σ] [Fintype ι]
    (P : ι → MvPolynomial σ O) (x : ι → σ → O) {a : O} {r : ℚ≥0}
    (ha : V (a : K) = ((r : ℝ) : WithTop ℝ)) {β : ℝ≥0} {s₀ m : ℕ}
    (hs : Fintype.card σ ≤ s₀) (hP : ∑ i, V (↑(eval (x i) (P i)) : K) ≤ (β : ℝ)) :
    ∑ ki : (Icc 1 m : Finset ℕ) × (ι ⊕ σ),
        V (↑(eval (Sum.elim x (fun _ _ ↦ a) ki.2) (Sum.elim P X ki.2)) : K) ≤
      ((m • (β + s₀ • (r : ℝ≥0)) : ℝ≥0) : ℝ) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    eval_X, ha, sum_const, card_univ, Fintype.card_coe, Nat.card_Icc, Nat.add_sub_cancel]
  have hr : (0 : WithTop ℝ) ≤ (r : ℝ) := WithTop.coe_nonneg.mpr (by positivity)
  have h := nsmul_le_nsmul_right (add_le_add hP (nsmul_le_nsmul_left hr hs)) m
  have hB : (((m • (β + s₀ • (r : ℝ≥0)) : ℝ≥0) : ℝ) : WithTop ℝ) =
      m • (((β : ℝ) : WithTop ℝ) + s₀ • ((r : ℝ) : WithTop ℝ)) := by
    simp only [← WithTop.coe_nsmul, ← WithTop.coe_add, NNReal.coe_nsmul, NNReal.coe_add]
    rfl
  rw [hB]
  simpa only [nsmul_add] using h

/-- For any bounded range of positive powers, specialize an integral polynomial family at a
single tuple of prime-power roots of unity. If the input evaluations at points of valuation at
least `ρ` have total valuation at most `β`, then at every `k` from `1` through `m` the substitution
`X j ↦ ζ j ^ k - 1` loses at most `ε` for each polynomial and has coordinate valuations at most
`ρ`. The cutoff on the root orders is chosen before the polynomial family. -/
theorem exists_rootsOfUnity_ofNorm_eval_pow_le_add (s₀ m : ℕ)
    {ρ : ℚ≥0} (hρ : 0 < ρ) (β : ℝ≥0) {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ h₀ : ℕ, ∀ (σ : Type u) (ι : Type v) [Fintype σ] [Fintype ι]
      (P : ι → MvPolynomial σ O) (x : ι → σ → O), Fintype.card σ ≤ s₀ →
      (∀ i j, ((ρ : ℝ) : WithTop ℝ) ≤ V (x i j : K)) →
      (∑ i, V (↑(eval (x i) (P i)) : K) ≤ (β : ℝ)) →
      ∃ ζ : σ → O, (∀ j, ζ j ^ p ^ h₀ = 1) ∧ ∀ k ∈ Icc 1 m,
        (∀ j, V ((ζ j ^ k - 1 : O) : K) ≤ (ρ : ℝ)) ∧
        ∀ i, V (↑(eval (fun j ↦ ζ j ^ k - 1) (P i)) : K) ≤
          V (↑(eval (x i) (P i)) : K) + (ε : ℝ) := by
  classical
  have hhalf : 0 < ρ / 2 := by positivity
  obtain ⟨r, hr, hrρ, a, ha⟩ := exists_testCoordinate (p := p) hhalf
  let r₀ : ℚ≥0 := r / (m + 1)
  let δ : ℝ≥0 := min ε ((ρ : ℝ≥0) / 2)
  let B : ℝ≥0 := m • (β + s₀ • (r : ℝ≥0))
  obtain ⟨h₀, hspec⟩ := exists_rootsOfUnity_ofNorm_eval_le_add (p := p)
    s₀ (ρ := r₀) (by dsimp [r₀]; positivity) B (ε := δ) (by dsimp [δ]; positivity)
  refine ⟨h₀, fun σ ι _ _ P x hs hx hP ↦ ?_⟩
  -- Add each coordinate as a test polynomial, so that the same specialization controls
  -- the radii as well as the given evaluations, even if the input family is empty.
  let Q : ι ⊕ σ → MvPolynomial σ O := Sum.elim P X
  let z : ι ⊕ σ → σ → O := Sum.elim x (fun _ _ ↦ a)
  let J := (Icc 1 m : Finset ℕ)
  have hz (i : ι ⊕ σ) (j : σ) : ((r : ℝ) : WithTop ℝ) ≤ V (z i j : K) := by
    cases i with
    | inl i =>
      have hh : r ≤ ρ := hrρ.trans (div_le_self (by positivity) one_le_two)
      exact (WithTop.coe_le_coe.mpr (by exact_mod_cast hh)).trans (hx i j)
    | inr i => exact ha.ge
  choose y hy hyval using fun (ki : J × (ι ⊕ σ)) (j : σ) ↦
    exists_shifted_pow_eq (p := p) ki.1.property (hz ki.2 j)
  let F (ki : J × (ι ⊕ σ)) :=
    aeval (fun j ↦ ((1 + X j) ^ (ki.1 : ℕ) - 1 : MvPolynomial σ O)) (Q ki.2)
  have heval (w : σ → O) (ki : J × (ι ⊕ σ)) :
      eval w (F ki) = eval (fun j ↦ (1 + w j) ^ (ki.1 : ℕ) - 1) (Q ki.2) := by
    let g (j : σ) : MvPolynomial σ O := (1 + X j) ^ (ki.1 : ℕ) - 1
    have hg : (fun j ↦ aeval w (g j)) = fun j ↦ (1 + w j) ^ (ki.1 : ℕ) - 1 := by
      funext j
      simp [g]
    have h := comp_aeval_apply g (aeval w) (Q ki.2)
    rw [hg] at h
    exact h
  have hin (ki : J × (ι ⊕ σ)) : eval (y ki) (F ki) = eval (z ki.2) (Q ki.2) := by
    rw [heval, funext (hy ki)]
  have hsum : (∑ ki, V (↑(eval (y ki) (F ki)) : K)) ≤ (B : ℝ) := by
    simpa only [hin] using (sum_testEvaluations_le P x ha (m := m) hs hP)
  obtain ⟨ζ, hpow, _, hval⟩ := hspec σ (J × (ι ⊕ σ)) F y hs hyval hsum
  refine ⟨ζ, hpow, fun k hk ↦ ⟨fun j ↦ ?_, fun i ↦ ?_⟩⟩
  · have hh := hval (⟨k, hk⟩, Sum.inr j)
    rw [hin, heval] at hh
    simp only [Q, z, Sum.elim_inr, eval_X, ha, add_sub_cancel] at hh
    have hr' : (r : ℝ) ≤ (ρ : ℝ) / 2 := by exact_mod_cast hrρ
    have hδ : (δ : ℝ) ≤ (ρ : ℝ) / 2 := min_le_right _ _
    exact hh.trans (by rw [← WithTop.coe_add, WithTop.coe_le_coe]; linarith)
  · have hh := hval (⟨k, hk⟩, Sum.inl i)
    rw [hin, heval] at hh
    have hδε : ((δ : ℝ) : WithTop ℝ) ≤ (ε : ℝ) := by exact_mod_cast min_le_left ε _
    simpa only [Q, z, Sum.elim_inl, add_sub_cancel] using hh.trans (add_le_add le_rfl hδε)

end TauCeti
