/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Length
public import TauCeti.RingTheory.Polynomial.GaussianBinomial
import Mathlib.LinearAlgebra.Pi
import TauCeti.LinearAlgebra.Submodule.Prod.Index
import TauCeti.RingTheory.DiscreteValuationRing.Basic
import TauCeti.RingTheory.Ideal.Norm.AbsNorm
import TauCeti.RingTheory.Length

/-!
# Submodules of given colength in a free module over a discrete valuation ring

Let `O` be a discrete valuation ring whose residue field has `q` elements, and `M` a free
`O`-module of rank `j + 1`. The number of submodules of `M` of colength `e`, that is of index
`q ^ e`, is the Gaussian binomial coefficient `[e + j, j]_q`
(`TauCeti.IsDiscreteValuationRing.card_submodule_length_quotient_eq_gaussianBinomial`).
In the notation of a rank `j ≥ 1` this is `[e + j - 1, j - 1]_q`. It is at most
`q ^ (e (j + 1))` and at most `(e + 1) ^ j q ^ (e j)`; in rank `j` the second bound reads
`(e + 1) ^ (j - 1) q ^ (e (j - 1))`.

The count is by induction on the rank. In `O × N`, a submodule `L` of index `q ^ e` has a
projection `ϖ^c O` to `O`, of index `q ^ c`
(`TauCeti.IsDiscreteValuationRing.cardQuot_eq_pow_iff`), and an intersection `K` with `N`, of
index `q ^ (e - c)`, and the submodules with given `c` and `K` are the graphs `O (ϖ^c, x) + K` for
the classes `x ∈ N ⧸ K` (`Submodule.prodFiberEquivQuotient`). Writing `s_j(e)` for the number
of submodules of index `q ^ e` in `O^j`, this gives
`s_{j+1}(e) = ∑_{k ≤ e} q^k s_j(k)`, the column recursion of the Gaussian binomial coefficients
(`TauCeti.gaussianBinomial_add_succ_eq_sum`).

## Main results

* `TauCeti.IsDiscreteValuationRing.card_submodule_prod_cardQuot_eq_sum`: the recursion
  `s_{O × N}(e) = ∑_{k ≤ e} q^k s_N(k)`.
* `TauCeti.IsDiscreteValuationRing.card_submodule_cardQuot_eq_gaussianBinomial`,
  `TauCeti.IsDiscreteValuationRing.card_submodule_length_quotient_eq_gaussianBinomial`: the
  number of submodules of index `q ^ e`, equivalently of colength `e`, of a free module of
  rank `j + 1` is `[e + j, j]_q`.
* `TauCeti.IsDiscreteValuationRing.card_submodule_length_quotient_le_pow`,
  `TauCeti.IsDiscreteValuationRing.card_submodule_length_quotient_le_succ_pow_mul_pow`: the bounds
  `q ^ (e (j + 1))` and `(e + 1) ^ j q ^ (e j)`.

## Attribution

The decomposition of a submodule of `O × N` into its projection and its intersection with `N`
is adapted from the proof of `submoduleZeta_prod_le` in the file
`src/New/Spanning/RemainingTerms/Discriminants.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), which bounds
the zeta function of `R ^ r` by the same induction. The exact count is new here.

## References

* L. Solomon, *Zeta functions and integral representation theory*, Adv. Math. 26 (1977),
  306-326 (the zeta function `∏_{t<j} (1 - q^t X)⁻¹` of `O ^ j`, whose coefficients are these
  counts).
-/

public section

open IsLocalRing Module Submodule Finset TauCeti

namespace TauCeti.IsDiscreteValuationRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
  [Finite (ResidueField O)]

section Prod

variable {N : Type*} [AddCommGroup N] [Module O N]

/-- A submodule of `O × N` of index `q ^ e` projects onto `ϖ^(e - k) O` and meets `N` in a
submodule of index `q ^ k`, for some `k ≤ e`. -/
theorem exists_map_fst_eq_span_pow_of_cardQuot_eq (hϖ : Irreducible ϖ) {e : ℕ}
    {L : Submodule O (O × N)} (hL : L.cardQuot = Nat.card (ResidueField O) ^ e) :
    ∃ k : Fin (e + 1), L.map (LinearMap.fst O O N) = O ∙ ϖ ^ (e - k) ∧
      (L.comap (LinearMap.inr O O N)).cardQuot = Nat.card (ResidueField O) ^ (k : ℕ) := by
  have hq : 1 < Nat.card (ResidueField O) := Finite.one_lt_card
  rw [cardQuot_eq_cardQuot_map_fst_mul_cardQuot_comap_inr] at hL
  obtain ⟨c, hc⟩ := exists_eq_span_pow_of_cardQuot_ne_zero hϖ
    (left_ne_zero_of_mul (hL.trans_ne (by positivity)))
  rw [hc, cardQuot_span_pow hϖ] at hL
  have hce : c ≤ e := (Nat.pow_dvd_pow_iff_le_right hq).1 (Dvd.intro _ hL)
  refine ⟨⟨e - c, by omega⟩, by rwa [Nat.sub_sub_self hce, Ideal.submodule_span_eq], ?_⟩
  rw [← Nat.add_sub_of_le hce, pow_add] at hL
  exact Nat.eq_of_mul_eq_mul_left (by positivity) hL

/-- The colength data of a submodule `L ≤ O × N` of index `q ^ e`: the colength `k ≤ e` of its
intersection with `N`, and this intersection. -/
private noncomputable def colengthData (hϖ : Irreducible ϖ) (e : ℕ)
    (L : {L : Submodule O (O × N) // L.cardQuot = Nat.card (ResidueField O) ^ e}) :
    Σ k : Fin (e + 1), {K : Submodule O N // K.cardQuot = Nat.card (ResidueField O) ^ (k : ℕ)} :=
  ⟨(exists_map_fst_eq_span_pow_of_cardQuot_eq hϖ L.property).choose,
    ⟨L.val.comap (LinearMap.inr O O N),
      (exists_map_fst_eq_span_pow_of_cardQuot_eq hϖ L.property).choose_spec.right⟩⟩

private theorem colengthData_eq_iff (hϖ : Irreducible ϖ) {e : ℕ}
    (L : {L : Submodule O (O × N) // L.cardQuot = Nat.card (ResidueField O) ^ e})
    (b : Σ k : Fin (e + 1),
      {K : Submodule O N // K.cardQuot = Nat.card (ResidueField O) ^ (k : ℕ)}) :
    colengthData hϖ e L = b ↔ L.val.map (LinearMap.fst O O N) = O ∙ ϖ ^ (e - b.fst) ∧
      L.val.comap (LinearMap.inr O O N) = b.snd.val := by
  -- The first component of `colengthData hϖ e L` is by definition the chosen witness.
  have hspec : L.val.map (LinearMap.fst O O N) = O ∙ ϖ ^ (e - (colengthData hϖ e L).fst) :=
    (exists_map_fst_eq_span_pow_of_cardQuot_eq hϖ L.property).choose_spec.left
  constructor
  · rintro rfl
    exact ⟨hspec, rfl⟩
  · rintro ⟨hfst, hinr⟩
    refine Sigma.subtype_ext (Fin.ext ?_) hinr
    have hq : 1 < Nat.card (ResidueField O) := Finite.one_lt_card
    have h := congrArg Submodule.cardQuot (hspec.symm.trans hfst)
    rw [Ideal.submodule_span_eq, Ideal.submodule_span_eq, cardQuot_span_pow hϖ,
      cardQuot_span_pow hϖ] at h
    have h₁ := Nat.pow_right_injective hq h
    have h₂ := (colengthData hϖ e L).fst.isLt
    have h₃ := b.fst.isLt
    omega

/-- The submodules of `O × N` of index `q ^ e` with colength data `⟨k, K⟩` are those that
project onto `ϖ^(e - k) O` and meet `N` in `K`. -/
private noncomputable def fiberEquiv (hϖ : Irreducible ϖ) (e : ℕ)
    (b : Σ k : Fin (e + 1),
      {K : Submodule O N // K.cardQuot = Nat.card (ResidueField O) ^ (k : ℕ)}) :
    {L // colengthData hϖ e L = b} ≃
      {L : Submodule O (O × N) // L.map (LinearMap.fst O O N) = O ∙ ϖ ^ (e - b.fst) ∧
        L.comap (LinearMap.inr O O N) = b.snd.val} where
  toFun L := ⟨L.val.val, (colengthData_eq_iff hϖ L.val b).1 L.property⟩
  invFun L := by
    refine ⟨⟨L.val, ?_⟩, (colengthData_eq_iff hϖ _ b).2 L.property⟩
    rw [cardQuot_eq_cardQuot_map_fst_mul_cardQuot_comap_inr, L.property.left, L.property.right,
      b.snd.property, Ideal.submodule_span_eq, cardQuot_span_pow hϖ, ← pow_add,
      Nat.sub_add_cancel (Nat.lt_succ_iff.1 b.fst.isLt)]
  left_inv _ := rfl
  right_inv _ := rfl

/-- The submodules of `O × N` of index `q ^ e` decompose by their colength data `⟨k, K⟩`, and
those with given data are the graphs `O (ϖ^(e - k), x) + K`, `x ∈ N ⧸ K`. -/
private noncomputable def prodEquiv (hϖ : Irreducible ϖ) (e : ℕ) :
    {L : Submodule O (O × N) // L.cardQuot = Nat.card (ResidueField O) ^ e} ≃
      Σ b : Σ k : Fin (e + 1),
        {K : Submodule O N // K.cardQuot = Nat.card (ResidueField O) ^ (k : ℕ)}, N ⧸ b.snd.val :=
  (Equiv.sigmaFiberEquiv (colengthData hϖ e)).symm.trans <| Equiv.sigmaCongrRight fun b ↦
    (fiberEquiv hϖ e b).trans <| prodFiberEquivQuotient
      (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ hϖ.ne_zero)) b.snd.val

variable (O N) in
/-- If `N` has finitely many submodules of each index `q ^ k`, then so has `O × N`. -/
theorem finite_submodule_prod_cardQuot_eq
    (hN : ∀ k : ℕ, Finite {K : Submodule O N // K.cardQuot = Nat.card (ResidueField O) ^ k})
    (e : ℕ) : Finite {L : Submodule O (O × N) // L.cardQuot = Nat.card (ResidueField O) ^ e} := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible O
  have (b : Σ k : Fin (e + 1),
      {K : Submodule O N // K.cardQuot = Nat.card (ResidueField O) ^ (k : ℕ)}) :
      Finite (N ⧸ b.snd.val) :=
    finite_quotient_of_cardQuot_ne_zero (b.snd.property.trans_ne (pow_pos Nat.card_pos _).ne')
  exact Finite.of_equiv _ (prodEquiv hϖ e).symm

variable (O N) in
/-- **The recursion for the number of submodules of given index.** Write `s_N(k)` for the number
of submodules of index `q ^ k` of an `O`-module `N`. If these are finite, then
`s_{O × N}(e) = ∑_{k ≤ e} q^k s_N(k)`. -/
theorem card_submodule_prod_cardQuot_eq_sum
    (hN : ∀ k : ℕ, Finite {K : Submodule O N // K.cardQuot = Nat.card (ResidueField O) ^ k})
    (e : ℕ) :
    Nat.card {L : Submodule O (O × N) // L.cardQuot = Nat.card (ResidueField O) ^ e} =
      ∑ k ∈ range (e + 1), Nat.card (ResidueField O) ^ k *
        Nat.card {K : Submodule O N // K.cardQuot = Nat.card (ResidueField O) ^ k} := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible O
  have (k : ℕ) :=
    Fintype.ofFinite {K : Submodule O N // K.cardQuot = Nat.card (ResidueField O) ^ k}
  have (b : Σ k : Fin (e + 1),
      {K : Submodule O N // K.cardQuot = Nat.card (ResidueField O) ^ (k : ℕ)}) :
      Finite (N ⧸ b.snd.val) :=
    finite_quotient_of_cardQuot_ne_zero (b.snd.property.trans_ne (pow_pos Nat.card_pos _).ne')
  rw [Nat.card_congr (prodEquiv hϖ e), Nat.card_sigma, Fintype.sum_sigma,
    ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp_rw [← cardQuot_apply]
  rw [Finset.sum_congr rfl fun K _ ↦ K.property, sum_const, card_univ, ← Nat.card_eq_fintype_card,
    smul_eq_mul, mul_comm]

end Prod

section Free

variable (O) in
/-- A free module `O ^ j` has finitely many submodules of each index `q ^ e`. -/
theorem finite_submodule_pi_cardQuot_eq (j e : ℕ) :
    Finite {L : Submodule O (Fin j → O) // L.cardQuot = Nat.card (ResidueField O) ^ e} := by
  induction j generalizing e with
  | zero => exact Finite.of_subsingleton
  | succ j ih =>
    have := finite_submodule_prod_cardQuot_eq O (Fin j → O) ih e
    exact Finite.of_equiv _ (subtypeCardQuotEquiv (Fin.consLinearEquiv O fun _ ↦ O) _)

variable (O) in
/-- **The number of submodules of given index in `O ^ (j + 1)`**: the submodules of index `q ^ e`
are counted by the Gaussian binomial coefficient `[e + j, j]_q`. -/
theorem card_submodule_pi_cardQuot_eq_gaussianBinomial (j e : ℕ) :
    Nat.card {L : Submodule O (Fin (j + 1) → O) // L.cardQuot = Nat.card (ResidueField O) ^ e} =
      gaussianBinomial (Nat.card (ResidueField O)) (e + j) j := by
  rw [← Nat.card_congr (subtypeCardQuotEquiv (Fin.consLinearEquiv O fun _ ↦ O) _),
    card_submodule_prod_cardQuot_eq_sum O _ (finite_submodule_pi_cardQuot_eq O j) e]
  induction j generalizing e with
  | zero =>
    -- The only submodule of `O ^ 0` is `⊤`, of index `1 = q ^ 0`.
    have hq : 1 < Nat.card (ResidueField O) := Finite.one_lt_card
    have h_top (K : Submodule O (Fin 0 → O)) : K = ⊤ := Subsingleton.elim _ _
    rw [sum_eq_single 0 (fun k _ hk ↦ ?_) (by simp), gaussianBinomial_zero_right]
    · simp [h_top]
    · have : IsEmpty {K : Submodule O (Fin 0 → O) // K.cardQuot = Nat.card (ResidueField O) ^ k} :=
        ⟨fun K ↦ hk (Nat.pow_right_injective hq (by simpa [h_top K.val] using K.property.symm))⟩
      simp
  | succ j ih =>
    simp_rw [← Nat.card_congr (subtypeCardQuotEquiv (Fin.consLinearEquiv O fun _ ↦ O) _),
      card_submodule_prod_cardQuot_eq_sum O _ (finite_submodule_pi_cardQuot_eq O j), ih]
    rw [← add_assoc, gaussianBinomial_add_succ_eq_sum]

variable {M : Type*} [AddCommGroup M] [Module O M] [Module.Free O M] {j : ℕ}

/-- **The number of submodules of given index in a free module.** Let `O` be a discrete valuation
ring whose residue field has `q` elements and `M` a free `O`-module of rank `j + 1`. The
submodules of `M` of index `q ^ e` are counted by the Gaussian binomial coefficient
`[e + j, j]_q`. -/
theorem card_submodule_cardQuot_eq_gaussianBinomial (hM : finrank O M = j + 1) (e : ℕ) :
    Nat.card {L : Submodule O M // L.cardQuot = Nat.card (ResidueField O) ^ e} =
      gaussianBinomial (Nat.card (ResidueField O)) (e + j) j := by
  have : Module.Finite O M := Module.finite_of_finrank_pos (hM ▸ j.succ_pos)
  rw [Nat.card_congr (subtypeCardQuotEquiv (finBasisOfFinrankEq O M hM).equivFun _),
    card_submodule_pi_cardQuot_eq_gaussianBinomial]

/-- **The number of submodules of given colength in a free module.** Let `O` be a discrete
valuation ring whose residue field has `q` elements and `M` a free `O`-module of rank `j + 1`.
The submodules `L` of `M` of colength `e`, that is with `M ⧸ L` of length `e`, are counted by the
Gaussian binomial coefficient `[e + j, j]_q`. -/
theorem card_submodule_length_quotient_eq_gaussianBinomial (hM : finrank O M = j + 1) (e : ℕ) :
    Nat.card {L : Submodule O M // Module.length O (M ⧸ L) = e} =
      gaussianBinomial (Nat.card (ResidueField O)) (e + j) j := by
  rw [← card_submodule_cardQuot_eq_gaussianBinomial hM e]
  exact Nat.card_congr <| Equiv.subtypeEquivRight fun L ↦ by
    rw [TauCeti.length_eq_iff_natCard_eq_pow, cardQuot_apply]

/-- The number of submodules of colength `e` of a free module of rank `j + 1` over a discrete
valuation ring with residue field of `q` elements is at most `q ^ (e (j + 1))`. -/
theorem card_submodule_length_quotient_le_pow (hM : finrank O M = j + 1) (e : ℕ) :
    Nat.card {L : Submodule O M // Module.length O (M ⧸ L) = e} ≤
      Nat.card (ResidueField O) ^ (e * (j + 1)) := by
  rw [card_submodule_length_quotient_eq_gaussianBinomial hM]
  exact gaussianBinomial_add_le_pow Finite.one_lt_card e j

/-- The number of submodules of colength `e` of a free module of rank `j + 1` over a discrete
valuation ring with residue field of `q` elements is at most `(e + 1) ^ j q ^ (e j)`. -/
theorem card_submodule_length_quotient_le_succ_pow_mul_pow (hM : finrank O M = j + 1) (e : ℕ) :
    Nat.card {L : Submodule O M // Module.length O (M ⧸ L) = e} ≤
      (e + 1) ^ j * Nat.card (ResidueField O) ^ (e * j) := by
  rw [card_submodule_length_quotient_eq_gaussianBinomial hM]
  exact gaussianBinomial_add_le_succ_pow_mul_pow Nat.card_pos.ne' e j

end Free

end TauCeti.IsDiscreteValuationRing
