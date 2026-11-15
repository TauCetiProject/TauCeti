/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.HasseDeriv.JetEvaluation
public import TauCeti.RingTheory.MvPolynomial.PowerSubstitution

import Mathlib.Data.Nat.Factorial.NatCast
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import TauCeti.RingTheory.MvPolynomial.HasseDeriv.OrdinaryJet

/-!
# Vanishing criteria and jet-map injectivity on the Frobenius graph

This file builds partial-degree forms, contrapositive vanishing criteria, and injectivity of the
jet-evaluation maps `MvPolynomial.jetEval` and `MvPolynomial.ordinaryJetEval` on top of the
Frobenius-graph nonvanishing tests `MvPolynomial.exists_nonzero_hasse_jet_on_frobenius_graph` and
`MvPolynomial.exists_nonzero_ordinary_jet_on_frobenius_graph` from
`TauCeti.RingTheory.MvPolynomial.PowerSubstitution`.

Let `R` be an integral domain of exponential characteristic `p` and `q = p ^ e` (`e ≥ 0`). For a
finite set `S : Finset R`, a derivative order bound `m < q`, and any exponent set
`s : Set (Fin 2 →₀ ℕ)` whose elements satisfy `μ 0 < q` and `μ 0 + q * μ 1 < #S * (m + 1)`:
* Every polynomial `F ∈ restrictSupport R s` has `Z`-degree below `q` and satisfies
  `(powerSubstitution q F).natDegree < #S * (m + 1)`
  (`MvPolynomial.natDegree_powerSubstitution_lt_of_mem_restrictSupport`), so the Hasse jet map
  evaluating `∂_Z^[k]` (`0 ≤ k ≤ m`) along the Frobenius graph `{(a, a ^ q) | a ∈ S}` is injective
  (`MvPolynomial.jetEval_frobeniusGraph_injective`).
* When `0 < e` and `m < p`, every factorial `k!` (`k ≤ m`) is a unit in `R`, so the ordinary jet
  map evaluating `∂_Z ^ k` (`0 ≤ k ≤ m`) along `{(a, a ^ q) | a ∈ S}` is likewise injective
  (`MvPolynomial.ordinaryJetEval_frobeniusGraph_injective`).

## Main results

* `MvPolynomial.exists_nonzero_hasse_jet_on_frobenius_graph_of_degreeOf`,
  `MvPolynomial.eq_zero_of_forall_eval_hasseDeriv_frobenius_eq_zero`,
  `MvPolynomial.jetEval_frobeniusGraph_injective`: partial-degree nonvanishing test, contrapositive
  vanishing criterion, and injectivity of `MvPolynomial.jetEval` along the Frobenius graph
  `{(a, a ^ (p ^ e)) | a ∈ S}` for Hasse `Z`-jets of order `≤ m < p ^ e`.
* `MvPolynomial.exists_nonzero_ordinary_jet_on_frobenius_graph_of_degreeOf`,
  `MvPolynomial.eq_zero_of_forall_eval_iterate_pderiv_frobenius_eq_zero`,
  `MvPolynomial.ordinaryJetEval_frobeniusGraph_injective`: the ordinary-derivative counterparts
  when `0 < e` and `m < p`.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, AMS Colloquium Publications 53 (2004),
  §11.6, pp. 283–284, Lemmas 11.16–11.17.
* W. M. Schmidt, *Equations over Finite Fields: An Elementary Approach*, Lecture Notes in
  Mathematics 536 (1976), ch. I, Lemma 2C.
-/

public section

namespace MvPolynomial

open Finsupp

section FrobeniusGraph

variable {R : Type*} [CommRing R] [IsDomain R] {p : ℕ} [ExpChar R p]

/-! ### Hasse jets -/

/-- Partial-degree form of `exists_nonzero_hasse_jet_on_frobenius_graph`, assuming
`F.degreeOf 0 + p ^ e * F.degreeOf 1 < S.card * (m + 1)`. -/
theorem exists_nonzero_hasse_jet_on_frobenius_graph_of_degreeOf {e : ℕ}
    {F : MvPolynomial (Fin 2) R} (hF : F ≠ 0) (hZ : F.degreeOf 0 < p ^ e)
    {S : Finset R} {m : ℕ} (hm : m < p ^ e)
    (hdeg : F.degreeOf 0 + p ^ e * F.degreeOf 1 < S.card * (m + 1)) :
    ∃ a ∈ S, ∃ k ≤ m,
      eval ![a, a ^ p ^ e] (hasseDeriv (single 0 k) F) ≠ 0 :=
  exists_nonzero_hasse_jet_on_frobenius_graph hF hZ hm
    ((natDegree_powerSubstitution_le (p ^ e) F).trans_lt hdeg)

/-- If `F` has `Z`-degree below `p ^ e`, `m < p ^ e`,
`(powerSubstitution (p ^ e) F).natDegree < S.card * (m + 1)`, and all pure `Z`-Hasse jets of `F`
of order at most `m` vanish at `(a, a ^ (p ^ e))` for every `a ∈ S`, then `F = 0`. -/
theorem eq_zero_of_forall_eval_hasseDeriv_frobenius_eq_zero {e : ℕ}
    {F : MvPolynomial (Fin 2) R} (hZ : F.degreeOf 0 < p ^ e)
    {S : Finset R} {m : ℕ} (hm : m < p ^ e)
    (hdeg : (powerSubstitution (p ^ e) F).natDegree < S.card * (m + 1))
    (hvan : ∀ a ∈ S, ∀ k ≤ m, eval ![a, a ^ p ^ e] (hasseDeriv (single 0 k) F) = 0) :
    F = 0 := by
  by_contra hF
  obtain ⟨a, ha, k, hk, hne⟩ :=
    exists_nonzero_hasse_jet_on_frobenius_graph hF hZ hm hdeg
  exact hne (hvan a ha k hk)

/-- On any exponent set `s` whose elements satisfy `μ 0 < p ^ e` and
`μ 0 + p ^ e * μ 1 < S.card * (m + 1)` with `m < p ^ e`, the Hasse jet map evaluating pure
`Z`-Hasse jets of orders `0, …, m` along the Frobenius graph `{(a, a ^ (p ^ e)) | a ∈ S}` is
injective. -/
theorem jetEval_frobeniusGraph_injective {e : ℕ} {s : Set (Fin 2 →₀ ℕ)}
    {S : Finset R} {m : ℕ} (hm : m < p ^ e)
    (hsZ : ∀ μ ∈ s, μ 0 < p ^ e)
    (hsdeg : ∀ μ ∈ s, μ 0 + p ^ e * μ 1 < S.card * (m + 1)) :
    Function.Injective
      (jetEval s (fun i : S × Fin (m + 1) ↦ ![(i.1 : R), (i.1 : R) ^ p ^ e])
        (fun i : S × Fin (m + 1) ↦ single 0 (i.2 : ℕ))) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro f hf
  rw [mem_ker_jetEval] at hf
  ext1
  by_contra hF
  obtain ⟨μ₀, hμ₀⟩ := support_nonempty.2 hF
  have hD : 0 < S.card * (m + 1) := (Nat.zero_le _).trans_lt (hsdeg μ₀ (f.2 hμ₀))
  have hZ : (f : MvPolynomial (Fin 2) R).degreeOf 0 < p ^ e :=
    degreeOf_lt_of_mem_restrictSupport f.2 ((Nat.zero_le m).trans_lt hm) hsZ
  have hdeg :
      (powerSubstitution (p ^ e) (f : MvPolynomial (Fin 2) R)).natDegree < S.card * (m + 1) :=
    natDegree_powerSubstitution_lt_of_mem_restrictSupport hD f.2 hsdeg
  exact absurd (eq_zero_of_forall_eval_hasseDeriv_frobenius_eq_zero hZ hm hdeg
    fun a ha k hk ↦ hf (⟨a, ha⟩, ⟨k, Nat.lt_succ_of_le hk⟩)) hF

/-! ### Ordinary jets -/

/-- Partial-degree form of `exists_nonzero_ordinary_jet_on_frobenius_graph`, assuming
`F.degreeOf 0 + p ^ e * F.degreeOf 1 < S.card * (m + 1)`. -/
theorem exists_nonzero_ordinary_jet_on_frobenius_graph_of_degreeOf {e : ℕ} (he : 0 < e)
    {F : MvPolynomial (Fin 2) R} (hF : F ≠ 0) (hZ : F.degreeOf 0 < p ^ e)
    {S : Finset R} {m : ℕ} (hm : m < p)
    (hdeg : F.degreeOf 0 + p ^ e * F.degreeOf 1 < S.card * (m + 1)) :
    ∃ a ∈ S, ∃ k ≤ m,
      eval ![a, a ^ p ^ e] ((pderiv (0 : Fin 2))^[k] F) ≠ 0 :=
  exists_nonzero_ordinary_jet_on_frobenius_graph he hF hZ hm
    ((natDegree_powerSubstitution_le (p ^ e) F).trans_lt hdeg)

/-- If `0 < e`, `F` has `Z`-degree below `p ^ e`, `m < p`,
`(powerSubstitution (p ^ e) F).natDegree < S.card * (m + 1)`, and all ordinary `Z`-derivatives of
`F` of order at most `m` vanish at `(a, a ^ (p ^ e))` for every `a ∈ S`, then `F = 0`. -/
theorem eq_zero_of_forall_eval_iterate_pderiv_frobenius_eq_zero {e : ℕ} (he : 0 < e)
    {F : MvPolynomial (Fin 2) R} (hZ : F.degreeOf 0 < p ^ e)
    {S : Finset R} {m : ℕ} (hm : m < p)
    (hdeg : (powerSubstitution (p ^ e) F).natDegree < S.card * (m + 1))
    (hvan : ∀ a ∈ S, ∀ k ≤ m, eval ![a, a ^ p ^ e] ((pderiv (0 : Fin 2))^[k] F) = 0) :
    F = 0 := by
  by_contra hF
  obtain ⟨a, ha, k, hk, hne⟩ :=
    exists_nonzero_ordinary_jet_on_frobenius_graph he hF hZ hm hdeg
  exact hne (hvan a ha k hk)

/-- For `0 < e` and `m < p`, on any exponent set `s` whose elements satisfy `μ 0 < p ^ e` and
`μ 0 + p ^ e * μ 1 < S.card * (m + 1)`, the ordinary jet map evaluating `∂_Z ^ k` (`0 ≤ k ≤ m`)
along `{(a, a ^ (p ^ e)) | a ∈ S}` is injective. -/
theorem ordinaryJetEval_frobeniusGraph_injective {e : ℕ} (he : 0 < e) {s : Set (Fin 2 →₀ ℕ)}
    {S : Finset R} {m : ℕ} (hm : m < p)
    (hsZ : ∀ μ ∈ s, μ 0 < p ^ e)
    (hsdeg : ∀ μ ∈ s, μ 0 + p ^ e * μ 1 < S.card * (m + 1)) :
    Function.Injective
      (ordinaryJetEval s (fun i : S × Fin (m + 1) ↦ ![(i.1 : R), (i.1 : R) ^ p ^ e])
        (fun _ ↦ 0) (fun i : S × Fin (m + 1) ↦ (i.2 : ℕ))) := by
  have hk : ∀ i : S × Fin (m + 1), IsUnit ((i.2 : ℕ).factorial : R) := fun i ↦ by
    rcases ‹ExpChar R p› with _ | ⟨hp⟩
    · have h0 : (i.2 : ℕ) = 0 := by omega
      simp [h0]
    · have : Fact p.Prime := ⟨hp⟩
      exact (IsUnit.natCast_factorial_iff_of_charP p).2 ((Nat.lt_succ_iff.1 i.2.isLt).trans_lt hm)
  rw [ordinaryJetEval_injective_iff s (fun _ ↦ 0) _ hk]
  exact jetEval_frobeniusGraph_injective (hm.trans_le (Nat.le_self_pow he.ne' p)) hsZ hsdeg

end FrobeniusGraph

/-! ### Examples and sharpness witnesses -/

section Examples

open scoped Polynomial

open Classical in
private noncomputable local instance : Fintype (GaloisField 2 2) :=
  Fintype.ofFinite (GaloisField 2 2)

open Classical in
/-- Over `GaloisField 2 2` (four elements, `p = 2`), for `e = 1`, `F = Z + W`, `S = {0, 1, c}`
with `c ∉ {0, 1}`, and `m = 0`: `F` vanishes at `(0, 0)` and `(1, 1)`, and the nonvanishing witness
at order `0` is `(c, c ^ 2)` where `c + c ^ 2 = 1 ≠ 0`. -/
example :
    ∃ c : GaloisField 2 2,
      c ^ 2 + c + 1 = 0 ∧
      ({0, 1, c} : Finset (GaloisField 2 2)).card = 3 ∧
      eval ![0, 0 ^ 2 ^ 1] (X 0 + X 1 : MvPolynomial (Fin 2) (GaloisField 2 2)) = 0 ∧
      eval ![1, 1 ^ 2 ^ 1] (X 0 + X 1 : MvPolynomial (Fin 2) (GaloisField 2 2)) = 0 ∧
      eval ![c, c ^ 2 ^ 1] (X 0 + X 1 : MvPolynomial (Fin 2) (GaloisField 2 2)) = 1 := by
  have hcard : Fintype.card (GaloisField 2 2) = 4 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by decide)]
    rfl
  have hne : ((Finset.univ : Finset (GaloisField 2 2)) \ {0, 1}).Nonempty := by
    refine Finset.card_pos.1 ?_
    have hle : ({0, 1} : Finset (GaloisField 2 2)).card ≤ 2 := Finset.card_le_two
    have hu : (Finset.univ : Finset (GaloisField 2 2)).card = 4 := hcard
    have hsub := Finset.le_card_sdiff ({0, 1} : Finset (GaloisField 2 2)) Finset.univ
    omega
  obtain ⟨c, hc⟩ := hne
  rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  rcases hc with ⟨_, hc0, hc1⟩
  have hc4 : c ^ 4 = c := by
    have h := FiniteField.pow_card c
    rwa [hcard] at h
  have h2 : (2 : GaloisField 2 2) = 0 := CharP.cast_eq_zero (GaloisField 2 2) 2
  have h11 : (1 : GaloisField 2 2) + 1 = 0 := by
    simpa [one_add_one_eq_two] using h2
  have hc1_add : c + 1 ≠ 0 := fun h ↦ hc1 <| by
    calc c = c + (1 + 1) := by rw [h11, add_zero]
      _ = (c + 1) + 1 := (add_assoc _ _ _).symm
      _ = 1 := by rw [h, zero_add]
  have hprod : c * (c + 1) * (c ^ 2 + c + 1) = 0 := by
    calc c * (c + 1) * (c ^ 2 + c + 1)
        = c ^ 4 + 2 * (c ^ 3 + c ^ 2) + c := by ring
      _ = c + 0 * (c ^ 3 + c ^ 2) + c := by rw [hc4, h2]
      _ = 2 * c := by ring
      _ = 0 := by rw [h2, zero_mul]
  have hmin : c ^ 2 + c + 1 = 0 :=
    (mul_eq_zero.1 hprod).resolve_left (mul_ne_zero hc0 hc1_add)
  have hval : c + c ^ 2 = 1 := by
    calc c + c ^ 2 = (c ^ 2 + c + 1) + 1 - 2 * 1 := by ring
      _ = 1 := by rw [hmin, h2]; ring
  have hS3 : ({0, 1, c} : Finset (GaloisField 2 2)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm hc0]),
      Finset.card_insert_of_notMem (by simp [Ne.symm hc1]), Finset.card_singleton]
  exact ⟨c, hmin, hS3, by simp, by simp [h11], by simpa [pow_one] using hval⟩

/-- Sharpness of the degree bound: for `p = 2`, `e = 1`, `F = Z + W` over `ZMod 2`, `S = {0, 1}`,
and `m = 0`, `natDegree (X + X ^ 2) = 2` is not below `S.card * (0 + 1) = 2`, and `F` vanishes at
both Frobenius-graph points `(0, 0)` and `(1, 1)`. -/
example :
    let F : MvPolynomial (Fin 2) (ZMod 2) := X 0 + X 1
    let S : Finset (ZMod 2) := {0, 1}
    F ≠ 0 ∧ F.degreeOf 0 < 2 ^ 1 ∧
      ¬ (powerSubstitution (2 ^ 1) F).natDegree < S.card * (0 + 1) ∧
      ∀ a ∈ S, eval ![a, a ^ 2 ^ 1] F = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have hval := congrArg (eval ![1, 0]) h
    simp at hval
  · refine (degreeOf_add_le 0 _ _).trans_lt (max_lt (by simp) ?_)
    simp [degreeOf_X]
  · have hsub : powerSubstitution (2 ^ 1) (X 0 + X 1 : MvPolynomial (Fin 2) (ZMod 2)) =
        Polynomial.X ^ 2 + Polynomial.X := by
      simp only [pow_one, map_add, powerSubstitution_X_zero, powerSubstitution_X_one]
      ring
    have hdeg : (Polynomial.X ^ 2 + Polynomial.X : (ZMod 2)[X]).natDegree = 2 := by
      rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
      · exact Polynomial.natDegree_X_pow 2
      · rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X]
        decide
    rw [hsub, hdeg]
    decide
  · intro a ha
    fin_cases ha
    · simp
    · simp only [eval_add, eval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
      decide

/-- Over `GaloisField 2 2` with `p = 2`, `e = 2` (`q = 4`), `F = Z + W`, and `S = univ` (`#S = 4`):
every `a` satisfies `a ^ 4 = a`, so `F(a, a ^ 4) = 0` on all of `S` (matching the failure of
`4 < 4 * 1` at `m = 0`), while at `m = 1 < 2` the degree bound `4 < 4 * 2` holds and the first jet
`∂_Z F = 1` is nonzero at every point. -/
example :
    let F : MvPolynomial (Fin 2) (GaloisField 2 2) := X 0 + X 1
    let S : Finset (GaloisField 2 2) := Finset.univ
    (∀ a ∈ S, eval ![a, a ^ 2 ^ 2] F = 0) ∧
      (∀ a ∈ S, eval ![a, a ^ 2 ^ 2] (pderiv 0 F) = 1) ∧
      ∃ a ∈ S, ∃ k ≤ 1, eval ![a, a ^ 2 ^ 2] ((pderiv (0 : Fin 2))^[k] F) ≠ 0 := by
  have hcard : Fintype.card (GaloisField 2 2) = 4 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by decide)]
    rfl
  have h2 : (2 : GaloisField 2 2) = 0 := CharP.cast_eq_zero (GaloisField 2 2) 2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨fun a _ ↦ ?_, fun a _ ↦ by simp, ?_⟩
  · have ha4 : a ^ 4 = a := by
      have h := FiniteField.pow_card a
      rwa [hcard] at h
    have h22 : 2 ^ 2 = 4 := rfl
    simp only [eval_add, eval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [h22, ha4, ← two_mul, h2, zero_mul]
  · refine exists_nonzero_ordinary_jet_on_frobenius_graph_of_degreeOf (p := 2) (e := 2) (by decide)
      (F := X 0 + X 1) ?_ ?_ (S := Finset.univ) (m := 1) (by decide) ?_
    · intro h
      have hval := congrArg (eval ![1, 0]) h
      simp at hval
    · refine (degreeOf_add_le 0 _ _).trans_lt (max_lt (by simp) ?_)
      simp [degreeOf_X]
    · have h0 : (X 0 + X 1 : MvPolynomial (Fin 2) (GaloisField 2 2)).degreeOf 0 ≤ 1 :=
        (degreeOf_add_le 0 _ _).trans (max_le (by simp) (by simp [degreeOf_X]))
      have h1 : (X 0 + X 1 : MvPolynomial (Fin 2) (GaloisField 2 2)).degreeOf 1 ≤ 1 :=
        (degreeOf_add_le 1 _ _).trans (max_le (by simp [degreeOf_X]) (by simp))
      have hScard : (Finset.univ : Finset (GaloisField 2 2)).card = 4 := hcard
      rw [hScard]
      omega

end Examples

end MvPolynomial
