/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.HasseDeriv
public import TauCeti.RingTheory.MvPolynomial.HasseDeriv.JetEvaluation
public import TauCeti.RingTheory.MvPolynomial.PowerSubstitution

import Mathlib.Data.Nat.Factorial.NatCast
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Nonvanishing of Hasse and ordinary jets on the Frobenius graph

Let `R` be an integral domain of exponential characteristic `p` and `q = p ^ e` (`e ≥ 0`). A
nonzero bivariate polynomial `F(Z, W) : MvPolynomial (Fin 2) R` (variable `0` is `Z`, variable `1`
is `W`) of `Z`-degree strictly below `q` maps under `MvPolynomial.powerSubstitution q` to a nonzero
univariate polynomial `f(X) = F(X, X ^ q)` (`MvPolynomial.powerSubstitution_ne_zero`).

For any finite set `S : Finset R` and any derivative order bound `m < q`:
* Whenever `f.natDegree < #S * (m + 1)`, root-multiplicity counting on `f`
  (`Polynomial.exists_eval_hasseDeriv_ne_zero_of_natDegree_lt`) furnishes `a ∈ S` and `k ≤ m` with
  `(Polynomial.hasseDeriv k f).eval a ≠ 0`. Since `k ≤ m < q`, Hasse derivatives commute with
  `powerSubstitution q` (`MvPolynomial.eval_hasseDeriv_powerSubstitution`), yielding a nonzero pure
  `Z`-Hasse jet `(∂_Z^[k] F)(a, a ^ q) ≠ 0` on the Frobenius graph
  (`MvPolynomial.exists_nonzero_hasse_jet_on_frobenius_graph`). This holds for every `e ≥ 0`
  (including `e = 0`, where `q = 1` forces `m = 0`) and for orders `p ≤ m < q`.
* In prime characteristic `p`, when `0 < e` and `m < p`, we have `m < p ≤ q`, and `(k! : R)` is a
  unit for every `k ≤ m < p` (`MvPolynomial.eval_iterate_pderiv_eq_zero_iff_of_lt_charP`), yielding
  a nonzero ordinary `Z`-jet `(∂_Z ^ k F)(a, a ^ q) ≠ 0` on the Frobenius graph
  (`MvPolynomial.exists_nonzero_ordinary_jet_on_frobenius_graph`). Both `0 < e` and `m < p` are
  sharp for the ordinary form.

## Main results

* `MvPolynomial.exists_nonzero_hasse_jet_on_frobenius_graph`,
  `MvPolynomial.exists_nonzero_hasse_jet_on_frobenius_graph_of_degreeOf`: nonvanishing of a pure
  `Z`-Hasse jet of order `≤ m` at some `(a, a ^ (p ^ e))` with `a ∈ S`, when `F ≠ 0`,
  `F.degreeOf 0 < p ^ e`, `m < p ^ e`, and `(powerSubstitution (p ^ e) F).natDegree < #S * (m + 1)`
  (or `F.degreeOf 0 + p ^ e * F.degreeOf 1 < #S * (m + 1)`).
* `MvPolynomial.eq_zero_of_forall_eval_hasseDeriv_frobenius_eq_zero`,
  `MvPolynomial.jetEval_frobeniusGraph_injective`: contrapositive vanishing criterion and
  injectivity of `MvPolynomial.jetEval` at the Frobenius-graph points `(a, a ^ (p ^ e))` (`a ∈ S`,
  orders `0, …, m`) on any support set with `μ 0 < p ^ e` and `μ 0 + p ^ e * μ 1 < #S * (m + 1)`.
* `MvPolynomial.exists_nonzero_ordinary_jet_on_frobenius_graph`,
  `MvPolynomial.exists_nonzero_ordinary_jet_on_frobenius_graph_of_degreeOf`,
  `MvPolynomial.eq_zero_of_forall_eval_iterate_pderiv_frobenius_eq_zero`,
  `MvPolynomial.ordinaryJetEval_frobeniusGraph_injective`: the ordinary-derivative counterparts in
  prime characteristic `p` when `0 < e` and `m < p`.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, AMS Colloquium Publications 53 (2004),
  §11.6, pp. 283–284, Lemmas 11.16–11.17.
* W. M. Schmidt, *Equations over Finite Fields: An Elementary Approach*, Lecture Notes in
  Mathematics 536 (1976), ch. I, Lemma 2C.
-/

public section

namespace MvPolynomial

open Finsupp

section Hasse

variable {R : Type*} [CommRing R] [IsDomain R] {p : ℕ} [ExpChar R p]

/-- **The Frobenius-graph nonvanishing test, Hasse form** (Iwaniec–Kowalski, Lemmas 11.16–11.17).
Over an integral domain `R` of exponential characteristic `p`, let `q = p ^ e` (`e ≥ 0`). If
`F : MvPolynomial (Fin 2) R` is nonzero of `Z`-degree below `q`, `m < q`, and
`(powerSubstitution q F).natDegree < S.card * (m + 1)` for a finite set `S : Finset R`, then some
pure `Z`-Hasse jet `∂_Z^[k] F` of order `k ≤ m` does not vanish at `(a, a ^ q)` for some `a ∈ S`.
-/
theorem exists_nonzero_hasse_jet_on_frobenius_graph {e : ℕ}
    (F : MvPolynomial (Fin 2) R) (hF : F ≠ 0) (hZ : F.degreeOf 0 < p ^ e)
    (S : Finset R) (m : ℕ) (hm : m < p ^ e)
    (hdeg : (powerSubstitution (p ^ e) F).natDegree < S.card * (m + 1)) :
    ∃ a ∈ S, ∃ k ≤ m,
      eval ![a, a ^ p ^ e] (hasseDeriv (single 0 k) F) ≠ 0 := by
  obtain ⟨a, ha, k, hk, hne⟩ :=
    Polynomial.exists_eval_hasseDeriv_ne_zero_of_natDegree_lt
      (powerSubstitution_ne_zero hF hZ) hdeg
  refine ⟨a, ha, k, hk, ?_⟩
  rwa [← eval_hasseDeriv_powerSubstitution k (hk.trans_lt hm)]

/-- Partial-degree form of `exists_nonzero_hasse_jet_on_frobenius_graph`, assuming
`F.degreeOf 0 + p ^ e * F.degreeOf 1 < S.card * (m + 1)`. -/
theorem exists_nonzero_hasse_jet_on_frobenius_graph_of_degreeOf {e : ℕ}
    (F : MvPolynomial (Fin 2) R) (hF : F ≠ 0) (hZ : F.degreeOf 0 < p ^ e)
    (S : Finset R) (m : ℕ) (hm : m < p ^ e)
    (hdeg : F.degreeOf 0 + p ^ e * F.degreeOf 1 < S.card * (m + 1)) :
    ∃ a ∈ S, ∃ k ≤ m,
      eval ![a, a ^ p ^ e] (hasseDeriv (single 0 k) F) ≠ 0 :=
  exists_nonzero_hasse_jet_on_frobenius_graph F hF hZ S m hm
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
    exists_nonzero_hasse_jet_on_frobenius_graph F hF hZ S m hm hdeg
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

end Hasse

section Ordinary

variable {R : Type*} [CommRing R] [IsDomain R] {p : ℕ} [Fact p.Prime] [CharP R p]

/-- **The Frobenius-graph nonvanishing test, ordinary form.** Over an integral domain `R` of prime
characteristic `p`, let `q = p ^ e` with `0 < e`. If `F : MvPolynomial (Fin 2) R` is nonzero of
`Z`-degree below `q`, `m < p`, and `(powerSubstitution q F).natDegree < S.card * (m + 1)` for a
finite set `S : Finset R`, then some ordinary `Z`-derivative `∂_Z ^ k F` of order `k ≤ m` does not
vanish at `(a, a ^ q)` for some `a ∈ S`. -/
theorem exists_nonzero_ordinary_jet_on_frobenius_graph {e : ℕ} (he : 0 < e)
    (F : MvPolynomial (Fin 2) R) (hF : F ≠ 0) (hZ : F.degreeOf 0 < p ^ e)
    (S : Finset R) (m : ℕ) (hm : m < p)
    (hdeg : (powerSubstitution (p ^ e) F).natDegree < S.card * (m + 1)) :
    ∃ a ∈ S, ∃ k ≤ m,
      eval ![a, a ^ p ^ e] ((pderiv (0 : Fin 2))^[k] F) ≠ 0 := by
  have hmq : m < p ^ e := hm.trans_le (Nat.le_self_pow he.ne' p)
  obtain ⟨a, ha, k, hk, hne⟩ :=
    exists_nonzero_hasse_jet_on_frobenius_graph F hF hZ S m hmq hdeg
  refine ⟨a, ha, k, hk, ?_⟩
  rwa [ne_eq, eval_iterate_pderiv_eq_zero_iff_of_lt_charP (hk.trans_lt hm)]

/-- Partial-degree form of `exists_nonzero_ordinary_jet_on_frobenius_graph`, assuming
`F.degreeOf 0 + p ^ e * F.degreeOf 1 < S.card * (m + 1)`. -/
theorem exists_nonzero_ordinary_jet_on_frobenius_graph_of_degreeOf {e : ℕ} (he : 0 < e)
    (F : MvPolynomial (Fin 2) R) (hF : F ≠ 0) (hZ : F.degreeOf 0 < p ^ e)
    (S : Finset R) (m : ℕ) (hm : m < p)
    (hdeg : F.degreeOf 0 + p ^ e * F.degreeOf 1 < S.card * (m + 1)) :
    ∃ a ∈ S, ∃ k ≤ m,
      eval ![a, a ^ p ^ e] ((pderiv (0 : Fin 2))^[k] F) ≠ 0 :=
  exists_nonzero_ordinary_jet_on_frobenius_graph he F hF hZ S m hm
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
    exists_nonzero_ordinary_jet_on_frobenius_graph he F hF hZ S m hm hdeg
  exact hne (hvan a ha k hk)

/-- In prime characteristic `p`, for `0 < e` and `m < p`, on any exponent set `s` whose elements
satisfy `μ 0 < p ^ e` and `μ 0 + p ^ e * μ 1 < S.card * (m + 1)`, the ordinary jet map evaluating
`∂_Z ^ k` (`0 ≤ k ≤ m`) along `{(a, a ^ (p ^ e)) | a ∈ S}` is injective. -/
theorem ordinaryJetEval_frobeniusGraph_injective {e : ℕ} (he : 0 < e) {s : Set (Fin 2 →₀ ℕ)}
    {S : Finset R} {m : ℕ} (hm : m < p)
    (hsZ : ∀ μ ∈ s, μ 0 < p ^ e)
    (hsdeg : ∀ μ ∈ s, μ 0 + p ^ e * μ 1 < S.card * (m + 1)) :
    Function.Injective
      (ordinaryJetEval s (fun i : S × Fin (m + 1) ↦ ![(i.1 : R), (i.1 : R) ^ p ^ e])
        (fun _ ↦ 0) (fun i : S × Fin (m + 1) ↦ (i.2 : ℕ))) := by
  rw [ordinaryJetEval_injective_iff_of_lt_charP
    fun i ↦ (Nat.lt_succ_iff.1 i.2.isLt).trans_lt hm]
  exact jetEval_frobeniusGraph_injective (hm.trans_le (Nat.le_self_pow he.ne' p)) hsZ hsdeg

end Ordinary

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

/-- Sharpness of `F.degreeOf 0 < p ^ e`: over `ZMod 2` at `p = 2`, `e = 1`, `F = Z ^ 2 + W` is
nonzero of `Z`-degree `2 = p ^ e`, and `powerSubstitution 2 F = X ^ 2 + X ^ 2 = 0`, so every jet
along the Frobenius graph vanishes at every point. -/
example :
    let F : MvPolynomial (Fin 2) (ZMod 2) := X 0 ^ 2 + X 1
    F ≠ 0 ∧ ¬ F.degreeOf 0 < 2 ^ 1 ∧ powerSubstitution (2 ^ 1) F = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hval := congrArg (eval ![0, 1]) h
    simp at hval
  · intro hlt
    have h2 : (single (0 : Fin 2) 2) 0 ≤
        (X 0 ^ 2 + X 1 : MvPolynomial (Fin 2) (ZMod 2)).degreeOf 0 := by
      refine monomial_le_degreeOf 0 (mem_support_iff.2 ?_)
      simp [X_pow_eq_monomial]
    rw [single_eq_same] at h2
    omega
  · simp only [pow_one, map_add, map_pow, powerSubstitution_X_zero, powerSubstitution_X_one]
    have h2 : (2 : (ZMod 2)[X]) = 0 := CharP.cast_eq_zero _ 2
    calc (Polynomial.X ^ 2 + Polynomial.X ^ 2 : (ZMod 2)[X])
        = 2 * Polynomial.X ^ 2 := (two_mul _).symm
      _ = 0 := by rw [h2, zero_mul]

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
  refine ⟨fun a _ ↦ ?_, fun a _ ↦ by simp, ?_⟩
  · have ha4 : a ^ 4 = a := by
      have h := FiniteField.pow_card a
      rwa [hcard] at h
    have h22 : 2 ^ 2 = 4 := rfl
    simp only [eval_add, eval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [h22, ha4, ← two_mul, h2, zero_mul]
  · refine exists_nonzero_ordinary_jet_on_frobenius_graph (p := 2) (e := 2) (by decide)
      (X 0 + X 1) ?_ ?_ Finset.univ 1 (by decide) ?_
    · intro h
      have hval := congrArg (eval ![1, 0]) h
      simp at hval
    · refine (degreeOf_add_le 0 _ _).trans_lt (max_lt (by simp) ?_)
      simp [degreeOf_X]
    · refine (natDegree_powerSubstitution_le 4 _).trans_lt ?_
      have h0 : (X 0 + X 1 : MvPolynomial (Fin 2) (GaloisField 2 2)).degreeOf 0 ≤ 1 :=
        (degreeOf_add_le 0 _ _).trans (max_le (by simp) (by simp [degreeOf_X]))
      have h1 : (X 0 + X 1 : MvPolynomial (Fin 2) (GaloisField 2 2)).degreeOf 1 ≤ 1 :=
        (degreeOf_add_le 1 _ _).trans (max_le (by simp [degreeOf_X]) (by simp))
      have hScard : (Finset.univ : Finset (GaloisField 2 2)).card = 4 := hcard
      rw [hScard]
      omega

/-- Sharpness of `0 < e` in `exists_nonzero_ordinary_jet_on_frobenius_graph`: at `e = 0`, `p = 2`,
`F = W` over `ZMod 2`, `S = {0}`, and `m = 1`, all other hypotheses hold (`F ≠ 0`,
`F.degreeOf 0 = 0 < 1`, `1 < 2`, `natDegree X = 1 < 1 * 2`), yet both `W` and `∂_Z W = 0` vanish
at `(0, 0)`. -/
example :
    let F : MvPolynomial (Fin 2) (ZMod 2) := X 1
    let S : Finset (ZMod 2) := {0}
    F ≠ 0 ∧ F.degreeOf 0 < 2 ^ 0 ∧ 1 < 2 ∧
      (powerSubstitution (2 ^ 0) F).natDegree < S.card * (1 + 1) ∧
      ∀ k ≤ 1, eval ![0, (0 : ZMod 2) ^ 2 ^ 0] ((pderiv (0 : Fin 2))^[k] F) = 0 := by
  refine ⟨X_ne_zero 1, by simp [degreeOf_X], by decide, by simp, fun k hk ↦ ?_⟩
  interval_cases k <;> simp

/-- `exists_nonzero_hasse_jet_on_frobenius_graph` needs no `0 < e`: at `e = 0`, `p = 2`, `F = W`
over `ZMod 2`, `S = {0, 1}`, and `m = 0`, it produces a point of `S` where `F(a, a ^ 1) ≠ 0`
(namely `a = 1`). -/
example :
    ∃ a ∈ ({0, 1} : Finset (ZMod 2)), ∃ k ≤ 0,
      eval ![a, a ^ 2 ^ 0]
        (hasseDeriv (single 0 k) (X 1 : MvPolynomial (Fin 2) (ZMod 2))) ≠ 0 :=
  exists_nonzero_hasse_jet_on_frobenius_graph (p := 2) (e := 0) (X 1) (X_ne_zero 1)
    (by simp [degreeOf_X]) {0, 1} 0 (by decide) (by simp)

/-- Sharpness of `m < p` in `exists_nonzero_ordinary_jet_on_frobenius_graph` and necessity of the
Hasse form for `p ≤ m < p ^ e`: at `p = 2`, `e = 2` (`q = 4`), `F = Z ^ 2` over `ZMod 2`,
`S = {0}`, and `m = 2`, the Hasse form applies and `∂_Z^[2] (Z ^ 2) = 1 ≠ 0` at `(0, 0)`, whereas
the ordinary `Z`-derivatives of orders `0, 1, 2` all vanish at `(0, 0)`. -/
example :
    let F : MvPolynomial (Fin 2) (ZMod 2) := X 0 ^ 2
    (∃ a ∈ ({0} : Finset (ZMod 2)), ∃ k ≤ 2,
      eval ![a, a ^ 2 ^ 2] (hasseDeriv (single 0 k) F) ≠ 0) ∧
    eval ![0, (0 : ZMod 2) ^ 2 ^ 2] (hasseDeriv (single 0 2) F) = 1 ∧
    ∀ k ≤ 2, eval ![0, (0 : ZMod 2) ^ 2 ^ 2] ((pderiv (0 : Fin 2))^[k] F) = 0 := by
  refine ⟨?_, ?_, fun k hk ↦ ?_⟩
  · exact exists_nonzero_hasse_jet_on_frobenius_graph (p := 2) (e := 2) (X 0 ^ 2)
      (pow_ne_zero 2 (X_ne_zero 0)) (by simp) {0} 2 (by decide) (by simp)
  · simp [X_pow_eq_monomial]
  · interval_cases k
    · simp
    · simp
    · have h2 : ((Nat.factorial 2 : ℕ) : ZMod 2) = 0 := by decide
      rw [eval_iterate_pderiv_eq_factorial_mul, h2, zero_mul]

end Examples

end MvPolynomial
