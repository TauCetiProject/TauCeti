/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import TauCeti.RingTheory.WittVector.Big.Ghost

import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.RingTheory.MvPolynomial.Basic
import TauCeti.RingTheory.MvPolynomial.Expand

/-!
# Big Witt structure polynomials

Let `Φ` be an integral polynomial in variables indexed by a type `idx`. Its *big Witt structure
polynomials* are the integral polynomials `φ_n` in the variables `X (i, k)`, `i : idx`, `k : ℕ`,
such that for every positive `n`
`w_n(φ_1, φ_2, …) = Φ(w_n(X (i, ·)) : i : idx)`,
where `w_n` is the big Witt ghost polynomial `TauCeti.BigWitt.ghostPolynomial`. Taking `Φ` to be
`X 0 + X 1`, `X 0 * X 1` or `-X 0` gives the integral polynomials that define addition,
multiplication and negation of big Witt vectors: in each case the ghost components of the result
are obtained by applying `Φ` to the ghost components of the inputs.

Existence comes from Dwork's ghost-image criterion `TauCeti.BigWitt.ghost_image` over the
polynomial ring `ℤ[X (i, k)]`, using the Frobenius lifts `MvPolynomial.expand p`. Uniqueness
holds because `ℤ[X (i, k)]` is torsion-free. The polynomial `φ_n` involves only the variables
`X (i, d)` with `d ∣ n`, which is what makes the operations compatible with restriction of
truncation sets.

## Main definitions

* `TauCeti.BigWitt.wittStructure Φ n`: the `n`-th big Witt structure polynomial of `Φ`.

## Main results

* `TauCeti.BigWitt.ghostPolynomial_wittStructure`: the defining ghost identity.
* `TauCeti.BigWitt.eq_wittStructure_of_ghostPolynomial_eq`: uniqueness of the structure
  polynomials.
* `TauCeti.BigWitt.ghostPolynomial_aeval_wittStructure`: the ghost identity after evaluation in an
  arbitrary commutative ring.
* `TauCeti.BigWitt.aeval_wittStructure_congr`: `φ_n` only depends on the variables `X (i, d)`
  with `d ∣ n`.

## References

* L. Hesselholt, *The big de Rham–Witt complex*, Acta Math. 214 (2015), Proposition 1.2.
-/

public section

namespace TauCeti.BigWitt

open _root_.MvPolynomial

variable {idx : Type*}

/-- The ghost sequence `n ↦ Φ(w_n(X (i, ·)) : i : idx)` lies in the image of the ghost map over
`ℤ[X (i, k)]`, by Dwork's criterion with the Frobenius lifts `expand p`. -/
private theorem exists_ghostPolynomial_eq_aeval (Φ : MvPolynomial idx ℤ) :
    ∃ x : ℕ → MvPolynomial (idx × ℕ) ℤ, ∀ n ∈ (⊤ : TruncationSet),
      ghostPolynomial n x = aeval (fun i ↦ ghostPolynomial n fun k ↦ X (i, k)) Φ := by
  have hφ : ∀ p : ℕ, p.Prime → ∀ a : MvPolynomial (idx × ℕ) ℤ,
      (expand p : _ →ₐ[ℤ] _).toRingHom a - a ^ p ∈ Ideal.span {(p : MvPolynomial (idx × ℕ) ℤ)} :=
    fun p hp a ↦ have := Fact.mk hp; Ideal.mem_span_singleton.2 (natCast_dvd_expand_sub_pow p a)
  refine (ghost_image ⊤ (fun p ↦ (expand p : _ →ₐ[ℤ] _).toRingHom)
    (fun p hp _ ↦ hφ p hp) _).2 fun p hp n _ _ ↦ ?_
  -- reduce modulo the ideal and compare the arguments of `Φ`
  rw [← Ideal.Quotient.eq]
  simp only [← Ideal.Quotient.mkₐ_eq_mk ℤ, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    comp_aeval_apply]
  congr 2
  funext i
  exact Ideal.Quotient.eq.2 (ghostPolynomial_sub_map_ghostPolynomial_div_mem hp _ (hφ p hp) n _)

/-- The `n`-th big Witt structure polynomial of an integral polynomial `Φ` in variables indexed by
`idx`: the unique integral polynomials `φ_n`, `n > 0`, in the variables `X (i, k)` whose ghost
components are `w_n(φ) = Φ(w_n(X (i, ·)) : i : idx)` (`ghostPolynomial_wittStructure`). It is
normalised to be `0` at `n = 0`, where no ghost identity constrains it. -/
noncomputable def wittStructure (Φ : MvPolynomial idx ℤ) (n : ℕ) : MvPolynomial (idx × ℕ) ℤ :=
  if n = 0 then 0 else (exists_ghostPolynomial_eq_aeval Φ).choose n

@[simp]
theorem wittStructure_zero (Φ : MvPolynomial idx ℤ) : wittStructure Φ 0 = 0 := by
  simp [wittStructure]

/-- **The defining property of the big Witt structure polynomials.** For every positive `n`,
`w_n(φ_1, φ_2, …) = Φ(w_n(X (i, ·)) : i : idx)`. -/
theorem ghostPolynomial_wittStructure (Φ : MvPolynomial idx ℤ) {n : ℕ} (hn : n ≠ 0) :
    ghostPolynomial n (wittStructure Φ) =
      aeval (fun i ↦ ghostPolynomial n fun k ↦ X (i, k)) Φ := by
  rw [← (exists_ghostPolynomial_eq_aeval Φ).choose_spec n (Nat.pos_of_ne_zero hn)]
  exact ghostPolynomial_congr fun d hd ↦ by simp [wittStructure, ne_zero_of_dvd_ne_zero hn hd]

/-- **Uniqueness of the big Witt structure polynomials.** Any family of integral polynomials with
the ghost components of `wittStructure Φ` at every positive index agrees with it at every positive
index. -/
theorem eq_wittStructure_of_ghostPolynomial_eq {Φ : MvPolynomial idx ℤ}
    {ψ : ℕ → MvPolynomial (idx × ℕ) ℤ}
    (h : ∀ n, n ≠ 0 → ghostPolynomial n ψ = aeval (fun i ↦ ghostPolynomial n fun k ↦ X (i, k)) Φ)
    {n : ℕ} (hn : n ≠ 0) : ψ n = wittStructure Φ n := by
  refine (eqOn_ghostPolynomial_iff (S := ⊤)
    fun _ _ hp ↦ .of_ne_zero (Nat.cast_ne_zero.2 hp.ne_zero)).1 (fun k hk ↦ ?_)
    (Nat.pos_of_ne_zero hn)
  have hk : k ≠ 0 := (TruncationSet.mem_top.1 hk).ne'
  beta_reduce
  rw [h k hk, ghostPolynomial_wittStructure Φ hk]

/-- **The ghost identity after evaluation.** Evaluating the big Witt structure polynomials of `Φ`
at the coordinates `v (i, k)` in a commutative ring and taking the `n`-th ghost component is the
same as applying `Φ` to the `n`-th ghost components of the sequences `v (i, ·)`. -/
theorem ghostPolynomial_aeval_wittStructure {R : Type*} [CommRing R] (Φ : MvPolynomial idx ℤ)
    (v : idx × ℕ → R) {n : ℕ} (hn : n ≠ 0) :
    ghostPolynomial n (fun k ↦ aeval v (wittStructure Φ k)) =
      aeval (fun i ↦ ghostPolynomial n fun k ↦ v (i, k)) Φ := by
  have h := congrArg (aeval v) (ghostPolynomial_wittStructure Φ hn)
  rw [map_ghostPolynomial, comp_aeval_apply] at h
  simpa only [map_ghostPolynomial, Function.comp_def, aeval_X] using h

/-- The big Witt structure polynomial `φ_n` only involves the variables `X (i, d)` with `d ∣ n`:
its values at two assignments agreeing on these variables coincide. -/
theorem aeval_wittStructure_congr {R : Type*} [CommRing R] (Φ : MvPolynomial idx ℤ) {n : ℕ}
    {v w : idx × ℕ → R} (h : ∀ i d, d ∣ n → v (i, d) = w (i, d)) :
    aeval v (wittStructure Φ n) = aeval w (wittStructure Φ n) := by
  classical
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  -- `π` kills the variables `X (i, d)` with `d ∤ n`; it fixes `φ_n` by uniqueness over `Div(n)`
  set π : MvPolynomial (idx × ℕ) ℤ →ₐ[ℤ] MvPolynomial (idx × ℕ) ℤ :=
    aeval fun ik ↦ if ik.snd ∣ n then X ik else 0
  have hπ : π (wittStructure Φ n) = wittStructure Φ n := by
    refine (eqOn_ghostPolynomial_iff (S := TruncationSet.divisors n) (x := π ∘ wittStructure Φ)
      fun _ _ hp ↦ .of_ne_zero (Nat.cast_ne_zero.2 hp.ne_zero)).1 (fun k hk ↦ ?_)
      (TruncationSet.mem_divisors_self hn)
    obtain ⟨hkn, -⟩ := TruncationSet.mem_divisors.1 hk
    have hk0 : k ≠ 0 := ne_zero_of_dvd_ne_zero hn hkn
    simp only [π, Function.comp_def]
    refine (ghostPolynomial_aeval_wittStructure Φ _ hk0).trans ?_
    rw [ghostPolynomial_wittStructure Φ hk0]
    congr 2
    funext i
    exact ghostPolynomial_congr fun d hd ↦ by simp [hd.trans hkn]
  rw [← hπ, comp_aeval_apply, comp_aeval_apply]
  congr 2
  funext ik
  by_cases hd : ik.snd ∣ n
  · simpa [hd] using h ik.fst ik.snd hd
  · simp [hd]

end TauCeti.BigWitt
