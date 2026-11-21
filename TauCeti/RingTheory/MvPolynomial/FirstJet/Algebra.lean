/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.DoublePoint
import Mathlib.Data.ZMod.Defs

/-!
# Additional properties and examples for double-point quotients

This file complements `TauCeti.RingTheory.MvPolynomial.FirstJet` and
`TauCeti.RingTheory.MvPolynomial.DoublePoint` with basic monotonicity and small-index properties of
`TauCeti.doubleIdeal` over arbitrary commutative semirings, reindexing invariance for
`TauCeti.doublePointQuotientEquiv`, and worked examples over `ℚ`, `ℤ`, and arbitrary commutative
semirings.

## Main results

* `TauCeti.doubleIdeal_le_iInf_sq`, `TauCeti.doubleIdeal_isEmpty`, `TauCeti.doubleIdeal_unique`:
  containment and degenerate-index formulas for `doubleIdeal`.
* `TauCeti.doublePointQuotientEquiv_comp_equiv`: reindexing invariance of
  `doublePointQuotientEquiv`.
-/

public section

namespace TauCeti

open MvPolynomial

section DoubleIdeal

variable {σ ι κ R : Type*}

/-- The squared intersection ideal is always contained in the intersection of the squared point
ideals. -/
theorem doubleIdeal_le_iInf_sq [CommSemiring R] (P : ι → σ → R) :
    doubleIdeal P ≤ ⨅ i, RingHom.ker (eval (P i)) ^ 2 := by
  rw [doubleIdeal_def]
  exact le_iInf fun i ↦ Ideal.pow_right_mono (iInf_le _ i) 2

@[simp]
theorem doubleIdeal_isEmpty [CommSemiring R] [IsEmpty ι] (P : ι → σ → R) :
    doubleIdeal P = ⊤ := by
  simp [doubleIdeal_def]

@[simp]
theorem doubleIdeal_unique [CommSemiring R] [Unique ι] (P : ι → σ → R) :
    doubleIdeal P = RingHom.ker (eval (P default)) ^ 2 := by
  simp [doubleIdeal_def]

/-- Reindexing a point tuple along an equivalence commutes with `doublePointQuotientEquiv`. -/
theorem doublePointQuotientEquiv_comp_equiv [CommRing R] [Finite σ] [Finite ι] [Finite κ]
    [DecidableEq σ] {P : ι → σ → R}
    (hP : Pairwise (Function.onFun IsCoprime fun i ↦ RingHom.ker (eval (P i)))) (e : κ ≃ ι)
    (x : MvPolynomial σ R ⧸ doubleIdeal (P ∘ e)) (j : κ) :
    doublePointQuotientEquiv (P := P ∘ e) (fun _ _ h ↦ hP (e.injective.ne h)) x j =
      doublePointQuotientEquiv hP
        (Ideal.quotientEquivAlgOfEq R (doubleIdeal_comp P e) x) (e j) := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [congrFun (doublePointQuotientEquiv_mk (P := P ∘ e)
    (fun _ _ h ↦ hP (e.injective.ne h)) f) j,
    Ideal.quotientEquivAlgOfEq_mk, congrFun (doublePointQuotientEquiv_mk hP f) (e j)]
  rfl

end DoubleIdeal

/-! ### Examples -/

/-- At the origin, `X 0` maps to `(0, e₀)` and `X 0 ^ 2` maps to `0` in the square-zero first-jet
algebra. -/
example {R : Type*} [CommSemiring R] :
    jetAlgebra (0 : Fin 2 → R) (X 0) = TrivSqZeroExt.inr (Pi.single 0 1) ∧
    jetAlgebra (0 : Fin 2 → R) (X 0 ^ 2) = 0 := by
  refine ⟨by simp, ?_⟩
  rw [map_pow, jetAlgebra_X]
  simp [sq, TrivSqZeroExt.inr_mul_inr]

/-- For the two distinct points `0` and `1` on the affine line over `ℚ`, the class of
`X 0 * (X 0 - 1)` in the double-point quotient is nonzero, while its square is zero: the quotient
retains its nonreduced structure. -/
example :
    let P : Fin 2 → Fin 1 → ℚ := ![fun _ ↦ 0, fun _ ↦ 1]
    let f : MvPolynomial (Fin 1) ℚ := X 0 * (X 0 - 1)
    Ideal.Quotient.mk (doubleIdeal P) f ≠ 0 ∧ Ideal.Quotient.mk (doubleIdeal P) f ^ 2 = 0 := by
  intro P f
  have hP : Pairwise (Function.onFun IsCoprime fun i ↦ RingHom.ker (eval (P i))) := by
    refine fun i j hij ↦ isCoprime_ker_eval ?_
    intro h
    have h0 := congrFun h 0
    fin_cases i <;> fin_cases j <;> simp [P] at hij h0
  refine ⟨?_, ?_⟩
  · intro h0
    have hmem : f ∈ doubleIdeal P := Ideal.Quotient.eq_zero_iff_mem.1 h0
    have hd := ((mem_doubleIdeal_iff hP).1 hmem 0).2 0
    simp [f, P] at hd
  · rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, mem_doubleIdeal_iff hP]
    intro i
    fin_cases i <;> simp [f, P, sq]

/-- Over `ℤ`, the distinct points `0` and `2` on the affine line do not have comaximal evaluation
ideals: their sum is contained in the ideal `(X 0, 2)`, which is proper. -/
example :
    ¬ IsCoprime (RingHom.ker (eval (fun _ : Fin 1 ↦ (0 : ℤ))))
      (RingHom.ker (eval (fun _ : Fin 1 ↦ (2 : ℤ)))) := by
  intro h
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.1 h
  let φ : ℤ →+* ZMod 2 := Int.castRingHom (ZMod 2)
  have h02 : (φ ∘ fun _ : Fin 1 ↦ (0 : ℤ)) = φ ∘ fun _ : Fin 1 ↦ (2 : ℤ) := by
    funext _
    rw [Function.comp_apply, Function.comp_apply]
    exact (by decide : φ 0 = φ 2)
  have hmod : eval (φ ∘ fun _ : Fin 1 ↦ (0 : ℤ)) (map φ (a + b)) = 1 := by
    rw [hab, map_one, map_one]
  have ha0 : eval (φ ∘ fun _ : Fin 1 ↦ (0 : ℤ)) (map φ a) = 0 := by
    rw [eval_map, ← eval₂_comp, RingHom.mem_ker.1 ha, map_zero]
  have hb0 : eval (φ ∘ fun _ : Fin 1 ↦ (0 : ℤ)) (map φ b) = 0 := by
    rw [h02, eval_map, ← eval₂_comp, RingHom.mem_ker.1 hb, map_zero]
  rw [map_add, map_add, ha0, hb0, add_zero] at hmod
  exact zero_ne_one hmod

/-- The empty point tuple has zero-dimensional double-point quotient. -/
example {k : Type*} [Field k] (r : ℕ) (P : Fin 0 → Fin r → k) :
    Module.finrank k (MvPolynomial (Fin r) k ⧸ doubleIdeal P) = 0 := by
  simpa using finrank_quotient_doubleIdeal (P := P) fun i ↦ isEmptyElim i

end TauCeti
