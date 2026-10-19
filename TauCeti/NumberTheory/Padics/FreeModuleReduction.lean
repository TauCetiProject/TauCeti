/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.RingTheory.QuotSMulTop
import Mathlib.Tactic.LinearCombination
import TauCeti.NumberTheory.Padics.RingHoms

/-!
# Reduction modulo `p` of finite free `ℤ_p`-modules

A finite free `ℤ_p`-module `M` of rank `r` is isomorphic to `ℤ_p ^ r`, so its reduction
`M / pM` is isomorphic to `(ℤ_p / p) ^ r ≃ 𝔽_p ^ r` and has `p ^ r` elements.

For the free `ℤ_p`-module `ℤ_p[X] = X →₀ ℤ_[p]`, the integral lattice `ℤ[X] = X →₀ ℤ`, embedded
by the integral cast `Finsupp.mapRange.addMonoidHom (Int.castAddHom ℤ_[p])`, already surjects
onto `ℤ_p[X] / p ℤ_p[X]`, and it is `p`-saturated in `ℤ_p[X]`. So the cokernel of
`ℤ[X] → ℤ_p[X]` is uniquely `p`-divisible.

## Main results

* `TauCeti.natCard_quotient_padicInt_smul_top`: reduction modulo `p` of a finite free
  `ℤ_p`-module of rank `r` has `p^r` elements.
* `TauCeti.PadicInt.exists_finsupp_eq_mapRange_intCast_add`: every element of `ℤ_p[X]` lies in
  `ℤ[X]` modulo `p`.
* `TauCeti.PadicInt.mem_range_finsupp_mapRange_intCast_of_smul_mem`: an element of `ℤ_p[X]`
  whose `p`-fold lies in `ℤ[X]` lies in `ℤ[X]`.
-/

public section

namespace TauCeti

open scoped Pointwise

universe u

variable (p : ℕ) [Fact p.Prime]

/-- **The reduction of a finite free `ℤ_p`-module has the expected cardinality.** If `M` is
free of finite rank over `ℤ_p`, then `M / pM` has `p ^ finrank M` elements. -/
theorem natCard_quotient_padicInt_smul_top (M : Type u) [AddCommGroup M] [Module ℤ_[p] M]
    [Module.Free ℤ_[p] M] [Module.Finite ℤ_[p] M] :
    Nat.card (M ⧸ (p : ℤ_[p]) • (⊤ : Submodule ℤ_[p] M)) =
      p ^ Module.finrank ℤ_[p] M := by
  classical
  let ι := Module.Free.ChooseBasisIndex ℤ_[p] M
  let b := Module.Free.chooseBasis ℤ_[p] M
  let e : (M ⧸ (p : ℤ_[p]) • (⊤ : Submodule ℤ_[p] M)) ≃ₗ[ℤ_[p]]
      ((i : ι) → ℤ_[p]) ⧸ (p : ℤ_[p]) • (⊤ : Submodule ℤ_[p] (ι → ℤ_[p])) :=
    QuotSMulTop.congr (p : ℤ_[p]) b.equivFun
  have hpi : (p : ℤ_[p]) • (⊤ : Submodule ℤ_[p] (ι → ℤ_[p])) =
      Submodule.pi Set.univ (fun _ : ι ↦ Ideal.span {(p : ℤ_[p])}) := by
    ext x
    simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top,
      Submodule.mem_pi, Set.mem_univ, forall_const, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨y, -, hy⟩ i
      exact ⟨y i, (congrFun hy i).symm⟩
    · intro hx
      choose y hy using hx
      exact ⟨y, trivial, (funext hy).symm⟩
  let q : (((i : ι) → ℤ_[p]) ⧸ (p : ℤ_[p]) •
      (⊤ : Submodule ℤ_[p] (ι → ℤ_[p]))) ≃ₗ[ℤ_[p]]
      ((i : ι) → (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])})) :=
    (Submodule.quotEquivOfEq _ _ hpi).trans
      (Submodule.quotientPi fun _ : ι ↦ Ideal.span {(p : ℤ_[p])})
  rw [Nat.card_congr e.toEquiv, Nat.card_congr q.toEquiv, Nat.card_pi,
    PadicInt.natCard_quotient_span (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero),
    PadicInt.valuation_p, pow_one, Finset.prod_const, Finset.card_univ,
    ← Module.finrank_eq_card_chooseBasisIndex]

namespace PadicInt

variable {p} {X : Type*}

/-- Every element of `ℤ_p[X] = X →₀ ℤ_[p]` lies in the integral lattice `ℤ[X]` modulo `p`: every
`p`-adic integer is congruent to an integer modulo `p`. -/
theorem exists_finsupp_eq_mapRange_intCast_add (v : X →₀ ℤ_[p]) :
    ∃ w : X →₀ ℤ, ∃ y : X →₀ ℤ_[p],
      v = Finsupp.mapRange.addMonoidHom (Int.castAddHom ℤ_[p]) w + (p : ℤ) • y := by
  classical
  have h (a : ℤ_[p]) : ∃ n : ℤ, ∃ z, a = n + p * z := by
    obtain ⟨n, -, hn⟩ := PadicInt.exists_mem_range a
    rw [PadicInt.maximalIdeal_eq_span_p (p := p)] at hn
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hn
    exact ⟨n, z, by push_cast; linear_combination -hz⟩
  choose n z hz using h
  -- choose the decomposition `0 = 0 + p • 0` at `0`, so that both parts are finitely supported
  refine ⟨v.mapRange (fun a ↦ if a = 0 then 0 else n a) (by simp),
    v.mapRange (fun a ↦ if a = 0 then 0 else z a) (by simp), Finsupp.ext fun x ↦ ?_⟩
  by_cases hx : v x = 0
  · simp [hx]
  · simpa [hx] using hz (v x)

/-- An element of `ℤ_p[X] = X →₀ ℤ_[p]` whose `p`-fold lies in the integral lattice `ℤ[X]` lies
in `ℤ[X]` itself: if `p a = n` for an integer `n`, then `‖n‖ < 1`, so `p ∣ n` and `a = n / p`. -/
theorem mem_range_finsupp_mapRange_intCast_of_smul_mem {v : X →₀ ℤ_[p]}
    (h : (p : ℤ) • v ∈ (Finsupp.mapRange.addMonoidHom (Int.castAddHom ℤ_[p])).range) :
    v ∈ (Finsupp.mapRange.addMonoidHom (Int.castAddHom ℤ_[p])).range := by
  obtain ⟨w, hw⟩ := h
  refine ⟨w.mapRange (· / (p : ℤ)) (Int.zero_ediv _), Finsupp.ext fun x ↦ ?_⟩
  have hx : (p : ℤ_[p]) * v x = w x := by
    have := DFunLike.congr_fun hw x
    simp only [Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_apply,
      Int.coe_castAddHom] at this
    rw [this, Finsupp.smul_apply, zsmul_eq_mul, Int.cast_natCast]
  obtain ⟨m, hm⟩ := (PadicInt.norm_int_lt_one_iff_dvd (w x)).mp <|
    (PadicInt.norm_lt_one_iff_dvd _).mpr ⟨v x, hx.symm⟩
  have hp : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  simp only [Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_apply, Int.coe_castAddHom, hm,
    Int.mul_ediv_cancel_left _ hp]
  refine mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) ?_
  rw [hx, hm]
  push_cast
  ring

end PadicInt

end TauCeti
