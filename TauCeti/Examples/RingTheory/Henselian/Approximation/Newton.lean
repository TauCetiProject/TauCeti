/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import TauCeti.Algebra.MvPolynomial.Eval
import TauCeti.RingTheory.Henselian.Approximation.Newton
import TauCeti.RingTheory.MvPolynomial.Ideal

/-!
# Checks for Newton approximation with Elkik's Jacobian ideal

These importing examples exercise `TauCeti.RingTheory.Henselian.Approximation.Newton` across the
étale (`h = 0`) and ramified (`h ≥ 1`) regimes, overdetermined rectangular systems whose full-size
minors vanish unless colon factors are used, infinite variable index types (`ι = ℕ`), degenerate
filtrations (`σ = Empty`, `I = ⊥`, `t = 1`), and boundary counterexamples showing that neither
`2 * h < n` nor `IsLeftRegular (t ^ h)` can be dropped.
-/

open MvPolynomial TauCeti.HenselianApproximation

namespace TauCeti.Examples.HenselianApproximation

/-- With no equations (`σ = Empty`), `h = 0` and `n = 1`, lifting holds over any `(t) * I`-adically
complete ring without any regularity assumption on `t`. -/
example {R ι : Type*} [CommRing R] (t : R) (I : Ideal R)
    [IsAdicComplete (Ideal.span {t} * I) R] (a : ι → R) :
    ∃ b : ι → R, (∀ i, b i - a i ∈ filtrationIdeal t I 1) ∧
      (∀ e : Empty, MvPolynomial.eval b (nomatch e : MvPolynomial ι R) = 0) ∧
      1 ∈ (elkikJacobianIdeal (fun e : Empty ↦ (nomatch e : MvPolynomial ι R))).map
        (MvPolynomial.eval b) := by
  have hjac : t ^ 0 ∈
      (elkikJacobianIdeal (fun e : Empty ↦ (nomatch e : MvPolynomial ι R))).map
        (MvPolynomial.eval a) ⊔ filtrationIdeal t I (1 - 0) := by
    have hone : t ^ 0 = MvPolynomial.eval a 1 := by simp
    exact Ideal.mem_sup_left (hone ▸ Ideal.mem_map_of_mem _ (by simp))
  simpa using exists_eval_eq_zero_of_isAdicComplete t I
    (fun e : Empty ↦ (nomatch e : MvPolynomial ι R)) a (h := 0) (n := 1) (by decide)
    (by simpa using (isRegular_one (R := R)).left) (fun e ↦ nomatch e) hjac

/-- For the zero ideal `I = ⊥`, every commutative ring is `(t) * ⊥`-adically complete, and
`exists_span_le_ker_eval_of_isAdicComplete` applies directly (`t = 6`, `h = 1`, `n = 3`). -/
example :
    ∃ b : Unit → ℤ, (∀ i, b i - 3 ∈ filtrationIdeal (6 : ℤ) ⊥ 2) ∧
      Ideal.span (Set.range fun _ : Unit ↦ (X () ^ 2 - C 9 : MvPolynomial Unit ℤ)) ≤
        Ideal.span (Set.range fun i : Unit ↦ X i - C (b i)) ∧
      C ((6 : ℤ) ^ 1) ∈
        elkikJacobianIdeal (fun _ : Unit ↦ (X () ^ 2 - C 9 : MvPolynomial Unit ℤ)) ⊔
          RingHom.ker (MvPolynomial.eval b) := by
  have : IsAdicComplete (Ideal.span {(6 : ℤ)} * (⊥ : Ideal ℤ)) ℤ := by
    rw [Ideal.mul_bot]
    infer_instance
  let f : Unit → MvPolynomial Unit ℤ := fun _ ↦ X () ^ 2 - C 9
  let a : Unit → ℤ := fun _ ↦ 3
  have hp : pderiv () (f ()) = 2 * X () := by
    simp only [f, map_sub, pderiv_C]
    simp
  have hderiv : (2 * X () : MvPolynomial Unit ℤ) ∈ elkikJacobianIdeal f :=
    hp ▸ pderiv_mem_elkikJacobianIdeal f () () (by simp [Set.range_unique])
  have ha : Ideal.span (Set.range f) ≤
      RingHom.ker (MvPolynomial.eval a) ⊔ (filtrationIdeal (6 : ℤ) ⊥ 3).map C := by
    rw [Ideal.span_le]
    rintro _ ⟨_, rfl⟩
    refine Ideal.mem_sup_left ?_
    rw [RingHom.mem_ker]
    norm_num [f, a]
  have hjac : C ((6 : ℤ) ^ 1) ∈ elkikJacobianIdeal f ⊔ RingHom.ker (MvPolynomial.eval a) := by
    have hk : C ((6 : ℤ) ^ 1) - 2 * X () ∈ RingHom.ker (MvPolynomial.eval a) := by
      rw [RingHom.mem_ker]
      norm_num [a]
    simpa only [add_sub_cancel] using Submodule.add_mem_sup hderiv hk
  have ht : IsLeftRegular ((6 : ℤ) ^ 1) := fun x y hxy ↦ by
    dsimp at hxy
    omega
  obtain ⟨b, hb1, hb2, hb3⟩ :=
    exists_span_le_ker_eval_of_isAdicComplete 6 ⊥ f a (h := 1) (n := 3) (by decide) ht ha hjac
  exact ⟨b, hb1, MvPolynomial.ker_eval b ▸ hb2, hb3⟩

/-- Étale quadratic lifting (`h = 0`, `n = 2`) in `completion (3 : ℤ) ⊤`: starting at `a = 4` with
`4 ^ 2 - 7 = 9 ∈ (3) ^ 2` and `f'(4) = 8 ≡ -1 (mod 9)`, `X ^ 2 - 7` acquires an exact root in the
`3`-adic completion of `ℤ` congruent to `4` modulo `9`. -/
example :
    ∃ b : Unit → completion (3 : ℤ) ⊤,
      eval 3 ⊤ 2 (b ()) = residueMap 3 ⊤ 2 4 ∧
      b () ^ 2 - completionMap 3 ⊤ 7 = 0 := by
  let f : Unit → MvPolynomial Unit ℤ := fun _ ↦ X () ^ 2 - C 7
  let a : Unit → ℤ := fun _ ↦ 4
  have hp : pderiv () (f ()) = 2 * X () := by
    simp only [f, map_sub, pderiv_C]
    simp
  have hderiv : (2 * X () : MvPolynomial Unit ℤ) ∈ elkikJacobianIdeal f :=
    hp ▸ pderiv_mem_elkikJacobianIdeal f () () (by simp [Set.range_unique])
  have hjac : (3 : ℤ) ^ 0 ∈ (elkikJacobianIdeal f).map (MvPolynomial.eval a) ⊔
      filtrationIdeal 3 ⊤ (2 - 0) := by
    have hu : MvPolynomial.eval a (C (-1) * (2 * X ())) ∈
        (elkikJacobianIdeal f).map (MvPolynomial.eval a) :=
      Ideal.mem_map_of_mem _ (Ideal.mul_mem_left _ _ hderiv)
    have hr : (9 : ℤ) ∈ filtrationIdeal 3 ⊤ 2 := by
      norm_num [filtrationIdeal_def, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    have hsum : MvPolynomial.eval a (C (-1) * (2 * X ())) + 9 = (3 : ℤ) ^ 0 := by
      norm_num [a]
    exact hsum ▸ Submodule.add_mem_sup hu hr
  have ha : ∀ r, MvPolynomial.eval a (f r) ∈ filtrationIdeal 3 ⊤ 2 := fun _ ↦ by
    norm_num [f, a, filtrationIdeal_def, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  obtain ⟨b, hb_res, hb_root, -⟩ := exists_eval_completion_eq_zero (3 : ℤ) ⊤ f a
    (h := 0) (n := 2) (by decide) isRegular_one.left ha hjac
  refine ⟨b, hb_res (), ?_⟩
  simpa [f] using hb_root ()

/-- Ramified quadratic lifting (`h = 1`, `n = 4 > 2 * 1`) in `completion (2 : ℤ) ⊤`: for
`f(X) = X ^ 2 - 17` at `a = 1`, the derivative `f'(1) = 2` is not a `2`-adic unit, yet
`1 ^ 2 - 17 = -16 ∈ (2) ^ 4` lifts to an exact square root of `17` congruent to `1` modulo `8`. -/
example :
    IsLeftRegular (completionMap (2 : ℤ) ⊤ 2) ∧
      ∃ b : Unit → completion (2 : ℤ) ⊤,
        eval 2 ⊤ 3 (b ()) = residueMap 2 ⊤ 3 1 ∧
        b () ^ 2 - completionMap 2 ⊤ 17 = 0 := by
  let f : Unit → MvPolynomial Unit ℤ := fun _ ↦ X () ^ 2 - C 17
  let a : Unit → ℤ := fun _ ↦ 1
  have hp : pderiv () (f ()) = 2 * X () := by
    simp only [f, map_sub, pderiv_C]
    simp
  have hderiv : (2 * X () : MvPolynomial Unit ℤ) ∈ elkikJacobianIdeal f :=
    hp ▸ pderiv_mem_elkikJacobianIdeal f () () (by simp [Set.range_unique])
  have hjac : (2 : ℤ) ^ 1 ∈ (elkikJacobianIdeal f).map (MvPolynomial.eval a) ⊔
      filtrationIdeal 2 ⊤ (4 - 1) := by
    refine Ideal.mem_sup_left ?_
    have hev : MvPolynomial.eval a (2 * X ()) = (2 : ℤ) ^ 1 := by norm_num [a]
    exact hev ▸ Ideal.mem_map_of_mem _ hderiv
  have ha : ∀ r, MvPolynomial.eval a (f r) ∈ filtrationIdeal 2 ⊤ 4 := fun _ ↦ by
    norm_num [f, a, filtrationIdeal_def, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have ht : IsLeftRegular ((2 : ℤ) ^ 1) := by
    intro x y hxy
    dsimp at hxy
    omega
  have ht2 : IsLeftRegular (2 : ℤ) := by simpa using ht
  obtain ⟨b, hb_res, hb_root, -⟩ := exists_eval_completion_eq_zero (2 : ℤ) ⊤ f a
    (h := 1) (n := 4) (by decide) ht ha hjac
  refine ⟨isLeftRegular_completionMap ⊤ ht2, b, hb_res (), ?_⟩
  simpa [f] using hb_root ()

/-- Overdetermined rectangular system (`2` equations in `1` variable) over `PowerSeries ℤ`:
`f 0 = Y ^ 2 + Y - T` and `f 1 = Y ^ 3 + Y ^ 2 - T * Y = Y * f 0`. Full `2 × 2` Jacobian minors on
`{0, 1}` vanish identically because there is only one variable, whereas the singleton selection
`{0}` has unit colon ideal and unit derivative `2 Y + 1` at `0`. -/
example :
    ∃ b : Unit → PowerSeries ℤ,
      PowerSeries.X ∣ b () ∧
      b () ^ 2 + b () - PowerSeries.X = 0 ∧
      b () ^ 3 + b () ^ 2 - PowerSeries.X * b () = 0 := by
  let T : PowerSeries ℤ := PowerSeries.X
  let f : Fin 2 → MvPolynomial Unit (PowerSeries ℤ) :=
    ![X () ^ 2 + X () - C T, X () ^ 3 + X () ^ 2 - C T * X ()]
  let a : Unit → PowerSeries ℤ := fun _ ↦ 0
  have hf1 : f 1 = X () * f 0 := by
    simp only [f, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hspan : Ideal.span (Set.range f) ≤ Ideal.span {f 0} := by
    rw [Ideal.span_le, Set.range_subset_iff, Fin.forall_fin_two]
    exact ⟨Ideal.subset_span rfl, hf1 ▸ Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)⟩
  have hderiv : pderiv () (f 0) ∈ elkikJacobianIdeal f :=
    pderiv_mem_elkikJacobianIdeal f 0 () hspan
  have hjac :
      T ^ 0 ∈ (elkikJacobianIdeal f).map (MvPolynomial.eval a) ⊔ Ideal.span {T ^ (1 - 0)} := by
    refine Ideal.mem_sup_left ?_
    have hev : MvPolynomial.eval a (pderiv () (f 0)) = T ^ 0 := by
      simp only [f, Matrix.cons_val_zero, map_sub, map_add, pderiv_C]
      simp [a]
    exact hev ▸ Ideal.mem_map_of_mem _ hderiv
  have ha : ∀ r : Fin 2, T ^ 1 ∣ MvPolynomial.eval a (f r) := by
    intro r
    fin_cases r <;> simp [f, a]
  obtain ⟨b, hb_dvd, hb_zero, -⟩ := exists_eval_eq_zero_of_isAdicComplete_span_singleton T f a
    (h := 0) (n := 1) (by decide) isRegular_one.left ha hjac
  refine ⟨b, ?_, ?_, ?_⟩
  · simpa [T, a] using hb_dvd ()
  · simpa [f] using hb_zero 0
  · simpa [f] using hb_zero 1

/-- Single Newton step on infinitely many variables (`ι = ℕ`): starting at `0 : ℕ → ℤ` for
`X 0 ^ 2 + X 0 - 3`, one step modifies only finitely many coordinates while improving the residual
from `(3)` to `(9)`. -/
example :
    ∃ b : ℕ → ℤ, {i : ℕ | b i ≠ 0}.Finite ∧
      (∀ i, (3 : ℤ) ∣ b i) ∧
      (9 : ℤ) ∣ b 0 ^ 2 + b 0 - 3 := by
  let f : Unit → MvPolynomial ℕ ℤ := fun _ ↦ X 0 ^ 2 + X 0 - C 3
  let a : ℕ → ℤ := fun _ ↦ 0
  have hderiv : pderiv 0 (f ()) ∈ elkikJacobianIdeal f :=
    pderiv_mem_elkikJacobianIdeal f () 0 (by simp [Set.range_unique])
  have hjac : (3 : ℤ) ^ 0 ∈ (elkikJacobianIdeal f).map (MvPolynomial.eval a) ⊔
      filtrationIdeal 3 ⊤ (1 - 0) := by
    refine Ideal.mem_sup_left ?_
    have hev : MvPolynomial.eval a (pderiv 0 (f ())) = (3 : ℤ) ^ 0 := by
      simp only [f, map_sub, map_add, pderiv_C]
      simp [a]
    exact hev ▸ Ideal.mem_map_of_mem _ hderiv
  have ha : ∀ r, MvPolynomial.eval a (f r) ∈ filtrationIdeal 3 ⊤ 1 := fun _ ↦ by
    simp only [f, a, filtrationIdeal_def, Ideal.mul_top, pow_one, Ideal.mem_span_singleton,
      map_sub, map_add, map_pow, eval_X, eval_C]
    norm_num
  obtain ⟨b, hfin, hba, hfb⟩ := exists_approximateSolution_step (3 : ℤ) ⊤ f a
    (h := 0) (n := 1) (by decide) isRegular_one.left ha hjac
  refine ⟨b, hfin, fun i ↦ ?_, ?_⟩
  · have hm := hba i
    simpa [a, filtrationIdeal_def, Ideal.mem_span_singleton] using hm
  · have hm := filtrationIdeal_sq_le (3 : ℤ) ⊤ 1 (hfb ())
    simp only [f, filtrationIdeal_def, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton, map_sub, map_add, map_pow, eval_X, eval_C] at hm
    simpa using hm

/-- Congruence on `p.vars` suffices even when infinitely many unused variables differ arbitrarily
(`eval_sub_eval_mem_of_vars`). -/
example (x y : ℕ → ℤ) (I : Ideal ℤ) (h0 : x 0 - y 0 ∈ I) :
    MvPolynomial.eval x (X 0 ^ 2 : MvPolynomial ℕ ℤ) -
      MvPolynomial.eval y (X 0 ^ 2 : MvPolynomial ℕ ℤ) ∈ I := by
  refine MvPolynomial.eval_sub_eval_mem_of_vars _ fun i hi ↦ ?_
  have hx := vars_pow (X 0 : MvPolynomial ℕ ℤ) 2 hi
  rw [vars_X, Finset.mem_singleton] at hx
  exact hx ▸ h0

/-- **Sharpness of `2 * h < n`:** when `h = 1` and `n = 2 = 2 * h`, `f(X) = X ^ 2 - 5` at `a = 1`
satisfies `f(1) = -4 ∈ filtrationIdeal 2 ⊤ 2`, `2 ^ 1 ∈ (elkikJacobianIdeal f).map (eval 1)`, and
`IsLeftRegular ((2 : ℤ) ^ 1)`, yet `X ^ 2 - 5` has no root in `completion (2 : ℤ) ⊤` (already none
modulo `8`). -/
example :
    let f : Unit → MvPolynomial Unit ℤ := fun _ ↦ X () ^ 2 - C 5
    let a : Unit → ℤ := fun _ ↦ 1
    MvPolynomial.eval a (f ()) ∈ filtrationIdeal (2 : ℤ) ⊤ 2 ∧
      (2 : ℤ) ^ 1 ∈ (elkikJacobianIdeal f).map (MvPolynomial.eval a) ∧
      ¬ ∃ b : Unit → completion (2 : ℤ) ⊤,
        MvPolynomial.eval b (MvPolynomial.map (completionMap 2 ⊤) (f ())) = 0 := by
  intro f a
  refine ⟨?_, ?_, ?_⟩
  · norm_num [f, a, filtrationIdeal_def, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  · have hp : pderiv () (f ()) = 2 * X () := by
      simp only [f, map_sub, pderiv_C]
      simp
    have hderiv : (2 * X () : MvPolynomial Unit ℤ) ∈ elkikJacobianIdeal f :=
      hp ▸ pderiv_mem_elkikJacobianIdeal f () () (by simp [Set.range_unique])
    have hev : MvPolynomial.eval a (2 * X ()) = (2 : ℤ) ^ 1 := by norm_num [a]
    exact hev ▸ Ideal.mem_map_of_mem _ hderiv
  · rintro ⟨b, hb⟩
    obtain ⟨r, hr⟩ := residueMap_surjective (2 : ℤ) ⊤ 3 (eval 2 ⊤ 3 (b ()))
    have h0 : residueMap (2 : ℤ) ⊤ 3 (r ^ 2 - 5) = 0 := by
      have h1 := congrArg (eval 2 ⊤ 3) hb
      simpa [f, map_ofNat, ← hr] using h1
    have hmem : r ^ 2 - 5 ∈ filtrationIdeal (2 : ℤ) ⊤ 3 :=
      (residueMap_eq_zero_iff 2 ⊤ 3 _).mp h0
    rw [filtrationIdeal_def, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at hmem
    have hmod : ((r : ZMod 8)) ^ 2 - 5 = 0 := by
      have hcast : (((r ^ 2 - 5 : ℤ) : ZMod 8)) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mpr (by norm_num at hmem; exact hmem)
      push_cast at hcast
      exact hcast
    have hsq : ∀ z : ZMod 8, z ^ 2 - 5 ≠ 0 := by decide
    exact hsq (r : ZMod 8) hmod

/-- **Necessity of `IsLeftRegular (t ^ h)`:** over the `(2)`-adically complete ring `ZMod 16` with
zero-divisor parameter `t = 2`, `h = 1` and `n = 3 > 2 * h`, the constant equation `f = C 8` at
`a = 0` satisfies `f(0) = 8 = 2 ^ 3 ∈ filtrationIdeal 2 ⊤ 3` and `2 ^ 1 ∈ H(0)` (via
`C 2 ∈ Ann(C 8)`), yet neither a single Newton step into `filtrationIdeal 2 ⊤ 2 ^ 2 = ⊥` nor an
exact root exists. -/
example :
    let f : Unit → MvPolynomial Unit (ZMod 16) := fun _ ↦ C 8
    let a : Unit → ZMod 16 := fun _ ↦ 0
    IsAdicComplete (Ideal.span {(2 : ZMod 16)}) (ZMod 16) ∧
      MvPolynomial.eval a (f ()) ∈ filtrationIdeal (2 : ZMod 16) ⊤ 3 ∧
      (2 : ZMod 16) ^ 1 ∈ (elkikJacobianIdeal f).map (MvPolynomial.eval a) ∧
      (¬ ∃ b : Unit → ZMod 16, MvPolynomial.eval b (f ()) ∈
        filtrationIdeal (2 : ZMod 16) ⊤ (3 - 1) ^ 2) ∧
      ¬ ∃ b : Unit → ZMod 16, MvPolynomial.eval b (f ()) = 0 := by
  intro f a
  have hnil : Ideal.span {(2 : ZMod 16)} ^ 4 = ⊥ := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_eq_bot]
    decide
  have hcomp : IsAdicComplete (Ideal.span {(2 : ZMod 16)}) (ZMod 16) :=
    { haus' x hx := by
        have h4 := SModEq.zero.mp (hx 4)
        rw [hnil, Ideal.smul_eq_mul, Ideal.bot_mul, Submodule.mem_bot] at h4
        exact h4
      prec' u hu := ⟨u 4, fun m ↦ by
        rcases le_or_gt m 4 with hm | hm
        · exact hu hm
        · have h4m := SModEq.sub_mem.mp (hu (Nat.le_of_lt hm))
          rw [hnil, Ideal.smul_eq_mul, Ideal.bot_mul, Submodule.mem_bot, sub_eq_zero] at h4m
          rw [h4m]⟩ }
  refine ⟨hcomp, ?_, ?_, ?_, ?_⟩
  · rw [filtrationIdeal_def, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    simp only [f, MvPolynomial.eval_C]
    exact ⟨1, by decide⟩
  · have hann : (C 2 : MvPolynomial Unit (ZMod 16)) ∈
        (Ideal.span (Set.range f)).annihilator := by
      rw [Submodule.mem_annihilator]
      intro p hp
      have hle : Ideal.span (Set.range f) ≤
          (⊥ : Ideal (MvPolynomial Unit (ZMod 16))).colon {C 2} := by
        rw [Ideal.span_le]
        rintro _ ⟨_, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_colon_singleton, smul_eq_mul, Submodule.mem_bot]
        have h16 : (8 : ZMod 16) * 2 = 0 := by decide
        simp [f, ← map_mul, h16]
      have hp' := Submodule.mem_colon_singleton.mp (hle hp)
      simpa only [smul_eq_mul, Submodule.mem_bot, mul_comm] using hp'
    have hmem : (C 2 : MvPolynomial Unit (ZMod 16)) ∈ elkikJacobianIdeal f :=
      annihilator_span_range_le_elkikJacobianIdeal f hann
    simpa using Ideal.mem_map_of_mem (MvPolynomial.eval a) hmem
  · rintro ⟨b, hb⟩
    rw [filtrationIdeal_def, Ideal.mul_top, ← pow_mul, Ideal.span_singleton_pow,
      Ideal.span_singleton_eq_bot.mpr (by decide : (2 : ZMod 16) ^ (2 * (3 - 1)) = 0),
      Submodule.mem_bot] at hb
    simp only [f, eval_C] at hb
    exact absurd hb (by decide)
  · rintro ⟨b, hb⟩
    simp only [f, eval_C] at hb
    exact absurd hb (by decide)

end TauCeti.Examples.HenselianApproximation
