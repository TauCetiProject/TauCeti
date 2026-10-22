/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Fintype.Defs
public import TauCeti.Computability.DFAO
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.ZMod.Basic
import TauCeti.Data.Nat.Periodic

/-!
# Automatic sequences

For a base `k`, a sequence `a : ℕ → Δ` is `k`-automatic if some deterministic automaton with
output (`TauCeti.DFAO`) with finitely many states and input alphabet `Fin k` computes `a n` from
the base-`k` digits of `n`. The digits are Mathlib's `Nat.digits k n`, read least significant
digit first and without padding zeros. Reading the least significant digit first is the
convention that Bridy (Section 2.1) calls reverse reading and that Christol, Kamae, Mendès France
and Rauzy (Section 4) call *lecture inverse*. Automatic sequences are the subject of
Christol's theorem, which identifies the `p`-automatic sequences with values in `𝔽_p`, for a
prime `p`, with the coefficient sequences of the power series over `𝔽_p` algebraic over
`𝔽_p(X)`, and of Cobham's theorem, which identifies the
sequences automatic in two multiplicatively independent bases with the eventually periodic ones.

The output alphabet is arbitrary; automaticity forces the range of the sequence to be finite. The
definition is made for every `k ≠ 0`. For `k = 1`, `Nat.digits 1 n` is the unary word of length
`n`, and the constructions below cover this case too.

## Main definitions and results

* `TauCeti.IsAutomatic k a`: the sequence `a` is `k`-automatic.
* `TauCeti.DFAO.isAutomatic`: a finite automaton computes a `k`-automatic sequence.
* `TauCeti.IsAutomatic.map`, `TauCeti.IsAutomatic.prod`: closure under changing the values and
  under pairing.
* `TauCeti.IsAutomatic.finite_range`: an automatic sequence takes finitely many values.
* `TauCeti.isAutomatic_const`: constant sequences are automatic.
* `TauCeti.isAutomatic_of_eventually_periodic`: eventually periodic sequences are automatic in
  every base.

## Implementation notes

For an eventually periodic sequence with preperiod `N` and period `p`, the automaton keeps the
value of the digits read so far and the current place value `k ^ i`, each only through its
truncation `min · N` and its residue modulo `p`. Both are compatible with addition and with
multiplication by a natural number, and together they determine the value of the sequence.

## References

* Andrew Bridy, *Automatic sequences and curves over finite fields*, Algebra & Number Theory
  11 (2017), Section 2.1.
* G. Christol, T. Kamae, M. Mendès France, G. Rauzy, *Suites algébriques, automates et
  substitutions*, Bull. Soc. Math. France 108 (1980), Section 4.
* Jakub Byszewski, Jakub Konieczny, *Automatic sequences and generalised polynomials*,
  Canad. J. Math. 72 (2020), Section 1.
-/

public section

universe u v

namespace TauCeti

/-- A sequence `a : ℕ → Δ` is **`k`-automatic** if a deterministic automaton with output, with
finitely many states and input alphabet `Fin k`, outputs `a n` on the base-`k` digits of `n`, read
least significant digit first (Mathlib's `Nat.digits k n`, so `0` is the empty word). -/
def IsAutomatic (k : ℕ) [NeZero k] {Δ : Type u} (a : ℕ → Δ) : Prop :=
  ∃ (σ : Type) (_ : Fintype σ) (M : DFAO (Fin k) σ Δ),
    ∀ n, a n = M.output (M.eval ((Nat.digits k n).map (Fin.ofNat k)))

variable {k : ℕ} [NeZero k] {Δ : Type u} {Δ' : Type v} {a : ℕ → Δ}

/-- Unfolding `IsAutomatic`: the introduction and elimination rule. -/
theorem isAutomatic_iff :
    IsAutomatic k a ↔ ∃ (σ : Type) (_ : Fintype σ) (M : DFAO (Fin k) σ Δ),
      ∀ n, a n = M.output (M.eval ((Nat.digits k n).map (Fin.ofNat k))) :=
  Iff.rfl

/-- The sequence computed by an automaton with finitely many states on base-`k` digits is
`k`-automatic. -/
theorem DFAO.isAutomatic {σ : Type} [Finite σ] (M : DFAO (Fin k) σ Δ) :
    IsAutomatic k fun n ↦ M.output (M.eval ((Nat.digits k n).map (Fin.ofNat k))) :=
  ⟨σ, Fintype.ofFinite σ, M, fun _ ↦ rfl⟩

/-- Changing the values of a `k`-automatic sequence along any map keeps it `k`-automatic. -/
theorem IsAutomatic.map (ha : IsAutomatic k a) (f : Δ → Δ') : IsAutomatic k fun n ↦ f (a n) := by
  obtain ⟨σ, _, M, hM⟩ := ha
  simpa [hM] using (M.mapOutput f).isAutomatic

/-- The pairing of two `k`-automatic sequences is `k`-automatic. -/
theorem IsAutomatic.prod {b : ℕ → Δ'} (ha : IsAutomatic k a) (hb : IsAutomatic k b) :
    IsAutomatic k fun n ↦ (a n, b n) := by
  obtain ⟨σ, _, M, hM⟩ := ha
  obtain ⟨τ, _, N, hN⟩ := hb
  simpa [hM, hN] using (M.prod N).isAutomatic

/-- A `k`-automatic sequence takes only finitely many values. -/
theorem IsAutomatic.finite_range (ha : IsAutomatic k a) : (Set.range a).Finite := by
  obtain ⟨σ, _, M, hM⟩ := ha
  refine (Set.finite_range M.output).subset ?_
  rintro _ ⟨n, rfl⟩
  exact ⟨_, (hM n).symm⟩

/-- Constant sequences are `k`-automatic, computed by a one-state automaton. -/
theorem isAutomatic_const (c : Δ) : IsAutomatic k fun _ : ℕ ↦ c :=
  (⟨fun _ _ ↦ (), (), fun _ ↦ c⟩ : DFAO (Fin k) Unit Δ).isAutomatic

/-! ### Eventually periodic sequences -/

section EventuallyPeriodic

variable {N p : ℕ}

/-- The truncation `min n N` and the residue of `n` modulo `p`, the finite data from which the
value at `n` of a sequence with preperiod `N` and period `p` is read off. -/
private def trunc (N p n : ℕ) : Fin (N + 1) × ZMod p :=
  (⟨min n N, by omega⟩, n)

/-- Addition on truncations, compatible with `trunc` (`trunc_add`). -/
private def truncAdd (x y : Fin (N + 1) × ZMod p) : Fin (N + 1) × ZMod p :=
  (⟨min (x.1 + y.1) N, by omega⟩, x.2 + y.2)

/-- Multiplication of a truncation by a natural number, compatible with `trunc` (`trunc_mul`). -/
private def truncMul (c : ℕ) (x : Fin (N + 1) × ZMod p) : Fin (N + 1) × ZMod p :=
  (⟨min (c * x.1) N, by omega⟩, c * x.2)

private theorem trunc_add (m n : ℕ) :
    trunc N p (m + n) = truncAdd (trunc N p m) (trunc N p n) := by
  ext
  · simp only [trunc, truncAdd]
    omega
  · simp [trunc, truncAdd]

private theorem trunc_mul (c n : ℕ) : trunc N p (c * n) = truncMul c (trunc N p n) := by
  ext
  · simp only [trunc, truncMul]
    rcases le_total n N with hn | hn
    · rw [min_eq_left hn]
    · rcases Nat.eq_zero_or_pos c with rfl | hc
      · simp
      · have := Nat.le_mul_of_pos_left n hc
        have := Nat.le_mul_of_pos_left N hc
        rw [min_eq_right hn]
        omega
  · simp [trunc, truncMul]

/-- The value of the sequence read off from a truncation. -/
private def truncOut (a : ℕ → Δ) (N p : ℕ) (x : Fin (N + 1) × ZMod p) : Δ :=
  if (x.1 : ℕ) < N then a x.1 else a (N + (x.2 - N).val)

private theorem truncOut_trunc (h : ∀ n, N ≤ n → a (n + p) = a n) (n : ℕ) :
    truncOut a N p (trunc N p n) = a n := by
  by_cases hn : n < N
  · simp [truncOut, trunc, min_eq_left hn.le, hn]
  · have hmin : min n N = N := min_eq_right (by omega)
    simp only [truncOut, trunc, hmin, lt_irrefl, ite_false]
    rw [← Nat.cast_sub (by omega), ZMod.val_natCast]
    exact (Nat.apply_eq_apply_add_sub_mod h (by omega)).symm

/-- For `2 ≤ k`, the automaton reading base-`k` digits that keeps the truncations of the value
read so far and of the current place value. -/
@[simps]
private def periodicDFAO (k : ℕ) (a : ℕ → Δ) (N p : ℕ) :
    DFAO (Fin k) ((Fin (N + 1) × ZMod p) × (Fin (N + 1) × ZMod p)) Δ where
  step q d := (truncAdd q.1 (truncMul d q.2), truncMul k q.2)
  start := (trunc N p 0, trunc N p 1)
  output q := truncOut a N p q.1

private theorem evalFrom_periodicDFAO (L : List ℕ) (hL : ∀ d ∈ L, d < k) (v P : ℕ) :
    (periodicDFAO k a N p).evalFrom (trunc N p v, trunc N p P) (L.map (Fin.ofNat k)) =
      (trunc N p (v + P * Nat.ofDigits k L), trunc N p (P * k ^ L.length)) := by
  induction L generalizing v P with
  | nil => simp
  | cons d L ih =>
    have hd : ((Fin.ofNat k d : Fin k) : ℕ) = d := by
      rw [Fin.val_ofNat, Nat.mod_eq_of_lt (hL d List.mem_cons_self)]
    have hstep : (periodicDFAO k a N p).step (trunc N p v, trunc N p P) (Fin.ofNat k d) =
        (trunc N p (v + d * P), trunc N p (k * P)) := by
      simp only [periodicDFAO_step, hd, trunc_add, trunc_mul]
    simp only [List.map_cons, DFAO.evalFrom_cons, hstep,
      ih (fun e he ↦ hL e (List.mem_cons_of_mem d he)), Nat.ofDigits_cons, List.length_cons,
      pow_succ]
    congr 2 <;> ring

/-- In base one, the automaton counting the letters of the unary word through truncations. -/
@[simps]
private def unaryPeriodicDFAO (a : ℕ → Δ) (N p : ℕ) : DFAO (Fin 1) (Fin (N + 1) × ZMod p) Δ where
  step q _ := truncAdd q (trunc N p 1)
  start := trunc N p 0
  output := truncOut a N p

private theorem evalFrom_unaryPeriodicDFAO (m v : ℕ) (d : Fin 1) :
    (unaryPeriodicDFAO a N p).evalFrom (trunc N p v) (List.replicate m d) = trunc N p (v + m) := by
  induction m generalizing v with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ, DFAO.evalFrom_cons]
    have hstep : (unaryPeriodicDFAO a N p).step (trunc N p v) d = trunc N p (v + 1) := by
      simp only [unaryPeriodicDFAO_step, trunc_add]
    rw [hstep, ih]
    congr 1
    omega

/-- **Eventually periodic sequences are automatic.** A sequence `a` with `a (n + p) = a n` for all
`n ≥ N`, for some period `p > 0`, is `k`-automatic in every base `k`. -/
theorem isAutomatic_of_eventually_periodic (hp : 0 < p) (h : ∀ n, N ≤ n → a (n + p) = a n) :
    IsAutomatic k a := by
  have : NeZero p := ⟨hp.ne'⟩
  obtain rfl | hk : k = 1 ∨ 2 ≤ k := by
    have := NeZero.ne k
    omega
  · convert (unaryPeriodicDFAO a N p).isAutomatic with n
    simp [DFAO.eval_eq_evalFrom, Nat.digits_one, evalFrom_unaryPeriodicDFAO, truncOut_trunc h]
  · convert (periodicDFAO k a N p).isAutomatic with n
    simp [DFAO.eval_eq_evalFrom, evalFrom_periodicDFAO _ (fun d hd ↦ Nat.digits_lt_base hk hd),
      Nat.ofDigits_digits, truncOut_trunc h]

end EventuallyPeriodic

/-! ### Checks -/

/-- The parity of `n` is `2`-automatic. -/
example : IsAutomatic 2 fun n : ℕ ↦ n % 2 :=
  isAutomatic_of_eventually_periodic (N := 0) (p := 2) two_pos fun n _ ↦ Nat.add_mod_right n 2

/-- The residue modulo `3` is `1`-automatic, read on the unary word. -/
example : IsAutomatic 1 fun n : ℕ ↦ n % 3 :=
  isAutomatic_of_eventually_periodic (N := 0) (p := 3) three_pos fun n _ ↦ Nat.add_mod_right n 3

/-- The identity sequence is not automatic in any base: it takes infinitely many values. -/
example : ¬ IsAutomatic k fun n : ℕ ↦ n := fun h ↦
  Set.infinite_range_of_injective (fun _ _ h ↦ h) h.finite_range

end TauCeti
