/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Polynomial.Div
import TauCeti.RingTheory.Perfect.Basic
import TauCeti.RingTheory.PowerSeries.Trunc

/-!
# Twisted Teichmüller lifts in equal characteristic

Let `S` be a perfect ring of characteristic `p` and `q = p ^ f` with `f ≠ 0`. In equal
characteristic the ramified Witt vectors of `S` over `𝔽_q⟦π⟧` are the power series `S⟦π⟧`, and a
polynomial `Q` over `S⟦π⟧` with `Q ≡ X ^ q` modulo `π` plays the role of a Frobenius lift. For
`a : S` the *`Q`-Teichmüller lift* `[a]_Q` is the `π`-adic limit of `Q_n(â_n)`, where `Q_n` is the
`n`-fold iterate of evaluation at `Q` and `â_n` is any lift of `a ^ (q ^ (-n))`.

The limit exists and is independent of the lifts by contraction: since `S⟦π⟧` has characteristic
`p`, `Q(x) - Q(y)` lies in `(x - y) ^ q S⟦π⟧ + π (x - y) S⟦π⟧`, so `x ≡ y` modulo `π ^ (i + 1)`
implies `Q(x) ≡ Q(y)` modulo `π ^ (i + 2)`. We define `[a]_Q` by its stabilized coefficients,
using the canonical constant lifts, and express the limit as the congruences
`[a]_Q ≡ Q_n(â_n)` modulo `π ^ (n + 1)` for arbitrary lifts.

The lift reduces to `a`, satisfies `Q([a]_Q) = [a ^ q]_Q`, and is the unique lift of the identity
with this property. It commutes with ring maps of perfect rings, and is additive when evaluation
at `Q` is, for instance for `Q = X ^ q + c π X`. For `Q = X ^ q` it is the constant lift; in general
it is not multiplicative.

Here `π` is the power series variable `PowerSeries.X`, while `Q` is a `Polynomial` over `S⟦X⟧`.

## Main definitions

* `TauCeti.twistedTeichmuller p f Q a`: the `Q`-Teichmüller lift `[a]_Q ∈ S⟦X⟧`.

## Main results

* `TauCeti.X_pow_succ_dvd_twistedTeichmuller_sub`: `[a]_Q ≡ Q_n(b)` modulo `X ^ (n + 1)` for every
  lift `b` of a `q ^ n`-th root of `a`; this is the limit formula.
* `TauCeti.eq_twistedTeichmuller_iff`: `[a]_Q` is characterized by these congruences.
* `TauCeti.constantCoeff_twistedTeichmuller`: `[a]_Q` reduces to `a` modulo `X`.
* `TauCeti.eval_twistedTeichmuller`: `Q([a]_Q) = [a ^ q]_Q`.
* `TauCeti.eq_twistedTeichmuller_of_eval`: a lift of the identity of `S` commuting with `Q` in
  this sense is `a ↦ [a]_Q`.
* `TauCeti.map_twistedTeichmuller`: naturality for ring maps of perfect rings.
* `TauCeti.twistedTeichmuller_add`: additivity for additive `Q`.
* `TauCeti.twistedTeichmuller_X_pow`: for `Q = X ^ q` the lift is the constant series.

## References

* L. Fargues and J.-M. Fontaine, *Courbes et fibrés vectoriels en théorie de Hodge `p`-adique*,
  Astérisque 406 (2018), Proposition 1.2.7 and Example 1.2.8, for the limit formula over a
  coefficient field of characteristic zero.
-/

public section

namespace TauCeti

open PowerSeries

section Reduction

variable {R : Type*} [CommSemiring R] {q : ℕ} {Q : Polynomial R⟦X⟧}

/-- If `Q ≡ X ^ q` modulo `X`, then modulo `X` evaluation at `Q` is the `q`-th power map. -/
theorem constantCoeff_eval (hQ : Q.map constantCoeff = Polynomial.X ^ q) (x : R⟦X⟧) :
    constantCoeff (Q.eval x) = constantCoeff x ^ q := by
  rw [← Polynomial.eval_map_apply, hQ]
  simp

/-- If `Q ≡ X ^ q` modulo `X`, then modulo `X` the `k`-fold iterate of evaluation at `Q` is the
`q ^ k`-th power map. -/
theorem constantCoeff_iterate_eval (hQ : Q.map constantCoeff = Polynomial.X ^ q) (k : ℕ)
    (x : R⟦X⟧) : constantCoeff ((Q.eval ·)^[k] x) = constantCoeff x ^ q ^ k := by
  induction k generalizing x with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply, ih, constantCoeff_eval hQ, ← pow_mul, pow_succ']

end Reduction

section Contraction

variable {S : Type*} [CommRing S] {p : ℕ} [Fact p.Prime] [CharP S p] {f : ℕ}
  {Q : Polynomial S⟦X⟧}

omit [Fact p.Prime] [CharP S p] in
/-- If `Q ≡ X ^ (p ^ f)` modulo `X`, every coefficient of `Q - X ^ (p ^ f)` is divisible by `X`. -/
private theorem X_dvd_coeff_sub_X_pow (hQ : Q.map constantCoeff = Polynomial.X ^ p ^ f) (e : ℕ) :
    X ∣ (Q - Polynomial.X ^ p ^ f).coeff e := by
  rw [X_dvd_iff, ← Polynomial.coeff_map, Polynomial.map_sub, hQ, Polynomial.map_pow,
    Polynomial.map_X, sub_self, Polynomial.coeff_zero]

/-- **Contraction.** If `Q ≡ X ^ (p ^ f)` modulo `X` with `f ≠ 0`, evaluation at `Q` improves an
`X`-adic congruence of positive order by one. -/
theorem X_pow_succ_dvd_eval_sub_eval (hf : f ≠ 0) (hQ : Q.map constantCoeff = Polynomial.X ^ p ^ f)
    {n : ℕ} {x y : S⟦X⟧} (h : X ^ (n + 1) ∣ x - y) :
    X ^ (n + 2) ∣ Q.eval x - Q.eval y := by
  have : CharP S⟦X⟧ p := charP_of_injective_ringHom C_injective p
  set P := Q - Polynomial.X ^ p ^ f
  have hsplit : Q.eval x - Q.eval y = (x - y) ^ p ^ f + (P.eval x - P.eval y) := by
    rw [sub_pow_char_pow]
    simp only [P, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
    ring
  rw [hsplit]
  refine dvd_add ?_ ?_
  · -- `(x - y) ^ q` is divisible by `X ^ ((n + 1) * q)` and `n + 2 ≤ (n + 1) * q` as `q ≥ 2`.
    have hq : 2 ≤ p ^ f := (Nat.one_lt_pow hf (Fact.out : p.Prime).one_lt)
    have h' : X ^ ((n + 1) * p ^ f) ∣ (x - y) ^ p ^ f := by
      rw [pow_mul]
      exact pow_dvd_pow_of_dvd h _
    exact (pow_dvd_pow (X : S⟦X⟧) (by nlinarith)).trans h'
  · -- Each term `cₑ (x ^ e - y ^ e)` of `P(x) - P(y)` has `X ∣ cₑ` and `x - y ∣ x ^ e - y ^ e`.
    rw [Polynomial.eval_eq_sum, Polynomial.eval_eq_sum, Polynomial.sum_def, Polynomial.sum_def,
      ← Finset.sum_sub_distrib, pow_succ']
    refine Finset.dvd_sum fun e _ ↦ ?_
    rw [← mul_sub]
    exact mul_dvd_mul (X_dvd_coeff_sub_X_pow hQ e) (h.trans (sub_dvd_pow_sub_pow x y e))

/-- Iterated contraction: lifts congruent modulo `X` stay congruent modulo `X ^ (k + 1)` under
`k`-fold evaluation at `Q`. -/
theorem X_pow_succ_dvd_iterate_eval_sub (hf : f ≠ 0)
    (hQ : Q.map constantCoeff = Polynomial.X ^ p ^ f) (k : ℕ) {x y : S⟦X⟧} (h : X ∣ x - y) :
    X ^ (k + 1) ∣ (Q.eval ·)^[k] x - (Q.eval ·)^[k] y := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    simp only [Function.iterate_succ_apply']
    exact X_pow_succ_dvd_eval_sub_eval hf hQ ih

end Contraction

section Lift

variable {S : Type*} [CommRing S] (p : ℕ) [Fact p.Prime] [CharP S p] [PerfectRing S p] (f : ℕ)

/-- The **`Q`-Teichmüller lift** `[a]_Q` of `a : S` to `S⟦X⟧`, for a perfect ring `S` of
characteristic `p` and a polynomial `Q` over `S⟦X⟧` with `Q ≡ X ^ (p ^ f)` modulo `X`. Its
`n`-th coefficient is that of `Q_n(â_n)`, where `Q_n` is the `n`-fold iterate of `x ↦ Q.eval x`
and `â_n` is the constant lift of the `(p ^ f) ^ n`-th root of `a`. When `f ≠ 0`,
`X_pow_succ_dvd_twistedTeichmuller_sub` shows that it is the `X`-adic limit of `Q_n(b_n)` for any
lifts `b_n` of these roots. -/
noncomputable def twistedTeichmuller (Q : Polynomial S⟦X⟧) (a : S) : S⟦X⟧ :=
  mk fun n ↦ coeff n ((Q.eval ·)^[n] (C ((iterateFrobeniusEquiv S p (f * n)).symm a)))

variable {p f} {Q : Polynomial S⟦X⟧}

/-- The constant lift of the `p ^ (f * n)`-th root of `a` lifts a `(p ^ f) ^ n`-th root of `a`. -/
private theorem constantCoeff_C_iterateFrobeniusEquiv_symm_pow (n : ℕ) (a : S) :
    constantCoeff (C ((iterateFrobeniusEquiv S p (f * n)).symm a)) ^ (p ^ f) ^ n = a := by
  rw [constantCoeff_C, ← pow_mul, iterateFrobeniusEquiv_symm_pow]

/-- For `k ≤ n`, iterating `n` times on a lift of a `(p ^ f) ^ n`-th root of `a` agrees modulo
`X ^ (k + 1)` with iterating `k` times on a lift of a `(p ^ f) ^ k`-th root of `a`. -/
private theorem X_pow_succ_dvd_iterate_eval_sub_of_le (hf : f ≠ 0)
    (hQ : Q.map constantCoeff = Polynomial.X ^ p ^ f) {a : S} {k n : ℕ} (hkn : k ≤ n)
    {b b' : S⟦X⟧} (hb : constantCoeff b ^ (p ^ f) ^ n = a)
    (hb' : constantCoeff b' ^ (p ^ f) ^ k = a) :
    X ^ (k + 1) ∣ (Q.eval ·)^[n] b - (Q.eval ·)^[k] b' := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkn
  rw [Function.iterate_add_apply]
  refine X_pow_succ_dvd_iterate_eval_sub hf hQ k (X_dvd_iff.2 ?_)
  rw [map_sub, sub_eq_zero, constantCoeff_iterate_eval hQ]
  refine (iterateFrobeniusEquiv S p (f * k)).injective ?_
  rw [iterateFrobeniusEquiv_def, iterateFrobeniusEquiv_def, pow_mul, hb', ← pow_mul, ← pow_add,
    add_comm, hb]

/-- The coefficients of `Q_n(b)` up to degree `n` are those of `[a]_Q`, for every lift `b` of a
`(p ^ f) ^ n`-th root of `a`. -/
theorem coeff_twistedTeichmuller (hf : f ≠ 0) (hQ : Q.map constantCoeff = Polynomial.X ^ p ^ f)
    {a : S} {k n : ℕ} (hkn : k ≤ n) {b : S⟦X⟧} (hb : constantCoeff b ^ (p ^ f) ^ n = a) :
    coeff k (twistedTeichmuller p f Q a) = coeff k ((Q.eval ·)^[n] b) := by
  have h := X_pow_succ_dvd_iterate_eval_sub_of_le hf hQ hkn hb (b' :=
    C ((iterateFrobeniusEquiv S p (f * k)).symm a))
    (constantCoeff_C_iterateFrobeniusEquiv_symm_pow k a)
  rw [X_pow_dvd_iff] at h
  have := h k (Nat.lt_succ_self k)
  rw [map_sub, sub_eq_zero] at this
  rw [twistedTeichmuller, coeff_mk, this]

/-- **Limit formula.** For every lift `b` of a `(p ^ f) ^ n`-th root of `a`, the iterate `Q_n(b)`
agrees with `[a]_Q` modulo `X ^ (n + 1)`. Thus `[a]_Q = lim_n Q_n(b_n)` `X`-adically, for any
choice of lifts `b_n`. -/
theorem X_pow_succ_dvd_twistedTeichmuller_sub (hf : f ≠ 0)
    (hQ : Q.map constantCoeff = Polynomial.X ^ p ^ f) {a : S} {n : ℕ} {b : S⟦X⟧}
    (hb : constantCoeff b ^ (p ^ f) ^ n = a) :
    X ^ (n + 1) ∣ twistedTeichmuller p f Q a - (Q.eval ·)^[n] b := by
  rw [X_pow_dvd_iff]
  intro k hk
  rw [map_sub, coeff_twistedTeichmuller hf hQ (Nat.lt_succ_iff.1 hk) hb, sub_self]

/-- `[a]_Q` is the unique power series which, for every `n`, agrees modulo `X ^ (n + 1)` with
`Q_n(b)` for some lift `b` of a `(p ^ f) ^ n`-th root of `a`. -/
theorem eq_twistedTeichmuller_iff (hf : f ≠ 0) (hQ : Q.map constantCoeff = Polynomial.X ^ p ^ f)
    {a : S} {y : S⟦X⟧} :
    y = twistedTeichmuller p f Q a ↔ ∀ n, ∃ b : S⟦X⟧, constantCoeff b ^ (p ^ f) ^ n = a ∧
      X ^ (n + 1) ∣ y - (Q.eval ·)^[n] b := by
  refine ⟨?_, fun h ↦ eq_of_forall_X_pow_dvd_sub fun n ↦ ?_⟩
  · rintro rfl n
    exact ⟨C ((iterateFrobeniusEquiv S p (f * n)).symm a),
      constantCoeff_C_iterateFrobeniusEquiv_symm_pow n a,
      X_pow_succ_dvd_twistedTeichmuller_sub hf hQ
        (constantCoeff_C_iterateFrobeniusEquiv_symm_pow n a)⟩
  · obtain ⟨b, hb, hy⟩ := h n
    simpa only [sub_sub_sub_cancel_right] using
      dvd_sub hy (X_pow_succ_dvd_twistedTeichmuller_sub hf hQ hb)

/-- The `Q`-Teichmüller lift reduces to `a` modulo `X`. -/
@[simp]
theorem constantCoeff_twistedTeichmuller (a : S) :
    constantCoeff (twistedTeichmuller p f Q a) = a := by
  simp [twistedTeichmuller, ← coeff_zero_eq_constantCoeff_apply]

/-- **The `Q`-equation.** Evaluation at `Q` sends `[a]_Q` to `[a ^ (p ^ f)]_Q`. -/
theorem eval_twistedTeichmuller (hf : f ≠ 0) (hQ : Q.map constantCoeff = Polynomial.X ^ p ^ f)
    (a : S) : Q.eval (twistedTeichmuller p f Q a) = twistedTeichmuller p f Q (a ^ p ^ f) := by
  refine (eq_twistedTeichmuller_iff hf hQ).2 fun n ↦ ?_
  -- Compare with `Q_n(Q(â_n)) = Q(Q_n(â_n))`, where `â_n` is the constant lift of the root of `a`.
  set c := C ((iterateFrobeniusEquiv S p (f * n)).symm a)
  have hc : constantCoeff c ^ (p ^ f) ^ n = a :=
    constantCoeff_C_iterateFrobeniusEquiv_symm_pow n a
  refine ⟨Q.eval c, by rw [constantCoeff_eval hQ, ← pow_mul, mul_comm, pow_mul, hc], ?_⟩
  rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
  exact (pow_dvd_pow X (Nat.le_succ _)).trans
    (X_pow_succ_dvd_eval_sub_eval hf hQ (X_pow_succ_dvd_twistedTeichmuller_sub hf hQ hc))

/-- **Uniqueness.** A lift `L` of the identity of `S` satisfying `Q(L(a)) = L(a ^ (p ^ f))` is the
`Q`-Teichmüller lift. -/
theorem eq_twistedTeichmuller_of_eval (hf : f ≠ 0)
    (hQ : Q.map constantCoeff = Polynomial.X ^ p ^ f) {L : S → S⟦X⟧}
    (hL : ∀ a, constantCoeff (L a) = a) (hLQ : ∀ a, Q.eval (L a) = L (a ^ p ^ f)) :
    L = twistedTeichmuller p f Q := by
  -- By induction, `L(a) = Q_n(L(a'))` for every `a'` with `a' ^ ((p ^ f) ^ n) = a`.
  have key (n : ℕ) (a' : S) : L (a' ^ (p ^ f) ^ n) = (Q.eval ·)^[n] (L a') := by
    induction n generalizing a' with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply, hLQ, ← ih]
      ring_nf
  funext a
  refine (eq_twistedTeichmuller_iff hf hQ).2 fun n ↦
    ⟨L ((iterateFrobeniusEquiv S p (f * n)).symm a),
      by rw [hL, ← pow_mul, iterateFrobeniusEquiv_symm_pow], ?_⟩
  rw [← key, ← pow_mul, iterateFrobeniusEquiv_symm_pow, sub_self]
  exact dvd_zero _

/-- **Naturality.** A ring map `g` of perfect rings of characteristic `p` carries `[a]_Q` to the
lift of `g a` for the image of `Q`. -/
@[simp]
theorem map_twistedTeichmuller {T : Type*} [CommRing T] [CharP T p] [PerfectRing T p]
    (g : S →+* T) (a : S) :
    map g (twistedTeichmuller p f Q a) = twistedTeichmuller p f (Q.map (map g)) (g a) := by
  have hroot (n : ℕ) : g ((iterateFrobeniusEquiv S p (f * n)).symm a) =
      (iterateFrobeniusEquiv T p (f * n)).symm (g a) :=
    (iterateFrobeniusEquiv T p (f * n)).injective <| by
      rw [iterateFrobeniusEquiv_def, iterateFrobeniusEquiv_def, ← map_pow,
        iterateFrobeniusEquiv_symm_pow, iterateFrobeniusEquiv_symm_pow]
  have hcomm : Function.Semiconj (map g) (Q.eval ·) ((Q.map (map g)).eval ·) := fun x ↦
    (Polynomial.eval_map_apply (map g) x).symm
  ext n
  simp only [twistedTeichmuller, coeff_map, coeff_mk]
  rw [← coeff_map, (hcomm.iterate_right n).eq, map_C, hroot]

/-- **Additivity.** If evaluation at `Q` is additive, so is the `Q`-Teichmüller lift. This holds
for `Q = X ^ (p ^ f) + c X` with any `c`. -/
theorem twistedTeichmuller_add (hadd : ∀ x y, Q.eval (x + y) = Q.eval x + Q.eval y) (a b : S) :
    twistedTeichmuller p f Q (a + b) = twistedTeichmuller p f Q a + twistedTeichmuller p f Q b := by
  -- Each coefficient is that of an iterate of the additive map `x ↦ Q.eval x` on an additive lift.
  have hiter (n : ℕ) (x y : S⟦X⟧) :
      (Q.eval ·)^[n] (x + y) = (Q.eval ·)^[n] x + (Q.eval ·)^[n] y :=
    iterate_map_add (AddMonoidHom.mk' (Q.eval ·) hadd) n x y
  ext n
  simp only [twistedTeichmuller, coeff_mk, map_add, hiter]

/-- For `Q = X ^ (p ^ f)` the `Q`-Teichmüller lift is the constant series `C a`. -/
@[simp]
theorem twistedTeichmuller_X_pow (a : S) :
    twistedTeichmuller p f (Polynomial.X ^ p ^ f) a = C a := by
  have heval : ((Polynomial.X ^ p ^ f : Polynomial S⟦X⟧).eval ·) = (· ^ p ^ f) := by
    funext x
    rw [Polynomial.eval_pow, Polynomial.eval_X]
  ext n
  rw [twistedTeichmuller, coeff_mk, heval, pow_iterate]
  dsimp only
  rw [← map_pow, ← pow_mul, iterateFrobeniusEquiv_symm_pow]

end Lift

end TauCeti
