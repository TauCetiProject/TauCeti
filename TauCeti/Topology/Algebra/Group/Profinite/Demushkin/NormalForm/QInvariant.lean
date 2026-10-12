/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.QInvariant
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# The `q`-invariant of the Demushkin normal forms

Labute's classification puts a Demushkin group of rank `n` with `q`-invariant `q` in one of three
normal forms, presented on `x₁, …, xₙ` by the relator words

* `x₁^q (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)`, for `q ≠ 2`;
* `x₁² x₂^{2^f} (x₂, x₃)(x₄, x₅) ⋯ (x_{n-1}, x_n)`, for `q = 2` and `n` odd, together with its
  level `f = ∞`, the word `x₁² (x₂, x₃)(x₄, x₅) ⋯ (x_{n-1}, x_n)`;
* `x₁^{2+a} (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)`, for `q = 2` and `n` even, `4 ∣ a`.

This file checks that the parameter `q` of a normal form is the `q`-invariant of the group it
presents: whenever such a presented group is a Demushkin group, `TauCeti.demushkinQ` of it is `q`
for the first word (`p^{v_p(q)}` in general, so `q` itself for `q = 0` or `q` a positive power of
`p`), and `2` for the dyadic words. The computation goes through the one-relator
abelianization structure theorem `TauCeti.presentedProP.oneRelatorAbelianizationEquiv`, in the form
`TauCeti.demushkinQ_presentedProP_eq_pow_valuation`: the exponent vector of the first word is
`q e₁`, that of the second is `2 e₁ + 2^f e₂ = 2 (e₁ + 2^{f-1} e₂)`, or `2 e₁` at level `f = ∞`,
and that of the third is
`(2 + a) e₁ + 2^f e₃ = (2 + a)(e₁ + c e₃)` with `2 + a = 2u` for the unit `u = 1 + a/2` of `ℤ₂`,
so the abelianizations are `ℤ_p^{n-1} × ℤ_p ⧸ (q)`, `ℤ₂^{n-1} × ℤ/2` and `ℤ₂^{n-1} × ℤ/2`. The
hypothesis `4 ∣ a` in the third word is Labute's normalisation `α ∈ 4ℤ₂`, and it is what makes
`1 + a/2` a unit: for `a ≡ 2 mod 4` and `f ≥ 2` the whole exponent vector is divisible by `4`, so
the `q`-invariant would be at least `4`. (For `f = 1` the coordinate `2` at `x₃` alone gives
`q`-invariant `2`, whatever `a` is.)

## Main results

* `TauCeti.freeProP.toAdd_exponentSum_demushkinWordNeTwo`,
  `TauCeti.freeProP.toAdd_exponentSum_demushkinWordTwoOdd`,
  `TauCeti.freeProP.toAdd_exponentSum_demushkinWordTwoOddTop`,
  `TauCeti.freeProP.toAdd_exponentSum_demushkinWordTwoEven`: the exponent vectors of the words on
  the free generators.
* `TauCeti.demushkinQ_presentedProP_demushkinWordNeTwo_eq_zero_iff`,
  `TauCeti.demushkinQ_presentedProP_demushkinWordNeTwo`,
  `TauCeti.demushkinQ_presentedProP_demushkinWordNeTwo_of_eq_pow`: the `q`-invariant of the
  `q ≠ 2` normal form vanishes exactly when `q = 0`, is `p^{v_p(q)}` for `q ≠ 0`, and is `q` when
  `q` is a positive power of `p`.
* `TauCeti.demushkinQ_presentedProP_demushkinWordTwoOdd`,
  `TauCeti.demushkinQ_presentedProP_demushkinWordTwoOddTop`,
  `TauCeti.demushkinQ_presentedProP_demushkinWordTwoEven`: the dyadic normal forms have
  `q`-invariant `2`.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, p. 106
  and Theorems 1–3.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Theorem 3.9.19.
-/

public section

namespace TauCeti

open Multiplicative

variable {p : ℕ} [Fact p.Prime] {n : ℕ}

/-! ### Exponent vectors of the normal-form words -/

namespace freeProP

variable (p)

/-- The exponent vector of the `q ≠ 2` word `x₁^q (x₁, x₂) ⋯ (x_{n-1}, x_n)` on the free generators
is `q e₁`. -/
theorem toAdd_exponentSum_demushkinWordNeTwo (q : ℕ) :
    (exponentSum p (Fin n) (demushkinWordNeTwo q n (freeProPGen p n))).toAdd =
      (q : ℤ_[p]) • (exponentSum p (Fin n) (freeProPGen p n 0)).toAdd := by
  simp [← Nat.cast_smul_eq_nsmul ℤ_[p]]

/-- The exponent vector of the `q = 2`, `n` odd word `x₁² x₂^{2^f} (x₂, x₃) ⋯ (x_{n-1}, x_n)` on
the free generators is `2 e₁ + 2^f e₂`. -/
theorem toAdd_exponentSum_demushkinWordTwoOdd (f : ℕ) :
    (exponentSum p (Fin n) (demushkinWordTwoOdd f n (freeProPGen p n))).toAdd =
      (2 : ℤ_[p]) • (exponentSum p (Fin n) (freeProPGen p n 0)).toAdd +
        (2 : ℤ_[p]) ^ f • (exponentSum p (Fin n) (freeProPGen p n 1)).toAdd := by
  simp [← Nat.cast_smul_eq_nsmul ℤ_[p]]

/-- The exponent vector of the `q = 2`, `n` odd word at level `f = ∞`,
`x₁² (x₂, x₃) ⋯ (x_{n-1}, x_n)`, on the free generators is `2 e₁`. -/
theorem toAdd_exponentSum_demushkinWordTwoOddTop :
    (exponentSum p (Fin n) (demushkinWordTwoOddTop n (freeProPGen p n))).toAdd =
      (2 : ℤ_[p]) • (exponentSum p (Fin n) (freeProPGen p n 0)).toAdd := by
  simp [← Nat.cast_smul_eq_nsmul ℤ_[p]]

/-- The exponent vector of the `q = 2`, `n` even word
`x₁^{2+a} (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)` on the free generators is
`(2 + a) e₁ + 2^f e₃`. -/
theorem toAdd_exponentSum_demushkinWordTwoEven (a f : ℕ) :
    (exponentSum p (Fin n) (demushkinWordTwoEven a f n (freeProPGen p n))).toAdd =
      (2 + (a : ℤ_[p])) • (exponentSum p (Fin n) (freeProPGen p n 0)).toAdd +
        (2 : ℤ_[p]) ^ f • (exponentSum p (Fin n) (freeProPGen p n 2)).toAdd := by
  simp [← Nat.cast_smul_eq_nsmul ℤ_[p]]

end freeProP

/-! ### The `q`-invariant of the normal forms -/

open freeProP

section NeTwo

variable {q : ℕ}

/-- **The `q`-invariant of the `q ≠ 2` normal form vanishes exactly when `q = 0`**: for `p ∣ q`,
if `⟨x₁, …, xₙ ∣ x₁^q (x₁, x₂) ⋯ (x_{n-1}, x_n)⟩` is a Demushkin group, its `q`-invariant is `0`
if and only if `q = 0`. -/
theorem demushkinQ_presentedProP_demushkinWordNeTwo_eq_zero_iff (hq : p ∣ q)
    (hG : IsDemushkin p (presentedProP p (Fin n) {demushkinWordNeTwo q n (freeProPGen p n)})) :
    demushkinQ hG = 0 ↔ q = 0 := by
  have hn : 0 < n := by simpa using hG.card_pos_presentedProP
  have hw : (exponentSum p (Fin n) (freeProPGen p n 0)).toAdd ⟨0, hn⟩ = 1 := by simp
  rw [demushkinQ_presentedProP_eq_zero_iff hw (toAdd_exponentSum_demushkinWordNeTwo p q) hG
    (map_dvd (Nat.castRingHom ℤ_[p]) hq), Nat.cast_eq_zero]

/-- **The `q`-invariant of the `q ≠ 2` normal form is `p^{v_p(q)}`**: for `p ∣ q` and `q ≠ 0`, if
`⟨x₁, …, xₙ ∣ x₁^q (x₁, x₂) ⋯ (x_{n-1}, x_n)⟩` is a Demushkin group, its `q`-invariant is
`p ^ padicValNat p q`. -/
@[simp]
theorem demushkinQ_presentedProP_demushkinWordNeTwo (hq : p ∣ q) (hq0 : q ≠ 0)
    (hG : IsDemushkin p (presentedProP p (Fin n) {demushkinWordNeTwo q n (freeProPGen p n)})) :
    demushkinQ hG = p ^ padicValNat p q := by
  have hn : 0 < n := by simpa using hG.card_pos_presentedProP
  have hw : (exponentSum p (Fin n) (freeProPGen p n 0)).toAdd ⟨0, hn⟩ = 1 := by simp
  rw [demushkinQ_presentedProP_eq_pow_valuation hw (toAdd_exponentSum_demushkinWordNeTwo p q) hG
    (map_dvd (Nat.castRingHom ℤ_[p]) hq) (Nat.cast_ne_zero.2 hq0), PadicInt.valuation_natCast]

/-- **The `q ≠ 2` normal form with parameter `q = p^f`, `f ≥ 1`, has `q`-invariant `q`**: if
`⟨x₁, …, xₙ ∣ x₁^q (x₁, x₂) ⋯ (x_{n-1}, x_n)⟩` is a Demushkin group, its `q`-invariant is `q`. -/
theorem demushkinQ_presentedProP_demushkinWordNeTwo_of_eq_pow {f : ℕ} (hq : q = p ^ f) (hf : 0 < f)
    (hG : IsDemushkin p (presentedProP p (Fin n) {demushkinWordNeTwo q n (freeProPGen p n)})) :
    demushkinQ hG = q := by
  subst hq
  rw [demushkinQ_presentedProP_demushkinWordNeTwo (dvd_pow_self p hf.ne')
    (pow_ne_zero f (Fact.out : p.Prime).ne_zero) hG, padicValNat.prime_pow]

end NeTwo

section Two

variable {f : ℕ}

/-- **The `q = 2`, `n` odd normal form has `q`-invariant `2`**: for `f ≥ 1`, if
`⟨x₁, …, xₙ ∣ x₁² x₂^{2^f} (x₂, x₃) ⋯ (x_{n-1}, x_n)⟩` is a Demushkin group, its `q`-invariant is
`2`. -/
@[simp]
theorem demushkinQ_presentedProP_demushkinWordTwoOdd (hf : 0 < f)
    (hG : IsDemushkin 2 (presentedProP 2 (Fin n) {demushkinWordTwoOdd f n (freeProPGen 2 n)})) :
    demushkinQ hG = 2 := by
  have hn : 0 < n := by simpa using hG.card_pos_presentedProP
  set e : ℕ → Fin n → ℤ_[2] := fun i ↦ (exponentSum 2 (Fin n) (freeProPGen 2 n i)).toAdd with he
  -- The exponent vector is `2 (e₁ + 2^{f-1} e₂)`, and the second factor is `1` at `x₁`.
  have hw : (e 0 + (2 : ℤ_[2]) ^ (f - 1) • e 1) ⟨0, hn⟩ = 1 := by
    simp [he]
  have hr : (exponentSum 2 (Fin n) (demushkinWordTwoOdd f n (freeProPGen 2 n))).toAdd =
      (2 : ℤ_[2]) • (e 0 + (2 : ℤ_[2]) ^ (f - 1) • e 1) := by
    rw [toAdd_exponentSum_demushkinWordTwoOdd, smul_add, smul_smul, ← pow_succ',
      Nat.sub_add_cancel hf]
  have h2 : (2 : ℤ_[2]).valuation = 1 := PadicInt.valuation_p
  rw [demushkinQ_presentedProP_eq_pow_valuation hw hr hG (dvd_refl _) two_ne_zero, h2, pow_one]

/-- **The `q = 2`, `n` odd normal form at level `f = ∞` has `q`-invariant `2`**: if
`⟨x₁, …, xₙ ∣ x₁² (x₂, x₃) ⋯ (x_{n-1}, x_n)⟩` is a Demushkin group, its `q`-invariant is `2`. -/
@[simp]
theorem demushkinQ_presentedProP_demushkinWordTwoOddTop
    (hG : IsDemushkin 2 (presentedProP 2 (Fin n) {demushkinWordTwoOddTop n (freeProPGen 2 n)})) :
    demushkinQ hG = 2 := by
  have hn : 0 < n := by simpa using hG.card_pos_presentedProP
  have hw : (exponentSum 2 (Fin n) (freeProPGen 2 n 0)).toAdd ⟨0, hn⟩ = 1 := by simp
  have h2 : (2 : ℤ_[2]).valuation = 1 := PadicInt.valuation_p
  rw [demushkinQ_presentedProP_eq_pow_valuation hw (toAdd_exponentSum_demushkinWordTwoOddTop 2) hG
    (dvd_refl _) two_ne_zero, h2, pow_one]

/-- **The `q = 2`, `n` even normal form has `q`-invariant `2`**: for `4 ∣ a` and `f ≥ 1`, if
`⟨x₁, …, xₙ ∣ x₁^{2+a} (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)⟩` is a Demushkin group, its
`q`-invariant is `2`. The hypothesis `4 ∣ a` makes `2 + a` exactly divisible by `2`. -/
@[simp]
theorem demushkinQ_presentedProP_demushkinWordTwoEven {a : ℕ} (ha : 4 ∣ a) (hf : 0 < f)
    (hG : IsDemushkin 2
      (presentedProP 2 (Fin n) {demushkinWordTwoEven a f n (freeProPGen 2 n)})) :
    demushkinQ hG = 2 := by
  have hn : 0 < n := by simpa using hG.card_pos_presentedProP
  obtain ⟨b, rfl⟩ := ha
  -- `2 + 4b = 2u` for the unit `u = 1 + 2b` of `ℤ₂`.
  obtain ⟨u, hu⟩ : IsUnit (1 + 2 * (b : ℤ_[2])) :=
    PadicInt.isUnit_one_add_of_dvd (by rw [Nat.cast_ofNat]; exact dvd_mul_right 2 _)
  have hq : (2 + ((4 * b : ℕ) : ℤ_[2])) = 2 * u := by
    rw [hu]; push_cast; ring
  set e : ℕ → Fin n → ℤ_[2] := fun i ↦ (exponentSum 2 (Fin n) (freeProPGen 2 n i)).toAdd with he
  -- The exponent vector is `(2 + 4b) (e₁ + 2^{f-1} u⁻¹ e₃)`, and the second factor is `1` at `x₁`.
  have hw : (e 0 + ((2 : ℤ_[2]) ^ (f - 1) * ↑u⁻¹) • e 2) ⟨0, hn⟩ = 1 := by
    simp [he]
  have hr : (exponentSum 2 (Fin n) (demushkinWordTwoEven (4 * b) f n (freeProPGen 2 n))).toAdd =
      (2 + ((4 * b : ℕ) : ℤ_[2])) • (e 0 + ((2 : ℤ_[2]) ^ (f - 1) * ↑u⁻¹) • e 2) := by
    rw [toAdd_exponentSum_demushkinWordTwoEven, smul_add, smul_smul, hq]
    congr 2
    calc (2 : ℤ_[2]) ^ f = 2 * 2 ^ (f - 1) * (u * ↑u⁻¹) := by
          rw [Units.mul_inv, mul_one, ← pow_succ', Nat.sub_add_cancel hf]
      _ = 2 * ↑u * (2 ^ (f - 1) * ↑u⁻¹) := by ring
  have hval : (2 * (u : ℤ_[2])).valuation = 1 := by
    rw [PadicInt.valuation_mul two_ne_zero u.ne_zero, PadicInt.valuation_eq_zero_of_isUnit u.isUnit,
      add_zero]
    exact PadicInt.valuation_p
  rw [demushkinQ_presentedProP_eq_pow_valuation hw hr hG (by rw [hq]; exact dvd_mul_right _ _)
    (by rw [hq]; exact mul_ne_zero two_ne_zero u.ne_zero), hq, hval, pow_one]

end Two

end TauCeti
