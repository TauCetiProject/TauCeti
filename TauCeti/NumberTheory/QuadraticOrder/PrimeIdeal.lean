/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Tactic.LinearCombination

/-!
# Primes above a rational prime in an integral quadratic algebra

Let `ℤ[ω] = QuadraticAlgebra ℤ a b`, so `ω² = a + b ω`: the quadratic orders `ℤ[√d]` and
`ℤ[(1 + √d)/2]` are of this shape. Here `f = X² - b X - a` denotes the minimal polynomial of `ω`
and `p` a rational prime. This file describes the ideals of `ℤ[ω]` above `p` by explicit
generators, following the Dedekind–Kummer recipe:

* if `r` is a root of `f` modulo `p`, then `𝔭_r = (p, ω - r)` is the kernel of the evaluation
  `ℤ[ω] → ℤ/p` sending `ω ↦ r`. It is a maximal ideal with residue field of size `p`
  (`isMaximal_span_natCast_omega_sub`, `card_quotient_span_natCast_omega_sub`), and
  `x ∈ 𝔭_r ↔ p ∣ x.re + x.im r`;
* the second root is `b - r`, and the product formula
  `(p, ω - r) (p, ω - (b - r)) = (p)` holds exactly when `p` does not divide both `f'(r) = 2r - b`
  and `f(r) / p` (`span_natCast_omega_sub_mul_span_natCast_omega_sub_eq_iff`). This is the
  quadratic case of Dedekind's criterion, stated as an identity of ideals of the order `ℤ[ω]`
  itself, maximal or not. In the maximal order of a quadratic field it holds at every prime; in
  `ℤ[√d]` with `d ≡ 1 (mod 4)`, an order of conductor `2`, it fails at `p = 2`
  (`span_two_omega_sub_one_sq_ne_span_two`);
* every prime of `ℤ[ω]` containing `p` is `𝔭_r` or `𝔭_(b - r)` (`eq_or_eq_of_natCast_mem`),
  whether or not the criterion holds; the two coincide exactly when `p ∣ 2r - b`, that is, when
  `p` divides the discriminant `b² + 4a` of `f`
  (`span_natCast_omega_sub_eq_span_natCast_omega_sub_iff`);
* if `f` has no root modulo `p`, then `(p)` itself is maximal, so `p` is inert
  (`isMaximal_span_natCast_iff`), and conversely;
* together, the primes of `ℤ[ω]` above `p` are exactly `(p)` when `f` has no root modulo `p`, and
  the ideals `𝔭_r` otherwise (`isPrime_and_natCast_mem_iff`).

For a monogenic order inside a number field, Mathlib's Kummer–Dedekind theorem
(`KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk`) describes the primes of
the ring of integers above a prime not dividing the conductor, and
`TauCeti.NumberField.IntegralPrimitiveElement.not_dvd_index_iff` decides when that hypothesis
holds. The statements here need neither a Dedekind domain nor an ambient field.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §5.B and §7.D.
* J. Neukirch, *Algebraic Number Theory*, Chapter I, Proposition 8.3.
-/

public section

namespace QuadraticAlgebra

variable {a b : ℤ} {p : ℕ} {r : ℤ}

/-- An integer root `r` of `X² - b X - a` modulo `p`, as a root in `ℤ/p` of the defining relation
of `QuadraticAlgebra ℤ a b`. -/
private theorem intCast_mul_self_of_dvd (hr : (p : ℤ) ∣ r ^ 2 - b * r - a) :
    (r : ZMod p) * r = a • (1 : ZMod p) + b • (r : ZMod p) := by
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hr
  push_cast at h
  rw [zsmul_eq_mul, zsmul_eq_mul, mul_one]
  linear_combination h

/-- The evaluation `ℤ[ω] → ℤ/p`, `ω ↦ r`, at a root `r` of `X² - b X - a` modulo `p`. -/
private noncomputable def evalRoot (hr : (p : ℤ) ∣ r ^ 2 - b * r - a) :
    QuadraticAlgebra ℤ a b →+* ZMod p :=
  (lift ⟨(r : ZMod p), intCast_mul_self_of_dvd hr⟩ : QuadraticAlgebra ℤ a b →ₐ[ℤ] ZMod p)

private theorem evalRoot_apply (hr : (p : ℤ) ∣ r ^ 2 - b * r - a) (x : QuadraticAlgebra ℤ a b) :
    evalRoot hr x = ((x.re + x.im * r : ℤ) : ZMod p) := by
  simp [evalRoot, zsmul_eq_mul]

private theorem evalRoot_surjective (hr : (p : ℤ) ∣ r ^ 2 - b * r - a) :
    Function.Surjective (evalRoot hr) := by
  intro z
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective z
  exact ⟨n, by simp⟩

private theorem ker_evalRoot (hr : (p : ℤ) ∣ r ^ 2 - b * r - a) :
    RingHom.ker (evalRoot hr) =
      Ideal.span {(p : QuadraticAlgebra ℤ a b), ω - (r : QuadraticAlgebra ℤ a b)} := by
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker, evalRoot_apply, ZMod.intCast_zmod_eq_zero_iff_dvd] at hx
    obtain ⟨k, hk⟩ := hx
    refine Ideal.mem_span_pair.mpr ⟨k, x.im, ?_⟩
    ext
    · simp only [re_add, re_mul, re_natCast, im_natCast, re_intCast, im_intCast, re_sub, im_sub,
        re_omega, im_omega]
      linear_combination -hk
    · simp
  · rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨?_, ?_⟩ <;> simp [RingHom.mem_ker, evalRoot_apply]

/-- **Membership in `(p, ω - r)`.** For a root `r` of `X² - b X - a` modulo `p`, an element
`x` of `ℤ[ω]` lies in `(p, ω - r)` exactly when `p ∣ x.re + x.im r`, that is, when `x` vanishes
under `ω ↦ r` modulo `p`. -/
@[simp]
theorem mem_span_natCast_omega_sub_iff (hr : (p : ℤ) ∣ r ^ 2 - b * r - a)
    {x : QuadraticAlgebra ℤ a b} :
    x ∈ Ideal.span {(p : QuadraticAlgebra ℤ a b), ω - (r : QuadraticAlgebra ℤ a b)} ↔
      (p : ℤ) ∣ x.re + x.im * r := by
  rw [← ker_evalRoot hr, RingHom.mem_ker, evalRoot_apply,
    ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- **The norm of `(p, ω - r)` is `p`.** For a root `r` of `X² - b X - a` modulo `p`, the
residue ring of `(p, ω - r)` is `ℤ/p`, so its `Nat.card` is `p`. For `p ≠ 0` this says that it
has exactly `p` elements; for `p = 0` the residue ring is `ℤ`, which is infinite. -/
@[simp]
theorem card_quotient_span_natCast_omega_sub (hr : (p : ℤ) ∣ r ^ 2 - b * r - a) :
    Nat.card (QuadraticAlgebra ℤ a b ⧸
      Ideal.span {(p : QuadraticAlgebra ℤ a b), ω - (r : QuadraticAlgebra ℤ a b)}) = p := by
  rw [← ker_evalRoot hr, Nat.card_congr
    (RingHom.quotientKerEquivOfSurjective (evalRoot_surjective hr)).toEquiv, Nat.card_zmod]

/-- **Two roots give the same ideal iff they agree modulo `p`.** For a root `r` of
`X² - b X - a` modulo `p`, the ideals `(p, ω - s)` and `(p, ω - r)` coincide exactly when
`s ≡ r (mod p)`. When `p` is prime these ideals are the primes above `p`
(`isMaximal_span_natCast_omega_sub`). -/
theorem span_natCast_omega_sub_eq_iff (hr : (p : ℤ) ∣ r ^ 2 - b * r - a) {s : ℤ} :
    Ideal.span {(p : QuadraticAlgebra ℤ a b), ω - (s : QuadraticAlgebra ℤ a b)} =
        Ideal.span {(p : QuadraticAlgebra ℤ a b), ω - (r : QuadraticAlgebra ℤ a b)} ↔
      (p : ℤ) ∣ r - s := by
  constructor
  · intro h
    have hs : ω - (s : QuadraticAlgebra ℤ a b) ∈
        Ideal.span {(p : QuadraticAlgebra ℤ a b), ω - (r : QuadraticAlgebra ℤ a b)} :=
      h ▸ Ideal.subset_span (by simp)
    rw [mem_span_natCast_omega_sub_iff hr] at hs
    convert hs using 1
    simp only [re_sub, re_omega, re_intCast, im_sub, im_omega, im_intCast, sub_zero, Int.cast_id]
    ring
  · rintro ⟨k, hk⟩
    have key : ω - (s : QuadraticAlgebra ℤ a b) =
        (k : QuadraticAlgebra ℤ a b) * (p : QuadraticAlgebra ℤ a b) +
          (ω - (r : QuadraticAlgebra ℤ a b)) := by
      have : ((r - s : ℤ) : QuadraticAlgebra ℤ a b) = ((p * k : ℤ) : QuadraticAlgebra ℤ a b) := by
        rw [hk]
      push_cast at this
      linear_combination this
    rw [key, Ideal.span_pair_mul_left_add]

/-- The second root: `(ω - r) (ω - (b - r)) = -(r² - b r - a)` in `ℤ[ω]`, written as `-p m` when
`r² - b r - a = p m`. -/
private theorem omega_sub_mul_omega_sub {m : ℤ} (hm : r ^ 2 - b * r - a = p * m) :
    (ω - (r : QuadraticAlgebra ℤ a b)) * (ω - ((b - r : ℤ) : QuadraticAlgebra ℤ a b)) =
      -((p : QuadraticAlgebra ℤ a b) * (m : QuadraticAlgebra ℤ a b)) := by
  have h : ((r ^ 2 - b * r - a : ℤ) : QuadraticAlgebra ℤ a b) = ((p * m : ℤ) : _) := by rw [hm]
  push_cast at h
  rw [← h]
  ext <;> simp [sq] <;> ring

/-- `(p : ℤ[ω])` is cancellable: `p z = p` forces `z = 1`. -/
private theorem eq_one_of_natCast_mul_eq (hp : p ≠ 0) {z : QuadraticAlgebra ℤ a b}
    (h : (p : QuadraticAlgebra ℤ a b) * z = p) : z = 1 := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp
  have hre := congrArg re h
  have him := congrArg im h
  simp only [re_mul, im_mul, re_natCast, im_natCast, zero_mul, mul_zero, add_zero] at hre him
  ext
  · simpa using mul_left_cancel₀ hp0 (hre.trans (mul_one _).symm)
  · simpa using (mul_eq_zero.mp him).resolve_left hp0

variable [Fact p.Prime]

/-- **The prime `(p, ω - r)`.** For a root `r` of `X² - b X - a` modulo `p`, the ideal
`(p, ω - r)` of `ℤ[ω]` is maximal. -/
theorem isMaximal_span_natCast_omega_sub (hr : (p : ℤ) ∣ r ^ 2 - b * r - a) :
    (Ideal.span {(p : QuadraticAlgebra ℤ a b), ω - (r : QuadraticAlgebra ℤ a b)}).IsMaximal := by
  rw [← ker_evalRoot hr]
  exact RingHom.ker_isMaximal_of_surjective _ (evalRoot_surjective hr)

/-- **Dedekind's criterion for a quadratic order.** Let `r` be a root of `X² - b X - a` modulo
`p`, so that `b - r` is the second root. Then `p` factors as `(p) = (p, ω - r) (p, ω - (b - r))`
in `ℤ[ω]` if and only if `p` does not divide both the derivative `2r - b` and the quotient
`(r² - b r - a)/p`, that is, unless `p ∣ 2r - b` and `p² ∣ r² - b r - a`. -/
theorem span_natCast_omega_sub_mul_span_natCast_omega_sub_eq_iff
    (hr : (p : ℤ) ∣ r ^ 2 - b * r - a) :
    Ideal.span {(p : QuadraticAlgebra ℤ a b), ω - (r : QuadraticAlgebra ℤ a b)} *
        Ideal.span {(p : QuadraticAlgebra ℤ a b), ω - ((b - r : ℤ) : QuadraticAlgebra ℤ a b)} =
        Ideal.span {(p : QuadraticAlgebra ℤ a b)} ↔
      ¬ ((p : ℤ) ∣ 2 * r - b ∧ (p : ℤ) ^ 2 ∣ r ^ 2 - b * r - a) := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  obtain ⟨m, hm⟩ := hr
  have hkey := omega_sub_mul_omega_sub (a := a) (b := b) hm
  have hsq : (p : ℤ) ^ 2 ∣ r ^ 2 - b * r - a ↔ (p : ℤ) ∣ m := by
    rw [hm, sq, mul_dvd_mul_iff_left hp0]
  rw [hsq]
  set P : QuadraticAlgebra ℤ a b := (p : QuadraticAlgebra ℤ a b)
  set R : QuadraticAlgebra ℤ a b := (r : QuadraticAlgebra ℤ a b)
  set R' : QuadraticAlgebra ℤ a b := ((b - r : ℤ) : QuadraticAlgebra ℤ a b) with hR'
  set M : QuadraticAlgebra ℤ a b := (m : QuadraticAlgebra ℤ a b)
  set 𝔭 := Ideal.span {P, ω - R}
  set 𝔮 := Ideal.span {P, ω - R'}
  have hP𝔭 : P ∈ 𝔭 := Ideal.subset_span (by simp)
  have hP𝔮 : P ∈ 𝔮 := Ideal.subset_span (by simp)
  have hω𝔭 : ω - R ∈ 𝔭 := Ideal.subset_span (by simp)
  have hω𝔮 : ω - R' ∈ 𝔮 := Ideal.subset_span (by simp)
  -- The product is always contained in `(p)`: the only product of generators not visibly a
  -- multiple of `p` is `(ω - r)(ω - (b - r)) = -p m`.
  have hle : 𝔭 * 𝔮 ≤ Ideal.span {P} := by
    have hP := Ideal.mem_span_singleton_self P
    refine (Ideal.span_pair_mul_span_pair P (ω - R) P (ω - R')).le.trans ?_
    simp only [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    refine ⟨Ideal.mul_mem_right _ _ hP, Ideal.mul_mem_right _ _ hP, Ideal.mul_mem_left _ _ hP, ?_⟩
    rw [hkey]
    exact neg_mem (Ideal.mul_mem_right _ _ hP)
  constructor
  · -- If `p ∣ 2r - b` and `p ∣ m`, then `𝔭 = 𝔮` and `𝔭² ≤ p 𝔭`, which cannot contain `p`.
    rintro h ⟨⟨t, ht⟩, hmp⟩
    have h𝔮 : 𝔮 = 𝔭 :=
      (span_natCast_omega_sub_eq_iff ⟨m, hm⟩).mpr ⟨t, by linear_combination ht⟩
    have hM𝔭 : M ∈ 𝔭 := (mem_span_natCast_omega_sub_iff ⟨m, hm⟩).mpr (by simpa [M] using hmp)
    have hR'eq : R' = R - P * (t : QuadraticAlgebra ℤ a b) := by
      have h' : ((2 * r - b : ℤ) : QuadraticAlgebra ℤ a b) = ((p * t : ℤ) : _) := by rw [ht]
      simp only [hR', P, R]
      push_cast at h' ⊢
      linear_combination -h'
    have hsq' : (ω - R) * (ω - R) =
        P * (-(t : QuadraticAlgebra ℤ a b) * (ω - R) - M) := by
      rw [hR'eq] at hkey
      linear_combination hkey
    have hle' : 𝔭 * 𝔭 ≤ Ideal.span {P} * 𝔭 := by
      have hP : ∀ x ∈ 𝔭, P * x ∈ Ideal.span {P} * 𝔭 :=
        fun x hx => Ideal.mul_mem_mul (Ideal.mem_span_singleton_self P) hx
      refine (Ideal.span_pair_mul_span_pair P (ω - R) P (ω - R)).le.trans ?_
      simp only [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
      refine ⟨hP _ hP𝔭, hP _ hω𝔭, mul_comm P (ω - R) ▸ hP _ hω𝔭, ?_⟩
      rw [hsq']
      exact hP _ (sub_mem (Ideal.mul_mem_left _ _ hω𝔭) hM𝔭)
    rw [h𝔮] at h
    obtain ⟨z, hz, hPz⟩ :=
      Ideal.mem_span_singleton_mul.mp (hle' (h ▸ Ideal.mem_span_singleton_self P))
    exact (isMaximal_span_natCast_omega_sub ⟨m, hm⟩).ne_top
      ((Ideal.eq_top_iff_one _).mpr
        (eq_one_of_natCast_mul_eq (Fact.out : p.Prime).ne_zero hPz ▸ hz))
  · -- Otherwise `2r - b` or `m` is coprime to `p`, and a Bézout relation writes `p` as a
    -- combination of products of generators.
    intro h
    refine le_antisymm hle ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
    have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
    rcases not_and_or.mp h with hs | hmp
    · obtain ⟨u, v, huv⟩ := (hpr.coprime_iff_not_dvd).mpr hs
      have huv' : ((u * p + v * (2 * r - b) : ℤ) : QuadraticAlgebra ℤ a b) = 1 := by
        rw [huv, Int.cast_one]
      push_cast at huv'
      have hP : P = (u : QuadraticAlgebra ℤ a b) * (P * P) + (v : QuadraticAlgebra ℤ a b) *
          (P * (ω - R')) - (v : QuadraticAlgebra ℤ a b) * ((ω - R) * P) := by
        rw [hR']
        push_cast
        linear_combination (-P) * huv'
      rw [hP]
      exact sub_mem (add_mem (Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul hP𝔭 hP𝔮))
        (Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul hP𝔭 hω𝔮)))
        (Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul hω𝔭 hP𝔮))
    · obtain ⟨u, v, huv⟩ := (hpr.coprime_iff_not_dvd).mpr hmp
      have huv' : ((u * p + v * m : ℤ) : QuadraticAlgebra ℤ a b) = 1 := by
        rw [huv, Int.cast_one]
      push_cast at huv'
      have hP : P = (u : QuadraticAlgebra ℤ a b) * (P * P) -
          (v : QuadraticAlgebra ℤ a b) * ((ω - R) * (ω - R')) := by
        linear_combination (-P) * huv' + v * hkey
      rw [hP]
      exact sub_mem (Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul hP𝔭 hP𝔮))
        (Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul hω𝔭 hω𝔮))

/-- **The ramified case of Dedekind's criterion.** If `r` is a double root of `X² - b X - a`
modulo `p` (that is, `p ∣ 2r - b`), then `(p) = (p, ω - r)²` exactly when
`p² ∤ r² - b r - a`. -/
theorem span_natCast_omega_sub_sq_eq_iff (hr : (p : ℤ) ∣ r ^ 2 - b * r - a)
    (hs : (p : ℤ) ∣ 2 * r - b) :
    Ideal.span {(p : QuadraticAlgebra ℤ a b), ω - (r : QuadraticAlgebra ℤ a b)} ^ 2 =
        Ideal.span {(p : QuadraticAlgebra ℤ a b)} ↔
      ¬ (p : ℤ) ^ 2 ∣ r ^ 2 - b * r - a := by
  have h𝔮 : Ideal.span {(p : QuadraticAlgebra ℤ a b), ω - ((b - r : ℤ) : QuadraticAlgebra ℤ a b)} =
      Ideal.span {(p : QuadraticAlgebra ℤ a b), ω - (r : QuadraticAlgebra ℤ a b)} :=
    (span_natCast_omega_sub_eq_iff hr).mpr (by convert hs using 1; ring)
  have h := span_natCast_omega_sub_mul_span_natCast_omega_sub_eq_iff hr
  rw [h𝔮] at h
  rw [sq, h]
  simp [hs]

/-- **Dedekind's criterion fails at the conductor.** For `d ≡ 1 (mod 4)`, the order `ℤ[√d]` has
conductor `2` in `ℤ[(1 + √d)/2]`, and Dedekind's criterion fails at `2`: the maximal ideal
`(2, √d - 1)` above `2` satisfies `(2, √d - 1)² ≠ (2)`. -/
theorem span_two_omega_sub_one_sq_ne_span_two {d : ℤ} (hd4 : d % 4 = 1) :
    Ideal.span {(2 : QuadraticAlgebra ℤ d 0), ω - 1} ^ 2 ≠ Ideal.span {2} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := span_natCast_omega_sub_sq_eq_iff (p := 2) (a := d) (b := 0) (r := 1)
    (by norm_num; omega) (by norm_num)
  simp only [Nat.cast_ofNat, Int.cast_one] at h
  rw [Ne, h, not_not]
  norm_num
  omega

/-- **The primes above a split or ramified `p`.** If `r` is a root of `X² - b X - a` modulo `p`,
every prime ideal of `ℤ[ω]` containing `p` is `(p, ω - r)` or `(p, ω - (b - r))`. This needs no
Dedekind criterion, so it also holds at primes dividing the conductor of a nonmaximal order. -/
theorem eq_or_eq_of_natCast_mem (hr : (p : ℤ) ∣ r ^ 2 - b * r - a)
    {P : Ideal (QuadraticAlgebra ℤ a b)} [P.IsPrime] (hP : (p : QuadraticAlgebra ℤ a b) ∈ P) :
    P = Ideal.span {(p : QuadraticAlgebra ℤ a b), ω - (r : QuadraticAlgebra ℤ a b)} ∨
      P = Ideal.span {(p : QuadraticAlgebra ℤ a b),
        ω - ((b - r : ℤ) : QuadraticAlgebra ℤ a b)} := by
  have hr' : (p : ℤ) ∣ (b - r) ^ 2 - b * (b - r) - a := by
    convert hr using 1; ring
  -- `(ω - r)(ω - (b - r)) = -p m` lies in `P`, so one factor does, and then so does its root ideal.
  have hle : ∀ s : ℤ, ω - (s : QuadraticAlgebra ℤ a b) ∈ P →
      Ideal.span {(p : QuadraticAlgebra ℤ a b), ω - (s : QuadraticAlgebra ℤ a b)} ≤ P :=
    fun s hs => by
      rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨hP, hs⟩
  obtain ⟨m, hm⟩ := hr
  have hprod : (ω - (r : QuadraticAlgebra ℤ a b)) *
      (ω - ((b - r : ℤ) : QuadraticAlgebra ℤ a b)) ∈ P := by
    rw [omega_sub_mul_omega_sub hm]
    exact neg_mem (Ideal.mul_mem_right _ P hP)
  rcases Ideal.IsPrime.mem_or_mem inferInstance hprod with h | h
  · exact Or.inl ((isMaximal_span_natCast_omega_sub ⟨m, hm⟩).eq_of_le Ideal.IsPrime.ne_top'
      (hle _ h)).symm
  · exact Or.inr ((isMaximal_span_natCast_omega_sub hr').eq_of_le Ideal.IsPrime.ne_top'
      (hle _ h)).symm

/-- **The inert case.** The ideal `(p)` of `ℤ[ω]` is maximal, that is, `p` is inert, exactly when
`X² - b X - a` has no root modulo `p`. -/
theorem isMaximal_span_natCast_iff :
    (Ideal.span {(p : QuadraticAlgebra ℤ a b)}).IsMaximal ↔
      ∀ r : ℤ, ¬ (p : ℤ) ∣ r ^ 2 - b * r - a := by
  have hmem : ∀ x : QuadraticAlgebra ℤ a b, x ∈ Ideal.span {(p : QuadraticAlgebra ℤ a b)} ↔
      (p : ℤ) ∣ x.re ∧ (p : ℤ) ∣ x.im := by
    intro x
    rw [Ideal.mem_span_singleton, ← map_natCast (algebraMap ℤ (QuadraticAlgebra ℤ a b)) p,
      algebraMap_dvd_iff]
  constructor
  · -- A root `r` gives the proper ideal `(p, ω - r) ⊇ (p)`, which `ω - r ∉ (p)` separates.
    intro hmax r hr
    have heq := hmax.eq_of_le (isMaximal_span_natCast_omega_sub hr).ne_top
      (Ideal.span_mono (by simp))
    have hω : ω - (r : QuadraticAlgebra ℤ a b) ∈ Ideal.span {(p : QuadraticAlgebra ℤ a b)} :=
      heq ▸ Ideal.subset_span (by simp)
    have h1 := ((hmem _).mp hω).2
    simp only [im_sub, im_omega, im_intCast, sub_zero] at h1
    exact (Fact.out : p.Prime).not_dvd_one (by exact_mod_cast h1)
  · intro h
    have hroot : ∀ t : ZMod p, t ^ 2 ≠ Int.castRingHom (ZMod p) a +
        Int.castRingHom (ZMod p) b * t := by
      intro t ht
      apply h t.cast
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      simp only [eq_intCast] at ht ⊢
      linear_combination ht
    have : Fact _ := ⟨hroot⟩
    have hspan : Ideal.span {(p : QuadraticAlgebra ℤ a b)} =
        RingHom.ker (mapRingHom (Int.castRingHom (ZMod p)) a b) := by
      ext x
      rw [hmem, RingHom.mem_ker, QuadraticAlgebra.ext_iff]
      simp [mapRingHom, ZMod.intCast_zmod_eq_zero_iff_dvd]
    rw [hspan]
    exact RingHom.ker_isMaximal_of_surjective _
      (mapRingHom_surjective (Int.castRingHom (ZMod p)) a b ZMod.intCast_surjective)

/-- **When the two primes above `p` coincide.** For a root `r` of `X² - b X - a` modulo `p`, the
ideals `(p, ω - r)` and `(p, ω - (b - r))` coincide exactly when `p` divides the discriminant
`b² + 4a` of `X² - b X - a`. -/
theorem span_natCast_omega_sub_eq_span_natCast_omega_sub_iff
    (hr : (p : ℤ) ∣ r ^ 2 - b * r - a) :
    Ideal.span {(p : QuadraticAlgebra ℤ a b), ω - (r : QuadraticAlgebra ℤ a b)} =
        Ideal.span {(p : QuadraticAlgebra ℤ a b), ω - ((b - r : ℤ) : QuadraticAlgebra ℤ a b)} ↔
      (p : ℤ) ∣ b ^ 2 + 4 * a := by
  have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  rw [eq_comm, span_natCast_omega_sub_eq_iff hr]
  -- `(2r - b)² = b² + 4a + 4 (r² - br - a)`, so `p ∣ 2r - b` exactly when `p ∣ b² + 4a`.
  have h4 : (p : ℤ) ∣ (r - (b - r)) ^ 2 - (b ^ 2 + 4 * a) := by
    convert dvd_mul_of_dvd_right hr 4 using 1; ring
  constructor
  · intro h
    simpa using dvd_sub (dvd_pow h two_ne_zero) h4
  · intro h
    exact hp.dvd_of_dvd_pow (n := 2) (by simpa using dvd_add h4 h)

/-- **The primes above `p`.** A prime ideal `P` of `ℤ[ω]` contains the rational prime `p` exactly
when either `X² - b X - a` has no root modulo `p` and `P = (p)`, or `P = (p, ω - r)` for a root
`r` of `X² - b X - a` modulo `p`. This lists every prime of `ℤ[ω]` above `p`, including at primes
dividing the conductor of a nonmaximal order. -/
theorem isPrime_and_natCast_mem_iff {P : Ideal (QuadraticAlgebra ℤ a b)} :
    P.IsPrime ∧ (p : QuadraticAlgebra ℤ a b) ∈ P ↔
      (P = Ideal.span {(p : QuadraticAlgebra ℤ a b)} ∧
          ∀ r : ℤ, ¬ (p : ℤ) ∣ r ^ 2 - b * r - a) ∨
        ∃ r : ℤ, (p : ℤ) ∣ r ^ 2 - b * r - a ∧
          P = Ideal.span {(p : QuadraticAlgebra ℤ a b), ω - (r : QuadraticAlgebra ℤ a b)} := by
  constructor
  · rintro ⟨hP, hp⟩
    by_cases h : ∃ r : ℤ, (p : ℤ) ∣ r ^ 2 - b * r - a
    · obtain ⟨r, hr⟩ := h
      refine Or.inr ?_
      rcases eq_or_eq_of_natCast_mem hr hp with h | h
      · exact ⟨r, hr, h⟩
      · exact ⟨b - r, by convert hr using 1; ring, h⟩
    · rw [not_exists] at h
      refine Or.inl ⟨((isMaximal_span_natCast_iff.mpr h).eq_of_le hP.ne_top ?_).symm, h⟩
      rwa [Ideal.span_le, Set.singleton_subset_iff]
  · rintro (⟨rfl, h⟩ | ⟨r, hr, rfl⟩)
    · exact ⟨(isMaximal_span_natCast_iff.mpr h).isPrime, Ideal.mem_span_singleton_self _⟩
    · exact ⟨(isMaximal_span_natCast_omega_sub hr).isPrime, Ideal.subset_span (by simp)⟩

end QuadraticAlgebra
