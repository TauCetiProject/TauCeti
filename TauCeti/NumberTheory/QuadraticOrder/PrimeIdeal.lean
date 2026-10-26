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
  `ℤ[√d]` with `d ≡ 1 (mod 4)`, an order of conductor `2`, it fails at `p = 2`;
* when the criterion holds, every prime of `ℤ[ω]` containing `p` is `𝔭_r` or `𝔭_(b - r)`
  (`eq_or_eq_of_natCast_mem`); the two coincide (`p` ramifies) exactly when `p ∣ 2r - b`;
* if `f` has no root modulo `p`, then `(p)` itself is maximal, so `p` is inert
  (`isMaximal_span_natCast_iff`), and conversely.

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
theorem mem_span_natCast_omega_sub_iff (hr : (p : ℤ) ∣ r ^ 2 - b * r - a)
    {x : QuadraticAlgebra ℤ a b} :
    x ∈ Ideal.span {(p : QuadraticAlgebra ℤ a b), ω - (r : QuadraticAlgebra ℤ a b)} ↔
      (p : ℤ) ∣ x.re + x.im * r := by
  rw [← ker_evalRoot hr, RingHom.mem_ker, evalRoot_apply,
    ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- **The norm of `(p, ω - r)` is `p`.** For a root `r` of `X² - b X - a` modulo `p`, the
residue ring of `(p, ω - r)` has exactly `p` elements. -/
theorem card_quotient_span_natCast_omega_sub (hr : (p : ℤ) ∣ r ^ 2 - b * r - a) :
    Nat.card (QuadraticAlgebra ℤ a b ⧸
      Ideal.span {(p : QuadraticAlgebra ℤ a b), ω - (r : QuadraticAlgebra ℤ a b)}) = p := by
  rw [← ker_evalRoot hr, Nat.card_congr
    (RingHom.quotientKerEquivOfSurjective (evalRoot_surjective hr)).toEquiv, Nat.card_zmod]

/-- **Two roots give the same prime iff they agree modulo `p`.** -/
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
          1 * (ω - (r : QuadraticAlgebra ℤ a b)) := by
      have : ((r - s : ℤ) : QuadraticAlgebra ℤ a b) = ((p * k : ℤ) : QuadraticAlgebra ℤ a b) := by
        rw [hk]
      push_cast at this
      linear_combination this
    have key' : ω - (r : QuadraticAlgebra ℤ a b) =
        (-k : QuadraticAlgebra ℤ a b) * (p : QuadraticAlgebra ℤ a b) +
          1 * (ω - (s : QuadraticAlgebra ℤ a b)) := by
      linear_combination -1 * key
    apply le_antisymm <;> rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff] <;>
      refine ⟨Ideal.subset_span (by simp), Ideal.mem_span_pair.mpr ?_⟩
    · exact ⟨_, _, key.symm⟩
    · exact ⟨_, _, key'.symm⟩

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
    refine Ideal.mul_le.mpr fun x hx y hy => ?_
    obtain ⟨α, β, rfl⟩ := Ideal.mem_span_pair.mp hx
    obtain ⟨γ, δ, rfl⟩ := Ideal.mem_span_pair.mp hy
    refine Ideal.mem_span_singleton'.mpr
      ⟨α * γ * P + α * δ * (ω - R') + β * γ * (ω - R) - β * δ * M, ?_⟩
    linear_combination -(β * δ) * hkey
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
      refine Ideal.mul_le.mpr fun x hx y hy => ?_
      obtain ⟨α, β, rfl⟩ := Ideal.mem_span_pair.mp hx
      obtain ⟨γ, δ, rfl⟩ := Ideal.mem_span_pair.mp hy
      refine Ideal.mem_span_singleton_mul.mpr ⟨α * γ * P + (α * δ + β * γ) * (ω - R) +
        β * δ * (-(t : QuadraticAlgebra ℤ a b) * (ω - R) - M), ?_, ?_⟩
      · exact add_mem (add_mem (Ideal.mul_mem_left _ _ hP𝔭) (Ideal.mul_mem_left _ _ hω𝔭))
          (Ideal.mul_mem_left _ _ (sub_mem (Ideal.mul_mem_left _ _ hω𝔭) hM𝔭))
      · linear_combination -(β * δ) * hsq'
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

/-- **The primes above a split or ramified `p`.** If `r` is a root of `X² - b X - a` modulo `p`
and Dedekind's criterion holds, every prime ideal of `ℤ[ω]` containing `p` is `(p, ω - r)` or
`(p, ω - (b - r))`. -/
theorem eq_or_eq_of_natCast_mem (hr : (p : ℤ) ∣ r ^ 2 - b * r - a)
    (hD : ¬ ((p : ℤ) ∣ 2 * r - b ∧ (p : ℤ) ^ 2 ∣ r ^ 2 - b * r - a))
    {P : Ideal (QuadraticAlgebra ℤ a b)} [P.IsPrime] (hP : (p : QuadraticAlgebra ℤ a b) ∈ P) :
    P = Ideal.span {(p : QuadraticAlgebra ℤ a b), ω - (r : QuadraticAlgebra ℤ a b)} ∨
      P = Ideal.span {(p : QuadraticAlgebra ℤ a b),
        ω - ((b - r : ℤ) : QuadraticAlgebra ℤ a b)} := by
  have hr' : (p : ℤ) ∣ (b - r) ^ 2 - b * (b - r) - a := by
    convert hr using 1; ring
  have hle := ((span_natCast_omega_sub_mul_span_natCast_omega_sub_eq_iff hr).mpr hD).le.trans
    ((Ideal.span_singleton_le_iff_mem P).mpr hP)
  rcases (Ideal.IsPrime.mul_le inferInstance).mp hle with h | h
  · exact Or.inl ((isMaximal_span_natCast_omega_sub hr).eq_of_le Ideal.IsPrime.ne_top' h).symm
  · exact Or.inr ((isMaximal_span_natCast_omega_sub hr').eq_of_le Ideal.IsPrime.ne_top' h).symm

/-- **The inert case.** The ideal `(p)` of `ℤ[ω]` is maximal, that is, `p` is inert, exactly when
`X² - b X - a` has no root modulo `p`. -/
theorem isMaximal_span_natCast_iff :
    (Ideal.span {(p : QuadraticAlgebra ℤ a b)}).IsMaximal ↔
      ∀ r : ℤ, ¬ (p : ℤ) ∣ r ^ 2 - b * r - a := by
  have hmem : ∀ x : QuadraticAlgebra ℤ a b, x ∈ Ideal.span {(p : QuadraticAlgebra ℤ a b)} ↔
      (p : ℤ) ∣ x.re ∧ (p : ℤ) ∣ x.im := by
    intro x
    rw [Ideal.mem_span_singleton, show (p : QuadraticAlgebra ℤ a b) =
      algebraMap ℤ _ (p : ℤ) by simp, algebraMap_dvd_iff]
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

end QuadraticAlgebra
