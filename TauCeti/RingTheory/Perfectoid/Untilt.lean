/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Perfectoid.Untilt
public import TauCeti.Algebra.Ring.NonZeroDivisors
public import TauCeti.RingTheory.AdicCompletion.Frobenius
public import TauCeti.RingTheory.Jacobson.Associated
public import TauCeti.RingTheory.Perfection

/-!
# Approximation, divisibility, and quotients along the untilt map

Let `p` be a prime and `A` a `(p)`-adically complete commutative ring in which `p` is not a unit,
so Mathlib's tilt `PreTilt A p` and multiplicative untilt map `PreTilt.untilt : PreTilt A p →* A`
are defined.

Under the hypotheses of Bhatt–Morrow–Scholze, *Integral `p`-adic Hodge theory*, Lemmas 3.9 and
3.10(ii) — `A` is `π`-adically complete with `π ^ p ∣ p` and surjective relative Frobenius
`A ⧸ (π) → A ⧸ (π ^ p)` — every element of `A` agrees modulo `π p` with `f.untilt` for some
`f : PreTilt A p`. In particular, a unit multiple of `π` lies in the image of `PreTilt.untilt` and
therefore admits compatible `p`-power roots in `A`.

When `ϖ : PreTilt A p` has a nonzerodivisor untilt `ϖ.untilt ∈ A⁰`, `ϖ` is a nonzerodivisor of
`PreTilt A p`. If moreover `ϖ.untilt ^ p ∣ p` and relative Frobenius
`A ⧸ (ϖ.untilt) → A ⧸ (ϖ.untilt ^ p)` is injective, divisibility by `ϖ` in `PreTilt A p` is
detected after untilting (`ϖ ∣ f ↔ ϖ.untilt ∣ f.untilt`), and when `A` is `(ϖ.untilt)`-adically
complete with bijective relative Frobenius, reducing the zeroth coordinate induces a ring
isomorphism `PreTilt A p ⧸ (ϖ) ≃+* A ⧸ (ϖ.untilt)`.

## Main definitions

* `PreTilt.quotientSpanEquiv`: `PreTilt A p ⧸ (ϖ) ≃+* A ⧸ (ϖ.untilt)` when `A` is complete for the
  nonzerodivisor `ϖ.untilt` with `ϖ.untilt ^ p ∣ p` and bijective relative Frobenius.

## Main results

* `PreTilt.untilt_equivPerfection_symm`, `PreTilt.teichmuller₀_equivPerfection`,
  `PreTilt.untilt_zero`: compatibility of `PreTilt.untilt` and `Perfection.teichmuller₀` across
  `PreTilt.equivPerfection`, and `(0 : PreTilt A p).untilt = 0`.
* `PreTilt.coeff_eq_mk_untilt_iterate`, `PreTilt.untilt_iterate_frobeniusEquiv_symm_succ_pow`:
  the `n`-th `ModP A p` coordinate of `x : PreTilt A p` is the reduction modulo `p` of
  `untilt ((frobeniusEquiv.symm^[n]) x)`, whose `p`-th powers step along the root tower.
* `PreTilt.mem_nonZeroDivisors_of_untilt`: `ϖ` is a nonzerodivisor of `PreTilt A p` whenever
  `ϖ.untilt` is a nonzerodivisor of `A`.
* `PreTilt.exists_mul_natCast_dvd_sub_untilt`, `PreTilt.exists_associated_untilt`: every element of
  `A` is congruent modulo `π p` to an untilt, and `π` is associated to an untilt.
* `PreTilt.dvd_iff_untilt_dvd`: `ϖ ∣ f` in `PreTilt A p` iff `ϖ.untilt ∣ f.untilt` in `A`.

## References

* B. Bhatt, M. Morrow, P. Scholze, *Integral `p`-adic Hodge theory*, Lemmas 3.9 and 3.10.
* P. Scholze, *Étale cohomology of diamonds*, Lemma 3.10 and Lemma 3.14.
-/

public section

open Ideal
open scoped nonZeroDivisors

namespace PreTilt

variable {A : Type*} [CommRing A] {p : ℕ} [hp : Fact p.Prime] [Fact ¬IsUnit (p : A)]
  [IsAdicComplete (span {(p : A)}) A]

/-- The `n`-th coordinate of `x : PreTilt A p` is the reduction modulo `p` of the untilt of its
`p ^ n`-th root `(frobeniusEquiv.symm^[n]) x`. -/
theorem coeff_eq_mk_untilt_iterate (n : ℕ) (x : PreTilt A p) :
    coeff n x =
      Ideal.Quotient.mk (span {(p : A)})
        (untilt (((frobeniusEquiv (PreTilt A p) p).symm^[n]) x)) := by
  have h0 : coeff 0 (((frobeniusEquiv (PreTilt A p) p).symm^[n]) x) = coeff n x := by
    simpa only [zero_add] using coeff_iterate_frobeniusEquiv_symm 0 n x
  exact h0.symm.trans (mk_untilt_eq_coeff_zero _).symm

/-- Raising the untilt of `(frobeniusEquiv.symm^[n + 1]) x` to the `p`-th power recovers the untilt
of `(frobeniusEquiv.symm^[n]) x`. -/
theorem untilt_iterate_frobeniusEquiv_symm_succ_pow (x : PreTilt A p) (n : ℕ) :
    untilt (((frobeniusEquiv (PreTilt A p) p).symm^[n + 1]) x) ^ p =
      untilt (((frobeniusEquiv (PreTilt A p) p).symm^[n]) x) := by
  rw [← map_pow, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]

/-- `PreTilt.untilt` on `equivPerfection.symm x` is `Perfection.teichmuller₀` on `x`. -/
@[simp]
theorem untilt_equivPerfection_symm (x : Perfection (ModP A p) p) :
    (equivPerfection.symm x).untilt = Perfection.teichmuller₀ p (span {(p : A)}) x := by
  symm
  refine Perfection.teichmuller₀_spec fun n ↦
    ⟨untilt (((frobeniusEquiv (PreTilt A p) p).symm^[n]) (equivPerfection.symm x)), ?_, ?_⟩
  · rw [← coeff_equivPerfection_symm, coeff_eq_mk_untilt_iterate]
  · rw [untilt_iterate_frobeniusEquiv_symm_pow]

/-- `Perfection.teichmuller₀` on `equivPerfection x` is `x.untilt`. -/
@[simp]
theorem teichmuller₀_equivPerfection (x : PreTilt A p) :
    Perfection.teichmuller₀ p (span {(p : A)}) (equivPerfection x) = x.untilt := by
  symm
  simpa using untilt_equivPerfection_symm (equivPerfection x)

/-- The untilt of `0 : PreTilt A p` is `0`. -/
@[simp]
theorem untilt_zero : (0 : PreTilt A p).untilt = 0 := by
  rw [← teichmuller₀_equivPerfection, map_zero, map_zero]

/-- **Nonzerodivisors lift along `untilt`.** If `ϖ.untilt` is a nonzerodivisor of `A`, then `ϖ`
is a nonzerodivisor of `PreTilt A p` (the converse can fail when `A` has nilpotent elements killed
by perfection). -/
theorem mem_nonZeroDivisors_of_untilt {ϖ : PreTilt A p} (hreg : ϖ.untilt ∈ A⁰) :
    ϖ ∈ (PreTilt A p)⁰ := by
  refine mem_nonZeroDivisors_iff_left.mpr fun x hx ↦ ext fun n ↦ ?_
  set ψ : PreTilt A p ≃+* PreTilt A p := (frobeniusEquiv (PreTilt A p) p).symm
  have hmul : untilt ((ψ^[n]) ϖ) * untilt ((ψ^[n]) x) = 0 := by
    rw [← map_mul, ← iterate_map_mul ψ n ϖ x, hx, iterate_map_zero ψ n, untilt_zero]
  have hpow : untilt ((ψ^[n]) ϖ) ^ p ^ n = ϖ.untilt :=
    untilt_iterate_frobeniusEquiv_symm_pow ϖ n
  have hreg_n : untilt ((ψ^[n]) ϖ) ∈ A⁰ :=
    (TauCeti.pow_mem_nonZeroDivisors_iff (pow_ne_zero n hp.out.ne_zero)).mp (hpow.symm ▸ hreg)
  have hx_n : untilt ((ψ^[n]) x) = 0 :=
    (mul_left_mem_nonZeroDivisors_eq_zero_iff hreg_n).mp hmul
  rw [map_zero, coeff_eq_mk_untilt_iterate, hx_n, map_zero]

/-- **Approximation modulo `π p` by untilts** (Bhatt–Morrow–Scholze, *Integral `p`-adic Hodge
theory*, Lemma 3.9). In a `π`-adically complete ring `A` with `π ^ p ∣ p` in which every element is
a `p`-th power modulo `π ^ p`, every element of `A` is congruent modulo `π p` to `f.untilt` for
some `f : PreTilt A p`. -/
theorem exists_mul_natCast_dvd_sub_untilt {π : A} (hdvd : π ^ p ∣ (p : A))
    [IsAdicComplete (span {π}) A] (hs : ∀ x : A, ∃ y, π ^ p ∣ x - y ^ p) (x : A) :
    ∃ f : PreTilt A p, π * (p : A) ∣ x - f.untilt := by
  choose r hr using fun a : A ↦ TauCeti.exists_mul_dvd_sub_pow hs a
  let f₀ : Perfection (ModP A p) p := ⟨fun n ↦ Ideal.Quotient.mk (span {(p : A)}) (r^[n] x),
    fun n ↦ by
      dsimp only
      rw [Function.iterate_succ_apply', ← map_pow, Ideal.Quotient.eq, mem_span_singleton]
      exact (dvd_mul_left (p : A) π).trans (dvd_sub_comm.mp (hr (r^[n] x)))⟩
  let f : PreTilt A p := equivPerfection.symm f₀
  have hmod : (r x) ^ p ≡ f.untilt [SMOD (span {(p : A)}) ^ 2] := by
    have hf1 : Ideal.Quotient.mk (span {(p : A)}) (r x) =
        Perfection.coeff (ModP A p) p 1 (equivPerfection f) := by
      rw [equivPerfection.apply_symm_apply]
      symm
      exact Perfection.coeff_mk _ _ 1
    have h := Perfection.teichmuller₀_sModEq (I := span {(p : A)})
      (x := equivPerfection f) (y := r x) (n := 1) hf1
    rw [teichmuller₀_equivPerfection, pow_one] at h
    exact h.symm
  have hp2 : (p : A) ^ 2 ∣ (r x) ^ p - f.untilt := by
    rwa [SModEq.sub_mem, span_singleton_pow, mem_span_singleton] at hmod
  have hπp : π * (p : A) ∣ (p : A) ^ 2 := by
    rw [sq]
    exact mul_dvd_mul_right ((dvd_pow_self π hp.out.ne_zero).trans hdvd) _
  refine ⟨f, ?_⟩
  have hadd := dvd_add (hr x) (hπp.trans hp2)
  rwa [sub_add_sub_cancel] at hadd

/-- **Existence of compatible `p`-power roots up to a unit** (Bhatt–Morrow–Scholze, *Integral
`p`-adic Hodge theory*, Lemma 3.9). In a `π`-adically complete ring `A` with `π ^ p ∣ p` in which
every element is a `p`-th power modulo `π ^ p`, some `ϖ : PreTilt A p` satisfies
`π * p ∣ π - ϖ.untilt` and `Associated π ϖ.untilt`. -/
theorem exists_associated_untilt {π : A} (hdvd : π ^ p ∣ (p : A))
    [IsAdicComplete (span {π}) A] (hs : ∀ x : A, ∃ y, π ^ p ∣ x - y ^ p) :
    ∃ ϖ : PreTilt A p, π * (p : A) ∣ π - ϖ.untilt ∧ Associated π ϖ.untilt := by
  obtain ⟨ϖ, hϖ⟩ := exists_mul_natCast_dvd_sub_untilt hdvd hs π
  have hp_mem : (p : A) ∈ span {π} :=
    mem_span_singleton.mpr ((dvd_pow_self π hp.out.ne_zero).trans hdvd)
  have hp_jac : (p : A) ∈ (⊥ : Ideal A).jacobson := by
    rw [Ideal.jacobson_bot]
    exact IsAdicComplete.le_jacobson (span {π}) hp_mem
  exact ⟨ϖ, hϖ,
    TauCeti.associated_of_mul_dvd_sub_of_mem_jacobson hp_jac (dvd_sub_comm.mp hϖ)⟩

/-- **Divisibility by `ϖ` is detected after untilting.** Let `ϖ : PreTilt A p` be such that
`ϖ.untilt` is a nonzerodivisor of `A` with `ϖ.untilt ^ p ∣ p` and injective relative Frobenius
`A ⧸ (ϖ.untilt) → A ⧸ (ϖ.untilt ^ p)`. Then `ϖ ∣ f` in `PreTilt A p` if and only if
`ϖ.untilt ∣ f.untilt` in `A`. -/
theorem dvd_iff_untilt_dvd {ϖ : PreTilt A p} {hdvd : ϖ.untilt ^ p ∣ (p : A)}
    (hreg : ϖ.untilt ∈ A⁰) (hinj : Function.Injective (TauCeti.frobeniusModPow p hdvd))
    {f : PreTilt A p} : ϖ ∣ f ↔ ϖ.untilt ∣ f.untilt := by
  refine ⟨map_dvd untilt, fun hf ↦ ?_⟩
  set ψ : PreTilt A p ≃+* PreTilt A p := (frobeniusEquiv (PreTilt A p) p).symm
  set w : ℕ → A := fun n ↦ untilt ((ψ^[n]) ϖ)
  set y : ℕ → A := fun n ↦ untilt ((ψ^[n]) f)
  have hw_pow (n : ℕ) : w (n + 1) ^ p = w n := untilt_iterate_frobeniusEquiv_symm_succ_pow ϖ n
  have hy_pow (n : ℕ) : y (n + 1) ^ p = y n := untilt_iterate_frobeniusEquiv_symm_succ_pow f n
  -- Inductively propagate regularity, root-divisibility, and `w n ∣ y n` along the root tower.
  have hstep (n : ℕ) :
      w n ∈ A⁰ ∧ (∀ z : A, w n ^ p ∣ z ^ p → w n ∣ z) ∧ w n ∣ y n := by
    induction n with
    | zero => exact ⟨hreg, (TauCeti.frobeniusModPow_injective_iff hdvd).mp hinj, hf⟩
    | succ n ih =>
      obtain ⟨hwn_reg, hwn_inj, _⟩ := ih
      have hw1_reg : w (n + 1) ∈ A⁰ :=
        (TauCeti.pow_mem_nonZeroDivisors_iff hp.out.ne_zero).mp ((hw_pow n).symm ▸ hwn_reg)
      have hw1_inj (z : A) (hz : w (n + 1) ^ p ∣ z ^ p) : w (n + 1) ∣ z :=
        TauCeti.dvd_of_pow_dvd_pow hp.out.ne_zero ((hw_pow n).symm ▸ hwn_reg)
          ((hw_pow n).symm ▸ hwn_inj) hz
      refine ⟨hw1_reg, hw1_inj, hw1_inj (y (n + 1)) ?_⟩
      rwa [hw_pow n, hy_pow n]
  choose q hq using fun n ↦ (hstep n).2.2
  have hq_compat (n : ℕ) : q (n + 1) ^ p = q n := by
    apply (mul_cancel_left_mem_nonZeroDivisors (hstep n).1).mp
    calc w n * q (n + 1) ^ p
      _ = (w (n + 1) * q (n + 1)) ^ p := by rw [← hw_pow n, mul_pow]
      _ = y n := by rw [← hq (n + 1), hy_pow n]
      _ = w n * q n := hq n
  let g₀ : Perfection (ModP A p) p := ⟨fun n ↦ Ideal.Quotient.mk (span {(p : A)}) (q n),
    fun n ↦ by
      dsimp only
      rw [← map_pow, hq_compat]⟩
  let g : PreTilt A p := equivPerfection.symm g₀
  have hg (n : ℕ) : coeff n g = Ideal.Quotient.mk (span {(p : A)}) (q n) := by
    rw [coeff_equivPerfection_symm]
    exact Perfection.coeff_mk _ _ n
  refine ⟨g, ext fun n ↦ ?_⟩
  rw [map_mul, coeff_eq_mk_untilt_iterate n f, coeff_eq_mk_untilt_iterate n ϖ, hg, ← map_mul]
  exact congrArg (Ideal.Quotient.mk (span {(p : A)})) (hq n)

/-- **The small quotient `PreTilt A p ⧸ (ϖ) ≃+* A ⧸ (ϖ.untilt)`.** When `A` is complete for a
nonzerodivisor `ϖ.untilt` with `ϖ.untilt ^ p ∣ p` and relative Frobenius
`A ⧸ (ϖ.untilt) → A ⧸ (ϖ.untilt ^ p)` is bijective, reducing the zeroth coordinate modulo
`ϖ.untilt` induces a ring isomorphism `PreTilt A p ⧸ (ϖ) ≃+* A ⧸ (ϖ.untilt)`. -/
noncomputable def quotientSpanEquiv {ϖ : PreTilt A p} {hdvd : ϖ.untilt ^ p ∣ (p : A)}
    [IsAdicComplete (span {ϖ.untilt}) A] (hreg : ϖ.untilt ∈ A⁰)
    (hbij : Function.Bijective (TauCeti.frobeniusModPow p hdvd)) :
    PreTilt A p ⧸ span {ϖ} ≃+* A ⧸ span {ϖ.untilt} := by
  have hle : span {(p : A)} ≤ span {ϖ.untilt} :=
    span_le.mpr <| Set.singleton_subset_iff.mpr <|
      mem_span_singleton.mpr ((dvd_pow_self _ hp.out.ne_zero).trans hdvd)
  set ψ : PreTilt A p →+* A ⧸ span {ϖ.untilt} := (Ideal.Quotient.factor hle).comp (coeff 0)
  have hψ (f : PreTilt A p) : ψ f = Ideal.Quotient.mk (span {ϖ.untilt}) f.untilt := by
    simp [ψ, ← mk_untilt_eq_coeff_zero]
  have hker : RingHom.ker ψ = span {ϖ} := by
    ext f
    rw [RingHom.mem_ker, hψ, Ideal.Quotient.eq_zero_iff_mem, mem_span_singleton,
      mem_span_singleton, dvd_iff_untilt_dvd hreg hbij.1]
  have hs_modP : Function.Surjective (frobenius (ModP A p) p) :=
    TauCeti.surjective_frobenius_modP_of_frobeniusModPow_surjective hbij.2
  have hsurj : Function.Surjective ψ :=
    (Ideal.Quotient.factor_surjective hle).comp (Perfection.coeff_surjective hs_modP 0)
  exact (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)

/-- `PreTilt.quotientSpanEquiv` sends the class of `f` to the class of `f.untilt`. -/
@[simp]
theorem quotientSpanEquiv_mk {ϖ : PreTilt A p} {hdvd : ϖ.untilt ^ p ∣ (p : A)}
    [IsAdicComplete (span {ϖ.untilt}) A] (hreg : ϖ.untilt ∈ A⁰)
    (hbij : Function.Bijective (TauCeti.frobeniusModPow p hdvd)) (f : PreTilt A p) :
    quotientSpanEquiv hreg hbij (Ideal.Quotient.mk (span {ϖ}) f) =
      Ideal.Quotient.mk (span {ϖ.untilt}) f.untilt := by
  simp [quotientSpanEquiv, ← mk_untilt_eq_coeff_zero]

end PreTilt

end
