/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.Perfectoid.Untilt
public import TauCeti.RingTheory.AdicCompletion.Frobenius
public import TauCeti.RingTheory.AdicCompletion.Principal
public import TauCeti.RingTheory.Ideal.Quotient.Frobenius
public import TauCeti.RingTheory.Jacobson.Associated

/-!
# Adic completeness and quotients of ring perfections and tilts

Let `R` be a commutative ring of prime characteristic `p` and `w : Perfection R p` an element whose
zeroth coordinate `coeff R p 0 w` vanishes. For every coordinate index `m` and every exponent
`j ≥ p ^ m`, the `m`-th coordinate of `w ^ j` vanishes, because `(coeff R p m w) ^ (p ^ m)` is
`coeff R p 0 w = 0`. Consequently every formal series `∑ w ^ j * c j` in `Perfection R p` is
coordinatewise finite, and `Perfection R p` is `(w)`-adically complete and separated without any
completeness assumption on `R`.

When `A` is complete for two ideals `I ≤ J` whose quotients have characteristic `p`, reducing modulo
`J` induces a ring isomorphism `Perfection (A ⧸ I) p ≃+* Perfection (A ⧸ J) p`: multiplicatively,
both sides are isomorphic to `Perfection A p` through `Perfection.quotientMulEquiv`. Specialising to
`I = (p)` and `J = (ϖ)` for an element `ϖ♭ : PreTilt A p` whose untilt `ϖ = ϖ♭.untilt` divides `p`
and makes `A` `ϖ`-adically complete shows that `PreTilt A p` is `ϖ♭`-adically complete.

Finally, under the hypotheses of Bhatt–Morrow–Scholze, *Integral `p`-adic Hodge theory*, Lemmas 3.9
and 3.10(ii) — `A` is `π`-adically complete with `π ^ p ∣ p` and surjective Frobenius modulo `p` —
every element of `A` agrees modulo `π p` with an untilt from `PreTilt A p`, so a unit multiple of
`π` lies in the image of `PreTilt.untilt` (and therefore admits compatible `p`-power roots in `A`).
When moreover `π = ϖ♭.untilt` is a nonzerodivisor and relative Frobenius `A ⧸ (π) → A ⧸ (π ^ p)` is
injective, `ϖ♭` is a nonzerodivisor of `PreTilt A p`, divisibility by `ϖ♭` in `PreTilt A p` is
detected after untilting, and `PreTilt A p ⧸ (ϖ♭) ≃+* A ⧸ (π)`.

## Main definitions

* `Perfection.quotientRingEquiv`: `Perfection (A ⧸ I) p ≃+* Perfection (A ⧸ J) p` for `I ≤ J` when
  `A` is both `I`- and `J`-adically complete and both quotients have characteristic `p`.
* `PreTilt.quotientSpanEquiv`: `PreTilt A p ⧸ (ϖ♭) ≃+* A ⧸ (ϖ♭.untilt)` when `A` is complete for the
  nonzerodivisor `ϖ♭.untilt` with `ϖ♭.untilt ^ p ∣ p` and bijective relative Frobenius.

## Main results

* `Perfection.isAdicComplete_span_singleton_of_coeff_zero_eq_zero`: `Perfection R p` is
  `(w)`-adically complete whenever `coeff R p 0 w = 0`.
* `PreTilt.isAdicComplete_span_singleton`: `PreTilt A p` is `(ϖ♭)`-adically complete when
  `ϖ♭.untilt ∣ p` and `A` is `(ϖ♭.untilt)`-adically complete.
* `PreTilt.mem_nonZeroDivisors_of_untilt`: `ϖ♭` is a nonzerodivisor of `PreTilt A p` whenever
  `ϖ♭.untilt` is a nonzerodivisor of `A`.
* `PreTilt.exists_mul_natCast_dvd_sub_untilt`, `PreTilt.exists_associated_untilt`: every element of
  `A` is congruent modulo `π p` to an untilt, and `π` is associated to an untilt.
* `PreTilt.dvd_iff_untilt_dvd`: `ϖ♭ ∣ f` in `PreTilt A p` iff `ϖ♭.untilt ∣ f.untilt` in `A`.

## References

* B. Bhatt, M. Morrow, P. Scholze, *Integral `p`-adic Hodge theory*, Lemmas 3.9 and 3.10.
* P. Scholze, *Étale cohomology of diamonds*, Lemma 3.10 and Lemma 3.14.
-/

public section

open Ideal Finset
open scoped nonZeroDivisors

namespace Perfection

section AdicComplete

variable {R : Type*} [CommRing R] {p : ℕ} [hp : Fact p.Prime] [CharP R p]

/-- If the zeroth coordinate of `w : Perfection R p` vanishes, then the `m`-th coordinate of `w ^ j`
vanishes for every `j ≥ p ^ m`. -/
theorem coeff_pow_eq_zero_of_coeff_zero_eq_zero {w : Perfection R p} (hw : coeff R p 0 w = 0)
    {m j : ℕ} (hj : p ^ m ≤ j) : coeff R p m (w ^ j) = 0 := by
  have hpm : coeff R p m (w ^ p ^ m) = 0 := by
    have h := coeffMonoidHom_pow_p_pow w 0 m
    rw [zero_add, coeffMonoidHom_eq_coeff, coeffMonoidHom_eq_coeff] at h
    exact h.trans hw
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [pow_add, map_mul, hpm, zero_mul]

/-- If `coeff R p 0 w = 0`, then `Perfection R p` is `(w)`-adically separated. -/
theorem isHausdorff_span_singleton_of_coeff_zero_eq_zero {w : Perfection R p}
    (hw : coeff R p 0 w = 0) : IsHausdorff (span {w}) (Perfection R p) where
  haus' f hf := Perfection.ext fun m ↦ by
    have hm := hf (p ^ m)
    rw [smul_eq_mul, mul_top, SModEq.zero, span_singleton_pow, mem_span_singleton] at hm
    obtain ⟨g, rfl⟩ := hm
    rw [map_mul, coeff_pow_eq_zero_of_coeff_zero_eq_zero hw le_rfl, zero_mul, map_zero]

/-- Coordinatewise finite sum of the formal series `∑ w ^ j * c j` in `Perfection R p` when
`coeff R p 0 w = 0`: at coordinate `m`, all terms with `j ≥ p ^ m` vanish. -/
private def tsumPowMul {w : Perfection R p} (hw : coeff R p 0 w = 0)
    (c : ℕ → Perfection R p) : Perfection R p :=
  ⟨fun m ↦ ∑ j ∈ range (p ^ m), coeff R p m (w ^ j * c j), fun m ↦ by
    rw [← frobenius_def, map_sum]
    have hterm (j : ℕ) :
        frobenius R p (coeff R p (m + 1) (w ^ j * c j)) = coeff R p m (w ^ j * c j) := by
      rw [frobenius_def, coeff_pow_p']
    simp_rw [hterm]
    refine (sum_subset (range_mono (Nat.pow_le_pow_right hp.out.pos m.le_succ)) ?_).symm
    intro j _ hj
    rw [mem_range, not_lt] at hj
    rw [map_mul, coeff_pow_eq_zero_of_coeff_zero_eq_zero hw hj, zero_mul]⟩

private theorem tsumPowMul_eq_sum_add {w : Perfection R p} (hw : coeff R p 0 w = 0)
    (c : ℕ → Perfection R p) (n : ℕ) :
    tsumPowMul hw c =
      (∑ j ∈ range n, w ^ j * c j) + w ^ n * tsumPowMul hw (fun k ↦ c (n + k)) := by
  refine Perfection.ext fun m ↦ ?_
  have hext : coeff R p m (tsumPowMul hw c) =
      ∑ j ∈ range (n + p ^ m), coeff R p m (w ^ j * c j) := by
    refine sum_subset (range_mono (Nat.le_add_left (p ^ m) n)) fun j _ hj ↦ ?_
    rw [mem_range, not_lt] at hj
    rw [map_mul, coeff_pow_eq_zero_of_coeff_zero_eq_zero hw hj, zero_mul]
  rw [hext, sum_range_add, map_add, map_sum, map_mul]
  congr 1
  -- Unfold `coeff` on `tsumPowMul` at coordinate `m`, where `range (p ^ m)` matches the outer sum.
  change ∑ k ∈ range (p ^ m), coeff R p m (w ^ (n + k) * c (n + k)) =
    coeff R p m (w ^ n) * ∑ k ∈ range (p ^ m), coeff R p m (w ^ k * c (n + k))
  rw [mul_sum]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [pow_add, mul_assoc, map_mul]

/-- If `coeff R p 0 w = 0`, then `Perfection R p` is `(w)`-adically precomplete. -/
theorem isPrecomplete_span_singleton_of_coeff_zero_eq_zero {w : Perfection R p}
    (hw : coeff R p 0 w = 0) : IsPrecomplete (span {w}) (Perfection R p) where
  prec' f hf := by
    have hd (n : ℕ) : ∃ c : Perfection R p, w ^ n * c = f (n + 1) - f n := by
      have h := SModEq.sub_mem.mp (hf (Nat.le_succ n)).symm
      rw [smul_eq_mul, mul_top, span_singleton_pow, mem_span_singleton] at h
      obtain ⟨c, hc⟩ := h
      exact ⟨c, hc.symm⟩
    choose c hc using hd
    have htel (n : ℕ) : ∑ j ∈ range n, w ^ j * c j = f n - f 0 := by
      simp_rw [hc]
      exact sum_range_sub f n
    refine ⟨tsumPowMul hw c + f 0, fun n ↦ ?_⟩
    rw [SModEq.sub_mem, smul_eq_mul, mul_top, span_singleton_pow, mem_span_singleton,
      tsumPowMul_eq_sum_add hw c n, htel n]
    exact ⟨-tsumPowMul hw (fun k ↦ c (n + k)), by ring⟩

/-- **Adic completeness of a perfection.** Over any commutative ring `R` of characteristic `p`,
`Perfection R p` is complete and separated for the principal ideal generated by any `w` with
`coeff R p 0 w = 0`. -/
theorem isAdicComplete_span_singleton_of_coeff_zero_eq_zero {w : Perfection R p}
    (hw : coeff R p 0 w = 0) : IsAdicComplete (span {w}) (Perfection R p) where
  toIsHausdorff := isHausdorff_span_singleton_of_coeff_zero_eq_zero hw
  toIsPrecomplete := isPrecomplete_span_singleton_of_coeff_zero_eq_zero hw

end AdicComplete

section QuotientRingEquiv

variable (p : ℕ) [Fact p.Prime] {A : Type*} [CommRing A] {I J : Ideal A}
  [CharP (A ⧸ I) p] [CharP (A ⧸ J) p] [IsAdicComplete I A] [IsAdicComplete J A]

/-- **Change of ideal in the perfection of a quotient.** If `A` is complete for two ideals `I ≤ J`
whose quotients have characteristic `p`, reducing every coordinate from `A ⧸ I` to `A ⧸ J` is a
ring isomorphism `Perfection (A ⧸ I) p ≃+* Perfection (A ⧸ J) p` (compare Bhatt–Morrow–Scholze,
*Integral `p`-adic Hodge theory*, Lemma 3.2(i)). -/
noncomputable def quotientRingEquiv (hIJ : I ≤ J) :
    Perfection (A ⧸ I) p ≃+* Perfection (A ⧸ J) p :=
  RingEquiv.ofBijective (map p (Ideal.Quotient.factor hIJ)) <| by
    let e : Perfection (A ⧸ I) p ≃* Perfection (A ⧸ J) p :=
      (quotientMulEquiv p I).symm.trans (quotientMulEquiv p J)
    have heq : ⇑(map p (Ideal.Quotient.factor hIJ)) = ⇑e := by
      funext x
      obtain ⟨y, rfl⟩ := (quotientMulEquiv p I).surjective x
      refine Perfection.ext fun n ↦ ?_
      simp [e]
    rw [heq]
    exact e.bijective

@[simp]
theorem coeff_quotientRingEquiv (hIJ : I ≤ J) (x : Perfection (A ⧸ I) p) (n : ℕ) :
    coeff (A ⧸ J) p n (quotientRingEquiv p hIJ x) =
      Ideal.Quotient.factor hIJ (coeff (A ⧸ I) p n x) := by
  simp [quotientRingEquiv]

@[simp]
theorem teichmuller₀_quotientRingEquiv (hIJ : I ≤ J) (x : Perfection (A ⧸ I) p) :
    teichmuller₀ p J (quotientRingEquiv p hIJ x) = teichmuller₀ p I x := by
  obtain ⟨y, rfl⟩ := (quotientMulEquiv p I).surjective x
  have h : quotientRingEquiv p hIJ (quotientMulEquiv p I y) = quotientMulEquiv p J y := by
    ext n
    simp
  rw [h, ← coeff_zero_symm_quotientMulEquiv, ← coeff_zero_symm_quotientMulEquiv,
    MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]

end QuotientRingEquiv

end Perfection

namespace PreTilt

variable {A : Type*} [CommRing A] {p : ℕ} [hp : Fact p.Prime] [hpu : Fact ¬IsUnit (p : A)]

/-- If `a ^ k` is a nonzerodivisor for `k ≠ 0`, then `a` is a nonzerodivisor. -/
private theorem mem_nonZeroDivisors_of_pow {M₀ : Type*} [CommMonoidWithZero M₀] {a : M₀} {k : ℕ}
    (hk : k ≠ 0) (h : a ^ k ∈ M₀⁰) : a ∈ M₀⁰ :=
  (mul_mem_nonZeroDivisors.mp
    (by rwa [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk)])).2

/-- Two elements of `PreTilt A p` are equal if all of their `ModP A p` coordinates agree. -/
@[ext]
theorem ext {f g : PreTilt A p} (h : ∀ n, coeff n f = coeff n g) : f = g :=
  Perfection.ext h

/-- The definitional ring isomorphism `PreTilt A p ≃+* Perfection (ModP A p) p`. -/
@[expose]
def equivPerfection : PreTilt A p ≃+* Perfection (ModP A p) p :=
  RingEquiv.refl (Perfection (ModP A p) p)

@[simp]
theorem coeff_equivPerfection (x : PreTilt A p) (n : ℕ) :
    Perfection.coeff (ModP A p) p n (equivPerfection x) = coeff n x := by
  rw [equivPerfection, coeff_def]
  rfl

variable [IsAdicComplete (span {(p : A)}) A]

/-- **`PreTilt A p` is `(ϖ)`-adically complete.** If `ϖ : PreTilt A p` has `ϖ.untilt ∣ p` and
`A` is `(ϖ.untilt)`-adically complete, then `PreTilt A p` is `(ϖ)`-adically complete and
separated. -/
theorem isAdicComplete_span_singleton {ϖ : PreTilt A p} (hdvd : ϖ.untilt ∣ (p : A))
    [IsAdicComplete (span {ϖ.untilt}) A] : IsAdicComplete (span {ϖ}) (PreTilt A p) := by
  have : Nontrivial A := ⟨⟨p, 1, fun h ↦ hpu.out (h ▸ isUnit_one)⟩⟩
  set J : Ideal A := span {ϖ.untilt}
  have hJ : J ≠ ⊤ :=
    mt span_singleton_eq_top.mp (IsAdicComplete.not_isUnit_of_mem (mem_span_singleton_self _))
  have : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have : CharP (A ⧸ J) p := (CharP.charP_iff_prime_eq_zero hp.out).mpr <| by
    rw [← map_natCast (Ideal.Quotient.mk J), Ideal.Quotient.eq_zero_iff_mem]
    exact mem_span_singleton.mpr hdvd
  have hle : span {(p : A)} ≤ J :=
    span_le.mpr (Set.singleton_subset_iff.mpr (mem_span_singleton.mpr hdvd))
  let e : PreTilt A p ≃+* Perfection (A ⧸ J) p :=
    equivPerfection.trans (Perfection.quotientRingEquiv p hle)
  have he0 : Perfection.coeff (A ⧸ J) p 0 (e ϖ) = 0 := by
    simp only [e, RingEquiv.trans_apply, Perfection.coeff_quotientRingEquiv, coeff_equivPerfection,
      ← PreTilt.mk_untilt_eq_coeff_zero, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact mem_span_singleton_self _
  have hc : IsAdicComplete (span {e ϖ}) (Perfection (A ⧸ J) p) :=
    Perfection.isAdicComplete_span_singleton_of_coeff_zero_eq_zero he0
  have hmap : (span {ϖ}).map (e : PreTilt A p →+* Perfection (A ⧸ J) p) = span {e ϖ} := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  exact (IsAdicComplete.congr_ringEquiv (span {ϖ}) e).mp (hmap.symm ▸ hc)

/-- **Nonzerodivisors lift along `untilt`.** If `ϖ.untilt` is a nonzerodivisor of `A`, then `ϖ`
is a nonzerodivisor of `PreTilt A p` (the converse can fail when `A` has nilpotent elements killed
by perfection). -/
theorem mem_nonZeroDivisors_of_untilt {ϖ : PreTilt A p} (hreg : ϖ.untilt ∈ A⁰) :
    ϖ ∈ (PreTilt A p)⁰ := by
  refine mem_nonZeroDivisors_iff_left.mpr fun x hx ↦ ext fun n ↦ ?_
  set ψ : PreTilt A p ≃+* PreTilt A p := (frobeniusEquiv (PreTilt A p) p).symm
  have hψ_mul (k : ℕ) : (ψ^[k]) (ϖ * x) = (ψ^[k]) ϖ * (ψ^[k]) x := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', ih, map_mul]
  have hmul : untilt ((ψ^[n]) ϖ) * untilt ((ψ^[n]) x) = 0 := by
    rw [← map_mul, ← hψ_mul, hx, Function.iterate_fixed (map_zero ψ)]
    exact Perfection.teichmuller_zero
  have hpow : untilt ((ψ^[n]) ϖ) ^ p ^ n = ϖ.untilt :=
    untilt_iterate_frobeniusEquiv_symm_pow ϖ n
  have hreg_n : untilt ((ψ^[n]) ϖ) ∈ A⁰ :=
    mem_nonZeroDivisors_of_pow (pow_ne_zero n hp.out.ne_zero) (hpow.symm ▸ hreg)
  have hx_n : untilt ((ψ^[n]) x) = 0 :=
    (mul_left_mem_nonZeroDivisors_eq_zero_iff hreg_n).mp hmul
  have hcoeff : coeff 0 ((ψ^[n]) x) = coeff n x := by
    simpa only [ψ, zero_add] using coeff_iterate_frobeniusEquiv_symm 0 n x
  rw [map_zero, ← hcoeff, ← mk_untilt_eq_coeff_zero, hx_n, map_zero]

/-- **Approximation modulo `π p` by untilts** (Bhatt–Morrow–Scholze, *Integral `p`-adic Hodge
theory*, Lemma 3.9). In a `π`-adically complete ring `A` with `π ^ p ∣ p` in which every element is
a `p`-th power modulo `π ^ p`, every element of `A` is congruent modulo `π p` to `f.untilt` for
some `f : PreTilt A p`. -/
theorem exists_mul_natCast_dvd_sub_untilt {π : A} (hdvd : π ^ p ∣ (p : A))
    [IsAdicComplete (span {π}) A] (hs : ∀ x : A, ∃ y, π ^ p ∣ x - y ^ p) (x : A) :
    ∃ f : PreTilt A p, π * (p : A) ∣ x - f.untilt := by
  choose r hr using fun a : A ↦ TauCeti.exists_mul_dvd_sub_pow hs a
  let f : PreTilt A p := ⟨fun n ↦ Ideal.Quotient.mk (span {(p : A)}) (r^[n] x), fun n ↦ by
    dsimp only
    rw [Function.iterate_succ_apply', ← map_pow, Ideal.Quotient.eq, mem_span_singleton]
    exact (dvd_mul_left (p : A) π).trans (dvd_sub_comm.mp (hr (r^[n] x)))⟩
  have hmod : (r x) ^ p ≡ f.untilt [SMOD (span {(p : A)}) ^ 2] := by
    have h := Perfection.teichmuller₀_sModEq (I := span {(p : A)}) (x := f) (y := r x) (n := 1) rfl
    rw [pow_one] at h
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

/-- If `w₁ ^ p ∈ R⁰` and `w₁ ^ p`-divisibility is detected on `p`-th powers, then `w₁`-divisibility
is also detected on `p`-th powers: `(w₁ ^ p) ^ p ∣ (z * w₁ ^ (p - 1)) ^ p` yields
`w₁ ^ p ∣ z * w₁ ^ (p - 1)`, and cancelling `w₁ ^ (p - 1) ∈ R⁰` yields `w₁ ∣ z`. -/
private theorem dvd_of_pow_prime_dvd_pow {R : Type*} [CommRing R] {w₁ z : R}
    (hw_reg : w₁ ^ p ∈ R⁰) (hinj : ∀ u : R, (w₁ ^ p) ^ p ∣ u ^ p → w₁ ^ p ∣ u)
    (hz : w₁ ^ p ∣ z ^ p) : w₁ ∣ z := by
  have hz' : (w₁ ^ p) ^ p ∣ (z * w₁ ^ (p - 1)) ^ p := by
    have hlhs : w₁ ^ p * (w₁ ^ p) ^ (p - 1) = (w₁ ^ p) ^ p := by
      rw [← pow_succ', Nat.sub_add_cancel hp.out.one_le]
    have hrhs : z ^ p * (w₁ ^ p) ^ (p - 1) = (z * w₁ ^ (p - 1)) ^ p := by
      rw [← pow_mul, mul_comm p (p - 1), pow_mul, mul_pow]
    rw [← hlhs, ← hrhs]
    exact mul_dvd_mul_right hz _
  obtain ⟨c, hc⟩ := hinj _ hz'
  have hd_reg : w₁ ^ (p - 1) ∈ R⁰ :=
    pow_mem (mem_nonZeroDivisors_of_pow hp.out.ne_zero hw_reg) (p - 1)
  have hmul : (w₁ * c) * w₁ ^ (p - 1) = z * w₁ ^ (p - 1) := by
    have hw_eq : w₁ ^ p = w₁ * w₁ ^ (p - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hp.out.one_le]
    rw [hc, hw_eq]
    ring
  exact ⟨c, (mul_cancel_right_mem_nonZeroDivisors hd_reg).mp hmul.symm⟩

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
  have hw_pow (n : ℕ) : w (n + 1) ^ p = w n := by
    rw [← map_pow]
    exact congrArg untilt
      (by rw [Function.iterate_succ_apply']; exact frobeniusEquiv_symm_pow_p _ p ((ψ^[n]) ϖ))
  have hy_pow (n : ℕ) : y (n + 1) ^ p = y n := by
    rw [← map_pow]
    exact congrArg untilt
      (by rw [Function.iterate_succ_apply']; exact frobeniusEquiv_symm_pow_p _ p ((ψ^[n]) f))
  -- Inductively propagate regularity, root-divisibility, and `w n ∣ y n` along the root tower.
  have hstep (n : ℕ) :
      w n ∈ A⁰ ∧ (∀ z : A, w n ^ p ∣ z ^ p → w n ∣ z) ∧ w n ∣ y n := by
    induction n with
    | zero => exact ⟨hreg, (TauCeti.frobeniusModPow_injective_iff hdvd).mp hinj, hf⟩
    | succ n ih =>
      obtain ⟨hwn_reg, hwn_inj, hwn_dvd⟩ := ih
      have hw1_reg : w (n + 1) ∈ A⁰ :=
        mem_nonZeroDivisors_of_pow hp.out.ne_zero ((hw_pow n).symm ▸ hwn_reg)
      have hw1_inj (z : A) (hz : w (n + 1) ^ p ∣ z ^ p) : w (n + 1) ∣ z :=
        dvd_of_pow_prime_dvd_pow ((hw_pow n).symm ▸ hwn_reg) ((hw_pow n).symm ▸ hwn_inj) hz
      refine ⟨hw1_reg, hw1_inj, hw1_inj (y (n + 1)) ?_⟩
      rwa [hw_pow n, hy_pow n]
  choose q hq using fun n ↦ (hstep n).2.2
  have hq_compat (n : ℕ) : q (n + 1) ^ p = q n := by
    apply (mul_cancel_left_mem_nonZeroDivisors (hstep n).1).mp
    calc w n * q (n + 1) ^ p
      _ = (w (n + 1) * q (n + 1)) ^ p := by rw [← hw_pow n, mul_pow]
      _ = y n := by rw [← hq (n + 1), hy_pow n]
      _ = w n * q n := hq n
  let g : PreTilt A p := ⟨fun n ↦ Ideal.Quotient.mk (span {(p : A)}) (q n), fun n ↦ by
    dsimp only
    rw [← map_pow, hq_compat]⟩
  have hg (n : ℕ) : coeff n g = Ideal.Quotient.mk (span {(p : A)}) (q n) := rfl
  refine ⟨g, ext fun n ↦ ?_⟩
  have hcoeff (x : PreTilt A p) :
      coeff n x = Ideal.Quotient.mk (span {(p : A)}) (untilt ((ψ^[n]) x)) := by
    have h0 : coeff 0 ((ψ^[n]) x) = coeff n x := by
      simpa only [ψ, zero_add] using coeff_iterate_frobeniusEquiv_symm 0 n x
    exact h0.symm.trans (mk_untilt_eq_coeff_zero ((ψ^[n]) x)).symm
  rw [map_mul, hcoeff f, hcoeff ϖ, hg, ← map_mul]
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
  have hs_mul :=
    TauCeti.exists_mul_dvd_sub_pow ((TauCeti.frobeniusModPow_surjective_iff hdvd).mp hbij.2)
  have hs_modP : Function.Surjective (frobenius (ModP A p) p) :=
    (TauCeti.surjective_frobenius_modP_iff A).mpr fun a ↦
      (hs_mul a).imp fun _ ↦ (dvd_mul_left (p : A) ϖ.untilt).trans
  have hsurj : Function.Surjective ψ :=
    (Ideal.Quotient.factor_surjective hle).comp (Perfection.coeff_surjective hs_modP 0)
  exact (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)

@[simp]
theorem quotientSpanEquiv_mk {ϖ : PreTilt A p} {hdvd : ϖ.untilt ^ p ∣ (p : A)}
    [IsAdicComplete (span {ϖ.untilt}) A] (hreg : ϖ.untilt ∈ A⁰)
    (hbij : Function.Bijective (TauCeti.frobeniusModPow p hdvd)) (f : PreTilt A p) :
    quotientSpanEquiv hreg hbij (Ideal.Quotient.mk (span {ϖ}) f) =
      Ideal.Quotient.mk (span {ϖ.untilt}) f.untilt := by
  simp [quotientSpanEquiv, ← mk_untilt_eq_coeff_zero]

end PreTilt

end
