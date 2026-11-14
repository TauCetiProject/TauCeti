/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.Perfectoid.Untilt
public import TauCeti.RingTheory.AdicCompletion.Principal
public import TauCeti.RingTheory.Perfection

/-!
# Adic completeness and change-of-ideal isomorphisms of ring perfections and tilts

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
(or has a positive power dividing `p`) and makes `A` `ϖ`-adically complete shows that `PreTilt A p`
is `ϖ♭`-adically complete.

## Main definitions

* `Perfection.quotientRingEquiv`: `Perfection (A ⧸ I) p ≃+* Perfection (A ⧸ J) p` for `I ≤ J` when
  `A` is both `I`- and `J`-adically complete and both quotients have characteristic `p`.

## Main results

* `Perfection.isAdicComplete_span_singleton_of_coeff_zero_eq_zero`: `Perfection R p` is
  `(w)`-adically complete whenever `coeff R p 0 w = 0`.
* `PreTilt.isAdicComplete_span_singleton`,
  `PreTilt.isAdicComplete_span_singleton_of_pow_dvd`: `PreTilt A p` is `(ϖ♭)`-adically complete when
  `ϖ♭.untilt ∣ p` (or `ϖ♭.untilt ^ k ∣ p` for `k ≠ 0`) and `A` is `(ϖ♭.untilt)`-adically complete.

## References

* B. Bhatt, M. Morrow, P. Scholze, *Integral `p`-adic Hodge theory*, Lemma 3.2(i) and Lemma 3.10.
* P. Scholze, *Étale cohomology of diamonds*, Lemma 3.4.
-/

public section

open Ideal Finset

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

/-- `Perfection.quotientRingEquiv` applies `Ideal.Quotient.factor` at every coordinate. -/
@[simp]
theorem coeff_quotientRingEquiv (hIJ : I ≤ J) (x : Perfection (A ⧸ I) p) (n : ℕ) :
    coeff (A ⧸ J) p n (quotientRingEquiv p hIJ x) =
      Ideal.Quotient.factor hIJ (coeff (A ⧸ I) p n x) := by
  simp [quotientRingEquiv]

/-- `Perfection.teichmuller₀` is invariant under `Perfection.quotientRingEquiv`. -/
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
  [IsAdicComplete (span {(p : A)}) A]

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
    rw [Ideal.map_span, Set.image_singleton, RingEquiv.coe_toRingHom]
  exact (IsAdicComplete.congr_ringEquiv (span {ϖ}) e).mp (hmap.symm ▸ hc)

/-- **`PreTilt A p` is `(ϖ)`-adically complete when a positive power of `ϖ.untilt` divides `p`.** -/
theorem isAdicComplete_span_singleton_of_pow_dvd {ϖ : PreTilt A p} {k : ℕ} [NeZero k]
    (hdvd : ϖ.untilt ^ k ∣ (p : A)) [IsAdicComplete (span {ϖ.untilt}) A] :
    IsAdicComplete (span {ϖ}) (PreTilt A p) :=
  isAdicComplete_span_singleton ((dvd_pow_self _ (NeZero.ne k)).trans hdvd)

end PreTilt

end
