/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Jacobson.Ideal
public import TauCeti.RingTheory.DeltaRing.Basic
import TauCeti.RingTheory.Jacobson.Basic

/-!
# Distinguished elements of δ-rings

An element `d` of a `δ`-ring `A` is *distinguished* when `δ d` is a unit. Distinguished elements
are the generators of the ideals of oriented prisms. This file proves the basic properties of
distinguished elements from Bhatt and Scholze, *Prisms and prismatic cohomology*, §2.3, where
`rad(A)` is the Jacobson radical `Ring.jacobson A`:

* `δ`-maps preserve distinguished elements, and a distinguished `d` has `p ∈ (d, φ d)`;
* if `p ∈ rad(A)` then `p` is distinguished, as `δ p = 1 - p ^ (p - 1)`;
* if `d ∈ rad(A)`, a unit multiple of a distinguished `d` is distinguished (Lemma 2.23);
* if `f * h` is distinguished and `f ∈ rad(A)`, then `f` is distinguished, and if moreover
  `p ∈ rad(A)` then `h` is a unit (Lemma 2.24);
* if `d, p ∈ rad(A)`, then `d` is distinguished if and only if `p ∈ (d, φ d)` (Lemma 2.25);
* if `d ∈ rad(A)`, distinguishedness only depends on the ideal `(d)` (Lemma 2.25).

Lemmas 2.23 and 2.24 and the last part of Lemma 2.25 assume `p ∈ rad(A)` in the source; the
proofs here only use it to make `h` a unit, by writing `δ (x * y) = x ^ p * δ y + δ x * φ y`.

The converse in Lemma 2.25 is proved modulo every maximal ideal `m` containing `δ d`, rather than
after a completion as in the source: writing `p = a d + b φ d` gives
`p * (1 - b δ d) = c * d`, and applying `δ` and reducing modulo `m` gives `1 = 0`.

## Main definitions

* `TauCeti.DeltaRing.IsDistinguished p d`: `δ d` is a unit.

## Main results

* `TauCeti.DeltaRing.IsDistinguished.map`: `δ`-maps preserve distinguished elements.
* `TauCeti.DeltaRing.IsDistinguished.natCast_mem_span_frobenius`: `p ∈ (d, φ d)` for distinguished
  `d`.
* `TauCeti.DeltaRing.isDistinguished_natCast_self`: `p` is distinguished when `p ∈ rad(A)`.
* `TauCeti.DeltaRing.IsDistinguished.unit_mul`: unit multiples (Lemma 2.23).
* `TauCeti.DeltaRing.IsDistinguished.of_mul_left` and
  `TauCeti.DeltaRing.IsDistinguished.isUnit_of_mul_right`: the factor lemma (Lemma 2.24).
* `TauCeti.DeltaRing.IsDistinguished.of_dvd`: divisors in the Jacobson radical.
* `TauCeti.DeltaRing.isDistinguished_iff_natCast_mem_span_frobenius` and
  `TauCeti.DeltaRing.isDistinguished_iff_of_span_singleton_eq`: Lemma 2.25.

## References

* B. Bhatt and P. Scholze, *Prisms and prismatic cohomology*, Ann. of Math. 196 (2022),
  Definition 2.19, Example 2.20 (1), Lemmas 2.23–2.25.
-/

public section

namespace TauCeti

namespace DeltaRing

variable {p : ℕ} {A B : Type*} [CommRing A] [CommRing B] [DeltaRing p A] [DeltaRing p B]

variable (p) in
/-- An element `d` of a `δ`-ring is **distinguished** when `δ d` is a unit (Bhatt and Scholze,
*Prisms and prismatic cohomology*, Definition 2.19). -/
def IsDistinguished (d : A) : Prop :=
  IsUnit (delta p d)

/-- Unfolding lemma for `IsDistinguished`. -/
theorem isDistinguished_iff {d : A} : IsDistinguished p d ↔ IsUnit (delta p d) :=
  Iff.rfl

/-- `δ`-maps preserve distinguished elements. -/
theorem IsDistinguished.map {f : A →+* B} (hf : IsDeltaMap p f) {d : A}
    (hd : IsDistinguished p d) : IsDistinguished p (f d) := by
  rw [isDistinguished_iff, ← hf.map_delta]
  exact (isDistinguished_iff.1 hd).map f

variable [hp : Fact p.Prime]

/-- For `x` in the Jacobson radical, `δ (x * y) = x ^ p * δ y + δ x * φ y` is a unit if and only if
`δ x * φ y` is. -/
private theorem isUnit_delta_mul_iff {x y : A} (hxJ : x ∈ Ring.jacobson A) :
    IsUnit (delta p (x * y)) ↔ IsUnit (delta p x * frobenius p A y) := by
  have h : delta p (x * y) = delta p x * frobenius p A y + x ^ p * delta p y := by
    rw [delta_mul, frobenius_apply]
    ring
  rw [h, Ring.isUnit_add_iff_of_mem_jacobson
    (Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hxJ _ hp.out.pos))]

/-- A distinguished element `d` has `p ∈ (d, φ d)`, as `φ d = d ^ p + p * δ d`. -/
theorem IsDistinguished.natCast_mem_span_frobenius {d : A} (hd : IsDistinguished p d) :
    (p : A) ∈ Ideal.span {d, frobenius p A d} := by
  obtain ⟨u, hu⟩ := isDistinguished_iff.1 hd
  have hdp : d ^ (p - 1) * d = d ^ p := pow_sub_one_mul hp.out.ne_zero d
  have hv : (↑u⁻¹ : A) * delta p d = 1 := by rw [← hu, Units.inv_mul]
  refine Ideal.mem_span_pair.2 ⟨-(↑u⁻¹ * d ^ (p - 1)), ↑u⁻¹, ?_⟩
  rw [frobenius_apply]
  linear_combination (-(↑u⁻¹ : A)) * hdp + (p : A) * hv

/-- If `p` lies in the Jacobson radical, then `p` is distinguished: `δ p = 1 - p ^ (p - 1)`
(Bhatt and Scholze, *Prisms and prismatic cohomology*, Example 2.20 (1)). -/
theorem isDistinguished_natCast_self (hpJ : (p : A) ∈ Ring.jacobson A) :
    IsDistinguished p (p : A) := by
  rw [isDistinguished_iff, delta_natCast_self, sub_eq_add_neg,
    Ring.isUnit_add_iff_of_mem_jacobson (neg_mem (Ideal.pow_mem_of_mem _ hpJ _
      (Nat.sub_pos_of_lt hp.out.one_lt)))]
  exact isUnit_one

/-- **Unit multiples of distinguished elements.** If `d` is distinguished and lies in the Jacobson
radical, then `u * d` is distinguished for every unit `u` (Bhatt and Scholze, *Prisms and
prismatic cohomology*, Lemma 2.23, which also assumes `p` in the Jacobson radical). -/
theorem IsDistinguished.unit_mul {d u : A} (hd : IsDistinguished p d) (hu : IsUnit u)
    (hdJ : d ∈ Ring.jacobson A) : IsDistinguished p (u * d) := by
  rw [mul_comm, isDistinguished_iff, isUnit_delta_mul_iff hdJ]
  exact (isDistinguished_iff.1 hd).mul (hu.map (frobenius p A))

/-- **The factor lemma, distinguished factor.** If `f * h` is distinguished and `f` lies in the
Jacobson radical, then `f` is distinguished (Bhatt and Scholze, *Prisms and prismatic cohomology*,
Lemma 2.24, which also assumes `p` in the Jacobson radical). -/
theorem IsDistinguished.of_mul_left {f h : A} (hd : IsDistinguished p (f * h))
    (hfJ : f ∈ Ring.jacobson A) : IsDistinguished p f :=
  isDistinguished_iff.2
    (isUnit_of_mul_isUnit_left ((isUnit_delta_mul_iff hfJ).1 (isDistinguished_iff.1 hd)))

/-- **The factor lemma, unit factor.** If `f * h` is distinguished and `f` and `p` lie in the
Jacobson radical, then `h` is a unit (Bhatt and Scholze, *Prisms and prismatic cohomology*,
Lemma 2.24). -/
theorem IsDistinguished.isUnit_of_mul_right {f h : A} (hd : IsDistinguished p (f * h))
    (hfJ : f ∈ Ring.jacobson A) (hpJ : (p : A) ∈ Ring.jacobson A) : IsUnit h := by
  have hφ := isUnit_of_mul_isUnit_right ((isUnit_delta_mul_iff hfJ).1 (isDistinguished_iff.1 hd))
  rw [frobenius_apply, Ring.isUnit_add_iff_of_mem_jacobson (Ideal.mul_mem_right _ _ hpJ)] at hφ
  exact (isUnit_pow_iff hp.out.ne_zero).1 hφ

/-- A divisor in the Jacobson radical of a distinguished element is distinguished. -/
theorem IsDistinguished.of_dvd {d e : A} (hd : IsDistinguished p d) (hed : e ∣ d)
    (heJ : e ∈ Ring.jacobson A) : IsDistinguished p e := by
  obtain ⟨x, rfl⟩ := hed
  exact hd.of_mul_left heJ

/-- If `p ∈ (d, φ d)` and `d` and `p` lie in the Jacobson radical, then `δ d` lies in no maximal
ideal. -/
private theorem delta_notMem_of_natCast_mem_span {d : A}
    (hspan : (p : A) ∈ Ideal.span {d, frobenius p A d}) (hdJ : d ∈ Ring.jacobson A)
    (hpJ : (p : A) ∈ Ring.jacobson A) (m : Ideal A) [hm : m.IsMaximal] : delta p d ∉ m := by
  intro hδ
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 hspan
  rw [frobenius_apply] at hab
  have hdp : d ^ (p - 1) * d = d ^ p := pow_sub_one_mul hp.out.ne_zero d
  have h1 : (p : A) * (1 - b * delta p d) = (a + b * d ^ (p - 1)) * d := by
    linear_combination -hab - b * hdp
  have hpm : (p : A) ∈ m := Ring.jacobson_le_of_isMaximal m hpJ
  have hdm : d ∈ m := Ring.jacobson_le_of_isMaximal m hdJ
  have hw : 1 - b * delta p d ∉ m := fun h =>
    hm.ne_top ((Ideal.eq_top_iff_one m).2 (by simpa using m.add_mem h (m.mul_mem_left b hδ)))
  refine delta_natCast_mul_notMem hm.isPrime.isRadical hpm hw ?_
  rw [h1, delta_mul]
  exact m.add_mem (m.add_mem (m.mul_mem_left _ hδ)
    (m.mul_mem_right _ (m.pow_mem_of_mem hdm _ hp.out.pos))) (m.mul_mem_left _ hδ)

/-- **Distinguished elements in the Jacobson radical.** If `d` and `p` lie in the Jacobson
radical, then `d` is distinguished if and only if `p ∈ (d, φ d)` (Bhatt and Scholze, *Prisms and
prismatic cohomology*, Lemma 2.25). -/
theorem isDistinguished_iff_natCast_mem_span_frobenius {d : A} (hdJ : d ∈ Ring.jacobson A)
    (hpJ : (p : A) ∈ Ring.jacobson A) :
    IsDistinguished p d ↔ (p : A) ∈ Ideal.span {d, frobenius p A d} := by
  refine ⟨IsDistinguished.natCast_mem_span_frobenius, fun hspan => ?_⟩
  by_contra hd
  rw [isDistinguished_iff] at hd
  obtain ⟨m, hm, hδ⟩ := exists_max_ideal_of_mem_nonunits hd
  exact delta_notMem_of_natCast_mem_span hspan hdJ hpJ m hδ

/-- **Distinguishedness depends only on the ideal.** If `(d) = (e)` and `d` lies in the Jacobson
radical, then `d` is distinguished if and only if `e` is (Bhatt and Scholze, *Prisms and
prismatic cohomology*, Lemma 2.25, which also assumes `p` in the Jacobson radical). -/
theorem isDistinguished_iff_of_span_singleton_eq {d e : A}
    (hde : Ideal.span {d} = Ideal.span {e}) (hdJ : d ∈ Ring.jacobson A) :
    IsDistinguished p d ↔ IsDistinguished p e := by
  have hed : e ∣ d := Ideal.span_singleton_le_span_singleton.1 hde.le
  have hde' : d ∣ e := Ideal.span_singleton_le_span_singleton.1 hde.ge
  have heJ : e ∈ Ring.jacobson A := by
    obtain ⟨x, rfl⟩ := hde'
    exact Ideal.mul_mem_right _ _ hdJ
  exact ⟨fun h => h.of_dvd hed heJ, fun h => h.of_dvd hde' hdJ⟩

end DeltaRing

end TauCeti
