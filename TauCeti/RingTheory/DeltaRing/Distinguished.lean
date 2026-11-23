/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Jacobson.Ideal
public import TauCeti.RingTheory.DeltaRing.Basic

/-!
# Distinguished elements of δ-rings

An element `d` of a `δ`-ring `A` is *distinguished* when `δ d` is a unit. Distinguished elements
are the generators of the ideals of oriented prisms. This file proves the basic properties of
distinguished elements from Bhatt and Scholze, *Prisms and prismatic cohomology*, §2.3, where
`rad(A)` is the Jacobson radical `Ring.jacobson A`:

* `δ`-maps preserve distinguished elements, and a distinguished `d` has `p ∈ (d, φ d)`;
* if `p ∈ rad(A)` then `p` is distinguished, as `δ p = 1 - p ^ (p - 1)`;
* if `d, p ∈ rad(A)`, a unit multiple of a distinguished `d` is distinguished (Lemma 2.23);
* if `f * h` is distinguished and `f, p ∈ rad(A)`, then `f` is distinguished and `h` is a unit
  (Lemma 2.24);
* if `d, p ∈ rad(A)`, then `d` is distinguished if and only if `p ∈ (d, φ d)`, so distinguishedness
  only depends on the ideal `(d)` (Lemma 2.25).

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
* `TauCeti.DeltaRing.IsDistinguished.of_mul` and `TauCeti.DeltaRing.IsDistinguished.isUnit_of_mul`:
  the factor lemma (Lemma 2.24).
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
  exact IsUnit.map f hd

/-- Adding an element of the Jacobson radical does not change being a unit. -/
private theorem isUnit_add_iff_of_mem_jacobson {a j : A} (hj : j ∈ Ring.jacobson A) :
    IsUnit (a + j) ↔ IsUnit a := by
  have key {a j : A} (hj : j ∈ Ring.jacobson A) (ha : IsUnit a) : IsUnit (a + j) := by
    obtain ⟨u, rfl⟩ := ha
    have h := Ring.mem_jacobson_iff.1 hj ↑u⁻¹
    have he : (u : A) + j = (j * ↑u⁻¹ + 1) * u := by
      rw [add_mul, mul_assoc, Units.inv_mul, mul_one, one_mul, add_comm]
    rw [he]
    exact h.mul u.isUnit
  refine ⟨fun h => ?_, key hj⟩
  simpa using key (neg_mem hj) h

variable [hp : Fact p.Prime]

/-- A distinguished element `d` has `p ∈ (d, φ d)`, as `φ d = d ^ p + p * δ d`. -/
theorem IsDistinguished.natCast_mem_span_frobenius {d : A} (hd : IsDistinguished p d) :
    (p : A) ∈ Ideal.span {d, frobenius p A d} := by
  obtain ⟨u, hu⟩ := hd
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
    isUnit_add_iff_of_mem_jacobson (neg_mem (Ideal.pow_mem_of_mem _ hpJ _
      (Nat.sub_pos_of_lt hp.out.one_lt)))]
  exact isUnit_one

/-- **Unit multiples of distinguished elements.** If `d` is distinguished and `d` and `p` lie in
the Jacobson radical, then `u * d` is distinguished for every unit `u` (Bhatt and Scholze,
*Prisms and prismatic cohomology*, Lemma 2.23). -/
theorem IsDistinguished.unit_mul {d u : A} (hd : IsDistinguished p d) (hu : IsUnit u)
    (hdJ : d ∈ Ring.jacobson A) (hpJ : (p : A) ∈ Ring.jacobson A) :
    IsDistinguished p (u * d) := by
  rw [isDistinguished_iff, delta_mul, add_assoc, isUnit_add_iff_of_mem_jacobson]
  · exact (hu.pow p).mul hd
  · refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ ?_) ?_
    · exact Ideal.pow_mem_of_mem _ hdJ _ hp.out.pos
    · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hpJ)

/-- In a factorization `f * h` of a distinguished element with `f` and `p` in the Jacobson
radical, `h ^ p * δ f` is a unit. -/
private theorem IsDistinguished.isUnit_pow_mul_delta {f h : A}
    (hd : IsDistinguished p (f * h)) (hfJ : f ∈ Ring.jacobson A)
    (hpJ : (p : A) ∈ Ring.jacobson A) : IsUnit (h ^ p * delta p f) := by
  rw [isDistinguished_iff, delta_mul, add_comm (f ^ p * _), add_assoc,
    isUnit_add_iff_of_mem_jacobson] at hd
  · exact hd
  · refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ ?_) ?_
    · exact Ideal.pow_mem_of_mem _ hfJ _ hp.out.pos
    · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hpJ)

/-- **The factor lemma, distinguished factor.** If `f * h` is distinguished and `f` and `p` lie in
the Jacobson radical, then `f` is distinguished (Bhatt and Scholze, *Prisms and prismatic
cohomology*, Lemma 2.24). -/
theorem IsDistinguished.of_mul {f h : A} (hd : IsDistinguished p (f * h))
    (hfJ : f ∈ Ring.jacobson A) (hpJ : (p : A) ∈ Ring.jacobson A) : IsDistinguished p f :=
  isUnit_of_mul_isUnit_right (hd.isUnit_pow_mul_delta hfJ hpJ)

/-- **The factor lemma, unit factor.** If `f * h` is distinguished and `f` and `p` lie in the
Jacobson radical, then `h` is a unit (Bhatt and Scholze, *Prisms and prismatic cohomology*,
Lemma 2.24). -/
theorem IsDistinguished.isUnit_of_mul {f h : A} (hd : IsDistinguished p (f * h))
    (hfJ : f ∈ Ring.jacobson A) (hpJ : (p : A) ∈ Ring.jacobson A) : IsUnit h :=
  (isUnit_pow_iff hp.out.ne_zero).1 (isUnit_of_mul_isUnit_left (hd.isUnit_pow_mul_delta hfJ hpJ))

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
  have h2 := congrArg (fun x => Ideal.Quotient.mk m (delta p x)) h1
  have hpm : Ideal.Quotient.mk m (p : A) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ring.jacobson_le_of_isMaximal m hpJ)
  have hdm : Ideal.Quotient.mk m d = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ring.jacobson_le_of_isMaximal m hdJ)
  have hδm : Ideal.Quotient.mk m (delta p d) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hδ
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have hp1 : p - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hp.out.one_lt
  simp only [delta_mul, delta_natCast_self, map_add, map_mul, map_pow, map_sub, map_one, hpm,
    hdm, hδm, mul_zero, sub_zero, one_pow, zero_pow hp0, zero_pow hp1, zero_mul, zero_add,
    add_zero, mul_one] at h2
  exact one_ne_zero h2

/-- **Distinguished elements in the Jacobson radical.** If `d` and `p` lie in the Jacobson
radical, then `d` is distinguished if and only if `p ∈ (d, φ d)` (Bhatt and Scholze, *Prisms and
prismatic cohomology*, Lemma 2.25). -/
theorem isDistinguished_iff_natCast_mem_span_frobenius {d : A} (hdJ : d ∈ Ring.jacobson A)
    (hpJ : (p : A) ∈ Ring.jacobson A) :
    IsDistinguished p d ↔ (p : A) ∈ Ideal.span {d, frobenius p A d} := by
  refine ⟨IsDistinguished.natCast_mem_span_frobenius, fun hspan => ?_⟩
  by_contra hd
  obtain ⟨m, hm, hδ⟩ := exists_max_ideal_of_mem_nonunits hd
  exact delta_notMem_of_natCast_mem_span hspan hdJ hpJ m hδ

/-- Generators of the same principal ideal give the same ideal `(d, φ d)`. -/
private theorem span_frobenius_le_of_mem {d e : A} (hd : d ∈ Ideal.span {e}) :
    Ideal.span {d, frobenius p A d} ≤ Ideal.span {e, frobenius p A e} := by
  obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton'.1 hd
  rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff, map_mul]
  exact ⟨Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)),
    Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))⟩

/-- **Distinguishedness depends only on the ideal.** If `(d) = (e)` and `d` and `p` lie in the
Jacobson radical, then `d` is distinguished if and only if `e` is (Bhatt and Scholze, *Prisms and
prismatic cohomology*, Lemma 2.25). -/
theorem isDistinguished_iff_of_span_singleton_eq {d e : A}
    (hde : Ideal.span {d} = Ideal.span {e}) (hdJ : d ∈ Ring.jacobson A)
    (hpJ : (p : A) ∈ Ring.jacobson A) : IsDistinguished p d ↔ IsDistinguished p e := by
  have heJ : e ∈ Ring.jacobson A := by
    have he : e ∈ Ideal.span {d} := hde ▸ Ideal.mem_span_singleton_self e
    exact (Ideal.span_singleton_le_iff_mem _).2 hdJ he
  have hspan : Ideal.span {d, frobenius p A d} = Ideal.span {e, frobenius p A e} :=
    le_antisymm (span_frobenius_le_of_mem (hde ▸ Ideal.mem_span_singleton_self d))
      (span_frobenius_le_of_mem (hde ▸ Ideal.mem_span_singleton_self e))
  rw [isDistinguished_iff_natCast_mem_span_frobenius hdJ hpJ,
    isDistinguished_iff_natCast_mem_span_frobenius heJ hpJ, hspan]

end DeltaRing

end TauCeti
