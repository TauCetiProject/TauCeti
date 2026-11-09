/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Rückert's descent along polynomial-like ring maps

This file develops the abstract descent principle of Bosch, Güntzer and Remmert, §5.2.5, which
transfers the noetherian, factorial and Jacobson properties from a ring `A` to a ring `B`
receiving an injective map `φ : A[X] →+* B` that behaves like the inclusion of polynomials into
restricted power series.

The hypotheses (`RingHom.IsRueckert`) concern a set `W` of monic polynomials, closed under
taking monic factors, such that

* for every `w ∈ W`, the map `φ` induces an isomorphism `A[X] ⧸ (w) ≃+* B ⧸ (φ w)`
  (`RingHom.IsRueckert.quotientEquiv`), and
* every nonzero `b : B` becomes a unit multiple of some `φ w` after a ring automorphism of `B`.

For a Tate algebra `A = K⟨X₁, …, Xₙ⟩` and `B = A⟨Y⟩`, the polynomials `W` are the
Weierstrass polynomials: the quotient comparison is Weierstrass division, and the automorphisms
are the changes of variables making a series distinguished, followed by Weierstrass preparation.

The quotient comparison descends every quotient of `B` by a nonzero ideal, after an automorphism,
to a quotient of some `A[X] ⧸ (w)`, which is finite over `A` because `w` is monic
(`RingHom.IsRueckert.exists_finite_quotient`). Consequently:

* `RingHom.IsRueckert.isNoetherianRing`: if `A` is noetherian, so is `B`;
* `RingHom.IsRueckert.uniqueFactorizationMonoid`: if `A` is a unique factorisation domain and `B`
  is a domain, then `B` is a unique factorisation domain. Each `φ w` is a product of primes,
  because a monic factorisation of `w` in the factorial ring `A[X]` stays in `W`, and an
  irreducible `w ∈ W` generates a prime ideal whose quotient is identified with `B ⧸ (φ w)`;
* `RingHom.IsRueckert.isJacobsonRing`: if `A` is a Jacobson ring and the Jacobson radical of `B`
  is zero, then `B` is a Jacobson ring. Indeed every nonzero prime of `B` is the intersection of
  the maximal ideals containing it (`RingHom.IsRueckert.jacobson_eq_self`): it contains some
  nonzero `b`, and `B ⧸ (b)` is isomorphic to the Jacobson ring `A[X] ⧸ (w)`. The condition on
  the Jacobson radical cannot be dropped: for a domain `B` it is necessary
  (`RingHom.IsRueckert.isJacobsonRing_iff_jacobson_eq_bot`).

## Main definitions

* `RingHom.IsRueckert φ W`: the Rückert hypotheses for `φ : A[X] →+* B` and `W ⊆ A[X]`.
* `RingHom.IsRueckert.quotientEquiv`: the ring isomorphism `A[X] ⧸ (w) ≃+* B ⧸ (φ w)` induced by
  `φ`, for `w ∈ W`.

## References

* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, §5.2.5.
-/

public section

open Polynomial

namespace RingHom

variable {A B : Type*} [CommRing A] [CommRing B]

/-- **The Rückert hypotheses** for an injective ring map `φ : A[X] →+* B` and a set `W` of monic
polynomials closed under taking monic factors: for each `w ∈ W`, the map `φ` induces an
isomorphism `A[X] ⧸ (w) ≃+* B ⧸ (φ w)` (the divisibility and remainder conditions below), and
every nonzero element of `B` is mapped by some ring automorphism of `B` to a unit multiple of
`φ w` for some `w ∈ W`. -/
structure IsRueckert (φ : A[X] →+* B) (W : Set A[X]) : Prop where
  /-- The map `φ` is injective. -/
  injective : Function.Injective φ
  /-- Every member of `W` is monic. -/
  monic {w : A[X]} (hw : w ∈ W) : w.Monic
  /-- Monic factors of members of `W` belong to `W`. -/
  mem_of_dvd {w p : A[X]} (hw : w ∈ W) (hp : p.Monic) (hpw : p ∣ w) : p ∈ W
  /-- Divisibility by `w ∈ W` is detected after applying `φ`: the induced map
  `A[X] ⧸ (w) → B ⧸ (φ w)` is injective. -/
  dvd_iff {w : A[X]} (hw : w ∈ W) (p : A[X]) : φ w ∣ φ p ↔ w ∣ p
  /-- Every element of `B` is congruent to an element of the image of `φ` modulo `φ w` for
  `w ∈ W`: the induced map `A[X] ⧸ (w) → B ⧸ (φ w)` is surjective. -/
  exists_dvd_sub {w : A[X]} (hw : w ∈ W) (b : B) : ∃ p : A[X], φ w ∣ b - φ p
  /-- Every nonzero element of `B` is, after a ring automorphism, a unit multiple of `φ w` for
  some `w ∈ W`. -/
  exists_mul_eq {b : B} (hb : b ≠ 0) : ∃ (α : B ≃+* B) (u : Bˣ), ∃ w ∈ W, u * α b = φ w

namespace IsRueckert

variable {φ : A[X] →+* B} {W : Set A[X]} (h : φ.IsRueckert W)
include h

private theorem ker_comp_mk {w : A[X]} (hw : w ∈ W) :
    ker ((Ideal.Quotient.mk (Ideal.span {φ w})).comp φ) = Ideal.span {w} := by
  ext p
  simp [mem_ker, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, h.dvd_iff hw]

private theorem surjective_comp_mk {w : A[X]} (hw : w ∈ W) :
    Function.Surjective ((Ideal.Quotient.mk (Ideal.span {φ w})).comp φ) := by
  intro x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨p, hp⟩ := h.exists_dvd_sub hw b
  exact ⟨p, (Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr hp)).symm⟩

/-- For `w ∈ W`, the map `φ` induces a ring isomorphism `A[X] ⧸ (w) ≃+* B ⧸ (φ w)`. -/
noncomputable def quotientEquiv {w : A[X]} (hw : w ∈ W) :
    A[X] ⧸ Ideal.span {w} ≃+* B ⧸ Ideal.span {φ w} :=
  (Ideal.quotEquivOfEq (h.ker_comp_mk hw).symm).trans
    (quotientKerEquivOfSurjective (h.surjective_comp_mk hw))

/-- The quotient comparison sends the class of a polynomial to the class of its image. -/
@[simp]
theorem quotientEquiv_mk {w : A[X]} (hw : w ∈ W) (p : A[X]) :
    h.quotientEquiv hw (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (φ p) :=
  (rfl)

/-- The quotient of `B` by a nonzero principal ideal is isomorphic to `A[X] ⧸ (w)` for some
`w ∈ W`. -/
theorem exists_nonempty_ringEquiv_quotient_span_singleton {b : B} (hb : b ≠ 0) :
    ∃ w ∈ W, Nonempty (A[X] ⧸ Ideal.span {w} ≃+* B ⧸ Ideal.span {b}) := by
  obtain ⟨α, u, w, hw, hu⟩ := h.exists_mul_eq hb
  have hspan : Ideal.span {φ w} = (Ideal.span {b}).map (α : B →+* B) := by
    rw [Ideal.map_span, Set.image_singleton, ← hu, Ideal.span_singleton_mul_left_unit u.isUnit,
      RingEquiv.coe_toRingHom]
  exact ⟨w, hw, ⟨(h.quotientEquiv hw).trans (Ideal.quotientEquiv _ _ α hspan).symm⟩⟩

/-- **Finite-quotient descent.** For every nonzero ideal `I` of `B` there is a ring automorphism
`α` of `B` such that `B ⧸ α(I)` is finite over `A`, through `A → A[X] → B`. -/
theorem exists_finite_quotient {I : Ideal B} (hI : I ≠ ⊥) :
    ∃ α : B ≃+* B, ((Ideal.Quotient.mk (I.map α)).comp (φ.comp C)).Finite := by
  obtain ⟨b, hbI, hb⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨α, u, w, hw, hu⟩ := h.exists_mul_eq hb
  have hle : Ideal.span {φ w} ≤ I.map α := by
    rw [Ideal.span_singleton_le_iff_mem, ← hu]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem α hbI)
  have hfin : (algebraMap A (A[X] ⧸ Ideal.span {w})).Finite :=
    finite_algebraMap.mpr (h.monic hw).finite_quotient
  refine ⟨α, ?_⟩
  have he := Finite.of_surjective (h.quotientEquiv hw).toRingHom (h.quotientEquiv hw).surjective
  convert ((Finite.of_surjective _ (Ideal.Quotient.factor_surjective hle)).comp he).comp hfin
    using 1
  ext a
  simp [← Ideal.Quotient.mk_algebraMap, Polynomial.algebraMap_eq]

/-- **Rückert's noetherian descent.** If `A` is noetherian, so is `B`. -/
theorem isNoetherianRing [IsNoetherianRing A] : IsNoetherianRing B := by
  rw [isNoetherianRing_iff_ideal_fg]
  intro I
  rcases eq_or_ne I ⊥ with rfl | hI
  · exact Submodule.fg_bot
  obtain ⟨b, hbI, hb⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨w, -, ⟨e⟩⟩ := h.exists_nonempty_ringEquiv_quotient_span_singleton hb
  have : IsNoetherianRing (B ⧸ Ideal.span {b}) := isNoetherianRing_of_ringEquiv _ e
  refine Ideal.fg_of_fg_map_of_fg_inf_ker_of_surjective
    ((isNoetherianRing_iff_ideal_fg _).mp this _) ?_ Ideal.Quotient.mk_surjective
  rw [Ideal.mk_ker, inf_eq_right.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hbI)]
  exact Submodule.fg_span_singleton b

/-- The image of a prime member of `W` is prime. -/
theorem prime_apply {w : A[X]} (hw : w ∈ W) (hp : Prime w) : Prime (φ w) := by
  have hw0 : φ w ≠ 0 := (map_ne_zero_iff φ h.injective).mpr hp.ne_zero
  have : IsDomain (A[X] ⧸ Ideal.span {w}) :=
    (Ideal.Quotient.isDomain_iff_prime _).mpr ((Ideal.span_singleton_prime hp.ne_zero).mpr hp)
  rw [← Ideal.span_singleton_prime hw0, ← Ideal.Quotient.isDomain_iff_prime]
  exact (h.quotientEquiv hw).symm.toMulEquiv.isDomain _

/-- Over a unique factorisation domain `A`, the image of every member of `W` is associated to a
product of primes. -/
theorem exists_prime_factors_apply [IsDomain A] [UniqueFactorizationMonoid A] {w : A[X]}
    (hw : w ∈ W) : ∃ f : Multiset B, (∀ b ∈ f, Prime b) ∧ Associated f.prod (φ w) := by
  induction hn : w.natDegree using Nat.strong_induction_on generalizing w with
  | _ n ih =>
  have hm := h.monic hw
  by_cases hirr : Irreducible w
  · exact ⟨{φ w}, by simpa using h.prime_apply hw hirr.prime, by simp⟩
  rcases eq_or_ne w 1 with rfl | hw1
  · exact ⟨0, by simp, by simp⟩
  -- A reducible monic member of `W` is a product of two monic members of positive degree.
  obtain ⟨f, g, hf, hg, rfl, hf0, hg0⟩ : ∃ f g : A[X], f.Monic ∧ g.Monic ∧ f * g = w ∧
      f.natDegree ≠ 0 ∧ g.natDegree ≠ 0 := by
    simpa [hm.irreducible_iff_natDegree, hw1, not_or] using hirr
  have hdeg := hf.natDegree_mul hg
  obtain ⟨F, hF, hFf⟩ := ih f.natDegree (by omega)
    (h.mem_of_dvd hw hf (dvd_mul_right f g)) rfl
  obtain ⟨G, hG, hGg⟩ := ih g.natDegree (by omega)
    (h.mem_of_dvd hw hg (dvd_mul_left g f)) rfl
  refine ⟨F + G, fun b hb ↦ (Multiset.mem_add.mp hb).elim (hF b) (hG b), ?_⟩
  rw [Multiset.prod_add, map_mul]
  exact hFf.mul_mul hGg

/-- **Rückert's factorial descent.** If `A` is a unique factorisation domain and `B` is a domain,
then `B` is a unique factorisation domain. -/
theorem uniqueFactorizationMonoid [IsDomain A] [UniqueFactorizationMonoid A] [IsDomain B] :
    UniqueFactorizationMonoid B := by
  refine UniqueFactorizationMonoid.of_exists_prime_factors fun b hb ↦ ?_
  obtain ⟨α, u, w, hw, hu⟩ := h.exists_mul_eq hb
  obtain ⟨f, hf, hfw⟩ := h.exists_prime_factors_apply hw
  refine ⟨f.map α.symm, fun c hc ↦ ?_, ?_⟩
  · obtain ⟨d, hd, rfl⟩ := Multiset.mem_map.mp hc
    exact (MulEquiv.prime_iff α.symm.toMulEquiv).mpr (hf d hd)
  · rw [← map_multiset_prod]
    refine (hfw.map α.symm).trans ?_
    rw [← hu, map_mul, RingEquiv.symm_apply_apply]
    exact associated_unit_mul_left b _ (u.isUnit.map α.symm)

/-- Over a Jacobson ring `A`, every nonzero prime ideal of `B` is the intersection of the maximal
ideals containing it. -/
theorem jacobson_eq_self [IsJacobsonRing A] {P : Ideal B} (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    P.jacobson = P := by
  obtain ⟨b, hbP, hb⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  obtain ⟨w, -, ⟨e⟩⟩ := h.exists_nonempty_ringEquiv_quotient_span_singleton hb
  have : IsJacobsonRing (B ⧸ Ideal.span {b}) :=
    isJacobsonRing_of_surjective ⟨e.toRingHom, e.surjective⟩
  have hle : Ideal.span {b} ≤ P := (Ideal.span_singleton_le_iff_mem _).mpr hbP
  have : IsJacobsonRing (B ⧸ P) :=
    isJacobsonRing_of_surjective ⟨_, Ideal.Quotient.factor_surjective hle⟩
  have : IsDomain (B ⧸ P) := (Ideal.Quotient.isDomain_iff_prime P).mpr hP
  rw [Ideal.jacobson_eq_iff_jacobson_quotient_eq_bot, ← Ideal.jacobson_bot]
  exact IsJacobsonRing.out' ⊥ Ideal.isPrime_bot.isRadical

/-- **Rückert's Jacobson descent.** If `A` is a Jacobson ring and the Jacobson radical of `B` is
zero, then `B` is a Jacobson ring. -/
theorem isJacobsonRing [IsJacobsonRing A] (hB : Ring.jacobson B = ⊥) : IsJacobsonRing B := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  rcases eq_or_ne P ⊥ with rfl | hP0
  · rw [Ideal.jacobson_bot, hB]
  · exact h.jacobson_eq_self hP hP0

/-- For a domain `B` over a Jacobson ring `A`, the ring `B` is Jacobson exactly when its Jacobson
radical is zero. -/
theorem isJacobsonRing_iff_jacobson_eq_bot [IsJacobsonRing A] [IsDomain B] :
    IsJacobsonRing B ↔ Ring.jacobson B = ⊥ :=
  ⟨fun _ ↦ by rw [← Ideal.jacobson_bot]; exact IsJacobsonRing.out' ⊥ Ideal.isPrime_bot.isRadical,
    h.isJacobsonRing⟩

end IsRueckert

end RingHom
