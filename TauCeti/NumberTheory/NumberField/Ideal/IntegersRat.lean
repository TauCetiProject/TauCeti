/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Frobenius
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.RamificationInertia.Ramification
import TauCeti.RingTheory.Ideal.Norm.AbsNorm

/-!
# Local invariants over `ℤ` and over `𝓞 ℚ`

The ring of integers of `ℚ` is `ℤ` (`Rat.ringOfIntegersEquiv`), but the two are different
types, and the local invariants of a prime `P` of a number field `E` can be taken relative to
either base ring: the residue degree `P.inertiaDeg ℤ` or `P.inertiaDeg (𝓞 ℚ)`, the ramification
index `P.ramificationIdx ℤ` or `P.ramificationIdx (𝓞 ℚ)`, and the arithmetic Frobenius condition
`IsArithFrobAt ℤ σ P` or `IsArithFrobAt (𝓞 ℚ) σ P`. Statements about number fields over `ℚ` as
a base *field* naturally produce the `𝓞 ℚ` versions, while statements about rational primes
produce the `ℤ` versions. This file proves that they agree.

The residue degrees are compared through the absolute norm, `absNorm (P.under R) ^ f = absNorm P`
for both base rings, since the ideal of `𝓞 ℚ` below `P` is the image of the ideal of `ℤ` below
`P` under the structure map. The ramification indices are compared as multiplicities of `P` in
the extension of the prime below, and the Frobenius conditions only involve the size of the
residue field below `P`. The comparison lemmas are `simp` lemmas oriented towards the `ℤ` forms.

## Main results

* `Ideal.under_ringOfIntegers_rat_eq_map`: the ideal of `𝓞 ℚ` below `P` is the image of the ideal
  of `ℤ` below `P`.
* `Ideal.inertiaDeg_ringOfIntegers_rat_eq_int`: the residue degrees over `𝓞 ℚ` and over `ℤ`
  agree.
* `Ideal.ramificationIdx_ringOfIntegers_rat_eq_int`: the ramification indices over `𝓞 ℚ` and over
  `ℤ` agree.
* `Ideal.isArithFrobAt_ringOfIntegers_rat_iff`: the Frobenius conditions over `𝓞 ℚ` and over `ℤ`
  agree.
* `Ideal.primesOver_under_ringOfIntegers_rat_eq`: for a prime `Q` above the rational prime `p`,
  the primes of a subfield above `Q ∩ 𝓞 ℚ` are the primes above `p`.
-/

public section

open scoped NumberField

namespace Ideal

variable {E : Type*} [Field E] [NumberField E]

/-- The structure map `ℤ → 𝓞 ℚ` is the inverse of `Rat.ringOfIntegersEquiv`. -/
theorem _root_.Rat.algebraMap_int_ringOfIntegers_eq :
    algebraMap ℤ (𝓞 ℚ) = (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) :=
  (RingHom.eq_intCast' _).trans (RingHom.eq_intCast' _).symm

/-- The ideal of `𝓞 ℚ` below an ideal `P` of `𝓞 E` is the image of the ideal of `ℤ` below `P`. -/
-- Not a `simp` lemma: it would rewrite the left-hand sides of `absNorm_under_ringOfIntegers_rat`
-- and `card_quot_under_ringOfIntegers_rat` out of simp normal form (`simpNF`).
theorem under_ringOfIntegers_rat_eq_map (P : Ideal (𝓞 E)) :
    P.under (𝓞 ℚ) = (P.under ℤ).map (algebraMap ℤ (𝓞 ℚ)) := by
  have : IsScalarTower ℤ (𝓞 ℚ) (𝓞 E) :=
    IsScalarTower.of_algebraMap_eq' ((RingHom.eq_intCast' _).trans (RingHom.eq_intCast' _).symm)
  rw [← under_under (A := ℤ) (B := 𝓞 ℚ) P]
  exact (map_comap_of_surjective _
    (Rat.algebraMap_int_ringOfIntegers_eq ▸ Rat.ringOfIntegersEquiv.symm.surjective) _).symm

/-- The absolute norm of the ideal of `𝓞 ℚ` below `P` is that of the ideal of `ℤ` below `P`. -/
@[simp]
theorem absNorm_under_ringOfIntegers_rat (P : Ideal (𝓞 E)) :
    absNorm (P.under (𝓞 ℚ)) = absNorm (P.under ℤ) := by
  rw [under_ringOfIntegers_rat_eq_map, Rat.algebraMap_int_ringOfIntegers_eq]
  exact absNorm_map_of_ringEquiv Rat.ringOfIntegersEquiv.symm _

/-- The residue rings of `𝓞 ℚ` and of `ℤ` below `P` have the same number of elements. -/
@[simp]
theorem card_quot_under_ringOfIntegers_rat (P : Ideal (𝓞 E)) :
    Nat.card (𝓞 ℚ ⧸ P.under (𝓞 ℚ)) = Nat.card (ℤ ⧸ P.under ℤ) := by
  rw [← Submodule.cardQuot_apply, ← Submodule.cardQuot_apply, ← absNorm_apply, ← absNorm_apply,
    absNorm_under_ringOfIntegers_rat]

/-- **Frobenius elements over `𝓞 ℚ` and over `ℤ` are the same.** An element `σ` is an arithmetic
Frobenius at `Q` relative to the base ring `𝓞 ℚ` exactly when it is one relative to `ℤ`: the
defining congruence only involves the size of the residue field below `Q`, which is the same
for both base rings. -/
@[simp]
theorem isArithFrobAt_ringOfIntegers_rat_iff {G : Type*} [Group G] [MulSemiringAction G (𝓞 E)]
    [SMulCommClass G ℤ (𝓞 E)] [SMulCommClass G (𝓞 ℚ) (𝓞 E)] (σ : G) (Q : Ideal (𝓞 E)) :
    IsArithFrobAt (𝓞 ℚ) σ Q ↔ IsArithFrobAt ℤ σ Q := by
  simp only [IsArithFrobAt, AlgHom.IsArithFrobAt, MulSemiringAction.toAlgHom_apply,
    card_quot_under_ringOfIntegers_rat]

/-- **The residue degree over `ℤ` is the residue degree over `𝓞 ℚ`.** -/
@[simp]
theorem inertiaDeg_ringOfIntegers_rat_eq_int (P : Ideal (𝓞 E)) [P.IsPrime] (hP : P ≠ ⊥) :
    P.inertiaDeg (𝓞 ℚ) = P.inertiaDeg ℤ := by
  have h1 := absNorm_pow_inertiaDeg (P.under ℤ) P
  have h2 := absNorm_pow_inertiaDeg (P.under (𝓞 ℚ)) P
  rw [absNorm_under_ringOfIntegers_rat] at h2
  have hne : P.under ℤ ≠ ⊥ := under_ne_bot ℤ hP
  have htop : P.under ℤ ≠ ⊤ := (IsPrime.under ℤ P).ne_top
  have h2le : 2 ≤ absNorm (P.under ℤ) := by
    by_contra h
    interval_cases hn : absNorm (P.under ℤ)
    · exact hne (absNorm_eq_zero_iff.mp hn)
    · exact htop (absNorm_eq_one_iff.mp hn)
  exact Nat.pow_right_injective h2le (h2.trans h1.symm)

/-- **The ramification index over `ℤ` is the ramification index over `𝓞 ℚ`.** -/
@[simp]
theorem ramificationIdx_ringOfIntegers_rat_eq_int (P : Ideal (𝓞 E)) [P.IsPrime] (hP : P ≠ ⊥) :
    P.ramificationIdx (𝓞 ℚ) = P.ramificationIdx ℤ := by
  have : IsScalarTower ℤ (𝓞 ℚ) (𝓞 E) :=
    IsScalarTower.of_algebraMap_eq' ((RingHom.eq_intCast' _).trans (RingHom.eq_intCast' _).symm)
  have hne : P.under ℤ ≠ ⊥ := under_ne_bot ℤ hP
  have hne' : P.under (𝓞 ℚ) ≠ ⊥ := under_ne_bot (𝓞 ℚ) hP
  rw [IsDedekindDomain.ramificationIdx_eq_multiplicity (p := P.under (𝓞 ℚ)) (q := P)
      (map_ne_bot_of_ne_bot hne'),
    IsDedekindDomain.ramificationIdx_eq_multiplicity (p := P.under ℤ) (q := P)
      (map_ne_bot_of_ne_bot hne),
    under_ringOfIntegers_rat_eq_map, map_map, ← IsScalarTower.algebraMap_eq]

/-- The primes of a subfield above `Q ∩ 𝓞 ℚ` are the primes above `p`, when `Q` lies over the
rational prime `p`. -/
-- Not a `simp` lemma: `p` occurs only in the `LiesOver` instance and on the right-hand side, so
-- the `simpNF` linter reports that `simp` could never infer it.
theorem primesOver_under_ringOfIntegers_rat_eq {M : Type*} [Field M] [NumberField M] {p : ℕ}
    (Q : Ideal (𝓞 M)) [Q.LiesOver (Ideal.span {(p : ℤ)})] (E : IntermediateField ℚ M) :
    (Q.under (𝓞 ℚ)).primesOver (𝓞 E) = (Ideal.span {(p : ℤ)}).primesOver (𝓞 E) := by
  have : IsScalarTower ℤ (𝓞 ℚ) (𝓞 E) :=
    IsScalarTower.of_algebraMap_eq' ((RingHom.eq_intCast' _).trans (RingHom.eq_intCast' _).symm)
  have : IsScalarTower ℤ (𝓞 ℚ) (𝓞 M) :=
    IsScalarTower.of_algebraMap_eq' ((RingHom.eq_intCast' _).trans (RingHom.eq_intCast' _).symm)
  ext 𝔮
  simp only [Ideal.primesOver, Set.mem_ofPred_eq]
  refine and_congr_right fun _ => ⟨fun h => ⟨?_⟩, fun h => ⟨?_⟩⟩
  · rw [Ideal.over_def (P := Q) (p := Ideal.span {(p : ℤ)}),
      ← Ideal.under_under (A := ℤ) (B := 𝓞 ℚ) Q, h.over, Ideal.under_under]
  · rw [under_ringOfIntegers_rat_eq_map, under_ringOfIntegers_rat_eq_map, ← h.over,
      ← Ideal.over_def (P := Q) (p := Ideal.span {(p : ℤ)})]

end Ideal
