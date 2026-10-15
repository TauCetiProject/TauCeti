/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.RamificationInertia.Unramified
import Mathlib.FieldTheory.PurelyInseparable.Tower
import Mathlib.RingTheory.Finiteness.Quotient

/-!
# Unramified primes below an intermediate invariant ring

Let a finite group `G` act on a finite flat extension of domains `B/A`, and let `C` be the
invariant ring of a subgroup `H`. Assume that `B/C` is flat and `C/A` is finite. The prime
of `C` below a maximal prime `P` of `B` is unramified over `A` exactly when `P.inertia G ≤ H`.

No separability of the residue extension of `B/A` is assumed. Over imperfect residue fields,
the relative inertia index measures the product of the ramification index and the inseparable
residue degree of `C/A`, rather than the ramification index alone. Both factors must equal one
for unramifiedness. Quantifying the criterion over primes above a base prime gives the subgroup
condition used to study unramifiedness in composita and normal closures.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §9, Exercise 4.
* The inertia-order and tower argument extends the number-field proof in
  `NumberField.ramificationIdx_under_eq_one_iff_inertia_le` to imperfect residue fields.
-/

public section

open Ideal

namespace TauCeti.RamificationInertia

attribute [local instance] Ideal.Quotient.field

variable (A C : Type*) {B G : Type*}
  [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [CommRing C] [IsDomain C]
  [Algebra A B] [Algebra A C] [Algebra C B] [IsScalarTower A C B]
  [Group G] [MulSemiringAction G B] [IsGaloisGroup G A B]
  [Module.Finite A B] [Module.Flat A B] [Module.Flat C B]
  (H : Subgroup G) [IsGaloisGroup H C B]

/-- The inertia index below an intermediate invariant ring is the ramification index times
the inseparable residue degree. This holds even when the upper residue extension is inseparable. -/
theorem ramificationIdx_under_mul_finInsepDegree_eq_relIndex_inertia
    (p : Ideal A) [p.IsMaximal] {P : Ideal B} [P.IsMaximal] [P.LiesOver p] :
    let := Module.Finite.right A C B
    (P.under C).ramificationIdx A *
        Field.finInsepDegree (A ⧸ p) (C ⧸ P.under C) =
      H.relIndex (P.inertia G) := by
  have : Finite G := IsGaloisGroup.finite G A B
  let := Module.Finite.right A C B
  have : (P.under C).LiesOver p := LiesOver.tower_bot P (P.under C) p
  let _ : IsScalarTower (A ⧸ p) (C ⧸ P.under C) (B ⧸ P) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      simp only [RingHom.comp_apply, Ideal.Quotient.algebraMap_mk_of_liesOver]
      rw [IsScalarTower.algebraMap_apply A C B])
  have : Algebra.IsAlgebraic (A ⧸ p) (C ⧸ P.under C) :=
    .tower_bot _ _ (B ⧸ P)
  have hcard : Nat.card (P.inertia G ⊓ H : Subgroup G) =
      P.ramificationIdx C * Field.finInsepDegree (C ⧸ P.under C) (B ⧸ P) := by
    rw [← AddSubgroup.inertia_map_subtype,
      ← Nat.card_congr (Subgroup.equivMapOfInjective (P.inertia H) H.subtype
        H.subtype_injective).toEquiv]
    exact card_inertia_eq_ramificationIdx_mul_finInsepDegree (R := C) (G := H) P
  have hidx := H.relIndex_mul_card (P.inertia G)
  rw [inf_comm, hcard,
    card_inertia_eq_ramificationIdxIn_mul_finInsepDegree (G := G) p P,
    ramificationIdxIn_eq_ramificationIdx p P G] at hidx
  have htower :
      ((P.under C).ramificationIdx A *
          Field.finInsepDegree (A ⧸ p) (C ⧸ P.under C)) *
        (P.ramificationIdx C * Field.finInsepDegree (C ⧸ P.under C) (B ⧸ P)) =
      P.ramificationIdx A * Field.finInsepDegree (A ⧸ p) (B ⧸ P) := by
    rw [ramificationIdx_tower (R := A) (P.under C) P,
      ← Field.finInsepDegree_mul_finInsepDegree_of_isAlgebraic
        (A ⧸ p) (C ⧸ P.under C) (B ⧸ P)]
    ring
  exact Nat.eq_of_mul_eq_mul_right
    (Nat.mul_pos (ramificationIdx_pos C P)
      (NeZero.pos (Field.finInsepDegree (C ⧸ P.under C) (B ⧸ P))))
    (htower.trans hidx.symm)

variable [Module.Finite A C]

/-- A prime below an intermediate invariant ring is unramified exactly when its inertia group
fixes that ring. No residue-separability hypothesis is needed. -/
theorem isUnramifiedAt_under_iff_inertia_le {P : Ideal B} [P.IsMaximal] :
    Algebra.IsUnramifiedAt A (P.under C) ↔ P.inertia G ≤ H := by
  let := Module.Finite.right A C B
  let := Localization.AtPrime.algebraOfLiesOver ((P.under C).under A) (P.under C)
  rw [← Subgroup.relIndex_eq_one,
    ← ramificationIdx_under_mul_finInsepDegree_eq_relIndex_inertia A C H
      ((P.under C).under A),
    mul_eq_one, isUnramifiedAt_iff_ramificationIdx_eq_one_and_isSeparable_residueField,
    Algebra.isSeparable_residueField_iff]
  rw [isSeparable_iff_finInsepDegree_eq_one]

/-- A maximal prime of the base is unramified in an intermediate invariant ring exactly when
all inertia groups above it fix that ring. This criterion includes imperfect residue fields. -/
theorem isUnramifiedIn_iff_forall_inertia_le (p : Ideal A) [p.IsMaximal] :
    Algebra.IsUnramifiedIn C p ↔ ∀ P ∈ p.primesOver B, P.inertia G ≤ H := by
  constructor
  · intro h P hP
    have : P.IsPrime := hP.1
    have : P.LiesOver p := hP.2
    have : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P p
    have : (P.under C).LiesOver p := LiesOver.tower_bot P (P.under C) p
    exact (isUnramifiedAt_under_iff_inertia_le A C H).mp
      (h (P.under C) inferInstance inferInstance)
  · intro h q hq hqp
    have : q.IsPrime := hq
    have : q.LiesOver p := hqp
    let := Module.Finite.right A C B
    obtain ⟨⟨P, hP, hPq⟩⟩ := q.nonempty_primesOver (S := B)
    have : P.IsPrime := hP
    have : P.LiesOver q := hPq
    have : P.LiesOver p := LiesOver.trans P q p
    have : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P p
    have hu := (isUnramifiedAt_under_iff_inertia_le A C H (P := P)).mpr
      (h P ⟨inferInstance, inferInstance⟩)
    simpa only [← over_def P q] using hu

end TauCeti.RamificationInertia
