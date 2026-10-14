/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Subgroup.Pointwise
public import TauCeti.NumberTheory.RamificationInertia.ResidueSeparable
public import TauCeti.NumberTheory.RamificationInertia.SeparableDegree
public import TauCeti.RingTheory.Ideal.Pointwise

/-!
# Ramification indices below an intermediate invariant ring

Let a finite group `G` act on a finite flat extension of domains `B/A`, with invariant
ring `A`, and let `C` be the invariant ring of a subgroup `H`. Assume also that `B/C`
is flat. At a maximal ideal `P` of `B` with separable residue extension over `A`,
the ramification index of `P ∩ C` over `A` is
`[I(P) : I(P) ∩ H]`. In particular that index is one exactly when `I(P) ≤ H`.
This supplies the inertia part of the splitting dictionary for non-Galois intermediate rings.

The division-free tower formula needs only that `H` is the Galois group of `B/C` and
that its residue extension is separable; the base ring need not be a domain. The index
formula additionally uses the invariant extension `B/A`. Residue separability is essential:
without it the inertia order is the ramification index times the inseparable residue degree.
The translated formulas apply the same description throughout the group orbit of a selected
prime, while requiring separability only at that prime.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §9.
* G. J. Janusz, *Algebraic Number Fields*, Chapter I.
* These results generalize Tau Ceti's `NumberField.ramificationIdx_under_eq_one_iff_inertia_le`
  in `TauCeti/NumberTheory/NumberField/Inertia.lean` to intermediate invariant rings.
-/

public section

open scoped Pointwise

namespace Ideal

attribute [local instance] Ideal.Quotient.field

variable {A B G : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [Group G] [MulSemiringAction G B]

/-- The ramification index below an intermediate invariant ring, multiplied by the order
of the inertia subgroup fixing that ring, is the ramification index over the base.
Only the residue extension above the intermediate ring needs to be separable. -/
theorem ramificationIdx_under_mul_card_inertia_inf (P : Ideal B) [P.IsMaximal]
    (H : Subgroup G) (C : Type*) [CommRing C] [IsDomain C] [IsDomain B]
    [Algebra A C] [Algebra C B] [IsScalarTower A C B]
    [IsGaloisGroup H C B] [Module.Finite C B] [Module.Flat C B]
    [Algebra.IsSeparable (C ⧸ P.under C) (B ⧸ P)] :
    (P.under C).ramificationIdx A * Nat.card (P.inertia G ⊓ H : Subgroup G) =
      P.ramificationIdx A := by
  have : Finite H := IsGaloisGroup.finite H C B
  have hcard : Nat.card (P.inertia G ⊓ H : Subgroup G) = P.ramificationIdx C := by
    rw [← AddSubgroup.inertia_map_subtype,
      ← Nat.card_congr (Subgroup.equivMapOfInjective (P.inertia H) H.subtype
        H.subtype_injective).toEquiv]
    exact card_inertia_eq_ramificationIdx_of_isSeparable (G := H) P
  rw [hcard, ramificationIdx_tower (R := A) (P.under C) P]

variable [IsDomain A] [IsDomain B] [IsGaloisGroup G A B]
  [Module.Finite A B] [Module.Flat A B]

/-- The ramification index below an intermediate invariant ring is the relative index
of its fixing subgroup in inertia. Separability is required only at the selected prime. -/
theorem ramificationIdx_under_eq_relIndex_inertia (P : Ideal B) [P.IsMaximal]
    (H : Subgroup G) (C : Type*) [CommRing C] [IsDomain C]
    [Algebra A C] [Algebra C B] [IsScalarTower A C B]
    [IsGaloisGroup H C B] [Module.Flat C B]
    [Algebra.IsSeparable (A ⧸ P.under A) (B ⧸ P)] :
    (P.under C).ramificationIdx A = H.relIndex (P.inertia G) := by
  have : Finite G := IsGaloisGroup.finite G A B
  have : Module.Finite C B := Module.Finite.right A C B
  have : (P.under C).LiesOver (P.under A) := LiesOver.tower_bot P (P.under C) (P.under A)
  have : IsScalarTower (A ⧸ P.under A) (C ⧸ P.under C) (B ⧸ P) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      simp only [RingHom.comp_apply, Ideal.Quotient.algebraMap_mk_of_liesOver]
      rw [IsScalarTower.algebraMap_apply A C B])
  have : Algebra.IsSeparable (C ⧸ P.under C) (B ⧸ P) :=
    Algebra.isSeparable_tower_top_of_isSeparable (A ⧸ P.under A) _ _
  have hmul := ramificationIdx_under_mul_card_inertia_inf (A := A) P H C
  have hidx := H.relIndex_mul_card (P.inertia G)
  rw [inf_comm, card_inertia_eq_ramificationIdx_of_isSeparable (R := A) (G := G) P,
    ← hmul] at hidx
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hidx.symm

/-- The prime below `P` in an intermediate invariant ring has ramification index one
exactly when every inertia element fixes that ring. -/
theorem ramificationIdx_under_eq_one_iff_inertia_le (P : Ideal B) [P.IsMaximal]
    (H : Subgroup G) (C : Type*) [CommRing C] [IsDomain C]
    [Algebra A C] [Algebra C B] [IsScalarTower A C B]
    [IsGaloisGroup H C B] [Module.Flat C B]
    [Algebra.IsSeparable (A ⧸ P.under A) (B ⧸ P)] :
    (P.under C).ramificationIdx A = 1 ↔ P.inertia G ≤ H := by
  have : Finite G := IsGaloisGroup.finite G A B
  rw [ramificationIdx_under_eq_relIndex_inertia P H C, Subgroup.relIndex_eq_one]

variable [SMulCommClass G A B]

/-- The ramification index below a translate of `Q` is the relative index of the conjugate
inertia group. Separability is required only for the selected residue extension at `Q`; the
group action transports it to every translate. -/
theorem ramificationIdx_under_smul_eq_relIndex_inertia (Q : Ideal B) [Q.IsMaximal]
    (H : Subgroup G) (C : Type*) [CommRing C] [IsDomain C]
    [Algebra A C] [Algebra C B] [IsScalarTower A C B]
    [IsGaloisGroup H C B] [Module.Flat C B]
    [Algebra.IsSeparable (A ⧸ Q.under A) (B ⧸ Q)] (σ : G) :
    ((σ • Q).under C).ramificationIdx A =
      H.relIndex (MulAut.conj σ • Q.inertia G) := by
  let : Algebra.IsSeparable (A ⧸ (σ • Q).under A) (B ⧸ σ • Q) :=
    Quotient.isSeparable_smul Q σ
  rw [ramificationIdx_under_eq_relIndex_inertia (σ • Q) H C, inertia_smul,
    TauCeti.map_conj_eq_conj_smul]

/-- The contraction of a translated prime has ramification index one exactly when its conjugate
inertia group is contained in the subgroup fixing the intermediate ring. -/
theorem ramificationIdx_under_smul_eq_one_iff_inertia_le (Q : Ideal B) [Q.IsMaximal]
    (H : Subgroup G) (C : Type*) [CommRing C] [IsDomain C]
    [Algebra A C] [Algebra C B] [IsScalarTower A C B]
    [IsGaloisGroup H C B] [Module.Flat C B]
    [Algebra.IsSeparable (A ⧸ Q.under A) (B ⧸ Q)] (σ : G) :
    ((σ • Q).under C).ramificationIdx A = 1 ↔
      MulAut.conj σ • Q.inertia G ≤ H := by
  rw [Q.ramificationIdx_under_smul_eq_relIndex_inertia H C σ, Subgroup.relIndex_eq_one]

end Ideal
