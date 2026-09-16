/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# Separable and inseparable residue degrees in Hilbert theory

For a prime `P` of a finite Galois extension lying over `p`, the quotient of the decomposition
group by inertia acts faithfully on the residue field.  The residue extension is normal but need
not be separable, so the order of this quotient is its separable degree rather than its full
degree.  Consequently the inertia group has order `e * fᵢ`, where `fᵢ` is the inseparable residue
degree.

These formulas are the form of the decomposition and inertia cardinalities that remains valid
over an imperfect residue field.  When the residue extension is separable, `fᵢ = 1` and they
specialize to the familiar identities `|I| = e` and `|D| = e * f`.

## Main results

* `Ideal.card_stabilizer_quotient_inertia_eq_finSepDegree`: the decomposition quotient has order
  equal to the separable residue degree.
* `Ideal.card_stabilizer_eq_card_inertia_mul_finSepDegree`: the decomposition group has order
  `|I| * fₛ`.
* `Ideal.card_stabilizer_eq_ramificationIdxIn_mul_inertiaDegIn`: the decomposition group has
  order `e * f` without a residue-separability hypothesis.
* `Ideal.card_inertia_eq_ramificationIdxIn_mul_finInsepDegree`: the inertia group has order
  `e * fᵢ`.
* `Ideal.card_inertia_eq_ramificationIdxIn_of_isSeparable`: for a separable residue extension,
  the familiar identity `|I| = e` holds without assuming the base residue field is perfect.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §9.

The proof follows the same cardinality argument as the function-field place API in
`TauCeti.FieldTheory.FunctionField.Place.Extension.Inertia`: normality identifies residue-field
embeddings with automorphisms, and the fundamental identity then separates the inseparable
degree from the inertia degree.
-/

public section

open Algebra MulAction
open scoped Pointwise

namespace Ideal

attribute [local instance] Ideal.Quotient.field

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S] [Group G]
  [MulSemiringAction G S] [IsGaloisGroup G R S] [Finite G]

include G

/-- The automorphism group of a residue extension in a finite invariant extension has order its
separable degree.  The residue extension is normal, but it need not be separable. -/
theorem card_residueFieldAut_eq_finSepDegree (p : Ideal R) [p.IsMaximal]
    (P : Ideal S) [P.LiesOver p] [P.IsMaximal] :
    Nat.card ((S ⧸ P) ≃ₐ[R ⧸ p] (S ⧸ P)) = Field.finSepDegree (R ⧸ p) (S ⧸ P) := by
  let _ : Normal (R ⧸ p) (S ⧸ P) := Ideal.Quotient.normal G p P
  exact (Nat.card_congr
    (Normal.algHomEquivAut (R ⧸ p) (AlgebraicClosure (S ⧸ P)) (S ⧸ P))).symm

/-- The quotient of the decomposition group by inertia has order equal to the separable residue
degree. -/
theorem card_stabilizer_quotient_inertia_eq_finSepDegree (p : Ideal R) [p.IsMaximal]
    (P : Ideal S) [P.LiesOver p] [P.IsMaximal] :
    Nat.card (stabilizer G P ⧸ P.inertia (stabilizer G P)) =
      Field.finSepDegree (R ⧸ p) (S ⧸ P) := by
  rw [Nat.card_congr (Ideal.Quotient.stabilizerQuotientInertiaEquiv G p P).toEquiv,
    card_residueFieldAut_eq_finSepDegree (G := G) p P]

/-- The order of the decomposition group is the order of inertia times the separable residue
degree. -/
theorem card_stabilizer_eq_card_inertia_mul_finSepDegree (p : Ideal R) [p.IsMaximal]
    (P : Ideal S) [P.LiesOver p] [P.IsMaximal] :
    Nat.card (stabilizer G P) =
      Nat.card (P.inertia G) * Field.finSepDegree (R ⧸ p) (S ⧸ P) := by
  have hindex : Subgroup.index (P.inertia (stabilizer G P)) =
      Field.finSepDegree (R ⧸ p) (S ⧸ P) := by
    rw [Subgroup.index_eq_card,
      card_stabilizer_quotient_inertia_eq_finSepDegree (G := G) p P]
  rw [← hindex,
    ← ((P.inertia G).subgroupOf (stabilizer G P)).card_mul_index,
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inertia_le_stabilizer (M := G) P)).toEquiv,
    AddSubgroup.subgroupOf_inertia]

variable [IsDedekindDomain R] [IsDedekindDomain S] [Module.Finite R S] [Module.Flat R S]

/-- The order of the decomposition group is `e * f`, without a separability hypothesis on the
residue extension. -/
theorem card_stabilizer_eq_ramificationIdxIn_mul_inertiaDegIn (p : Ideal R) [p.IsMaximal]
    (P : Ideal S) [P.LiesOver p] [P.IsMaximal] :
    Nat.card (stabilizer G P) = p.ramificationIdxIn S * p.inertiaDegIn S := by
  have horbit : (p.primesOver S).ncard * Nat.card (stabilizer G P) = Nat.card G := by
    rw [← IsInvariant.orbit_eq_primesOver R S G p P, ← Nat.card_coe_set_eq]
    simpa only [Nat.card_prod] using
      Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G P)
  have hfund := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p S G
  exact mul_right_injective₀ (IsDedekindDomain.primesOver_ncard_ne_zero p S)
    (by simpa only [mul_comm] using horbit.trans hfund.symm)

/-- Over an imperfect residue field, the inertia group has order `e * fᵢ`, where `fᵢ` is the
inseparable residue degree. -/
theorem card_inertia_eq_ramificationIdxIn_mul_finInsepDegree (p : Ideal R) [p.IsMaximal]
    (P : Ideal S) [P.LiesOver p] [P.IsMaximal] :
    Nat.card (P.inertia G) =
      p.ramificationIdxIn S * Field.finInsepDegree (R ⧸ p) (S ⧸ P) := by
  have hcard := card_stabilizer_eq_card_inertia_mul_finSepDegree (G := G) p P
  rw [card_stabilizer_eq_ramificationIdxIn_mul_inertiaDegIn (G := G) p P,
    inertiaDegIn_eq_inertiaDeg p P G, inertiaDeg_eq_of_isMaximal p P,
    ← Field.finSepDegree_mul_finInsepDegree] at hcard
  refine Nat.eq_of_mul_eq_mul_right
    (NeZero.pos (Field.finSepDegree (R ⧸ p) (S ⧸ P))) ?_
  calc
    Nat.card (P.inertia G) * Field.finSepDegree (R ⧸ p) (S ⧸ P) =
        p.ramificationIdxIn S *
          (Field.finSepDegree (R ⧸ p) (S ⧸ P) *
            Field.finInsepDegree (R ⧸ p) (S ⧸ P)) := hcard.symm
    _ = (p.ramificationIdxIn S * Field.finInsepDegree (R ⧸ p) (S ⧸ P)) *
          Field.finSepDegree (R ⧸ p) (S ⧸ P) := by
      simp only [mul_assoc, mul_left_comm, mul_comm]

/-- If the residue extension is separable, the inertia group has order equal to the ramification
index.  Unlike the standard perfect-residue-field form, this assumes separability only for the
one residue extension in the statement. -/
theorem card_inertia_eq_ramificationIdxIn_of_isSeparable (p : Ideal R) [p.IsMaximal]
    (P : Ideal S) [P.LiesOver p] [P.IsMaximal]
    [Algebra.IsSeparable (R ⧸ p) (S ⧸ P)] :
    Nat.card (P.inertia G) = p.ramificationIdxIn S := by
  have hfi : Field.finInsepDegree (R ⧸ p) (S ⧸ P) = 1 :=
    (isSeparable_iff_finInsepDegree_eq_one (F := R ⧸ p) (K := S ⧸ P)).mp
      inferInstance
  rw [card_inertia_eq_ramificationIdxIn_mul_finInsepDegree (G := G) p P,
    hfi, mul_one]

end Ideal
