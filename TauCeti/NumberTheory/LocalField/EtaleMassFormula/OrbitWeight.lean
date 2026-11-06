/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MassFormula.Basic
public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
import TauCeti.FieldTheory.Galois.FixedField
import Mathlib.Algebra.BigOperators.Finprod

/-!
# Discriminant weights of Galois actions

For an action of `Gal(SeparableClosure K / K)`, `TauCeti.orbitDiscriminantExponent` adds the
discriminant exponents of the fields fixed by point stabilizers, one per orbit. Conjugate
stabilizers have isomorphic fixed fields, so the summands do not depend on the representatives.
This is the discriminant weight used to count finite étale algebras by their Galois sets.

The weight is invariant under equivariant bijections and additive on disjoint unions with
finitely many orbits. For a transitive nonempty action it is the discriminant exponent of any
point's fixed field;
for a trivial action it is zero. No continuity is required here: the subextension discriminant
exponent is already totalized to zero on infinite extensions. The finite-support sum is likewise
zero if infinitely many orbits have nonzero weight.

## References

* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density of
  number field discriminants*, IMRN **2007**, rnm052, §2.
* K. S. Kedlaya, *Mass formulas for local Galois representations*, IMRN **2007**, rnm021.
-/

public section

noncomputable section

namespace TauCeti

open _root_.MulAction

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable {X Y : Type*} [MulAction Gal(SeparableClosure K/K) X]
  [MulAction Gal(SeparableClosure K/K) Y]

/-- Translating a point does not change the discriminant exponent of its stabilizer's fixed
field, since the two fixed fields are conjugate. -/
@[simp]
theorem discriminantExponent_fixedField_stabilizer_smul
    (σ : Gal(SeparableClosure K/K)) (x : X) :
    (IntermediateField.fixedField
      (stabilizer Gal(SeparableClosure K/K) (σ • x))).discriminantExponent =
        (IntermediateField.fixedField
          (stabilizer Gal(SeparableClosure K/K) x)).discriminantExponent := by
  rw [stabilizer_smul_eq_stabilizer_map_conj, MulEquiv.toMonoidHom_eq_coe,
    Subgroup.fixedField_map_conj]
  exact (IntermediateField.discriminantExponent_eq_of_algEquiv
    ((IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) x)).equivMap
      σ.toAlgHom)).symm

/-- The summand of an orbit can be computed at any point in that orbit. -/
theorem discriminantExponent_fixedField_stabilizer_out
    {ω : orbitRel.Quotient Gal(SeparableClosure K/K) X} {x : X}
    (hx : (Quotient.mk'' x : orbitRel.Quotient Gal(SeparableClosure K/K) X) = ω) :
    (IntermediateField.fixedField
      (stabilizer Gal(SeparableClosure K/K) ω.out)).discriminantExponent =
        (IntermediateField.fixedField
          (stabilizer Gal(SeparableClosure K/K) x)).discriminantExponent := by
  obtain ⟨σ, rfl⟩ := MulAction.exists_smul_out_eq hx
  exact (discriminantExponent_fixedField_stabilizer_smul K σ ω.out).symm

private theorem discriminantExponent_fixedField_stabilizer_out_of_injective
    (f : X → Y) (hf : Function.Injective f)
    (he : ∀ (σ : Gal(SeparableClosure K/K)) (x : X), f (σ • x) = σ • f x)
    {ω : orbitRel.Quotient Gal(SeparableClosure K/K) Y} {x : X}
    (hx : (Quotient.mk'' (f x) : orbitRel.Quotient Gal(SeparableClosure K/K) Y) = ω) :
    (IntermediateField.fixedField
      (stabilizer Gal(SeparableClosure K/K) ω.out)).discriminantExponent =
        (IntermediateField.fixedField
          (stabilizer Gal(SeparableClosure K/K) x)).discriminantExponent := by
  rw [discriminantExponent_fixedField_stabilizer_out K hx,
    MulAction.stabilizer_eq_of_injective f hf he]

/-- The sum of the discriminant exponents of the fixed fields of point stabilizers, one per
orbit. An infinite fixed field contributes zero; infinitely many nonzero summands give a total
of zero. -/
def orbitDiscriminantExponent (X : Type*) [MulAction Gal(SeparableClosure K/K) X] : ℕ :=
  ∑ᶠ ω : orbitRel.Quotient Gal(SeparableClosure K/K) X,
    (IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) ω.out)).discriminantExponent

/-- The defining finite-support sum for the orbit discriminant exponent. -/
theorem orbitDiscriminantExponent_def :
    orbitDiscriminantExponent K X =
      ∑ᶠ ω : orbitRel.Quotient Gal(SeparableClosure K/K) X,
        (IntermediateField.fixedField
          (stabilizer Gal(SeparableClosure K/K) ω.out)).discriminantExponent :=
  (rfl)

/-- Any choice of one point per orbit gives the same discriminant weight. -/
theorem orbitDiscriminantExponent_eq_finsum
    (s : orbitRel.Quotient Gal(SeparableClosure K/K) X → X)
    (hs : ∀ ω, (Quotient.mk'' (s ω) : orbitRel.Quotient Gal(SeparableClosure K/K) X) = ω) :
    orbitDiscriminantExponent K X =
      ∑ᶠ ω, (IntermediateField.fixedField
        (stabilizer Gal(SeparableClosure K/K) (s ω))).discriminantExponent := by
  exact finsum_congr fun ω ↦ discriminantExponent_fixedField_stabilizer_out K (hs ω)

/-- An equivariant bijection preserves the orbit discriminant exponent. -/
theorem orbitDiscriminantExponent_eq_of_equiv (e : X ≃ Y)
    (he : ∀ (σ : Gal(SeparableClosure K/K)) (x : X), e (σ • x) = σ • e x) :
    orbitDiscriminantExponent K X = orbitDiscriminantExponent K Y := by
  let E := MulAction.orbitRelQuotientCongr (MulEquiv.refl Gal(SeparableClosure K/K)) e he
  rw [orbitDiscriminantExponent_def, orbitDiscriminantExponent_def, ← finsum_comp_equiv E]
  apply finsum_congr
  intro ω
  have hE : (Quotient.mk'' (e ω.out) : orbitRel.Quotient Gal(SeparableClosure K/K) Y) = E ω := by
    rw [← MulAction.orbitRelQuotientCongr_mk (MulEquiv.refl _) e he, Quotient.out_eq']
  exact (discriminantExponent_fixedField_stabilizer_out_of_injective K e e.injective he hE).symm

/-- A transitive action has the discriminant exponent of the fixed field of any point
stabilizer. The point supplies nonemptiness. -/
theorem orbitDiscriminantExponent_of_isPretransitive
    [MulAction.IsPretransitive Gal(SeparableClosure K/K) X] (x : X) :
    orbitDiscriminantExponent K X =
      (IntermediateField.fixedField
        (stabilizer Gal(SeparableClosure K/K) x)).discriminantExponent := by
  have : Nonempty X := ⟨x⟩
  let := ((MulAction.pretransitive_iff_unique_quotient_of_nonempty
    Gal(SeparableClosure K/K) X).mp inferInstance).some
  rw [orbitDiscriminantExponent_def, finsum_eq_single _ (Quotient.mk'' x)
    (fun ω hω ↦ (hω (Subsingleton.elim _ _)).elim)]
  exact discriminantExponent_fixedField_stabilizer_out K rfl

/-- The coset action has the discriminant exponent of the subgroup's fixed field. In particular,
this computes the weight of a transitive Galois set presented by an open subgroup. -/
@[simp]
theorem orbitDiscriminantExponent_quotient (H : Subgroup Gal(SeparableClosure K/K)) :
    orbitDiscriminantExponent K (Gal(SeparableClosure K/K) ⧸ H) =
      (IntermediateField.fixedField H).discriminantExponent := by
  rw [orbitDiscriminantExponent_of_isPretransitive K
    ((1 : Gal(SeparableClosure K/K)) : Gal(SeparableClosure K/K) ⧸ H), stabilizer_quotient]

/-- Every trivial action has zero discriminant weight, including actions on empty or infinite
sets. -/
theorem orbitDiscriminantExponent_of_trivial
    (htriv : ∀ (σ : Gal(SeparableClosure K/K)) (x : X), σ • x = x) :
    orbitDiscriminantExponent K X = 0 := by
  have hstab (x : X) : stabilizer Gal(SeparableClosure K/K) x = ⊤ := by
    ext σ
    simp [mem_stabilizer_iff, htriv]
  simp [orbitDiscriminantExponent_def, hstab, InfiniteGalois.fixedField_bot]

/-- Actions on an empty or one-point set have zero weight. -/
@[simp]
theorem orbitDiscriminantExponent_of_subsingleton [Subsingleton X] :
    orbitDiscriminantExponent K X = 0 :=
  orbitDiscriminantExponent_of_trivial K fun _ _ ↦ Subsingleton.elim _ _

/-- Discriminant weight is additive on disjoint unions with finitely many orbits. Finiteness
prevents the infinite-support junk value from interfering with additivity. -/
@[simp]
theorem orbitDiscriminantExponent_sum
    [Finite (orbitRel.Quotient Gal(SeparableClosure K/K) X)]
    [Finite (orbitRel.Quotient Gal(SeparableClosure K/K) Y)] :
    orbitDiscriminantExponent K (X ⊕ Y) =
      orbitDiscriminantExponent K X + orbitDiscriminantExponent K Y := by
  classical
  let := Fintype.ofFinite (orbitRel.Quotient Gal(SeparableClosure K/K) X)
  let := Fintype.ofFinite (orbitRel.Quotient Gal(SeparableClosure K/K) Y)
  let E := MulAction.orbitRelQuotientSumEquiv
    (G := Gal(SeparableClosure K/K)) (X := X) (Y := Y)
  rw [orbitDiscriminantExponent_def, ← finsum_comp_equiv E.symm,
    finsum_eq_sum_of_fintype]
  rw [Fintype.sum_sum_type]
  congr 1
  · rw [orbitDiscriminantExponent_def, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun ω _ ↦
      discriminantExponent_fixedField_stabilizer_out_of_injective K
        Sum.inl Sum.inl_injective (fun _ _ ↦ rfl) ?_
    apply E.injective
    simp [E]
  · rw [orbitDiscriminantExponent_def, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun ω _ ↦
      discriminantExponent_fixedField_stabilizer_out_of_injective K
        Sum.inr Sum.inr_injective (fun _ _ ↦ rfl) ?_
    apply E.injective
    simp [E]

end TauCeti
