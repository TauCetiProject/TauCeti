/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisGroups.Degree
public import TauCeti.FieldTheory.GaloisGroups.Discriminant.Basic
public import TauCeti.FieldTheory.GaloisGroups.Orbits
public import TauCeti.GroupTheory.Perm.TransitiveGroupLabel

/-!
# The transitive-group label of a polynomial

A separable polynomial `f` of degree `n` over a field `F` has `n` distinct roots in its splitting
field, and its Galois group acts faithfully on them. Choosing a numbering
`e : f.rootSet f.SplittingField ≃ Fin n` turns the image of that action into a subgroup of
`Equiv.Perm (Fin n)`, which can then be compared with the reference subgroups of
`TauCeti.referenceSubgroup`. The predicate `TauCeti.HasGaloisLabel f j` says that some numbering
carries the Galois image to a subgroup with the label `j`, that is, onto a conjugate of the
reference subgroup `referenceSubgroup n j`. This is the label `nT(j+1)` that the LMFDB attaches to
`f`.

The numbering is only a device for the comparison. The main result
`TauCeti.hasGaloisLabel_iff_forall` shows that the label does not depend on it: if one numbering
exhibits the label then every numbering does. The predicate is therefore a property of `f`.

A label records the permutation invariants of the Galois group. `f.Gal` has the order of the
reference subgroup, and it is solvable, respectively acts primitively on the roots, exactly when
the reference subgroup is solvable, respectively primitive. The Galois image consists of even
permutations exactly when the reference subgroup does, and so, away from characteristic `2` and
for monic `f`, the discriminant of `f` is a square exactly when the reference subgroup lies in the
alternating group. Since every reference subgroup is transitive, a polynomial with a label is
irreducible.

Separability and the degree are part of the predicate, so an inseparable polynomial, or one of
degree other than `n`, has no label in degree `n`; nor does a polynomial of degree zero or of
degree above five, where there are no reference subgroups. In degree one the label is determined
by the degree alone, and in degree two by separability and irreducibility.

## Main definitions

* `TauCeti.HasGaloisLabel`: the Galois image of `f`, read through some numbering of the roots,
  carries a given transitive-group label.

## Main results

* `TauCeti.hasGaloisLabel_iff_forall`: the label does not depend on the numbering of the roots.
* `TauCeti.HasGaloisLabel.natCard_gal`: the order of the Galois group is that of the reference.
* `TauCeti.HasGaloisLabel.range_le_alternatingGroup_iff` and
  `TauCeti.HasGaloisLabel.isSquare_discr_iff`: the parity of the Galois image.
* `TauCeti.HasGaloisLabel.isPreprimitive_iff`, `TauCeti.HasGaloisLabel.isPreprimitive_gal_iff`:
  primitivity of the Galois image, respectively of the Galois group, on the roots.
* `TauCeti.HasGaloisLabel.isSolvable_iff`: solvability of the Galois group.
* `TauCeti.HasGaloisLabel.irreducible`: a polynomial with a label is irreducible.
* `TauCeti.hasGaloisLabel_one_iff`, `TauCeti.hasGaloisLabel_two_iff`: the labels in degrees one
  and two.

## References

* LMFDB, *Galois group labels*, <https://www.lmfdb.org/GaloisGroup/>.
-/

public section

open Polynomial Equiv MulAction

namespace TauCeti

universe u

variable {F : Type u} [Field F]

section GalActionHom

/-- A polynomial splits in its splitting field, recorded as the `Fact` that
`Polynomial.Gal.galActionHom` asks for. It stays local: as a global instance it would give
`f.rootSet f.SplittingField` the action `Polynomial.Gal.galAction` in addition to Mathlib's
intrinsic `Polynomial.Gal.galActionAux`, and the two are different actions. -/
local instance factSplitsSplittingField (f : F[X]) :
    Fact ((f.map (algebraMap F f.SplittingField)).Splits) :=
  ⟨SplittingField.splits f⟩

-- Formalization source: `TauCetiRoadmap/PolynomialGaloisGroups/Suggested.lean`.
/-- The Galois group of `f` carries the transitive-group label `j` of degree `n`: `f` is
separable of degree `n`, and some numbering of its roots in the splitting field by `Fin n` carries
the image of the Galois action on the roots to a conjugate of the reference subgroup
`referenceSubgroup n j`. By `TauCeti.hasGaloisLabel_iff_forall`, every numbering then does. -/
def HasGaloisLabel (f : F[X]) {n : ℕ} (j : TransitiveGroupIndex n) : Prop :=
  f.Separable ∧ f.natDegree = n ∧
    ∃ e : f.rootSet f.SplittingField ≃ Fin n,
      TransitiveGroupLabel j
        ((Gal.galActionHom f f.SplittingField).range.map e.permCongrHom.toMonoidHom)

variable {f : F[X]} {n : ℕ} {j : TransitiveGroupIndex n}

/-- Construct a Galois label from one numbering of the roots that exhibits it. -/
theorem HasGaloisLabel.mk (hsep : f.Separable) (hdeg : f.natDegree = n)
    (e : f.rootSet f.SplittingField ≃ Fin n)
    (he : TransitiveGroupLabel j
      ((Gal.galActionHom f f.SplittingField).range.map e.permCongrHom.toMonoidHom)) :
    HasGaloisLabel f j :=
  ⟨hsep, hdeg, e, he⟩

/-- A polynomial with a label is separable. -/
theorem HasGaloisLabel.separable (h : HasGaloisLabel f j) : f.Separable :=
  h.1

/-- A polynomial with a label in degree `n` has degree `n`. -/
theorem HasGaloisLabel.natDegree_eq (h : HasGaloisLabel f j) : f.natDegree = n :=
  h.2.1

/-- A label is exhibited by every numbering of the roots. -/
theorem HasGaloisLabel.transitiveGroupLabel (h : HasGaloisLabel f j)
    (e : f.rootSet f.SplittingField ≃ Fin n) :
    TransitiveGroupLabel j
      ((Gal.galActionHom f f.SplittingField).range.map e.permCongrHom.toMonoidHom) := by
  obtain ⟨-, -, e', he'⟩ := h
  exact (Subgroup.transitiveGroupLabel_map_permCongrHom_iff _ e' e).mp he'

/-- **The label does not depend on the numbering of the roots.** A separable polynomial of degree
`n` has the label `j` exactly when every numbering of its roots by `Fin n` carries its Galois image
to a subgroup with the label `j`. -/
theorem hasGaloisLabel_iff_forall :
    HasGaloisLabel f j ↔ f.Separable ∧ f.natDegree = n ∧
      ∀ e : f.rootSet f.SplittingField ≃ Fin n,
        TransitiveGroupLabel j
          ((Gal.galActionHom f f.SplittingField).range.map e.permCongrHom.toMonoidHom) := by
  refine ⟨fun h => ⟨h.separable, h.natDegree_eq, h.transitiveGroupLabel⟩, ?_⟩
  rintro ⟨hsep, rfl, h⟩
  obtain ⟨e⟩ := nonempty_rootSet_splittingField_equiv_fin f hsep
  exact ⟨hsep, rfl, e, h e⟩

/-- An inseparable polynomial has no label. -/
theorem not_hasGaloisLabel_of_not_separable (hf : ¬ f.Separable) : ¬ HasGaloisLabel f j :=
  fun h => hf h.separable

/-- A polynomial has no label in a degree other than its own. -/
theorem not_hasGaloisLabel_of_natDegree_ne (hf : f.natDegree ≠ n) : ¬ HasGaloisLabel f j :=
  fun h => hf h.natDegree_eq

/-- The Galois group of a polynomial with a label has the order of the reference subgroup. -/
theorem HasGaloisLabel.natCard_gal (h : HasGaloisLabel f j) :
    Nat.card f.Gal = Nat.card (referenceSubgroup n j) := by
  obtain ⟨-, -, e, he⟩ := h
  rw [← he.natCard_eq, Subgroup.card_map_of_injective e.permCongrHom.injective,
    natCard_galActionHom_range]

/-- A polynomial with a label is irreducible, because every reference subgroup is transitive.
There are no labels in degree zero, so no degree hypothesis is needed. -/
theorem HasGaloisLabel.irreducible (h : HasGaloisLabel f j) : Irreducible f := by
  obtain ⟨hsep, rfl, e, he⟩ := h
  have := he.isPretransitive
  rw [Equiv.isPretransitive_map_permCongrHom_iff, Gal.galActionHom,
    isPretransitive_range_toPermHom_iff] at this
  exact (isPretransitive_iff_irreducible f.SplittingField hsep
    (pos_of_transitiveGroupIndex j)).mp this

/-- The Galois image of a polynomial with a label acts primitively on the roots exactly when the
reference subgroup acts primitively. -/
theorem HasGaloisLabel.isPreprimitive_iff (h : HasGaloisLabel f j) :
    IsPreprimitive (Gal.galActionHom f f.SplittingField).range (f.rootSet f.SplittingField) ↔
      IsPreprimitive (referenceSubgroup n j) (Fin n) := by
  obtain ⟨-, -, e, he⟩ := h
  rw [← he.isPreprimitive_iff, Equiv.isPreprimitive_map_permCongrHom_iff]

/-- The Galois group of a polynomial with a label is solvable exactly when the reference subgroup
is. -/
theorem HasGaloisLabel.isSolvable_iff (h : HasGaloisLabel f j) :
    Group.IsSolvable f.Gal ↔ Group.IsSolvable (referenceSubgroup n j) := by
  obtain ⟨-, -, e, he⟩ := h
  rw [← he.isSolvable_iff]
  exact MulEquiv.isSolvable_congr <|
    (MonoidHom.ofInjective (Gal.galActionHom_injective f f.SplittingField)).trans
      (e.permCongrHom.subgroupMap _)

open scoped Classical in
/-- The Galois image of a polynomial with a label consists of even permutations of the roots
exactly when the reference subgroup consists of even permutations. -/
theorem HasGaloisLabel.range_le_alternatingGroup_iff (h : HasGaloisLabel f j) :
    (Gal.galActionHom f f.SplittingField).range ≤
        alternatingGroup (f.rootSet f.SplittingField) ↔
      referenceSubgroup n j ≤ alternatingGroup (Fin n) := by
  obtain ⟨-, -, e, he⟩ := h
  rw [← he.le_alternatingGroup_iff, Equiv.map_permCongrHom_le_alternatingGroup_iff]

/-- **The discriminant reads the parity of the label.** Away from characteristic `2`, a monic
polynomial with a label has a square discriminant exactly when the reference subgroup lies in the
alternating group. -/
theorem HasGaloisLabel.isSquare_discr_iff (h : HasGaloisLabel f j) (hf : f.Monic)
    (hchar : ringChar F ≠ 2) :
    IsSquare f.discr ↔ referenceSubgroup n j ≤ alternatingGroup (Fin n) := by
  have : IsGalois F f.SplittingField := IsGalois.of_separable_splitting_field h.separable
  rw [← h.range_le_alternatingGroup_iff,
    hf.isSquare_discr_iff_range_le_alternatingGroup (E := f.SplittingField) h.separable hchar]

/-- In degree one, a polynomial carries the label `1T1` exactly when it has degree one; such a
polynomial is automatically separable. -/
@[simp]
theorem hasGaloisLabel_one_iff (j : TransitiveGroupIndex 1) :
    HasGaloisLabel f j ↔ f.natDegree = 1 := by
  refine ⟨HasGaloisLabel.natDegree_eq, fun hdeg => ?_⟩
  have hsep : f.Separable := by
    rw [separable_iff_derivative_ne_zero (irreducible_of_degree_eq_one
      ((degree_eq_iff_natDegree_eq_of_pos one_pos).mpr hdeg))]
    intro h0
    have h := congrArg (coeff · 0) h0
    simp only [coeff_derivative, coeff_zero, zero_add, Nat.cast_zero, mul_one] at h
    have hf : f ≠ 0 := by rintro rfl; simp at hdeg
    exact hf (leadingCoeff_eq_zero.mp (by rwa [leadingCoeff, hdeg]))
  obtain ⟨e⟩ := nonempty_rootSet_splittingField_equiv_fin f hsep
  exact ⟨hsep, hdeg, e.trans (finCongr hdeg), transitiveGroupLabel_one j _⟩

/-- In degree two, a polynomial carries the label `2T1` exactly when it is separable, irreducible,
and of degree two. -/
@[simp]
theorem hasGaloisLabel_two_iff (j : TransitiveGroupIndex 2) :
    HasGaloisLabel f j ↔ f.Separable ∧ Irreducible f ∧ f.natDegree = 2 := by
  refine ⟨fun h => ⟨h.separable, h.irreducible, h.natDegree_eq⟩, fun ⟨hsep, hirr, hdeg⟩ => ?_⟩
  obtain ⟨e⟩ := nonempty_rootSet_splittingField_equiv_fin f hsep
  refine ⟨hsep, hdeg, e.trans (finCongr hdeg), ?_⟩
  rw [transitiveGroupLabel_two_iff, Equiv.isPretransitive_map_permCongrHom_iff, Gal.galActionHom,
    isPretransitive_range_toPermHom_iff]
  exact (isPretransitive_iff_irreducible f.SplittingField hsep (by omega)).mpr hirr

end GalActionHom

/- Outside the section above, the roots in the splitting field carry only Mathlib's intrinsic
action `Polynomial.Gal.galActionAux`. -/

variable {f : F[X]} {n : ℕ} {j : TransitiveGroupIndex n}

/-- The Galois group of a polynomial with a label acts primitively on its roots in the splitting
field exactly when the reference subgroup acts primitively. -/
theorem HasGaloisLabel.isPreprimitive_gal_iff (h : HasGaloisLabel f j) :
    IsPreprimitive f.Gal (f.rootSet f.SplittingField) ↔
      IsPreprimitive (referenceSubgroup n j) (Fin n) := by
  have : Fact ((f.map (algebraMap F f.SplittingField)).Splits) := ⟨SplittingField.splits f⟩
  rw [← h.isPreprimitive_iff, Gal.galActionHom, isPreprimitive_range_toPermHom_iff]
  -- `Gal.rootsEquivRootsAux` intertwines the intrinsic action with `Gal.galAction`; both actions
  -- are now in scope, so they are named explicitly.
  exact @isPreprimitive_congr f.Gal _ _ (Gal.galActionAux f) f.Gal _ _ (Gal.galAction f _) id
    (@MulActionHom.mk _ _ id _ (Gal.galActionAux f).toSMul _ (Gal.smul f _)
      (Gal.rootsEquivRootsAux f f.SplittingField) fun g x => by
        rw [id, Gal.smul_def, Equiv.symm_apply_apply])
    Function.surjective_id (Gal.rootsEquivRootsAux f f.SplittingField).bijective

end TauCeti
