/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisGroups.Resolvent.Quintic.Basic
public import TauCeti.FieldTheory.GaloisGroups.Resolvent.Root

import TauCeti.FieldTheory.GaloisGroups.Degree
import TauCeti.FieldTheory.GaloisGroups.Orbits
import TauCeti.GroupTheory.Perm.TransitiveGroupLabel.Solvable

/-!
# Solvability of a quintic from its resolvent sextic

Let `f` be a monic irreducible separable quintic over a field `F`.  The Galois group of `f` is
solvable exactly when its permutation image on the five roots lies in a conjugate of the
Frobenius group `F₂₀ = 5T3`.  The resolvent attached to
`TauCeti.quinticF20Spec` detects exactly that containment: provided the specialized resolvent is
separable, it has a root in `F` if and only if the image lies in a conjugate of `F₂₀`.

Thus a separable specialized resolvent has a root in the base field exactly when the polynomial
Galois group is solvable.  Separability of `f` does not imply separability of the resolvent and
cannot replace that hypothesis: specialization can make distinct values of the six universal
orbit elements collide.

No characteristic restriction is needed for this group-and-resolvent statement.  Restrictions
on characteristics two and five enter the separate discriminant and depression arguments, not
the exact-stabilizer criterion used here.

## Main result

* `TauCeti.isSolvable_gal_iff_exists_isRoot_specialize_quinticF20Spec`: the Galois group of an
  irreducible separable quintic is solvable exactly when its separable `F₂₀` resolvent has a
  root in the base field.

## References

* D. S. Dummit, *Solving solvable quintics*, Mathematics of Computation **57** (1991), Theorem 1.
  The separability hypothesis here makes explicit the distinct-value condition used when a
  resolvent root is read as containment in an invariant's stabilizer.
-/

public section

open Polynomial Equiv MulAction

namespace TauCeti

universe u

variable {F : Type u} [Field F] {f : F[X]}

/-- **The quintic resolvent solvability criterion.** Let `f` be a monic irreducible separable
quintic over a field.  If the specialization of Dummit's `F₂₀` resolvent is separable, then
the polynomial Galois group is solvable if and only if that resolvent has a root in the base
field. -/
theorem isSolvable_gal_iff_exists_isRoot_specialize_quinticF20Spec (hf : f.Monic)
    (hsep : f.Separable) (hirr : Irreducible f) (hdeg : f.natDegree = 5)
    (hres : (quinticF20Spec.specialize F f).Separable) :
    Group.IsSolvable f.Gal ↔
      ∃ a : F, (quinticF20Spec.specialize F f).IsRoot a := by
  let _ : Fact ((f.map (algebraMap F f.SplittingField)).Splits) :=
    ⟨SplittingField.splits f⟩
  let _ : IsGalois F f.SplittingField := IsGalois.of_separable_splitting_field hsep
  obtain ⟨e⟩ := nonempty_rootSet_splittingField_equiv_fin f hsep
  let e₅ : f.rootSet f.SplittingField ≃ Fin 5 := e.trans (finCongr hdeg)
  let G : Subgroup (Equiv.Perm (Fin 5)) :=
    (Gal.galActionHom f f.SplittingField).range.map e₅.permCongrHom.toMonoidHom
  have htrans : IsPretransitive G (Fin 5) := by
    dsimp only [G]
    rw [Equiv.isPretransitive_map_permCongrHom_iff]
    exact isPretransitive_range_galActionHom f.SplittingField hirr
  let _ : IsPretransitive G (Fin 5) := htrans
  have hgal : Group.IsSolvable f.Gal ↔ Group.IsSolvable G := by
    exact MulEquiv.isSolvable_congr <|
      (MonoidHom.ofInjective (Gal.galActionHom_injective f f.SplittingField)).trans
        (e₅.permCongrHom.subgroupMap _)
  have hgroup := isSolvable_iff_exists_le_map_conj_referenceSubgroup_five_two G
  have hroot := quinticF20Spec.exists_isRoot_specialize_iff_exists_le_map_conj
    (E := f.SplittingField) hf hsep hdeg e₅ hres
  rw [hgal, hgroup]
  simpa [G] using hroot.symm

end TauCeti
