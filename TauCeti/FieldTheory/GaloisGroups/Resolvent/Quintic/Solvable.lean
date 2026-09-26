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

## Main results

* `TauCeti.exists_isRoot_specialize_quinticF20Spec_of_isSolvable`: a solvable Galois group gives
  the `F₂₀` resolvent a root in the base field, with no hypothesis on the resolvent.
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

-- The permutation image of the Galois group of an irreducible quintic is a transitive subgroup of
-- `Equiv.Perm (Fin 5)`, and such a subgroup is solvable exactly when it lies in a conjugate of the
-- Frobenius group `5T3`.
private theorem isSolvable_gal_iff_exists_le_map_conj
    [Fact ((f.map (algebraMap F f.SplittingField)).Splits)] (hirr : Irreducible f)
    (e : f.rootSet f.SplittingField ≃ Fin 5) :
    Group.IsSolvable f.Gal ↔
      ∃ τ : Equiv.Perm (Fin 5),
        (Gal.galActionHom f f.SplittingField).range.map e.permCongrHom.toMonoidHom ≤
          (referenceSubgroup 5 ⟨2, by simp⟩).map (MulAut.conj τ).toMonoidHom := by
  let G : Subgroup (Equiv.Perm (Fin 5)) :=
    (Gal.galActionHom f f.SplittingField).range.map e.permCongrHom.toMonoidHom
  have htrans : IsPretransitive G (Fin 5) := by
    dsimp only [G]
    rw [Equiv.isPretransitive_map_permCongrHom_iff]
    exact isPretransitive_range_galActionHom f.SplittingField hirr
  let _ : IsPretransitive G (Fin 5) := htrans
  have hgal : Group.IsSolvable f.Gal ↔ Group.IsSolvable G :=
    MulEquiv.isSolvable_congr <|
      (MonoidHom.ofInjective (Gal.galActionHom_injective f f.SplittingField)).trans
        (e.permCongrHom.subgroupMap _)
  rw [hgal]
  exact isSolvable_iff_exists_le_map_conj_referenceSubgroup_five_two G

/-- **A solvable quintic Galois group gives the resolvent a root.** Let `f` be a monic irreducible
separable quintic over a field. If the polynomial Galois group is solvable, then the
specialization of Dummit's `F₂₀` resolvent has a root in the base field.

Nothing is assumed about the resolvent here; the converse direction, in
`TauCeti.isSolvable_gal_iff_exists_isRoot_specialize_quinticF20Spec`, does assume its
separability. -/
theorem exists_isRoot_specialize_quinticF20Spec_of_isSolvable (hf : f.Monic) (hsep : f.Separable)
    (hirr : Irreducible f) (hdeg : f.natDegree = 5) (hsol : Group.IsSolvable f.Gal) :
    ∃ a : F, (quinticF20Spec.specialize F f).IsRoot a := by
  let _ : Fact ((f.map (algebraMap F f.SplittingField)).Splits) := ⟨SplittingField.splits f⟩
  let _ : IsGalois F f.SplittingField := IsGalois.of_separable_splitting_field hsep
  obtain ⟨e⟩ := nonempty_rootSet_splittingField_equiv_fin f hsep
  obtain ⟨τ, hτ⟩ :=
    (isSolvable_gal_iff_exists_le_map_conj hirr (e.trans (finCongr hdeg))).mp hsol
  exact quinticF20Spec.exists_isRoot_specialize_of_le_map_conj hf hsep hdeg _ τ
    (by rwa [quinticF20Spec_H])

/-- **The quintic resolvent solvability criterion.** Let `f` be a monic irreducible separable
quintic over a field.  If the specialization of Dummit's `F₂₀` resolvent is separable, then
the polynomial Galois group is solvable if and only if that resolvent has a root in the base
field. -/
theorem isSolvable_gal_iff_exists_isRoot_specialize_quinticF20Spec (hf : f.Monic)
    (hsep : f.Separable) (hirr : Irreducible f) (hdeg : f.natDegree = 5)
    (hres : (quinticF20Spec.specialize F f).Separable) :
    Group.IsSolvable f.Gal ↔
      ∃ a : F, (quinticF20Spec.specialize F f).IsRoot a := by
  refine ⟨exists_isRoot_specialize_quinticF20Spec_of_isSolvable hf hsep hirr hdeg,
    fun ⟨a, ha⟩ => ?_⟩
  let _ : Fact ((f.map (algebraMap F f.SplittingField)).Splits) := ⟨SplittingField.splits f⟩
  let _ : IsGalois F f.SplittingField := IsGalois.of_separable_splitting_field hsep
  obtain ⟨e⟩ := nonempty_rootSet_splittingField_equiv_fin f hsep
  obtain ⟨τ, hτ⟩ := quinticF20Spec.exists_le_map_conj_of_isRoot_specialize hf hsep hdeg
    (e.trans (finCongr hdeg)) hres ha
  exact (isSolvable_gal_iff_exists_le_map_conj hirr (e.trans (finCongr hdeg))).mpr
    ⟨τ, by rwa [quinticF20Spec_H] at hτ⟩

end TauCeti
