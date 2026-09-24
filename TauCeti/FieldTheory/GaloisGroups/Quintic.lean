/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisGroups.Label
public import TauCeti.FieldTheory.GaloisGroups.Resolvent.Quintic.Basic

import TauCeti.FieldTheory.GaloisGroups.Resolvent.Quintic.Solvable
import TauCeti.GroupTheory.Perm.TransitiveGroupLabel.Solvable
import TauCeti.GroupTheory.Perm.TransitiveGroupLabel.Order
import TauCeti.FieldTheory.Galois.PrimeDegree

/-!
# The Galois group of a quintic

An irreducible separable quintic over a field carries exactly one of the five transitive-group
labels `5T1`, …, `5T5`. For a monic such quintic, two data constrain the label. Away from
characteristic `2` the discriminant reads its parity: it is a square exactly for the even labels
`5T1`, `5T2` and `5T4`. Dummit's `F₂₀` resolvent sextic gives an unconditional implication from
solvability to having a root in the base field; when its specialization is separable, the converse
holds as well, so a root is then equivalent to one of the labels `5T1`, `5T2` and `5T3`.

For monic quintics, the two data together separate `5T3`, `5T4` and `5T5` from each other and from
the rest, and this file proves those three identifications, together with a fourth branch
concluding `5T1` or `5T2`:

| discriminant | resolvent sextic | label |
|---|---|---|
| not a square | no root in the base field | `5T5` |
| a square | no root in the base field | `5T4` |
| not a square | a root in the base field | `5T3` |
| a square | a root in the base field | `5T1` **or** `5T2` |

The fourth row concludes only that the label is `5T1` or `5T2`.
An independent criterion identifies `5T1` when the root field has a nonidentity automorphism.

The first two rows need no hypothesis on the resolvent sextic, because they use only the
unconditional direction of the resolvent criterion, that a solvable Galois group produces a root.
The last two rows read a root of the sextic as a containment, which is sound only when the
specialized sextic is separable; separability of `f` does not imply it, since specialization can
make the values of two distinct orbit elements collide.

The two characterizations behind the table, `TauCeti.HasGaloisLabel.isSquare_discr_iff_five` and
`TauCeti.HasGaloisLabel.exists_isRoot_specialize_quinticF20Spec_iff`, are equivalences when the
specialized resolvent is separable, so under that additional hypothesis they also supply the
converse of each row.

## Main results

* `TauCeti.existsUnique_hasGaloisLabel_five`: an irreducible separable quintic carries exactly one
  label.
* `TauCeti.HasGaloisLabel.isSolvable_iff_five`: the Galois group of a quintic is solvable
  exactly for the labels `5T1`, `5T2` and `5T3`.
* `TauCeti.HasGaloisLabel.isSquare_discr_iff_five`: **the discriminant reads the parity of the
  label**, and `TauCeti.HasGaloisLabel.exists_isRoot_specialize_quinticF20Spec_iff`: **a root of
  the separable resolvent sextic reads solvability of the label**.
* `TauCeti.hasGaloisLabel_five_four_of_not_isSquare_discr_of_forall_not_isRoot`,
  `TauCeti.hasGaloisLabel_five_three_of_isSquare_discr_of_forall_not_isRoot`,
  `TauCeti.hasGaloisLabel_five_two_of_not_isSquare_discr_of_isRoot`,
  `TauCeti.hasGaloisLabel_five_zero_or_one_of_isSquare_discr_of_isRoot`: the four rows of the
  table above.
* `TauCeti.hasGaloisLabel_five_zero_of_exists_rootField_aut_ne_one`: a nonidentity
  automorphism of a quintic root field identifies the label as `5T1`.

## References

* D. S. Dummit, *Solving solvable quintics*, Mathematics of Computation **57** (1991), §2.
* H. Cohen, *A Course in Computational Algebraic Number Theory*, §6.3.
-/

public section

open Polynomial IntermediateField

namespace TauCeti

universe u

variable {F : Type u} [Field F] {f : F[X]} {j : TransitiveGroupIndex 5}

/-- A polynomial carries at most one label in degree five. -/
theorem HasGaloisLabel.eq_of_five {j k : TransitiveGroupIndex 5} (hj : HasGaloisLabel f j)
    (hk : HasGaloisLabel f k) : j = k :=
  hj.eq_of (fun h h' => h.eq_of_five h') hk

/-- **An irreducible separable quintic carries exactly one label**, one of `5T1`, …, `5T5`. -/
theorem existsUnique_hasGaloisLabel_five (hsep : f.Separable) (hirr : Irreducible f)
    (hdeg : f.natDegree = 5) : ∃! j : TransitiveGroupIndex 5, HasGaloisLabel f j :=
  existsUnique_hasGaloisLabel hsep hirr hdeg (fun G _ => exists_transitiveGroupLabel_five G)
    fun h h' => h.eq_of_five h'

/-- **Solvability and the quintic labels.** The Galois group of a quintic with a label is solvable
exactly for the labels `5T1`, `5T2` and `5T3`, the cyclic, dihedral and Frobenius groups. This is a
statement about the group, not about `solvableByRad`. -/
theorem HasGaloisLabel.isSolvable_iff_five (h : HasGaloisLabel f j) :
    Group.IsSolvable f.Gal ↔ (j : ℕ) < 3 := by
  rw [h.isSolvable_iff, isSolvable_referenceSubgroup_five_iff]

/-- **The discriminant reads the parity of a quintic label.** Away from characteristic `2`, the
discriminant of a monic quintic with a label is a square exactly for the even labels `5T1`, `5T2`
and `5T4`. -/
theorem HasGaloisLabel.isSquare_discr_iff_five (h : HasGaloisLabel f j) (hf : f.Monic)
    (hchar : ringChar F ≠ 2) :
    IsSquare f.discr ↔ (j : ℕ) = 0 ∨ (j : ℕ) = 1 ∨ (j : ℕ) = 3 := by
  rw [h.isSquare_discr_iff hf hchar, referenceSubgroup_five_le_alternatingGroup_iff]

/-- **A solvable label gives the resolvent sextic a root.** A monic quintic whose label is `5T1`,
`5T2` or `5T3` has a root of its `F₂₀` resolvent in the base field. Nothing is assumed about the
resolvent; the converse needs its separability, and is
`TauCeti.HasGaloisLabel.exists_isRoot_specialize_quinticF20Spec_iff`. -/
theorem HasGaloisLabel.exists_isRoot_specialize_quinticF20Spec_of_lt_three
    (h : HasGaloisLabel f j) (hf : f.Monic) (hj : (j : ℕ) < 3) :
    ∃ a : F, (quinticF20Spec.specialize F f).IsRoot a :=
  exists_isRoot_specialize_quinticF20Spec_of_isSolvable hf h.separable h.irreducible
    h.natDegree_eq (h.isSolvable_iff_five.mpr hj)

/-- **A root of the separable resolvent sextic reads solvability of the label.** For a monic
quintic with a label and a separable specialized `F₂₀` resolvent, that resolvent has a root in the
base field exactly for the labels `5T1`, `5T2` and `5T3`. -/
theorem HasGaloisLabel.exists_isRoot_specialize_quinticF20Spec_iff (h : HasGaloisLabel f j)
    (hf : f.Monic) (hres : (quinticF20Spec.specialize F f).Separable) :
    (∃ a : F, (quinticF20Spec.specialize F f).IsRoot a) ↔ (j : ℕ) < 3 := by
  rw [← isSolvable_gal_iff_exists_isRoot_specialize_quinticF20Spec hf h.separable h.irreducible
    h.natDegree_eq hres, h.isSolvable_iff_five]

/-- **The first row of the quintic table: `5T5`.** Away from characteristic `2`, an irreducible
monic quintic whose discriminant is not a square and whose `F₂₀` resolvent has no root in the base
field has the full symmetric group on its five roots. -/
theorem hasGaloisLabel_five_four_of_not_isSquare_discr_of_forall_not_isRoot (hf : f.Monic)
    (hchar : ringChar F ≠ 2) (hirr : Irreducible f) (hdeg : f.natDegree = 5)
    (hdisc : ¬ IsSquare f.discr)
    (hroot : ∀ a : F, ¬ (quinticF20Spec.specialize F f).IsRoot a) :
    HasGaloisLabel f (⟨4, by simp⟩ : TransitiveGroupIndex 5) := by
  have hsep : f.Separable := hf.discr_ne_zero_iff.mp fun h0 => hdisc ⟨0, by simp [h0]⟩
  obtain ⟨j, hj, -⟩ := existsUnique_hasGaloisLabel_five hsep hirr hdeg
  have hsol : ¬ (j : ℕ) < 3 := fun hlt =>
    (hj.exists_isRoot_specialize_quinticF20Spec_of_lt_three hf hlt).elim hroot
  have hpar : ¬ ((j : ℕ) = 0 ∨ (j : ℕ) = 1 ∨ (j : ℕ) = 3) := fun hp =>
    hdisc ((hj.isSquare_discr_iff_five hf hchar).mpr hp)
  have hlt : (j : ℕ) < 5 := by simpa [numTransitiveGroups_five] using j.isLt
  have hval : (j : ℕ) = 4 := by omega
  have : j = ⟨4, by simp⟩ := Fin.ext hval
  exact this ▸ hj

/-- **The second row of the quintic table: `5T4`.** Away from characteristic `2`, an irreducible
separable monic quintic whose discriminant is a square and whose `F₂₀` resolvent has no root in
the base field has the alternating group on its five roots. -/
theorem hasGaloisLabel_five_three_of_isSquare_discr_of_forall_not_isRoot (hf : f.Monic)
    (hchar : ringChar F ≠ 2) (hsep : f.Separable) (hirr : Irreducible f) (hdeg : f.natDegree = 5)
    (hdisc : IsSquare f.discr)
    (hroot : ∀ a : F, ¬ (quinticF20Spec.specialize F f).IsRoot a) :
    HasGaloisLabel f (⟨3, by simp⟩ : TransitiveGroupIndex 5) := by
  obtain ⟨j, hj, -⟩ := existsUnique_hasGaloisLabel_five hsep hirr hdeg
  have hsol : ¬ (j : ℕ) < 3 := fun hlt =>
    (hj.exists_isRoot_specialize_quinticF20Spec_of_lt_three hf hlt).elim hroot
  have hpar := (hj.isSquare_discr_iff_five hf hchar).mp hdisc
  have hval : (j : ℕ) = 3 := by omega
  have : j = ⟨3, by simp⟩ := Fin.ext hval
  exact this ▸ hj

/-- **The third row of the quintic table: `5T3`.** Away from characteristic `2`, an irreducible
monic quintic whose discriminant is not a square and whose separable `F₂₀` resolvent has a root in
the base field has the Frobenius group of order twenty on its five roots. -/
theorem hasGaloisLabel_five_two_of_not_isSquare_discr_of_isRoot (hf : f.Monic)
    (hchar : ringChar F ≠ 2) (hirr : Irreducible f) (hdeg : f.natDegree = 5)
    (hdisc : ¬ IsSquare f.discr) (hres : (quinticF20Spec.specialize F f).Separable) {a : F}
    (ha : (quinticF20Spec.specialize F f).IsRoot a) :
    HasGaloisLabel f (⟨2, by simp⟩ : TransitiveGroupIndex 5) := by
  have hsep : f.Separable := hf.discr_ne_zero_iff.mp fun h0 => hdisc ⟨0, by simp [h0]⟩
  obtain ⟨j, hj, -⟩ := existsUnique_hasGaloisLabel_five hsep hirr hdeg
  have hsol := (hj.exists_isRoot_specialize_quinticF20Spec_iff hf hres).mp ⟨a, ha⟩
  have hpar : ¬ ((j : ℕ) = 0 ∨ (j : ℕ) = 1 ∨ (j : ℕ) = 3) := fun hp =>
    hdisc ((hj.isSquare_discr_iff_five hf hchar).mpr hp)
  have hval : (j : ℕ) = 2 := by omega
  have : j = ⟨2, by simp⟩ := Fin.ext hval
  exact this ▸ hj

/-- **The fourth row of the quintic table: `5T1` or `5T2`.** Away from characteristic `2`, an
irreducible separable monic quintic whose discriminant is a square and whose separable `F₂₀`
resolvent has a root in the base field has either the cyclic group or the dihedral group of order
ten on its five roots. -/
theorem hasGaloisLabel_five_zero_or_one_of_isSquare_discr_of_isRoot (hf : f.Monic)
    (hchar : ringChar F ≠ 2) (hsep : f.Separable) (hirr : Irreducible f) (hdeg : f.natDegree = 5)
    (hdisc : IsSquare f.discr) (hres : (quinticF20Spec.specialize F f).Separable) {a : F}
    (ha : (quinticF20Spec.specialize F f).IsRoot a) :
    HasGaloisLabel f (⟨0, by simp⟩ : TransitiveGroupIndex 5) ∨
      HasGaloisLabel f (⟨1, by simp⟩ : TransitiveGroupIndex 5) := by
  obtain ⟨j, hj, -⟩ := existsUnique_hasGaloisLabel_five hsep hirr hdeg
  have hsol := (hj.exists_isRoot_specialize_quinticF20Spec_iff hf hres).mp ⟨a, ha⟩
  have hpar := (hj.isSquare_discr_iff_five hf hchar).mp hdisc
  rcases (by omega : (j : ℕ) = 0 ∨ (j : ℕ) = 1) with hval | hval
  · exact Or.inl ((Fin.ext hval : j = ⟨0, by simp⟩) ▸ hj)
  · exact Or.inr ((Fin.ext hval : j = ⟨1, by simp⟩) ▸ hj)

section RootFieldAut

local instance quinticFactSplitsSplittingField (f : F[X]) :
    Fact ((f.map (algebraMap F f.SplittingField)).Splits) :=
  ⟨SplittingField.splits f⟩

/-- For an irreducible separable quintic, its label is determined by the order of its Galois
group. -/
theorem hasGaloisLabel_five_iff_natCard_gal (hsep : f.Separable) (hirr : Irreducible f)
    (hdeg : f.natDegree = 5) :
    HasGaloisLabel f j ↔ Nat.card f.Gal = Nat.card (referenceSubgroup 5 j) := by
  constructor
  · exact HasGaloisLabel.natCard_gal
  · intro hcard
    obtain ⟨k, hlabel, -⟩ := existsUnique_hasGaloisLabel_five hsep hirr hdeg
    obtain ⟨e⟩ := nonempty_rootSet_splittingField_equiv_fin f hsep
    let e := e.trans (finCongr hdeg)
    let G := (Gal.galActionHom f f.SplittingField).range.map e.permCongrHom.toMonoidHom
    have he := hlabel.transitiveGroupLabel e
    have hG : MulAction.IsPretransitive G (Fin 5) := he.isPretransitive
    have hGcard : Nat.card G = Nat.card (referenceSubgroup 5 j) :=
      (he.natCard_eq.trans hlabel.natCard_gal.symm).trans hcard
    exact HasGaloisLabel.mk hsep hdeg e
      ((@transitiveGroupLabel_five_iff_natCard_eq _ G hG).mpr hGcard)

/-- A quintic whose root field has a nonidentity automorphism over the base field has label
`5T1`. The field `E` is generated by `x`, whose minimal polynomial is `q`. -/
theorem hasGaloisLabel_five_zero_of_exists_rootField_aut_ne_one
    {F : Type*} [Field F] {q : F[X]} (hdeg : q.natDegree = 5)
    (E : Type*) [Field E] [Algebra F E] (x : E)
    (hminpoly : minpoly F x = q) (hgen : F⟮x⟯ = ⊤)
    (hAut : ∃ σ : E ≃ₐ[F] E, σ ≠ 1) :
    HasGaloisLabel q (⟨0, by simp⟩ : TransitiveGroupIndex 5) := by
  have hq : q ≠ 0 := by
    intro h
    simp [h] at hdeg
  have hx : IsIntegral F x := minpoly.ne_zero_iff.mp (hminpoly ▸ hq)
  have hirr : Irreducible q := hminpoly ▸ minpoly.irreducible hx
  obtain ⟨hsep, hcard⟩ :=
    separable_and_natCard_gal_eq_natDegree_of_prime_of_exists_aut_ne_one F q
      (hdeg ▸ (by decide : Nat.Prime 5)) E x hminpoly hgen hAut
  apply (hasGaloisLabel_five_iff_natCard_gal hsep hirr hdeg).mpr
  simpa only [hdeg, natCard_referenceSubgroup_five_zero] using hcard

end RootFieldAut

end TauCeti
