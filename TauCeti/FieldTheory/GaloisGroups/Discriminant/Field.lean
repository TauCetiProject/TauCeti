/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisGroups.Discriminant.Basic
import Mathlib.GroupTheory.GroupAction.Transitive
import TauCeti.Algebra.Polynomial.AlgebraMap
import TauCeti.FieldTheory.GaloisGroups.Orbits
import TauCeti.FieldTheory.Kummer.Extension

/-!
# The discriminant field `F(√disc f)`

Let `f` be a polynomial over a field `F` and let `E` be an extension of `F`. The **discriminant
field** of `f` in `E` is the subfield of `E` generated over `F` by the square roots of
`Polynomial.discr f` that lie in `E`. It is `TauCeti.discrField f E`, defined as the adjunction to
`F` of the root set of `X ^ 2 - C f.discr` in `E`.

Whenever `E` contains an element `δ` with `δ ^ 2 = discr f` — for monic separable `f` splitting in
`E` the square root `TauCeti.discrSqrt` of the previous file is one — the definition collapses to
the simple extension `F⟮δ⟯`, because the only other square root of the discriminant is `-δ`, and it
is then a splitting field of `X ^ 2 - C f.discr` over `F`. (When `E` contains no square root at all
the root set is empty and the discriminant field is just `F`.) In particular the discriminant field
does not depend on the numbering of the roots that `discrSqrt` is computed from, even though
`discrSqrt` itself changes sign with it. From that description one reads off the two
possibilities: `F⟮δ⟯` is `F` when `discr f` is a square in `F`, and a quadratic extension of `F`
otherwise. Away from characteristic `2` it is moreover a Galois extension of `F` as soon as the
discriminant is nonzero, since `X ^ 2 - C f.discr` is then separable.

The discriminant field is determined by the discriminant alone. The comparison theorem
`TauCeti.fixedField_evenAutSubgroup` characterizes it additionally through the action on the roots
of `f`: in a Galois splitting extension and away from characteristic `2`, the discriminant field is
exactly the field fixed by the automorphisms that permute the roots of `f` evenly. That subgroup is
`TauCeti.evenAutSubgroup f E`. The transformation law `AlgEquiv.map_discrSqrt` makes both
inclusions short: an even automorphism fixes `δ`, and an odd one negates it, which is a genuine move
because `δ ≠ 0` and `2 ≠ 0`.

The same comparison reads factorizations over the discriminant field on the Galois image: in a
normal splitting extension, `f` stays irreducible over its discriminant field exactly when the even
permutations in the Galois image act transitively on the roots
(`TauCeti.irreducible_map_discrField_iff`). Since all discriminant fields are splitting fields of
`X ^ 2 - C f.discr`, whether `f` stays irreducible over one does not depend on the extension `E` in
which it is taken (`TauCeti.irreducible_map_discrField_congr`). This is the datum that separates the
cyclic quartic group from the dihedral one, whose even parts are respectively intransitive and
transitive. The discriminant test of the previous file is recovered here as the statement that the
discriminant field is trivial exactly when the Galois image is contained in the alternating group.

## Main definitions

* `TauCeti.discrField`: the subfield of `E` generated over `F` by the square roots of `discr f`.
* `TauCeti.evenAutSubgroup`: the automorphisms of a splitting extension `E` over `F` that induce an
  even permutation of the roots of `f`.

## Main results

* `TauCeti.discrField_eq_adjoin_simple`: a square root `δ` of the discriminant generates the
  discriminant field.
* `TauCeti.isSplittingField_discrField`: if `E` contains a square root of the discriminant, the
  discriminant field is a splitting field of `X ^ 2 - C f.discr`.
* `TauCeti.discrField_map`: it is natural in the extension.
* `TauCeti.discrField_baseChange`: after extending the base field, it is the compositum of the
  new base field with the original discriminant field.
* `TauCeti.discrField_eq_bot_iff`, `TauCeti.finrank_discrField_eq_two`: the discriminant field is
  `F` exactly when the discriminant is a square, and has degree `2` otherwise.
* `TauCeti.isGalois_discrField`: away from characteristic `2`, and for nonzero discriminant, it is
  a Galois extension of `F`.
* `TauCeti.irreducible_map_discrField_congr`: irreducibility over the discriminant field does not
  depend on the extension in which the discriminant field is taken.
* `TauCeti.fixedField_evenAutSubgroup`: **the comparison theorem**, that the discriminant field is
  the fixed field of the even part of the Galois group, and `TauCeti.fixingSubgroup_discrField`:
  conversely, the even part of the Galois group is the subgroup fixing the discriminant field.
* `TauCeti.irreducible_map_discrField_iff`: `f` stays irreducible over the discriminant field
  exactly when the even part of its Galois image is transitive on the roots.
* `TauCeti.discrField_eq_bot_iff_range_le_alternatingGroup`,
  `TauCeti.finrank_discrField_eq_two_iff`: the discriminant test, read on the discriminant field.

## References

* [H. Cohen, *A Course in Computational Algebraic Number Theory*][cohen1993], §6.3.
-/

public section

open Polynomial

open scoped IntermediateField

namespace TauCeti

universe u v w

variable {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E]

/-! ## The discriminant field -/

variable {f : F[X]}

/-- **The discriminant field of `f` in `E`**: the subfield of `E` generated over `F` by the square
roots of `Polynomial.discr f` that lie in `E`. If `E` contains such a square root this is a
splitting field of `X ^ 2 - C f.discr` over `F` (`TauCeti.isSplittingField_discrField`); if it
contains none, the root set is empty and the discriminant field is `F` itself.

`TauCeti.discrField_eq_adjoin_simple` describes it as `F⟮δ⟯` for any square root `δ` of the
discriminant in `E`. Stating it as an adjunction of the whole root set instead of a simple
extension keeps it independent of the choice of square root, hence of the numbering of the roots of
`f` that `TauCeti.discrSqrt` is computed from. -/
def discrField (f : F[X]) (E : Type v) [Field E] [Algebra F E] : IntermediateField F E :=
  IntermediateField.adjoin F ((X ^ 2 - C f.discr).rootSet E)

/-- Any square root of the discriminant in `E` generates the discriminant field. -/
theorem discrField_eq_adjoin_simple {δ : E} (hδ : δ ^ 2 = algebraMap F E f.discr) :
    discrField f E = F⟮δ⟯ :=
  IntermediateField.adjoin_rootSet_X_pow_two_sub_C hδ

/-- If `E` contains a square root of the discriminant, then the discriminant field is a splitting
field of `X ^ 2 - C f.discr` over `F`; `Polynomial.IsSplittingField.algEquiv` therefore identifies
it with the abstract splitting field of that polynomial. -/
theorem isSplittingField_discrField {δ : E} (hδ : δ ^ 2 = algebraMap F E f.discr) :
    IsSplittingField F (discrField f E) (X ^ 2 - C f.discr) :=
  IntermediateField.adjoin_rootSet_isSplittingField (Polynomial.splits_map_X_pow_two_sub_C hδ)

/-- **Naturality in the extension.** An `F`-isomorphism of extensions carries the discriminant
field of `f` in one to the discriminant field of `f` in the other. Taking `E' = E` it says that
every `F`-automorphism of `E` maps the discriminant field onto itself. -/
@[simp]
theorem discrField_map {E' : Type w} [Field E'] [Algebra F E'] (ψ : E ≃ₐ[F] E') :
    (discrField f E).map ψ.toAlgHom = discrField f E' := by
  rw [discrField, discrField, IntermediateField.adjoin_map]
  congr 1
  refine Set.Subset.antisymm ?_ fun y hy ↦ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact Polynomial.rootSet_mapsTo ψ.toAlgHom hx
  · exact ⟨ψ.symm y, Polynomial.rootSet_mapsTo ψ.symm.toAlgHom hy, ψ.apply_symm_apply y⟩

/-- **Base change of the discriminant field.** In a tower `E / K / F`, the discriminant field of
`f` after extending scalars from `F` to `K` is the compositum in `E` of `K` with the original
discriminant field. Since a field extension preserves polynomial degree, no hypothesis on `f` is
needed. When `E` contains a square root of `f.discr` and the image of `f.discr` remains a
nonsquare in `K`, the base-changed field is still quadratic over `K` by
`TauCeti.finrank_discrField_baseChange_eq_two`. -/
theorem discrField_baseChange {K : Type w} [Field K] [Algebra F K] [Algebra K E]
    [IsScalarTower F K E] :
    discrField (f.map (algebraMap F K)) E =
      IntermediateField.adjoin K (discrField f E : Set E) := by
  have hdeg : (f.map (algebraMap F K)).natDegree = f.natDegree :=
    Polynomial.natDegree_map (algebraMap F K)
  have hroots :
      (X ^ 2 - C ((algebraMap F K) f.discr) : K[X]).rootSet E =
        (X ^ 2 - C f.discr : F[X]).rootSet E := by
    have hpoly : (X ^ 2 - C ((algebraMap F K) f.discr) : K[X]) =
        (X ^ 2 - C f.discr : F[X]).map (algebraMap F K) := by
      rw [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]
    rw [hpoly, Polynomial.rootSet_map E K]
  rw [discrField, discrField, Polynomial.discr_map_of_natDegree_eq _ hdeg, hroots,
    IntermediateField.adjoin_adjoin_right]

/-- **The trivial case.** Once `E` contains a square root of the discriminant, the discriminant
field is the base field exactly when the discriminant is a square in the base field. -/
theorem discrField_eq_bot_iff {δ : E} (hδ : δ ^ 2 = algebraMap F E f.discr) :
    discrField f E = ⊥ ↔ IsSquare f.discr := by
  rw [discrField_eq_adjoin_simple hδ, IntermediateField.adjoin_simple_eq_bot_iff,
    IntermediateField.mem_bot]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, (algebraMap F E).injective (by rw [map_mul, ← sq, hδ])⟩
  · rintro ⟨c, hc⟩
    have hc' : algebraMap F E f.discr = algebraMap F E c * algebraMap F E c := by
      rw [← map_mul, ← hc]
    have hfac : (δ - algebraMap F E c) * (δ + algebraMap F E c) = 0 := by
      linear_combination hδ + hc'
    rcases mul_eq_zero.mp hfac with h | h
    · exact ⟨c, (sub_eq_zero.mp h).symm⟩
    · exact ⟨-c, by rw [map_neg]; exact (eq_neg_of_add_eq_zero_left h).symm⟩

/-- The discriminant field is trivial exactly when it has degree one over the base field. -/
theorem finrank_discrField_eq_one_iff {δ : E} (hδ : δ ^ 2 = algebraMap F E f.discr) :
    Module.finrank F (discrField f E) = 1 ↔ IsSquare f.discr :=
  IntermediateField.finrank_eq_one_iff.trans (discrField_eq_bot_iff hδ)

/-- **The quadratic case.** When the discriminant is not a square in the base field, the
discriminant field is a quadratic extension of it. -/
theorem finrank_discrField_eq_two {δ : E} (hδ : δ ^ 2 = algebraMap F E f.discr)
    (hsq : ¬ IsSquare f.discr) : Module.finrank F (discrField f E) = 2 := by
  have haeval : (aeval δ) ((X : F[X]) ^ 2 - C f.discr) = 0 := by
    rw [map_sub, aeval_X_pow, aeval_C, hδ, sub_self]
  have hint : IsIntegral F δ := ⟨_, monic_X_pow_sub_C f.discr two_ne_zero, haeval⟩
  have hrank : Module.finrank F (discrField f E) = (minpoly F δ).natDegree := by
    rw [discrField_eq_adjoin_simple hδ, IntermediateField.adjoin.finrank hint]
  have hle : (minpoly F δ).natDegree ≤ 2 := by
    have hdvd := Polynomial.natDegree_le_of_dvd (minpoly.dvd F δ haeval)
      (monic_X_pow_sub_C f.discr two_ne_zero).ne_zero
    rwa [natDegree_X_pow_sub_C] at hdvd
  have hpos : 0 < (minpoly F δ).natDegree := minpoly.natDegree_pos hint
  have hne : (minpoly F δ).natDegree ≠ 1 := fun h1 ↦
    hsq ((finrank_discrField_eq_one_iff hδ).mp (hrank.trans h1))
  rw [hrank]
  omega

/-- If `E` contains a square root of the discriminant and the discriminant remains a nonsquare
after extending scalars from `F` to `K`, then the compositum of `K` with the original
discriminant field is quadratic over `K`. This is the quadratic, nonsplit case of
`TauCeti.discrField_baseChange`. -/
theorem finrank_discrField_baseChange_eq_two {K : Type w} [Field K] [Algebra F K] [Algebra K E]
    [IsScalarTower F K E] {δ : E} (hδ : δ ^ 2 = algebraMap F E f.discr)
    (hsq : ¬ IsSquare ((algebraMap F K) f.discr)) :
    Module.finrank K (IntermediateField.adjoin K (discrField f E : Set E)) = 2 := by
  have hdeg : (f.map (algebraMap F K)).natDegree = f.natDegree :=
    Polynomial.natDegree_map (algebraMap F K)
  rw [← discrField_baseChange]
  apply finrank_discrField_eq_two (f := f.map (algebraMap F K)) (E := E) (δ := δ)
  · rw [Polynomial.discr_map_of_natDegree_eq _ hdeg,
      ← IsScalarTower.algebraMap_apply F K E]
    exact hδ
  · rwa [Polynomial.discr_map_of_natDegree_eq _ hdeg]

/-- Away from characteristic `2`, the discriminant field of a polynomial with nonzero discriminant
is a Galois extension of the base field: it is the splitting field of `X ^ 2 - C f.discr`, which is
separable because the discriminant is nonzero and `2` is invertible. For a monic polynomial,
`Polynomial.Monic.discr_ne_zero_iff` reads the hypothesis as separability of `f`. -/
theorem isGalois_discrField {δ : E} (hδ : δ ^ 2 = algebraMap F E f.discr) (hdisc : f.discr ≠ 0)
    (hchar : ringChar F ≠ 2) : IsGalois F (discrField f E) := by
  have hsep2 : ((X : F[X]) ^ 2 - C f.discr).Separable :=
    separable_X_pow_sub_C _ (by simpa using Ring.two_ne_zero hchar) hdisc
  have := isSplittingField_discrField hδ
  exact IsGalois.of_separable_splitting_field hsep2

/-- **Irreducibility over the discriminant field does not depend on the ambient extension.** If
`E` and `E'` both contain a square root of the discriminant of `f`, then a polynomial `g` is
irreducible over the discriminant field of `f` in `E` exactly when it is irreducible over the
discriminant field of `f` in `E'`: both are splitting fields of `X ^ 2 - C f.discr`, hence
isomorphic over `F`. -/
theorem irreducible_map_discrField_congr {E' : Type w} [Field E'] [Algebra F E'] {δ : E}
    {δ' : E'} (hδ : δ ^ 2 = algebraMap F E f.discr) (hδ' : δ' ^ 2 = algebraMap F E' f.discr)
    (g : F[X]) :
    Irreducible (g.map (algebraMap F (discrField f E))) ↔
      Irreducible (g.map (algebraMap F (discrField f E'))) := by
  have := isSplittingField_discrField hδ
  have := isSplittingField_discrField hδ'
  exact irreducible_map_iff_of_algEquiv
    ((IsSplittingField.algEquiv _ (X ^ 2 - C f.discr)).trans
      (IsSplittingField.algEquiv _ (X ^ 2 - C f.discr)).symm) g

/-! ## The comparison with the even part of the Galois group -/

section Galois

variable [Fact ((f.map (algebraMap F E)).Splits)]

open scoped Classical in
/-- **The even part of the Galois group.** For a splitting extension `E` of `f` over `F`, this is
the subgroup of automorphisms of `E` over `F` that permute the roots of `f` evenly. It is the
kernel of the sign of the root action, hence a normal subgroup of index at most two. -/
noncomputable def evenAutSubgroup (f : F[X]) (E : Type v) [Field E] [Algebra F E]
    [Fact ((f.map (algebraMap F E)).Splits)] : Subgroup (E ≃ₐ[F] E) :=
  ((alternatingGroup (f.rootSet E)).comap (Gal.galActionHom f E)).comap (Gal.restrict f E)

open scoped Classical in
@[simp]
theorem mem_evenAutSubgroup {ϕ : E ≃ₐ[F] E} :
    ϕ ∈ evenAutSubgroup f E ↔
      Equiv.Perm.sign (Gal.galActionHom f E (Gal.restrict f E ϕ)) = 1 :=
  Equiv.Perm.mem_alternatingGroup

open scoped Classical in
/-- The even part of the Galois group is the subgroup fixing the root-difference product.
Both inclusions are the transformation law `AlgEquiv.map_discrSqrt`: an even automorphism fixes the
product, and an odd one negates it, which moves it because it is nonzero and `2 ≠ 0`. -/
theorem evenAutSubgroup_eq_fixingSubgroup (hchar : ringChar F ≠ 2)
    (e : Fin f.natDegree ≃ f.rootSet E) :
    evenAutSubgroup f E = IntermediateField.fixingSubgroup F⟮discrSqrt e⟯ := by
  have h2 : (2 : E) ≠ 0 := by
    rw [← map_ofNat (algebraMap F E) 2]
    exact (map_ne_zero_iff _ (algebraMap F E).injective).mpr (Ring.two_ne_zero hchar)
  refine le_antisymm ?_ fun ϕ hϕ ↦ ?_
  · rw [← IntermediateField.le_iff_le, IntermediateField.adjoin_simple_le_iff,
      IntermediateField.mem_fixedField_iff]
    intro ϕ hϕ
    rw [mem_evenAutSubgroup] at hϕ
    rw [AlgEquiv.map_discrSqrt, hϕ, one_smul]
  · have hfix : Equiv.Perm.sign (Gal.galActionHom f E (Gal.restrict f E ϕ)) •
        discrSqrt (f := f) e = discrSqrt (f := f) e := by
      rw [← AlgEquiv.map_discrSqrt]
      exact (IntermediateField.mem_fixingSubgroup_iff _ ϕ).mp hϕ _
        (IntermediateField.mem_adjoin_simple_self F _)
    rw [mem_evenAutSubgroup]
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Gal.galActionHom f E (Gal.restrict f E ϕ)))
      with h1 | h1
    · exact h1
    -- An odd automorphism would negate the nonzero product and fix it, forcing `2 = 0`.
    · refine absurd ?_ (discrSqrt_ne_zero e)
      rw [h1] at hfix
      have hdouble : (2 : E) * discrSqrt (f := f) e = 0 := by
        simp only [Units.smul_def, Units.val_neg, Units.val_one, neg_smul, one_smul] at hfix
        linear_combination -hfix
      exact (mul_eq_zero.mp hdouble).resolve_left h2

/-- **The comparison theorem, from the other side.** Away from characteristic `2`, the
automorphisms of a splitting extension that fix the discriminant field of a monic separable
polynomial are exactly those acting on its roots by an even permutation. Unlike
`TauCeti.fixedField_evenAutSubgroup`, this needs no normality of the extension. -/
theorem fixingSubgroup_discrField (hf : f.Monic) (hsep : f.Separable) (hchar : ringChar F ≠ 2) :
    (discrField f E).fixingSubgroup = evenAutSubgroup f E := by
  obtain ⟨e⟩ : Nonempty (Fin f.natDegree ≃ f.rootSet E) :=
    ⟨(Fintype.equivFinOfCardEq (card_rootSet_eq_natDegree hsep Fact.out)).symm⟩
  rw [discrField_eq_adjoin_simple (hf.discrSqrt_sq hsep e),
    evenAutSubgroup_eq_fixingSubgroup hchar e]

open scoped Classical in
/-- **The comparison theorem.** In a Galois splitting extension, and away from characteristic `2`,
the discriminant field of a monic separable polynomial is the field fixed by the automorphisms
acting on the roots by an even permutation. -/
theorem fixedField_evenAutSubgroup [IsGalois F E] (hf : f.Monic) (hsep : f.Separable)
    (hchar : ringChar F ≠ 2) :
    IntermediateField.fixedField (evenAutSubgroup f E) = discrField f E := by
  rw [← fixingSubgroup_discrField hf hsep hchar, InfiniteGalois.fixedField_fixingSubgroup]

open scoped Classical in
/-- In a normal splitting extension, the even part of the automorphism group acts transitively on
the roots exactly when the even permutations in the Galois image do. The root action maps the
former onto the latter, because every element of `f.Gal` lifts to an automorphism of `E`. -/
theorem isPretransitive_evenAutSubgroup_iff [Normal F E] :
    MulAction.IsPretransitive (evenAutSubgroup f E) (f.rootSet E) ↔
      MulAction.IsPretransitive
        ((Gal.galActionHom f E).range ⊓ alternatingGroup (f.rootSet E) :
          Subgroup (Equiv.Perm (f.rootSet E))) (f.rootSet E) := by
  let φ : evenAutSubgroup f E →
      ((Gal.galActionHom f E).range ⊓ alternatingGroup (f.rootSet E) :
        Subgroup (Equiv.Perm (f.rootSet E))) :=
    fun σ ↦ ⟨Gal.galActionHom f E (Gal.restrict f E σ), ⟨_, rfl⟩, σ.2⟩
  refine MulAction.isPretransitive_congr (φ := φ)
    (f := ⟨id, fun σ x ↦ Subtype.ext ?_⟩) ?_ Function.bijective_id
  · simp [φ, Subgroup.smul_def, Equiv.Perm.smul_def, Gal.galActionHom_restrict, AlgEquiv.smul_def]
  · rintro ⟨π, ⟨g, rfl⟩, hπ⟩
    obtain ⟨σ, rfl⟩ := Gal.restrict_surjective f E g
    exact ⟨⟨σ, hπ⟩, rfl⟩

open scoped Classical in
/-- **Irreducibility over the discriminant field.** In a normal splitting extension, and away from
characteristic `2`, a monic separable polynomial of positive degree stays irreducible over its
discriminant field exactly when the even permutations in its Galois image act transitively on its
roots.

By `TauCeti.irreducible_map_discrField_congr`, the left-hand side is the same for the discriminant
field taken in any extension containing a square root of the discriminant. -/
theorem irreducible_map_discrField_iff [Normal F E] (hf : f.Monic) (hsep : f.Separable)
    (hchar : ringChar F ≠ 2) (hdeg : 0 < f.natDegree) :
    Irreducible (f.map (algebraMap F (discrField f E))) ↔
      MulAction.IsPretransitive
        ((Gal.galActionHom f E).range ⊓ alternatingGroup (f.rootSet E) :
          Subgroup (Equiv.Perm (f.rootSet E))) (f.rootSet E) := by
  rw [irreducible_map_iff_isPretransitive_fixingSubgroup E _ hsep hdeg,
    fixingSubgroup_discrField hf hsep hchar, isPretransitive_evenAutSubgroup_iff]

open scoped Classical in
/-- **The discriminant test, read on the discriminant field.** The discriminant field is trivial
exactly when the Galois image consists of even permutations of the roots. -/
theorem discrField_eq_bot_iff_range_le_alternatingGroup [IsGalois F E] (hf : f.Monic)
    (hsep : f.Separable) (hchar : ringChar F ≠ 2) :
    discrField f E = ⊥ ↔ (Gal.galActionHom f E).range ≤ alternatingGroup (f.rootSet E) := by
  obtain ⟨e⟩ : Nonempty (Fin f.natDegree ≃ f.rootSet E) :=
    ⟨(Fintype.equivFinOfCardEq (card_rootSet_eq_natDegree hsep Fact.out)).symm⟩
  rw [discrField_eq_bot_iff (hf.discrSqrt_sq hsep e)]
  exact hf.isSquare_discr_iff_range_le_alternatingGroup hsep hchar

open scoped Classical in
/-- The discriminant field is a quadratic extension exactly when the Galois image contains an odd
permutation of the roots. This is the separation the quartic decision table reads. -/
theorem finrank_discrField_eq_two_iff [IsGalois F E] (hf : f.Monic) (hsep : f.Separable)
    (hchar : ringChar F ≠ 2) :
    Module.finrank F (discrField f E) = 2 ↔
      ¬ (Gal.galActionHom f E).range ≤ alternatingGroup (f.rootSet E) := by
  obtain ⟨e⟩ : Nonempty (Fin f.natDegree ≃ f.rootSet E) :=
    ⟨(Fintype.equivFinOfCardEq (card_rootSet_eq_natDegree hsep Fact.out)).symm⟩
  have hδ := hf.discrSqrt_sq hsep e
  rw [← hf.isSquare_discr_iff_range_le_alternatingGroup (E := E) hsep hchar]
  refine ⟨fun h hsq ↦ ?_, finrank_discrField_eq_two hδ⟩
  rw [← finrank_discrField_eq_one_iff hδ] at hsq
  omega

end Galois

end TauCeti
