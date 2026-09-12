/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.PolynomialGaloisGroup
public import Mathlib.GroupTheory.GroupAction.Primitive
public import TauCeti.FieldTheory.Galois.FixedField

/-!
# Point stabilizers of the Galois action on the roots

Let `p` be a polynomial over a field `F` and let `L = p.SplittingField`. The Galois group
`Polynomial.Gal p` acts on `p.rootSet L`, and this file identifies the stabilizer of a root `x`
with a relative Galois group: it is the subgroup of `p.Gal` fixing the simple extension `F⟮x⟯`
pointwise. Every further reading of the action against the Galois correspondence goes through
that identification.

Three consequences follow, each with the hypothesis it needs. For separable `p` the splitting
field is Galois over `F`, so the fixed field of the stabilizer is `F⟮x⟯` again and the
correspondence loses nothing; the index of the stabilizer is then `[F⟮x⟯ : F]`, which for
irreducible `p` is `p.natDegree`. For `p` irreducible and separable of degree greater than one,
the action is primitive exactly when `F⟮x⟯` is an atom, that is, exactly when `F⟮x⟯ / F` has no
intermediate field other than its two ends.

## Main results

* `TauCeti.stabilizer_eq_fixingSubgroup_adjoin`: the stabilizer of a root is the fixing subgroup
  of the field the root generates.
* `TauCeti.fixedField_stabilizer`: for separable `p`, the field it fixes is that same field.
* `TauCeti.index_stabilizer`, `TauCeti.index_stabilizer_eq_natDegree`: the index of the
  stabilizer is the degree of the minimal polynomial of the root, so for irreducible `p` it is
  `p.natDegree`.
* `TauCeti.stabilizer_eq_bot_iff_adjoin_eq_top`,
  `TauCeti.stabilizer_eq_top_iff_adjoin_eq_bot`: the two ends of the correspondence, a root that
  generates the whole splitting field and a root that lies in the base field.
* `TauCeti.isPreprimitive_iff_isAtom_adjoin`: for irreducible separable `p` of degree greater
  than one, the root action is primitive exactly when `F⟮x⟯` admits no proper intermediate
  field.
* `TauCeti.isPreprimitive_of_prime_natDegree`: an irreducible separable polynomial of prime
  degree has a primitive root action.

## Implementation notes

The action used here is Mathlib's `Polynomial.Gal.galActionAux`, the intrinsic action on
`p.rootSet p.SplittingField`, for which `↑(g • x)` is literally `g ↑x`. Mathlib also has
`Polynomial.Gal.galAction` on `p.rootSet E` for a splitting extension `E`, but its instance for
`E = p.SplittingField` is the transport of `galActionAux` along `Polynomial.Gal.rootsEquivRoots`,
which goes through the `Algebra p.SplittingField p.SplittingField` instance built from
`IsSplittingField.lift` rather than through the identity. The two actions are isomorphic but not
the same instance, and only the intrinsic one has stabilizers that the Galois correspondence
reads directly. No `Fact` instance is introduced below, so `galActionAux` is the only candidate
and no ambiguity arises. For the same reason `TauCeti.isPretransitive_of_irreducible` is proved
here rather than taken from `Polynomial.Gal.galAction_isPretransitive`.
-/

public section

namespace TauCeti

open Polynomial IntermediateField MulAction

variable {F : Type*} [Field F] {p : F[X]}

/-! ### The stabilizer of a root -/

/-- The Galois action on the roots in the splitting field is the action by evaluation. -/
@[simp]
theorem _root_.Polynomial.Gal.coe_smul (g : p.Gal) (x : p.rootSet p.SplittingField) :
    ((g • x : p.rootSet p.SplittingField) : p.SplittingField) = g x :=
  rfl

/-- **The stabilizer of a root is a relative Galois group.** An automorphism of the splitting
field fixes a root `x` exactly when it fixes the subfield `F⟮x⟯` pointwise, so the point
stabilizer of the root action is the fixing subgroup of that subfield.

No hypothesis on `p` is needed: the statement is about one root and the field it generates, not
about the polynomial. -/
theorem stabilizer_eq_fixingSubgroup_adjoin (x : p.rootSet p.SplittingField) :
    stabilizer p.Gal x = F⟮(x : p.SplittingField)⟯.fixingSubgroup := by
  ext σ
  rw [MulAction.mem_stabilizer_iff, Subtype.ext_iff, Polynomial.Gal.coe_smul,
    IntermediateField.fixingSubgroup_adjoin_simple]
  exact Iff.rfl

/-- **The field a root generates is recovered from its stabilizer.** For separable `p` the
splitting field is Galois over `F`, so the fixed field of the stabilizer of `x` is `F⟮x⟯`. -/
theorem fixedField_stabilizer (hsep : p.Separable) (x : p.rootSet p.SplittingField) :
    IntermediateField.fixedField (stabilizer p.Gal x) = F⟮(x : p.SplittingField)⟯ := by
  have : IsGalois F p.SplittingField := IsGalois.of_separable_splitting_field hsep
  rw [stabilizer_eq_fixingSubgroup_adjoin, IsGalois.fixedField_fixingSubgroup]

/-! ### The index of a point stabilizer -/

/-- **The index of a point stabilizer is the degree of the minimal polynomial of the point.** The
index of the fixing subgroup of an intermediate field is the degree of that field over the base,
and `F⟮x⟯` has the degree of the minimal polynomial of `x`. -/
theorem index_stabilizer (hsep : p.Separable) (x : p.rootSet p.SplittingField) :
    (stabilizer p.Gal x).index = (minpoly F (x : p.SplittingField)).natDegree := by
  have : IsGalois F p.SplittingField := IsGalois.of_separable_splitting_field hsep
  rw [stabilizer_eq_fixingSubgroup_adjoin,
    ← IntermediateField.adjoin.finrank (IsIntegral.of_finite F (x : p.SplittingField))]
  exact (IntermediateField.finrank_eq_fixingSubgroup_index _ F⟮(x : p.SplittingField)⟯).symm

/-- **For an irreducible polynomial every point stabilizer has index the degree.** This is the
form the permutation representation uses: a transitive subgroup of degree `n` has point
stabilizers of index `n`. -/
theorem index_stabilizer_eq_natDegree (hp : Irreducible p) (hsep : p.Separable)
    (x : p.rootSet p.SplittingField) : (stabilizer p.Gal x).index = p.natDegree := by
  have hmin : (minpoly F (x : p.SplittingField)).natDegree = p.natDegree := by
    rw [← minpoly.eq_of_irreducible hp (aeval_eq_zero_of_mem_rootSet x.2)]
    exact natDegree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.mpr hp.ne_zero))
  rw [index_stabilizer hsep, hmin]

/-! ### The two ends of the correspondence -/

/-- **A root with trivial stabilizer is a primitive element**, and conversely. Together with
`TauCeti.stabilizer_eq_top_iff_adjoin_eq_bot` this pins the orientation of the correspondence:
the stabilizer shrinks as the field the root generates grows. -/
theorem stabilizer_eq_bot_iff_adjoin_eq_top (hsep : p.Separable)
    (x : p.rootSet p.SplittingField) :
    stabilizer p.Gal x = ⊥ ↔ F⟮(x : p.SplittingField)⟯ = ⊤ := by
  have : IsGalois F p.SplittingField := IsGalois.of_separable_splitting_field hsep
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← fixedField_stabilizer hsep x, h]
    exact IntermediateField.fixedField_bot
  · rw [stabilizer_eq_fixingSubgroup_adjoin, h]
    exact IntermediateField.fixingSubgroup_top

/-- **A root fixed by the whole Galois group lies in the base field**, and conversely. -/
theorem stabilizer_eq_top_iff_adjoin_eq_bot (hsep : p.Separable)
    (x : p.rootSet p.SplittingField) :
    stabilizer p.Gal x = ⊤ ↔ F⟮(x : p.SplittingField)⟯ = ⊥ := by
  have : IsGalois F p.SplittingField := IsGalois.of_separable_splitting_field hsep
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← fixedField_stabilizer hsep x, h]
    exact IsGalois.fixedField_top
  · rw [stabilizer_eq_fixingSubgroup_adjoin, h]
    exact IntermediateField.fixingSubgroup_bot

/-! ### Transitivity and primitivity -/

/-- **The root action of an irreducible polynomial is transitive.** Two roots of an irreducible
polynomial have the same minimal polynomial, and a normal extension moves one to the other.

This is `Polynomial.Gal.galAction_isPretransitive` for the intrinsic action on the roots in the
splitting field; see the implementation notes for why that instance is not the one Mathlib's
statement carries. -/
theorem isPretransitive_of_irreducible (hp : Irreducible p) :
    IsPretransitive p.Gal (p.rootSet p.SplittingField) := by
  refine ⟨fun x y => ?_⟩
  have hx := minpoly.eq_of_irreducible hp (aeval_eq_zero_of_mem_rootSet x.2)
  have hy := minpoly.eq_of_irreducible hp (aeval_eq_zero_of_mem_rootSet y.2)
  obtain ⟨g, hg⟩ := (Normal.minpoly_eq_iff_mem_orbit p.SplittingField).mp (hy.symm.trans hx)
  exact ⟨g, Subtype.ext hg⟩

/-- **Primitivity of the root action is the absence of intermediate fields.** For an irreducible
separable `p` of degree greater than one, the action of `p.Gal` on the roots is primitive exactly
when `F⟮x⟯` is an atom, that is, exactly when no field lies strictly between `F` and `F⟮x⟯`.

The degree hypothesis cannot be dropped. For linear `p` the root set is a single point, on which
every action is primitive, while `F⟮x⟯ = ⊥` is not an atom. It is the hypothesis that Mathlib's
`MulAction.isCoatom_stabilizer_iff_preprimitive` carries as `[Nontrivial X]`.

The conclusion does not depend on the chosen root, since the action is transitive; `x` appears on
the right only to name a field. -/
theorem isPreprimitive_iff_isAtom_adjoin (hp : Irreducible p) (hsep : p.Separable)
    (hdeg : 1 < p.natDegree) (x : p.rootSet p.SplittingField) :
    IsPreprimitive p.Gal (p.rootSet p.SplittingField) ↔
      IsAtom F⟮(x : p.SplittingField)⟯ := by
  have hgal : IsGalois F p.SplittingField := IsGalois.of_separable_splitting_field hsep
  have htr : IsPretransitive p.Gal (p.rootSet p.SplittingField) :=
    isPretransitive_of_irreducible hp
  have hcard : Fintype.card (p.rootSet p.SplittingField) = p.natDegree :=
    Polynomial.card_rootSet_eq_natDegree hsep (IsSplittingField.splits p.SplittingField p)
  have hnt : Nontrivial (p.rootSet p.SplittingField) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  rw [← isCoatom_stabilizer_iff_preprimitive p.Gal x, stabilizer_eq_fixingSubgroup_adjoin]
  exact IntermediateField.isCoatom_fixingSubgroup_iff_isAtom F⟮(x : p.SplittingField)⟯

/-- **An irreducible separable polynomial of prime degree has a primitive root action.** A
transitive action on a set of prime cardinality is primitive, and the roots of a separable
polynomial number its degree. -/
theorem isPreprimitive_of_prime_natDegree (hp : Irreducible p) (hsep : p.Separable)
    (hprime : p.natDegree.Prime) : IsPreprimitive p.Gal (p.rootSet p.SplittingField) := by
  have htr : IsPretransitive p.Gal (p.rootSet p.SplittingField) :=
    isPretransitive_of_irreducible hp
  refine IsPreprimitive.of_prime_card ?_
  rwa [Nat.card_eq_fintype_card,
    Polynomial.card_rootSet_eq_natDegree hsep (IsSplittingField.splits p.SplittingField p)]

end TauCeti
