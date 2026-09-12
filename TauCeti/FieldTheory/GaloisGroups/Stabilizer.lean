/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.PolynomialGaloisGroup
public import TauCeti.FieldTheory.Galois.FixedField

/-!
# Point stabilizers of the Galois action on the roots

Let `p` be a polynomial over a field `F` and let `L = p.SplittingField`. The Galois group
`Polynomial.Gal p` acts on `p.rootSet L`, and this file identifies the stabilizer of a root `x`
with a relative Galois group: it is the subgroup of `p.Gal` fixing the simple extension `F⟮x⟯`
pointwise. Every further reading of the action against the Galois correspondence goes through
that identification.

The identification itself needs no hypothesis on `p`. Reading it back through the Galois
correspondence needs one, and the hypothesis it needs is `IsGalois F L`: that is what makes the
fixed field of the stabilizer `F⟮x⟯` again, and its index `[F⟮x⟯ : F]`, which for irreducible `p`
is `p.natDegree`. Separability of `p` supplies that instance through
`IsGalois.of_separable_splitting_field`, but it is not the weakest hypothesis that does: a power
of a separable irreducible polynomial is inseparable and still has a Galois splitting field.

## Main results

* `TauCeti.stabilizer_eq_fixingSubgroup_adjoin`: the stabilizer of a root is the fixing subgroup
  of the field the root generates.
* `TauCeti.fixedField_stabilizer`: for a Galois splitting field, the field the stabilizer fixes
  is that same field.
* `TauCeti.index_stabilizer_eq_minpoly_natDegree`,
  `TauCeti.index_stabilizer_eq_natDegree`: the index of the stabilizer is the degree of the
  minimal polynomial of the root, so for irreducible `p` it is `p.natDegree`.
* `TauCeti.stabilizer_eq_bot_iff_adjoin_eq_top`,
  `TauCeti.stabilizer_eq_top_iff_adjoin_eq_bot`: the two ends of the correspondence, a root that
  generates the whole splitting field and a root that lies in the base field.

## Implementation notes

The action used here is Mathlib's `Polynomial.Gal.galActionAux`, the intrinsic action on
`p.rootSet p.SplittingField`, for which `↑(g • x)` is literally `g ↑x`. Mathlib also has
`Polynomial.Gal.galAction` on `p.rootSet E` for a splitting extension `E`, but its instance for
`E = p.SplittingField` is the transport of `galActionAux` along `Polynomial.Gal.rootsEquivRoots`,
which goes through the `Algebra p.SplittingField p.SplittingField` instance built from
`IsSplittingField.lift` rather than through the identity. The two actions are isomorphic but not
the same instance, and only the intrinsic one has stabilizers that the Galois correspondence
reads directly. No `Fact` instance is introduced below, so `galActionAux` is the only candidate
and no ambiguity arises.
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

/-- **The field a root generates is recovered from its stabilizer.** When the splitting field is
Galois over `F` the fixed field of the stabilizer of `x` is `F⟮x⟯`. -/
theorem fixedField_stabilizer [IsGalois F p.SplittingField] (x : p.rootSet p.SplittingField) :
    IntermediateField.fixedField (stabilizer p.Gal x) = F⟮(x : p.SplittingField)⟯ := by
  rw [stabilizer_eq_fixingSubgroup_adjoin, IsGalois.fixedField_fixingSubgroup]

/-! ### The index of a point stabilizer -/

/-- **The index of a point stabilizer is the degree of the minimal polynomial of the point.** The
index of the fixing subgroup of an intermediate field is the degree of that field over the base,
and `F⟮x⟯` has the degree of the minimal polynomial of `x`; the splitting field being Galois over
`F` is what makes the correspondence apply. -/
theorem index_stabilizer_eq_minpoly_natDegree [IsGalois F p.SplittingField]
    (x : p.rootSet p.SplittingField) :
    (stabilizer p.Gal x).index = (minpoly F (x : p.SplittingField)).natDegree := by
  rw [stabilizer_eq_fixingSubgroup_adjoin,
    ← IntermediateField.adjoin.finrank (IsIntegral.of_finite F (x : p.SplittingField))]
  exact (IntermediateField.finrank_eq_fixingSubgroup_index _ F⟮(x : p.SplittingField)⟯).symm

/-- **For an irreducible polynomial every point stabilizer has index the degree.** This is the
form the permutation representation uses: a transitive subgroup of degree `n` has point
stabilizers of index `n`.

An irreducible `p` whose splitting field is Galois over `F` is separable, and an inseparable
irreducible polynomial has fewer roots than its degree; so the hypotheses here are the same as
irreducibility together with `p.Separable`, stated in the form the Galois correspondence uses. -/
theorem index_stabilizer_eq_natDegree [IsGalois F p.SplittingField] (hp : Irreducible p)
    (x : p.rootSet p.SplittingField) : (stabilizer p.Gal x).index = p.natDegree := by
  have hmin : (minpoly F (x : p.SplittingField)).natDegree = p.natDegree := by
    rw [← minpoly.eq_of_irreducible hp (aeval_eq_zero_of_mem_rootSet x.2)]
    exact natDegree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.mpr hp.ne_zero))
  rw [index_stabilizer_eq_minpoly_natDegree x, hmin]

/-! ### The two ends of the correspondence -/

/-- **A root with trivial stabilizer is a primitive element**, and conversely. Together with
`TauCeti.stabilizer_eq_top_iff_adjoin_eq_bot` this pins the orientation of the correspondence:
the stabilizer shrinks as the field the root generates grows. -/
theorem stabilizer_eq_bot_iff_adjoin_eq_top [IsGalois F p.SplittingField]
    (x : p.rootSet p.SplittingField) :
    stabilizer p.Gal x = ⊥ ↔ F⟮(x : p.SplittingField)⟯ = ⊤ := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← fixedField_stabilizer x, h]
    exact IntermediateField.fixedField_bot
  · rw [stabilizer_eq_fixingSubgroup_adjoin, h]
    exact IntermediateField.fixingSubgroup_top

/-- **A root fixed by the whole Galois group lies in the base field**, and conversely. The
splitting field being Galois over `F` is what makes the fixed field of the whole group `F`
itself; over an inseparable extension a root outside `F` can be fixed by every automorphism. -/
theorem stabilizer_eq_top_iff_adjoin_eq_bot [IsGalois F p.SplittingField]
    (x : p.rootSet p.SplittingField) :
    stabilizer p.Gal x = ⊤ ↔ F⟮(x : p.SplittingField)⟯ = ⊥ := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← fixedField_stabilizer x, h]
    exact IsGalois.fixedField_top
  · rw [stabilizer_eq_fixingSubgroup_adjoin, h]
    exact IntermediateField.fixingSubgroup_bot

end TauCeti
