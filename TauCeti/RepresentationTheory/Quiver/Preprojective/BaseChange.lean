/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.BaseChange
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Basic

/-!
# Base change for additive preprojective algebras

The additive preprojective algebra is defined over a commutative ring, but its presentation has
integer coefficients: the doubled paths are unchanged and only the coefficients are transported.
Consequently a ring homomorphism `f : k →+* l` gives a canonical coefficient map

```text
Π_k(Q) → Π_l(Q).
```

This is the presentation-level base-change map.  It is deliberately a semilinear `RingHom`: its
restriction to scalars is `f`, while the target is naturally an `l`-algebra.  The quotient map is
characterized on every basis path, so the construction does not silently identify `Π_l(Q)` with a
tensor product.  Such a tensor-product identification is a separate result and is not part of this
module.

The relation is preserved because the global preprojective relator is a sum of differences of
paths with coefficients `1` and `-1`. The same argument works for loops and parallel arrows,
which are retained by `Quiver.Symmetrify`.

The conventions follow the presentation and later-factor-first multiplication fixed in
`Preprojective.Basic`.

## References

See Crawley-Boevey, *Quiver algebras, weighted projective lines, and the Deligne--Simpson
problem*, Section 1.
-/

public section

namespace RingHom

open _root_.Quiver TauCeti TauCeti.PathAlgebra

universe u v w z

section

variable {k : Type w} {l : Type z} {Q : Type u}
  [CommRing k] [CommRing l] [Quiver.{v} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

/-! ### Descent through the preprojective relation -/

private noncomputable def preprojectiveBaseChangeAlgHom (f : k →+* l) :
    letI : Algebra k (preprojectiveAlgebra l Q) :=
      Algebra.compHom (preprojectiveAlgebra l Q) f
    preprojectiveAlgebra k Q →ₐ[k] preprojectiveAlgebra l Q := by
  let _ : Algebra k (preprojectiveAlgebra l Q) :=
    Algebra.compHom (preprojectiveAlgebra l Q) f
  refine preprojectiveLift (RingHom.pathAlgebraBaseChangeAlgHom f (preprojectiveMk l Q)) ?_
  rw [preprojectiveRelator_def]
  simp only [map_sum, map_sub, headBacktrackElem_def, tailBacktrackElem_def,
    RingHom.pathAlgebraBaseChangeAlgHom_ofPath]
  simpa only [preprojectiveRelator_def, headBacktrackElem_def, tailBacktrackElem_def,
    map_sum, map_sub] using preprojectiveMk_preprojectiveRelator l Q

/-! ### The public coefficient map -/

/-- The coefficient base-change map on an additive preprojective algebra.

The map leaves every doubled path unchanged and applies `f` to its coefficients.  It is exposed
as a `RingHom` because the scalar rings on the two quotient algebras differ; its semilinearity is
recorded by `RingHom.preprojectiveBaseChange_algebraMap`. -/
noncomputable def preprojectiveBaseChange (f : k →+* l) :
    preprojectiveAlgebra k Q →+* preprojectiveAlgebra l Q := by
  let _ : Algebra k (preprojectiveAlgebra l Q) :=
    Algebra.compHom (preprojectiveAlgebra l Q) f
  exact (preprojectiveBaseChangeAlgHom f).toRingHom

/-- The base-change map sends the quotient class of every path to the quotient class of the same
path over the new coefficient ring. -/
@[simp]
theorem preprojectiveBaseChange_preprojectiveMk_ofPath (f : k →+* l)
    (x : Quiver.TotalPath (Symmetrify Q)) :
    preprojectiveBaseChange f (preprojectiveMk k Q (ofPath x)) =
      preprojectiveMk l Q (ofPath x) := by
  let _ : Algebra k (preprojectiveAlgebra l Q) :=
    Algebra.compHom (preprojectiveAlgebra l Q) f
  -- The public map is the underlying ring map of the quotient lift; expose that lift here.
  change preprojectiveBaseChangeAlgHom f (preprojectiveMk k Q (ofPath x)) = _
  rw [preprojectiveBaseChangeAlgHom, preprojectiveLift_preprojectiveMk,
    RingHom.pathAlgebraBaseChangeAlgHom_ofPath]

/-- The map on preprojective algebras carries the source scalar action to the target scalar action
through the coefficient homomorphism. -/
@[simp]
theorem preprojectiveBaseChange_algebraMap (f : k →+* l) (r : k) :
    preprojectiveBaseChange f (algebraMap k (preprojectiveAlgebra k Q) r) =
      algebraMap l (preprojectiveAlgebra l Q) (f r) := by
  let _ : Algebra k (preprojectiveAlgebra l Q) :=
    Algebra.compHom (preprojectiveAlgebra l Q) f
  -- The target is a `k`-algebra via the composite coefficient map.
  change preprojectiveBaseChangeAlgHom f (algebraMap k (preprojectiveAlgebra k Q) r) =
    ((algebraMap l (preprojectiveAlgebra l Q)).comp f) r
  exact (preprojectiveBaseChangeAlgHom f).commutes r

/-- Base change along the identity coefficient homomorphism is the identity map. -/
@[simp]
theorem preprojectiveBaseChange_id :
    preprojectiveBaseChange (RingHom.id k) = RingHom.id (preprojectiveAlgebra k Q) := by
  apply ringHom_ext_of_surjective (preprojectiveMk k Q) (preprojectiveMk_surjective k Q)
  · intro r
    simp
  · intro x
    simp

/-- Base change along a composite coefficient homomorphism is the composite of the base-change
maps. -/
@[simp]
theorem preprojectiveBaseChange_comp {m : Type*} [CommRing m] (f : k →+* l) (g : l →+* m) :
    preprojectiveBaseChange (Q := Q) (g.comp f) =
      (preprojectiveBaseChange (Q := Q) g).comp (preprojectiveBaseChange (Q := Q) f) := by
  apply ringHom_ext_of_surjective (preprojectiveMk k Q) (preprojectiveMk_surjective k Q)
  · intro r
    simp
  · intro x
    simp

end

end RingHom
