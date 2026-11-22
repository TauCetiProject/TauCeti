/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.SchemePoints
public import TauCeti.Algebra.AlgebraicGroup.WittGroup.Basic
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.HopfSpec

/-!
# The Witt vector group scheme `W_n`

Fix a prime `p` and a length `n`. For a commutative ring `R`, the group scheme `W_n` of Witt
vectors of length `n` over `Spec R` is the relative spectrum of the coordinate Hopf algebra
`TauCeti.WittGroup.coordinateHopfAlgebra p n R`, the polynomial ring `R[X₀, …, X_{n-1}]` with the
comultiplication of Witt vector addition. It is an affine commutative group scheme, locally of
finite presentation over the base, whose underlying scheme is affine `n`-space.

Its scheme-valued points are the truncated Witt vectors: for a commutative `R`-algebra `A`,
morphisms `Spec A ⟶ W_n` over `Spec R` form a group isomorphic to the additive group of
`TruncatedWittVector p n A`, naturally in `A`. This composes Mathlib's spectrum-points
equivalence with the description of algebra-valued points,
`TauCeti.WittGroup.pointsMulEquiv`.

Over a perfect field of characteristic `p` these are the groups `W_n` from which the finite Witt
group schemes `W_n^m = ker(F^m : W_n → W_n)` are cut out, and they compute the Dieudonné module
of a unipotent finite commutative group scheme as `colim_n Hom(G, W_n)`.

## Main declarations

* `TauCeti.WittGroup.groupScheme`: the group scheme `W_n` over `Spec R`.
* `TauCeti.WittGroup.isAffine_groupScheme`,
  `TauCeti.WittGroup.locallyOfFinitePresentation_groupScheme`: it is affine and locally of finite
  presentation; it is commutative by the instance `TauCeti.WittGroup.isCommMonObj_groupScheme`.
* `TauCeti.WittGroup.schemePointsMulEquiv`: its `Spec A`-valued points are the truncated Witt
  vectors `W_n(A)`, naturally in `A` (`TauCeti.WittGroup.schemePointsMulEquiv_mapValue`).

## References

* R. Pink, *Finite group schemes*, lecture course WS 2004/05, ETH Zürich lecture notes, §22,
  <https://people.math.ethz.ch/~pink/ftp/FGS/CompleteNotes.pdf>.
* M. Demazure, *Lectures on p-divisible groups*, Lecture Notes in Mathematics 302, Springer,
  1972, Chapter III, §1.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace TauCeti

namespace WittGroup

universe u

variable (p : ℕ) [Fact p.Prime] (n : ℕ) (R : Type u) [CommRing R]

/-- The group scheme `W_n` of Witt vectors of length `n` over `Spec R`: the relative spectrum of
the coordinate Hopf algebra of Witt vector addition. -/
def groupScheme : Grp (Over (Spec (CommRingCat.of R))) :=
  (hopfSpec (CommRingCat.of R)).obj (Opposite.op (coordinateHopfAlgebra p n R))

/-- The Witt vector group scheme is the relative spectrum of its coordinate Hopf algebra. -/
lemma groupScheme_def :
    groupScheme p n R =
      (hopfSpec (CommRingCat.of R)).obj (Opposite.op (coordinateHopfAlgebra p n R)) :=
  (rfl)

/-- The scheme underlying the Witt vector group scheme is the spectrum of its coordinate
algebra. -/
@[simp]
lemma groupScheme_X_left :
    (groupScheme p n R).X.left = Spec (CommRingCat.of (coordinateHopfAlgebra p n R)) := by
  rw [groupScheme_def]
  exact hopfSpec_obj_X_left R (coordinateHopfAlgebra p n R)

/-- The Witt vector group scheme is affine. -/
instance isAffine_groupScheme : IsAffine (groupScheme p n R).X.left := by
  rw [groupScheme_X_left]
  exact isAffine_Spec _

/-- The Witt vector group scheme is commutative. -/
instance isCommMonObj_groupScheme : IsCommMonObj (groupScheme p n R).X := by
  rw [groupScheme_def]
  infer_instance

/-- The Witt vector group scheme is locally of finite presentation over the base. -/
instance locallyOfFinitePresentation_groupScheme :
    LocallyOfFinitePresentation (groupScheme p n R).X.hom := by
  rw [groupScheme_def]
  exact (algebraFinitePresentation_iff_locallyOfFinitePresentation_hopfSpec R
    (coordinateHopfAlgebra p n R)).mp inferInstance

section SchemePoints

variable {p n R} (A : Type u) [CommRing A] [Algebra R A]

/-- Mathlib's spectrum-points equivalence, with its target presented as the underlying object of
the Witt vector group scheme. It sends an algebra point to its contravariant spectrum morphism. -/
def groupSchemePointMulEquiv :
    WithConv (coordinateHopfAlgebra p n R →ₐ[R] A) ≃*
      ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶ (groupScheme p n R).X) :=
  CommHopfAlgCat.mapMulEquivOfPresentation (coordinateHopfAlgebra p n R) A (groupScheme_def p n R)

/-- **The points of the Witt vector group scheme.** Morphisms `Spec A ⟶ W_n` over `Spec R` form
a group isomorphic to the additive group of truncated Witt vectors `W_n(A)`, written
multiplicatively to match the group law on a hom-set into a group object. -/
def schemePointsMulEquiv :
    ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶ (groupScheme p n R).X) ≃*
      Multiplicative (TruncatedWittVector p n A) :=
  (groupSchemePointMulEquiv A).symm.trans pointsMulEquiv

/-- Evaluating the scheme-points equivalence on a point presented by `groupSchemePointMulEquiv`
gives the Witt vector of the underlying algebra point. -/
@[simp]
theorem schemePointsMulEquiv_groupSchemePointMulEquiv
    (q : WithConv (coordinateHopfAlgebra p n R →ₐ[R] A)) :
    schemePointsMulEquiv A (groupSchemePointMulEquiv A q) = pointsMulEquiv q := by
  simp [schemePointsMulEquiv]

/-- The inverse scheme-points equivalence sends a Witt vector to the spectrum map of the
corresponding algebra point. -/
theorem schemePointsMulEquiv_symm_apply (x : Multiplicative (TruncatedWittVector p n A)) :
    (schemePointsMulEquiv A).symm x =
      groupSchemePointMulEquiv A ((pointsMulEquiv (R := R)).symm x) :=
  (rfl)

variable {A} {B : Type u} [CommRing B] [Algebra R B]

/-- The identification of scheme-valued points of `W_n` with truncated Witt vectors is natural in
the value algebra: precomposing a point with the spectrum map of `φ : A →ₐ[R] B` changes the
coefficients of its Witt vector along `φ`. -/
theorem schemePointsMulEquiv_mapValue (φ : A →ₐ[R] B)
    (x : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶ (groupScheme p n R).X) :
    schemePointsMulEquiv B
        ((Spec.map (CommRingCat.ofHom φ.toRingHom)).asOver (Spec (CommRingCat.of R)) ≫ x) =
      Multiplicative.ofAdd
        (TruncatedWittVector.map n φ.toRingHom (schemePointsMulEquiv A x).toAdd) :=
  CommHopfAlgCat.mapMulEquivOfPresentation_symm_trans_mapValue
    (coordinateHopfAlgebra p n R) φ (groupScheme_def p n R) pointsMulEquiv pointsMulEquiv
    (fun y : Multiplicative (TruncatedWittVector p n A) ↦
      Multiplicative.ofAdd (TruncatedWittVector.map n φ.toRingHom y.toAdd))
    (pointsMulEquiv_mapValue φ) x

end SchemePoints

end WittGroup

end TauCeti
