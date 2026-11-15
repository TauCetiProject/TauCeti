/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.FunctorOfPoints
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.SmoothConnected
public import TauCeti.Algebra.HopfAlgebra.WeilRestriction

/-!
# The Weil restriction of the general linear group

Let `B` be a commutative `A`-algebra that is finitely generated and projective as an `A`-module.
The Weil restriction `Res_{B/A} GLₙ` of the general linear group of `B` is the affine group over
`A` with coordinate Hopf algebra `WeilRestriction A B (GeneralLinear.coordinateHopfAlgebra B n)`.
Its points over a commutative `A`-algebra `T` are the invertible `n × n` matrices over `B ⊗[A] T`
(`TauCeti.Algebra.WeilRestriction.generalLinearPoints`), naturally in `T`. The matrix attached to
a point is the matrix of values on the generic entries of the point of `GLₙ` over `B ⊗[A] T` that
it classifies. For instance, the real points of `Res_{ℂ/ℝ} GL₂` form the nonabelian group
`GL₂(ℂ ⊗[ℝ] ℝ) ≅ GL₂(ℂ)`.

## Main declarations

* `TauCeti.Algebra.WeilRestriction.generalLinearPoints`: the group isomorphism
  `(Res_{B/A} GLₙ)(T) ≃* GLₙ(B ⊗[A] T)`.
* `TauCeti.Algebra.WeilRestriction.generalLinearPoints_apply` and
  `TauCeti.Algebra.WeilRestriction.generalLinearPoints_symm_apply`: the entries of the matrix
  attached to a point are the values of the classified point of `GLₙ` on the generic entries, and
  the point attached to a matrix classifies evaluation at that matrix.
* `TauCeti.Algebra.WeilRestriction.generalLinearPoints_naturality`: the isomorphism is natural
  in `T`.

## References

* F. Bruhat, J. Tits, *Groupes réductifs sur un corps local. II*, Publ. Math. IHÉS 60 (1984),
  §1.5.
* J. S. Milne, *Algebraic Groups* (2017), §2.i.
-/

public section

open WithConv
open scoped TensorProduct

namespace TauCeti.Algebra.WeilRestriction

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]
variable (n : ℕ) (T : Type*) [CommRing T] [Algebra A T]

/-- **The points of the Weil restriction of `GLₙ` are invertible matrices.** For every commutative
`A`-algebra `T`, the points of `Res_{B/A} GLₙ` over `T` form a group isomorphic to the general
linear group `GLₙ(B ⊗[A] T)`. -/
noncomputable def generalLinearPoints :
    WithConv (WeilRestriction A B (GeneralLinear.coordinateHopfAlgebra B n) →ₐ[A] T) ≃*
      Matrix.GeneralLinearGroup (Fin n) (B ⊗[A] T) :=
  (pointsMulEquiv A B (GeneralLinear.coordinateHopfAlgebra B n) T).trans
    (GeneralLinear.pointsMulEquiv n)

variable {A B n T}

/-- The `(i, j)` entry of the matrix attached to a point of `Res_{B/A} GLₙ` is the value at the
generic entry `Xᵢⱼ` of the point of `GLₙ` over `B ⊗[A] T` that it classifies. -/
@[simp]
theorem generalLinearPoints_apply
    (f : WithConv (WeilRestriction A B (GeneralLinear.coordinateHopfAlgebra B n) →ₐ[A] T))
    (i j : Fin n) :
    generalLinearPoints A B n T f i j =
      homEquiv A B _ T f.ofConv (GeneralLinear.coordinateHopfAlgebraAlgEquiv B n
        (GeneralLinear.coordinateRingMap B n (MvPolynomial.X (i, j)))) := by
  simp [generalLinearPoints, GeneralLinear.pointToGeneralLinear_apply]

/-- The point of `Res_{B/A} GLₙ` attached to an invertible matrix `g` over `B ⊗[A] T` is the one
classifying the point of `GLₙ` given by evaluation at `g`. -/
@[simp]
theorem generalLinearPoints_symm_apply (g : Matrix.GeneralLinearGroup (Fin n) (B ⊗[A] T)) :
    ((generalLinearPoints A B n T).symm g).ofConv =
      (homEquiv A B _ T).symm (GeneralLinear.generalLinearToPoint (R := B) n g).ofConv := by
  simp [generalLinearPoints]

/-- Naturality of `WeilRestriction.generalLinearPoints` in the `A`-algebra `T`: post-composing
with `h : T →ₐ[A] T'` corresponds to applying `B ⊗[A] h` to the entries of matrices. -/
theorem generalLinearPoints_naturality {T' : Type*} [CommRing T'] [Algebra A T']
    (h : T →ₐ[A] T')
    (f : WithConv (WeilRestriction A B (GeneralLinear.coordinateHopfAlgebra B n) →ₐ[A] T)) :
    generalLinearPoints A B n T' (toConv (h.comp f.ofConv)) =
      Matrix.GeneralLinearGroup.map
        (Algebra.TensorProduct.lTensor (S := B) B h : B ⊗[A] T →+* B ⊗[A] T')
        (generalLinearPoints A B n T f) := by
  simp only [generalLinearPoints, MulEquiv.trans_apply, pointsMulEquiv_naturality,
    ← GeneralLinear.pointsMulEquiv_mapValue, AlgHom.mapValue_apply]

end TauCeti.Algebra.WeilRestriction
