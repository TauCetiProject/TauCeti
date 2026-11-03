/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Basic
public import TauCeti.Algebra.HopfAlgebra.WeilRestriction
public import TauCeti.Algebra.Polynomial.Laurent.Smooth
public import TauCeti.RingTheory.WeilRestriction.Smooth

/-!
# The Weil restriction of the multiplicative group

Let `B` be a commutative `A`-algebra that is finitely generated and projective as an `A`-module.
The Weil restriction `Res_{B/A} 𝔾ₘ` of the multiplicative group of `B` is the affine group over
`A` with coordinate Hopf algebra `WeilRestriction A B B[T;T⁻¹]`. Its points over a commutative
`A`-algebra `T` are the units of `B ⊗[A] T`
(`TauCeti.Algebra.WeilRestriction.multiplicativeGroupPoints`), naturally in `T`. The unit
attached to a point is the value at `T` of the point of `𝔾ₘ` over `B ⊗[A] T` that it classifies.

The group `Res_{B/A} 𝔾ₘ` is commutative, and it is smooth over `A`: the corresponding instances
`TauCeti.Algebra.WeilRestriction.instIsCocomm` and `TauCeti.Algebra.WeilRestriction.instSmooth`
apply because `B[T;T⁻¹]` is cocommutative and smooth over `B`
(`LaurentPolynomial.instSmooth`).

For a nontrivial finite purely inseparable field extension `K/k`, the group `Res_{K/k} 𝔾ₘ` is
the standard example of a commutative pseudo-reductive group which is not reductive; neither of
these two properties is proved in this file.

## Main declarations

* `TauCeti.Algebra.WeilRestriction.multiplicativeGroupPoints`: the group isomorphism
  `(Res_{B/A} 𝔾ₘ)(T) ≃* (B ⊗[A] T)ˣ`.
* `TauCeti.Algebra.WeilRestriction.multiplicativeGroupPoints_apply` and
  `TauCeti.Algebra.WeilRestriction.multiplicativeGroupPoints_symm_apply`: the unit attached to a
  point is the value of the classified point of `𝔾ₘ` at the coordinate `T`, and the point attached
  to a unit classifies evaluation at that unit.
* `TauCeti.Algebra.WeilRestriction.multiplicativeGroupPoints_naturality`: the isomorphism is
  natural in `T`.

## References

* F. Bruhat, J. Tits, *Groupes réductifs sur un corps local. II*, Publ. Math. IHÉS 60 (1984),
  §1.5.
* J. S. Milne, *Algebraic Groups* (2017), §2.i.
* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, 2nd ed. (2015), §1.1.
-/

public section

open WithConv
open scoped LaurentPolynomial TensorProduct

namespace TauCeti.Algebra.WeilRestriction

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]
variable (T : Type*) [CommRing T] [Algebra A T]

/-- **The points of the Weil restriction of `𝔾ₘ` are units.** For every commutative `A`-algebra
`T`, the points of `Res_{B/A} 𝔾ₘ` over `T` form a group isomorphic to the unit group of
`B ⊗[A] T`. -/
noncomputable def multiplicativeGroupPoints :
    WithConv (WeilRestriction A B B[T;T⁻¹] →ₐ[A] T) ≃* (B ⊗[A] T)ˣ :=
  (pointsMulEquiv A B B[T;T⁻¹] T).trans MultiplicativeGroup.pointsMulEquiv

variable {A B T}

/-- The unit attached to a point of `Res_{B/A} 𝔾ₘ` is the value at the coordinate `T` of the
point of `𝔾ₘ` over `B ⊗[A] T` that it classifies. -/
@[simp]
theorem multiplicativeGroupPoints_apply (f : WithConv (WeilRestriction A B B[T;T⁻¹] →ₐ[A] T)) :
    (multiplicativeGroupPoints A B T f : B ⊗[A] T) =
      homEquiv A B B[T;T⁻¹] T f.ofConv (LaurentPolynomial.T 1) := by
  simp [multiplicativeGroupPoints]

/-- The point of `Res_{B/A} 𝔾ₘ` attached to a unit `u` of `B ⊗[A] T` is the one classifying
evaluation of Laurent polynomials at `u`. -/
@[simp]
theorem multiplicativeGroupPoints_symm_apply (u : (B ⊗[A] T)ˣ) :
    ((multiplicativeGroupPoints A B T).symm u).ofConv =
      (homEquiv A B B[T;T⁻¹] T).symm (laurentEval u) := by
  simp [multiplicativeGroupPoints]

/-- Naturality of `WeilRestriction.multiplicativeGroupPoints` in the `A`-algebra `T`:
post-composing with `h : T →ₐ[A] T'` corresponds to applying `B ⊗[A] h` to units. -/
theorem multiplicativeGroupPoints_naturality {T' : Type*} [CommRing T'] [Algebra A T']
    (h : T →ₐ[A] T') (f : WithConv (WeilRestriction A B B[T;T⁻¹] →ₐ[A] T)) :
    multiplicativeGroupPoints A B T' (toConv (h.comp f.ofConv)) =
      Units.map (Algebra.TensorProduct.lTensor (S := B) B h : B ⊗[A] T →* B ⊗[A] T')
        (multiplicativeGroupPoints A B T f) := by
  simp only [multiplicativeGroupPoints, MulEquiv.trans_apply, pointsMulEquiv_naturality,
    ← MultiplicativeGroup.pointsMulEquiv_mapValue, AlgHom.mapValue_apply]

end TauCeti.Algebra.WeilRestriction
