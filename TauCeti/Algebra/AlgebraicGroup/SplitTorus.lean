/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup
import TauCeti.Algebra.Group.FreeAbelianCharacter

/-!
# The split torus and its functor of points

The split torus on an index type `σ` is the diagonalizable group `D(M)` of the free abelian
group `M = Multiplicative (σ →₀ ℤ)`; its character lattice is `σ →₀ ℤ`, the free `ℤ`-module on
`σ`. Concretely it is `Spec R[Multiplicative (σ →₀ ℤ)]`, and for `σ = Fin n` it is the rank-`n`
split torus `𝔾ₘⁿ`.

This file computes its functor of points: for every commutative `R`-algebra `A`, the convolution
group of `R`-algebra homomorphisms `R[Multiplicative (σ →₀ ℤ)] →ₐ[R] A` is the product group
`σ → Aˣ` (with `Fin n → Aˣ = (Aˣ)ⁿ` in the finite-rank case), under pointwise multiplication.
The equivalence sends a point to its values on the standard characters `ofAdd (single i 1)`,
equivalently the basis monomials `single (ofAdd (single i 1)) 1`.

This combines two existing pieces: the diagonalizable-group points calculation
`TauCeti.DiagonalizableGroup.pointsMulEquiv`, computing the points of `D(M)` as the character
group `M →* Aˣ`, and the free-abelian-group universal property
`TauCeti.freeAbelianCharEquiv`, identifying characters of `Multiplicative (σ →₀ ℤ)` with
families `σ → Aˣ`.

This is a worked-example check for the reductive-groups roadmap
(`ReductiveGroups/README.md` in TauCetiRoadmap), Layer 4 ("Tori: split ... the character
lattice `X*(T)`") together with the Layer 0 functor-of-points calculation, in the same spirit
as the existing multiplicative group `𝔾ₘ`, roots of unity `μ_n`, and diagonalizable group
`D(G)`.

## Main definitions

* `TauCeti.SplitTorus.pointsMulEquiv`: the multiplicative equivalence from the convolution
  group of `A`-points of the rank-`σ` split torus to `σ → Aˣ`.
* `TauCeti.SplitTorus.pointsMulEquiv_apply`: a point is sent to its values on the standard
  generators `single (ofAdd (single i 1)) 1`.
* `TauCeti.SplitTorus.pointsMulEquiv_mapValue`: the points equivalence is natural in the value
  algebra.

## References

The diagonalizable-group points calculation is Tau Ceti's
`DiagonalizableGroup.pointsMulEquiv`; the free-abelian-group character identification is
`TauCeti.freeAbelianCharEquiv`, which reuses Mathlib's `Finsupp.liftAddHom` and `zmultiplesHom`.
-/

open WithConv

namespace TauCeti

namespace SplitTorus

universe u v w

variable {R : Type u} {A : Type v} {σ : Type w}
variable [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- The functor of points of the rank-`σ` split torus `D(Multiplicative (σ →₀ ℤ))`: for every
commutative `R`-algebra `A`, the convolution group of `R`-algebra maps out of
`R[Multiplicative (σ →₀ ℤ)]` is the product group `σ → Aˣ`, under pointwise multiplication. -/
noncomputable def pointsMulEquiv :
    WithConv (MonoidAlgebra R (Multiplicative (σ →₀ ℤ)) →ₐ[R] A) ≃* (σ → Aˣ) :=
  DiagonalizableGroup.pointsMulEquiv.trans freeAbelianCharEquiv

/-- The points equivalence reads off the value of a point on the `i`-th standard generator
`single (ofAdd (single i 1)) 1` of `R[Multiplicative (σ →₀ ℤ)]`. -/
@[simp]
theorem pointsMulEquiv_apply
    (f : WithConv (MonoidAlgebra R (Multiplicative (σ →₀ ℤ)) →ₐ[R] A)) (i : σ) :
    (pointsMulEquiv f i : A) =
      f.ofConv (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single i 1)) 1) := by
  rw [pointsMulEquiv, MulEquiv.trans_apply, freeAbelianCharEquiv_apply,
    DiagonalizableGroup.pointsMulEquiv_apply, DiagonalizableGroup.charOfPoint_apply_coe]

/-- The inverse points equivalence sends a family `c : σ → Aˣ` to the point extending the
character of `Multiplicative (σ →₀ ℤ)` determined by `c`. -/
theorem pointsMulEquiv_symm_apply (c : σ → Aˣ) :
    (pointsMulEquiv (R := R) (A := A)).symm c =
      toConv (DiagonalizableGroup.point (freeAbelianCharEquiv.symm c)) := by
  rw [pointsMulEquiv, MulEquiv.symm_trans_apply, DiagonalizableGroup.pointsMulEquiv_symm_apply]

/-- The inverse points equivalence sends a coordinate family to the point taking the `i`-th
standard generator to the `i`-th coordinate. -/
@[simp]
theorem pointsMulEquiv_symm_apply_single (c : σ → Aˣ) (i : σ) :
    ((pointsMulEquiv (R := R) (A := A)).symm c).ofConv
        (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single i 1)) 1) =
      (c i : A) := by
  rw [pointsMulEquiv_symm_apply, ofConv_toConv, DiagonalizableGroup.point_single_one,
    freeAbelianCharEquiv_symm_apply_ofAdd_single]

variable {B : Type*} [CommSemiring B] [Algebra R B]

/-- The split-torus points equivalence is natural in the value algebra: post-composing a point
with an `R`-algebra map `φ : A →ₐ[R] B` sends each coordinate through the induced map on
units. -/
@[simp]
theorem pointsMulEquiv_mapValue (φ : A →ₐ[R] B)
    (f : WithConv (MonoidAlgebra R (Multiplicative (σ →₀ ℤ)) →ₐ[R] A)) (i : σ) :
    pointsMulEquiv (AlgHom.mapValue (H := MonoidAlgebra R (Multiplicative (σ →₀ ℤ))) φ f) i =
      Units.map φ.toMonoidHom (pointsMulEquiv f i) := by
  simp only [pointsMulEquiv, MulEquiv.trans_apply, DiagonalizableGroup.pointsMulEquiv_mapValue,
    freeAbelianCharEquiv_comp]

/-- Naturality of the inverse split-torus points equivalence in the value algebra. -/
@[simp]
theorem mapValue_pointsMulEquiv_symm_apply (φ : A →ₐ[R] B) (c : σ → Aˣ) :
    AlgHom.mapValue (H := MonoidAlgebra R (Multiplicative (σ →₀ ℤ))) φ
        ((pointsMulEquiv (R := R) (A := A)).symm c) =
      (pointsMulEquiv (R := R) (A := B)).symm
        (fun i => Units.map φ.toMonoidHom (c i)) := by
  apply (pointsMulEquiv (R := R) (A := B)).injective
  funext i
  rw [pointsMulEquiv_mapValue]
  simp

/-- The rank-`n` split torus `𝔾ₘⁿ`: its `A`-points are `Fin n → Aˣ = (Aˣ)ⁿ`. -/
noncomputable example (n : ℕ) :
    WithConv (MonoidAlgebra R (Multiplicative (Fin n →₀ ℤ)) →ₐ[R] A) ≃* (Fin n → Aˣ) :=
  pointsMulEquiv

end SplitTorus

end TauCeti
