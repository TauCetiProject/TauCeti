/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints
import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup

/-!
# The diagonalizable group and its character functor of points

For a commutative group `G`, the group algebra `R[G]` is a commutative Hopf algebra in which
every group element `g` is group-like (`Δ(single g 1) = single g 1 ⊗ single g 1`,
`ε(single g 1) = 1`, antipode `single g 1 ↦ single g⁻¹ 1`). The associated affine group
scheme `Spec R[G]` is the *diagonalizable group* `D(G)` of the reductive-groups roadmap.

This file records the functor-of-points calculation for `D(G)`: for every commutative
`R`-algebra `A`, the convolution group of `R`-algebra homomorphisms `R[G] →ₐ[R] A` is the
**character group** `G →* Aˣ`, with convolution corresponding to the pointwise product of
characters. A point `f` is sent to the character `g ↦ f (single g 1)` (a unit of `A` with
inverse `f (single g⁻¹ 1)`), and a character `χ` is sent to the algebra map extending it via
`MonoidAlgebra.lift`.

Specializing to `G = Multiplicative ℤ` recovers the multiplicative group `𝔾ₘ` on the
group-algebra presentation `R[Multiplicative ℤ]`: its points are `Aˣ`
(`multiplicativeGroupPointsMulEquiv`), since a character of `Multiplicative ℤ` is its value on
the generator (`zpowersMulHom`).

This is a worked-example check for the reductive-groups roadmap (Layer 4, "diagonalizable
groups and groups of multiplicative type: the anti-equivalence `M ↦ D(M) = Spec k[M]`", and
the Layer 0 target "R-points as a group"), in the same spirit as the existing multiplicative
group `𝔾ₘ`.

## Main definitions

* `TauCeti.DiagonalizableGroup.point`: the `R[G]`-point extending a character of `G`.
* `TauCeti.DiagonalizableGroup.charOfPoint`: the character of `G` read off from a point.
* `TauCeti.DiagonalizableGroup.pointEquiv`: algebra maps `R[G] →ₐ[R] A` are equivalent to
  characters `G →* Aˣ`.
* `TauCeti.DiagonalizableGroup.pointsMulEquiv`: the same equivalence as a multiplicative
  equivalence from the convolution group of points to the character group.
* `TauCeti.DiagonalizableGroup.multiplicativeGroupPointsMulEquiv`: the `G = Multiplicative ℤ`
  specialization, identifying the points of `D(Multiplicative ℤ) = 𝔾ₘ` with `Aˣ`.

## References

The Hopf algebra structure on a group algebra is Mathlib's
`Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra` (with the bialgebra structure of Amelia
Livingston's monoid-algebra formalization), and `MonoidAlgebra.lift` is its universal
property. The convolution group of points and its antipode-driven inverse are Tau Ceti's
`TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints`, built on the Mathlib convolution monoid of
Yaël Dillies, Michał Mrugała and Yunzhou Xie. This realizes the diagonalizable-group worked
example of the Tau Ceti reductive-groups roadmap (Layer 4 and Layer 0).
-/

open WithConv
open scoped TensorProduct

namespace TauCeti

universe u v w

namespace DiagonalizableGroup

variable {R : Type u} {A : Type v} {G : Type w}
variable [CommSemiring R] [CommSemiring A] [Algebra R A] [CommGroup G]

/-- The `R[G]`-point of the diagonalizable group `D(G)` corresponding to a character of `G`.
It is the algebra map extending `χ` via the universal property of the group algebra; it sends
`single g r` to `r • χ g`. -/
noncomputable def point (χ : G →* Aˣ) : MonoidAlgebra R G →ₐ[R] A :=
  MonoidAlgebra.lift R A G ((Units.coeHom A).comp χ)

/-- The point associated to a character sends `single g r` to `r • χ g`. -/
@[simp]
theorem point_single (χ : G →* Aˣ) (g : G) (r : R) :
    point (R := R) χ (MonoidAlgebra.single g r) = r • (χ g : A) := by
  rw [point, MonoidAlgebra.lift_single, MonoidHom.coe_comp, Function.comp_apply,
    Units.coeHom_apply]

/-- The point associated to a character sends the group-like `single g 1` to `χ g`. -/
@[simp]
theorem point_single_one (χ : G →* Aˣ) (g : G) :
    point (R := R) χ (MonoidAlgebra.single g 1) = (χ g : A) := by
  rw [point_single, one_smul]

/-- The character of `G` read off from an `R[G]`-point: it sends `g` to the unit
`f (single g 1)` of `A`, whose inverse is `f (single g⁻¹ 1)`. It is the monoid hom
`(MonoidAlgebra.lift R A G).symm f : G →* A` made unit-valued through `MonoidHom.toHomUnits`,
using that `G` is a group. -/
noncomputable def charOfPoint (f : MonoidAlgebra R G →ₐ[R] A) : G →* Aˣ :=
  ((MonoidAlgebra.lift R A G).symm f).toHomUnits

/-- The character read off from a point sends `g` to the value of the point on `single g 1`. -/
@[simp]
theorem charOfPoint_apply_coe (f : MonoidAlgebra R G →ₐ[R] A) (g : G) :
    (charOfPoint f g : A) = f (MonoidAlgebra.single g 1) :=
  rfl

/-- The inverse of the unit `charOfPoint f g` is the value of the point on `single g⁻¹ 1`. -/
@[simp]
theorem charOfPoint_apply_inv_coe (f : MonoidAlgebra R G →ₐ[R] A) (g : G) :
    (↑(charOfPoint f g)⁻¹ : A) = f (MonoidAlgebra.single g⁻¹ 1) :=
  (congrArg (fun u : Aˣ => (u : A)) ((charOfPoint f).map_inv g)).symm.trans
    (charOfPoint_apply_coe f g⁻¹)

/-- Reading off the character of the point of `χ` recovers `χ`. -/
@[simp]
theorem charOfPoint_point (χ : G →* Aˣ) :
    charOfPoint (point (R := R) χ) = χ := by
  ext g
  rw [charOfPoint_apply_coe, point_single_one]

/-- The point of the character read off from `f` recovers `f`. -/
@[simp]
theorem point_charOfPoint (f : MonoidAlgebra R G →ₐ[R] A) :
    point (R := R) (charOfPoint f) = f := by
  apply MonoidAlgebra.algHom_ext
  intro g
  rw [point_single_one, charOfPoint_apply_coe]

/-- Algebra maps out of `R[G]` are the same as characters `G →* Aˣ` of `G`. -/
noncomputable def pointEquiv : (MonoidAlgebra R G →ₐ[R] A) ≃ (G →* Aˣ) :=
  (MonoidAlgebra.lift R A G).symm.trans MonoidHom.toHomUnitsMulEquiv.toEquiv

/-- The equivalence sends a point to the character read off from it. -/
@[simp]
theorem pointEquiv_apply (f : MonoidAlgebra R G →ₐ[R] A) :
    pointEquiv (R := R) (A := A) (G := G) f = charOfPoint f :=
  rfl

/-- The inverse equivalence sends a character to the point extending it. -/
@[simp]
theorem pointEquiv_symm_apply (χ : G →* Aˣ) :
    (pointEquiv (R := R) (A := A) (G := G)).symm χ = point χ :=
  rfl

omit [CommGroup G] in
/-- The comultiplication of `R[G]` on a group-like element: `single g 1` is group-like. -/
private theorem comul_single_one (g : G) :
    Coalgebra.comul (R := R) (MonoidAlgebra.single g (1 : R)) =
      MonoidAlgebra.single g 1 ⊗ₜ[R] MonoidAlgebra.single g 1 := by
  rw [MonoidAlgebra.comul_single, Bialgebra.comul_one, Algebra.TensorProduct.one_def,
    TensorProduct.map_tmul, MonoidAlgebra.lsingle_apply]

/-- A convolution product of points, evaluated on the group-like `single x 1`, is the product
of the two values: convolution restricted to group-like elements is pointwise multiplication.
This is the reusable fact behind `charOfPoint_convMul`. -/
@[simp]
theorem convMul_ofConv_single_one (f g : WithConv (MonoidAlgebra R G →ₐ[R] A)) (x : G) :
    (f * g).ofConv (MonoidAlgebra.single x 1) =
      f.ofConv (MonoidAlgebra.single x 1) * g.ofConv (MonoidAlgebra.single x 1) := by
  rw [AlgHom.convMul_apply, comul_single_one, Algebra.TensorProduct.lift_tmul]

/-- Reading off characters turns the convolution product of points into the pointwise
product of characters. -/
@[simp]
theorem charOfPoint_convMul (f g : WithConv (MonoidAlgebra R G →ₐ[R] A)) :
    charOfPoint ((f * g).ofConv) = charOfPoint f.ofConv * charOfPoint g.ofConv := by
  ext x
  rw [charOfPoint_apply_coe, MonoidHom.mul_apply, Units.val_mul, charOfPoint_apply_coe,
    charOfPoint_apply_coe, convMul_ofConv_single_one]

variable {B : Type*} [CommSemiring B] [Algebra R B]

/-- Reading off characters is natural in the value algebra: post-composing a point with an
`R`-algebra map sends the associated character through the induced map on units. -/
@[simp]
theorem charOfPoint_mapValue (φ : A →ₐ[R] B)
    (f : WithConv (MonoidAlgebra R G →ₐ[R] A)) :
    charOfPoint ((AlgHom.mapValue (H := MonoidAlgebra R G) φ f).ofConv) =
      (Units.map φ.toMonoidHom).comp (charOfPoint f.ofConv) := by
  ext x
  simp

/-- The functor of points of the diagonalizable group `D(G)` is the character group `G →* Aˣ`.

The source is the convolution group of `R`-algebra maps out of `R[G]`; the target is the
group of characters of `G` valued in the units of `A`, under pointwise multiplication. -/
noncomputable def pointsMulEquiv : WithConv (MonoidAlgebra R G →ₐ[R] A) ≃* (G →* Aˣ) where
  toFun f := charOfPoint f.ofConv
  invFun χ := toConv (point (R := R) χ)
  left_inv f := congrArg toConv (point_charOfPoint f.ofConv)
  right_inv := charOfPoint_point
  map_mul' := charOfPoint_convMul

/-- The multiplicative equivalence sends a convolution point to the character read off from it. -/
@[simp]
theorem pointsMulEquiv_apply (f : WithConv (MonoidAlgebra R G →ₐ[R] A)) :
    pointsMulEquiv (R := R) (A := A) (G := G) f = charOfPoint f.ofConv :=
  rfl

/-- The multiplicative point equivalence is natural in the value algebra. -/
@[simp]
theorem pointsMulEquiv_mapValue (φ : A →ₐ[R] B)
    (f : WithConv (MonoidAlgebra R G →ₐ[R] A)) :
    pointsMulEquiv (R := R) (A := B) (G := G)
        (AlgHom.mapValue (H := MonoidAlgebra R G) φ f) =
      (Units.map φ.toMonoidHom).comp
        (pointsMulEquiv (R := R) (A := A) (G := G) f) := by
  rw [pointsMulEquiv_apply, pointsMulEquiv_apply, charOfPoint_mapValue]

/-- The inverse multiplicative equivalence sends a character to the point extending it. -/
@[simp]
theorem pointsMulEquiv_symm_apply (χ : G →* Aˣ) :
    (pointsMulEquiv (R := R) (A := A) (G := G)).symm χ = toConv (point χ) :=
  rfl

/-! ### The multiplicative group `𝔾ₘ` as `D(Multiplicative ℤ)`

Specializing to `G = Multiplicative ℤ` recovers the multiplicative group on the group-algebra
presentation `R[Multiplicative ℤ]`: a character of `Multiplicative ℤ` is determined by its value
on the generator, so the character group `Multiplicative ℤ →* Aˣ` is `Aˣ` via Mathlib's
`zpowersMulHom`. -/

/-- The points of `D(Multiplicative ℤ)` are units of `A`: composing `pointEquiv` with
`zpowersMulHom`, which identifies a character of `Multiplicative ℤ` with its value on the
generator. -/
noncomputable def multiplicativeGroupPointEquiv :
    (MonoidAlgebra R (Multiplicative ℤ) →ₐ[R] A) ≃ Aˣ :=
  pointEquiv.trans (zpowersMulHom Aˣ).symm.toEquiv

/-- The equivalence sends a point to its value on the generator `single (ofAdd 1) 1`. -/
@[simp]
theorem multiplicativeGroupPointEquiv_apply (f : MonoidAlgebra R (Multiplicative ℤ) →ₐ[R] A) :
    multiplicativeGroupPointEquiv (R := R) (A := A) f = charOfPoint f (Multiplicative.ofAdd 1) :=
  rfl

/-- The inverse equivalence sends a unit to the point of the character `n ↦ u ^ n`. -/
@[simp]
theorem multiplicativeGroupPointEquiv_symm_apply (u : Aˣ) :
    (multiplicativeGroupPointEquiv (R := R) (A := A)).symm u = point (zpowersMulHom Aˣ u) :=
  rfl

/-- The functor of points of `𝔾ₘ`, presented as `D(Multiplicative ℤ)`, is the unit group of the
value algebra: the convolution group of `R`-algebra maps out of `R[Multiplicative ℤ]` is `Aˣ`. -/
noncomputable def multiplicativeGroupPointsMulEquiv :
    WithConv (MonoidAlgebra R (Multiplicative ℤ) →ₐ[R] A) ≃* Aˣ :=
  pointsMulEquiv.trans (zpowersMulHom Aˣ).symm

/-- The multiplicative equivalence sends a convolution point to its value on the generator. -/
@[simp]
theorem multiplicativeGroupPointsMulEquiv_apply
    (f : WithConv (MonoidAlgebra R (Multiplicative ℤ) →ₐ[R] A)) :
    multiplicativeGroupPointsMulEquiv (R := R) (A := A) f =
      charOfPoint f.ofConv (Multiplicative.ofAdd 1) :=
  rfl

/-- The inverse multiplicative equivalence sends a unit to the point of the character
`n ↦ u ^ n`. -/
@[simp]
theorem multiplicativeGroupPointsMulEquiv_symm_apply (u : Aˣ) :
    (multiplicativeGroupPointsMulEquiv (R := R) (A := A)).symm u =
      toConv (point (zpowersMulHom Aˣ u)) :=
  rfl

/-- Evaluating `AddMonoidAlgebra.toMultiplicativeAlgEquiv` on the Laurent generator `T n`:
it sends `T n` to the group-like `single (ofAdd n) 1` of `R[Multiplicative ℤ]`. -/
private theorem toMultiplicativeAlgEquiv_T (n : ℤ) :
    AddMonoidAlgebra.toMultiplicativeAlgEquiv (R := R) R ℤ (LaurentPolynomial.T n) =
      MonoidAlgebra.single (Multiplicative.ofAdd n) 1 := by
  simp only [AddMonoidAlgebra.toMultiplicativeAlgEquiv, AlgEquiv.coe_mk,
    AddMonoidAlgebra.toMultiplicative, Equiv.coe_fn_mk,
    LaurentPolynomial.T, Finsupp.mapDomain_single]

/-- The `D(Multiplicative ℤ)` functor of points agrees with the Laurent-polynomial multiplicative
group `𝔾ₘ` of `TauCeti.MultiplicativeGroup`: precomposing a point with the algebra equivalence
`AddMonoidAlgebra.toMultiplicativeAlgEquiv` between `R[T;T⁻¹]` and `R[Multiplicative ℤ]` carries
`multiplicativeGroupPointsMulEquiv` to `TauCeti.MultiplicativeGroup.pointsMulEquiv`, so the two
presentations of `𝔾ₘ` give the same unit of `A`. -/
theorem multiplicativeGroupPointsMulEquiv_eq
    (f : WithConv (MonoidAlgebra R (Multiplicative ℤ) →ₐ[R] A)) :
    multiplicativeGroupPointsMulEquiv f =
      MultiplicativeGroup.pointsMulEquiv
        (toConv (f.ofConv.comp (AddMonoidAlgebra.toMultiplicativeAlgEquiv R ℤ).toAlgHom)) := by
  ext
  rw [multiplicativeGroupPointsMulEquiv_apply, MultiplicativeGroup.pointsMulEquiv_apply,
    ofConv_toConv, charOfPoint_apply_coe, MultiplicativeGroup.unitOfPoint_val, AlgHom.comp_apply]
  congr 1
  exact (toMultiplicativeAlgEquiv_T 1).symm

end DiagonalizableGroup

end TauCeti
