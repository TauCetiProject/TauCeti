/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Prod
public import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints

/-!
# Convolution points valued in binary and indexed products of coefficient algebras

For a `k`-bialgebra `H`, taking `k`-algebra homomorphisms into a binary product `R₁ × R₂` or an
indexed product `∀ i, R i` of commutative `k`-algebras identifies the convolution monoid
`WithConv (H →ₐ[k] R₁ × R₂)` (resp. `WithConv (H →ₐ[k] ∀ i, R i)`) with the product of the factor
convolution monoids, together with canonical factor inclusions `inlPoints` and `inrPoints`. When
`H` is a Hopf algebra, these monoid isomorphisms are group isomorphisms.

These algebraic splittings separate coordinatewise product decompositions of functors of points from
their affine point-topology upgrades in `TauCeti.Topology.Algebra.PointTopology.Prod`, which are
used to split adelic points `G(𝔸_F) = G(F_∞ × 𝔸_{F,f})` into archimedean and finite-adelic factors
and `G(F_∞)` into local archimedean factors.

## Main declarations

* `TauCeti.AlgHom.prodPointsMulEquiv`: convolution monoid isomorphism
  `WithConv (H →ₐ[k] R₁ × R₂) ≃* WithConv (H →ₐ[k] R₁) × WithConv (H →ₐ[k] R₂)`.
* `TauCeti.AlgHom.inlPoints`, `TauCeti.AlgHom.inrPoints`: factor monoid homomorphisms `x ↦ (x, 1)`
  and `y ↦ (1, y)` into `WithConv (H →ₐ[k] R₁ × R₂)`.
* `TauCeti.AlgHom.piPointsMulEquiv`: convolution monoid isomorphism
  `WithConv (H →ₐ[k] ∀ i, R i) ≃* ∀ i, WithConv (H →ₐ[k] R i)`.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Graduate Texts in Mathematics 66,
  Springer-Verlag, 1979, §1.4.
-/

public section

open WithConv

namespace TauCeti.AlgHom

section BialgebraProd

variable (k H R₁ R₂ : Type*) [CommSemiring k] [Semiring H] [Bialgebra k H]
  [CommSemiring R₁] [Algebra k R₁] [CommSemiring R₂] [Algebra k R₂]

/-- Convolution points of a bialgebra valued in `R₁ × R₂` split as the product of the convolution
monoids valued in `R₁` and `R₂`. -/
noncomputable def prodPointsMulEquiv :
    WithConv (H →ₐ[k] R₁ × R₂) ≃* WithConv (H →ₐ[k] R₁) × WithConv (H →ₐ[k] R₂) where
  toFun f := (AlgHom.mapValue (AlgHom.fst k R₁ R₂) f, AlgHom.mapValue (AlgHom.snd k R₁ R₂) f)
  invFun p := toConv (p.1.ofConv.prod p.2.ofConv)
  left_inv f := ofConv_injective <| AlgHom.ext fun h ↦ by simp
  right_inv p := Prod.ext
    (ofConv_injective <| AlgHom.ext fun h ↦ by simp)
    (ofConv_injective <| AlgHom.ext fun h ↦ by simp)
  map_mul' f g := Prod.ext (map_mul _ f g) (map_mul _ f g)

/-- The first component of `prodPointsMulEquiv` is post-composition with `AlgHom.fst`. -/
@[simp]
theorem prodPointsMulEquiv_fst (f : WithConv (H →ₐ[k] R₁ × R₂)) :
    (prodPointsMulEquiv k H R₁ R₂ f).1 = AlgHom.mapValue (AlgHom.fst k R₁ R₂) f := by
  simp [prodPointsMulEquiv]

/-- The second component of `prodPointsMulEquiv` is post-composition with `AlgHom.snd`. -/
@[simp]
theorem prodPointsMulEquiv_snd (f : WithConv (H →ₐ[k] R₁ × R₂)) :
    (prodPointsMulEquiv k H R₁ R₂ f).2 = AlgHom.mapValue (AlgHom.snd k R₁ R₂) f := by
  simp [prodPointsMulEquiv]

/-- The inverse of `prodPointsMulEquiv` pairs two points coordinatewise. -/
@[simp]
theorem prodPointsMulEquiv_symm_ofConv_apply
    (p : WithConv (H →ₐ[k] R₁) × WithConv (H →ₐ[k] R₂)) (h : H) :
    ((prodPointsMulEquiv k H R₁ R₂).symm p).ofConv h = (p.1.ofConv h, p.2.ofConv h) := by
  simp [prodPointsMulEquiv]

/-- Embedding the first factor `x ↦ (x, 1)` into convolution points valued in `R₁ × R₂`. -/
noncomputable def inlPoints :
    WithConv (H →ₐ[k] R₁) →* WithConv (H →ₐ[k] R₁ × R₂) :=
  (prodPointsMulEquiv k H R₁ R₂).symm.toMonoidHom.comp (MonoidHom.inl _ _)

/-- Embedding the second factor `y ↦ (1, y)` into convolution points valued in `R₁ × R₂`. -/
noncomputable def inrPoints :
    WithConv (H →ₐ[k] R₂) →* WithConv (H →ₐ[k] R₁ × R₂) :=
  (prodPointsMulEquiv k H R₁ R₂).symm.toMonoidHom.comp (MonoidHom.inr _ _)

@[simp]
theorem inlPoints_apply (x : WithConv (H →ₐ[k] R₁)) :
    inlPoints k H R₁ R₂ x = (prodPointsMulEquiv k H R₁ R₂).symm (x, 1) := by
  simp [inlPoints]

@[simp]
theorem inrPoints_apply (y : WithConv (H →ₐ[k] R₂)) :
    inrPoints k H R₁ R₂ y = (prodPointsMulEquiv k H R₁ R₂).symm (1, y) := by
  simp [inrPoints]

theorem mapValue_fst_inlPoints (x : WithConv (H →ₐ[k] R₁)) :
    AlgHom.mapValue (AlgHom.fst k R₁ R₂) (inlPoints k H R₁ R₂ x) = x := by
  rw [inlPoints_apply, ← prodPointsMulEquiv_fst, MulEquiv.apply_symm_apply]

theorem mapValue_snd_inlPoints (x : WithConv (H →ₐ[k] R₁)) :
    AlgHom.mapValue (AlgHom.snd k R₁ R₂) (inlPoints k H R₁ R₂ x) = 1 := by
  rw [inlPoints_apply, ← prodPointsMulEquiv_snd, MulEquiv.apply_symm_apply]

theorem mapValue_fst_inrPoints (y : WithConv (H →ₐ[k] R₂)) :
    AlgHom.mapValue (AlgHom.fst k R₁ R₂) (inrPoints k H R₁ R₂ y) = 1 := by
  rw [inrPoints_apply, ← prodPointsMulEquiv_fst, MulEquiv.apply_symm_apply]

theorem mapValue_snd_inrPoints (y : WithConv (H →ₐ[k] R₂)) :
    AlgHom.mapValue (AlgHom.snd k R₁ R₂) (inrPoints k H R₁ R₂ y) = y := by
  rw [inrPoints_apply, ← prodPointsMulEquiv_snd, MulEquiv.apply_symm_apply]

/-- Any pair of factor points decomposes in `WithConv (H →ₐ[k] R₁ × R₂)` as the convolution product
of its `inlPoints` and `inrPoints` images. -/
theorem inlPoints_mul_inrPoints (x : WithConv (H →ₐ[k] R₁)) (y : WithConv (H →ₐ[k] R₂)) :
    inlPoints k H R₁ R₂ x * inrPoints k H R₁ R₂ y =
      (prodPointsMulEquiv k H R₁ R₂).symm (x, y) := by
  simp [← map_mul]

end BialgebraProd

section BialgebraPi

variable (k H : Type*) {ι : Type*} (R : ι → Type*) [CommSemiring k] [Semiring H] [Bialgebra k H]
  [∀ i, CommSemiring (R i)] [∀ i, Algebra k (R i)]

/-- Convolution points of a bialgebra valued in an indexed product `∀ i, R i` split as the
indexed product of the factor convolution monoids. -/
noncomputable def piPointsMulEquiv :
    WithConv (H →ₐ[k] ∀ i, R i) ≃* ∀ i, WithConv (H →ₐ[k] R i) where
  toFun f i := AlgHom.mapValue (Pi.evalAlgHom k R i) f
  invFun f := toConv (AlgHom.pi fun i ↦ (f i).ofConv)
  left_inv _ := ofConv_injective <| AlgHom.ext fun _ ↦ funext fun _ ↦ by simp
  right_inv _ := funext fun _ ↦ ofConv_injective <| AlgHom.ext fun _ ↦ by simp
  map_mul' f g := funext fun i ↦ map_mul _ f g

/-- Evaluating `piPointsMulEquiv` at `i` is post-composition with `Pi.evalAlgHom k R i`. -/
@[simp]
theorem piPointsMulEquiv_apply (f : WithConv (H →ₐ[k] ∀ i, R i)) (i : ι) :
    piPointsMulEquiv k H R f i = AlgHom.mapValue (Pi.evalAlgHom k R i) f := by
  simp [piPointsMulEquiv]

/-- The inverse of `piPointsMulEquiv` assembles a family of points coordinatewise. -/
@[simp]
theorem piPointsMulEquiv_symm_ofConv_apply
    (f : ∀ i, WithConv (H →ₐ[k] R i)) (h : H) (i : ι) :
    ((piPointsMulEquiv k H R).symm f).ofConv h i = (f i).ofConv h := by
  simp [piPointsMulEquiv]

end BialgebraPi

end TauCeti.AlgHom
