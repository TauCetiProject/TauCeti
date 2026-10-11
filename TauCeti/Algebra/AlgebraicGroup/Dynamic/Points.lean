/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Hopf.Map
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Basic
public import TauCeti.Algebra.Polynomial.Laurent.Basic

/-!
# Polynomial and Laurent-valued points of a bialgebra

For an `R`-bialgebra `H`, write `M(A) = WithConv (H →ₐ[R] A)` for its convolution-points
monoid over a commutative `R`-algebra `A`. If `H` is commutative, this is the functor of points
of the affine monoid scheme `M = Spec H`.

The structure maps of the affine line and the punctured affine line induce constant-point
inclusions, the injective map `M(A[X]) → M(A[T;T⁻¹])`, and evaluation at the origin. These maps
are natural in `A`. A bialgebra morphism `l : H →ₐc[R] R[T;T⁻¹]` also induces the map
`Aˣ → M(A)` on multiplicative-group points and its generic value `l(T)`.

These constructions use no antipode. For a commutative Hopf algebra `H`, `M` is an affine
group scheme and `l` is a cocharacter. The polynomial and Laurent point maps then provide the
extension and evaluation operations used to define dynamic parabolic subgroups and their limits.

## Main declarations

* `TauCeti.Cocharacter.constPoint` and `TauCeti.Cocharacter.constPolyPoint`: constant points.
* `TauCeti.Cocharacter.ofPolyPoint`: inclusion of polynomial-valued points into Laurent-valued
  points, with injectivity given by `TauCeti.Cocharacter.ofPolyPoint_injective`.
* `TauCeti.Cocharacter.evalZeroPoint`: evaluation of polynomial-valued points at the origin.
* `TauCeti.Cocharacter.pointsHom` and `TauCeti.Cocharacter.genericPoint`: the map from
  multiplicative-group points and its generic value.
* `TauCeti.Cocharacter.mapValue_ofPolyPoint` and `TauCeti.Cocharacter.mapValue_evalZeroPoint`:
  naturality of inclusion and evaluation.
-/

public section

open WithConv

namespace TauCeti.Cocharacter

variable {R H A B : Type*} [CommSemiring R] [Semiring H]
variable [CommSemiring A] [Algebra R A] [CommSemiring B] [Algebra R B]

section Bialgebra

variable [_root_.Bialgebra R H]

/-! ### Points over the line and the punctured line -/

variable (A) in
/-- The constant-point inclusion `M(A) → M(A[T;T⁻¹])`, pullback of points along the structure
map `A → A[T;T⁻¹]`. -/
noncomputable def constPoint :
    WithConv (H →ₐ[R] A) →* WithConv (H →ₐ[R] LaurentPolynomial A) :=
  AlgHom.mapValue (IsScalarTower.toAlgHom R A (LaurentPolynomial A))

variable (A) in
/-- The constant-point inclusion `M(A) → M(A[X])`, pullback of points along `A → A[X]`. -/
noncomputable def constPolyPoint :
    WithConv (H →ₐ[R] A) →* WithConv (H →ₐ[R] Polynomial A) :=
  AlgHom.mapValue (IsScalarTower.toAlgHom R A (Polynomial A))

variable (A) in
/-- The inclusion `M(A[X]) → M(A[T;T⁻¹])` of points over the affine line into points over the
punctured affine line, pullback along `Polynomial.toLaurent`. -/
noncomputable def ofPolyPoint :
    WithConv (H →ₐ[R] Polynomial A) →* WithConv (H →ₐ[R] LaurentPolynomial A) :=
  AlgHom.mapValue (Polynomial.toLaurentAlg.restrictScalars R)

variable (A) in
/-- Evaluation at the origin, `M(A[X]) → M(A)`. -/
noncomputable def evalZeroPoint :
    WithConv (H →ₐ[R] Polynomial A) →* WithConv (H →ₐ[R] A) :=
  AlgHom.mapValue ((Polynomial.aeval (0 : A)).restrictScalars R)

variable (A) in
/-- The constant-point inclusion post-composes a point with the structure map `A → A[T;T⁻¹]`. -/
theorem constPoint_apply (g : WithConv (H →ₐ[R] A)) :
    constPoint A g = toConv ((IsScalarTower.toAlgHom R A (LaurentPolynomial A)).comp g.ofConv) := by
  rw [constPoint, AlgHom.mapValue_apply]

variable (A) in
/-- The constant-point inclusion post-composes a point with the structure map `A → A[X]`. -/
theorem constPolyPoint_apply (g : WithConv (H →ₐ[R] A)) :
    constPolyPoint A g = toConv ((IsScalarTower.toAlgHom R A (Polynomial A)).comp g.ofConv) := by
  rw [constPolyPoint, AlgHom.mapValue_apply]

variable (A) in
/-- The inclusion of points over the affine line post-composes with `Polynomial.toLaurent`. -/
theorem ofPolyPoint_apply (F : WithConv (H →ₐ[R] Polynomial A)) :
    ofPolyPoint A F = toConv ((Polynomial.toLaurentAlg.restrictScalars R).comp F.ofConv) := by
  rw [ofPolyPoint, AlgHom.mapValue_apply]

variable (A) in
/-- Evaluation at the origin post-composes a point over `A[X]` with `X ↦ 0`. -/
theorem evalZeroPoint_apply (F : WithConv (H →ₐ[R] Polynomial A)) :
    evalZeroPoint A F = toConv (((Polynomial.aeval (0 : A)).restrictScalars R).comp F.ofConv) := by
  rw [evalZeroPoint, AlgHom.mapValue_apply]

variable (A) in
/-- A point over `A[X]` is determined by the point over `A[T;T⁻¹]` that it induces. -/
theorem ofPolyPoint_injective :
    Function.Injective (ofPolyPoint (R := R) (H := H) A) :=
  AlgHom.mapValue_injective Polynomial.toLaurent_injective

variable (A) in
/-- A constant point over `A[X]` induces the constant point over `A[T;T⁻¹]`. -/
@[simp]
theorem ofPolyPoint_constPolyPoint (g : WithConv (H →ₐ[R] A)) :
    ofPolyPoint A (constPolyPoint A g) = constPoint A g := by
  ext h
  simp [ofPolyPoint_apply, constPolyPoint_apply, constPoint_apply]

variable (A) in
/-- A constant point over `A[X]` evaluates at the origin to the point it came from. -/
@[simp]
theorem evalZeroPoint_constPolyPoint (g : WithConv (H →ₐ[R] A)) :
    evalZeroPoint A (constPolyPoint A g) = g := by
  ext h
  simp [evalZeroPoint_apply, constPolyPoint_apply]

/-! ### Multiplicative-group morphisms on points -/

variable (A) in
/-- The map `𝔾ₘ(A) = Aˣ → M(A)` induced by a multiplicative-group morphism into the
convolution-points monoid, presented contravariantly as a bialgebra homomorphism
`H →ₐc[R] R[T;T⁻¹]`. For commutative `H`, this is the map on points of the monoid-scheme
morphism `𝔾ₘ → Spec H`. -/
noncomputable def pointsHom (l : H →ₐc[R] LaurentPolynomial R) :
    Aˣ →* WithConv (H →ₐ[R] A) :=
  (AlgHom.mapDomain l).comp
    (MultiplicativeGroup.pointsMulEquiv (R := R) (A := A)).symm.toMonoidHom

/-- A multiplicative-group morphism sends a unit to the `𝔾ₘ`-point precomposed with `l`. -/
theorem pointsHom_apply (l : H →ₐc[R] LaurentPolynomial R) (u : Aˣ) :
    pointsHom A l u = AlgHom.mapDomain l (toConv (MultiplicativeGroup.point (R := R) u)) := by
  rw [pointsHom, MonoidHom.comp_apply]
  congr 1

/-- Images of multiplicative-group points commute: they lie in the image of the commutative
group `𝔾ₘ(A)`. -/
theorem pointsHom_commute (l : H →ₐc[R] LaurentPolynomial R) (u v : Aˣ) :
    Commute (pointsHom A l u) (pointsHom A l v) :=
  (Commute.all u v).map (pointsHom A l)

variable (A) in
/-- The point `l(T)` with values in `A[T;T⁻¹]`, obtained by evaluating the multiplicative-group
morphism `l` at the tautological unit `T`. For commutative `H`, it is a point of the affine
monoid scheme `Spec H`. -/
noncomputable def genericPoint (l : H →ₐc[R] LaurentPolynomial R) :
    WithConv (H →ₐ[R] LaurentPolynomial A) :=
  pointsHom (LaurentPolynomial A) l (MultiplicativeGroup.genericUnit A)

/-- The generic point is the image of the generic unit `T`. -/
theorem genericPoint_eq_pointsHom (l : H →ₐc[R] LaurentPolynomial R) :
    genericPoint A l =
      pointsHom (LaurentPolynomial A) l (MultiplicativeGroup.genericUnit A) := by
  rw [genericPoint]

/-! ### Naturality in the value algebra -/

section Naturality

variable (φ : A →ₐ[R] B) (l : H →ₐc[R] LaurentPolynomial R)

/-- The map from multiplicative-group points is natural in the value algebra. -/
theorem mapValue_pointsHom (u : Aˣ) :
    AlgHom.mapValue φ (pointsHom A l u) = pointsHom B l (Units.map φ.toMonoidHom u) := by
  rw [pointsHom_apply, pointsHom_apply, ← MonoidHom.comp_apply,
    ← AlgHom.mapValue_mapDomain, MonoidHom.comp_apply]
  congr 1
  rw [AlgHom.mapValue_apply, MultiplicativeGroup.comp_point]

/-- The constant-point inclusion is natural in the value algebra. -/
theorem mapValue_constPoint (g : WithConv (H →ₐ[R] A)) :
    AlgHom.mapValue (AddMonoidAlgebra.mapAlgHom ℤ φ) (constPoint A g) =
      constPoint B (AlgHom.mapValue φ g) := by
  ext h
  simp [constPoint_apply]

/-- The image of the generic multiplicative-group point is natural in the value algebra. -/
theorem mapValue_genericPoint :
    AlgHom.mapValue (AddMonoidAlgebra.mapAlgHom ℤ φ) (genericPoint A l) = genericPoint B l := by
  rw [genericPoint, genericPoint, mapValue_pointsHom]
  congr 1
  apply Units.ext
  simp only [Units.coe_map, MultiplicativeGroup.genericUnit_val]
  exact LaurentPolynomial.mapAlgHom_T φ 1

/-- The inclusion of points over the affine line is natural in the value algebra. -/
theorem mapValue_ofPolyPoint (F : WithConv (H →ₐ[R] Polynomial A)) :
    AlgHom.mapValue (AddMonoidAlgebra.mapAlgHom ℤ φ) (ofPolyPoint A F) =
      ofPolyPoint B (AlgHom.mapValue (Polynomial.mapAlgHom φ) F) := by
  ext h : 2
  simp [ofPolyPoint_apply]
  induction F.ofConv h using Polynomial.induction_on' <;> simp_all

/-- Evaluation at the origin is natural in the value algebra. -/
theorem mapValue_evalZeroPoint (F : WithConv (H →ₐ[R] Polynomial A)) :
    AlgHom.mapValue φ (evalZeroPoint A F) =
      evalZeroPoint B (AlgHom.mapValue (Polynomial.mapAlgHom φ) F) := by
  ext h
  simp [evalZeroPoint_apply]

end Naturality

end Bialgebra

end TauCeti.Cocharacter
