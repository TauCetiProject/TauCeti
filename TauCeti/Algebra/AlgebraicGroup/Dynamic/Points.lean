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
* `BialgHom.oppositeCocharacter`: the opposite cocharacter, with its point formulas
  `TauCeti.Cocharacter.pointsHom_oppositeCocharacter` and
  `TauCeti.Cocharacter.genericPoint_oppositeCocharacter`.
* `BialgHom.powCocharacter`: the power `t ↦ λ(tⁿ)` of a cocharacter, with
  `BialgHom.powCocharacter_one`, `BialgHom.powCocharacter_powCocharacter`,
  `BialgHom.powCocharacter_neg_one` (the power `λ⁻¹` is the opposite cocharacter) and the point
  formula `BialgHom.pointsHom_powCocharacter`.
* `TauCeti.Cocharacter.mapValue_ofPolyPoint` and `TauCeti.Cocharacter.mapValue_evalZeroPoint`:
  naturality of inclusion and evaluation.
-/

public section

open WithConv

namespace BialgHom

variable {R H : Type*} [CommSemiring R] [Semiring H] [Bialgebra R H]

/-- The opposite cocharacter, obtained by precomposing the group morphism with `t ↦ t⁻¹`. -/
noncomputable def oppositeCocharacter (l : H →ₐc[R] LaurentPolynomial R) :
    H →ₐc[R] LaurentPolynomial R :=
  (AddMonoidAlgebra.domCongrBialgEquiv R R (AddEquiv.neg ℤ)).toBialgHom.comp l

/-- On coordinates the opposite cocharacter inverts the Laurent variable. -/
@[simp]
theorem oppositeCocharacter_apply (l : H →ₐc[R] LaurentPolynomial R) (h : H) :
    l.oppositeCocharacter h = LaurentPolynomial.invert (l h) := (rfl)

/-- Taking the opposite cocharacter twice recovers the original one. -/
@[simp]
theorem oppositeCocharacter_oppositeCocharacter (l : H →ₐc[R] LaurentPolynomial R) :
    l.oppositeCocharacter.oppositeCocharacter = l := by
  ext h : 1
  simpa only [oppositeCocharacter_apply] using LaurentPolynomial.involutive_invert (l h)

/-- The `n`-th power `t ↦ λ(tⁿ)` of a cocharacter `λ`: its composite with the `n`-th power
map of the multiplicative group. -/
noncomputable def powCocharacter (l : H →ₐc[R] LaurentPolynomial R) (n : ℤ) :
    H →ₐc[R] LaurentPolynomial R :=
  (AddMonoidAlgebra.mapDomainBialgHom R (AddMonoidHom.mulRight n)).comp l

/-- On coordinates the `n`-th power of a cocharacter substitutes `Tⁿ` for the Laurent
variable. -/
@[simp]
theorem powCocharacter_apply (l : H →ₐc[R] LaurentPolynomial R) (n : ℤ) (h : H) :
    l.powCocharacter n h = AddMonoidAlgebra.mapDomain (· * n) (l h) := (rfl)

/-- The first power of a cocharacter is the cocharacter itself. -/
@[simp]
theorem powCocharacter_one (l : H →ₐc[R] LaurentPolynomial R) : l.powCocharacter 1 = l := by
  ext h k : 2
  simp

/-- Powers of a cocharacter compose by multiplying the exponents: `(λᵐ)ⁿ = λ^{mn}`. -/
@[simp]
theorem powCocharacter_powCocharacter (l : H →ₐc[R] LaurentPolynomial R) (m n : ℤ) :
    (l.powCocharacter m).powCocharacter n = l.powCocharacter (m * n) := by
  ext h k : 2
  simp only [powCocharacter_apply, AddMonoidAlgebra.coeff_mapDomain, ← Finsupp.mapDomain_comp,
    Function.comp_def, mul_assoc]

/-- The power `λ⁻¹` of a cocharacter is its opposite cocharacter. -/
@[simp]
theorem powCocharacter_neg_one (l : H →ₐc[R] LaurentPolynomial R) :
    l.powCocharacter (-1) = l.oppositeCocharacter := by
  ext h k : 2
  simpa using Finsupp.mapDomain_apply_of_injective neg_injective (l h).coeff (-k)

end BialgHom

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
/-- On a rational point, the constant-point inclusion agrees with pullback along the structure
map `R → A[T;T⁻¹]`. -/
theorem constPoint_mapValue_ofId (g : WithConv (H →ₐ[R] R)) :
    constPoint A (AlgHom.mapValue (Algebra.ofId R A) g) =
      AlgHom.mapValue (Algebra.ofId R (LaurentPolynomial A)) g := by
  rw [constPoint_apply, AlgHom.mapValue_apply, AlgHom.mapValue_apply, ofConv_toConv,
    ← AlgHom.comp_assoc, Algebra.comp_ofId]

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
  (BialgHom.mapDomain l).comp
    (MultiplicativeGroup.pointsMulEquiv (R := R) (A := A)).symm.toMonoidHom

/-- A multiplicative-group morphism sends a unit to the `𝔾ₘ`-point precomposed with `l`. -/
theorem pointsHom_apply (l : H →ₐc[R] LaurentPolynomial R) (u : Aˣ) :
    pointsHom A l u = BialgHom.mapDomain l (toConv (laurentEval (R := R) u)) := by
  rw [pointsHom, MonoidHom.comp_apply]
  exact congrArg (BialgHom.mapDomain l)
    (MultiplicativeGroup.pointsMulEquiv_symm_apply (R := R) u)

/-- The opposite cocharacter evaluates at the inverse unit. -/
@[simp]
theorem pointsHom_oppositeCocharacter (l : H →ₐc[R] LaurentPolynomial R) (u : Aˣ) :
    pointsHom A l.oppositeCocharacter u = pointsHom A l u⁻¹ := by
  ext h
  simp [pointsHom_apply, BialgHom.mapDomain_apply, laurentEval_invert]

/-- The `n`-th power of a cocharacter evaluates at the `n`-th power of a unit. -/
@[simp]
theorem _root_.BialgHom.pointsHom_powCocharacter (l : H →ₐc[R] LaurentPolynomial R) (n : ℤ)
    (u : Aˣ) :
    pointsHom A (l.powCocharacter n) u = pointsHom A l (u ^ n) := by
  ext h
  rw [pointsHom_apply, pointsHom_apply, ← laurentEval_comp_mapDomainAlgHom_mulRight]
  simp only [BialgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply, BialgHom.coe_toAlgHom,
    BialgHom.powCocharacter_apply, AddMonoidAlgebra.mapDomainAlgHom_apply,
    AddMonoidHom.coe_mulRight]

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
  pointsHom (LaurentPolynomial A) l (LaurentPolynomial.genericUnit A)

/-- The generic point is the image of the generic unit `T`. -/
theorem genericPoint_eq_pointsHom (l : H →ₐc[R] LaurentPolynomial R) :
    genericPoint A l =
      pointsHom (LaurentPolynomial A) l (LaurentPolynomial.genericUnit A) := by
  rw [genericPoint]

/-- The generic cocharacter point is its coordinate map with coefficients extended to the
value algebra. -/
theorem genericPoint_ofConv (l : H →ₐc[R] LaurentPolynomial R) :
    (genericPoint A l).ofConv =
      (AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId R A)).comp l.toAlgHom := by
  have he : laurentEval (R := R) (LaurentPolynomial.genericUnit A) =
      AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId R A) := by
    apply Eq.symm
    apply laurentEval_unique
    simp [LaurentPolynomial.genericUnit_val]
  rw [genericPoint_eq_pointsHom, pointsHom_apply, BialgHom.mapDomain_apply,
    ofConv_toConv, he]

/-! ### Naturality in the value algebra -/

section Naturality

variable (φ : A →ₐ[R] B) (l : H →ₐc[R] LaurentPolynomial R)

/-- The map from multiplicative-group points is natural in the value algebra. -/
theorem mapValue_pointsHom (u : Aˣ) :
    AlgHom.mapValue φ (pointsHom A l u) = pointsHom B l (Units.map φ.toMonoidHom u) := by
  rw [pointsHom_apply, pointsHom_apply, ← MonoidHom.comp_apply,
    ← BialgHom.mapValue_mapDomain, MonoidHom.comp_apply]
  congr 1
  simp [AlgHom.mapValue_apply, comp_laurentEval]

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
  simp only [Units.coe_map, LaurentPolynomial.genericUnit_val]
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

section HopfAlgebra

variable [HopfAlgebra R H]

/-- The generic value of the opposite cocharacter is the inverse generic value. -/
@[simp]
theorem genericPoint_oppositeCocharacter (l : H →ₐc[R] LaurentPolynomial R) :
    genericPoint A l.oppositeCocharacter = (genericPoint A l)⁻¹ := by
  simp only [genericPoint_eq_pointsHom, pointsHom_oppositeCocharacter, map_inv]

end HopfAlgebra

end TauCeti.Cocharacter

namespace BialgHom

open TauCeti.Cocharacter

variable {R H K A : Type*} [CommSemiring R] [Semiring H] [Semiring K]
variable [Bialgebra R H] [Bialgebra R K] [CommSemiring A] [Algebra R A]

/-- Inclusion of polynomial-valued points commutes with a group homomorphism. -/
theorem mapDomain_ofPolyPoint (φ : H →ₐc[R] K)
    (F : WithConv (K →ₐ[R] Polynomial A)) :
    BialgHom.mapDomain φ (ofPolyPoint A F) =
      ofPolyPoint A (BialgHom.mapDomain φ F) := by
  ext h
  simp [ofPolyPoint_apply, BialgHom.mapDomain_apply]

/-- Evaluation at the origin commutes with a group homomorphism. -/
theorem mapDomain_evalZeroPoint (φ : H →ₐc[R] K)
    (F : WithConv (K →ₐ[R] Polynomial A)) :
    BialgHom.mapDomain φ (evalZeroPoint A F) =
      evalZeroPoint A (BialgHom.mapDomain φ F) := by
  ext h
  simp [evalZeroPoint_apply, BialgHom.mapDomain_apply]

end BialgHom
