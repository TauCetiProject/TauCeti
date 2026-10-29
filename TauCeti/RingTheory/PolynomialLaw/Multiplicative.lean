/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PolynomialLaw.Homogeneous
public import Mathlib.RingTheory.TensorProduct.Maps

import TauCeti.RingTheory.TensorProduct.Maps

/-!
# Multiplicative polynomial laws

For `R`-algebras `A` and `B`, associative and unital but not necessarily commutative, a
polynomial law `f : A →ₚₗ[R] B` is *multiplicative* if `f 1 = 1` and `f (x * y) = f x * f y`
for every commutative `R`-algebra `S` and all `x y : S ⊗[R] A`, where `S ⊗[R] A` and
`S ⊗[R] B` carry the ring structures of `Algebra.TensorProduct`. As for homogeneity, the
condition is imposed after every scalar extension: the determinant `Mₙ(R) → R` is the motivating
example, and `det (X * Y) = det X * det Y` is an identity of matrices with entries in every
commutative `R`-algebra, not only in `R`.

Multiplicative laws homogeneous of degree `d` are the objects classified by the Roby algebra
`Γ^d_R(A)`, with its internal multiplication. This file treats the degree-one case: a law which is
homogeneous of degree one and multiplicative is exactly the polynomial law of an `R`-algebra map
`A →ₐ[R] B`.

## Main declarations

* `PolynomialLaw.IsMultiplicative f`: the law `f` is multiplicative.
* `PolynomialLaw.IsMultiplicative.toFun_one`, `PolynomialLaw.IsMultiplicative.toFun_mul`:
  multiplicativity holds after scalar extension to algebras in every universe.
* `PolynomialLaw.IsMultiplicative.ground_one`, `PolynomialLaw.IsMultiplicative.ground_mul`: the
  ground map of a multiplicative law preserves `1` and products.
* `PolynomialLaw.isMultiplicative_id`, `PolynomialLaw.IsMultiplicative.comp`: the identity law is
  multiplicative, and multiplicative laws compose.
* `PolynomialLaw.not_isMultiplicative_zero`: the zero law to a nontrivial algebra is not
  multiplicative.
* `AlgHom.isMultiplicative_toPolynomialLaw`: the polynomial law of an algebra map is
  multiplicative.
* `PolynomialLaw.IsHomogeneousOfDegree.toAlgHom`: the ground map of a multiplicative law
  homogeneous of degree one, as an algebra map, whose polynomial law is the original law.
* `PolynomialLaw.isHomogeneousOfDegree_one_and_isMultiplicative_iff`: a law is homogeneous of
  degree one and multiplicative if and only if it is the polynomial law of an algebra map.
* `PolynomialLaw.algHomEquiv`: `A →ₐ[R] B` is identified with the multiplicative laws
  `A →ₚₗ[R] B` homogeneous of degree one.

## References

* [G. Chenevier, *The p-adic analytic space of pseudocharacters of a profinite group and
  pseudorepresentations over arbitrary rings*, §1.1](https://arxiv.org/abs/0809.0415)
-/

public section

noncomputable section

universe u

open TensorProduct

namespace PolynomialLaw

variable {R : Type u} [CommSemiring R] {A B C : Type*} [Semiring A] [Algebra R A] [Semiring B]
  [Algebra R B] [Semiring C] [Algebra R C]

/-- A polynomial law `f : A →ₚₗ[R] B` between `R`-algebras is multiplicative if `f 1 = 1` and
`f (x * y) = f x * f y` for every commutative `R`-algebra `S` and all `x y : S ⊗[R] A`. See
`IsMultiplicative.toFun_one` and `IsMultiplicative.toFun_mul` for algebras in other universes. -/
structure IsMultiplicative (f : A →ₚₗ[R] B) : Prop where
  toFun'_one (S : Type u) [CommSemiring S] [Algebra R S] : f.toFun' S 1 = 1
  toFun'_mul {S : Type u} [CommSemiring S] [Algebra R S] (x y : S ⊗[R] A) :
    f.toFun' S (x * y) = f.toFun' S x * f.toFun' S y

namespace IsMultiplicative

variable {f : A →ₚₗ[R] B}

/-- A multiplicative law sends `1` to `1` after scalar extension to a commutative `R`-algebra in an
arbitrary universe. -/
@[simp]
theorem toFun_one (hf : f.IsMultiplicative) (S : Type*) [CommSemiring S] [Algebra R S] :
    f.toFun S 1 = 1 := by
  calc f.toFun S 1 = f.toFun S ((Algebra.ofId R S).toLinearMap.rTensor A 1) := by
        rw [AlgHom.rTensor_toLinearMap_apply, map_one]
    _ = (Algebra.ofId R S).toLinearMap.rTensor B (f.toFun' R 1) := by
        rw [toFun'_eq_toFun, isCompat_apply]
    _ = 1 := by rw [hf.toFun'_one, AlgHom.rTensor_toLinearMap_apply, map_one]

/-- A multiplicative law preserves products after scalar extension to a commutative `R`-algebra
in an arbitrary universe. -/
@[simp]
theorem toFun_mul (hf : f.IsMultiplicative) {S : Type*} [CommSemiring S] [Algebra R S]
    (x y : S ⊗[R] A) : f.toFun S (x * y) = f.toFun S x * f.toFun S y := by
  -- lift `x` and `y` simultaneously to a polynomial algebra in the universe of `R`
  obtain ⟨m, ψ, p, rfl⟩ := exists_lift x
  obtain ⟨n, χ, q, rfl⟩ := exists_lift y
  let θ : MvPolynomial (Fin m ⊕ Fin n) R →ₐ[R] S :=
    MvPolynomial.aeval (Sum.elim (fun i ↦ ψ (.X i)) fun i ↦ χ (.X i))
  have hψ : θ.comp (MvPolynomial.rename Sum.inl) = ψ := by ext; simp [θ]
  have hχ : θ.comp (MvPolynomial.rename Sum.inr) = χ := by ext; simp [θ]
  have hθ (u v : MvPolynomial (Fin m ⊕ Fin n) R ⊗[R] A) :
      θ.toLinearMap.rTensor A (u * v) = θ.toLinearMap.rTensor A u * θ.toLinearMap.rTensor A v := by
    simp only [AlgHom.rTensor_toLinearMap_apply, map_mul]
  -- transport `p` and `q` along the inclusions into the polynomial algebra in `m + n` variables
  set p' := (MvPolynomial.rename Sum.inl).toLinearMap.rTensor A p
  set q' := (MvPolynomial.rename Sum.inr).toLinearMap.rTensor A q
  have hp : ψ.toLinearMap.rTensor A p = θ.toLinearMap.rTensor A p' := by
    rw [← hψ, AlgHom.comp_toLinearMap, LinearMap.rTensor_comp_apply]
  have hq : χ.toLinearMap.rTensor A q = θ.toLinearMap.rTensor A q' := by
    rw [← hχ, AlgHom.comp_toLinearMap, LinearMap.rTensor_comp_apply]
  calc f.toFun S (ψ.toLinearMap.rTensor A p * χ.toLinearMap.rTensor A q)
      = θ.toLinearMap.rTensor B (f.toFun' _ (p' * q')) := by
        rw [hp, hq, ← hθ, toFun'_eq_toFun, isCompat_apply]
    _ = θ.toLinearMap.rTensor B (f.toFun' _ p') * θ.toLinearMap.rTensor B (f.toFun' _ q') := by
        rw [hf.toFun'_mul]
        simp only [AlgHom.rTensor_toLinearMap_apply, map_mul]
    _ = f.toFun S (ψ.toLinearMap.rTensor A p) * f.toFun S (χ.toLinearMap.rTensor A q) := by
        rw [hp, hq, toFun'_eq_toFun, isCompat_apply, isCompat_apply]

/-- The ground map of a multiplicative law sends `1` to `1`. -/
@[simp]
theorem ground_one (hf : f.IsMultiplicative) : f.ground 1 = 1 := by
  simp only [ground_apply, ← Algebra.TensorProduct.one_def, hf.toFun'_one,
    ← Algebra.TensorProduct.lid_toLinearEquiv, AlgEquiv.toLinearEquiv_apply, map_one]

/-- The ground map of a multiplicative law preserves products. -/
@[simp]
theorem ground_mul (hf : f.IsMultiplicative) (a b : A) :
    f.ground (a * b) = f.ground a * f.ground b := by
  have hab : (1 : R) ⊗ₜ[R] (a * b) = (1 ⊗ₜ[R] a) * (1 ⊗ₜ[R] b) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  simp only [ground_apply, hab, hf.toFun'_mul, ← Algebra.TensorProduct.lid_toLinearEquiv,
    AlgEquiv.toLinearEquiv_apply, map_mul]

/-- Multiplicative laws compose. -/
theorem comp {g : B →ₚₗ[R] C} (hg : g.IsMultiplicative) (hf : f.IsMultiplicative) :
    (g.comp f).IsMultiplicative where
  toFun'_one S _ _ := by rw [comp_toFun', Function.comp_apply, hf.toFun'_one, hg.toFun'_one]
  toFun'_mul x y := by simp only [comp_toFun', Function.comp_apply, hf.toFun'_mul, hg.toFun'_mul]

end IsMultiplicative

/-- The identity law is multiplicative. -/
theorem isMultiplicative_id : (id : A →ₚₗ[R] A).IsMultiplicative where
  toFun'_one S _ _ := by rw [id_apply', id_eq]
  toFun'_mul x y := by simp only [id_apply', id_eq]

/-- The zero law to a nontrivial algebra is not multiplicative: it preserves products but sends
`1` to `0`. -/
theorem not_isMultiplicative_zero [Nontrivial B] : ¬ (0 : A →ₚₗ[R] B).IsMultiplicative :=
  fun h ↦ zero_ne_one (α := B) <| by
    rw [← h.ground_one, ground_apply, zero_def, Pi.zero_apply, map_zero]

end PolynomialLaw

/-- The polynomial law of an algebra map is multiplicative: after scalar extension to `S`, it is
the algebra map `Algebra.TensorProduct.map (AlgHom.id R S) φ`. -/
theorem AlgHom.isMultiplicative_toPolynomialLaw {R : Type u} [CommSemiring R] {A B : Type*}
    [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] (φ : A →ₐ[R] B) :
    φ.toLinearMap.toPolynomialLaw.IsMultiplicative := by
  have h {S : Type u} [CommSemiring S] [Algebra R S] (x : S ⊗[R] A) :
      φ.toLinearMap.toPolynomialLaw.toFun' S x = Algebra.TensorProduct.map (AlgHom.id R S) φ x := by
    rw [LinearMap.toPolynomialLaw_toFun', LinearMap.baseChange_eq_lTensor,
      AlgHom.lTensor_toLinearMap_apply]
  exact
    { toFun'_one S _ _ := by rw [h, map_one]
      toFun'_mul x y := by rw [h, h, h, map_mul] }

namespace PolynomialLaw

variable {R : Type u} [CommSemiring R] {A B : Type*} [Semiring A] [Algebra R A] [Semiring B]
  [Algebra R B]

namespace IsHomogeneousOfDegree

variable {f : A →ₚₗ[R] B}

/-- The ground map of a multiplicative polynomial law homogeneous of degree one, as an algebra
map, whose polynomial law is the original law. -/
def toAlgHom (hf : f.IsHomogeneousOfDegree 1) (hm : f.IsMultiplicative) : A →ₐ[R] B :=
  AlgHom.ofLinearMap hf.toLinearMap (by rw [coe_toLinearMap, hm.ground_one])
    fun a b ↦ by rw [coe_toLinearMap, hm.ground_mul]

@[simp]
theorem coe_toAlgHom (hf : f.IsHomogeneousOfDegree 1) (hm : f.IsMultiplicative) :
    ⇑(hf.toAlgHom hm) = f.ground := by
  funext a
  rw [toAlgHom, AlgHom.ofLinearMap_apply, coe_toLinearMap]

@[simp]
theorem toLinearMap_toAlgHom (hf : f.IsHomogeneousOfDegree 1) (hm : f.IsMultiplicative) :
    (hf.toAlgHom hm).toLinearMap = hf.toLinearMap :=
  AlgHom.toLinearMap_ofLinearMap _ _ _

/-- A multiplicative polynomial law homogeneous of degree one is the polynomial law of its ground
map. -/
theorem toPolynomialLaw_toAlgHom (hf : f.IsHomogeneousOfDegree 1) (hm : f.IsMultiplicative) :
    (hf.toAlgHom hm).toLinearMap.toPolynomialLaw = f := by
  rw [toLinearMap_toAlgHom, toPolynomialLaw_toLinearMap]

end IsHomogeneousOfDegree

/-- A polynomial law is homogeneous of degree one and multiplicative if and only if it is the
polynomial law of an algebra map, namely of its ground map `IsHomogeneousOfDegree.toAlgHom`. -/
theorem isHomogeneousOfDegree_one_and_isMultiplicative_iff {f : A →ₚₗ[R] B} :
    f.IsHomogeneousOfDegree 1 ∧ f.IsMultiplicative ↔
      ∃ φ : A →ₐ[R] B, φ.toLinearMap.toPolynomialLaw = f :=
  ⟨fun ⟨hf, hm⟩ ↦ ⟨hf.toAlgHom hm, hf.toPolynomialLaw_toAlgHom hm⟩, fun ⟨φ, hφ⟩ ↦
    hφ ▸ ⟨φ.toLinearMap.isHomogeneousOfDegree_toPolynomialLaw, φ.isMultiplicative_toPolynomialLaw⟩⟩

end PolynomialLaw

/-- The algebra map recovered from the polynomial law of an algebra map `φ` is `φ`. -/
@[simp]
theorem AlgHom.toAlgHom_isHomogeneousOfDegree_toPolynomialLaw {R : Type u} [CommSemiring R]
    {A B : Type*} [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] (φ : A →ₐ[R] B) :
    φ.toLinearMap.isHomogeneousOfDegree_toPolynomialLaw.toAlgHom
      φ.isMultiplicative_toPolynomialLaw = φ := by
  ext a
  simp

namespace PolynomialLaw

variable {R : Type u} [CommSemiring R] {A B : Type*} [Semiring A] [Algebra R A] [Semiring B]
  [Algebra R B]

variable (R A B) in
/-- Algebra maps `A →ₐ[R] B` are identified with the multiplicative polynomial laws
`A →ₚₗ[R] B` homogeneous of degree one, by `φ ↦ φ.toLinearMap.toPolynomialLaw` with inverse
`IsHomogeneousOfDegree.toAlgHom`. -/
def algHomEquiv :
    (A →ₐ[R] B) ≃ {f : A →ₚₗ[R] B // f.IsHomogeneousOfDegree 1 ∧ f.IsMultiplicative} where
  toFun φ := ⟨φ.toLinearMap.toPolynomialLaw,
    φ.toLinearMap.isHomogeneousOfDegree_toPolynomialLaw, φ.isMultiplicative_toPolynomialLaw⟩
  invFun f := f.2.1.toAlgHom f.2.2
  left_inv := AlgHom.toAlgHom_isHomogeneousOfDegree_toPolynomialLaw
  right_inv f := Subtype.ext (f.2.1.toPolynomialLaw_toAlgHom f.2.2)

@[simp]
theorem coe_algHomEquiv_apply (φ : A →ₐ[R] B) :
    (algHomEquiv R A B φ : A →ₚₗ[R] B) = φ.toLinearMap.toPolynomialLaw :=
  (rfl)

@[simp]
theorem algHomEquiv_symm_apply
    (f : {f : A →ₚₗ[R] B // f.IsHomogeneousOfDegree 1 ∧ f.IsMultiplicative}) :
    (algHomEquiv R A B).symm f = f.2.1.toAlgHom f.2.2 :=
  (rfl)

end PolynomialLaw
