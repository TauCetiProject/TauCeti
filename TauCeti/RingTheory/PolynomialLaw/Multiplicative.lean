/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PolynomialLaw.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Multiplicative polynomial laws

A polynomial law between associative unital algebras is multiplicative when it preserves
one and products after every commutative scalar extension. The algebras themselves need not
be commutative. This condition does not require the law to be additive or homogeneous.

`TauCeti.PolynomialLaw.IsMultiplicative` tests the components in the universe of the base, as in
Mathlib's `PolynomialLaw`. Its `map_one` and `map_mul` lemmas extend this condition to
`PolynomialLaw.toFun` in arbitrary universes. Thus `toMonoidHom` gives a multiplicative
evaluation on every scalar extension, and `groundMonoidHom` gives the ground evaluation.
The identity law is multiplicative, and multiplicative laws compose.

The definition follows Chenevier, *The p-adic analytic space of pseudocharacters of a
profinite group and pseudorepresentations over arbitrary rings*, §1.1, p. 8. We use
Mathlib's polynomial laws and their extension to arbitrary universes, formalized by
Antoine Chambert-Loir and María Inés de Frutos-Fernández.
-/

public section

noncomputable section

namespace TauCeti

open scoped TensorProduct

variable {R : Type u} [CommSemiring R]
variable {A B C : Type*} [Semiring A] [Algebra R A]
  [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

namespace PolynomialLaw

/-- Naturality of evaluation along the algebra tensor map of a scalar algebra morphism. -/
theorem toFun_rTensor_algHom (f : A →ₚₗ[R] B)
    {S T : Type*} [CommSemiring S] [Algebra R S] [CommSemiring T] [Algebra R T]
    (φ : S →ₐ[R] T) (x : S ⊗[R] A) :
    f.toFun T (Algebra.TensorProduct.rTensor A φ x) =
      Algebra.TensorProduct.rTensor B φ (f.toFun S x) := by
  simpa only [← AlgHom.toLinearMap_apply, Algebra.TensorProduct.toLinearMap_map,
    TensorProduct.AlgebraTensorModule.map_eq, AlgHom.toLinearMap_id,
    ← LinearMap.rTensor_def] using (f.isCompat_apply φ x).symm

/-- A polynomial law is multiplicative if all its scalar extensions preserve one and products.
The source and target algebras may be noncommutative. -/
structure IsMultiplicative (f : A →ₚₗ[R] B) : Prop where
  /-- Every component preserves the unit. -/
  map_one' (S : Type u) [CommSemiring S] [Algebra R S] : f.toFun' S 1 = 1
  /-- Every component preserves products. -/
  map_mul' (S : Type u) [CommSemiring S] [Algebra R S] (x y : S ⊗[R] A) :
    f.toFun' S (x * y) = f.toFun' S x * f.toFun' S y

namespace IsMultiplicative

variable {f : A →ₚₗ[R] B} (hf : IsMultiplicative f)

include hf

/-- Multiplicative laws preserve one over scalar algebras in any universe. -/
@[simp]
theorem map_one (S : Type*) [CommSemiring S] [Algebra R S] : f.toFun S 1 = 1 := by
  have h := toFun_rTensor_algHom f (Algebra.ofId R S) (1 : R ⊗[R] A)
  simpa only [← PolynomialLaw.toFun'_eq_toFun, hf.map_one', _root_.map_one] using h

/-- Multiplicative laws preserve products over scalar algebras in any universe. -/
@[simp]
theorem map_mul (S : Type*) [CommSemiring S] [Algebra R S] (x y : S ⊗[R] A) :
    f.toFun S (x * y) = f.toFun S x * f.toFun S y := by
  -- Lift both arguments to one finitely generated scalar algebra in the base universe.
  obtain ⟨U, hU, hx⟩ := TensorProduct.Algebra.exists_of_fg x
  obtain ⟨V, hV, hy⟩ := TensorProduct.Algebra.exists_of_fg y
  obtain ⟨s, hs⟩ := PolynomialLaw.exists_range_φ_eq_of_fg (hU.sup hV)
  obtain ⟨p, rfl⟩ := PolynomialLaw.exists_lift_of_mem_range_rTensor U
    (φ := PolynomialLaw.φ R s) (hs.symm ▸ le_sup_left) hx
  obtain ⟨q, rfl⟩ := PolynomialLaw.exists_lift_of_mem_range_rTensor V
    (φ := PolynomialLaw.φ R s) (hs.symm ▸ le_sup_right) hy
  simp only [LinearMap.rTensor_def, ← TensorProduct.AlgebraTensorModule.map_eq,
    ← AlgHom.toLinearMap_id, ← Algebra.TensorProduct.toLinearMap_map, AlgHom.toLinearMap_apply,
    ← _root_.map_mul (Algebra.TensorProduct.rTensor A (PolynomialLaw.φ R s)),
    toFun_rTensor_algHom, ← PolynomialLaw.toFun'_eq_toFun, hf.map_mul',
    _root_.map_mul (Algebra.TensorProduct.rTensor B (PolynomialLaw.φ R s))]

/-- The component of a multiplicative law, bundled as a monoid homomorphism. -/
def toMonoidHom (S : Type*) [CommSemiring S] [Algebra R S] :
    (S ⊗[R] A) →* (S ⊗[R] B) where
  toFun := f.toFun S
  map_one' := hf.map_one S
  map_mul' := hf.map_mul S

@[simp]
theorem toMonoidHom_apply (S : Type*) [CommSemiring S] [Algebra R S] (x : S ⊗[R] A) :
    hf.toMonoidHom S x = f.toFun S x := (rfl)

/-- The ground evaluation of a multiplicative polynomial law is multiplicative. -/
def groundMonoidHom : A →* B :=
  (Algebra.TensorProduct.lid R B).toMonoidHom.comp
    ((hf.toMonoidHom R).comp (Algebra.TensorProduct.lid R A).symm.toMonoidHom)

@[simp]
theorem groundMonoidHom_apply (a : A) : hf.groundMonoidHom a = f.ground a := by
  suffices h : (Algebra.TensorProduct.lid R B) (f.toFun' R (1 ⊗ₜ[R] a)) =
      (TensorProduct.lid R B) (f.toFun' R (1 ⊗ₜ[R] a)) by
    simpa [groundMonoidHom, PolynomialLaw.ground_apply, ← PolynomialLaw.toFun'_eq_toFun] using h
  exact congrArg (fun e : R ⊗[R] B ≃ₗ[R] B ↦ e (f.toFun' R (1 ⊗ₜ[R] a)))
    (Algebra.TensorProduct.lid_toLinearEquiv R B)

/-- Multiplicative polynomial laws are closed under composition. -/
theorem comp {g : C →ₚₗ[R] A} (hg : IsMultiplicative g) :
    IsMultiplicative (f.comp g) where
  map_one' S := by
    intros
    simp [hf.map_one, hg.map_one]
  map_mul' S := by
    intros
    simp [hf.map_mul, hg.map_mul]

end IsMultiplicative

/-- The identity polynomial law is multiplicative, including for noncommutative algebras. -/
theorem IsMultiplicative.id :
    IsMultiplicative (PolynomialLaw.id : A →ₚₗ[R] A) where
  map_one' S := by intros; simp only [PolynomialLaw.id_apply', id_eq]
  map_mul' S := by intros; simp only [PolynomialLaw.id_apply', id_eq]

/-- The zero law is not multiplicative when the target algebra is nontrivial: the unit
condition cannot be dropped. -/
theorem not_isMultiplicative_zero [Nontrivial B] :
    ¬ IsMultiplicative (0 : A →ₚₗ[R] B) := by
  intro h
  have h1 := congrArg (TensorProduct.lid R B) (h.map_one' R)
  simp [Algebra.TensorProduct.one_def] at h1

end PolynomialLaw

end TauCeti
