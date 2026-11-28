/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.TensorProduct
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Symmetric
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.MatrixCoefficient

/-!
# Bialgebra laws detected by finite comodules

A coalgebra's multiplication and unit can be supplied as coalgebra maps before their algebra
laws are known. If finite comodules have tensor objects with the usual underlying
modules, the product formula for matrix coefficients transfers the ordinary associator,
left unitor and flip to associativity, a left unit and commutativity on the coalgebra.
For a coalgebra that is projective over a commutative semiring, every element is tested using
a finite regular subcomodule and its counit; over a field, projectivity is automatic.

`FGComoduleCat.TensorPresentation` records the tensor objects and their module
identifications. `TensorPresentation.CoefficientCompatibility` asks that the three ordinary
linear equivalences lift to comodule isomorphisms and that coefficients obey the supplied
multiplication and unit formulas. No rigidity or antipode is needed.

The argument is the verification of the algebra laws in Deligne–Milne, *Tannakian categories*,
Proposition 2.16 and the proof of Theorem 2.11, before constructing the antipode.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.FGComoduleCat

universe u v

section Semiring

variable {K : Type u} [CommSemiring K] {B : Type v}
variable [AddCommMonoid B] [Module K B] [Coalgebra K B]

/-- Chosen tensor objects and unit of finite comodules, identified with the ordinary tensor
product and the base semiring. No multiplication on the coefficient coalgebra is presupposed. -/
structure TensorPresentation where
  /-- The chosen tensor object. -/
  tensor : FGComoduleCat.{u, v, v} K B → FGComoduleCat.{u, v, v} K B →
    FGComoduleCat.{u, v, v} K B
  /-- Its underlying module identification. -/
  tensorEquiv (M N) : tensor M N ≃ₗ[K] M ⊗[K] N
  /-- The chosen unit object. -/
  unit : FGComoduleCat.{u, v, v} K B
  /-- The underlying module identification of the unit. -/
  unitEquiv : unit ≃ₗ[K] K

namespace TensorPresentation

variable (T : TensorPresentation (K := K) (B := B))
variable {M N P : FGComoduleCat.{u, v, v} K B}

/-- A pure tensor, viewed in the chosen tensor object. -/
def tensorVector (m : M) (n : N) : T.tensor M N :=
  (T.tensorEquiv M N).symm (m ⊗ₜ[K] n)

/-- The underlying vector of a chosen pure tensor is the ordinary pure tensor. -/
@[simp]
theorem tensorEquiv_tensorVector (m : M) (n : N) :
    T.tensorEquiv M N (T.tensorVector m n) = m ⊗ₜ[K] n := by
  simp [tensorVector]

/-- The product of two functionals, viewed on the chosen tensor object. -/
def tensorFunctional (φ : Module.Dual K M) (ψ : Module.Dual K N) :
    Module.Dual K (T.tensor M N) :=
  (TensorProduct.dualDistrib K M N (φ ⊗ₜ[K] ψ)).comp (T.tensorEquiv M N).toLinearMap

/-- A chosen product functional is the ordinary product functional after the identification. -/
@[simp]
theorem tensorFunctional_apply (φ : Module.Dual K M) (ψ : Module.Dual K N)
    (x : T.tensor M N) :
    T.tensorFunctional φ ψ x =
      TensorProduct.dualDistrib K M N (φ ⊗ₜ[K] ψ) (T.tensorEquiv M N x) :=
  (rfl)

/-- Linear maps out of a chosen tensor object are determined on pure tensors. -/
theorem tensorVector_ext {V : Type*} [AddCommMonoid V] [Module K V]
    {f g : T.tensor M N →ₗ[K] V}
    (h : ∀ m n, f (T.tensorVector m n) = g (T.tensorVector m n)) : f = g := by
  apply (LinearMap.cancel_right (T.tensorEquiv M N).symm.surjective).mp
  ext m n
  exact h m n

/-- Compatibility of a tensor presentation with candidate coefficient multiplication and unit.
The algebra laws are conclusions, rather than fields: the coherence hypotheses concern only
comodule isomorphisms with the ordinary underlying associator, left unitor and flip. -/
structure CoefficientCompatibility (μ : B ⊗[K] B →ₗ[K] B) (e : B) : Prop where
  /-- Pure tensor coefficients are multiplied by `μ`. -/
  tensor_coefficient (M N : FGComoduleCat.{u, v, v} K B)
      (φ : Module.Dual K M) (ψ : Module.Dual K N) (m : M) (n : N) :
    Comodule.matrixCoefficient (C := B) (T.tensorFunctional φ ψ) (T.tensorVector m n) =
      μ (Comodule.matrixCoefficient (C := B) φ m ⊗ₜ[K]
        Comodule.matrixCoefficient (C := B) ψ n)
  /-- The coefficient of the unit vector against the unit coordinate is `e`. -/
  unit_coefficient :
    Comodule.matrixCoefficient (C := B) T.unitEquiv.toLinearMap (T.unitEquiv.symm 1) = e
  /-- The ordinary associator is a comodule isomorphism. -/
  associator (M N P : FGComoduleCat.{u, v, v} K B) :
    ∃ f : T.tensor (T.tensor M N) P ≅ T.tensor M (T.tensor N P),
    ∀ (m : M) (n : N) (p : P),
      f.hom.hom.toLinearMap (T.tensorVector (T.tensorVector m n) p) =
        T.tensorVector m (T.tensorVector n p)
  /-- The ordinary left unitor is a comodule isomorphism. -/
  leftUnitor (M : FGComoduleCat.{u, v, v} K B) : ∃ f : T.tensor T.unit M ≅ M,
    ∀ (r : K) (m : M), f.hom.hom.toLinearMap (T.tensorVector (T.unitEquiv.symm r) m) = r • m
  /-- The ordinary flip is a comodule isomorphism. -/
  commutor (M N : FGComoduleCat.{u, v, v} K B) : ∃ f : T.tensor M N ≅ T.tensor N M,
    ∀ (m : M) (n : N), f.hom.hom.toLinearMap (T.tensorVector m n) = T.tensorVector n m

variable {T} {μ : B ⊗[K] B →ₗ[K] B} {e : B}
variable (h : T.CoefficientCompatibility μ e)

include h

private theorem coefficient_assoc (M N P : FGComoduleCat.{u, v, v} K B)
    (φ : Module.Dual K M) (ψ : Module.Dual K N) (χ : Module.Dual K P)
    (m : M) (n : N) (p : P) :
    μ (μ (Comodule.matrixCoefficient (C := B) φ m ⊗ₜ[K]
      Comodule.matrixCoefficient (C := B) ψ n) ⊗ₜ[K]
        Comodule.matrixCoefficient (C := B) χ p) =
    μ (Comodule.matrixCoefficient (C := B) φ m ⊗ₜ[K]
      μ (Comodule.matrixCoefficient (C := B) ψ n ⊗ₜ[K]
        Comodule.matrixCoefficient (C := B) χ p)) := by
  obtain ⟨f, hf⟩ := h.associator M N P
  have hφ : (T.tensorFunctional φ (T.tensorFunctional ψ χ)).comp f.hom.hom.toLinearMap =
      T.tensorFunctional (T.tensorFunctional φ ψ) χ := by
    apply (LinearMap.cancel_right (T.tensorEquiv _ _).symm.surjective).mp
    apply (LinearMap.cancel_right
      (TensorProduct.congr (T.tensorEquiv M N).symm (LinearEquiv.refl K P)).surjective).mp
    ext m n p
    simpa [tensorVector] using
      (by rw [hf]; simp [mul_assoc] :
        T.tensorFunctional φ (T.tensorFunctional ψ χ)
          (f.hom.hom.toLinearMap (T.tensorVector (T.tensorVector m n) p)) =
        T.tensorFunctional (T.tensorFunctional φ ψ) χ
          (T.tensorVector (T.tensorVector m n) p))
  have hc := Comodule.matrixCoefficient_map f.hom.hom
    (T.tensorFunctional φ (T.tensorFunctional ψ χ))
    (T.tensorVector (T.tensorVector m n) p)
  rw [hφ, ← Comodule.Hom.coe_toLinearMap, hf] at hc
  simpa only [h.tensor_coefficient] using hc.symm

private theorem coefficient_comm (M N : FGComoduleCat.{u, v, v} K B)
    (φ : Module.Dual K M) (ψ : Module.Dual K N) (m : M) (n : N) :
    μ (Comodule.matrixCoefficient (C := B) φ m ⊗ₜ[K]
      Comodule.matrixCoefficient (C := B) ψ n) =
    μ (Comodule.matrixCoefficient (C := B) ψ n ⊗ₜ[K]
      Comodule.matrixCoefficient (C := B) φ m) := by
  obtain ⟨f, hf⟩ := h.commutor M N
  have hφ : (T.tensorFunctional ψ φ).comp f.hom.hom.toLinearMap =
      T.tensorFunctional φ ψ := by
    apply T.tensorVector_ext
    intro m n
    rw [LinearMap.comp_apply, hf]
    simp [mul_comm]
  have hc := Comodule.matrixCoefficient_map f.hom.hom (T.tensorFunctional ψ φ)
    (T.tensorVector m n)
  rw [hφ, ← Comodule.Hom.coe_toLinearMap, hf] at hc
  simpa only [h.tensor_coefficient] using hc.symm

private theorem coefficient_one_mul (M : FGComoduleCat.{u, v, v} K B)
    (φ : Module.Dual K M) (m : M) :
    μ (e ⊗ₜ[K] Comodule.matrixCoefficient (C := B) φ m) =
      Comodule.matrixCoefficient (C := B) φ m := by
  obtain ⟨f, hf⟩ := h.leftUnitor M
  have hφ : φ.comp f.hom.hom.toLinearMap = T.tensorFunctional T.unitEquiv.toLinearMap φ := by
    apply T.tensorVector_ext
    intro x m
    obtain ⟨r, rfl⟩ := T.unitEquiv.symm.surjective x
    rw [LinearMap.comp_apply, hf]
    simp
  have hc := Comodule.matrixCoefficient_map f.hom.hom φ
    (T.tensorVector (T.unitEquiv.symm 1) m)
  rw [hφ, ← Comodule.Hom.coe_toLinearMap, hf] at hc
  simpa only [one_smul, h.tensor_coefficient, h.unit_coefficient] using hc.symm

end TensorPresentation

end Semiring

section Projective

variable {K : Type u} [CommSemiring K] {B : Type v}
variable [AddCommMonoid B] [Module K B] [Coalgebra K B] [Module.Projective K B]

namespace TensorPresentation.CoefficientCompatibility

variable {T : TensorPresentation (K := K) (B := B)}
variable {μ : B ⊗[K] B →ₗ[K] B} {e : B} (h : T.CoefficientCompatibility μ e)

include h

/-- The candidate multiplication is associative. -/
theorem mul_assoc (a b c : B) :
    μ (μ (a ⊗ₜ[K] b) ⊗ₜ[K] c) = μ (a ⊗ₜ[K] μ (b ⊗ₜ[K] c)) := by
  obtain ⟨M, φ, m, rfl⟩ := exists_matrixCoefficient_eq (K := K) a
  obtain ⟨N, ψ, n, rfl⟩ := exists_matrixCoefficient_eq (K := K) b
  obtain ⟨P, χ, p, rfl⟩ := exists_matrixCoefficient_eq (K := K) c
  exact TensorPresentation.coefficient_assoc h M N P φ ψ χ m n p

/-- The candidate multiplication is commutative. -/
theorem mul_comm (a b : B) : μ (a ⊗ₜ[K] b) = μ (b ⊗ₜ[K] a) := by
  obtain ⟨M, φ, m, rfl⟩ := exists_matrixCoefficient_eq (K := K) a
  obtain ⟨N, ψ, n, rfl⟩ := exists_matrixCoefficient_eq (K := K) b
  exact TensorPresentation.coefficient_comm h M N φ ψ m n

/-- The coefficient of the chosen unit is a left unit. -/
theorem one_mul (a : B) : μ (e ⊗ₜ[K] a) = a := by
  obtain ⟨M, φ, m, rfl⟩ := exists_matrixCoefficient_eq (K := K) a
  exact TensorPresentation.coefficient_one_mul h M φ m

/-- The right unit law follows from the left unit law and commutativity. -/
theorem mul_one (a : B) : μ (a ⊗ₜ[K] e) = a := by
  rw [h.mul_comm, h.one_mul]

end TensorPresentation.CoefficientCompatibility

end Projective

section Semiring

variable {K : Type u} [CommSemiring K] {B : Type v}
variable [AddCommMonoid B] [Module K B] [cB : Coalgebra K B] [Module.Projective K B]

namespace TensorPresentation.CoefficientCompatibility

variable {T : TensorPresentation (K := K) (B := B)}
variable {μ : B ⊗[K] B →ₗ[K] B} {e : B} (h : T.CoefficientCompatibility μ e)

/-- The commutative semiring with multiplication `μ` and unit `e`, retaining the original additive
monoid. The scalar algebra is constructed separately so its module is the original one too.
The body is exposed to identify its additive operations with those of the input module. -/
@[instance_reducible, expose]
noncomputable def commSemiring : CommSemiring B where
  __ := (inferInstance : AddCommMonoid B)
  mul a b := μ (a ⊗ₜ[K] b)
  one := e
  -- Restate the new multiplication fields in terms of the supplied linear map.
  left_distrib a b c := by
    change μ (a ⊗ₜ[K] (b + c)) = μ (a ⊗ₜ[K] b) + μ (a ⊗ₜ[K] c)
    simp [TensorProduct.tmul_add]
  right_distrib a b c := by
    change μ ((a + b) ⊗ₜ[K] c) = μ (a ⊗ₜ[K] c) + μ (b ⊗ₜ[K] c)
    simp [TensorProduct.add_tmul]
  zero_mul a := by
    change μ (0 ⊗ₜ[K] a) = 0
    simp
  mul_zero a := by
    change μ (a ⊗ₜ[K] 0) = 0
    simp
  mul_assoc := h.mul_assoc
  one_mul := h.one_mul
  mul_one := h.mul_one
  mul_comm := h.mul_comm

/-- Multiplication in the constructed semiring is the supplied map on pure tensors. -/
@[simp]
theorem commSemiring_mul (a b : B) : letI := h.commSemiring; a * b = μ (a ⊗ₜ[K] b) :=
  (rfl)

/-- The constructed semiring has the supplied unit. -/
@[simp]
theorem commSemiring_one : letI := h.commSemiring; (1 : B) = e :=
  (rfl)

/-- The scalar algebra of the constructed semiring, with the original scalar action.
The body is exposed to identify its module with the input module and hence retain its coalgebra. -/
@[instance_reducible, expose]
noncomputable def algebra : letI := h.commSemiring; Algebra K B := by
  letI := h.commSemiring
  exact Algebra.ofModule
    (fun r a b ↦ by
      -- Reduce multiplication in the selected semiring, keeping the original scalar action.
      change μ ((r • a) ⊗ₜ[K] b) = r • μ (a ⊗ₜ[K] b)
      simp [← TensorProduct.smul_tmul'])
    (fun r a b ↦ by
      change μ (a ⊗ₜ[K] (r • b)) = r • μ (a ⊗ₜ[K] b)
      simp [TensorProduct.tmul_smul])

end TensorPresentation.CoefficientCompatibility

namespace TensorPresentation.CoefficientCompatibility

variable {T : TensorPresentation (K := K) (B := B)}
variable {μ : B ⊗[K] B →ₗc[K] B} {η : K →ₗc[K] B}
variable (h : T.CoefficientCompatibility μ.toLinearMap (η 1))

/-- A coherent coefficient tensor with coalgebra multiplication and unit defines a commutative
bialgebra. Install `h.commSemiring` and then `h.bialgebra`; its coalgebra and scalar action are the
original ones, and its multiplication and unit are characterized by `commSemiring_mul` and
`commSemiring_one`. Its body is exposed to identify the parent module and coalgebra
with the input. -/
@[instance_reducible, expose]
noncomputable def bialgebra : letI := h.commSemiring; Bialgebra K B := by
  letI := h.commSemiring
  letI := h.algebra
  have hcomul : ∀ a b : B, Coalgebra.comul (R := K) (a * b) =
      Coalgebra.comul (R := K) a * Coalgebra.comul (R := K) b := by
    intro a b
    have hμ : (μ : B ⊗[K] B →ₗ[K] B) = LinearMap.mul' K B := by
      apply TensorProduct.ext'
      intro x y
      exact (commSemiring_mul h x y).symm
    simp only [commSemiring_mul h, CoalgHom.toLinearMap_eq_ofClass, CoalgHom.coe_linearMapOfClass]
    rw [← CoalgHomClass.map_comp_comul_apply μ]
    rw [TensorProduct.comul_tmul, TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_eq]
    simp only [hμ]
    simpa only [LinearMap.comp_apply, LinearMap.mul'_apply, LinearEquiv.coe_coe] using
      (LinearMap.congr_fun (LinearMap.mul'_tensor (R := K) (A := B) (B := B))
        (Coalgebra.comul (R := K) a ⊗ₜ[K] Coalgebra.comul (R := K) b)).symm
  refine Bialgebra.mk' K B ?_ ?_ ?_ (hcomul _ _)
  · simpa only [commSemiring_one h, CommSemiring.counit_apply] using
      CoalgHomClass.counit_comp_apply η 1
  · intro a b
    simpa only [commSemiring_mul h, CoalgHom.toLinearMap_eq_ofClass,
      CoalgHom.coe_linearMapOfClass, TensorProduct.counit_tmul,
      smul_eq_mul, _root_.mul_comm] using
      CoalgHomClass.counit_comp_apply μ (a ⊗ₜ[K] b)
  · rw [commSemiring_one h, ← CoalgHomClass.map_comp_comul_apply η]
    simp only [CommSemiring.comul_apply, TensorProduct.map_tmul,
      Algebra.TensorProduct.one_def, commSemiring_one h]
    rfl

/-- The bialgebra construction retains the input coalgebra. -/
@[simp]
theorem bialgebra_toCoalgebra :
    letI := h.commSemiring
    letI := h.algebra
    (h.bialgebra).toCoalgebra = cB :=
  (rfl)

/-- The algebra map of the constructed bialgebra is the supplied coalgebra unit map. -/
@[simp]
theorem bialgebra_algebraMap (r : K) :
    letI := h.commSemiring
    letI := h.bialgebra
    algebraMap K B r = η r := by
  let _ := h.commSemiring
  let _ := h.bialgebra
  rw [Algebra.algebraMap_eq_smul_one, commSemiring_one h]
  simpa using (map_smul η r (1 : K)).symm

end TensorPresentation.CoefficientCompatibility

end Semiring

section Ring

variable {K : Type u} [CommSemiring K] {B : Type v}
variable [AddCommGroup B] [Module K B] [Coalgebra K B] [Module.Projective K B]

namespace TensorPresentation.CoefficientCompatibility

variable {T : TensorPresentation (K := K) (B := B)}
variable {μ : B ⊗[K] B →ₗ[K] B} {e : B} (h : T.CoefficientCompatibility μ e)

/-- The commutative ring obtained from the constructed semiring when the original additive
monoid is a group. Its exposed body retains the original additive group and the multiplication
and unit of `commSemiring`. -/
@[instance_reducible, expose]
noncomputable def commRing : CommRing B where
  __ := h.commSemiring
  __ := (inferInstance : AddCommGroup B)

end TensorPresentation.CoefficientCompatibility

end Ring

section Scalar

variable {K : Type u} [Field K]

attribute [local instance] Comodule.tensor

-- On the base field, use the existing diagonal tensor and trivial unit.
private noncomputable def scalarTensorPresentation : TensorPresentation (K := K) (B := K) where
  tensor := tensor K K
  tensorEquiv M N := LinearEquiv.refl K (M ⊗[K] N)
  unit := tensorUnit K K
  unitEquiv := LinearEquiv.refl K K

private theorem scalarTensorPresentation_compatible :
    (scalarTensorPresentation (K := K)).CoefficientCompatibility
      (Bialgebra.mulCoalgHom K K).toLinearMap ((CoalgHom.id K K) 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro M N φ ψ m n
    -- The chosen identifications are identities; expose the diagonal tensor coefficient.
    change Comodule.matrixCoefficient (C := K)
      (TensorProduct.dualDistrib K M N (φ ⊗ₜ[K] ψ)) (m ⊗ₜ[K] n) = _
    exact Comodule.matrixCoefficient_tensor φ ψ m n
  · -- The chosen unit is the existing trivial comodule on the field.
    let : Comodule K K K := Comodule.trivial (R := K) (C := K) (M := K)
    change Comodule.matrixCoefficient (C := K) (LinearMap.id : K →ₗ[K] K) 1 = 1
    simp
  · intro M N P
    refine ⟨tensorAssociator K K M N P, ?_⟩
    intro m n p
    -- Rewrite the named comodule associator through its underlying linear map.
    rw [tensorAssociator_eq, associator_hom_toLinearMap]
    rfl
  · intro M
    refine ⟨tensorLeftUnitor K K M, ?_⟩
    intro r m
    -- The presentation has identity vector-space identifications.
    rw [tensorLeftUnitor_eq, leftUnitor_hom_toLinearMap]
    rfl
  · intro M N
    refine ⟨tensorBraiding K K M N, ?_⟩
    intro m n
    -- Both evaluations are the same flip, viewed through the categorical wrapper.
    exact braiding_hom_apply m n

-- The resulting multiplication and unit are the usual ones on the scalar field.
example (a b : K) :
    let h := scalarTensorPresentation_compatible (K := K)
    h.commRing.mul a b = a * b ∧ h.commRing.one = (1 : K) := by
  constructor <;> rfl

-- The full bialgebra constructor applies and retains the usual coalgebra on the field.
-- Bind it before installing the new ring, so the base ring remains the original field.
example :
    let h := scalarTensorPresentation_compatible (K := K)
    let b := h.bialgebra
    letI := h.commRing
    b.toCoalgebra = CommSemiring.toCoalgebra K := by
  exact TensorPresentation.CoefficientCompatibility.bialgebra_toCoalgebra _

end Scalar

end TauCeti.FGComoduleCat
