/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import TauCeti.LinearAlgebra.TensorProduct.Basis

/-!
# Reconstructing a Frobenius coalgebra from its trace

A linear functional whose multiplication pairing is perfect on a finite free algebra
determines a unique Frobenius coalgebra. Its coproduct is the sum of a basis tensored with its
trace-dual basis, multiplied
by the input in the second factor. The contraction characterization makes this formula
independent of the basis and gives the counit, coassociativity and Frobenius identities.

We use Mathlib's `LinearMap.IsPerfPair` and `Coalgebra.IsFrobenius` interfaces. The algebraic
construction is the dual-basis construction of the coproduct of a Frobenius algebra.
-/

public section

open TensorProduct LinearMap

noncomputable section

namespace Module.Basis

variable {R A ι : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  [Fintype ι] (b : Basis ι R A) (ε : A →ₗ[R] R)
  (hε : ((LinearMap.mul R A).compr₂ ε).IsPerfPair)

/-- The basis dual to `b` for the trace pairing `ε (x * y)`. -/
def traceDualBasis : Basis ι R A := by
  classical
  exact b.dualBasis.map (LinearEquiv.ofBijective _ hε.bijective_left).symm

/-- Pairing a trace-dual basis vector with an element reads its coordinate in the original
basis. -/
@[simp]
theorem trace_traceDualBasis_mul (i : ι) (a : A) :
    ε (b.traceDualBasis ε hε i * a) = b.repr a i := by
  classical
  simpa only [traceDualBasis, Basis.map_apply, LinearEquiv.ofBijective_apply,
    LinearMap.compr₂_apply, LinearMap.mul_apply', Basis.dualBasis_apply] using
    congrArg (fun f : A →ₗ[R] R => f a)
    ((LinearEquiv.ofBijective _ hε.bijective_left).apply_symm_apply (b.dualBasis i))

/-- Expansion in the trace-dual basis using the original basis. -/
theorem sum_trace_mul_basis_smul (a : A) :
    ∑ i, ε (a * b i) • b.traceDualBasis ε hε i = a := by
  classical
  apply (LinearEquiv.ofBijective _ hε.bijective_left).injective
  simp only [map_sum, map_smul, traceDualBasis, Basis.map_apply,
    LinearEquiv.apply_symm_apply]
  simpa only [Basis.dualBasis_repr, LinearMap.compr₂_apply, LinearMap.mul_apply',
    LinearEquiv.ofBijective_apply] using
    b.dualBasis.sum_repr (((LinearMap.mul R A).compr₂ ε) a)

/-- The coproduct defined using a basis and its trace-dual basis. -/
def frobeniusComul : A →ₗ[R] A ⊗[R] A :=
  ∑ i, (TensorProduct.mk R A A (b i)).comp
    (LinearMap.mulLeft R (b.traceDualBasis ε hε i))

/-- The dual-basis formula for the coproduct. -/
theorem frobeniusComul_apply (a : A) :
    b.frobeniusComul ε hε a = ∑ i, b i ⊗ₜ[R] (b.traceDualBasis ε hε i * a) := by
  simp [frobeniusComul]

/-- Contracting the first leg of the coproduct with the trace pairing is multiplication. -/
@[simp]
theorem lid_pairing_frobeniusComul (x a : A) :
    TensorProduct.lid R A
      ((((LinearMap.mul R A).compr₂ ε) x).rTensor A (b.frobeniusComul ε hε a)) =
      x * a := by
  simp only [frobeniusComul_apply, map_sum, rTensor_tmul, compr₂_apply,
    mul_apply', lid_tmul, ← smul_mul_assoc, ← Finset.sum_mul,
    sum_trace_mul_basis_smul]

/-- The coproduct is independent of the basis used in its construction. -/
theorem frobeniusComul_eq {κ : Type*} [Fintype κ] (c : Basis κ R A) :
    b.frobeniusComul ε hε = c.frobeniusComul ε hε := by
  let := Module.Free.of_basis b
  ext a
  apply (TensorProduct.comm R _ _).injective
  apply TensorProduct.tensor_eq_of_forall_tensorComponent_eq
  intro φ
  obtain ⟨x, rfl⟩ := hε.bijective_left.surjective φ
  simp only [LinearMap.tensorComponent_def, LinearMap.comp_apply, LinearEquiv.coe_coe,
    lTensor_comm, rid_comm]
  simp

/-- Multiplication in the second tensor factor commutes with the coproduct. -/
theorem frobeniusComul_mul_right (x a : A) :
    (LinearMap.mulRight R x).lTensor A (b.frobeniusComul ε hε a) =
      b.frobeniusComul ε hε (a * x) := by
  simp [frobeniusComul_apply, mul_assoc]

/-- Multiplication in the first tensor factor commutes with the coproduct. -/
theorem frobeniusComul_mul_left (x a : A) :
    (LinearMap.mulLeft R x).rTensor A (b.frobeniusComul ε hε a) =
      b.frobeniusComul ε hε (x * a) := by
  let := Module.Free.of_basis b
  apply (TensorProduct.comm R _ _).injective
  apply TensorProduct.tensor_eq_of_forall_tensorComponent_eq
  intro φ
  obtain ⟨y, rfl⟩ := hε.bijective_left.surjective φ
  simp only [LinearMap.tensorComponent_def, LinearMap.comp_apply, LinearEquiv.coe_coe,
    lTensor_comm, rid_comm]
  have h (t : A ⊗[R] A) :
      TensorProduct.lid R A ((((LinearMap.mul R A).compr₂ ε) y).rTensor A
        ((LinearMap.mulLeft R x).rTensor A t)) =
      TensorProduct.lid R A ((((LinearMap.mul R A).compr₂ ε) (y * x)).rTensor A t) := by
    induction t <;> simp_all [mul_assoc]
  rw [h]
  simp [mul_assoc]

private theorem frobeniusComul_coassoc :
    (TensorProduct.assoc R A A A).toLinearMap ∘ₗ
        (b.frobeniusComul ε hε).rTensor A ∘ₗ b.frobeniusComul ε hε =
      (b.frobeniusComul ε hε).lTensor A ∘ₗ b.frobeniusComul ε hε := by
  let := Module.Free.of_basis b
  ext a
  apply (TensorProduct.comm R _ _).injective
  apply TensorProduct.tensor_eq_of_forall_tensorComponent_eq
  intro φ
  obtain ⟨x, rfl⟩ := hε.bijective_left.surjective φ
  simp only [LinearMap.tensorComponent_def, LinearMap.comp_apply, LinearEquiv.coe_coe,
    lTensor_comm, rid_comm]
  -- After contraction, the two coassociativity composites are multiplication followed by
  -- the coproduct. The first identity uses the dual-basis expansion; the second is naturality.
  let p := ((LinearMap.mul R A).compr₂ ε) x
  have hl : (TensorProduct.lid R (A ⊗[R] A)).toLinearMap ∘ₗ
      p.rTensor (A ⊗[R] A) ∘ₗ (TensorProduct.assoc R A A A).toLinearMap ∘ₗ
        (b.frobeniusComul ε hε).rTensor A = (LinearMap.mulLeft R x).rTensor A := by
    ext u v
    have hs : ∑ i, ε (x * b i) • (b.traceDualBasis ε hε i * u) = x * u := by
      simp only [← smul_mul_assoc, ← Finset.sum_mul, sum_trace_mul_basis_smul]
    simpa [p, frobeniusComul_apply, sum_tmul, smul_tmul'] using
      congrArg (fun z : A => z ⊗ₜ[R] v) hs
  have hr : (TensorProduct.lid R (A ⊗[R] A)).toLinearMap ∘ₗ
      p.rTensor (A ⊗[R] A) ∘ₗ (b.frobeniusComul ε hε).lTensor A =
      b.frobeniusComul ε hε ∘ₗ (TensorProduct.lid R A).toLinearMap ∘ₗ p.rTensor A := by
    ext u v
    simp
  exact (LinearMap.congr_fun hl (b.frobeniusComul ε hε a)).trans <|
    (b.frobeniusComul_mul_left ε hε x a).trans <|
      (by simpa only [p, LinearMap.comp_apply, LinearEquiv.coe_coe,
        lid_pairing_frobeniusComul] using
          (LinearMap.congr_fun hr (b.frobeniusComul ε hε a)).symm)

/-- The Frobenius coalgebra with counit `ε`, constructed from a trace-dual basis. This is
explicit data rather than a global instance: an algebra can carry several different traces. -/
@[instance_reducible]
def frobeniusCoalgebra : Coalgebra R A where
  comul := b.frobeniusComul ε hε
  counit := ε
  coassoc := b.frobeniusComul_coassoc ε hε
  rTensor_counit_comp_comul := by
    ext a
    apply (TensorProduct.lid R A).injective
    have he : ((LinearMap.mul R A).compr₂ ε) 1 = ε := by ext; simp
    simpa only [he, one_mul, lid_tmul, LinearMap.comp_apply,
      TensorProduct.mk_apply, one_smul] using b.lid_pairing_frobeniusComul ε hε 1 a
  lTensor_counit_comp_comul := by
    ext a
    apply (TensorProduct.rid R A).injective
    simp [frobeniusComul_apply]

/-- The reconstructed coalgebra has the specified trace as counit. -/
@[simp]
theorem frobeniusCoalgebra_counit : (b.frobeniusCoalgebra ε hε).counit = ε := (rfl)

/-- The comultiplication of the reconstructed coalgebra is its dual-basis coproduct. -/
@[simp]
theorem frobeniusCoalgebra_comul :
    (b.frobeniusCoalgebra ε hε).comul = b.frobeniusComul ε hε := (rfl)

/-- The coalgebra reconstructed from the trace satisfies the Frobenius law. -/
theorem frobeniusCoalgebra_isFrobenius :
    let := b.frobeniusCoalgebra ε hε
    Coalgebra.IsFrobenius R A := by
  let := b.frobeniusCoalgebra ε hε
  constructor
  ext x y
  have hl : (LinearMap.mulRight R y).lTensor A (b.frobeniusComul ε hε x) =
      Coalgebra.IsFrobenius.left R A (x ⊗ₜ[R] y) := by
    simp [Coalgebra.IsFrobenius.left_def, frobeniusComul_apply, sum_tmul]
  have hr : (LinearMap.mulLeft R x).rTensor A (b.frobeniusComul ε hε y) =
      Coalgebra.IsFrobenius.right R A (x ⊗ₜ[R] y) := by
    simp [Coalgebra.IsFrobenius.right_def, frobeniusComul_apply, tmul_sum]
  exact hl.symm.trans <| (b.frobeniusComul_mul_right ε hε y x).trans <|
    (b.frobeniusComul_mul_left ε hε x y).symm.trans hr

end Module.Basis

namespace Coalgebra.IsFrobenius

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  [Coalgebra R A] [Coalgebra.IsFrobenius R A]

/-- Contracting a Frobenius coproduct against its trace pairing gives multiplication. -/
@[simp]
theorem lid_pairing_comul (x a : A) :
    TensorProduct.lid R A
      ((((LinearMap.mul R A).compr₂ Coalgebra.counit) x).rTensor A
        (Coalgebra.comul a)) = x * a := by
  have h (t : A ⊗[R] A) :
      TensorProduct.lid R A (Coalgebra.counit.rTensor A
        ((LinearMap.mul' R A).rTensor A
          ((TensorProduct.assoc R A A A).symm (x ⊗ₜ[R] t)))) =
      TensorProduct.lid R A
        ((((LinearMap.mul R A).compr₂ Coalgebra.counit) x).rTensor A t) := by
    induction t <;> simp_all [tmul_add]
  have he := congrArg (fun t : A ⊗[R] A =>
    TensorProduct.lid R A (Coalgebra.counit.rTensor A t))
    (LinearMap.congr_fun (right_eq_comul_comp_mul' (R := R) (A := A)) (x ⊗ₜ[R] a))
  simpa only [right_def, LinearMap.comp_apply, lTensor_tmul, LinearEquiv.coe_coe,
    h, LinearMap.mul'_apply, Coalgebra.rTensor_counit_comul, lid_tmul, one_smul] using he

end Coalgebra.IsFrobenius

namespace Module.Basis

variable {R A ι : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  [Fintype ι] (b : Basis ι R A) (ε : A →ₗ[R] R)
  (hε : ((LinearMap.mul R A).compr₂ ε).IsPerfPair)

/-- Any Frobenius coproduct with counit `ε` is given by the trace-dual-basis formula. -/
theorem comul_eq_frobeniusComul [Coalgebra R A] [Coalgebra.IsFrobenius R A]
    (he : Coalgebra.counit (R := R) (A := A) = ε) :
    Coalgebra.comul = b.frobeniusComul ε hε := by
  let := Module.Free.of_basis b
  ext a
  apply (TensorProduct.comm R _ _).injective
  apply TensorProduct.tensor_eq_of_forall_tensorComponent_eq
  intro φ
  obtain ⟨x, rfl⟩ := hε.bijective_left.surjective φ
  simp only [LinearMap.tensorComponent_def, LinearMap.comp_apply, LinearEquiv.coe_coe,
    lTensor_comm, rid_comm]
  rw [lid_pairing_frobeniusComul, ← he, Coalgebra.IsFrobenius.lid_pairing_comul]

/-- Uniqueness of a Frobenius coalgebra with prescribed perfect trace. -/
theorem eq_frobeniusCoalgebra (c : Coalgebra R A) (he : c.counit = ε)
    (hc : @Coalgebra.IsFrobenius R A _ _ _ _ _ c.toCoalgebraStruct) :
    c = b.frobeniusCoalgebra ε hε := by
  let := c
  let := hc
  have hd := b.comul_eq_frobeniusComul ε hε he
  cases c with
  | @mk cs _ _ _ =>
    cases cs with
    | mk Δ η =>
      have he' : η = ε := he
      have hd' : Δ = b.frobeniusComul ε hε := hd
      subst η
      subst Δ
      rfl

end Module.Basis

namespace TauCeti

/-- A perfect trace on a finite free algebra determines a unique Frobenius
coalgebra with that trace as counit. -/
theorem existsUnique_frobeniusCoalgebra
    (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
    [Module.Free R A] [Module.Finite R A]
    (ε : A →ₗ[R] R) (hε : ((LinearMap.mul R A).compr₂ ε).IsPerfPair) :
    ∃! c : Coalgebra R A,
      c.counit = ε ∧ @Coalgebra.IsFrobenius R A _ _ _ _ _ c.toCoalgebraStruct := by
  let b := Module.Free.chooseBasis R A
  exact ⟨b.frobeniusCoalgebra ε hε,
    ⟨b.frobeniusCoalgebra_counit ε hε, b.frobeniusCoalgebra_isFrobenius ε hε⟩,
    fun c hc => b.eq_frobeniusCoalgebra ε hε c hc.1 hc.2⟩

end TauCeti
