/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import TauCeti.Algebra.Coalgebra.Basic
import TauCeti.Algebra.HopfAlgebra.FiniteDual.Basic

/-!
# Reconstructing a Frobenius coalgebra from a perfect trace

A perfect trace pairing on a finite projective commutative algebra determines a
unique Frobenius coalgebra with the given counit. The coproduct is the transpose
of multiplication under the trace pairing. In a finite basis it is the familiar
sum of basis vectors tensored with their trace-duals times the input.

We reuse the transposed coalgebra on `TauCeti.ConvolutionDual`, Mathlib's perfect
pairings, and `CoalgEquiv.toCoalgebra` to obtain the coalgebra laws. No field or
characteristic hypothesis is needed.

The trace presentation of commutative Frobenius algebras is the algebraic input
to surface evaluation and neck cutting; see J. Kock, *Frobenius Algebras and 2D
Topological Quantum Field Theories*, Chapter 2.
-/

public section

noncomputable section

open TensorProduct

namespace LinearMap

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  [Module.Finite R A] [Module.Projective R A]
  (ε : A →ₗ[R] R) [hε : ((mul R A).compr₂ ε).IsPerfPair]

local notation3 "e" => ((mul R A).compr₂ ε).toPerfPair
local notation3 "d" => (e).trans (WithConv.linearEquiv R (Module.Dual R A)).symm

/-- The coalgebra obtained by transposing multiplication under a perfect trace
pairing. Its counit is the prescribed trace. -/
@[instance_reducible]
def frobeniusCoalgebra : Coalgebra R A := by
  letI : CoalgebraStruct R A :=
    { comul := (TensorProduct.congr d d).symm.toLinearMap ∘ₗ
        Coalgebra.comul ∘ₗ (d).toLinearMap
      counit := ε }
  let f : TauCeti.ConvolutionDual R A ≃ₗc[R] A :=
    { __ := (d).symm
      counit_comp := by
        ext φ
        -- Expose the local coalgebra data and the convolution type synonym.
        change ε ((e).symm φ.ofConv) = φ.ofConv 1
        simpa only [compr₂_apply, mul_apply_apply, mul_one] using
          congrArg (fun f : Module.Dual R A => f 1)
            (((mul R A).compr₂ ε).apply_symm_toPerfPair_self φ.ofConv)
      map_comp_comul := by
        ext φ
        -- The target's coproduct is defined by transport along the inverse.
        change TensorProduct.congr (d).symm (d).symm (Coalgebra.comul φ) =
          (TensorProduct.congr d d).symm (Coalgebra.comul ((d) ((d).symm φ)))
        simp }
  exact f.toCoalgebra

/-- The reconstructed coalgebra has the original trace as counit. -/
@[simp] theorem frobeniusCoalgebra_counit : (frobeniusCoalgebra ε).counit = ε := (rfl)

private theorem frobeniusCoalgebra_comul :
    (frobeniusCoalgebra ε).comul =
      (TensorProduct.congr d d).symm.toLinearMap ∘ₗ
        Coalgebra.comul ∘ₗ (d).toLinearMap := (rfl)

/-- Tensoring the trace pairing identifies a tensor with the corresponding
bilinear functional on two copies of the algebra. -/
def traceTensorEquiv : A ⊗[R] A ≃ₗ[R] Module.Dual R (A ⊗[R] A) :=
  (TensorProduct.congr d d).trans (TauCeti.ConvolutionDual.dualDistribEquiv R A)

/-- The tensor trace pairing evaluates pure tensors componentwise. -/
@[simp] theorem traceTensorEquiv_tmul (a b x y : A) :
    traceTensorEquiv ε (a ⊗ₜ[R] b) (x ⊗ₜ[R] y) = ε (a * x) * ε (b * y) := by
  simp [traceTensorEquiv]

/-- The coproduct is adjoint to multiplication for the trace pairing. -/
@[simp] theorem traceTensorEquiv_frobeniusCoalgebra_comul (a x y : A) :
    traceTensorEquiv ε ((frobeniusCoalgebra ε).comul a) (x ⊗ₜ[R] y) =
      ε (a * (x * y)) := by
  simp only [frobeniusCoalgebra_comul, comp_apply, traceTensorEquiv,
    LinearEquiv.trans_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  simp

private theorem traceTensorEquiv_map_mulLeft (a : A) (t : A ⊗[R] A) (x y : A) :
    traceTensorEquiv ε ((mulLeft R a).rTensor A t) (x ⊗ₜ[R] y) =
      traceTensorEquiv ε t ((a * x) ⊗ₜ[R] y) := by
  induction t using TensorProduct.inductionOn with
  | tmul b c => simp [mul_left_comm, mul_comm]
  | add t u ht hu => simp_all

private theorem traceTensorEquiv_map_mulRight (a : A) (t : A ⊗[R] A) (x y : A) :
    traceTensorEquiv ε ((mulRight R a).lTensor A t) (x ⊗ₜ[R] y) =
      traceTensorEquiv ε t (x ⊗ₜ[R] (y * a)) := by
  induction t using TensorProduct.inductionOn with
  | tmul b c => simp [mul_left_comm, mul_comm]
  | add t u ht hu => simp_all

/-- Multiplying the first leg of the coproduct multiplies its input. -/
theorem frobeniusCoalgebra_comul_mul_left (a b : A) :
    (frobeniusCoalgebra ε).comul (a * b) =
      (mulLeft R a).rTensor A ((frobeniusCoalgebra ε).comul b) := by
  apply (traceTensorEquiv ε).injective
  apply TensorProduct.ext'
  intro x y
  simp [traceTensorEquiv_map_mulLeft, mul_left_comm, mul_comm]

/-- The right-leg form of the coproduct's multiplication law. -/
theorem frobeniusCoalgebra_comul_mul_right (a b : A) :
    (frobeniusCoalgebra ε).comul (a * b) =
      (mulRight R b).lTensor A ((frobeniusCoalgebra ε).comul a) := by
  apply (traceTensorEquiv ε).injective
  apply TensorProduct.ext'
  intro x y
  simp [traceTensorEquiv_map_mulRight, mul_left_comm, mul_comm]

/-- The trace-reconstructed coalgebra satisfies the native Frobenius law. -/
theorem frobeniusCoalgebra_isFrobenius :
    letI := frobeniusCoalgebra ε
    Coalgebra.IsFrobenius R A := by
  let := frobeniusCoalgebra ε
  constructor
  apply TensorProduct.ext'
  intro a b
  simp only [Coalgebra.IsFrobenius.left_def, Coalgebra.IsFrobenius.right_def,
    comp_apply, rTensor_tmul, lTensor_tmul, LinearEquiv.coe_coe]
  have hl (t : A ⊗[R] A) :
      (mul' R A).lTensor A (TensorProduct.assoc R A A A (t ⊗ₜ[R] b)) =
        (mulRight R b).lTensor A t := by
    induction t using TensorProduct.inductionOn with
    | tmul x y => simp
    | add t u ht hu => simp_all [add_tmul]
  have hr (t : A ⊗[R] A) :
      (mul' R A).rTensor A ((TensorProduct.assoc R A A A).symm (a ⊗ₜ[R] t)) =
        (mulLeft R a).rTensor A t := by
    induction t using TensorProduct.inductionOn with
    | tmul x y => simp
    | add t u ht hu => simp_all [tmul_add]
  rw [hl, hr, ← frobeniusCoalgebra_comul_mul_left ε a b,
    ← frobeniusCoalgebra_comul_mul_right ε a b]

/-- The coproduct of any Frobenius coalgebra with counit `ε` is adjoint to
multiplication for the trace pairing. -/
theorem traceTensorEquiv_comul_of_isFrobenius (c : Coalgebra R A) (hc : c.counit = ε)
    (hf : letI := c; Coalgebra.IsFrobenius R A) (a x y : A) :
    traceTensorEquiv ε (c.comul a) (x ⊗ₜ[R] y) = ε (a * (x * y)) := by
  let := c
  let := hf
  -- Contract the first leg after multiplying it by x, then pair the second with y.
  have heval (t : A ⊗[R] A) :
      traceTensorEquiv ε t (x ⊗ₜ[R] y) =
        ε (TensorProduct.lid R A (c.counit.rTensor A
          ((mul' R A).rTensor A ((TensorProduct.assoc R A A A).symm (x ⊗ₜ[R] t)))) * y) := by
    induction t using TensorProduct.inductionOn with
    | tmul b z => simp [hc, mul_comm b x]
    | add t u ht hu => simp_all [tmul_add, add_mul]
  have h := congrArg (fun f : A ⊗[R] A →ₗ[R] A ⊗[R] A => f (x ⊗ₜ[R] a))
    (Coalgebra.IsFrobenius.right_eq_comul_comp_mul' (R := R) (A := A))
  simp only [Coalgebra.IsFrobenius.right_def, comp_apply, lTensor_tmul,
    LinearEquiv.coe_coe, mul'_apply] at h
  rw [heval, h, Coalgebra.rTensor_counit_comul, TensorProduct.lid_tmul, one_smul,
    mul_comm x a, mul_assoc]

/-- A Frobenius coalgebra with the given counit is the trace reconstruction.
In particular, the reconstruction is independent of any choice of basis. -/
theorem frobeniusCoalgebra_eq (c : Coalgebra R A) (hc : c.counit = ε)
    (hf : letI := c; Coalgebra.IsFrobenius R A) : frobeniusCoalgebra ε = c := by
  have hcomul : (frobeniusCoalgebra ε).comul = c.comul := by
    ext a
    apply (traceTensorEquiv ε).injective
    apply TensorProduct.ext'
    intro x y
    rw [traceTensorEquiv_frobeniusCoalgebra_comul,
      traceTensorEquiv_comul_of_isFrobenius ε c hc hf]
  have hcounit : (frobeniusCoalgebra ε).counit = c.counit := by simp [hc]
  exact Coalgebra.ext hcomul hcounit

omit [Module.Finite R A] [Module.Projective R A] in
/-- The basis dual to `b` for the trace pairing, with the same indexing type. -/
def traceDualBasis {ι : Type*} [Finite ι] (b : Module.Basis ι R A) : Module.Basis ι R A := by
  classical
  exact b.dualBasis.map (e).symm

omit [Module.Finite R A] [Module.Projective R A] in
/-- Pairing a trace-dual basis vector with an element extracts its coordinate. -/
@[simp] theorem traceDualBasis_mul {ι : Type*} [Finite ι]
    (b : Module.Basis ι R A) (i : ι) (a : A) :
    ε (traceDualBasis ε b i * a) = b.repr a i := by
  classical
  simpa only [traceDualBasis, Module.Basis.map_apply, Module.Basis.dualBasis_apply,
    compr₂_apply, mul_apply_apply] using
    congrArg (fun f : Module.Dual R A => f a)
      (((mul R A).compr₂ ε).apply_symm_toPerfPair_self (b.dualBasis i))

omit [Module.Finite R A] [Module.Projective R A] in
/-- Coordinates in the trace-dual basis are pairings with the original basis. -/
@[simp] theorem traceDualBasis_repr {ι : Type*} [Finite ι]
    (b : Module.Basis ι R A) (a : A) (i : ι) :
    (traceDualBasis ε b).repr a i = ε (a * b i) := by
  classical
  simp [traceDualBasis]

/-- The dual-basis formula for the reconstructed coproduct, valid for every
finite basis, not just a chosen one. -/
theorem frobeniusCoalgebra_comul_eq_sum {ι : Type*} [Fintype ι]
    (b : Module.Basis ι R A) (a : A) :
    (frobeniusCoalgebra ε).comul a = ∑ i, b i ⊗ₜ[R] (traceDualBasis ε b i * a) := by
  classical
  apply (traceTensorEquiv ε).injective
  apply TensorProduct.ext'
  intro x y
  simp only [traceTensorEquiv_frobeniusCoalgebra_comul, map_sum]
  rw [LinearMap.sum_apply]
  simp only [traceTensorEquiv_tmul, mul_assoc, traceDualBasis_mul]
  symm
  calc
    ∑ i, ε (b i * x) * b.repr (a * y) i =
        ∑ i, b.repr (a * y) i • ε (b i * x) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_eq_mul, mul_comm]
    _ = ε ((∑ i, b.repr (a * y) i • b i) * x) := by
      rw [Finset.sum_mul, map_sum]
      simp only [smul_mul_assoc, map_smul]
    _ = ε ((a * y) * x) := by rw [b.sum_repr]
    _ = ε (a * (x * y)) := by rw [mul_right_comm, mul_assoc]

end LinearMap

namespace TauCeti

/-- A perfect trace on a finite projective commutative algebra determines a unique
coalgebra with that counit satisfying the Frobenius law. -/
theorem existsUnique_frobeniusCoalgebra
    (R A : Type*) [CommSemiring R] [CommSemiring A] [Algebra R A]
    [Module.Finite R A] [Module.Projective R A]
    (ε : A →ₗ[R] R) (hε : ((LinearMap.mul R A).compr₂ ε).IsPerfPair) :
    ∃! c : Coalgebra R A, c.counit = ε ∧ (letI := c; Coalgebra.IsFrobenius R A) := by
  let := hε
  exact ⟨ε.frobeniusCoalgebra, ⟨ε.frobeniusCoalgebra_counit, ε.frobeniusCoalgebra_isFrobenius⟩,
    fun c hc => (ε.frobeniusCoalgebra_eq c hc.1 hc.2).symm⟩

end TauCeti
