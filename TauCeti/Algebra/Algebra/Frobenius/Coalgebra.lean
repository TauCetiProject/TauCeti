/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import TauCeti.Algebra.Coalgebra.Basic
import TauCeti.Algebra.HopfAlgebra.FiniteDual.Basic

/-!
# Reconstructing a Frobenius coalgebra from a perfect trace

This file develops single-algebra Frobenius coalgebra duality and trace reconstruction over an
arbitrary commutative semiring `R`:

* For any unital (not necessarily associative or commutative) Frobenius coalgebra `A`, its trace
  pairing `(a, b) ↦ counit (a * b)` is perfect
  (`TauCeti.Coalgebra.IsFrobenius.isPerfPair_compr₂_mul_counit`), `LinearMap.traceTensorEquiv`
  identifies `A ⊗[R] A` with `Module.Dual R (A ⊗[R] A)` via `x ⊗ₜ y ↦ ε (x * a) * ε (b * y)`,
  and the counit uniquely determines the Frobenius coalgebra structure
  (`Coalgebra.eq_of_counit_eq_of_isFrobenius`).
* For a finite projective commutative algebra `A`, a perfect trace pairing determines a unique
  Frobenius coalgebra `LinearMap.frobeniusCoalgebra` with the given counit. The coproduct is the
  transpose of multiplication under the trace pairing. In any finite basis it is the familiar sum
  of basis vectors tensored with their trace-duals times the input
  (`LinearMap.frobeniusCoalgebra_comul_eq_sum`, `TauCeti.Coalgebra.IsFrobenius.comul_eq_sum`).

We reuse the transposed coalgebra on `TauCeti.ConvolutionDual`, Mathlib's perfect pairings, and
`CoalgEquiv.toCoalgebra` to obtain the coalgebra laws. No field or characteristic hypothesis is
needed.

## References

* J. Kock, *Frobenius Algebras and 2D Topological Quantum Field Theories*, Chapter 2.
-/

public section

noncomputable section

open TensorProduct

namespace TauCeti.Coalgebra.IsFrobenius

variable {R A : Type*} [CommSemiring R]

/-- Multiplying the first leg of the coproduct of a Frobenius coalgebra on the left by `x`
multiplies its input on the left by `x`. -/
theorem comul_mul_left [NonUnitalNonAssocSemiring A] [Module R A] [SMulCommClass R A A]
    [IsScalarTower R A A] [Coalgebra R A] [Coalgebra.IsFrobenius R A] (x b : A) :
    (LinearMap.mulLeft R x).rTensor A (Coalgebra.comul (R := R) b) =
      Coalgebra.comul (R := R) (x * b) := by
  have h := congrArg (fun f : A ⊗[R] A →ₗ[R] A ⊗[R] A ↦ f (x ⊗ₜ[R] b))
    (Coalgebra.IsFrobenius.right_eq_comul_comp_mul' (R := R) (A := A))
  simp only [Coalgebra.IsFrobenius.right_def, LinearMap.comp_apply, LinearMap.lTensor_tmul,
    LinearMap.mul'_apply] at h
  rw [← h]
  induction Coalgebra.comul (R := R) b using TensorProduct.inductionOn with
  | tmul u v => simp
  | add t u ht hu => simp_all [TensorProduct.tmul_add]

/-- The trace pairing `(a, b) ↦ counit (a * b)` of a unital Frobenius coalgebra is a perfect
pairing. -/
instance isPerfPair_compr₂_mul_counit [NonAssocSemiring A] [Module R A] [Coalgebra R A]
    [SMulCommClass R A A] [IsScalarTower R A A] [Coalgebra.IsFrobenius R A] :
    ((LinearMap.mul R A).compr₂ (Coalgebra.counit (R := R) (A := A))).IsPerfPair :=
  LinearMap.IsPerfPair.of_bijective _ Coalgebra.IsFrobenius.compr₂_mul_counit_bijective

end TauCeti.Coalgebra.IsFrobenius

namespace LinearMap

section NonUnital

variable {R A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [SMulCommClass R A A] [IsScalarTower R A A]
  [Module.Finite R A] [Module.Projective R A]
  (ε : A →ₗ[R] R) [hε : ((mul R A).compr₂ ε).IsPerfPair]

/-- Tensoring the trace pairing identifies a tensor `a ⊗ₜ b` with the bilinear functional
`x ⊗ₜ y ↦ ε (x * a) * ε (b * y)` on two copies of the algebra. -/
def traceTensorEquiv : A ⊗[R] A ≃ₗ[R] Module.Dual R (A ⊗[R] A) :=
  (TensorProduct.congr
      (((mul R A).compr₂ ε).flip.toPerfPair)
      (((mul R A).compr₂ ε).toPerfPair)).trans
    (TensorProduct.dualDistribEquiv R A A)

/-- The tensor trace pairing evaluates pure tensors componentwise. -/
@[simp] theorem traceTensorEquiv_tmul (a b x y : A) :
    traceTensorEquiv ε (a ⊗ₜ[R] b) (x ⊗ₜ[R] y) = ε (x * a) * ε (b * y) := by
  simp [traceTensorEquiv, mul_comm]

/-- The coproduct of any Frobenius coalgebra with counit `ε` is adjoint to multiplication for the
trace pairing: `traceTensorEquiv ε (c.comul a) (x ⊗ₜ y) = ε (x * a * y)`. -/
theorem traceTensorEquiv_comul_of_isFrobenius (c : Coalgebra R A) (hc : c.counit = ε)
    (hf : letI := c; Coalgebra.IsFrobenius R A) (a x y : A) :
    traceTensorEquiv ε (c.comul a) (x ⊗ₜ[R] y) = ε (x * a * y) := by
  let := c
  let := hf
  -- Contract the first leg after multiplying it on the left by `x`, then pair the second with `y`.
  have heval (t : A ⊗[R] A) :
      traceTensorEquiv ε t (x ⊗ₜ[R] y) =
        ε (TensorProduct.lid R A (c.counit.rTensor A
          ((mul' R A).rTensor A ((TensorProduct.assoc R A A A).symm (x ⊗ₜ[R] t)))) * y) := by
    induction t using TensorProduct.inductionOn with
    | tmul b z => simp [hc, smul_mul_assoc, map_smul, smul_eq_mul]
    | add t u ht hu => simp_all [tmul_add, add_mul]
  have h := congrArg (fun f : A ⊗[R] A →ₗ[R] A ⊗[R] A => f (x ⊗ₜ[R] a))
    (Coalgebra.IsFrobenius.right_eq_comul_comp_mul' (R := R) (A := A))
  simp only [Coalgebra.IsFrobenius.right_def, comp_apply, lTensor_tmul,
    LinearEquiv.coe_coe, mul'_apply] at h
  rw [heval, h, Coalgebra.rTensor_counit_comul, TensorProduct.lid_tmul, one_smul]

end NonUnital

end LinearMap

namespace Coalgebra

/-- Two Frobenius coalgebra structures on the same algebra with the same counit are equal. -/
theorem eq_of_counit_eq_of_isFrobenius {R A : Type*} [CommSemiring R] [NonAssocSemiring A]
    [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
    (c₁ c₂ : Coalgebra R A) (h₁ : letI := c₁; IsFrobenius R A)
    (h₂ : letI := c₂; IsFrobenius R A) (hε : c₁.counit = c₂.counit) : c₁ = c₂ := by
  refine Coalgebra.ext ?_ hε
  let := c₁; have := h₁
  ext a
  apply (LinearMap.traceTensorEquiv c₁.counit).injective
  refine TensorProduct.ext' fun x y ↦ ?_
  rw [LinearMap.traceTensorEquiv_comul_of_isFrobenius c₁.counit c₁ rfl h₁,
    LinearMap.traceTensorEquiv_comul_of_isFrobenius c₁.counit c₂ hε.symm h₂]

end Coalgebra

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

private theorem traceTensorEquiv_eq_convolutionDual (t : A ⊗[R] A) :
    traceTensorEquiv ε t =
      TauCeti.ConvolutionDual.dualDistribEquiv R A (TensorProduct.congr d d t) := by
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    refine TensorProduct.ext' fun x y ↦ ?_
    simp [mul_comm]
  | add t u ht hu => simp_all

/-- The coproduct is adjoint to multiplication for the trace pairing. -/
@[simp] theorem traceTensorEquiv_frobeniusCoalgebra_comul (a x y : A) :
    traceTensorEquiv ε ((frobeniusCoalgebra ε).comul a) (x ⊗ₜ[R] y) =
      ε (a * (x * y)) := by
  rw [traceTensorEquiv_eq_convolutionDual, frobeniusCoalgebra_comul]
  simp only [comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
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

/-- A Frobenius coalgebra with the given counit is the trace reconstruction.
In particular, the reconstruction is independent of any choice of basis. -/
theorem frobeniusCoalgebra_eq (c : Coalgebra R A) (hc : c.counit = ε)
    (hf : letI := c; Coalgebra.IsFrobenius R A) : frobeniusCoalgebra ε = c :=
  Coalgebra.eq_of_counit_eq_of_isFrobenius (frobeniusCoalgebra ε) c
    (frobeniusCoalgebra_isFrobenius ε) hf (by simp [hc])

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
/-- Pairing a basis element with a trace-dual basis element yields the Kronecker delta. -/
@[simp] theorem apply_mul_traceDualBasis {ι : Type*} [Finite ι] [DecidableEq ι]
    (b : Module.Basis ι R A) (i j : ι) :
    ε (b i * traceDualBasis ε b j) = if i = j then 1 else 0 := by
  rw [mul_comm, traceDualBasis_mul, b.repr_self, Finsupp.single_apply, eq_comm]

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
    ∑ i, ε (x * b i) * b.repr (a * y) i =
        ∑ i, b.repr (a * y) i • ε (x * b i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_eq_mul, mul_comm]
    _ = ε (x * ∑ i, b.repr (a * y) i • b i) := by
      rw [Finset.mul_sum, map_sum]
      simp only [mul_smul_comm, map_smul]
    _ = ε (x * (a * y)) := by rw [b.sum_repr]
    _ = ε (a * (x * y)) := by rw [mul_left_comm]

end LinearMap

namespace TauCeti

/-- In any finite basis `b` of a commutative Frobenius algebra, the comultiplication of `a` is
`∑ i, b i ⊗ₜ (traceDualBasis counit b i * a)`. -/
theorem Coalgebra.IsFrobenius.comul_eq_sum {R A : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] [Coalgebra R A] [Coalgebra.IsFrobenius R A] {ι : Type*} [Fintype ι]
    (b : Module.Basis ι R A) (a : A) :
    Coalgebra.comul (R := R) a =
      ∑ i, b i ⊗ₜ[R] (LinearMap.traceDualBasis (Coalgebra.counit (R := R) (A := A)) b i * a) := by
  have hc : (Coalgebra.counit (R := R) (A := A)).frobeniusCoalgebra = ‹Coalgebra R A› :=
    LinearMap.frobeniusCoalgebra_eq _ _ rfl inferInstance
  have hcomul := LinearMap.frobeniusCoalgebra_comul_eq_sum (Coalgebra.counit (R := R) (A := A)) b a
  rw [hc] at hcomul
  exact hcomul

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
