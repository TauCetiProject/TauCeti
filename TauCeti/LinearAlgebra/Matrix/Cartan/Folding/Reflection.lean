/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Folding.Basic
public import TauCeti.LinearAlgebra.FixedSubmodule.Permutation
public import Mathlib.LinearAlgebra.Reflection
import TauCeti.LinearAlgebra.Matrix.Submatrix

/-!
# Integral reflections on the diagram-fixed Cartan lattice

For a simply laced Gram matrix `B` and a diagram permutation `σ`, regard the fixed
coordinate lattice as a Cartan lattice. Its normalized folded simple coroot is
`H'_O = c_O ∑_{i ∈ O} h_i`, where `c_O = Matrix.foldingScale B σ O`.
The corresponding simple root functional evaluates `B *ᵥ v` at a vertex of `O`.
Their pairing is two, so Mathlib's `Module.reflection` constructs the integral
simple reflection on this actual fixed lattice, without dividing by orbit sizes.

The pairing of root `O` with coroot `P` is `C_{P,O}`: the folded matrix `C`
has Cartan (`H`) rows, not root rows. In particular, these reflections use the
normalized coroots, not the unscaled orbit sums. This distinction matters for
adjacent orbits, where the coroot has an extra factor of two.

The construction follows V. G. Kac, *Infinite dimensional Lie algebras*, third
edition, §7.9, and uses `Equiv.Perm.permutationFixedBasis` for the integral
fixed lattice and `Matrix.foldingScale_mul_sum` for the normalization.
-/

public noncomputable section

open Finset LinearEquiv

namespace Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]
variable (B : Matrix I I ℤ) (σ : Equiv.Perm I)

/-- The normalized folded simple coroot in the actual diagram-fixed coordinate lattice. -/
def foldedCoroot (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    (funCongrLeft ℤ ℤ σ).toLinearMap.fixedSubmodule :=
  B.foldingScale σ O • σ.permutationFixedBasis O

/-- A normalized folded simple coroot scales the orbit indicator basis vector by `foldingScale`. -/
theorem foldedCoroot_def (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    B.foldedCoroot σ O = B.foldingScale σ O • σ.permutationFixedBasis O :=
  (rfl)

/-- The ambient coordinate formula for a normalized folded coroot. -/
theorem coe_foldedCoroot (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    (B.foldedCoroot σ O : I → ℤ) =
      B.foldingScale σ O • ∑ i with σ.SameCycle i O.out, Pi.single i 1 := by
  classical
  simp only [foldedCoroot, Submodule.coe_smul, Equiv.Perm.permutationFixedBasis_eq_sum]
  congr 2
  ext i
  simp only [mem_filter, mem_univ, true_and]
  exact Quotient.mk_eq_iff_out

/-- A folded simple root, restricted to the diagram-fixed Cartan lattice. -/
def foldedRootFunctional (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    Module.Dual ℤ (funCongrLeft ℤ ℤ σ).toLinearMap.fixedSubmodule :=
  (LinearMap.proj O.out).comp
    (B.mulVecLin.comp (funCongrLeft ℤ ℤ σ).toLinearMap.fixedSubmodule.subtype)

omit [DecidableEq I] in
theorem foldedRootFunctional_apply (O : Quotient (Equiv.Perm.SameCycle.setoid σ))
    (v : (funCongrLeft ℤ ℤ σ).toLinearMap.fixedSubmodule) :
    B.foldedRootFunctional σ O v = (B *ᵥ (v : I → ℤ)) O.out :=
  (rfl)

/-- The root/coroot pairing uses the transpose of the H-row folded Cartan matrix. -/
@[simp]
theorem foldedRootFunctional_foldedCoroot (hB : B.IsSymm)
    (O P : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    B.foldedRootFunctional σ O (B.foldedCoroot σ P) = B.foldedCartanMatrix σ P O := by
  rw [foldedRootFunctional_apply, coe_foldedCoroot, mulVec_smul, mulVec_sum]
  simp only [Pi.smul_apply, smul_eq_mul, mulVec_single, op_smul_eq_smul, one_smul,
    Finset.sum_apply, col_apply, foldedCartanMatrix_apply]
  congr 1
  exact sum_congr rfl fun i _ ↦ hB.apply _ _

variable {B σ}

omit [DecidableEq I] in
/-- A fixed vector's root evaluation is independent of the chosen vertex in an orbit. -/
theorem foldedRootFunctional_apply_of_sameCycle (hσ : B.reindex σ σ = B)
    {O : Quotient (Equiv.Perm.SameCycle.setoid σ)} {i : I} (hi : σ.SameCycle i O.out)
    (v : (funCongrLeft ℤ ℤ σ).toLinearMap.fixedSubmodule) :
    B.foldedRootFunctional σ O v = (B *ᵥ (v : I → ℤ)) i := by
  classical
  have hv (j : I) : (v : I → ℤ) (σ j) = (v : I → ℤ) j := by
    have h := congrFun (LinearMap.mem_fixedSubmodule_iff.mp v.property) j
    simpa using h
  have hrow (j : I) : (B *ᵥ (v : I → ℤ)) (σ j) = (B *ᵥ (v : I → ℤ)) j := by
    simp only [mulVec, dotProduct]
    rw [← Equiv.sum_comp σ]
    exact sum_congr rfl fun k _ ↦ by rw [apply_apply_of_reindex_eq hσ, hv]
  exact (hi.apply_eq_of_apply_eq hrow).symm

/-- The Gram pairing with a folded coroot is the simple root functional times the
folding scale and the orbit size. No orbit size is inverted. -/
theorem foldedCoroot_dotProduct_mulVec (hσ : B.reindex σ σ = B)
    (O : Quotient (Equiv.Perm.SameCycle.setoid σ))
    (v : (funCongrLeft ℤ ℤ σ).toLinearMap.fixedSubmodule) :
    (B.foldedCoroot σ O : I → ℤ) ⬝ᵥ B *ᵥ (v : I → ℤ) =
      (B.foldingScale σ O * ({i | σ.SameCycle i O.out} : Finset I).card) *
        B.foldedRootFunctional σ O v := by
  classical
  rw [coe_foldedCoroot, smul_dotProduct]
  simp only [sum_dotProduct, single_one_dotProduct, smul_eq_mul]
  have hs : ∑ i with σ.SameCycle i O.out, (B *ᵥ (v : I → ℤ)) i =
      ∑ i with σ.SameCycle i O.out, B.foldedRootFunctional σ O v :=
    sum_congr rfl fun i hi ↦
      (foldedRootFunctional_apply_of_sameCycle hσ (by simpa using hi) v).symm
  rw [hs, sum_const, nsmul_eq_mul, mul_assoc]

/-- The folded simple reflection on the integral fixed Cartan lattice. -/
def foldedReflection (hB : B.PosDef) (hdiag : ∀ i, B i i = 2)
    (hoff : ∀ i j, i ≠ j → B i j ≤ 0) (hσ : B.reindex σ σ = B)
    (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    (funCongrLeft ℤ ℤ σ).toLinearMap.fixedSubmodule ≃ₗ[ℤ]
      (funCongrLeft ℤ ℤ σ).toLinearMap.fixedSubmodule :=
  Module.reflection (x := B.foldedCoroot σ O) (f := B.foldedRootFunctional σ O)
    (by rw [foldedRootFunctional_foldedCoroot B σ hB.isHermitian.isSymm,
      foldedCartanMatrix_apply_self hB hdiag hoff hσ])

variable (hB : B.PosDef) (hdiag : ∀ i, B i i = 2)
    (hoff : ∀ i j, i ≠ j → B i j ≤ 0) (hσ : B.reindex σ σ = B)

/-- The reflection subtracts the root evaluation times the normalized coroot. -/
theorem foldedReflection_apply (O : Quotient (Equiv.Perm.SameCycle.setoid σ))
    (v : (funCongrLeft ℤ ℤ σ).toLinearMap.fixedSubmodule) :
    foldedReflection hB hdiag hoff hσ O v =
      v - B.foldedRootFunctional σ O v • B.foldedCoroot σ O :=
  Module.reflection_apply _ _

/-- Simple reflections act on folded coroots by the H-row Cartan coefficients. -/
theorem foldedReflection_foldedCoroot (O P : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    foldedReflection hB hdiag hoff hσ O (B.foldedCoroot σ P) =
      B.foldedCoroot σ P - B.foldedCartanMatrix σ P O • B.foldedCoroot σ O := by
  rw [foldedReflection_apply, foldedRootFunctional_foldedCoroot B σ hB.isHermitian.isSymm]

/-- Precomposition by a folded reflection acts on root functionals by the same H-row
Cartan coefficients. This is the dual reflection equation. -/
theorem foldedRootFunctional_foldedReflection
    (O P : Quotient (Equiv.Perm.SameCycle.setoid σ))
    (v : (funCongrLeft ℤ ℤ σ).toLinearMap.fixedSubmodule) :
    B.foldedRootFunctional σ O (foldedReflection hB hdiag hoff hσ P v) =
      B.foldedRootFunctional σ O v -
        B.foldedCartanMatrix σ P O * B.foldedRootFunctional σ P v := by
  rw [foldedReflection_apply, map_sub, _root_.map_smul,
    foldedRootFunctional_foldedCoroot B σ hB.isHermitian.isSymm]
  simp only [smul_eq_mul, mul_comm]

/-- The inverse of a folded simple reflection is itself. -/
@[simp]
theorem foldedReflection_symm (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    (foldedReflection hB hdiag hoff hσ O).symm = foldedReflection hB hdiag hoff hσ O :=
  Module.reflection_symm _

/-- Applying a folded simple reflection twice fixes every integral fixed vector. -/
@[simp]
theorem foldedReflection_foldedReflection (O : Quotient (Equiv.Perm.SameCycle.setoid σ))
    (v : (funCongrLeft ℤ ℤ σ).toLinearMap.fixedSubmodule) :
    foldedReflection hB hdiag hoff hσ O (foldedReflection hB hdiag hoff hσ O v) = v :=
  Module.involutive_reflection _ v

/-- A folded simple reflection negates its normalized simple coroot. -/
@[simp]
theorem foldedReflection_apply_self (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    foldedReflection hB hdiag hoff hσ O (B.foldedCoroot σ O) = -B.foldedCoroot σ O :=
  Module.reflection_apply_self _

/-- Folded simple reflections preserve the ambient integral Gram pairing on fixed vectors. -/
@[simp]
theorem foldedReflection_dotProduct_mulVec
    (O : Quotient (Equiv.Perm.SameCycle.setoid σ))
    (v w : (funCongrLeft ℤ ℤ σ).toLinearMap.fixedSubmodule) :
    (foldedReflection hB hdiag hoff hσ O v : I → ℤ) ⬝ᵥ
        B *ᵥ (foldedReflection hB hdiag hoff hσ O w : I → ℤ) =
      (v : I → ℤ) ⬝ᵥ B *ᵥ (w : I → ℤ) := by
  have hleft := foldedCoroot_dotProduct_mulVec hσ O
  have hright (u : (funCongrLeft ℤ ℤ σ).toLinearMap.fixedSubmodule) :
      (u : I → ℤ) ⬝ᵥ B *ᵥ (B.foldedCoroot σ O : I → ℤ) =
        (B.foldingScale σ O * ({i | σ.SameCycle i O.out} : Finset I).card) *
          B.foldedRootFunctional σ O u := by
    rw [hB.isHermitian.isSymm.dotProduct_mulVec_comm, hleft]
  rw [foldedReflection_apply, foldedReflection_apply]
  simp only [Submodule.coe_sub, Submodule.coe_smul, mulVec_sub, mulVec_smul,
    sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    hleft, hright, foldedRootFunctional_foldedCoroot B σ hB.isHermitian.isSymm,
    foldedCartanMatrix_apply_self hB hdiag hoff hσ]
  ring

end Matrix
