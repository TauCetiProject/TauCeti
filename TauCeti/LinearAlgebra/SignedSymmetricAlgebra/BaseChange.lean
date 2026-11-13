/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.GradedModule.BaseChange
public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Grading
public import Mathlib.RingTheory.GradedAlgebra.TensorProduct

/-!
# Scalar extension of signed symmetric algebras

`SignedSym.baseChangeEquiv` identifies scalar extension of the signed symmetric algebra with
the signed symmetric algebra on the scalar-extended internally graded module. The comparison
sends a pure tensor of a generator to the generator of that tensor and preserves input degree.
It works over arbitrary commutative rings, without flatness, freeness, or an invertible 2.

The signed quotient follows J. Pardon, *Contact homology and virtual fundamental cycles*,
equation (1.1). The two universal-property maps and their generator computations adapt the
construction of Mathlib's `ExteriorAlgebra.baseChangeEquiv` by Nailin Guan, using the signed
swap relation in place of the alternating relation.
-/

public section

open scoped TensorProduct

namespace TauCeti.SignedSym

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  (G : InternalGrading R V ℤ) (S : Type*) [CommRing S] [Algebra R S]

private theorem baseChange_generator_mul_generator (p q : ℤ) (x y : S ⊗[R] V)
    (hx : x ∈ (G.baseChange S).piece p) (hy : y ∈ (G.baseChange S).piece q) :
    (generator G).baseChange S x * (generator G).baseChange S y =
      ((p * q).negOnePow : ℤ) •
        ((generator G).baseChange S y * (generator G).baseChange S x) := by
  rw [InternalGrading.baseChange_piece] at hx hy
  obtain ⟨x, rfl⟩ := (G.piece p).toBaseChange_surjective' S hx
  obtain ⟨y, rfl⟩ := (G.piece q).toBaseChange_surjective' S hy
  clear hx hy
  induction x using TensorProduct.inductionOn with
  | tmul s x =>
    induction y using TensorProduct.inductionOn with
    | tmul t y =>
      simp only [Submodule.coe_toBaseChange_tmul, LinearMap.baseChange_tmul,
        Algebra.TensorProduct.tmul_mul_tmul]
      rw [generator_mul_generator G x.2 y.2, mul_comm s t]
      exact (map_zsmul (TensorProduct.mk R S (SignedSym G) (t * s)) _ _)
    | add a b ha hb =>
      simpa only [map_add, Submodule.coe_add, mul_add, add_mul, smul_add] using
        congrArg₂ (· + ·) ha hb
  | add a b ha hb =>
    simpa only [map_add, Submodule.coe_add, mul_add, add_mul, smul_add] using
      congrArg₂ (· + ·) ha hb

private noncomputable def fromBaseChange :
    SignedSym (G.baseChange S) →ₐ[S] S ⊗[R] SignedSym G :=
  lift (G.baseChange S) ((generator G).baseChange S)
    (baseChange_generator_mul_generator G S)

private noncomputable def baseChangeGenerator :
    V →ₗ[R] SignedSym (G.baseChange S) :=
  ((generator (G.baseChange S)).restrictScalars R).comp (TensorProduct.mk R S V 1)

private theorem baseChangeGenerator_mul_generator (p q : ℤ) (x y : V)
    (hx : x ∈ G.piece p) (hy : y ∈ G.piece q) :
    baseChangeGenerator G S x * baseChangeGenerator G S y =
      ((p * q).negOnePow : ℤ) • (baseChangeGenerator G S y * baseChangeGenerator G S x) := by
  exact generator_mul_generator (G.baseChange S)
    (by simpa using Submodule.tmul_mem_baseChange_of_mem (1 : S) hx)
    (by simpa using Submodule.tmul_mem_baseChange_of_mem (1 : S) hy)

private noncomputable def toBaseChangeAux :
    SignedSym G →ₐ[R] SignedSym (G.baseChange S) :=
  lift G (baseChangeGenerator G S) (baseChangeGenerator_mul_generator G S)

private noncomputable def toBaseChange :
    S ⊗[R] SignedSym G →ₐ[S] SignedSym (G.baseChange S) :=
  AlgHom.liftEquiv R S _ _ (toBaseChangeAux G S)

private theorem toBaseChange_tmul_generator (s : S) (x : V) :
    toBaseChange G S (s ⊗ₜ[R] generator G x) = generator (G.baseChange S) (s ⊗ₜ[R] x) := by
  rw [toBaseChange, AlgHom.liftEquiv_tmul, toBaseChangeAux, lift_generator]
  simp only [baseChangeGenerator, LinearMap.comp_apply, LinearMap.coe_restrictScalars,
    TensorProduct.mk_apply]
  rw [← map_smul, TensorProduct.smul_tmul']
  simp

private theorem fromBaseChange_generator (x : S ⊗[R] V) :
    fromBaseChange G S (generator (G.baseChange S) x) = (generator G).baseChange S x := by
  simp [fromBaseChange]

/-- Scalar extension commutes with the signed symmetric algebra, including in characteristic
two. -/
noncomputable def baseChangeEquiv :
    S ⊗[R] SignedSym G ≃ₐ[S] SignedSym (G.baseChange S) :=
  AlgEquiv.ofAlgHom (toBaseChange G S) (fromBaseChange G S)
    (by
      apply hom_ext
      intro x
      induction x using TensorProduct.inductionOn with
      | tmul s x => simp [fromBaseChange_generator, toBaseChange_tmul_generator]
      | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy)
    (by
      apply Algebra.TensorProduct.ext
      · exact Subsingleton.elim _ _
      · apply hom_ext
        intro x
        simp [toBaseChange_tmul_generator, fromBaseChange_generator])

/-- The forward comparison carries tensors of generators to generators of tensors. -/
@[simp]
theorem baseChangeEquiv_tmul_generator (s : S) (x : V) :
    baseChangeEquiv G S (s ⊗ₜ[R] generator G x) =
      generator (G.baseChange S) (s ⊗ₜ[R] x) :=
  toBaseChange_tmul_generator G S s x

/-- The inverse comparison is scalar extension of the original generator map. -/
@[simp]
theorem baseChangeEquiv_symm_generator (x : S ⊗[R] V) :
    (baseChangeEquiv G S).symm (generator (G.baseChange S) x) =
      (generator G).baseChange S x :=
  fromBaseChange_generator G S x

/-- Applying the comparison after scalar extension of the generator gives the extended
algebra's generator, on arbitrary tensors. -/
@[simp]
theorem baseChangeEquiv_baseChange_generator (x : S ⊗[R] V) :
    baseChangeEquiv G S ((generator G).baseChange S x) = generator (G.baseChange S) x := by
  rw [← baseChangeEquiv_symm_generator]
  exact (baseChangeEquiv G S).apply_symm_apply _

private theorem isHomogeneous_baseChangeEquiv_symm :
    LinearMap.IsHomogeneous (baseChangeEquiv G S).symm.toLinearMap
      (signedSymPiece (G.baseChange S)) (fun p ↦ (signedSymPiece G p).baseChange S) 0 := by
  apply isHomogeneous_lift
  refine LinearMap.isHomogeneous_def.2 fun p x hx => ?_
  rw [InternalGrading.baseChange_piece] at hx
  obtain ⟨x, rfl⟩ := (G.piece p).toBaseChange_surjective' S hx
  clear hx
  induction x using TensorProduct.inductionOn with
  | tmul s x =>
    simpa only [Submodule.coe_toBaseChange_tmul, LinearMap.baseChange_tmul, add_zero] using
      Submodule.tmul_mem_baseChange_of_mem s (generator_mem_signedSymPiece G x.2)
  | add x y hx hy => simpa only [map_add, Submodule.coe_add] using add_mem hx hy

/-- The scalar-extension comparison preserves the integer input degree. -/
theorem isHomogeneous_baseChangeEquiv :
    LinearMap.IsHomogeneous (baseChangeEquiv G S).toLinearMap
      (fun p ↦ (signedSymPiece G p).baseChange S) (signedSymPiece (G.baseChange S)) 0 := by
  have h := LinearMap.IsHomogeneous.linearEquiv_symm
    (G := InternalGrading.ofDecomposition (signedSymPiece (G.baseChange S)))
    (H := InternalGrading.ofDecomposition (fun p ↦ (signedSymPiece G p).baseChange S))
    (e := (baseChangeEquiv G S).symm.toLinearEquiv)
    (by simpa only [InternalGrading.ofDecomposition_piece,
      AlgEquiv.toLinearEquiv_toLinearMap] using isHomogeneous_baseChangeEquiv_symm G S)
  simpa only [InternalGrading.ofDecomposition_piece, ← AlgEquiv.toLinearEquiv_symm,
    AlgEquiv.symm_symm, AlgEquiv.toLinearEquiv_toLinearMap] using h

/-- The comparison preserves and reflects each homogeneous input-degree piece. -/
-- Compare pieces before the quotient-membership rule expands the target piece.
@[simp↓]
theorem baseChangeEquiv_mem_signedSymPiece_iff {p : ℤ} (x : S ⊗[R] SignedSym G) :
    baseChangeEquiv G S x ∈ signedSymPiece (G.baseChange S) p ↔
      x ∈ (signedSymPiece G p).baseChange S := by
  constructor
  · intro hx
    simpa only [add_zero, AlgEquiv.toLinearMap_apply, AlgEquiv.symm_apply_apply] using
      (isHomogeneous_baseChangeEquiv_symm G S).map_mem hx
  · intro hx
    simpa only [add_zero, AlgEquiv.toLinearMap_apply] using
      (isHomogeneous_baseChangeEquiv G S).map_mem hx

end TauCeti.SignedSym
