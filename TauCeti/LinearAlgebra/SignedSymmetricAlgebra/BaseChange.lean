/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.GradedModule.BaseChange
public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Grading
public import Mathlib.RingTheory.GradedAlgebra.TensorProduct
import TauCeti.RingTheory.GradedAlgebra.Homogeneous.Maps

/-!
# Scalar extension of signed symmetric algebras

`SignedSym.baseChangeEquiv` identifies scalar extension of the signed symmetric algebra with
the signed symmetric algebra on the scalar-extended internally graded module. The comparison
sends a pure tensor of a generator to the generator of that tensor, preserves input degree,
and is natural in degree-preserving linear maps.
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

private theorem baseChangeGenerator_apply (x : V) :
    baseChangeGenerator G S x = generator (G.baseChange S) ((1 : S) ⊗ₜ[R] x) := by
  simp [baseChangeGenerator]

private theorem baseChangeGenerator_mul_generator (p q : ℤ) (x y : V)
    (hx : x ∈ G.piece p) (hy : y ∈ G.piece q) :
    baseChangeGenerator G S x * baseChangeGenerator G S y =
      ((p * q).negOnePow : ℤ) • (baseChangeGenerator G S y * baseChangeGenerator G S x) := by
  simp only [baseChangeGenerator_apply]
  exact generator_mul_generator (G.baseChange S)
    (by simpa using Submodule.tmul_mem_baseChange_of_mem (1 : S) hx)
    (by simpa using Submodule.tmul_mem_baseChange_of_mem (1 : S) hy)

private noncomputable def toBaseChangeAux :
    signedSymPiece G →ₐᵍ[R]
      (fun p ↦ (signedSymPiece (G.baseChange S) p).restrictScalars R) :=
  gradedLift G _ (baseChangeGenerator G S) (baseChangeGenerator_mul_generator G S)
    (LinearMap.isHomogeneous_def.2 fun p x hx => by
      have hx' : (1 : S) ⊗ₜ[R] x ∈ (G.baseChange S).piece p := by
        simpa only [InternalGrading.baseChange_piece] using
          Submodule.tmul_mem_baseChange_of_mem (1 : S) hx
      simpa only [add_zero, baseChangeGenerator_apply, Submodule.restrictScalars_mem] using
        generator_mem_signedSymPiece (G.baseChange S) hx')

private noncomputable def toBaseChange :
    (fun p ↦ (signedSymPiece G p).baseChange S) →ₐᵍ[S]
      signedSymPiece (G.baseChange S) :=
  GradedAlgHom.liftEquiv _ _ (toBaseChangeAux G S)

private theorem toBaseChange_tmul_generator (s : S) (x : V) :
    toBaseChange G S (s ⊗ₜ[R] generator G x) = generator (G.baseChange S) (s ⊗ₜ[R] x) := by
  rw [toBaseChange, GradedAlgHom.liftEquiv_tmul, toBaseChangeAux, gradedLift_generator]
  rw [baseChangeGenerator_apply]
  rw [← map_smul, TensorProduct.smul_tmul']
  simp

private theorem fromBaseChange_generator (x : S ⊗[R] V) :
    fromBaseChange G S (generator (G.baseChange S) x) = (generator G).baseChange S x := by
  simp [fromBaseChange]

/-- Scalar extension commutes with the signed symmetric algebra, including in characteristic
two. -/
noncomputable def baseChangeEquiv :
    S ⊗[R] SignedSym G ≃ₐ[S] SignedSym (G.baseChange S) :=
  AlgEquiv.ofAlgHom (toBaseChange G S).toAlgHom (fromBaseChange G S)
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

private theorem coe_baseChangeEquiv :
    ⇑(baseChangeEquiv G S) = ⇑(toBaseChange G S) := by
  ext
  simp [baseChangeEquiv]

/-- The forward comparison carries tensors of generators to generators of tensors. -/
@[simp]
theorem baseChangeEquiv_tmul_generator (s : S) (x : V) :
    baseChangeEquiv G S (s ⊗ₜ[R] generator G x) =
      generator (G.baseChange S) (s ⊗ₜ[R] x) := by
  simp [baseChangeEquiv, toBaseChange_tmul_generator]

/-- The comparison carries scalar pure tensors to scalars in the extended algebra. -/
@[simp]
theorem baseChangeEquiv_tmul_one (s : S) :
    baseChangeEquiv G S (s ⊗ₜ[R] (1 : SignedSym G)) =
      algebraMap S (SignedSym (G.baseChange S)) s :=
  (baseChangeEquiv G S).commutes s

/-- The inverse comparison is scalar extension of the original generator map. -/
@[simp]
theorem baseChangeEquiv_symm_generator (x : S ⊗[R] V) :
    (baseChangeEquiv G S).symm (generator (G.baseChange S) x) =
      (generator G).baseChange S x := by
  simp [baseChangeEquiv, fromBaseChange_generator]

/-- Applying the comparison after scalar extension of the generator gives the extended
algebra's generator, on arbitrary tensors. -/
@[simp]
theorem baseChangeEquiv_baseChange_generator (x : S ⊗[R] V) :
    baseChangeEquiv G S ((generator G).baseChange S x) = generator (G.baseChange S) x := by
  rw [← baseChangeEquiv_symm_generator]
  exact (baseChangeEquiv G S).apply_symm_apply _

/-- The comparison preserves and reflects each homogeneous input-degree piece. -/
@[simp high]
theorem baseChangeEquiv_mem_signedSymPiece_iff {p : ℤ} (x : S ⊗[R] SignedSym G) :
    baseChangeEquiv G S x ∈ signedSymPiece (G.baseChange S) p ↔
      x ∈ (signedSymPiece G p).baseChange S := by
  have hinj := (baseChangeEquiv G S).injective
  rw [coe_baseChangeEquiv] at hinj ⊢
  exact Graded.map_mem_iff_of_injective (toBaseChange G S) hinj

/-- The inverse comparison preserves and reflects each homogeneous input-degree piece. -/
theorem baseChangeEquiv_symm_mem_baseChange_signedSymPiece_iff {p : ℤ}
    (x : SignedSym (G.baseChange S)) :
    (baseChangeEquiv G S).symm x ∈ (signedSymPiece G p).baseChange S ↔
      x ∈ signedSymPiece (G.baseChange S) p := by
  rw [← baseChangeEquiv_mem_signedSymPiece_iff, AlgEquiv.apply_symm_apply]

/-- The scalar-extension comparison preserves the integer input degree. -/
theorem isHomogeneous_baseChangeEquiv :
    LinearMap.IsHomogeneous (baseChangeEquiv G S).toLinearMap
      (fun p ↦ (signedSymPiece G p).baseChange S) (signedSymPiece (G.baseChange S)) 0 := by
  refine LinearMap.isHomogeneous_def.2 fun p x hx => ?_
  simpa only [add_zero, AlgEquiv.toLinearMap_apply] using
    (baseChangeEquiv_mem_signedSymPiece_iff G S x).2 hx

/-- The inverse scalar-extension comparison also preserves the integer input degree. -/
theorem isHomogeneous_baseChangeEquiv_symm :
    LinearMap.IsHomogeneous (baseChangeEquiv G S).symm.toLinearMap
      (signedSymPiece (G.baseChange S)) (fun p ↦ (signedSymPiece G p).baseChange S) 0 := by
  refine LinearMap.isHomogeneous_def.2 fun p x hx => ?_
  simpa only [add_zero, AlgEquiv.toLinearMap_apply] using
    (baseChangeEquiv_symm_mem_baseChange_signedSymPiece_iff G S x).2 hx

variable {W : Type*} [AddCommGroup W] [Module R W] (H : InternalGrading R W ℤ)

/-- The scalar-extension comparison is natural in degree-preserving linear maps. -/
theorem baseChangeEquiv_naturality (f : V →ₗ[R] W)
    (hf : LinearMap.IsHomogeneous f G.piece H.piece 0) :
    (map (G.baseChange S) (H.baseChange S) (f.baseChange S)
      (hf.baseChange_internalGrading S)).comp (baseChangeEquiv G S).toAlgHom =
        (baseChangeEquiv H S).toAlgHom.comp
          (Algebra.TensorProduct.map (AlgHom.id S S) (map G H f hf)) := by
  apply Algebra.TensorProduct.ext
  · exact Subsingleton.elim _ _
  · apply hom_ext
    intro x
    simp

end TauCeti.SignedSym
