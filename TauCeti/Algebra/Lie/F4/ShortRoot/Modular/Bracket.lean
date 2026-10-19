/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Modular.Exponential
public import TauCeti.Algebra.Lie.F4.ShortRoot.TorusAction
public import TauCeti.Algebra.AlgebraicGroup.ConstantMultiplication.Basic

/-!
# The bracket tensor of the modular F₄ short-root ideal

The characteristic-two short-root ideal is a twenty-six-dimensional Lie algebra. Its bracket
has constant structure matrices in the distinguished weight basis. The numbered root
exponentials and the weight torus preserve this tensor over every commutative coefficient
algebra. These polynomial identities let the generated short-root group act by automorphisms
of the bracket, and constrain its tangent matrices to be derivations.

The root calculation uses `f4ShortRootExponential_toMatrix_mul_adjoint` and
`f4RootExponential_intertwines`; the torus calculation uses the integral weight support of
`f4ShortRootAdjointMatrix`. No reduction of the character lattice modulo two is involved.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §12.
* R. W. Carter, *Simple Groups of Lie Type*, §12.3.
-/

public section

namespace TauCeti.DynkinType

open scoped TensorProduct
open TauCeti.F4ShortRoot

noncomputable section

attribute [local instance high] Algebra.toModule

/-- The matrix of bracketing on the left with the `a`th distinguished short-root ideal vector. -/
def f4ShortRootBracketMatrix (a : Fin 26) : Matrix (Fin 26) (Fin 26) (ZMod 2) :=
  f4ShortRootAdjointMatrix (f4ShortRootLieIdealBasis a : f4ModularChevalleyLieAlgebra)

/-- The bracket structure matrices are the restricted adjoint matrices at the ideal basis. -/
theorem f4ShortRootBracketMatrix_def (a : Fin 26) :
    f4ShortRootBracketMatrix a =
      f4ShortRootAdjointMatrix (f4ShortRootLieIdealBasis a : f4ModularChevalleyLieAlgebra) :=
  (rfl)

/-- A nonzero bracket coefficient adds the integral weights of its inputs. -/
theorem f4ShortRootBracketMatrix_weight_support (a i j : Fin 26)
    (hne : f4ShortRootBracketMatrix a i j ≠ 0) :
    f4ShortRootWeight i = f4ShortRootWeight j + f4ShortRootWeight a := by
  obtain ⟨b, rfl⟩ := f4ShortRootWeightIndexEquiv.symm.surjective a
  rcases b with α | k
  · rw [f4ShortRootBracketMatrix_def,
      coe_f4ShortRootLieIdealBasis_symm_inl α] at hne
    simpa only [f4ShortRootWeight_f4ShortRootWeightIndexEquiv_symm_inl] using
      f4ShortRootAdjointMatrix_root_weight_support α i j hne
  · rw [f4ShortRootBracketMatrix_def,
      coe_f4ShortRootLieIdealBasis_symm_inr k] at hne
    simpa only [f4ShortRootWeight_f4ShortRootWeightIndexEquiv_symm_inr, add_zero] using
      f4ShortRootAdjointMatrix_simpleCoroot_weight_support (f4ShortSimpleIndex k) i j hne

variable {A : Type*} [CommRing A] [Algebra (ZMod 2) A]

/-- The matrix of bracketing with a scalar-extended ideal vector, via the ambient inclusion. -/
private def idealAdjointMatrix :
    A ⊗[ZMod 2] f4ShortRootLieIdeal →ₗ[A] Matrix (Fin 26) (Fin 26) A :=
  (LinearMap.toMatrix (f4ShortRootLieIdealBasis.baseChange A)
    (f4ShortRootLieIdealBasis.baseChange A)).toLinearMap.comp
      (f4ShortRootBaseChangeAdjoint.comp f4ShortRootBaseChangeInclusion)

private theorem idealAdjointMatrix_apply (x : A ⊗[ZMod 2] f4ShortRootLieIdeal) :
    idealAdjointMatrix x =
      LinearMap.toMatrix (f4ShortRootLieIdealBasis.baseChange A)
        (f4ShortRootLieIdealBasis.baseChange A)
        (f4ShortRootBaseChangeAdjoint (f4ShortRootBaseChangeInclusion x)) :=
  (rfl)

private theorem idealAdjointMatrix_basis (a : Fin 26) :
    idealAdjointMatrix ((f4ShortRootLieIdealBasis.baseChange A) a) =
      (f4ShortRootBracketMatrix a).map (algebraMap (ZMod 2) A) := by
  calc
    _ = idealAdjointMatrix ((1 : A) ⊗ₜ[ZMod 2] f4ShortRootLieIdealBasis a) :=
      congrArg idealAdjointMatrix
        (Module.Basis.baseChange_apply A f4ShortRootLieIdealBasis a)
    _ = _ := (idealAdjointMatrix_apply _).trans <|
      (congrArg (fun z => LinearMap.toMatrix (f4ShortRootLieIdealBasis.baseChange A)
        (f4ShortRootLieIdealBasis.baseChange A) (f4ShortRootBaseChangeAdjoint z))
        (f4ShortRootBaseChangeInclusion_tmul (1 : A) (f4ShortRootLieIdealBasis a))).trans
        (f4ShortRootBaseChangeAdjoint_toMatrix_cancel_tmul
          (f4ShortRootLieIdealBasis a : f4ModularChevalleyLieAlgebra))

private theorem imageStructureMatrix_eq_idealAdjointMatrix
    (f : Module.End A (A ⊗[ZMod 2] f4ShortRootLieIdeal)) (a : Fin 26) :
    ConstantMultiplication.imageStructureMatrix (ZMod 2) 26 f4ShortRootBracketMatrix
        (LinearMap.toMatrix (f4ShortRootLieIdealBasis.baseChange A)
          (f4ShortRootLieIdealBasis.baseChange A) f) a =
      idealAdjointMatrix (f ((f4ShortRootLieIdealBasis.baseChange A) a)) := by
  let b := f4ShortRootLieIdealBasis.baseChange A
  calc
    _ = ∑ i, b.repr (f (b a)) i • idealAdjointMatrix (b i) := by
      simp only [b, ConstantMultiplication.imageStructureMatrix_def,
        LinearMap.toMatrix_apply, idealAdjointMatrix_basis]
    _ = idealAdjointMatrix (∑ i, b.repr (f (b a)) i • b i) := by
      simp only [map_sum, map_smul]
    _ = _ := congrArg idealAdjointMatrix (b.sum_repr (f (b a)))

/-- Every numbered root exponential preserves the short-root ideal's bracket tensor after
arbitrary extension of scalars from `𝔽₂`. -/
theorem f4ShortRootBracketMatrix_preserves_rootSubgroupPoints
    (k : Fin 4 ⊕ Fin 4) (u : Multiplicative A) :
    ConstantMultiplication.Preserves (ZMod 2) 26 f4ShortRootBracketMatrix
      ((rootSubgroupPoints k A u : Matrix.GeneralLinearGroup (Fin 26) A) :
        Matrix (Fin 26) (Fin 26) A) := by
  rw [← f4ShortRootExponential_toMatrix_eq_rootSubgroupPoints k u,
    ConstantMultiplication.preserves_def]
  intro a
  let b := f4ShortRootLieIdealBasis.baseChange A
  let e := f4ShortRootExponential k (Multiplicative.toAdd u)
  let M := LinearMap.toMatrix b b e
  calc
    _ = M * idealAdjointMatrix (b a) :=
      congrArg (M * ·) (idealAdjointMatrix_basis a).symm
    _ = idealAdjointMatrix (e (b a)) * M := by
      simpa only [idealAdjointMatrix_apply, f4RootExponential_intertwines] using
        f4ShortRootExponential_toMatrix_mul_adjoint k (Multiplicative.toAdd u)
          (f4ShortRootBaseChangeInclusion (b a))
    _ = _ := congrArg (· * M) (imageStructureMatrix_eq_idealAdjointMatrix e a).symm

/-- Every weight-torus matrix preserves the short-root ideal's bracket tensor over any
commutative `𝔽₂`-algebra. -/
theorem f4ShortRootBracketMatrix_preserves_diagonal_torusCharacter (s : Fin 4 → Aˣ) :
    ConstantMultiplication.Preserves (ZMod 2) 26 f4ShortRootBracketMatrix
      (Matrix.diagonal fun i => (torusCharacter s (f4ShortRootWeight i) : A)) := by
  classical
  rw [ConstantMultiplication.preserves_def]
  intro a
  have himage : ConstantMultiplication.imageStructureMatrix (ZMod 2) 26
      f4ShortRootBracketMatrix
        (Matrix.diagonal fun i => (torusCharacter s (f4ShortRootWeight i) : A)) a =
      (torusCharacter s (f4ShortRootWeight a) : A) •
        (f4ShortRootBracketMatrix a).map (algebraMap (ZMod 2) A) := by
    simp [ConstantMultiplication.imageStructureMatrix_def, Matrix.diagonal_apply]
  rw [himage]
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply, Matrix.map_apply,
    smul_eq_mul]
  by_cases h : f4ShortRootBracketMatrix a i j = 0
  · simp [h]
  · rw [f4ShortRootBracketMatrix_weight_support a i j h, torusCharacter_add, Units.val_mul]
    ring

end

end TauCeti.DynkinType
