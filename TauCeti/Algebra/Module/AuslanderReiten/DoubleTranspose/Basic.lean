/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Dual.Opposite
public import TauCeti.Algebra.Module.AuslanderReiten.Transpose
public import Mathlib.Algebra.Exact.Basic

/-!
# Double dualization of a projective presentation

For a map `f : P₁ → P₀` between finitely generated projective left modules over a ring `A`,
dualization gives a right-linear map `f* : Hom_A(P₀, A) → Hom_A(P₁, A)`. Dualizing again,
with values in the right regular module `A`, gives `f**`. Evaluation identifies its cokernel
with the cokernel of `f`. Thus, for a projective presentation `P₁ → P₀ → M → 0`, the
cokernel after two dualizations is canonically `M`.

This is the involutivity calculation behind the Auslander--Bridger transpose: using the
dual presentation to transpose `Tr M` returns `M`. Comparison with another projective
presentation then gives involutivity up to projective summands. Here we expose the canonical
calculation on the presenting maps; no minimality or finite-length hypothesis is needed.

The double-dual equivalences use codomain `A` with its right action and are left `A`-linear.
The double-transpose equivalences use the transpose's actual codomain `Aᵐᵒᵖ` and are
semilinear along the canonical ring equivalence `Aᵐᵒᵖᵐᵒᵖ ≃+* A`. Thus they apply to
noncommutative rings without changing the transpose's module instances.

## References

* M. Auslander, M. Bridger, *Stable module theory*, Mem. Amer. Math. Soc. 94 (1969), Section 2.1.
-/

public section

namespace TauCeti

variable (A : Type*) [Ring A]
variable {P₀ P₁ M : Type*} [AddCommGroup P₀] [Module A P₀]
  [AddCommGroup P₁] [Module A P₁] [AddCommGroup M] [Module A M]
variable [Module.Finite A P₀] [Module.Projective A P₀]
  [Module.Finite A P₁] [Module.Projective A P₁]

/-- The cokernel of the twice-dualized presenting map is canonically the original cokernel. -/
noncomputable def doubleDualCokernelEquiv (f : P₁ →ₗ[A] P₀) :
    ((Module.Dual A P₀ →ₗ[Aᵐᵒᵖ] A) ⧸
      LinearMap.range ((f.lcomp Aᵐᵒᵖ A).lcomp A A)) ≃ₗ[A]
        P₀ ⧸ LinearMap.range f :=
  (Submodule.Quotient.equiv _ _ (opDualEvalEquiv A P₀)
    (by simpa using map_range_opDualEval A f)).symm

/-- On a representative, double-dual cokernel transport applies inverse evaluation. -/
@[simp]
theorem doubleDualCokernelEquiv_mk (f : P₁ →ₗ[A] P₀)
    (F : Module.Dual A P₀ →ₗ[Aᵐᵒᵖ] A) :
    doubleDualCokernelEquiv A f (Submodule.Quotient.mk F) =
      Submodule.Quotient.mk ((opDualEvalEquiv A P₀).symm F) := (rfl)

/-- The inverse cokernel transport applies evaluation to a representative. -/
@[simp]
theorem doubleDualCokernelEquiv_symm_mk (f : P₁ →ₗ[A] P₀) (x : P₀) :
    (doubleDualCokernelEquiv A f).symm (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (opDualEval A P₀ x) := by
  simp [doubleDualCokernelEquiv, ← opDualEvalEquiv_toLinearMap]

/-- **Double dualization returns the presented module.** For an exact projective presentation
`P₁ → P₀ → M → 0` with finitely generated projectives, the cokernel of the twice-dualized
first map is canonically isomorphic to `M`. -/
noncomputable def doubleDualPresentationEquiv (f : P₁ →ₗ[A] P₀) (g : P₀ →ₗ[A] M)
    (hexact : Function.Exact f g) (hsurj : Function.Surjective g) :
    ((Module.Dual A P₀ →ₗ[Aᵐᵒᵖ] A) ⧸
      LinearMap.range ((f.lcomp Aᵐᵒᵖ A).lcomp A A)) ≃ₗ[A] M :=
  (doubleDualCokernelEquiv A f).trans
    (hexact.linearEquivOfSurjective hsurj)

/-- Double dualization recovers the image of a vector under the presentation's quotient map. -/
@[simp]
theorem doubleDualPresentationEquiv_mk (f : P₁ →ₗ[A] P₀) (g : P₀ →ₗ[A] M)
    (hexact : Function.Exact f g) (hsurj : Function.Surjective g)
    (F : Module.Dual A P₀ →ₗ[Aᵐᵒᵖ] A) :
    doubleDualPresentationEquiv A f g hexact hsurj (Submodule.Quotient.mk F) =
      g ((opDualEvalEquiv A P₀).symm F) := by
  rw [doubleDualPresentationEquiv, LinearEquiv.trans_apply, doubleDualCokernelEquiv_mk,
    ← Function.Exact.linearEquivOfSurjective_symm_apply hexact hsurj,
    LinearEquiv.apply_symm_apply]

/-- Inverse double-dual presentation transport sends the image of a presenting vector to its
evaluation functional. -/
@[simp]
theorem doubleDualPresentationEquiv_symm_apply (f : P₁ →ₗ[A] P₀) (g : P₀ →ₗ[A] M)
    (hexact : Function.Exact f g) (hsurj : Function.Surjective g) (x : P₀) :
    (doubleDualPresentationEquiv A f g hexact hsurj).symm (g x) =
      Submodule.Quotient.mk (opDualEval A P₀ x) := by
  rw [doubleDualPresentationEquiv, LinearEquiv.symm_trans_apply,
    Function.Exact.linearEquivOfSurjective_symm_apply, doubleDualCokernelEquiv_symm_mk]

/-- Transposing the dual of a finite-projective presenting map recovers its cokernel,
with the double opposite identified with the original ring. -/
noncomputable def doubleTransposeCokernelEquiv (f : P₁ →ₗ[A] P₀) :
    AuslanderReitenTranspose (f.lcomp Aᵐᵒᵖ A) ≃ₛₗ[RingHomClass.toRingHom (RingEquiv.opOp A).symm]
      P₀ ⧸ LinearMap.range f :=
  (AuslanderReitenTranspose.quotientEquiv (f.lcomp Aᵐᵒᵖ A) _
    (opDualCodomainEquiv A (Module.Dual A P₀)).symm
    ((Submodule.map_symm_eq_iff (opDualCodomainEquiv A (Module.Dual A P₀))).mpr
      (map_range_opDualCodomainEquiv A (f.lcomp Aᵐᵒᵖ A)))).trans
    (doubleDualCokernelEquiv A f)

/-- The second transpose sends a functional representative to the vector it represents under
inverse evaluation, after removing the opposite from its values. -/
@[simp]
theorem doubleTransposeCokernelEquiv_mk (f : P₁ →ₗ[A] P₀)
    (F : Module.Dual Aᵐᵒᵖ (Module.Dual A P₀)) :
    doubleTransposeCokernelEquiv A f (AuslanderReitenTranspose.mk (f.lcomp Aᵐᵒᵖ A) F) =
      Submodule.Quotient.mk
        ((opDualEvalEquiv A P₀).symm ((opDualCodomainEquiv A (Module.Dual A P₀)).symm F)) := by
  simp [doubleTransposeCokernelEquiv]

/-- Inverse second-transpose transport sends a vector to its opposite-valued evaluation
functional. -/
@[simp]
theorem doubleTransposeCokernelEquiv_symm_mk (f : P₁ →ₗ[A] P₀) (x : P₀) :
    (doubleTransposeCokernelEquiv A f).symm (Submodule.Quotient.mk x) =
      AuslanderReitenTranspose.mk (f.lcomp Aᵐᵒᵖ A)
        (opDualCodomainEquiv A (Module.Dual A P₀) (opDualEval A P₀ x)) := by
  simp [doubleTransposeCokernelEquiv]

/-- **Transposing the dual presentation returns the presented module.** No minimality or
finite-length assumption is required; the two presenting modules must be finite projective. -/
noncomputable def doubleTransposePresentationEquiv (f : P₁ →ₗ[A] P₀) (g : P₀ →ₗ[A] M)
    (hexact : Function.Exact f g) (hsurj : Function.Surjective g) :
    AuslanderReitenTranspose (f.lcomp Aᵐᵒᵖ A)
      ≃ₛₗ[RingHomClass.toRingHom (RingEquiv.opOp A).symm] M :=
  (doubleTransposeCokernelEquiv A f).trans
    (hexact.linearEquivOfSurjective hsurj)

/-- On representatives the recovered presentation applies the original quotient map to
the vector represented by the opposite-valued functional. -/
@[simp]
theorem doubleTransposePresentationEquiv_mk (f : P₁ →ₗ[A] P₀) (g : P₀ →ₗ[A] M)
    (hexact : Function.Exact f g) (hsurj : Function.Surjective g)
    (F : Module.Dual Aᵐᵒᵖ (Module.Dual A P₀)) :
    doubleTransposePresentationEquiv A f g hexact hsurj
        (AuslanderReitenTranspose.mk (f.lcomp Aᵐᵒᵖ A) F) =
      g ((opDualEvalEquiv A P₀).symm
        ((opDualCodomainEquiv A (Module.Dual A P₀)).symm F)) := by
  rw [doubleTransposePresentationEquiv, LinearEquiv.trans_apply,
    doubleTransposeCokernelEquiv_mk,
    ← Function.Exact.linearEquivOfSurjective_symm_apply hexact hsurj,
    LinearEquiv.apply_symm_apply]

/-- Inverse presentation transport sends the image of a presenting vector to its
opposite-valued evaluation functional. -/
@[simp]
theorem doubleTransposePresentationEquiv_symm_apply (f : P₁ →ₗ[A] P₀) (g : P₀ →ₗ[A] M)
    (hexact : Function.Exact f g) (hsurj : Function.Surjective g) (x : P₀) :
    (doubleTransposePresentationEquiv A f g hexact hsurj).symm (g x) =
      AuslanderReitenTranspose.mk (f.lcomp Aᵐᵒᵖ A)
        (opDualCodomainEquiv A (Module.Dual A P₀) (opDualEval A P₀ x)) := by
  rw [doubleTransposePresentationEquiv, LinearEquiv.symm_trans_apply,
    Function.Exact.linearEquivOfSurjective_symm_apply, doubleTransposeCokernelEquiv_symm_mk]

end TauCeti
