/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.DoubleTranspose
public import TauCeti.Algebra.Module.AuslanderReiten.Transpose
import all TauCeti.Algebra.Module.AuslanderReiten.Transpose

/-!
# Transposing the dual presentation

For a presenting map `f : P₁ → P₀` between finitely generated projective left `A`-modules,
the dual map `f* : Hom_A(P₀,A) → Hom_A(P₁,A)` presents its transpose over `Aᵐᵒᵖ`.
Transposing this dual map gives the original cokernel. For an exact presentation
`P₁ → P₀ → M → 0`, it therefore returns `M`.

The second transpose is naturally a module over `Aᵐᵒᵖᵐᵒᵖ`. The equivalences below are
semilinear along the canonical ring equivalence from this double opposite to `A`, so the
statement applies to noncommutative rings without changing the transpose's module instances.
This is the object calculation used to make the transpose an involution modulo projectives.

## References

* M. Auslander, M. Bridger, *Stable module theory*, Mem. Amer. Math. Soc. 94 (1969), Section 2.1.
-/

public section

namespace TauCeti

attribute [local instance] RingHomInvPair.of_ringEquiv

variable (A : Type*) [Ring A]
variable {P₀ P₁ M : Type*} [AddCommGroup P₀] [Module A P₀]
  [AddCommGroup P₁] [Module A P₁] [AddCommGroup M] [Module A M]
variable [Module.Finite A P₀] [Module.Projective A P₀]
  [Module.Finite A P₁] [Module.Projective A P₁]

/-- Transposing the dual of a finite-projective presenting map recovers its cokernel,
with the double opposite identified with the original ring. -/
noncomputable def doubleTransposeCokernelEquiv (f : P₁ →ₗ[A] P₀) :
    AuslanderReitenTranspose (f.lcomp Aᵐᵒᵖ A) ≃ₛₗ[RingHomClass.toRingHom (RingEquiv.opOp A).symm]
      P₀ ⧸ LinearMap.range f := by
  -- The transpose hides its quotient body across module boundaries. Unfold it here to
  -- apply the generic quotient equivalence; consumers use the representative lemmas below.
  with_unfolding_all
    exact (Submodule.Quotient.equiv _ _ (opDualCodomainEquiv A (Module.Dual A P₀))
      (map_range_opDualCodomainEquiv A (f.lcomp Aᵐᵒᵖ A))).symm.trans
        (doubleDualCokernelEquiv A f)

/-- The second transpose sends a functional representative to the vector it represents under
inverse evaluation, after removing the opposite from its values. -/
@[simp]
theorem doubleTransposeCokernelEquiv_mk (f : P₁ →ₗ[A] P₀)
    (F : Module.Dual Aᵐᵒᵖ (Module.Dual A P₀)) :
    doubleTransposeCokernelEquiv A f (AuslanderReitenTranspose.mk (f.lcomp Aᵐᵒᵖ A) F) =
      Submodule.Quotient.mk
        ((opDualEvalEquiv A P₀).symm ((opDualCodomainEquiv A (Module.Dual A P₀)).symm F)) := by
  -- Expand quotient transport on a representative, then use the public biduality formula.
  with_unfolding_all
    change doubleDualCokernelEquiv A f
      (Submodule.Quotient.mk ((opDualCodomainEquiv A (Module.Dual A P₀)).symm F)) = _
    exact doubleDualCokernelEquiv_mk A f _

/-- Inverse second-transpose transport sends a vector to its opposite-valued evaluation
functional. -/
@[simp]
theorem doubleTransposeCokernelEquiv_symm_mk (f : P₁ →ₗ[A] P₀) (x : P₀) :
    (doubleTransposeCokernelEquiv A f).symm (Submodule.Quotient.mk x) =
      AuslanderReitenTranspose.mk (f.lcomp Aᵐᵒᵖ A)
        (opDualCodomainEquiv A (Module.Dual A P₀) (opDualEval A P₀ x)) := by
  -- Inverting the composition first applies biduality, then transports the quotient.
  with_unfolding_all
    change (Submodule.Quotient.equiv _ _ (opDualCodomainEquiv A (Module.Dual A P₀))
      (map_range_opDualCodomainEquiv A (f.lcomp Aᵐᵒᵖ A)))
      ((doubleDualCokernelEquiv A f).symm (Submodule.Quotient.mk x)) = _
    rw [doubleDualCokernelEquiv_symm_mk]
    rfl

/-- **Transposing the dual presentation returns the presented module.** No minimality or
finite-length assumption is required; the two presenting modules must be finite projective. -/
noncomputable def doubleTransposePresentationEquiv (f : P₁ →ₗ[A] P₀) (g : P₀ →ₗ[A] M)
    (hexact : Function.Exact f g) (hsurj : Function.Surjective g) :
    AuslanderReitenTranspose (f.lcomp Aᵐᵒᵖ A)
      ≃ₛₗ[RingHomClass.toRingHom (RingEquiv.opOp A).symm] M :=
  (doubleTransposeCokernelEquiv A f).trans
    ((Submodule.quotEquivOfEq _ _ (LinearMap.exact_iff.mp hexact).symm).trans
      (g.quotKerEquivOfSurjective hsurj))

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
  -- On a representative, the cokernel-to-module equivalence applies `g`.
  change (g.quotKerEquivOfSurjective hsurj)
    ((Submodule.quotEquivOfEq _ _ (LinearMap.exact_iff.mp hexact).symm)
      (doubleTransposeCokernelEquiv A f
        (AuslanderReitenTranspose.mk (f.lcomp Aᵐᵒᵖ A) F))) = _
  rw [doubleTransposeCokernelEquiv_mk]
  simp

/-- Inverse presentation transport sends the image of a presenting vector to its
opposite-valued evaluation functional. -/
@[simp]
theorem doubleTransposePresentationEquiv_symm_apply (f : P₁ →ₗ[A] P₀) (g : P₀ →ₗ[A] M)
    (hexact : Function.Exact f g) (hsurj : Function.Surjective g) (x : P₀) :
    (doubleTransposePresentationEquiv A f g hexact hsurj).symm (g x) =
      AuslanderReitenTranspose.mk (f.lcomp Aᵐᵒᵖ A)
        (opDualCodomainEquiv A (Module.Dual A P₀) (opDualEval A P₀ x)) := by
  apply (doubleTransposePresentationEquiv A f g hexact hsurj).injective
  rw [(doubleTransposePresentationEquiv A f g hexact hsurj).apply_symm_apply,
    doubleTransposePresentationEquiv_mk,
    (opDualCodomainEquiv A (Module.Dual A P₀)).symm_apply_apply,
    ← opDualEvalEquiv_toLinearMap]
  exact congrArg g ((opDualEvalEquiv A P₀).symm_apply_apply x).symm

end TauCeti
