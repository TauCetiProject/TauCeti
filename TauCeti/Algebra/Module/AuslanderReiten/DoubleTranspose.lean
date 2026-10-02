/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Dual.Opposite
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Isomorphisms

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

The second dual has codomain `A` with its right action, rather than `Aᵐᵒᵖ`. This keeps both
regular modules on the same underlying additive group and the final maps left `A`-linear.

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
    ((Submodule.quotEquivOfEq _ _ (LinearMap.exact_iff.mp hexact).symm).trans
      (g.quotKerEquivOfSurjective hsurj))

/-- Double dualization recovers the image of a vector under the presentation's quotient map. -/
@[simp]
theorem doubleDualPresentationEquiv_mk (f : P₁ →ₗ[A] P₀) (g : P₀ →ₗ[A] M)
    (hexact : Function.Exact f g) (hsurj : Function.Surjective g)
    (F : Module.Dual A P₀ →ₗ[Aᵐᵒᵖ] A) :
    doubleDualPresentationEquiv A f g hexact hsurj (Submodule.Quotient.mk F) =
      g ((opDualEvalEquiv A P₀).symm F) := by
  simp [doubleDualPresentationEquiv]

end TauCeti
