/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Projective.FinitePresentation
public import TauCeti.LinearAlgebra.Dual.FiniteProjective
public import TauCeti.LinearAlgebra.Dual.Opposite
public import Mathlib.Algebra.Exact.Basic

/-!
# Dual right presentations

Dualizing a finite projective right presentation with values in the regular module `A`
gives a finite projective left presentation of its cokernel. The cokernel is finitely
presented over an arbitrary ring.

The `A`-valued dual makes the inverse Auslander–Bridger transpose an actual left `A`-module,
without transporting a module over the double opposite. `rightTransposePresentation` retains
the presenting projectives and maps so that the canonical recovery is available to the stable
equivalence.

## References

* M. Auslander, M. Bridger, *Stable module theory*, Section 2.1.
-/

public section

namespace TauCeti

universe u v

variable {A : Type u} [Ring A]

namespace FiniteProjectivePresentation

variable {N : ModuleCat.{v} Aᵐᵒᵖ}

/-- The transpose of a right presentation, with duals valued in `A` so that the result is
an actual left `A`-module rather than a module over the double opposite. -/
noncomputable abbrev rightTranspose (Q : FiniteProjectivePresentation N) : ModuleCat.{max u v} A :=
  ModuleCat.of A ((Q.P₁ →ₗ[Aᵐᵒᵖ] A) ⧸ LinearMap.range (Q.p.lcomp A A))

/-- The finite projective presentation of a right transpose obtained by dualizing its
right presentation. The abbreviation keeps the dual modules and their maps definitionally
identifiable for double-transpose recovery. -/
noncomputable abbrev rightTransposePresentation (Q : FiniteProjectivePresentation N) :
    FiniteProjectivePresentation Q.rightTranspose := by
  let : Module.Finite A (Q.P₀ →ₗ[Aᵐᵒᵖ] A) :=
    Module.Finite.of_surjective (opDualCodomainEquiv A Q.P₀).symm.toLinearMap
      (opDualCodomainEquiv A Q.P₀).symm.surjective
  let : Module.Finite A (Q.P₁ →ₗ[Aᵐᵒᵖ] A) :=
    Module.Finite.of_surjective (opDualCodomainEquiv A Q.P₁).symm.toLinearMap
      (opDualCodomainEquiv A Q.P₁).symm.surjective
  let : Module.Projective A (Q.P₀ →ₗ[Aᵐᵒᵖ] A) :=
    Module.Projective.of_equiv (opDualCodomainEquiv A Q.P₀).symm
  let : Module.Projective A (Q.P₁ →ₗ[Aᵐᵒᵖ] A) :=
    Module.Projective.of_equiv (opDualCodomainEquiv A Q.P₁).symm
  exact
    { P₀ := ModuleCat.of A (Q.P₁ →ₗ[Aᵐᵒᵖ] A)
      P₁ := ModuleCat.of A (Q.P₀ →ₗ[Aᵐᵒᵖ] A)
      p := Q.p.lcomp A A
      π := (LinearMap.range (Q.p.lcomp A A)).mkQ
      exact := LinearMap.exact_map_mkQ_range _
      surjective := Submodule.mkQ_surjective _ }

/-- A right transpose is finitely presented over an arbitrary ring. -/
instance (Q : FiniteProjectivePresentation N) : Module.FinitePresentation A Q.rightTranspose := by
  let P := Q.rightTransposePresentation
  let := P.finite₀
  let := P.finite₁
  let := P.projective₀
  let : Module.FinitePresentation A P.P₀ := Module.finitePresentation_of_projective _ _
  exact Module.finitePresentation_of_surjective P.π P.surjective
    (P.exact.linearMap_ker_eq.symm ▸ Submodule.fg_range P.p)

end FiniteProjectivePresentation

end TauCeti
