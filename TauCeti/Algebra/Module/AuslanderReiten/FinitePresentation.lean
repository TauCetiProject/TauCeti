/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.Transpose
public import TauCeti.LinearAlgebra.Dual.FiniteProjective
public import Mathlib.Algebra.Module.FinitePresentation

/-!
# Finite presentation of the Auslander–Bridger transpose

The transpose of an arrow `P₁ → P₀` between finite projective left `A`-modules is a finitely
presented left `Aᵐᵒᵖ`-module. Thus transposing a finite projective presentation stays within
finitely presented modules even when the ring is not Noetherian. Finite generation of the
transpose needs only finite projectivity of `P₁`.

These instances complement the presentation comparison in
`TauCeti.Algebra.Module.AuslanderReiten.StableTranspose`: the dual summands in that comparison
are finite projective, and the transposes themselves are finitely presented.

## References

* M. Auslander, M. Bridger, *Stable module theory*, Mem. Amer. Math. Soc. 94 (1969), Section 2.1.
-/

public section

namespace TauCeti

namespace AuslanderReitenTranspose

variable {A P₀ P₁ : Type*} [Ring A]
  [AddCommMonoid P₀] [Module A P₀] [AddCommMonoid P₁] [Module A P₁]
  [Module.Finite A P₁] [Module.Projective A P₁]

/-- The transpose is finitely generated when the source of its presenting arrow is
finite projective. -/
instance finite (f : P₁ →ₗ[A] P₀) : Module.Finite Aᵐᵒᵖ (AuslanderReitenTranspose f) :=
  Module.Finite.of_surjective (mk f) (mk_surjective f)

/-- The transpose of an arrow between finite projective modules is finitely presented over the
opposite ring. -/
instance finitePresentation [Module.Finite A P₀] [Module.Projective A P₀]
    (f : P₁ →ₗ[A] P₀) : Module.FinitePresentation Aᵐᵒᵖ (AuslanderReitenTranspose f) := by
  have : Module.FinitePresentation Aᵐᵒᵖ (Module.Dual A P₁) :=
    Module.finitePresentation_of_projective _ _
  apply Module.finitePresentation_of_surjective (mk f) (mk_surjective f)
  rw [ker_mk]
  exact Submodule.fg_range _

end AuslanderReitenTranspose

end TauCeti
