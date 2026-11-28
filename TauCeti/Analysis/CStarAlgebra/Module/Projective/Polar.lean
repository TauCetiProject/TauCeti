/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Module.Frame.Polar
public import TauCeti.Analysis.CStarAlgebra.Module.Projective.Basic

/-!
# Polar decomposition for finitely generated projective Hilbert C⋆-modules

Over a unital C⋆-algebra `A`, this file specializes the frame polar decomposition in
`TauCeti.Analysis.CStarAlgebra.Module.Frame.Polar` to complete finitely generated projective right
Hilbert `A`-modules:

* For a complete finitely generated projective right Hilbert `A`-module `E` and any complete
  right Hilbert `A`-module `F`, every right `A`-linear equivalence `T : E ≃ₗ[Aᵐᵒᵖ] F` admits a
  polar decomposition `T = U ∘ |T|` with unitary `U : E ≃ₗᵢ[Aᵐᵒᵖ] F`
  (`LinearEquiv.exists_polar_linearIsometryEquiv_of_finite_projective`).
* In particular, `E` and `F` are unitarily isomorphic if and only if they are algebraically
  isomorphic as right `A`-modules
  (`TauCeti.CStarModule.nonempty_linearIsometryEquiv_iff_nonempty_linearEquiv`).

## Main declarations

* `LinearEquiv.exists_polar_linearIsometryEquiv_of_finite_projective`
* `TauCeti.CStarModule.nonempty_linearIsometryEquiv_iff_nonempty_linearEquiv`

## References

* M. Frank and D. R. Larson, *Frames in Hilbert C⋆-modules and C⋆-algebras*, J. Operator Theory 48
  (2002), 273–314.
* E. C. Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapters 3 and 6.
* I. Raeburn and D. P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*, Chapter 2.
-/

public section

open MulOpposite CStarModule
open TauCeti.CStarModule

section FiniteProjectivePolar

variable {A E F : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [SeminormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] [Module Aᵐᵒᵖ E]
  [CStarModule Aᵐᵒᵖ E] [Module.Finite Aᵐᵒᵖ E] [Module.Projective Aᵐᵒᵖ E]
  [SeminormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] [Module Aᵐᵒᵖ F]
  [CStarModule Aᵐᵒᵖ F]

/-- For a complete finitely generated projective right Hilbert `A`-module `E` and any complete
right Hilbert `A`-module `F`, every right `A`-linear equivalence `T : E ≃ₗ[Aᵐᵒᵖ] F` admits a
polar decomposition `T = U ∘ |T|` into a self-adjoint positive module automorphism
`|T| : E ≃ₗ[Aᵐᵒᵖ] E` and a unitary isomorphism `U : E ≃ₗᵢ[Aᵐᵒᵖ] F`. -/
theorem LinearEquiv.exists_polar_linearIsometryEquiv_of_finite_projective (T : E ≃ₗ[Aᵐᵒᵖ] F) :
    ∃ (U : E ≃ₗᵢ[Aᵐᵒᵖ] F) (P : E ≃ₗ[Aᵐᵒᵖ] E), LinearMap.IsAdjointPair
      (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip P P ∧
      (∀ z : E, 0 ≤ inner Aᵐᵒᵖ z (P z)) ∧ (∀ z : E, U (P z) = T z) := by
  obtain ⟨_, _, hx⟩ := exists_isParsevalFrame_iff_finite_projective.mpr ⟨‹_›, ‹_›⟩
  exact ⟨hx.polarUnitary T, hx.polarModulus T, hx.isAdjointPair_polarModulus T,
    hx.inner_polarModulus_right_nonneg T, hx.polarUnitary_polarModulus_apply T⟩

/-- A complete finitely generated projective right Hilbert `A`-module `E` and any complete right
Hilbert `A`-module `F` are unitarily isomorphic (`E ≃ₗᵢ[Aᵐᵒᵖ] F`) if and only if they are
algebraically isomorphic as right `A`-modules (`E ≃ₗ[Aᵐᵒᵖ] F`). In particular, the complete
Hilbert `A`-module structure on any finitely generated projective right `A`-module is unique up to
unitary isomorphism. -/
theorem TauCeti.CStarModule.nonempty_linearIsometryEquiv_iff_nonempty_linearEquiv :
    Nonempty (E ≃ₗᵢ[Aᵐᵒᵖ] F) ↔ Nonempty (E ≃ₗ[Aᵐᵒᵖ] F) :=
  ⟨fun ⟨U⟩ ↦ ⟨U.toLinearEquiv⟩, fun ⟨T⟩ ↦
    ⟨T.exists_polar_linearIsometryEquiv_of_finite_projective.choose⟩⟩

end FiniteProjectivePolar
