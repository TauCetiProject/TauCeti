/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Finiteness.Projective
public import TauCeti.Analysis.CStarAlgebra.Module.Frame.Retract

/-!
# Finitely generated projective Hilbert C⋆-modules

Over a unital C⋆-algebra `A`, this file establishes the frame characterization of finitely generated
projective Hilbert modules (Frank–Larson; Roe, Prop. 10.2) and its basic structural consequences:

* **Frame characterization of finitely generated projective Hilbert modules (Frank–Larson; Roe,
  Prop. 10.2)** (`TauCeti.CStarModule.exists_isParsevalFrame_iff_finite_projective`): a complete
  right Hilbert `A`-module `E` admits a finite Parseval frame if and only if `E` is finitely
  generated and projective as an algebraic right `A`-module. Completeness of `E` is essential for
  the reverse implication: on `C([0, 1], ℂ)` with `⟨a, b⟩(t) = t · star (a t) * b t`, the module is
  free of rank `1` over itself yet incomplete and admits no finite Parseval frame.
* Every algebraic finitely generated projective right `A`-module admits a complete Hilbert
  `A`-module structure
  (`TauCeti.CStarModule.exists_completeSpace_cstarModule_of_finite_projective`).
* Every right `A`-linear map out of a complete finitely generated projective right Hilbert
  `A`-module is automatically adjointable (`LinearMap.exists_isAdjointPair_of_finite_projective`).

## Main declarations

* `TauCeti.CStarModule.exists_isParsevalFrame_iff_finite_projective`
* `TauCeti.CStarModule.exists_completeSpace_cstarModule_of_finite_projective`
* `LinearMap.exists_isAdjointPair_of_finite_projective`

## References

* M. Frank and D. R. Larson, *Frames in Hilbert C⋆-modules and C⋆-algebras*, J. Operator Theory 48
  (2002), 273–314.
* E. C. Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapters 1–4.
* I. Raeburn and D. P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*, Chapter 2.
* J. Roe, *Lectures on K-Theory and Operator Algebras*, Proposition 10.2.
-/

public section

open MulOpposite CStarModule
open scoped WithCStarModule

namespace TauCeti.CStarModule

/-- **Frame characterization of finitely generated projective Hilbert modules** (Frank–Larson; Roe,
Proposition 10.2): over a unital C⋆-algebra `A`, a complete right Hilbert `A`-module `E` admits a
finite Parseval frame if and only if `E` is finitely generated and projective as a right `A`-module.
-/
theorem exists_isParsevalFrame_iff_finite_projective {A E : Type*}
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [SeminormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] [Module Aᵐᵒᵖ E]
    [CStarModule Aᵐᵒᵖ E] : (∃ (n : ℕ) (x : Fin n → E), IsParsevalFrame Aᵐᵒᵖ x) ↔
      Module.Finite Aᵐᵒᵖ E ∧ Module.Projective Aᵐᵒᵖ E := by
  refine ⟨fun ⟨_, _, hx⟩ ↦ ⟨Module.Finite.of_isParsevalFrame hx,
    Module.Projective.of_isParsevalFrame hx⟩, fun ⟨_, _⟩ ↦ ?_⟩
  obtain ⟨n, f₀, g₀, _, _, hfg₀⟩ := Module.Finite.exists_comp_eq_id_of_projective Aᵐᵒᵖ E
  let e := TauCeti.WithCStarModule.piOpLinearEquiv A (Fin n)
  obtain ⟨x, hx⟩ := (f₀ ∘ₗ e.toLinearMap).exists_isParsevalFrame_of_comp_eq_id
    (e.symm.toLinearMap ∘ₗ g₀)
    (by ext z; simpa [LinearMap.comp_apply] using LinearMap.congr_fun hfg₀ z)
  exact ⟨n, x, hx⟩

/-- Every algebraic finitely generated projective right `A`-module `M` (with compatible complex
scalar multiplication, for example via `Module.compHom M (algebraMap ℂ Aᵐᵒᵖ)`) admits a norm and a
`CStarModule Aᵐᵒᵖ M` structure whose induced `NormedAddCommGroup`
(`CStarModule.normedAddCommGroup Aᵐᵒᵖ`) is complete. -/
theorem exists_completeSpace_cstarModule_of_finite_projective (A M : Type*)
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [AddCommGroup M] [Module ℂ M] [Module Aᵐᵒᵖ M] [IsScalarTower ℂ Aᵐᵒᵖ M]
    [Module.Finite Aᵐᵒᵖ M] [Module.Projective Aᵐᵒᵖ M] : ∃ (_ : Norm M) (_ : CStarModule Aᵐᵒᵖ M),
      letI := CStarModule.normedAddCommGroup Aᵐᵒᵖ (E := M)
      CompleteSpace M := by
  obtain ⟨n, f₀, g₀, _, hg₀_inj, hfg₀⟩ := Module.Finite.exists_comp_eq_id_of_projective Aᵐᵒᵖ M
  have : IsScalarTower ℂ Aᵐᵒᵖ C⋆ᵐᵒᵈ(Aᵐᵒᵖ, Fin n → A) := CStarModule.isScalarTower _ _
  let e_pi := TauCeti.WithCStarModule.piOpLinearEquiv A (Fin n)
  let f : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, Fin n → A) →ₗ[Aᵐᵒᵖ] M := f₀ ∘ₗ e_pi.toLinearMap
  let g : M →ₗ[Aᵐᵒᵖ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, Fin n → A) := e_pi.symm.toLinearMap ∘ₗ g₀
  have hfg_apply : Function.LeftInverse f g := fun m ↦ by
    simpa [f, g, LinearMap.comp_apply] using LinearMap.congr_fun hfg₀ m
  let : Norm M := ⟨fun m ↦ ‖g m‖⟩
  let : CStarModule Aᵐᵒᵖ M := induced (g.restrictScalars ℂ)
    (e_pi.symm.injective.comp hg₀_inj) g.map_smul fun _ ↦ rfl
  let : NormedAddCommGroup M := CStarModule.normedAddCommGroup Aᵐᵒᵖ
  let : NormedSpace ℂ M := .ofCore (CStarModule.normedSpaceCore Aᵐᵒᵖ)
  let : IsBoundedSMul Aᵐᵒᵖ M := IsBoundedSMul.of_norm_smul_le CStarModule.norm_smul_le
  have hisom : Isometry g := AddMonoidHomClass.isometry_of_norm (g.restrictScalars ℂ) fun _ ↦ rfl
  exact ⟨‹_›, ‹_›, hisom.isUniformInducing.completeSpace
    (hfg_apply.isClosed_range f.continuous_of_finite_pi_cstarModule hisom.continuous).isComplete⟩

end TauCeti.CStarModule

section FiniteProjectiveMaps

open TauCeti.CStarModule

variable {A E F : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [SeminormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] [Module Aᵐᵒᵖ E]
  [CStarModule Aᵐᵒᵖ E] [Module.Finite Aᵐᵒᵖ E] [Module.Projective Aᵐᵒᵖ E]

/-- Every right `A`-linear map out of a complete finitely generated projective right Hilbert
`A`-module into any right C⋆-module over `A` is automatically adjointable. -/
theorem LinearMap.exists_isAdjointPair_of_finite_projective
    [AddCommGroup F] [Module ℂ F] [Module Aᵐᵒᵖ F] [Norm F] [CStarModule Aᵐᵒᵖ F]
    (T : E →ₗ[Aᵐᵒᵖ] F) :
    ∃ S : F →ₗ[Aᵐᵒᵖ] E, LinearMap.IsAdjointPair (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip
      (innerₛₗ (A := Aᵐᵒᵖ) (E := F)).flip T S := by
  obtain ⟨_, x, hx⟩ := exists_isParsevalFrame_iff_finite_projective.mpr ⟨‹_›, ‹_›⟩
  exact ⟨frameAdjoint Aᵐᵒᵖ x T, hx.isAdjointPair_frameAdjoint T⟩

end FiniteProjectiveMaps
