/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Finiteness.Projective
public import TauCeti.Analysis.CStarAlgebra.Module.Frame

/-!
# Finitely generated projective Hilbert C⋆-modules

Over a unital C⋆-algebra `A`, this file establishes the frame characterization of finitely generated
projective Hilbert modules (Frank–Larson; Roe, Prop. 10.2) and its structural consequences:

* **Frame characterization of finitely generated projective Hilbert modules (Frank–Larson; Roe,
  Prop. 10.2)** (`CStarModule.exists_isParsevalFrame_iff_finite_projective`): a complete right
  Hilbert `A`-module `E` admits a finite Parseval frame if and only if `E` is finitely generated and
  projective as an algebraic right `A`-module. Completeness of `E` is essential for the reverse
  implication: on `C([0, 1], ℂ)` with `⟨a, b⟩(t) = t · star (a t) * b t`, the module is free of rank
  `1` over itself yet incomplete and admits no finite Parseval frame.
* Every algebraic finitely generated projective right `A`-module admits a complete Hilbert
  `A`-module structure (`CStarModule.exists_completeSpace_cstarModule_of_finite_projective`).
* Every right `A`-linear map out of a complete finitely generated projective right Hilbert
  `A`-module is automatically adjointable (`CStarModule.exists_isAdjointPair_of_finite_projective`).
* Every right `A`-linear equivalence `T : E ≃ₗ[Aᵐᵒᵖ] F` between complete finitely generated
  projective right Hilbert `A`-modules admits a polar decomposition `T = U ∘ |T|` with unitary
  `U : E ≃ₗᵢ[Aᵐᵒᵖ] F` (`CStarModule.exists_polar_linearIsometryEquiv_of_finite_projective`). In
  particular, two complete finitely generated projective right Hilbert `A`-modules are unitarily
  isomorphic if and only if they are algebraically isomorphic as right `A`-modules
  (`CStarModule.nonempty_linearIsometryEquiv_iff_nonempty_linearEquiv`).

## Main declarations

* `CStarModule.IsParsevalFrame.finite`, `CStarModule.IsParsevalFrame.projective`
* `CStarModule.exists_isParsevalFrame_iff_finite_projective`
* `CStarModule.exists_completeSpace_cstarModule_of_finite_projective`
* `CStarModule.exists_isAdjointPair_of_finite_projective`
* `CStarModule.exists_polar_linearIsometryEquiv_of_finite_projective`,
  `CStarModule.nonempty_linearIsometryEquiv_iff_nonempty_linearEquiv`

## References

* M. Frank and D. R. Larson, *Frames in Hilbert C⋆-modules and C⋆-algebras*, J. Operator Theory 48
  (2002), 273–314.
* E. C. Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapters 1–4 and 6.
* I. Raeburn and D. P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*, Chapter 2.
* J. Roe, *Lectures on K-Theory and Operator Algebras*, Proposition 10.2.
-/

public section

open MulOpposite CStarModule
open scoped WithCStarModule

namespace CStarModule

section Algebraic

/-- Any `A`-module admitting a finite Parseval frame is finitely generated over `A`; neither
completeness nor norms are needed. -/
theorem IsParsevalFrame.finite {A ι E : Type*} [Fintype ι] [Semiring A] [Inner A E]
    [AddCommMonoid E] [Module A E] {x : ι → E} (hx : IsParsevalFrame A x) :
    Module.Finite A E :=
  Module.Finite.of_surjective (∑ i : ι, (LinearMap.proj i).smulRight (x i)) fun z ↦
    ⟨fun i ↦ inner A (x i) z, by simpa [LinearMap.sum_apply] using hx.sum_inner_smul z⟩

/-- Any C⋆-module admitting a finite Parseval frame is projective over `A`; completeness is not
needed. -/
theorem IsParsevalFrame.projective {A ι E : Type*} [Fintype ι] [Semiring A] [StarRing A]
    [Module ℂ A] [PartialOrder A] [Norm A] [AddCommGroup E] [Module ℂ E] [Module A E] [Norm E]
    [CStarModule A E] {x : ι → E} (hx : IsParsevalFrame A x) :
    Module.Projective A E :=
  let i₀ : E →ₗ[A] (ι → A) :=
    LinearMap.pi fun i ↦
      { toFun := inner A (x i)
        map_add' := fun _ _ ↦ inner_add_right
        map_smul' := fun _ _ ↦ inner_op_smul_right }
  let s₀ : (ι → A) →ₗ[A] E := ∑ i : ι, (LinearMap.proj i).smulRight (x i)
  Module.Projective.of_split i₀ s₀ <|
    LinearMap.ext fun z ↦ by simpa [i₀, s₀, LinearMap.sum_apply] using hx.sum_inner_smul z

end Algebraic

section FiniteProjective

/-- **Frame characterization of finitely generated projective Hilbert modules** (Frank–Larson; Roe,
Proposition 10.2): over a unital C⋆-algebra `A`, a complete right Hilbert `A`-module `E` admits a
finite Parseval frame if and only if `E` is finitely generated and projective as a right `A`-module.
-/
theorem exists_isParsevalFrame_iff_finite_projective {A E : Type*}
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] [Module Aᵐᵒᵖ E]
    [CStarModule Aᵐᵒᵖ E] :
    (∃ (n : ℕ) (x : Fin n → E), IsParsevalFrame Aᵐᵒᵖ x) ↔
      Module.Finite Aᵐᵒᵖ E ∧ Module.Projective Aᵐᵒᵖ E := by
  constructor
  · rintro ⟨n, x, hx⟩
    exact ⟨hx.finite, hx.projective⟩
  · rintro ⟨_, _⟩
    obtain ⟨n, f₀, g₀, _, _, hfg₀⟩ := Module.Finite.exists_comp_eq_id_of_projective Aᵐᵒᵖ E
    let e_pi : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, Fin n → A) ≃ₗ[Aᵐᵒᵖ] (Fin n → Aᵐᵒᵖ) :=
      WithCStarModule.piOpLinearEquiv A (Fin n)
    let f : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, Fin n → A) →ₗ[Aᵐᵒᵖ] E := f₀ ∘ₗ e_pi.toLinearMap
    let g : E →ₗ[Aᵐᵒᵖ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, Fin n → A) := e_pi.symm.toLinearMap ∘ₗ g₀
    have hfg : f ∘ₗ g = LinearMap.id := by
      ext z
      simpa [f, g, LinearMap.comp_apply] using LinearMap.congr_fun hfg₀ z
    obtain ⟨x, hx⟩ := exists_isParsevalFrame_of_comp_eq_id f g hfg
    exact ⟨n, x, hx⟩

/-- Every algebraic finitely generated projective right `A`-module `M` (with compatible complex
scalar multiplication, for example via `Module.compHom M (algebraMap ℂ Aᵐᵒᵖ)`) admits a norm and a
`CStarModule Aᵐᵒᵖ M` structure whose induced `NormedAddCommGroup`
(`CStarModule.normedAddCommGroup Aᵐᵒᵖ`) is complete. -/
theorem exists_completeSpace_cstarModule_of_finite_projective (A M : Type*)
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [AddCommGroup M] [Module ℂ M] [Module Aᵐᵒᵖ M] [IsScalarTower ℂ Aᵐᵒᵖ M]
    [Module.Finite Aᵐᵒᵖ M] [Module.Projective Aᵐᵒᵖ M] :
    ∃ (_ : Norm M) (_ : CStarModule Aᵐᵒᵖ M),
      letI := CStarModule.normedAddCommGroup Aᵐᵒᵖ (E := M)
      CompleteSpace M := by
  obtain ⟨n, f₀, g₀, _, hg₀_inj, hfg₀⟩ := Module.Finite.exists_comp_eq_id_of_projective Aᵐᵒᵖ M
  set F_n := C⋆ᵐᵒᵈ(Aᵐᵒᵖ, Fin n → A)
  have : IsScalarTower ℂ Aᵐᵒᵖ F_n := CStarModule.isScalarTower Aᵐᵒᵖ F_n
  let e_pi : F_n ≃ₗ[Aᵐᵒᵖ] (Fin n → Aᵐᵒᵖ) := WithCStarModule.piOpLinearEquiv A (Fin n)
  let f : F_n →ₗ[Aᵐᵒᵖ] M := f₀ ∘ₗ e_pi.toLinearMap
  let g : M →ₗ[Aᵐᵒᵖ] F_n := e_pi.symm.toLinearMap ∘ₗ g₀
  have hg_inj : Function.Injective g := e_pi.symm.injective.comp hg₀_inj
  have hfg_apply : Function.LeftInverse f g := fun m ↦ by
    simpa [f, g, LinearMap.comp_apply] using LinearMap.congr_fun hfg₀ m
  let : Norm M := ⟨fun m ↦ ‖g m‖⟩
  let : CStarModule Aᵐᵒᵖ M :=
    CStarModule.induced (g.restrictScalars ℂ) hg_inj g.map_smul fun _ ↦ rfl
  let : NormedAddCommGroup M := CStarModule.normedAddCommGroup Aᵐᵒᵖ
  let : NormedSpace ℂ M := .ofCore (CStarModule.normedSpaceCore Aᵐᵒᵖ)
  have hisom : Isometry g := AddMonoidHomClass.isometry_of_norm (g.restrictScalars ℂ) fun _ ↦ rfl
  exact ⟨‹_›, ‹_›, hisom.isUniformInducing.completeSpace
    (hfg_apply.isClosed_range (continuous_of_linearMap f) hisom.continuous).isComplete⟩

variable {A E F : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Every right `A`-linear map out of a complete finitely generated projective right Hilbert
`A`-module into any right C⋆-module over `A` is automatically adjointable. -/
theorem exists_isAdjointPair_of_finite_projective
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] [Module Aᵐᵒᵖ E]
    [CStarModule Aᵐᵒᵖ E] [Module.Finite Aᵐᵒᵖ E] [Module.Projective Aᵐᵒᵖ E]
    [AddCommGroup F] [Module ℂ F] [Module Aᵐᵒᵖ F] [Norm F] [CStarModule Aᵐᵒᵖ F]
    (T : E →ₗ[Aᵐᵒᵖ] F) :
    ∃ S : F →ₗ[Aᵐᵒᵖ] E,
      LinearMap.IsAdjointPair (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip
        (innerₛₗ (A := Aᵐᵒᵖ) (E := F)).flip T S := by
  obtain ⟨_, x, hx⟩ := exists_isParsevalFrame_iff_finite_projective.mpr ⟨‹_›, ‹_›⟩
  exact ⟨frameAdjoint Aᵐᵒᵖ x T, hx.isAdjointPair_frameAdjoint T⟩

/-- Every right `A`-linear equivalence `T : E ≃ₗ[Aᵐᵒᵖ] F` between complete finitely generated
projective right Hilbert `A`-modules admits a polar decomposition `T = U ∘ |T|` into a self-adjoint
positive module automorphism `|T| : E ≃ₗ[Aᵐᵒᵖ] E` and a unitary isomorphism `U : E ≃ₗᵢ[Aᵐᵒᵖ] F`. -/
theorem exists_polar_linearIsometryEquiv_of_finite_projective
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] [Module Aᵐᵒᵖ E]
    [CStarModule Aᵐᵒᵖ E] [Module.Finite Aᵐᵒᵖ E] [Module.Projective Aᵐᵒᵖ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] [Module Aᵐᵒᵖ F]
    [CStarModule Aᵐᵒᵖ F] (T : E ≃ₗ[Aᵐᵒᵖ] F) :
    ∃ (U : E ≃ₗᵢ[Aᵐᵒᵖ] F) (P : E ≃ₗ[Aᵐᵒᵖ] E),
      LinearMap.IsAdjointPair (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip
        (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip P P ∧
      (∀ z : E, 0 ≤ inner Aᵐᵒᵖ z (P z)) ∧
      (∀ z : E, U (P z) = T z) := by
  obtain ⟨_, _, hx⟩ := exists_isParsevalFrame_iff_finite_projective.mpr ⟨‹_›, ‹_›⟩
  exact ⟨hx.polarUnitary T, hx.polarModulus T, hx.isAdjointPair_polarModulus T,
    hx.inner_polarModulus_right_nonneg T, hx.polarUnitary_polarModulus_apply T⟩

/-- Two complete finitely generated projective right Hilbert `A`-modules are unitarily isomorphic
(`E ≃ₗᵢ[Aᵐᵒᵖ] F`) if and only if they are algebraically isomorphic as right `A`-modules
(`E ≃ₗ[Aᵐᵒᵖ] F`). In particular, the complete Hilbert `A`-module structure on any finitely generated
projective right `A`-module is unique up to unitary isomorphism. -/
theorem nonempty_linearIsometryEquiv_iff_nonempty_linearEquiv
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] [Module Aᵐᵒᵖ E]
    [CStarModule Aᵐᵒᵖ E] [Module.Finite Aᵐᵒᵖ E] [Module.Projective Aᵐᵒᵖ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] [Module Aᵐᵒᵖ F]
    [CStarModule Aᵐᵒᵖ F] :
    Nonempty (E ≃ₗᵢ[Aᵐᵒᵖ] F) ↔ Nonempty (E ≃ₗ[Aᵐᵒᵖ] F) :=
  ⟨fun ⟨U⟩ ↦ ⟨U.toLinearEquiv⟩, fun ⟨T⟩ ↦
    let ⟨U, _, _, _, _⟩ := exists_polar_linearIsometryEquiv_of_finite_projective T
    ⟨U⟩⟩

end FiniteProjective

end CStarModule
