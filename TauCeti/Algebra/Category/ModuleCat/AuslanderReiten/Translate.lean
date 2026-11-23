/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.Translate
public import TauCeti.Algebra.Module.AuslanderReiten.Indecomposable
public import TauCeti.Algebra.Module.AuslanderReiten.Injective
public import TauCeti.Algebra.Module.MinimalProjectivePresentation.Finite
public import TauCeti.Algebra.Category.ModuleCat.Indecomposable
public import TauCeti.Algebra.Category.ModuleCat.Algebra
public import TauCeti.Algebra.Module.AuslanderReiten.Inverse
import TauCeti.Algebra.Module.AuslanderReiten.Isomorphism
import TauCeti.Algebra.Module.AuslanderReiten.Surjectivity
import TauCeti.Algebra.Module.AuslanderReiten.DoubleTranspose.Recovery
import Mathlib.Algebra.Category.ModuleCat.Injective
import TauCeti.RingTheory.Artinian.FiniteLength

/-!
# The Auslander–Reiten translate of a module

Let `A` be an Artin algebra over a commutative Artinian ring `R`, and `E` an injective `R`-module
such that each `Hom_R(R ⧸ 𝔪, E)` has length one, for instance an injective hull of `R ⧸ J(R)`, or
`E = k` for a field `R = k` (`TauCeti.length_quotient_linearMap_self_eq_one`). For a finitely
generated module `M`, `ModuleCat.arTranslate R E M` is `D Tr` of a chosen finite minimal projective
presentation of `M`, as an object of `ModuleCat A`, and `ModuleCat.arInverseTranslate R E N` is
`Tr D N`, the right transpose of a chosen finite minimal presentation of the Matlis dual of
`N`.

The translate is finitely generated, independent of the minimal presentation up to isomorphism
(`ModuleCat.nonempty_iso_arTranslate`), and zero exactly when `M` is projective. For
indecomposable `M`, it is indecomposable exactly when `M` is non-projective, and it is injective
exactly when `M` is projective. On non-projective indecomposables it detects isomorphism classes
(`ModuleCat.nonempty_iso_arTranslate_iff`). Dually the inverse translate vanishes exactly on the
injective modules and is projective exactly on them. The two are mutually inverse on
indecomposables: `τ⁻ τ M ≅ M` for non-projective `M`
(`ModuleCat.nonempty_iso_arInverseTranslate_arTranslate`) and `τ τ⁻ N ≅ N` for non-injective `N`
(`ModuleCat.nonempty_iso_arTranslate_arInverseTranslate`), so every non-injective indecomposable is
a translate (`ModuleCat.exists_nonempty_iso_arTranslate`).

The presentation-level constructions and their properties are in
`TauCeti/Algebra/Module/AuslanderReiten/`; this file chooses the presentations, so that the
translates become functions of the module.

The algebra may be noncommutative. The module lives in a universe containing those of `R`, `E` and
the algebra, as do its transpose and their Matlis duals. Over a field `k`, the classical translate
`Hom_k(Tr M, k)` is `ModuleCat.arTranslate k k M`.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Sections IV.1 and V.1.
-/

public section

namespace ModuleCat

open CategoryTheory CategoryTheory.Limits TauCeti

attribute [local instance] moduleOfAlgebra isScalarTower_moduleOfAlgebra

universe u v w

variable (R : Type u) {A : Type v} [CommRing R] [IsArtinianRing R] [Ring A] [Algebra R A]
  [Module.Finite R A]

private noncomputable def arPresentation (M : ModuleCat.{max u v w} A) [Module.Finite A M] :
    FiniteProjectivePresentation M :=
  letI : IsArtinianRing A := IsArtinianRing.of_finite R A
  haveI : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
  FiniteProjectivePresentation.minimal

private theorem arPresentation_isMinimal (M : ModuleCat.{max u v w} A) [Module.Finite A M] :
    IsMinimalProjectivePresentation (arPresentation R M).p (arPresentation R M).π := by
  let : IsArtinianRing A := IsArtinianRing.of_finite R A
  have : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
  exact FiniteProjectivePresentation.isMinimal_minimal

variable (E : Type u) [AddCommGroup E] [Module R E]

section Translate

/-- The Auslander–Reiten translate `τ M = D Tr M` of a finitely generated module, formed from a
chosen finite minimal projective presentation. -/
noncomputable def arTranslate (M : ModuleCat.{max u v w} A) [Module.Finite A M] :
    ModuleCat.{max u v w} A :=
  ModuleCat.of A (AuslanderReitenTranslate R E (arPresentation R M).p)

/-- Any finite minimal projective presentation computes the same translate up to isomorphism.
This characterizes `ModuleCat.arTranslate` without referring to its chosen presentation. -/
theorem nonempty_iso_arTranslate (M : ModuleCat.{max u v w} A) [Module.Finite A M]
    (P : FiniteProjectivePresentation M) (hP : IsMinimalProjectivePresentation P.p P.π) :
    Nonempty (arTranslate R E M ≅ ModuleCat.of A (AuslanderReitenTranslate R E P.p)) := by
  obtain ⟨e⟩ := (arPresentation_isMinimal R M).nonempty_linearEquiv_auslanderReitenTranslate
    (R := R) (E := E) hP
  exact ⟨e.toModuleIso⟩

/-- Isomorphic modules have isomorphic Auslander–Reiten translates. -/
theorem nonempty_iso_arTranslate_of_iso {M N : ModuleCat.{max u v w} A} [Module.Finite A M]
    [Module.Finite A N] (e : M ≅ N) : Nonempty (arTranslate R E M ≅ arTranslate R E N) := by
  have h := (arPresentation_isMinimal R M).comp_linearEquiv e.toLinearEquiv
  obtain ⟨f⟩ := h.nonempty_linearEquiv_auslanderReitenTranslate (R := R) (E := E)
    (arPresentation_isMinimal R N)
  exact ⟨f.toModuleIso⟩

instance [Module.Finite R E] (M : ModuleCat.{max u v w} A) [Module.Finite A M] :
    Module.Finite A (arTranslate R E M) :=
  inferInstanceAs (Module.Finite A (AuslanderReitenTranslate R E (arPresentation R M).p))

variable {R E} [Module.Injective R E]

/-- The translate vanishes precisely on the projective modules, for an injective `E` receiving a
nonzero map from every simple `R`-module. -/
@[simp]
theorem isZero_arTranslate_iff (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Nontrivial (R ⧸ 𝔪 →ₗ[R] E))
    (M : ModuleCat.{max u v w} A) [Module.Finite A M] :
    IsZero (arTranslate R E M) ↔ Projective M :=
  isZero_iff_subsingleton.trans
    (((arPresentation_isMinimal R M).subsingleton_auslanderReitenTranslate_iff_projective
      hE).trans (IsProjective.iff_projective (R := A) M))

variable (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)
include hE

/-- The translate of a finitely generated indecomposable module is indecomposable exactly when
the module is not projective. -/
@[simp]
theorem indecomposable_arTranslate_iff (M : ModuleCat.{max u v w} A) [Module.Finite A M]
    (hiM : Indecomposable M) : Indecomposable (arTranslate R E M) ↔ ¬ Projective M := by
  refine ⟨fun h hp ↦ h.1 ((isZero_arTranslate_iff (nontrivial_linearMap_of_isMaximal hE) M).mpr hp),
    fun hp ↦ ?_⟩
  let P := arPresentation R M
  have : IsArtinianRing A := IsArtinianRing.of_finite R A
  have htr := (P.isIndecomposableModule_auslanderReitenTranspose_iff
    (arPresentation_isMinimal R M) (isFiniteLength_of_finite A M)
    ((indecomposable_iff_isIndecomposableModule M).mp hiM)).mpr
      (fun h ↦ hp ((IsProjective.iff_projective (R := A) M).mp h))
  have : Module.Finite R (AuslanderReitenTranspose P.p) := Module.Finite.trans Aᵐᵒᵖ _
  exact (indecomposable_iff_isIndecomposableModule _).mpr
    ((MatlisDual.isIndecomposableModule_iff hE (isFiniteLength_of_finite R _)).mpr
      htr)

/-- The translate is injective exactly when the original module is projective. Consequently
every nonzero translate is non-injective. -/
@[simp]
theorem injective_arTranslate_iff (M : ModuleCat.{max u v w} A) [Module.Finite A M] :
    Injective (arTranslate R E M) ↔ Projective M :=
  (Module.injective_iff_injective_object A _).symm.trans
    (((arPresentation_isMinimal R M).moduleInjective_auslanderReitenTranslate_iff_projective
      hE).trans (IsProjective.iff_projective (R := A) M))

/-- On finitely generated indecomposables, with a non-projective source, isomorphism of
Auslander–Reiten translates is equivalent to isomorphism of the modules. -/
theorem nonempty_iso_arTranslate_iff {M N : ModuleCat.{max u v w} A} [Module.Finite A M]
    [Module.Finite A N] (hiM : Indecomposable M) (hiN : Indecomposable N)
    (hpM : ¬ Projective M) :
    Nonempty (arTranslate R E M ≅ arTranslate R E N) ↔ Nonempty (M ≅ N) := by
  refine ⟨fun ⟨e⟩ ↦ ?_, fun ⟨e⟩ ↦ nonempty_iso_arTranslate_of_iso R E e⟩
  let P := arPresentation R M
  let Q := arPresentation R N
  have : Module.Finite R (AuslanderReitenTranspose P.p) := Module.Finite.trans Aᵐᵒᵖ _
  have : Module.Finite R (AuslanderReitenTranspose Q.p) := Module.Finite.trans Aᵐᵒᵖ _
  have : IsArtinianRing A := IsArtinianRing.of_finite R A
  have hpM' : ¬ Module.Projective A M := fun h ↦
    hpM ((IsProjective.iff_projective (R := A) M).mp h)
  obtain ⟨f⟩ := P.nonempty_linearEquiv_of_auslanderReitenTranslate hE Q
    (isFiniteLength_of_finite R _) (isFiniteLength_of_finite R _) (isFiniteLength_of_finite A M)
    (isFiniteLength_of_finite A N) ((indecomposable_iff_isIndecomposableModule M).mp hiM)
    ((indecomposable_iff_isIndecomposableModule N).mp hiN) hpM' e.toLinearEquiv
  exact ⟨f.toModuleIso⟩

end Translate

section InverseTranslate

variable [Module.Finite R E]

private noncomputable def arInversePresentation (N : ModuleCat.{max u v w} A)
    [Module.Finite A N] : FiniteProjectivePresentation (ModuleCat.of Aᵐᵒᵖ (MatlisDual R E N)) :=
  letI : IsArtinianRing Aᵐᵒᵖ := IsArtinianRing.of_finite R Aᵐᵒᵖ
  haveI : Module.Finite R N := Module.Finite.trans A N
  haveI : Module.Finite Aᵐᵒᵖ (MatlisDual R E N) := Module.Finite.of_restrictScalars_finite R _ _
  haveI := Module.finitePresentation_of_finite Aᵐᵒᵖ (MatlisDual R E N)
  FiniteProjectivePresentation.minimal

private theorem arInversePresentation_isMinimal (N : ModuleCat.{max u v w} A)
    [Module.Finite A N] : IsMinimalProjectivePresentation (arInversePresentation R E N).p
      (arInversePresentation R E N).π := by
  let : IsArtinianRing Aᵐᵒᵖ := IsArtinianRing.of_finite R Aᵐᵒᵖ
  have : Module.Finite R N := Module.Finite.trans A N
  have : Module.Finite Aᵐᵒᵖ (MatlisDual R E N) := Module.Finite.of_restrictScalars_finite R _ _
  have := Module.finitePresentation_of_finite Aᵐᵒᵖ (MatlisDual R E N)
  exact FiniteProjectivePresentation.isMinimal_minimal

/-- The inverse Auslander–Reiten translate `τ⁻ N = Tr D N` of a finitely generated module: the
right transpose of a chosen finite minimal projective presentation of its Matlis dual. -/
noncomputable def arInverseTranslate (N : ModuleCat.{max u v w} A) [Module.Finite A N] :
    ModuleCat.{max u v w} A :=
  (arInversePresentation R E N).rightTranspose

/-- Any finite minimal projective presentation of the Matlis dual computes the same inverse
translate up to isomorphism. -/
theorem nonempty_iso_arInverseTranslate (N : ModuleCat.{max u v w} A) [Module.Finite A N]
    (Q : FiniteProjectivePresentation (ModuleCat.of Aᵐᵒᵖ (MatlisDual R E N)))
    (hQ : IsMinimalProjectivePresentation Q.p Q.π) :
    Nonempty (arInverseTranslate R E N ≅ Q.rightTranspose) :=
  ((arInversePresentation R E N).nonempty_linearEquiv_rightTranspose Q (LinearEquiv.refl _ _)
    (arInversePresentation_isMinimal R E N) hQ).map LinearEquiv.toModuleIso

/-- Isomorphic modules have isomorphic inverse Auslander–Reiten translates. -/
theorem nonempty_iso_arInverseTranslate_of_iso {N N' : ModuleCat.{max u v w} A}
    [Module.Finite A N] [Module.Finite A N'] (e : N ≅ N') :
    Nonempty (arInverseTranslate R E N ≅ arInverseTranslate R E N') :=
  ((arInversePresentation R E N).nonempty_linearEquiv_rightTranspose
    (arInversePresentation R E N') (MatlisDual.congr e.symm.toLinearEquiv)
    (arInversePresentation_isMinimal R E N) (arInversePresentation_isMinimal R E N')).map
      LinearEquiv.toModuleIso

instance (N : ModuleCat.{max u v w} A) [Module.Finite A N] :
    Module.Finite A (arInverseTranslate R E N) :=
  inferInstanceAs (Module.Finite A (arInversePresentation R E N).rightTranspose)

variable {R E} [Module.Injective R E]
  (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)
include hE

/-- The inverse translate vanishes precisely on the injective modules. -/
@[simp]
theorem isZero_arInverseTranslate_iff (N : ModuleCat.{max u v w} A) [Module.Finite A N] :
    IsZero (arInverseTranslate R E N) ↔ Injective N :=
  isZero_iff_subsingleton.trans
    ((((arInversePresentation R E N).subsingleton_rightTranspose_iff_projective
      (arInversePresentation_isMinimal R E N))).trans
        ((moduleProjective_op_matlisDual_iff_injective hE).trans
          (Module.injective_iff_injective_object A N)))

/-- The inverse translate is projective exactly when the original module is injective. -/
@[simp]
theorem projective_arInverseTranslate_iff (N : ModuleCat.{max u v w} A) [Module.Finite A N] :
    Projective (arInverseTranslate R E N) ↔ Injective N :=
  (IsProjective.iff_projective (R := A) (arInverseTranslate R E N)).symm.trans
    (((arInversePresentation R E N).projective_rightTranspose_iff
      (arInversePresentation_isMinimal R E N)).trans
        ((moduleProjective_op_matlisDual_iff_injective hE).trans
          (Module.injective_iff_injective_object A N)))

/-- The inverse translate of a finitely generated indecomposable module is indecomposable exactly
when the module is not injective. -/
@[simp]
theorem indecomposable_arInverseTranslate_iff (N : ModuleCat.{max u v w} A) [Module.Finite A N]
    (hiN : Indecomposable N) : Indecomposable (arInverseTranslate R E N) ↔ ¬ Injective N := by
  have hN := isFiniteLength_of_finite_trans R A N
  have hiD := (MatlisDual.isIndecomposableModule_op_iff hE hN).mpr
    ((indecomposable_iff_isIndecomposableModule N).mp hiN)
  exact (indecomposable_iff_isIndecomposableModule _).trans
    (((arInversePresentation R E N).isIndecomposableModule_rightTranspose_iff
      (arInversePresentation_isMinimal R E N)
      (isFiniteLength_of_tower R (MatlisDual.isFiniteLength hE hN)) hiD).trans
        (not_congr ((moduleProjective_op_matlisDual_iff_injective hE).trans
          (Module.injective_iff_injective_object A N))))

/-- **`τ⁻ τ M ≅ M`.** The inverse translate recovers a finitely generated non-projective
indecomposable module from its translate. -/
theorem nonempty_iso_arInverseTranslate_arTranslate (M : ModuleCat.{max u v w} A)
    [Module.Finite A M] (hiM : Indecomposable M) (hpM : ¬ Projective M) :
    Nonempty (arInverseTranslate R E (arTranslate R E M) ≅ M) := by
  -- The Matlis dual of the bundled translate carries the `R`-action restricted from `A`; it is
  -- the Matlis dual of the unbundled translate along the identity.
  let e : MatlisDual R E (AuslanderReitenTranslate R E (arPresentation R M).p) ≃ₗ[Aᵐᵒᵖ]
      MatlisDual R E (arTranslate R E M) := MatlisDual.congr (LinearEquiv.refl A _)
  obtain ⟨f⟩ := (arPresentation R M).nonempty_linearEquiv_rightTranspose_matlisDual_translate hE
    (arPresentation_isMinimal R M) _ (arInversePresentation_isMinimal R E _) e
    ((indecomposable_iff_isIndecomposableModule M).mp hiM)
    (fun h ↦ hpM ((IsProjective.iff_projective (R := A) M).mp h))
  exact ⟨f.toModuleIso⟩

/-- **`τ τ⁻ N ≅ N`.** The translate recovers a finitely generated non-injective indecomposable
module from its inverse translate. -/
theorem nonempty_iso_arTranslate_arInverseTranslate (N : ModuleCat.{max u v w} A)
    [Module.Finite A N] (hiN : Indecomposable N) (hinj : ¬ Injective N) :
    Nonempty (arTranslate R E (arInverseTranslate R E N) ≅ N) := by
  obtain ⟨f⟩ :=
    (arInversePresentation R E N).nonempty_linearEquiv_translate_rightTranspose_matlisDual hE
      ((indecomposable_iff_isIndecomposableModule N).mp hiN)
      (fun h ↦ hinj ((Module.injective_iff_injective_object A N).mp h)) _
      (arPresentation_isMinimal R _)
  exact ⟨f.toModuleIso⟩

end InverseTranslate

variable {R E} [Module.Injective R E]

/-- Every finitely generated non-injective indecomposable module is, up to isomorphism, the
translate of a finitely generated non-projective indecomposable module, its inverse translate. -/
theorem exists_nonempty_iso_arTranslate
    (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)
    (N : ModuleCat.{max u v w} A) [Module.Finite A N] (hiN : Indecomposable N)
    (hinj : ¬ Injective N) :
    ∃ (M : ModuleCat.{max u v w} A) (_ : Module.Finite A M),
      Indecomposable M ∧ ¬ Projective M ∧ Nonempty (arTranslate R E M ≅ N) :=
  have := finite_of_forall_isMaximal hE
  ⟨arInverseTranslate R E N, inferInstance,
    (indecomposable_arInverseTranslate_iff hE N hiN).mpr hinj,
    fun h ↦ hinj ((projective_arInverseTranslate_iff hE N).mp h),
    nonempty_iso_arTranslate_arInverseTranslate hE N hiN hinj⟩

end ModuleCat
