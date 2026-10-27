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
public import Mathlib.Algebra.Category.ModuleCat.Algebra
import TauCeti.Algebra.Module.AuslanderReiten.Isomorphism
import TauCeti.Algebra.Module.AuslanderReiten.Surjectivity
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.RingTheory.HopkinsLevitzki

/-!
# The Auslander–Reiten translate of a module

For a finitely generated module `M` over a finite-dimensional algebra `A` over a field `k`,
`ModuleCat.arTranslate k M` is `D Tr` of a chosen finite minimal projective presentation of `M`,
as an object of `ModuleCat A`. It is finitely generated, independent of the minimal presentation
up to isomorphism (`ModuleCat.nonempty_iso_arTranslate`), and zero exactly when `M` is
projective. For indecomposable `M`, it is indecomposable exactly when `M` is non-projective, and
it is injective exactly when `M` is projective. On non-projective indecomposables it detects
isomorphism classes (`ModuleCat.nonempty_iso_arTranslate_iff`), and every non-injective
indecomposable is a translate (`ModuleCat.exists_nonempty_iso_arTranslate`).

The presentation-level construction `TauCeti.AuslanderReitenTranslate` and its properties are in
`TauCeti/Algebra/Module/AuslanderReiten/`; this file chooses the presentation, so that the
translate becomes a function of the module.

The field is arbitrary and the algebra may be noncommutative. The module lives in a universe
containing those of the field and the algebra, as do its transpose and their linear duals.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section IV.1.
-/

public section

namespace ModuleCat

open CategoryTheory CategoryTheory.Limits TauCeti

attribute [local instance] moduleOfAlgebraModule isScalarTower_of_algebra_moduleCat

universe u v w

variable (k : Type u) {A : Type v} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

private noncomputable def arPresentation (M : ModuleCat.{max u v w} A) [Module.Finite A M] :
    FiniteProjectivePresentation M :=
  letI : IsArtinianRing A := IsArtinianRing.of_finite k A
  FiniteProjectivePresentation.minimal

private theorem arPresentation_isMinimal (M : ModuleCat.{max u v w} A) [Module.Finite A M] :
    IsMinimalProjectivePresentation (arPresentation k M).p (arPresentation k M).π := by
  let : IsArtinianRing A := IsArtinianRing.of_finite k A
  exact FiniteProjectivePresentation.isMinimal_minimal

include k in
private theorem isFiniteLength_of_finite (M : ModuleCat.{max u v w} A) [Module.Finite A M] :
    IsFiniteLength A M :=
  let : IsArtinianRing A := IsArtinianRing.of_finite k A
  isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩

/-- The Auslander–Reiten translate `τ M = D Tr M` of a finitely generated module, formed from a
chosen finite minimal projective presentation. -/
noncomputable def arTranslate (M : ModuleCat.{max u v w} A) [Module.Finite A M] :
    ModuleCat.{max u v w} A :=
  ModuleCat.of A (AuslanderReitenTranslate k (arPresentation k M).p)

/-- Any finite minimal projective presentation computes the same translate up to isomorphism.
This characterizes `ModuleCat.arTranslate` without referring to its chosen presentation. -/
theorem nonempty_iso_arTranslate (M : ModuleCat.{max u v w} A) [Module.Finite A M]
    (P : FiniteProjectivePresentation M) (hP : IsMinimalProjectivePresentation P.p P.π) :
    Nonempty (arTranslate k M ≅ ModuleCat.of A (AuslanderReitenTranslate k P.p)) := by
  obtain ⟨e⟩ := (arPresentation_isMinimal k M).nonempty_linearEquiv_auslanderReitenTranslate
    (k := k) hP
  exact ⟨e.toModuleIso⟩

/-- Isomorphic modules have isomorphic Auslander–Reiten translates. -/
theorem nonempty_iso_arTranslate_of_iso {M N : ModuleCat.{max u v w} A} [Module.Finite A M]
    [Module.Finite A N] (e : M ≅ N) : Nonempty (arTranslate k M ≅ arTranslate k N) := by
  have h := (arPresentation_isMinimal k M).comp_linearEquiv e.toLinearEquiv
  obtain ⟨f⟩ := h.nonempty_linearEquiv_auslanderReitenTranslate (k := k)
    (arPresentation_isMinimal k N)
  exact ⟨f.toModuleIso⟩

instance (M : ModuleCat.{max u v w} A) [Module.Finite A M] : Module.Finite A (arTranslate k M) :=
  inferInstanceAs (Module.Finite A (AuslanderReitenTranslate k (arPresentation k M).p))

/-- The translate vanishes precisely on the projective modules. -/
@[simp]
theorem isZero_arTranslate_iff (M : ModuleCat.{max u v w} A) [Module.Finite A M] :
    IsZero (arTranslate k M) ↔ Projective M :=
  isZero_iff_subsingleton.trans
    (((arPresentation_isMinimal k M).subsingleton_auslanderReitenTranslate_iff_projective k).trans
      (IsProjective.iff_projective (R := A) M))

/-- The translate of a finitely generated indecomposable module is indecomposable exactly when
the module is not projective. -/
@[simp]
theorem indecomposable_arTranslate_iff (M : ModuleCat.{max u v w} A) [Module.Finite A M]
    (hiM : Indecomposable M) : Indecomposable (arTranslate k M) ↔ ¬ Projective M := by
  constructor
  · intro h hp
    exact h.1 ((isZero_arTranslate_iff k M).mpr hp)
  · intro hp
    let P := arPresentation k M
    have hlength := isFiniteLength_of_finite k M
    have htr := (P.isIndecomposableModule_auslanderReitenTranspose_iff
      (arPresentation_isMinimal k M) hlength
      ((indecomposable_iff_isIndecomposableModule M).mp hiM)).mpr
        (fun h ↦ hp ((IsProjective.iff_projective (R := A) M).mp h))
    have : Module.Finite k (AuslanderReitenTranspose P.p) := Module.Finite.trans Aᵐᵒᵖ _
    exact (indecomposable_iff_isIndecomposableModule _).mpr
      ((AuslanderReitenTranslate.isIndecomposableModule_iff P.p k).mpr htr)

/-- The translate is injective exactly when the original module is projective. Consequently
every nonzero translate is non-injective. -/
@[simp]
theorem injective_arTranslate_iff (M : ModuleCat.{max u v w} A) [Module.Finite A M] :
    Injective (arTranslate k M) ↔ Projective M :=
  (Module.injective_iff_injective_object A _).symm.trans
    (((arPresentation_isMinimal k M).moduleInjective_auslanderReitenTranslate_iff_projective
      (k := k)).trans (IsProjective.iff_projective (R := A) M))

/-- On finitely generated indecomposables, with a non-projective source, isomorphism of
Auslander–Reiten translates is equivalent to isomorphism of the modules. -/
theorem nonempty_iso_arTranslate_iff {M N : ModuleCat.{max u v w} A} [Module.Finite A M]
    [Module.Finite A N] (hiM : Indecomposable M) (hiN : Indecomposable N)
    (hpM : ¬ Projective M) :
    Nonempty (arTranslate k M ≅ arTranslate k N) ↔ Nonempty (M ≅ N) := by
  refine ⟨fun ⟨e⟩ ↦ ?_, fun ⟨e⟩ ↦ nonempty_iso_arTranslate_of_iso k e⟩
  let P := arPresentation k M
  let R := arPresentation k N
  have : Module.Finite k (AuslanderReitenTranspose P.p) := Module.Finite.trans Aᵐᵒᵖ _
  have : Module.Finite k (AuslanderReitenTranspose R.p) := Module.Finite.trans Aᵐᵒᵖ _
  have hlenM := isFiniteLength_of_finite k M
  have hlenN := isFiniteLength_of_finite k N
  have hpM' : ¬ Module.Projective A M := fun h ↦
    hpM ((IsProjective.iff_projective (R := A) M).mp h)
  obtain ⟨f⟩ := P.nonempty_linearEquiv_of_auslanderReitenTranslate R hlenM hlenN
    ((indecomposable_iff_isIndecomposableModule M).mp hiM)
    ((indecomposable_iff_isIndecomposableModule N).mp hiN) hpM' e.toLinearEquiv
  exact ⟨f.toModuleIso⟩

/-- Every finitely generated non-injective indecomposable module is, up to isomorphism, the
translate of a finitely generated non-projective indecomposable module. -/
theorem exists_nonempty_iso_arTranslate (N : ModuleCat.{max u v w} A) [Module.Finite A N]
    (hiN : Indecomposable N) (hinj : ¬ Injective N) :
    ∃ (M : ModuleCat.{max u v w} A) (_ : Module.Finite A M),
      Indecomposable M ∧ ¬ Projective M ∧ Nonempty (arTranslate k M ≅ N) := by
  have : Module.Finite k N := Module.Finite.trans A N
  obtain ⟨M, hM, hiM, hpM, P, hP, ⟨e⟩⟩ :=
    exists_auslanderReitenTranslate.{u, v, w} (k := k) N hiN hinj
  have : Module.Finite A M := Module.Finite.of_restrictScalars_finite k A M
  obtain ⟨f⟩ := nonempty_iso_arTranslate k M P hP
  exact ⟨M, inferInstance, hiM, hpM, ⟨f ≪≫ e.toModuleIso⟩⟩

end ModuleCat
