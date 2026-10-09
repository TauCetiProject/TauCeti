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
public import TauCeti.RepresentationTheory.Quiver.Representation.FiniteDimensional
import TauCeti.Algebra.Module.AuslanderReiten.Isomorphism
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# The Auslander–Reiten translate of a quiver representation

For a quiver with finitely many paths, `arTranslate k Q M hM` is the representation corresponding
to `D Tr` of a chosen finite minimal projective presentation of the path-algebra module of `M`.
It is pointwise finite-dimensional, independent of the minimal presentation up to isomorphism,
and zero exactly when `M` is projective. For indecomposable `M`, it is indecomposable exactly
when `M` is non-projective, and every nonzero value is non-injective. These properties allow
the translate to act on isomorphism classes of indecomposables and provide the endpoints of
almost-split sequences. On non-projective indecomposables, it detects isomorphism classes.
AR duality and the inverse correspondence are separate results.

The field is arbitrary. Vertex and arrow universes are independent of the field universe.
The vertex spaces lie in a universe containing the field and the path algebra, as do the
transpose and its linear dual.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section IV.1.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat

attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

universe u v w t

variable (k : Type u) (Q : Type v) [Field k] [Quiver.{w} Q]
  [Finite (Quiver.TotalPath Q)]

local instance : Finite Q :=
  Finite.of_injective (fun q : Q ↦ (⟨q, q, Quiver.Path.nil⟩ : Quiver.TotalPath Q))
    (fun _ _ h ↦ congrArg Sigma.fst h)

local notation "kQ" => pathAlgebra k Q
local notation "E" => quiverRepEquivalence k Q
local notation "F" => quiverRepFunctor k Q

local instance : Module.Finite k kQ := module_finite_pathAlgebra k Q
local instance : IsArtinianRing kQ := IsArtinianRing.of_finite k kQ
local instance : IsNoetherianRing kQ := IsNoetherianRing.of_finite k kQ

private noncomputable def arPresentation (M : QuiverRep.{u, v, w, max u v w t} k Q)
    (hM : IsFinDim k Q M) : FiniteProjectivePresentation ((E).functor.obj M) := by
  have : Module.Finite k ((E).functor.obj M) :=
    module_finite_quiverRepEquivalenceFunctorObj_of_isFinDim k Q M hM
  have : Module.Finite kQ ((E).functor.obj M) :=
    Module.Finite.of_restrictScalars_finite k kQ _
  exact FiniteProjectivePresentation.minimal.{max u v w, max u v w t}
    (A := kQ) (M := (E).functor.obj M)

private theorem arPresentation_isMinimal (M : QuiverRep.{u, v, w, max u v w t} k Q)
    (hM : IsFinDim k Q M) :
    IsMinimalProjectivePresentation (arPresentation.{u, v, w, t} k Q M hM).p
      (arPresentation.{u, v, w, t} k Q M hM).π := by
  have : Module.Finite k ((E).functor.obj M) :=
    module_finite_quiverRepEquivalenceFunctorObj_of_isFinDim k Q M hM
  have : Module.Finite kQ ((E).functor.obj M) :=
    Module.Finite.of_restrictScalars_finite k kQ _
  unfold arPresentation
  exact FiniteProjectivePresentation.isMinimal_minimal.{max u v w, max u v w t}
    (A := kQ) (M := (E).functor.obj M)

/-- The Auslander–Reiten translate `τ M = D Tr M`, formed from a finite minimal projective
presentation of the path-algebra module of a pointwise finite-dimensional representation. -/
noncomputable def arTranslate (M : QuiverRep.{u, v, w, max u v w t} k Q)
    (hM : IsFinDim k Q M) : QuiverRep.{u, v, w, max u v w t} k Q :=
  (F).obj (ModuleCat.of kQ
    (AuslanderReitenTranslate k (arPresentation.{u, v, w, t} k Q M hM).p))

/-- Any finite minimal projective presentation computes the same translate up to isomorphism.
This characterizes `arTranslate` without referring to its chosen presentation. -/
theorem nonempty_iso_arTranslate (M : QuiverRep.{u, v, w, max u v w t} k Q)
    (hM : IsFinDim k Q M)
    (P : FiniteProjectivePresentation ((E).functor.obj M))
    (hP : IsMinimalProjectivePresentation P.p P.π) :
    Nonempty (arTranslate.{u, v, w, t} k Q M hM ≅
      (F).obj (ModuleCat.of kQ (AuslanderReitenTranslate k P.p))) := by
  obtain ⟨e⟩ :=
    (arPresentation_isMinimal.{u, v, w, t} k Q M hM).nonempty_linearEquiv_auslanderReitenTranslate
      (k := k) hP
  simpa only [arTranslate] using Nonempty.intro ((F).mapIso e.toModuleIso)

/-- Isomorphic representations have isomorphic Auslander–Reiten translates. -/
theorem nonempty_iso_arTranslate_of_iso {M N : QuiverRep.{u, v, w, max u v w t} k Q}
    (hM : IsFinDim k Q M) (hN : IsFinDim k Q N) (e : M ≅ N) :
    Nonempty (arTranslate.{u, v, w, t} k Q M hM ≅
      arTranslate.{u, v, w, t} k Q N hN) := by
  let eM := ((E).functor.mapIso e).toLinearEquiv
  have h := (arPresentation_isMinimal.{u, v, w, t} k Q M hM).comp_linearEquiv eM
  obtain ⟨f⟩ := h.nonempty_linearEquiv_auslanderReitenTranslate (k := k)
    (arPresentation_isMinimal.{u, v, w, t} k Q N hN)
  simpa only [arTranslate] using Nonempty.intro ((F).mapIso f.toModuleIso)

/-- The Auslander–Reiten translate stays within the pointwise finite-dimensional
representations. -/
theorem isFinDim_arTranslate (M : QuiverRep.{u, v, w, max u v w t} k Q)
    (hM : IsFinDim k Q M) : IsFinDim k Q (arTranslate.{u, v, w, t} k Q M hM) := by
  let P := arPresentation.{u, v, w, t} k Q M hM
  have : Module.Finite k (AuslanderReitenTranspose P.p) :=
    Module.Finite.trans kQᵐᵒᵖ _
  have : Module.Finite kQ (AuslanderReitenTranslate k P.p) :=
    Module.Finite.of_restrictScalars_finite k kQ _
  let T := ModuleCat.of kQ (AuslanderReitenTranslate k P.p)
  -- The bundled functor restricts scalars along the algebra map; pin that action rather
  -- than allowing typeclass search to use the unbundled dual's scalar action.
  let : SMul k T := (ModuleCat.moduleOfAlgebraModule (k := k) T).toSMul
  let : Module k T := ModuleCat.moduleOfAlgebraModule (k := k) T
  let : IsScalarTower k kQ T := ModuleCat.isScalarTower_of_algebra_moduleCat (k := k) T
  have hT : Module.Finite k T := Module.Finite.trans kQ _
  simpa only [arTranslate, P, T] using isFinDim_quiverRepFunctor_obj k Q T hT

/-- The translate vanishes precisely on the projective representations. -/
@[simp]
theorem isZero_arTranslate_iff (M : QuiverRep.{u, v, w, max u v w t} k Q)
    (hM : IsFinDim k Q M) : IsZero (arTranslate.{u, v, w, t} k Q M hM) ↔ Projective M := by
  let P := arPresentation.{u, v, w, t} k Q M hM
  let T := ModuleCat.of kQ (AuslanderReitenTranslate k P.p)
  have hzero : IsZero ((F).obj T) ↔ IsZero T :=
    ⟨fun h ↦ IsZero.of_full_of_faithful_of_isZero (F) T h, (F).map_isZero⟩
  have h := arPresentation_isMinimal.{u, v, w, t} k Q M hM
  have hproj := h.subsingleton_auslanderReitenTranslate_iff_projective k
  simpa only [arTranslate, P, T] using hzero.trans (ModuleCat.isZero_iff_subsingleton.trans
    (hproj.trans ((IsProjective.iff_projective (R := kQ) ((E).functor.obj M)).trans
      ((E).map_projective_iff M))))

/-- The translate of a finite-dimensional indecomposable representation is indecomposable
exactly when the representation is not projective. -/
@[simp]
theorem indecomposable_arTranslate_iff (M : QuiverRep.{u, v, w, max u v w t} k Q)
    (hM : IsFinDim k Q M) (hiM : Indecomposable M) :
    Indecomposable (arTranslate.{u, v, w, t} k Q M hM) ↔ ¬ Projective M := by
  let eRep := quiverRepEquivalence.{u, v, w, max u v w t} k Q
  let fRep := quiverRepFunctor.{u, v, w, max u v w t} k Q
  constructor
  · intro h hp
    exact h.1 ((isZero_arTranslate_iff k Q M hM).mpr hp)
  · intro hp
    let P := arPresentation.{u, v, w, t} k Q M hM
    have : Module.Finite k (eRep.functor.obj M) :=
      module_finite_quiverRepEquivalenceFunctorObj_of_isFinDim k Q M hM
    have : Module.Finite kQ (eRep.functor.obj M) :=
      Module.Finite.of_restrictScalars_finite k kQ _
    have hlength : IsFiniteLength kQ (eRep.functor.obj M) :=
      isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
    have hi := eRep.functor.indecomposable_obj_of_map_bijective hiM
      (eRep.fullyFaithfulFunctor.map_bijective _ _)
    have htr := (P.isIndecomposableModule_auslanderReitenTranspose_iff
      (arPresentation_isMinimal.{u, v, w, t} k Q M hM) hlength
      ((indecomposable_iff_isIndecomposableModule _).mp hi)).mpr
        (fun h ↦ hp ((eRep.map_projective_iff M).mp
          ((IsProjective.iff_projective (R := kQ) (eRep.functor.obj M)).mp h)))
    have : Module.Finite k (AuslanderReitenTranspose P.p) :=
      Module.Finite.trans kQᵐᵒᵖ _
    have ht := (AuslanderReitenTranslate.isIndecomposableModule_iff P.p k).mpr htr
    have hT := (indecomposable_iff_isIndecomposableModule
      (ModuleCat.of kQ (AuslanderReitenTranslate k P.p))).mpr ht
    simpa only [arTranslate, P] using fRep.indecomposable_obj_of_map_bijective hT
      ((Functor.FullyFaithful.ofFullyFaithful fRep).map_bijective _ _)

/-- The translate is injective exactly when the original representation is projective.
Consequently every nonzero translate is non-injective. -/
@[simp]
theorem injective_arTranslate_iff (M : QuiverRep.{u, v, w, max u v w t} k Q)
    (hM : IsFinDim k Q M) :
    Injective (arTranslate.{u, v, w, t} k Q M hM) ↔ Projective M := by
  let eRep := quiverRepEquivalence.{u, v, w, max u v w t} k Q
  let fRep := quiverRepFunctor.{u, v, w, max u v w t} k Q
  let P := arPresentation.{u, v, w, t} k Q M hM
  let T := ModuleCat.of kQ (AuslanderReitenTranslate k P.p)
  have hP := arPresentation_isMinimal.{u, v, w, t} k Q M hM
  have h := hP.moduleInjective_auslanderReitenTranslate_iff_projective (k := k)
  have hproj := (IsProjective.iff_projective (R := kQ) (eRep.functor.obj M)).trans
    (eRep.map_projective_iff M)
  have hinj : Injective (fRep.obj T) ↔ Injective T := by
    simpa only [eRep, fRep, Equivalence.symm_functor, quiverRepEquivalence_inverse] using
      eRep.symm.map_injective_iff T
  simpa only [arTranslate, P, T] using hinj.trans
    ((Module.injective_iff_injective_object kQ _).symm.trans (h.trans hproj))

/-- On finite-dimensional indecomposables, with a non-projective source, isomorphism
of Auslander–Reiten translates is equivalent to isomorphism of the representations. -/
theorem nonempty_iso_arTranslate_iff {M N : QuiverRep.{u, v, w, max u v w t} k Q}
    (hM : IsFinDim k Q M) (hN : IsFinDim k Q N)
    (hiM : Indecomposable M) (hiN : Indecomposable N) (hpM : ¬ Projective M) :
    Nonempty (arTranslate.{u, v, w, t} k Q M hM ≅ arTranslate.{u, v, w, t} k Q N hN) ↔
      Nonempty (M ≅ N) := by
  constructor
  · rintro ⟨e⟩
    let P := arPresentation.{u, v, w, t} k Q M hM
    let R := arPresentation.{u, v, w, t} k Q N hN
    obtain ⟨eM⟩ := nonempty_iso_arTranslate.{u, v, w, t} k Q M hM P
      (arPresentation_isMinimal.{u, v, w, t} k Q M hM)
    obtain ⟨eN⟩ := nonempty_iso_arTranslate.{u, v, w, t} k Q N hN R
      (arPresentation_isMinimal.{u, v, w, t} k Q N hN)
    let eT := (Functor.FullyFaithful.ofFullyFaithful (F)).preimageIso
      (eM.symm ≪≫ e ≪≫ eN)
    have : Module.Finite k ((E).functor.obj M) :=
      module_finite_quiverRepEquivalenceFunctorObj_of_isFinDim k Q M hM
    have : Module.Finite k ((E).functor.obj N) :=
      module_finite_quiverRepEquivalenceFunctorObj_of_isFinDim k Q N hN
    have : Module.Finite k (AuslanderReitenTranspose P.p) := Module.Finite.trans kQᵐᵒᵖ _
    have : Module.Finite k (AuslanderReitenTranspose R.p) := Module.Finite.trans kQᵐᵒᵖ _
    have hlenM : IsFiniteLength kQ ((E).functor.obj M) :=
      isFiniteLength_iff_isNoetherian_isArtinian.mpr
        ⟨isNoetherian_of_tower k inferInstance, isArtinian_of_tower k inferInstance⟩
    have hlenN : IsFiniteLength kQ ((E).functor.obj N) :=
      isFiniteLength_iff_isNoetherian_isArtinian.mpr
        ⟨isNoetherian_of_tower k inferInstance, isArtinian_of_tower k inferInstance⟩
    have hiM' := (E).functor.indecomposable_obj_of_map_bijective hiM
      ((E).fullyFaithfulFunctor.map_bijective _ _)
    have hiN' := (E).functor.indecomposable_obj_of_map_bijective hiN
      ((E).fullyFaithfulFunctor.map_bijective _ _)
    have hpM' : ¬ Module.Projective kQ ((E).functor.obj M) := fun h ↦
      hpM (((E).map_projective_iff M).mp ((IsProjective.iff_projective
        (R := kQ) ((E).functor.obj M)).mp h))
    obtain ⟨f⟩ := P.nonempty_linearEquiv_of_auslanderReitenTranslate R hlenM hlenN
      ((indecomposable_iff_isIndecomposableModule _).mp hiM')
      ((indecomposable_iff_isIndecomposableModule _).mp hiN') hpM' eT.toLinearEquiv
    exact ⟨(E).fullyFaithfulFunctor.preimageIso f.toModuleIso⟩
  · rintro ⟨e⟩
    exact nonempty_iso_arTranslate_of_iso.{u, v, w, t} k Q hM hN e

end TauCeti
