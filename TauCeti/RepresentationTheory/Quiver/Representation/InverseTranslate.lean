/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.ScalarDual
public import TauCeti.Algebra.Module.AuslanderReiten.Inverse
public import TauCeti.Algebra.Module.MinimalProjectivePresentation.Finite
public import TauCeti.RepresentationTheory.Quiver.Representation.FiniteDimensional
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# The inverse Auslander–Reiten translate of a quiver representation

For a quiver with finitely many paths, `arInverseTranslate k Q M hM` forms `Tr D M`:
take the right scalar dual of the path-algebra module of `M`, choose a finite minimal
projective presentation, and take its left transpose. The result is pointwise
finite-dimensional and independent of the presentation up to isomorphism.

It vanishes exactly on injectives. For an indecomposable input, it is indecomposable
exactly when the input is non-injective, and its nonzero values are non-projective.
These are the endpoint properties needed for inverse translation on isomorphism classes.
This file does not prove the inverse comparisons with `D Tr`.

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
local notation "eRep" => quiverRepEquivalence k Q
local notation "F" => quiverRepFunctor k Q
local notation "D" => ModuleCat.rightScalarDual k

local instance : Module.Finite k kQ := module_finite_pathAlgebra k Q
local instance : IsArtinianRing kQᵐᵒᵖ := IsArtinianRing.of_finite k kQᵐᵒᵖ
local instance : IsNoetherianRing kQᵐᵒᵖ := IsNoetherianRing.of_finite k kQᵐᵒᵖ

private theorem arDual_finite (M : QuiverRep.{u, v, w, max u v w t} k Q)
    (hM : IsFinDim k Q M) : Module.Finite k (D ((eRep).functor.obj M)) := by
  have := module_finite_quiverRepEquivalenceFunctorObj_of_isFinDim k Q M hM
  infer_instance

private noncomputable def arInversePresentation
    (M : QuiverRep.{u, v, w, max u v w t} k Q) (hM : IsFinDim k Q M) :
    FiniteProjectivePresentation (D ((eRep).functor.obj M)) := by
  have := arDual_finite.{u, v, w, t} k Q M hM
  have : Module.Finite kQᵐᵒᵖ (D ((eRep).functor.obj M)) :=
    Module.Finite.of_restrictScalars_finite k kQᵐᵒᵖ _
  exact FiniteProjectivePresentation.minimal

private theorem arInversePresentation_isMinimal
    (M : QuiverRep.{u, v, w, max u v w t} k Q) (hM : IsFinDim k Q M) :
    IsMinimalProjectivePresentation (arInversePresentation.{u, v, w, t} k Q M hM).p
      (arInversePresentation.{u, v, w, t} k Q M hM).π := by
  have := arDual_finite.{u, v, w, t} k Q M hM
  have : Module.Finite kQᵐᵒᵖ (D ((eRep).functor.obj M)) :=
    Module.Finite.of_restrictScalars_finite k kQᵐᵒᵖ _
  exact FiniteProjectivePresentation.isMinimal_minimal

/-- The inverse Auslander–Reiten translate `Tr D M`, using a finite minimal presentation
of the right scalar dual of the path-algebra module of `M`. -/
noncomputable def arInverseTranslate (M : QuiverRep.{u, v, w, max u v w t} k Q)
    (hM : IsFinDim k Q M) : QuiverRep.{u, v, w, max u v w t} k Q :=
  (F).obj (arInversePresentation.{u, v, w, t} k Q M hM).rightTranspose

/-- Any finite minimal presentation of the right scalar dual computes the inverse translate.
This characterizes the construction independently of its chosen presentation. -/
theorem nonempty_iso_arInverseTranslate (M : QuiverRep.{u, v, w, max u v w t} k Q)
    (hM : IsFinDim k Q M) (P : FiniteProjectivePresentation (D ((eRep).functor.obj M)))
    (hP : IsMinimalProjectivePresentation P.p P.π) :
    Nonempty (arInverseTranslate.{u, v, w, t} k Q M hM ≅ (F).obj P.rightTranspose) := by
  obtain ⟨e⟩ := (arInversePresentation.{u, v, w, t} k Q M hM).nonempty_linearEquiv_rightTranspose P
    (LinearEquiv.refl _ _) (arInversePresentation_isMinimal.{u, v, w, t} k Q M hM) hP
  exact ⟨(F).mapIso e.toModuleIso⟩

/-- Isomorphic representations have isomorphic inverse translates. -/
theorem nonempty_iso_arInverseTranslate_of_iso
    {M N : QuiverRep.{u, v, w, max u v w t} k Q}
    (hM : IsFinDim k Q M) (hN : IsFinDim k Q N) (e : M ≅ N) :
    Nonempty (arInverseTranslate.{u, v, w, t} k Q M hM ≅
      arInverseTranslate.{u, v, w, t} k Q N hN) := by
  let d := ModuleCat.rightScalarDualIso (k := k) ((eRep).functor.mapIso e).symm
  obtain ⟨f⟩ := (arInversePresentation.{u, v, w, t} k Q M hM).nonempty_linearEquiv_rightTranspose
    (arInversePresentation.{u, v, w, t} k Q N hN) d.toLinearEquiv
    (arInversePresentation_isMinimal.{u, v, w, t} k Q M hM)
    (arInversePresentation_isMinimal.{u, v, w, t} k Q N hN)
  exact ⟨(F).mapIso f.toModuleIso⟩

/-- The inverse translate is pointwise finite-dimensional. -/
theorem isFinDim_arInverseTranslate (M : QuiverRep.{u, v, w, max u v w t} k Q)
    (hM : IsFinDim k Q M) : IsFinDim k Q (arInverseTranslate.{u, v, w, t} k Q M hM) := by
  let P := arInversePresentation.{u, v, w, t} k Q M hM
  let T : ModuleCat kQ := P.rightTranspose
  -- Fix restriction of scalars on the bundled transpose, rather than its quotient action.
  let : SMul k T := (ModuleCat.moduleOfAlgebraModule (k := k) T).toSMul
  let : Module k T := ModuleCat.moduleOfAlgebraModule (k := k) T
  let : IsScalarTower k kQ T := ModuleCat.isScalarTower_of_algebra_moduleCat (k := k) T
  have hT : Module.Finite k T := Module.Finite.trans kQ _
  exact isFinDim_quiverRepFunctor_obj k Q T hT

/-- The inverse translate is projective exactly when the input is injective. -/
@[simp]
theorem projective_arInverseTranslate_iff (M : QuiverRep.{u, v, w, max u v w t} k Q)
    (hM : IsFinDim k Q M) :
    Projective (arInverseTranslate.{u, v, w, t} k Q M hM) ↔ Injective M := by
  let P := arInversePresentation.{u, v, w, t} k Q M hM
  have := module_finite_quiverRepEquivalenceFunctorObj_of_isFinDim k Q M hM
  have := arDual_finite.{u, v, w, t} k Q M hM
  have hp := P.projective_rightTranspose_iff_injective
    (E := (eRep).functor.obj M)
    (arInversePresentation_isMinimal.{u, v, w, t} k Q M hM)
    (ModuleCat.rightScalarDualEvalEquiv k ((eRep).functor.obj M))
    (ModuleCat.rightScalarDualEvalEquiv_smul k ((eRep).functor.obj M))
  have h : Projective ((F).obj P.rightTranspose) ↔ Projective P.rightTranspose := by
    simpa only [Equivalence.symm_functor, quiverRepEquivalence_inverse] using
      (eRep).symm.map_projective_iff P.rightTranspose
  exact h.trans ((IsProjective.iff_projective (R := kQ) P.rightTranspose).symm.trans
    (hp.trans ((Module.injective_iff_injective_object kQ _).trans
      ((eRep).map_injective_iff M))))

/-- The inverse translate vanishes exactly on injective representations. -/
@[simp]
theorem isZero_arInverseTranslate_iff (M : QuiverRep.{u, v, w, max u v w t} k Q)
    (hM : IsFinDim k Q M) :
    IsZero (arInverseTranslate.{u, v, w, t} k Q M hM) ↔ Injective M := by
  let P := arInversePresentation.{u, v, w, t} k Q M hM
  have := module_finite_quiverRepEquivalenceFunctorObj_of_isFinDim k Q M hM
  have := arDual_finite.{u, v, w, t} k Q M hM
  have hz : IsZero ((F).obj P.rightTranspose) ↔ IsZero P.rightTranspose :=
    ⟨fun h ↦ IsZero.of_full_of_faithful_of_isZero (F) _ h, (F).map_isZero⟩
  have hd := LinearEquiv.moduleInjective_iff_projective_of_dual
    (ModuleCat.rightScalarDualEvalEquiv k ((eRep).functor.obj M))
      (ModuleCat.rightScalarDualEvalEquiv_smul k ((eRep).functor.obj M))
  exact hz.trans (ModuleCat.isZero_iff_subsingleton.trans
    ((P.subsingleton_rightTranspose_iff_projective
      (arInversePresentation_isMinimal.{u, v, w, t} k Q M hM)).trans
        (hd.symm.trans ((Module.injective_iff_injective_object kQ _).trans
          ((eRep).map_injective_iff M)))))

/-- For an indecomposable input, the inverse translate is indecomposable exactly when
the input is non-injective. -/
@[simp]
theorem indecomposable_arInverseTranslate_iff (M : QuiverRep.{u, v, w, max u v w t} k Q)
    (hM : IsFinDim k Q M) (hiM : Indecomposable M) :
    Indecomposable (arInverseTranslate.{u, v, w, t} k Q M hM) ↔ ¬ Injective M := by
  let P := arInversePresentation.{u, v, w, t} k Q M hM
  have := module_finite_quiverRepEquivalenceFunctorObj_of_isFinDim k Q M hM
  have := arDual_finite.{u, v, w, t} k Q M hM
  have hi := (eRep).functor.indecomposable_obj_of_map_bijective hiM
    ((eRep).fullyFaithfulFunctor.map_bijective _ _)
  have ht := P.isIndecomposableModule_rightTranspose_iff_not_injective
    (E := (eRep).functor.obj M)
    (arInversePresentation_isMinimal.{u, v, w, t} k Q M hM)
    (ModuleCat.rightScalarDualEvalEquiv k ((eRep).functor.obj M))
    (ModuleCat.rightScalarDualEvalEquiv_smul k ((eRep).functor.obj M))
    ((indecomposable_iff_isIndecomposableModule _).mp hi)
  constructor
  · intro h hiM
    exact h.1 ((isZero_arInverseTranslate_iff.{u, v, w, t} k Q M hM).mpr hiM)
  · intro hn
    have htr := ht.mpr (fun h ↦ hn (((eRep).map_injective_iff M).mp
      ((Module.injective_iff_injective_object kQ _).mp h)))
    exact (F).indecomposable_obj_of_map_bijective
      ((indecomposable_iff_isIndecomposableModule _).mpr htr)
      ((Functor.FullyFaithful.ofFullyFaithful (F)).map_bijective _ _)

end TauCeti
