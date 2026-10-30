/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Representation.Translate
public import TauCeti.RepresentationTheory.Quiver.Representation.InverseTranslate
import TauCeti.Algebra.Module.AuslanderReiten.DoubleTranspose.Recovery

/-!
# Inverse identities for Auslander–Reiten translates of quiver representations

For a quiver with finitely many paths, `Tr D` recovers a non-projective indecomposable
representation from its `D Tr` translate. Conversely, `D Tr` recovers a non-injective
indecomposable from its `Tr D` translate. Thus the explicit inverse translate realizes
the inverse of the correspondence on indecomposable isomorphism classes.

The identities are isomorphisms of actual representations, with independently chosen minimal
presentations. The base field is arbitrary; neither algebraic closedness nor finite
representation type is needed.

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

local notation "kQ" => pathAlgebra k Q
local notation "E" => quiverRepEquivalence k Q
local notation "F" => quiverRepFunctor k Q

/-- The inverse translate `Tr D` recovers every finite-dimensional non-projective
indecomposable representation from its `D Tr` translate. -/
theorem nonempty_iso_arInverseTranslate_arTranslate
    (M : QuiverRep.{u, v, w, max u v w t} k Q) (hM : IsFinDim k Q M)
    (hiM : Indecomposable M) (hpM : ¬ Projective M) :
    Nonempty (arInverseTranslate.{u, v, w, t} k Q (arTranslate.{u, v, w, t} k Q M hM)
      (isFinDim_arTranslate.{u, v, w, t} k Q M hM) ≅ M) := by
  let : IsArtinianRing kQ := IsArtinianRing.of_finite k kQ
  let : IsArtinianRing kQᵐᵒᵖ := IsArtinianRing.of_finite k kQᵐᵒᵖ
  let : IsNoetherianRing kQ := IsNoetherianRing.of_finite k kQ
  let : IsNoetherianRing kQᵐᵒᵖ := IsNoetherianRing.of_finite k kQᵐᵒᵖ
  have := module_finite_pathAlgebra_quiverRepEquivalenceFunctorObj_of_isFinDim k Q M hM
  let P : FiniteProjectivePresentation ((E).functor.obj M) := .minimal
  have hP : IsMinimalProjectivePresentation P.p P.π :=
    FiniteProjectivePresentation.isMinimal_minimal
  let T := ModuleCat.of kQ (AuslanderReitenTranslate k P.p)
  have : Module.Finite k T := Module.Finite.trans kQ T
  let N := (E).functor.obj (arTranslate.{u, v, w, t} k Q M hM)
  have : Module.Finite k N :=
    module_finite_quiverRepEquivalenceFunctorObj_of_isFinDim k Q _
      (isFinDim_arTranslate.{u, v, w, t} k Q M hM)
  let D := ModuleCat.rightScalarDual k N
  have : Module.Finite kQᵐᵒᵖ D := Module.Finite.of_restrictScalars_finite k kQᵐᵒᵖ D
  let R : FiniteProjectivePresentation D := .minimal
  have hR : IsMinimalProjectivePresentation R.p R.π :=
    FiniteProjectivePresentation.isMinimal_minimal
  obtain ⟨a⟩ := nonempty_iso_arTranslate.{u, v, w, t} k Q M hM P hP
  -- The counit reads the represented translate back as a path-algebra module.
  have c : (E).functor.obj ((F).obj T) ≅ T := by
    simpa only [quiverRepEquivalence_inverse, Functor.comp_obj, Functor.id_obj] using
      (E).counitIso.app T
  let g : T ≅ N := c.symm ≪≫ (E).functor.mapIso a.symm
  let e : AuslanderReitenTranslate k P.p ≃ₗ[k] Module.Dual k D :=
    (g.toLinearEquiv.restrictScalars k).trans (ModuleCat.rightScalarDualEvalEquiv k N)
  have he (b : kQ) (y : AuslanderReitenTranslate k P.p) (x : D) :
      e (b • y) x = e y (MulOpposite.op b • x) := by
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply, map_smul]
    exact ModuleCat.rightScalarDualEvalEquiv_smul k N b _ x
  have hi := (E).functor.indecomposable_obj_of_map_bijective hiM
    ((E).fullyFaithfulFunctor.map_bijective _ _)
  have hp : ¬ Module.Projective kQ ((E).functor.obj M) := fun h ↦
    hpM (((E).map_projective_iff M).mp ((IsProjective.iff_projective _).mp h))
  obtain ⟨r⟩ := P.nonempty_linearEquiv_rightTranspose_dual_translate.{u, max u v w, t} hP R hR e he
    ((indecomposable_iff_isIndecomposableModule _).mp hi) hp
  obtain ⟨s⟩ := nonempty_iso_arInverseTranslate.{u, v, w, t} k Q (arTranslate.{u, v, w, t} k Q M hM)
    (isFinDim_arTranslate.{u, v, w, t} k Q M hM) R hR
  have cM : (F).obj ((E).functor.obj M) ≅ M := by
    simpa only [quiverRepEquivalence_inverse, Functor.comp_obj, Functor.id_obj] using
      ((E).unitIso.app M).symm
  exact ⟨s ≪≫ (F).mapIso r.toModuleIso ≪≫ cM⟩

/-- The translate `D Tr` recovers every finite-dimensional non-injective indecomposable
representation from its `Tr D` inverse translate. -/
theorem nonempty_iso_arTranslate_arInverseTranslate
    (N : QuiverRep.{u, v, w, max u v w t} k Q) (hN : IsFinDim k Q N)
    (hiN : Indecomposable N) (hinj : ¬ Injective N) :
    Nonempty (arTranslate.{u, v, w, t} k Q (arInverseTranslate.{u, v, w, t} k Q N hN)
      (isFinDim_arInverseTranslate.{u, v, w, t} k Q N hN) ≅ N) := by
  obtain ⟨M, hM, hiM, hpM, ⟨e⟩⟩ := exists_nonempty_iso_arTranslate.{u, v, w, t} k Q N hN hiN hinj
  obtain ⟨r⟩ := nonempty_iso_arInverseTranslate_arTranslate.{u, v, w, t} k Q M hM hiM hpM
  obtain ⟨s⟩ := nonempty_iso_arInverseTranslate_of_iso.{u, v, w, t} k Q
    (isFinDim_arTranslate.{u, v, w, t} k Q M hM) hN e
  obtain ⟨a⟩ := nonempty_iso_arTranslate_of_iso.{u, v, w, t} k Q
    (isFinDim_arInverseTranslate.{u, v, w, t} k Q N hN) hM (s.symm ≪≫ r)
  exact ⟨a ≪≫ e⟩

end TauCeti
