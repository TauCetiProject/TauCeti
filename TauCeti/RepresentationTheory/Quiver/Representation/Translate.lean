/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.Translate
public import TauCeti.Algebra.Module.AuslanderReiten.FinitePresentation
public import TauCeti.Algebra.Module.MinimalProjectivePresentation.Finite
public import TauCeti.RepresentationTheory.Quiver.Representation.FiniteDimensional
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# The Auslander–Reiten translate of a quiver representation

For a quiver with finitely many paths, `arTranslate k Q M hM` is the representation corresponding
to `D Tr` of a chosen finite minimal projective presentation of the path-algebra module of `M`.
It is pointwise finite-dimensional, independent of the minimal presentation up to isomorphism,
and zero exactly when `M` is projective. This supplies an object-level translate for the endpoints
of almost-split sequences; AR duality and the classification of its nonzero values are separate
results.

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

end TauCeti
