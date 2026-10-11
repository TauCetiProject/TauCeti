/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.AlmostSplit.Basic
public import TauCeti.RepresentationTheory.Quiver.Representation.FiniteDimensional
import TauCeti.Algebra.Category.ModuleCat.Minimal

/-!
# Minimal summands of maps of quiver representations

Over a finite vertex set, every map with pointwise finite-dimensional source restricts
to a right minimal map on a direct summand. The reduction is transported from finite-length
path algebra modules through `quiverRepEquivalence`.

For right almost split maps, the restriction retains the factorization property in the
full subcategory of pointwise finite-dimensional representations. Thus a construction of
a right almost split map can remove its redundant summands before taking its kernel.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section V.1.
-/

public section

namespace TauCeti.QuiverRep

open CategoryTheory
open scoped ModuleCat

universe u v w t

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q] [Finite Q]

/-- A map from a pointwise finite-dimensional representation restricts to a right minimal
map on a finite-dimensional retract and vanishes on its complementary summand. -/
theorem exists_retract_right_minimal {M N : QuiverRep.{u, v, w, t} k Q} (f : M ⟶ N)
    (hM : IsFinDim k Q M) :
    ∃ (P : QuiverRep.{u, v, w, t} k Q) (_ : IsFinDim k Q P) (s : Retract P M),
      s.r ≫ s.i ≫ f = f ∧
        ∀ b : P ⟶ P, b ≫ s.i ≫ f = s.i ≫ f → IsIso b := by
  classical
  let E := quiverRepEquivalence.{u, v, w, t} k Q
  have hfin : Module.Finite k (E.functor.obj M) :=
    module_finite_quiverRepEquivalenceFunctorObj_of_isFinDim k Q M hM
  have : IsArtinian (pathAlgebra k Q) (E.functor.obj M) := isArtinian_of_tower k inferInstance
  have : IsNoetherian (pathAlgebra k Q) (E.functor.obj M) := isNoetherian_of_tower k inferInstance
  obtain ⟨P, r, hr, hmin⟩ := ModuleCat.exists_retract_right_minimal (E.functor.map f)
    (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)
  let s : Retract (E.inverse.obj P) M :=
    (r.map E.inverse).trans (Retract.ofIso (E.unitIso.app M).symm)
  have hi : s.i = E.inverse.map r.i ≫ E.unitIso.inv.app M := by simp [s, Retract.ofIso]
  have hnat : E.unitIso.inv.app M ≫ f =
      E.inverse.map (E.functor.map f) ≫ E.unitIso.inv.app N := by
    simp
  have hs : s.r ≫ s.i ≫ f = f := by
    simp only [s, Retract.trans_r, Retract.trans_i, Retract.map_r, Retract.map_i,
      Retract.ofIso, Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv,
      Category.assoc]
    rw [hnat]
    simp only [← E.inverse.map_comp_assoc, hr]
    simp
  refine ⟨E.inverse.obj P, hM.of_mono s.i, s, hs, fun b hb ↦ ?_⟩
  let c := E.inverse.preimage b
  have hg : s.i ≫ f = E.inverse.map (r.i ≫ E.functor.map f) ≫ E.unitIso.inv.app N := by
    rw [hi, Category.assoc, hnat, E.inverse.map_comp]
    simp only [Category.assoc]
  have hc : c ≫ r.i ≫ E.functor.map f = r.i ≫ E.functor.map f := by
    apply E.inverse.map_injective
    apply (cancel_mono (E.unitIso.inv.app N)).mp
    rw [hg] at hb
    simpa only [c, Functor.map_comp, Functor.map_preimage, Category.assoc] using hb
  have := hmin c hc
  have : IsIso (E.inverse.map c) := inferInstance
  simpa [c] using this

/-- A right almost split map in the finite-dimensional category restricts to a right
minimal right almost split map on a retract of its source. The lifting quantifiers
continue to range only over finite-dimensional representations. -/
theorem exists_retract_right_minimal_isRightAlmostSplit
    {M N : ObjectProperty.FullSubcategory (IsFinDim.{u, v, w, t} k Q)}
    (f : M ⟶ N) (hf : IsRightAlmostSplit f) :
    ∃ (P : ObjectProperty.FullSubcategory (IsFinDim.{u, v, w, t} k Q)) (s : Retract P M),
      s.r ≫ s.i ≫ f = f ∧ IsRightAlmostSplit (s.i ≫ f) ∧
        ∀ b : P ⟶ P, b ≫ s.i ≫ f = s.i ≫ f → IsIso b := by
  let F := ObjectProperty.ι (IsFinDim.{u, v, w, t} k Q)
  obtain ⟨P, hP, r, hr, hmin⟩ := exists_retract_right_minimal f.hom M.property
  let P' : ObjectProperty.FullSubcategory (IsFinDim.{u, v, w, t} k Q) := ⟨P, hP⟩
  let s : Retract P' M :=
    { i := ObjectProperty.homMk r.i
      r := ObjectProperty.homMk r.r
      retract := ObjectProperty.hom_ext _ (by simp) }
  have hs : s.r ≫ s.i ≫ f = f := ObjectProperty.hom_ext _ (by simpa [s] using hr)
  refine ⟨P', s, hs, hf.retract_i_comp s hs, fun b hb ↦ ?_⟩
  have : IsIso (F.map b) := hmin b.hom (congrArg InducedCategory.Hom.hom hb)
  exact isIso_of_reflects_iso b F

end TauCeti.QuiverRep
