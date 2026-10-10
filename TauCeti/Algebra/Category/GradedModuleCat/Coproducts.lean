/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Products

/-!
# Coproducts of internally graded modules

The existing degreewise direct sum is a coproduct in `GradedModuleCat`. Its injections
and universal map have internal degree zero, so the underlying direct-sum universal
property lifts from modules to graded modules. The forgetful functor to modules preserves
these coproducts.

The universal property follows `ModuleCat.coproductCoconeIsColimit` in
`Mathlib.Algebra.Category.ModuleCat.Products`. The grading argument follows the
direct-sum argument in `GradedModuleCat.freeLift`.

These coproducts provide the sums required for Mathlib's totalization of cochain
bifunctors, including balanced tensor composition of graded bimodule complexes.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

namespace TauCeti.GradedModuleCat

universe uk uA v w

variable {k : Type uk} {A : Type uA} [CommRing k] [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A}
  {J : Type w} (M : J → GradedModuleCat.{max w v} 𝒜)

/-- The cofan of the direct-sum injections, each of internal degree zero.
The abbreviation retains the concrete point for computations with direct-sum elements. -/
abbrev coproductCofan : Cofan M where
  pt := directSumObj M
  ι := Discrete.natTrans fun j ↦ by
    classical
    exact ofHom (N := directSumObj M) (DirectSum.lof A J (fun j ↦ M j) j.as)
      (LinearMap.isHomogeneous_def.2 fun p x hx ↦ by
        rw [add_zero, InternalGrading.directSum_piece]
        simpa only [DirectSum.lof_eq_of] using
          InternalGrading.lof_mem_directSumPiece (fun j ↦ (M j).grading) p j.as ⟨x, hx⟩)

/-- The underlying map of a coproduct injection is the direct-sum inclusion. -/
@[simp]
theorem hom_coproductCofan_inj [hJ : DecidableEq J] (j : J) :
    ((coproductCofan M).inj j).hom = DirectSum.lof A J (fun j ↦ M j) j := by
  cases Subsingleton.elim hJ (Classical.decEq J)
  rfl

/-- Membership in a degree piece of the coproduct is componentwise. -/
theorem mem_coproductCofan_pt_piece_iff {p : ℤ} {x : (coproductCofan M).pt} :
    x ∈ (coproductCofan M).pt.grading.piece p ↔
      ∀ j, x j ∈ (M j).grading.piece p := by
  simpa only [InternalGrading.directSum_piece] using
    InternalGrading.mem_directSumPiece_iff (fun j ↦ (M j).grading) p x

/-- Extend a cofan of graded maps along the direct-sum universal property. -/
def coproductDesc (s : Cofan M) : (coproductCofan M).pt ⟶ s.pt := by
  classical
  let f := DirectSum.toModule A J s.pt fun j ↦ (s.inj j).hom
  refine ofHom f (LinearMap.isHomogeneous_def.2 fun p x hx ↦ ?_)
  have hx' := (mem_coproductCofan_pt_piece_iff M).1 hx
  rw [← DFinsupp.sum_single (f := x), DFinsupp.sum, map_sum]
  refine (s.pt.grading.piece (p + 0)).sum_mem fun j _ ↦ ?_
  dsimp only [f]
  rw [DirectSum.single_eq_lof A, DirectSum.toModule_lof]
  simpa using map_mem (s.inj j) (hx' j)

/-- The underlying universal map is the direct-sum universal linear map. -/
@[simp]
theorem hom_coproductDesc [hJ : DecidableEq J] (s : Cofan M) :
    (coproductDesc M s).hom = DirectSum.toModule A J s.pt fun j ↦ (s.inj j).hom := by
  cases Subsingleton.elim hJ (Classical.decEq J)
  rfl

/-- The universal map restricts to the prescribed map on each summand. -/
@[reassoc (attr := simp)]
theorem coproductCofan_inj_desc (s : Cofan M) (j : J) :
    (coproductCofan M).inj j ≫ coproductDesc M s = s.inj j := by
  classical
  apply hom_ext
  apply LinearMap.ext
  intro x
  -- Compute the two underlying maps on a direct-sum generator.
  change DirectSum.toModule A J s.pt (fun j ↦ (s.inj j).hom)
    (DirectSum.lof A J (fun j ↦ M j) j x) = (s.inj j).hom x
  exact DirectSum.toModule_lof A (M := fun j ↦ M j) (φ := fun j ↦ (s.inj j).hom) j x

/-- The direct sum of internally graded modules is their categorical coproduct. -/
def coproductCofanIsColimit : IsColimit (coproductCofan M) := by
  classical
  refine Cofan.IsColimit.mk _ (coproductDesc M) (coproductCofan_inj_desc M) ?_
  intro s f hf
  apply hom_ext
  apply DirectSum.linearMap_ext
  intro j
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun (congrArg Hom.hom (hf j)) x
  -- Express the cofan equation and universal map on the same direct-sum generator.
  change f.hom (DirectSum.lof A J (fun j ↦ M j) j x) = (s.inj j).hom x at h
  change f.hom (DirectSum.lof A J (fun j ↦ M j) j x) =
    DirectSum.toModule A J s.pt (fun j ↦ (s.inj j).hom)
      (DirectSum.lof A J (fun j ↦ M j) j x)
  rw [DirectSum.toModule_lof]
  exact h

instance : HasCoproduct M :=
  HasColimit.mk ⟨_, coproductCofanIsColimit M⟩

instance : HasCoproducts.{w} (GradedModuleCat.{max w v} 𝒜) :=
  fun _ ↦ ⟨fun F ↦ hasColimit_of_iso (Discrete.natIsoFunctor (F := F))⟩

instance : PreservesColimit (Discrete.functor M) toModuleCat := by
  classical
  exact preservesColimit_of_preserves_colimit_cocone (coproductCofanIsColimit M)
    ((Cofan.isColimitMapCoconeEquiv _ _ _).symm
      (ModuleCat.coproductCoconeIsColimit fun j ↦ toModuleCat.obj (M j)))

end TauCeti.GradedModuleCat
