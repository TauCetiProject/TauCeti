/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.Sequence
public import TauCeti.CategoryTheory.AlmostSplit.Equivalence
import TauCeti.CategoryTheory.AlmostSplit.Uniqueness
public import TauCeti.RepresentationTheory.Quiver.Representation.Translate

/-!
# Almost-split sequences realizing the quiver translate

For a quiver with finitely many paths, every pointwise finite-dimensional non-projective
indecomposable representation `M` ends an almost-split sequence `0 → τ M → E → M → 0`,
where `τ M` is the Auslander–Reiten translate `D Tr M`. Its middle term is pointwise
finite-dimensional. Every almost-split sequence with finite-dimensional right endpoint has
left endpoint isomorphic to that translate.

The sequences are almost split in the ambient category of all representations: the lifting
properties include infinite-dimensional test representations. No finite representation type or
algebraic closedness hypothesis is required. The construction transports
`ModuleCat.exists_isAlmostSplit_arTranslate` through the path-algebra equivalence.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section V.1.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti.QuiverRep

universe u v w t

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q]
  [Finite (Quiver.TotalPath Q)]

attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

local notation "kQ" => pathAlgebra k Q
local notation "E" => quiverRepEquivalence k Q
local notation "F" => quiverRepFunctor k Q

/-- Every pointwise finite-dimensional non-projective indecomposable ends an almost-split
sequence with left endpoint `D Tr M` and pointwise finite-dimensional middle term.
Both lifting properties hold in the category of all representations. -/
theorem exists_isAlmostSplit_arTranslate
    (M : QuiverRep.{u, v, w, max u v w t} k Q) (hM : IsFinDim k Q M)
    (hiM : Indecomposable M) (hpM : ¬ Projective M) :
    ∃ (B : QuiverRep.{u, v, w, max u v w t} k Q)
      (i : arTranslate.{u, v, w, t} k Q M hM ⟶ B) (p : B ⟶ M) (h : i ≫ p = 0),
      IsFinDim k Q B ∧ (ShortComplex.mk i p h).IsAlmostSplit := by
  have := module_finite_pathAlgebra_quiverRepEquivalenceFunctorObj_of_isFinDim k Q M hM
  have hi := (E).functor.indecomposable_obj_of_map_bijective hiM
    ((E).fullyFaithfulFunctor.map_bijective _ _)
  obtain ⟨B, i, p, hip, hB, hS⟩ := ModuleCat.exists_isAlmostSplit_arTranslate.{u, max u v w, t}
    k ((E).functor.obj M) hi (fun h ↦ hpM (((E).map_projective_iff M).mp h))
  have := hB
  let a : arTranslate.{u, v, w, t} k Q M hM ≅
      (F).obj (ModuleCat.arTranslate.{u, max u v w, t} k ((E).functor.obj M)) :=
    eqToIso (arTranslate_eq_quiverRepFunctor_obj k Q M hM)
  let c : (F).obj ((E).functor.obj M) ≅ M := by
    simpa only [Functor.comp_obj, Functor.id_obj, quiverRepEquivalence_inverse] using
      ((E).unitIso.app M).symm
  have hmap := ((ShortComplex.mk i p hip).isAlmostSplit_map_iff (F)).mpr hS
  have hip' : (F).map i ≫ (F).map p = 0 := by rw [← Functor.map_comp, hip, Functor.map_zero]
  refine ⟨(F).obj B, a.hom ≫ (F).map i, (F).map p ≫ c.hom,
    by simp only [Category.assoc, reassoc_of% hip', zero_comp, comp_zero],
    isFinDim_quiverRepFunctor_obj k Q B (Module.Finite.trans kQ B), ?_⟩
  exact ShortComplex.isAlmostSplit_of_iso
    (S₁ := (ShortComplex.mk i p hip).map (F))
    (ShortComplex.isoMk a.symm (Iso.refl _) c (by
      simp only [ShortComplex.map_f, Iso.symm_hom,
        Iso.inv_hom_id_assoc, Iso.refl_hom, Category.comp_id])) hmap

/-- A pointwise finite-dimensional representation ends an almost-split sequence in the
ambient representation category exactly when it is indecomposable and non-projective. -/
theorem exists_isAlmostSplit_X₃_eq_iff
    (M : QuiverRep.{u, v, w, max u v w t} k Q) (hM : IsFinDim k Q M) :
    (∃ S : ShortComplex (QuiverRep.{u, v, w, max u v w t} k Q),
      S.X₃ = M ∧ S.IsAlmostSplit) ↔ Indecomposable M ∧ ¬ Projective M := by
  refine ⟨?_, fun ⟨hiM, hpM⟩ ↦ ?_⟩
  · rintro ⟨S, rfl, hS⟩
    exact ⟨hS.isRightAlmostSplit_g.indecomposable, hS.not_projective_X₃⟩
  · obtain ⟨B, i, p, h, _, hS⟩ := exists_isAlmostSplit_arTranslate.{u, v, w, t} M hM hiM hpM
    exact ⟨_, rfl, hS⟩

/-- Every pointwise finite-dimensional non-injective indecomposable starts an almost-split
sequence with pointwise finite-dimensional middle and right terms. -/
theorem exists_isAlmostSplit_of_not_injective
    (N : QuiverRep.{u, v, w, max u v w t} k Q) (hN : IsFinDim k Q N)
    (hiN : Indecomposable N) (hinj : ¬ Injective N) :
    ∃ (B M : QuiverRep.{u, v, w, max u v w t} k Q)
      (i : N ⟶ B) (p : B ⟶ M) (h : i ≫ p = 0),
      IsFinDim k Q B ∧ IsFinDim k Q M ∧ (ShortComplex.mk i p h).IsAlmostSplit := by
  obtain ⟨M, hM, hiM, hpM, ⟨e⟩⟩ := exists_nonempty_iso_arTranslate.{u, v, w, t} k Q N hN hiN hinj
  obtain ⟨B, i, p, h, hB, hS⟩ := exists_isAlmostSplit_arTranslate.{u, v, w, t} M hM hiM hpM
  exact ⟨B, M, e.inv ≫ i, p, by simp [Category.assoc, h], hB, hM,
    ShortComplex.isAlmostSplit_of_iso (S₁ := ShortComplex.mk i p h)
      (ShortComplex.isoMk e (Iso.refl _) (Iso.refl _)) hS⟩

/-- A pointwise finite-dimensional representation starts an almost-split sequence in the
ambient representation category exactly when it is indecomposable and non-injective. -/
theorem exists_isAlmostSplit_X₁_eq_iff
    (N : QuiverRep.{u, v, w, max u v w t} k Q) (hN : IsFinDim k Q N) :
    (∃ S : ShortComplex (QuiverRep.{u, v, w, max u v w t} k Q),
      S.X₁ = N ∧ S.IsAlmostSplit) ↔ Indecomposable N ∧ ¬ Injective N := by
  refine ⟨?_, fun ⟨hiN, hinj⟩ ↦ ?_⟩
  · rintro ⟨S, rfl, hS⟩
    exact ⟨hS.isLeftAlmostSplit_f.indecomposable, hS.not_injective_X₁⟩
  · obtain ⟨B, M, i, p, h, _, _, hS⟩ :=
      exists_isAlmostSplit_of_not_injective.{u, v, w, t} N hN hiN hinj
    exact ⟨_, rfl, hS⟩

end TauCeti.QuiverRep

namespace CategoryTheory.ShortComplex.IsAlmostSplit

open TauCeti

universe u v w t

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q]
  [Finite (Quiver.TotalPath Q)]
  {S : ShortComplex (QuiverRep.{u, v, w, max u v w t} k Q)}

/-- The left endpoint of an almost-split sequence ending at a pointwise finite-dimensional
representation is isomorphic to its `D Tr` translate. -/
theorem nonempty_iso_arTranslate (hS : S.IsAlmostSplit) (hM : IsFinDim k Q S.X₃) :
    Nonempty (S.X₁ ≅ arTranslate.{u, v, w, t} k Q S.X₃ hM) := by
  obtain ⟨B, i, p, h, _, hT⟩ := QuiverRep.exists_isAlmostSplit_arTranslate.{u, v, w, t} S.X₃ hM
    hS.isRightAlmostSplit_g.indecomposable hS.not_projective_X₃
  exact hS.nonempty_iso_X₁ hT (Iso.refl _)

end CategoryTheory.ShortComplex.IsAlmostSplit
