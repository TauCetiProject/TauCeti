/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
public import TauCeti.AlgebraicGeometry.Compactification.Basic
public import TauCeti.AlgebraicGeometry.SchemeTheoreticImage.Basic

/-!
# Common refinements of scheme compactifications

Two compactifications `C₁`, `C₂` of `f : X ⟶ S` have a common dense refinement: the
scheme-theoretic closure of `X` in `C₁.Xbar ×_S C₂.Xbar`. The map of `X` into the fibre product
is an immersion, because its composite with the first projection is the open immersion `C₁.j`.
It is quasi-compact, because that projection is separated. Hence `X` is a quasi-compact open
subscheme of its scheme-theoretic closure, which is proper over `S` as a closed subscheme of a
fibre product of proper schemes.

A dense compactification with maps to `C₁` and `C₂` factors uniquely through the refinement, so
the refinement is the binary product in the category of dense compactifications. Iterating
gives a dense compactification refining any nonempty finite family of compactifications.
No hypotheses on `S` or `f` are needed for these constructions.

## Main declarations

* `TauCeti.Compactification.toPullback`: the immersion of `X` into `C₁.Xbar ×_S C₂.Xbar`.
* `TauCeti.Compactification.commonRefinement`: the dense compactification given by the
  scheme-theoretic closure of `X` in `C₁.Xbar ×_S C₂.Xbar`.
* `TauCeti.Compactification.commonRefinementFst`, `TauCeti.Compactification.commonRefinementSnd`:
  its maps to `C₁` and `C₂`.
* `TauCeti.Compactification.commonRefinementLift`: the factorization of a dense compactification
  mapping to `C₁` and `C₂`.
* `TauCeti.DenseCompactification.isLimitCommonRefinementFan`: the common refinement is the
  binary product of dense compactifications.
* `TauCeti.Compactification.exists_forall_nonempty_hom`: a nonempty finite family of
  compactifications has a dense common refinement.

## References

* The Stacks Project, Lemma 38.32.1 (tag 0ATU), *Compactifications*.
* The Stacks Project, Section 29.6, *Scheme theoretic image* (tag 01R5).
* The Stacks Project, Section 29.7, *Scheme theoretic closure and density* (tag 01RB).
-/

public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace TauCeti

variable {X S : Scheme.{u}} {f : X ⟶ S}

namespace Compactification

noncomputable section

/-- The map of the source into the fibre product of two compactifications over the base. -/
def toPullback (C₁ C₂ : Compactification f) : X ⟶ pullback C₁.p C₂.p :=
  pullback.lift C₁.j C₂.j (by simp)

@[reassoc (attr := simp)]
theorem toPullback_fst (C₁ C₂ : Compactification f) :
    C₁.toPullback C₂ ≫ pullback.fst C₁.p C₂.p = C₁.j :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem toPullback_snd (C₁ C₂ : Compactification f) :
    C₁.toPullback C₂ ≫ pullback.snd C₁.p C₂.p = C₂.j :=
  pullback.lift_snd _ _ _

/-- The source is an immersion into the fibre product of two compactifications. -/
instance isImmersion_toPullback (C₁ C₂ : Compactification f) : IsImmersion (C₁.toPullback C₂) :=
  have : IsImmersion (C₁.toPullback C₂ ≫ pullback.fst C₁.p C₂.p) := by
    rw [toPullback_fst]
    infer_instance
  IsImmersion.of_comp _ (pullback.fst C₁.p C₂.p)

/-- The immersion of the source into the fibre product is quasi-compact, since the first
projection is separated. -/
instance quasiCompact_toPullback (C₁ C₂ : Compactification f) : QuasiCompact (C₁.toPullback C₂) :=
  have : QuasiCompact (C₁.toPullback C₂ ≫ pullback.fst C₁.p C₂.p) := by
    rw [toPullback_fst]
    infer_instance
  QuasiCompact.of_comp _ (pullback.fst C₁.p C₂.p)

/-- The common refinement of two compactifications: the scheme-theoretic closure of the source
in the fibre product of their ambient schemes over the base. -/
-- Exposure and implicit reducibility keep the projection formulas of the ambient scheme and its
-- maps usable for dependent morphism equations in importing modules.
@[expose, implicit_reducible] def commonRefinement (C₁ C₂ : Compactification f) :
    DenseCompactification f :=
  ⟨ofHom (C₁.toPullback C₂).toImage
      ((C₁.toPullback C₂).imageι ≫ pullback.fst C₁.p C₂.p ≫ C₁.p) (by simp),
    (denseCompactificationProperty_iff f _).mpr inferInstance⟩

@[simp]
theorem commonRefinement_Xbar (C₁ C₂ : Compactification f) :
    (commonRefinement C₁ C₂).obj.Xbar = (C₁.toPullback C₂).image :=
  (rfl)

@[simp]
theorem commonRefinement_j (C₁ C₂ : Compactification f) :
    (commonRefinement C₁ C₂).obj.j = (C₁.toPullback C₂).toImage :=
  (rfl)

@[simp]
theorem commonRefinement_p (C₁ C₂ : Compactification f) :
    (commonRefinement C₁ C₂).obj.p =
      (C₁.toPullback C₂).imageι ≫ pullback.fst C₁.p C₂.p ≫ C₁.p :=
  (rfl)

/-- The map from the common refinement to the first compactification. -/
def commonRefinementFst (C₁ C₂ : Compactification f) : (commonRefinement C₁ C₂).obj ⟶ C₁ :=
  ObjectProperty.homMk
    { h := (C₁.toPullback C₂).imageι ≫ pullback.fst C₁.p C₂.p
      ι_h := by simp [commonRefinement] }

/-- The map from the common refinement to the second compactification. -/
def commonRefinementSnd (C₁ C₂ : Compactification f) : (commonRefinement C₁ C₂).obj ⟶ C₂ :=
  ObjectProperty.homMk
    { h := (C₁.toPullback C₂).imageι ≫ pullback.snd C₁.p C₂.p
      ι_h := by simp [commonRefinement]
      h_π := by simp [commonRefinement, pullback.condition] }

@[simp]
theorem commonRefinementFst_hom_h (C₁ C₂ : Compactification f) :
    (commonRefinementFst C₁ C₂).hom.h = (C₁.toPullback C₂).imageι ≫ pullback.fst C₁.p C₂.p :=
  (rfl)

@[simp]
theorem commonRefinementSnd_hom_h (C₁ C₂ : Compactification f) :
    (commonRefinementSnd C₁ C₂).hom.h = (C₁.toPullback C₂).imageι ≫ pullback.snd C₁.p C₂.p :=
  (rfl)

/-- Maps into the common refinement are determined by their composites with both projections.
No density of the source is needed. -/
theorem commonRefinement_hom_ext {C₁ C₂ : Compactification f} {D : Compactification f}
    {g g' : D ⟶ (commonRefinement C₁ C₂).obj}
    (h₁ : g ≫ commonRefinementFst C₁ C₂ = g' ≫ commonRefinementFst C₁ C₂)
    (h₂ : g ≫ commonRefinementSnd C₁ C₂ = g' ≫ commonRefinementSnd C₁ C₂) : g = g' := by
  apply ObjectProperty.hom_ext
  apply Factorisation.Hom.ext
  rw [← cancel_mono (C₁.toPullback C₂).imageι]
  apply pullback.hom_ext
  · simpa using congr_arg (fun k ↦ k.hom.h) h₁
  · simpa using congr_arg (fun k ↦ k.hom.h) h₂

/-- A dense compactification mapping to `C₁` and `C₂` factors through their common refinement:
its interior is scheme-theoretically dense, so its map to the fibre product lands in the
scheme-theoretic closure of the source. -/
def commonRefinementLift {C₁ C₂ : Compactification f} (E : DenseCompactification f)
    (h₁ : E.obj ⟶ C₁) (h₂ : E.obj ⟶ C₂) : E.obj ⟶ (commonRefinement C₁ C₂).obj :=
  have H : (C₁.toPullback C₂).imageι.ker ≤
      (pullback.lift h₁.hom.h h₂.hom.h (by simp) : E.obj.Xbar ⟶ pullback C₁.p C₂.p).ker := by
    have hj : C₁.toPullback C₂ = E.obj.j ≫ pullback.lift h₁.hom.h h₂.hom.h (by simp) := by
      apply pullback.hom_ext <;> simp
    rw [Scheme.IdealSheafData.ker_subschemeι, hj, Scheme.Hom.ker_comp, E.obj.j.ker_eq_bot,
      Scheme.IdealSheafData.map_bot]
  ObjectProperty.homMk
    { h := IsClosedImmersion.lift (C₁.toPullback C₂).imageι
        (pullback.lift h₁.hom.h h₂.hom.h (by simp)) H
      ι_h := by
        rw [← cancel_mono (C₁.toPullback C₂).imageι, Category.assoc,
          IsClosedImmersion.lift_fac]
        apply pullback.hom_ext <;> simp [commonRefinement]
      h_π := by simp [commonRefinement] }

/-- On ambient schemes, the factorization through the common refinement followed by the closed
immersion into the fibre product is the pair of the given maps. -/
@[reassoc (attr := simp)]
theorem commonRefinementLift_hom_h_imageι {C₁ C₂ : Compactification f}
    (E : DenseCompactification f) (h₁ : E.obj ⟶ C₁) (h₂ : E.obj ⟶ C₂) :
    (commonRefinementLift E h₁ h₂).hom.h ≫ (C₁.toPullback C₂).imageι =
      pullback.lift h₁.hom.h h₂.hom.h (by simp) :=
  IsClosedImmersion.lift_fac _ _ _

@[reassoc (attr := simp)]
theorem commonRefinementLift_fst {C₁ C₂ : Compactification f} (E : DenseCompactification f)
    (h₁ : E.obj ⟶ C₁) (h₂ : E.obj ⟶ C₂) :
    commonRefinementLift E h₁ h₂ ≫ commonRefinementFst C₁ C₂ = h₁ := by
  apply ObjectProperty.hom_ext
  apply Factorisation.Hom.ext
  simp

@[reassoc (attr := simp)]
theorem commonRefinementLift_snd {C₁ C₂ : Compactification f} (E : DenseCompactification f)
    (h₁ : E.obj ⟶ C₁) (h₂ : E.obj ⟶ C₂) :
    commonRefinementLift E h₁ h₂ ≫ commonRefinementSnd C₁ C₂ = h₂ := by
  apply ObjectProperty.hom_ext
  apply Factorisation.Hom.ext
  simp

/-- Every nonempty finite family of compactifications has a dense common refinement. -/
theorem exists_forall_nonempty_hom {ι : Type*} [Finite ι] [Nonempty ι]
    (C : ι → Compactification f) : ∃ E : DenseCompactification f, ∀ i, Nonempty (E.obj ⟶ C i) := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  suffices ∀ s : Finset ι, ∃ E : DenseCompactification f, ∀ i ∈ s, Nonempty (E.obj ⟶ C i) by
    simpa using this Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨commonRefinement (C i₀) (C i₀), by simp⟩
  | insert a s _ ih =>
    obtain ⟨E, hE⟩ := ih
    refine ⟨commonRefinement E.obj (C a), fun i hi ↦ ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact ⟨commonRefinementSnd E.obj (C i)⟩
    · exact ⟨commonRefinementFst E.obj (C a) ≫ (hE i hi).some⟩

end

end Compactification

namespace DenseCompactification

open Compactification

/-- The binary fan of dense compactifications given by the common refinement. -/
noncomputable abbrev commonRefinementFan (D₁ D₂ : DenseCompactification f) : BinaryFan D₁ D₂ :=
  BinaryFan.mk (P := commonRefinement D₁.obj D₂.obj)
    (ObjectProperty.homMk (commonRefinementFst D₁.obj D₂.obj))
    (ObjectProperty.homMk (commonRefinementSnd D₁.obj D₂.obj))

/-- The common refinement is the binary product in the category of dense compactifications. -/
noncomputable def isLimitCommonRefinementFan (D₁ D₂ : DenseCompactification f) :
    IsLimit (commonRefinementFan D₁ D₂) :=
  BinaryFan.IsLimit.mk _
    (fun {E} h₁ h₂ ↦ ObjectProperty.homMk (commonRefinementLift E h₁.hom h₂.hom))
    (fun h₁ h₂ ↦ ObjectProperty.hom_ext _ (commonRefinementLift_fst _ h₁.hom h₂.hom))
    (fun h₁ h₂ ↦ ObjectProperty.hom_ext _ (commonRefinementLift_snd _ h₁.hom h₂.hom))
    (fun h₁ h₂ m hm₁ hm₂ ↦ ObjectProperty.hom_ext _ <| commonRefinement_hom_ext
      (by simpa using congr_arg (fun k ↦ k.hom) hm₁)
      (by simpa using congr_arg (fun k ↦ k.hom) hm₂))

instance : HasBinaryProducts (DenseCompactification f) :=
  have (D₁ D₂ : DenseCompactification f) : HasLimit (pair D₁ D₂) :=
    ⟨⟨⟨_, isLimitCommonRefinementFan D₁ D₂⟩⟩⟩
  hasBinaryProducts_of_hasLimit_pair _

end DenseCompactification

end TauCeti
