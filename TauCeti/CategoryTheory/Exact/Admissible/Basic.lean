/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.CategoryTheory.Exact.Functor
public import Mathlib.CategoryTheory.MorphismProperty.Factorization

/-!
# Admissible morphisms in an exact category

A morphism is admissible when it factors as a deflation followed by an inflation. This is
relative to the chosen exact structure: for the canonical structure of an abelian category,
every morphism is admissible. No ambient kernels, cokernels or images are assumed here.

Admissible factorizations are image factorizations and hence unique up to a unique compatible
isomorphism. Among monomorphisms, admissibility is exactly the inflation condition; dually,
among epimorphisms it is exactly the deflation condition. Exact functors preserve admissibility,
and the predicate is self-dual. These facts supply the morphism calculus for exact complexes.

The factorization data and image uniqueness used here are Mathlib's
`MorphismProperty.MapFactorizationData`, `StrongEpiMonoFactorisation.toMonoIsImage`, and
`IsImage.isoExt`.

## References

* Theo Bühler, *Exact categories*, Definition 2.1 and Section 10, for admissible morphisms
  and acyclic complexes in exact categories.
-/

public section

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace TauCeti

universe v v' u u'

namespace ExactStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] (E : ExactStructure C)

/-- The morphism property of admitting a deflation--inflation factorization. -/
def admissibleMorphisms : MorphismProperty C := E.deflations.comp E.inflations

/-- An admissible morphism factors as a deflation followed by an inflation. -/
abbrev IsAdmissible {X Y : C} (f : X ⟶ Y) : Prop := E.admissibleMorphisms f

/-- The factorization characterization of admissible morphisms. -/
theorem isAdmissible_iff {X Y : C} (f : X ⟶ Y) :
    E.IsAdmissible f ↔ ∃ (I : C) (p : X ⟶ I) (i : I ⟶ Y),
      E.IsDeflation p ∧ E.IsInflation i ∧ p ≫ i = f := by
  constructor
  · rintro ⟨d⟩
    exact ⟨d.Z, d.i, d.p, d.hi, d.hp, d.fac⟩
  · rintro ⟨I, p, i, hp, hi, h⟩
    exact ⟨⟨I, p, i, h, hp, hi⟩⟩

/-- A deflation followed by an inflation is admissible. -/
theorem isAdmissible_comp {X I Y : C} {p : X ⟶ I} {i : I ⟶ Y}
    (hp : E.IsDeflation p) (hi : E.IsInflation i) : E.IsAdmissible (p ≫ i) :=
  (E.isAdmissible_iff _).2 ⟨I, p, i, hp, hi, rfl⟩

/-- Every inflation is admissible. -/
theorem isAdmissible_of_isInflation {X Y : C} {f : X ⟶ Y} (hf : E.IsInflation f) :
    E.IsAdmissible f :=
  (E.isAdmissible_iff _).2 ⟨X, 𝟙 X, f, E.isDeflation_id X, hf, Category.id_comp f⟩

/-- Every deflation is admissible. -/
theorem isAdmissible_of_isDeflation {X Y : C} {f : X ⟶ Y} (hf : E.IsDeflation f) :
    E.IsAdmissible f :=
  (E.isAdmissible_iff _).2 ⟨Y, f, 𝟙 Y, hf, E.isInflation_id Y, Category.comp_id f⟩

/-- The identity morphisms are admissible. -/
instance : E.admissibleMorphisms.ContainsIdentities where
  id_mem X := E.isAdmissible_of_isInflation (E.isInflation_id X)

/-- The zero morphism factors through a zero object by a deflation and an inflation. -/
@[simp]
theorem isAdmissible_zero (X Y : C) : E.IsAdmissible (0 : X ⟶ Y) :=
  (E.isAdmissible_iff _).2 ⟨0, 0, 0,
    E.isDeflation_g (E.conflation_id_zero X), E.isInflation_f (E.conflation_zero_id Y), by simp⟩

/-- Admissibility is invariant under isomorphisms of the source and target. -/
instance : E.admissibleMorphisms.RespectsIso := by
  apply MorphismProperty.RespectsIso.mk
  · rintro X Y Z e f hf
    obtain ⟨I, p, i, hp, hi, rfl⟩ := (E.isAdmissible_iff f).1 hf
    exact (E.isAdmissible_iff _).2
      ⟨I, e.hom ≫ p, i, MorphismProperty.RespectsIso.precomp E.deflations e.hom p hp, hi,
        Category.assoc _ _ _⟩
  · rintro X Y Z e f hf
    obtain ⟨I, p, i, hp, hi, rfl⟩ := (E.isAdmissible_iff f).1 hf
    exact (E.isAdmissible_iff _).2
      ⟨I, p, i ≫ e.hom, hp, MorphismProperty.RespectsIso.postcomp E.inflations e.hom i hi,
        (Category.assoc _ _ _).symm⟩

/-- An admissible monomorphism is an inflation. -/
@[simp]
theorem isAdmissible_iff_isInflation {X Y : C} (f : X ⟶ Y) [Mono f] :
    E.IsAdmissible f ↔ E.IsInflation f := by
  refine ⟨?_, E.isAdmissible_of_isInflation⟩
  intro hf
  obtain ⟨I, p, i, hp, hi, h⟩ := (E.isAdmissible_iff f).1 hf
  have : Mono (p ≫ i) := h.symm ▸ inferInstance
  have : Mono p := mono_of_mono p i
  let := hp.normalEpi
  have : IsIso p := isIso_of_mono_of_strongEpi p
  rw [← h]
  exact MorphismProperty.RespectsIso.precomp E.inflations p i hi

/-- Admissibility in the opposite structure is admissibility of the unopposed morphism. -/
@[simp]
theorem op_isAdmissible_iff {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    E.op.IsAdmissible f ↔ E.IsAdmissible f.unop := by
  constructor
  · intro hf
    obtain ⟨I, p, i, hp, hi, h⟩ := (E.op.isAdmissible_iff f).1 hf
    exact (E.isAdmissible_iff _).2 ⟨I.unop, i.unop, p.unop,
      (E.op_isInflation_iff i).1 hi, (E.op_isDeflation_iff p).1 hp,
      by simpa using congrArg Quiver.Hom.unop h⟩
  · intro hf
    obtain ⟨I, p, i, hp, hi, h⟩ := (E.isAdmissible_iff f.unop).1 hf
    exact (E.op.isAdmissible_iff _).2 ⟨Opposite.op I, i.op, p.op,
      (E.op_isDeflation_iff i.op).2 hi, (E.op_isInflation_iff p.op).2 hp,
      by simpa using congrArg Quiver.Hom.op h⟩

/-- An admissible epimorphism is a deflation. -/
@[simp]
theorem isAdmissible_iff_isDeflation {X Y : C} (f : X ⟶ Y) [Epi f] :
    E.IsAdmissible f ↔ E.IsDeflation f := by
  simpa only [op_isAdmissible_iff, op_isInflation_iff, Quiver.Hom.unop_op] using
    E.op.isAdmissible_iff_isInflation f.op

variable {E} in
/-- Exact functors preserve admissible morphisms. -/
theorem IsConflationExact.map_isAdmissible {D : Type u'} [Category.{v'} D] [Preadditive D]
    [HasZeroObject D] [HasBinaryBiproducts D] {E' : ExactStructure D} {F : C ⥤ D}
    [F.Additive] (hF : E.IsConflationExact E' F) {X Y : C} {f : X ⟶ Y}
    (hf : E.IsAdmissible f) : E'.IsAdmissible (F.map f) := by
  obtain ⟨I, p, i, hp, hi, rfl⟩ := (E.isAdmissible_iff f).1 hf
  rw [F.map_comp]
  exact E'.isAdmissible_comp (hF.map_isDeflation hp) (hF.map_isInflation hi)

variable {E} in
/-- An admissible morphism has an image even when the ambient category does not have all
images. Its admissible factorization supplies the universal property. -/
theorem IsAdmissible.hasImage {X Y : C} {f : X ⟶ Y} (hf : E.IsAdmissible f) :
    HasImage f := by
  obtain ⟨I, p, i, hp, hi, rfl⟩ := (E.isAdmissible_iff f).1 hf
  have := hi.mono
  exact HasImage.mk ⟨_, hp.isImage i rfl⟩

/-- Two admissible factorizations of the same morphism have a unique compatible isomorphism
between their middle objects. -/
theorem existsUnique_iso_of_admissible_factorisations {X I J Y : C}
    {p : X ⟶ I} {i : I ⟶ Y} {q : X ⟶ J} {j : J ⟶ Y}
    (hp : E.IsDeflation p) (hi : E.IsInflation i)
    (hq : E.IsDeflation q) (hj : E.IsInflation j) (h : p ≫ i = q ≫ j) :
    ∃! e : I ≅ J, p ≫ e.hom = q ∧ e.hom ≫ j = i := by
  let F : MonoFactorisation (p ≫ i) := { I := I, m := i, e := p, m_mono := hi.mono }
  let G : MonoFactorisation (p ≫ i) :=
    { I := J, m := j, e := q, m_mono := hj.mono, fac := h.symm }
  have := hi.mono
  have := hj.mono
  have hF : IsImage F := hp.isImage i rfl
  have hG : IsImage G := hq.isImage j h.symm
  refine ⟨IsImage.isoExt hF hG, ⟨IsImage.e_isoExt_hom hF hG, IsImage.isoExt_hom_m hF hG⟩, ?_⟩
  intro e he
  apply Iso.ext
  exact (cancel_mono j).1 (he.2.trans (IsImage.isoExt_hom_m hF hG).symm)

section Abelian

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Every morphism is admissible for the canonical exact structure of an abelian category. -/
@[simp]
theorem abelian_isAdmissible {X Y : A} (f : X ⟶ Y) : (abelian A).IsAdmissible f := by
  let d := Abelian.imageStrongEpiMonoFactorisation f
  exact ((abelian A).isAdmissible_iff _).2 ⟨d.I, d.e, d.m,
    (abelian_isDeflation_iff _).2 inferInstance, (abelian_isInflation_iff _).2 inferInstance,
    d.fac⟩

end Abelian

end ExactStructure

end TauCeti
