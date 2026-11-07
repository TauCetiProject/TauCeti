/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Functor
public import Mathlib.CategoryTheory.MorphismProperty.Factorization
public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono

/-!
# Admissible morphisms in exact categories

A morphism is admissible if it factors as a deflation followed by an inflation. These are the
maps for which the exact structure supplies an image factorization. The order matters: arbitrary
composites of admissible morphisms need not be admissible.

We use Mathlib's `MorphismProperty.comp` for the existence of a factorization, rather than
introducing another bundle of factorization data. Admissibility is self-dual, invariant under
isomorphisms, and preserved by conflation-exact functors. An admissible monomorphism is an
inflation, and an admissible epimorphism is a deflation. Any two admissible factorizations have a
unique compatible isomorphism between their intermediate objects.

For the canonical exact structure of an abelian category every morphism is admissible; no such
assertion is made for an arbitrary exact structure on that category.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1--69,
  <https://arxiv.org/abs/0811.1480>, Definition 2.1 and Section 10.
* The uniqueness argument uses Mathlib's `StrongEpiMonoFactorisation.toMonoIsImage` and
  `CategoryTheory.Limits.IsImage.isoExt`.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v v' u u'

namespace ConflationClass

variable {C : Type u} [Category.{v} C] [Preadditive C] {E : ConflationClass C}

/-- A deflation is a regular epimorphism, since it is a cokernel. -/
theorem IsDeflation.isRegularEpi {X Y : C} {p : X ⟶ Y} (hp : E.IsDeflation p) :
    IsRegularEpi p := by
  obtain ⟨K, k, h, hc⟩ := (E.isDeflation_iff p).1 hp
  exact ⟨⟨Cofork.IsColimit.regularEpi (E.isKernelCokernelPair _ hc).gIsCokernel⟩⟩

/-- An inflation is a regular monomorphism, since it is a kernel. -/
theorem IsInflation.isRegularMono {X Y : C} {i : X ⟶ Y} (hi : E.IsInflation i) :
    IsRegularMono i := by
  obtain ⟨Q, q, h, hc⟩ := (E.isInflation_iff i).1 hi
  exact ⟨⟨Fork.IsLimit.regularMono (E.isKernelCokernelPair _ hc).fIsKernel⟩⟩

end ConflationClass

namespace ExactStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] (E : ExactStructure C)

/-- The admissible morphisms: composites of a deflation followed by an inflation. -/
def admissibles : MorphismProperty C := E.deflations.comp E.inflations

/-- A morphism is admissible when it factors as a deflation followed by an inflation. -/
abbrev IsAdmissible {X Y : C} (f : X ⟶ Y) : Prop := E.admissibles f

/-- Object-facing characterization of an admissible factorization. -/
theorem isAdmissible_iff {X Y : C} (f : X ⟶ Y) :
    E.IsAdmissible f ↔ ∃ (I : C) (p : X ⟶ I) (i : I ⟶ Y),
      E.IsDeflation p ∧ E.IsInflation i ∧ p ≫ i = f := by
  constructor
  · rintro ⟨h⟩
    exact ⟨h.Z, h.i, h.p, h.hi, h.hp, h.fac⟩
  · rintro ⟨I, p, i, hp, hi, h⟩
    exact ⟨⟨I, p, i, h, hp, hi⟩⟩

variable {E}

/-- A deflation followed by an inflation is admissible. -/
theorem isAdmissible_comp {X I Y : C} {p : X ⟶ I} {i : I ⟶ Y}
    (hp : E.IsDeflation p) (hi : E.IsInflation i) : E.IsAdmissible (p ≫ i) :=
  (E.isAdmissible_iff _).2 ⟨I, p, i, hp, hi, rfl⟩

/-- Every inflation is admissible. -/
theorem isAdmissible_of_isInflation {X Y : C} {i : X ⟶ Y} (hi : E.IsInflation i) :
    E.IsAdmissible i := by
  simpa using isAdmissible_comp (E.isDeflation_id X) hi

/-- Every deflation is admissible. -/
theorem isAdmissible_of_isDeflation {X Y : C} {p : X ⟶ Y} (hp : E.IsDeflation p) :
    E.IsAdmissible p := by
  simpa using isAdmissible_comp hp (E.isInflation_id Y)

/-- Precomposing an admissible morphism with a deflation preserves admissibility. -/
theorem IsAdmissible.precomp_deflation {W X Y : C} {f : X ⟶ Y}
    (hf : E.IsAdmissible f) {p : W ⟶ X} (hp : E.IsDeflation p) :
    E.IsAdmissible (p ≫ f) := by
  obtain ⟨I, q, i, hq, hi, rfl⟩ := (E.isAdmissible_iff _).1 hf
  simpa only [Category.assoc] using isAdmissible_comp (E.isDeflation_comp p q hp hq) hi

/-- Postcomposing an admissible morphism with an inflation preserves admissibility. -/
theorem IsAdmissible.postcomp_inflation {X Y Z : C} {f : X ⟶ Y}
    (hf : E.IsAdmissible f) {i : Y ⟶ Z} (hi : E.IsInflation i) :
    E.IsAdmissible (f ≫ i) := by
  obtain ⟨I, p, j, hp, hj, rfl⟩ := (E.isAdmissible_iff _).1 hf
  simpa only [Category.assoc] using isAdmissible_comp hp (E.isInflation_comp j i hj hi)

instance : E.admissibles.ContainsIdentities where
  id_mem X := isAdmissible_of_isInflation (E.isInflation_id X)

instance : E.admissibles.RespectsIso := by
  apply MorphismProperty.RespectsIso.mk
  · intro X Y Z e f hf
    exact IsAdmissible.precomp_deflation hf (E.deflations.of_isIso e.hom)
  · intro X Y Z e f hf
    exact IsAdmissible.postcomp_inflation hf (E.inflations.of_isIso e.hom)

/-- Every zero morphism is admissible, through the zero object. -/
@[simp]
theorem isAdmissible_zero (X Y : C) : E.IsAdmissible (0 : X ⟶ Y) := by
  have hp := E.toConflationClass.isDeflation_g (E.conflation_id_zero X)
  have hi := E.toConflationClass.isInflation_f (E.conflation_zero_id Y)
  simpa using isAdmissible_comp hp hi

/-- Admissibility is self-dual: reversing a factorization exchanges its two admissible maps. -/
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
    obtain ⟨I, p, i, hp, hi, h⟩ := (E.isAdmissible_iff _).1 hf
    exact (E.op.isAdmissible_iff _).2 ⟨Opposite.op I, i.op, p.op,
      (E.op_isDeflation_iff i.op).2 hi, (E.op_isInflation_iff p.op).2 hp,
      by simpa using congrArg Quiver.Hom.op h⟩

/-- Among monomorphisms, the admissible morphisms are exactly the inflations. -/
theorem isAdmissible_iff_isInflation {X Y : C} (f : X ⟶ Y) [Mono f] :
    E.IsAdmissible f ↔ E.IsInflation f := by
  refine ⟨?_, isAdmissible_of_isInflation⟩
  intro hf
  obtain ⟨I, p, i, hp, hi, h⟩ := (E.isAdmissible_iff f).1 hf
  have : Mono (p ≫ i) := h.symm ▸ inferInstance
  have : Mono p := mono_of_mono p i
  have : IsRegularEpi p := hp.isRegularEpi
  have : IsIso p := isIso_of_mono_of_strongEpi p
  rw [← h]
  exact MorphismProperty.RespectsIso.precomp E.inflations p i hi

/-- Among epimorphisms, the admissible morphisms are exactly the deflations. -/
theorem isAdmissible_iff_isDeflation {X Y : C} (f : X ⟶ Y) [Epi f] :
    E.IsAdmissible f ↔ E.IsDeflation f := by
  simpa using (E.op.isAdmissible_iff_isInflation f.op)

/-- Two admissible factorizations of the same map have a unique compatible intermediate
isomorphism. In particular, admissibility supplies an image object independent of the chosen
factorization. -/
theorem existsUnique_admissibleFactorization_iso {X Y I J : C}
    {p : X ⟶ I} {i : I ⟶ Y} {q : X ⟶ J} {j : J ⟶ Y}
    (hp : E.IsDeflation p) (hi : E.IsInflation i)
    (hq : E.IsDeflation q) (hj : E.IsInflation j) (h : p ≫ i = q ≫ j) :
    ∃! e : I ≅ J, p ≫ e.hom = q ∧ e.hom ≫ j = i := by
  have : Mono i := hi.mono
  have : Mono j := hj.mono
  have : IsRegularEpi p := hp.isRegularEpi
  have : IsRegularEpi q := hq.isRegularEpi
  let F : StrongEpiMonoFactorisation (p ≫ i) := { I := I, e := p, m := i }
  let G : StrongEpiMonoFactorisation (p ≫ i) := { I := J, e := q, m := j, fac := h.symm }
  let e := IsImage.isoExt F.toMonoIsImage G.toMonoIsImage
  refine ⟨e, ⟨IsImage.e_isoExt_hom F.toMonoIsImage G.toMonoIsImage,
    IsImage.isoExt_hom_m F.toMonoIsImage G.toMonoIsImage⟩, ?_⟩
  rintro e' ⟨he', -⟩
  apply Iso.ext
  exact (cancel_epi p).1
    (he'.trans (IsImage.e_isoExt_hom F.toMonoIsImage G.toMonoIsImage).symm)

section Functor

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D] {E' : ExactStructure D} {F : C ⥤ D} [F.Additive]

/-- A conflation-exact functor preserves admissible morphisms. -/
theorem IsConflationExact.map_isAdmissible (hF : E.IsConflationExact E' F)
    {X Y : C} {f : X ⟶ Y} (hf : E.IsAdmissible f) : E'.IsAdmissible (F.map f) := by
  obtain ⟨I, p, i, hp, hi, rfl⟩ := (E.isAdmissible_iff f).1 hf
  rw [F.map_comp]
  exact isAdmissible_comp (hF.map_isDeflation hp) (hF.map_isInflation hi)

end Functor

section Abelian

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Every morphism is admissible for the canonical abelian exact structure, using its usual
image factorization. This need not hold for other exact structures on an abelian category. -/
@[simp]
theorem abelian_isAdmissible {X Y : A} (f : X ⟶ Y) : (abelian A).IsAdmissible f := by
  exact ((abelian A).isAdmissible_iff f).2 ⟨image f, factorThruImage f, image.ι f,
    (abelian_isDeflation_iff _).2 inferInstance,
    (abelian_isInflation_iff _).2 inferInstance, image.fac f⟩

end Abelian

end ExactStructure

end TauCeti
