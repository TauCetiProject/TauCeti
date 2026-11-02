/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TensorProduct.Pair

/-!
# Completed pushouts of Huber pairs

A completed pushout represents compatible morphisms into complete Hausdorff Huber pairs.
The outgoing morphisms need only be continuous and preserve integral elements; they need not
be adic. This diagram-level interface lets one use the completed tensor product without
choosing algebra structures on the two factors.

`IsCompletedPushout` records this universal property, and `exists_isCompletedPushout` constructs
such a square along any two adic morphisms. The construction uses the existing completed
tensor pair, with adic coprojections and dense algebraic tensors. No uniformisation or
sheafiness assumption is involved. The input rings need not themselves be complete.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §3, proof of Proposition 3.7 and Lemma 3.9(i).
* S. Morel, *Adic spaces*, §II.3.2, Proposition II.3.2.1.
-/

public section

open Topology TensorProduct

namespace TauCeti.Huber

universe u

variable {A B C E : Type u}
  [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
  [CommRing E] [TopologicalSpace E] [IsTopologicalRing E] [IsHuberRing E]
  {S : Pair A} {T : Pair B} {U : Pair C} {W : Pair E}

/-- A commuting square of Huber pairs is a *completed pushout* if compatible morphisms into
any complete Hausdorff Huber pair factor uniquely through its bottom-right vertex.
Completeness of the vertices is not part of this predicate. -/
structure IsCompletedPushout (f : Pair.Hom S T) (g : Pair.Hom S U)
    (i : Pair.Hom T W) (j : Pair.Hom U W) : Prop where
  /-- The two composites from the base agree. -/
  condition : i.comp f = j.comp g
  /-- Compatible maps into a complete pair have a unique common extension. -/
  existsUnique_desc : ∀ (D : Type u) [CommRing D] [UniformSpace D] [IsUniformAddGroup D]
    [IsTopologicalRing D] [IsHuberRing D] [CompleteSpace D] [T2Space D]
    (V : Pair D) (a : Pair.Hom T V) (b : Pair.Hom U V), a.comp f = b.comp g →
      ∃! h : Pair.Hom W V, h.comp i = a ∧ h.comp j = b

namespace IsCompletedPushout

variable {f : Pair.Hom S T} {g : Pair.Hom S U} {i : Pair.Hom T W} {j : Pair.Hom U W}
  (h : IsCompletedPushout f g i j)
  {D : Type u} [CommRing D] [UniformSpace D] [IsUniformAddGroup D]
  [IsTopologicalRing D] [IsHuberRing D] [CompleteSpace D] [T2Space D] {V : Pair D}

/-- The common extension of two compatible morphisms into a complete Hausdorff pair. -/
noncomputable def desc (a : Pair.Hom T V) (b : Pair.Hom U V) (hab : a.comp f = b.comp g) :
    Pair.Hom W V :=
  (h.existsUnique_desc D V a b hab).choose

/-- The common extension restricts to the prescribed map on the first factor. -/
@[simp]
theorem desc_comp_left (a : Pair.Hom T V) (b : Pair.Hom U V) (hab : a.comp f = b.comp g) :
    (h.desc a b hab).comp i = a :=
  (h.existsUnique_desc D V a b hab).choose_spec.1.1

/-- The common extension restricts to the prescribed map on the second factor. -/
@[simp]
theorem desc_comp_right (a : Pair.Hom T V) (b : Pair.Hom U V) (hab : a.comp f = b.comp g) :
    (h.desc a b hab).comp j = b :=
  (h.existsUnique_desc D V a b hab).choose_spec.1.2

include h in
/-- Morphisms from a completed pushout into a complete Hausdorff pair are determined by
their restrictions to the two factors. -/
theorem hom_ext {a b : Pair.Hom W V} (hi : a.comp i = b.comp i)
    (hj : a.comp j = b.comp j) : a = b := by
  have hab : (b.comp i).comp f = (b.comp j).comp g := by
    simp only [Pair.Hom.comp_assoc, h.condition]
  exact (h.existsUnique_desc D V (b.comp i) (b.comp j) hab).unique ⟨hi, hj⟩ ⟨rfl, rfl⟩

end IsCompletedPushout

/-- The existing completed tensor pair is a completed pushout of any compatible base pair.
The target maps in its universal property are not required to be adic. -/
theorem Pair.completedTensor.isCompletedPushout [Algebra A B] [Algebra A C]
    [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]
    (f : Pair.Hom S T) (g : Pair.Hom S U)
    (hf : f.toRingHom = algebraMap A B) (hg : g.toRingHom = algebraMap A C) :
    IsCompletedPushout f g (Pair.completedTensor.inl A T U) (Pair.completedTensor.inr A T U) where
  condition := Pair.completedTensor.inl_comp hf hg
  existsUnique_desc D _ _ _ _ _ _ _ V a b hab := by
    have hab' : a.toRingHom.comp (algebraMap A B) =
        b.toRingHom.comp (algebraMap A C) := by
      simpa [hf, hg] using congrArg Pair.Hom.toRingHom hab
    refine ⟨Pair.completedTensor.lift a b hab', ⟨by simp, by simp⟩, ?_⟩
    rintro χ ⟨hχi, hχj⟩
    exact Pair.completedTensor.hom_ext (by simpa using hχi) (by simpa using hχj)

/-- Adic morphisms of Huber pairs admit a completed pushout with adic coprojections and
dense subring generated by the two factors. Its ring is complete and Hausdorff; neither
completeness of the inputs nor adicness of outgoing maps is required. -/
theorem exists_isCompletedPushout (f : Pair.Hom S T) (g : Pair.Hom S U)
    [IsAdicHom f.toRingHom] [IsAdicHom g.toRingHom] :
    ∃ (E : Type u) (_ : CommRing E) (_ : UniformSpace E) (_ : IsUniformAddGroup E)
      (_ : IsTopologicalRing E) (_ : IsHuberRing E) (_ : CompleteSpace E) (_ : T2Space E)
      (W : Pair E) (i : Pair.Hom T W) (j : Pair.Hom U W),
      IsCompletedPushout f g i j ∧ IsAdicHom i.toRingHom ∧ IsAdicHom j.toRingHom ∧
        Dense (Subring.closure (Set.range i.toRingHom ∪ Set.range j.toRingHom) : Set E) := by
  let := f.toRingHom.toAlgebra
  let := g.toRingHom.toAlgebra
  refine ⟨CompletedTensor A B C, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, T.completedTensor A U,
    Pair.completedTensor.inl A T U, Pair.completedTensor.inr A T U,
    Pair.completedTensor.isCompletedPushout f g (RingHom.algebraMap_toAlgebra f.toRingHom)
      (RingHom.algebraMap_toAlgebra g.toRingHom), ?_, ?_, ?_⟩
  · simpa using CompletedTensor.isAdicHom_inl A B C
  · simpa using CompletedTensor.isAdicHom_inr A B C
  apply (CompletedTensor.denseRange_toCompletion A B C).mono
  rintro _ ⟨x, rfl⟩
  have hm := Subring.mem_closure_image_of (CompletedTensor.toCompletion A B C)
    (s := Set.range (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] C) ∪
      Set.range (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C))
    (x := x) (by rw [Algebra.TensorProduct.closure_range_union_range_eq_top]; trivial)
  have hleft : (CompletedTensor.toCompletion A B C) ∘
      (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] C) = CompletedTensor.inl A B C := by
    funext b
    simp
  have hright : (CompletedTensor.toCompletion A B C) ∘
      (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C) = CompletedTensor.inr A B C := by
    funext c
    simp
  simpa only [SetLike.mem_coe, Set.image_union, ← Set.range_comp, hleft, hright,
    Pair.completedTensor.toRingHom_inl, Pair.completedTensor.toRingHom_inr] using hm

end TauCeti.Huber
