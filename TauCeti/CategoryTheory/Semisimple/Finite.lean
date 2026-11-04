/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Semisimple.Multiplicity
public import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Finiteness of simple classes

A finite family of objects in a finite semisimple category detects only finitely many simple
classes. Consequently, if every simple object maps nontrivially to some member of that family,
there are finitely many simple classes in the whole category.

A faithful left adjoint between finite semisimple categories supplies such a family:
apply its right adjoint to the simple representatives of the target. Every simple object of
the source has nonzero image, which maps nontrivially to a simple object of the target; the
adjunction transposes this to a nonzero map into one of the right-adjoint images. Thus finiteness
of simple classes in the target implies finiteness in the source. This applies, in particular,
to forgetful functors from Drinfeld centres once their right adjoints and semisimplicity have
been established. Neither linearity over a field nor split endomorphism division rings is needed.

## Main results

* `TauCeti.finite_simpleClasses_of_detecting_family`: a finite family detecting every simple
  object forces finiteness of simple classes.
* `CategoryTheory.Functor.finite_simpleClasses_of_faithful_leftAdjoint`: finiteness transfers
  along a faithful left adjoint between finite semisimple categories.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §§1.8, 9.3.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti

universe v v' u u'

variable {C : Type u} [Category.{v} C] [Abelian C] [IsFiniteSemisimpleCategory C]

/-- A finite family receiving a nonzero morphism from every simple object forces finiteness
of the simple isomorphism classes. -/
theorem finite_simpleClasses_of_detecting_family {ι : Type*} [Finite ι] (X : ι → C)
    (h : ∀ (S : C) [Simple S], ∃ i, ∃ f : S ⟶ X i, f ≠ 0) :
    Finite (SimpleClasses C) := by
  classical
  let := Fintype.ofFinite ι
  let s := Finset.univ.biUnion fun i ↦ (simpleMultiplicities (X i)).support
  have hs (S : SimpleClasses C) : S ∈ s := by
    obtain ⟨i, f, hf⟩ := h S.repr
    have hm := (simpleMultiplicities_classOf_ne_zero_iff (X i) S.repr).2 ⟨f, hf⟩
    apply Finset.mem_biUnion.mpr
    exact ⟨i, Finset.mem_univ i, Finsupp.mem_support_iff.mpr (by simpa using hm)⟩
  exact Finite.of_injective (fun S : SimpleClasses C ↦ (⟨S, hs S⟩ : ↥s))
    (fun _ _ h ↦ congrArg Subtype.val h)

end TauCeti

namespace CategoryTheory.Functor

open TauCeti

universe v v' u u'

variable {C : Type u} [Category.{v} C] [Abelian C] [IsFiniteSemisimpleCategory C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [IsFiniteSemisimpleCategory D]

/-- A faithful left adjoint between finite semisimple categories transfers finiteness
of simple classes from its target to its source. The detecting objects are the right-adjoint
images of the target's simple representatives. -/
theorem finite_simpleClasses_of_faithful_leftAdjoint (F : C ⥤ D) [F.Faithful]
    {G : D ⥤ C} (adj : F ⊣ G) [Finite (SimpleClasses D)] : Finite (SimpleClasses C) := by
  have := adj.isLeftAdjoint
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  have := F.additive_of_preservesBinaryBiproducts
  apply finite_simpleClasses_of_detecting_family (fun T : SimpleClasses D ↦ G.obj T.repr)
  intro S _
  have hS : ¬IsZero (F.obj S) := by
    intro h
    apply CategoryTheory.id_ne_zero S
    exact F.map_injective (h.eq_of_src (F.map (𝟙 S)) (F.map (0 : S ⟶ S)))
  obtain ⟨T, hT, f, hf⟩ := exists_simple_hom_ne_zero hS
  obtain ⟨g, hg⟩ := exists_nonzero_from_simple_iff_exists_nonzero_to_simple.mp ⟨f, hf⟩
  let e := SimpleClasses.classOfReprIso T
  have hg' : g ≫ e.inv ≠ 0 := by simpa using hg
  refine ⟨SimpleClasses.classOf T, adj.homEquiv S _ (g ≫ e.inv), ?_⟩
  exact fun h ↦ hg' ((adj.homEquiv S _).injective (h.trans (adj.homAddEquiv_zero S _).symm))

end CategoryTheory.Functor
