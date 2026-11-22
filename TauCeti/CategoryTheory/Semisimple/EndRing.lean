/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Linear.Basic
public import TauCeti.CategoryTheory.Semisimple.Basic
import TauCeti.CategoryTheory.Linear.Endomorphism
import TauCeti.CategoryTheory.Preadditive.KrullSchmidt.Semiperfect
import TauCeti.RingTheory.Semisimple.Regular

/-!
# Finite semisimplicity from endomorphism rings

Let `C` be an additive category in which idempotents split. If the endomorphism ring of every
object is semisimple, then `C` is abelian, with the given addition of morphisms
(`TauCeti.abelianOfIsSemisimpleRingEnd`), and every object is a finite biproduct of simple objects
(`TauCeti.exists_biproduct_simples_of_isSemisimpleRing_end`), so `C` is a finite semisimple
category (`TauCeti.isFiniteSemisimpleCategory_abelianOfIsSemisimpleRingEnd`). Conversely, in an
abelian category in which monomorphisms split, for instance a finite semisimple one, an object with
Artinian endomorphism ring has a semisimple endomorphism ring
(`TauCeti.isSemisimpleRing_end_of_splitMonoCategory`).

This is Jannsen's criterion: it is how one shows that a category of motives modulo numerical
equivalence is abelian and semisimple, knowing only that its endomorphism algebras are
finite-dimensional and semisimple.

The construction rests on von Neumann regularity. A semisimple ring has `a * b * a = a` for some
`b` given any `a`, so every morphism `f : X ⟶ Y` has some `g : Y ⟶ X` with `f ≫ g ≫ f = f`
(`TauCeti.exists_comp_comp_eq_self_of_isSemisimpleRing_end`, applied in the endomorphism ring of
`X ⊞ Y`). Then `𝟙 X - f ≫ g` and `𝟙 Y - g ≫ f` are idempotents, and their splittings are a kernel
and a cokernel of `f` (`TauCeti.hasKernel_of_comp_comp_eq_self`,
`TauCeti.hasCokernel_of_comp_comp_eq_self`). The comparison from the coimage to the image of `f`
has inverse induced by `g` (`TauCeti.isIso_coimageImageComparison_of_comp_comp_eq_self`).

For the decomposition, a nonzero object with no idempotent endomorphism besides `0` and `𝟙` is
simple, because a nonzero monomorphism `f` into it with `f ≫ g ≫ f = f` has the idempotent
`g ≫ f`, which must be `𝟙` (`TauCeti.simple_of_idempotent_eq_zero_or_id`). Semisimple rings are
semiperfect, so the category is Krull–Schmidt, and its indecomposable summands, having local
endomorphism rings, are simple.

## Main results

* `TauCeti.abelianOfIsSemisimpleRingEnd`: an additive category with split idempotents and
  semisimple endomorphism rings is abelian.
* `TauCeti.exists_biproduct_simples_of_isSemisimpleRing_end`: every object of such a category is a
  finite biproduct of simple objects.
* `TauCeti.isFiniteSemisimpleCategory_abelianOfIsSemisimpleRingEnd`: Jannsen's criterion.
* `TauCeti.isFiniteSemisimpleCategory_iff_isSemisimpleRing_end`: an abelian category linear over an
  Artinian ring with finitely generated endomorphism modules is finite semisimple if and only if its
  endomorphism rings are semisimple.

## References

* U. Jannsen, *Motives, numerical equivalence, and semi-simplicity*, Invent. Math. **107** (1992),
  447–452, Lemma 2.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C]

/-- **A nonzero object whose only idempotent endomorphisms are `0` and `𝟙` is simple**, when every
monomorphism `f` into it has some `g` with `f ≫ g ≫ f = f`. -/
theorem simple_of_idempotent_eq_zero_or_id [HasZeroMorphisms C] {X : C} (hX : ¬ IsZero X)
    (h : ∀ e : X ⟶ X, e ≫ e = e → e = 0 ∨ e = 𝟙 X)
    (hreg : ∀ ⦃Y : C⦄ (f : Y ⟶ X), Mono f → ∃ g : X ⟶ Y, f ≫ g ≫ f = f) : Simple X where
  mono_isIso_iff_nonzero {Y} f _ := by
    refine ⟨fun _ h0 ↦ hX ?_, fun hf ↦ ?_⟩
    · obtain rfl := h0
      rw [IsZero.iff_id_eq_zero, ← IsIso.inv_hom_id (0 : Y ⟶ X), comp_zero]
    obtain ⟨g, hg⟩ := hreg f inferInstance
    have hfg : f ≫ g = 𝟙 Y := by rw [← cancel_mono f, Category.assoc, hg, Category.id_comp]
    rcases h (g ≫ f) (by rw [Category.assoc, reassoc_of% hfg]) with h0 | h1
    · exact absurd (by rw [← hg, h0, comp_zero]) hf
    · exact ⟨⟨g, hfg, h1⟩⟩

section Preadditive

variable [Preadditive C]

/-- **Semisimple endomorphism rings make morphisms von Neumann regular**: if the endomorphism ring
of `X ⊞ Y` is semisimple, every morphism `f : X ⟶ Y` has some `g` with `f ≫ g ≫ f = f`. -/
theorem exists_comp_comp_eq_self_of_isSemisimpleRing_end {X Y : C} [HasBinaryBiproduct X Y]
    [IsSemisimpleRing (End (X ⊞ Y))] (f : X ⟶ Y) : ∃ g : Y ⟶ X, f ≫ g ≫ f = f := by
  obtain ⟨φ, hφ⟩ := IsSemisimpleRing.exists_mul_mul_eq_self (End.of (biprod.fst ≫ f ≫ biprod.inr))
  refine ⟨biprod.inr ≫ φ.asHom ≫ biprod.fst, ?_⟩
  simpa using congrArg (fun ψ : End (X ⊞ Y) ↦ biprod.inl ≫ ψ.asHom ≫ biprod.snd) hφ

section Kernels

variable [IsIdempotentComplete C] {X Y : C} {f : X ⟶ Y} {g : Y ⟶ X}

/-- If `f ≫ g ≫ f = f`, then `f` has a kernel, a splitting of the idempotent `𝟙 X - f ≫ g`. -/
theorem hasKernel_of_comp_comp_eq_self (h : f ≫ g ≫ f = f) : HasKernel f := by
  obtain ⟨K, i, r, hir, hri⟩ := IsIdempotentComplete.idempotents_split X (𝟙 X - f ≫ g) (by
    simp [Preadditive.sub_comp, Preadditive.comp_sub, reassoc_of% h])
  have : IsSplitMono i := ⟨⟨r, hir⟩⟩
  have hi : i ≫ f = 0 := by
    rw [← Category.id_comp i, ← hir, Category.assoc, Category.assoc, reassoc_of% hri]
    simp [Preadditive.sub_comp, h]
  exact ⟨⟨⟨KernelFork.ofι i hi, KernelFork.IsLimit.ofι' i hi fun a ha ↦
    ⟨a ≫ r, by simp [hri, Preadditive.comp_sub, reassoc_of% ha]⟩⟩⟩⟩

/-- If `f ≫ g ≫ f = f`, then `f` has a cokernel, a splitting of the idempotent `𝟙 Y - g ≫ f`. -/
theorem hasCokernel_of_comp_comp_eq_self (h : f ≫ g ≫ f = f) : HasCokernel f := by
  obtain ⟨Q, s, e, hse, hes⟩ := IsIdempotentComplete.idempotents_split Y (𝟙 Y - g ≫ f) (by
    simp [Preadditive.sub_comp, Preadditive.comp_sub, h])
  have : IsSplitEpi e := ⟨⟨s, hse⟩⟩
  have he : f ≫ e = 0 := by
    rw [← Category.comp_id e, ← hse, ← Category.assoc e s e, hes]
    simp [Preadditive.comp_sub, reassoc_of% h]
  exact ⟨⟨⟨CokernelCofork.ofπ e he, CokernelCofork.IsColimit.ofπ' e he fun a ha ↦
    ⟨s ≫ a, by simp [reassoc_of% hes, Preadditive.sub_comp, ha]⟩⟩⟩⟩

end Kernels

/-- If `f ≫ g ≫ f = f`, the comparison from the coimage of `f` to its image is an isomorphism,
with inverse induced by `g`. -/
theorem isIso_coimageImageComparison_of_comp_comp_eq_self {X Y : C} {f : X ⟶ Y} {g : Y ⟶ X}
    [HasKernel f] [HasCokernel f] [HasKernel (cokernel.π f)] [HasCokernel (kernel.ι f)]
    (h : f ≫ g ≫ f = f) : IsIso (Abelian.coimageImageComparison f) := by
  -- `𝟙 X - f ≫ g` factors through the kernel of `f`, so `f ≫ g` fixes the coimage of `f`.
  have hπ : f ≫ g ≫ Abelian.coimage.π f = Abelian.coimage.π f := by
    have hk := kernel.lift_ι f (𝟙 X - f ≫ g) (by simp [Preadditive.sub_comp, h])
    have h0 : (𝟙 X - f ≫ g) ≫ Abelian.coimage.π f = 0 := by
      rw [← hk, Category.assoc, cokernel.condition, comp_zero]
    rwa [Preadditive.sub_comp, Category.id_comp, sub_eq_zero, eq_comm, Category.assoc] at h0
  -- Dually `𝟙 Y - g ≫ f` factors through the cokernel of `f`, so `g ≫ f` fixes its image.
  have hι : Abelian.image.ι f ≫ g ≫ f = Abelian.image.ι f := by
    have hc := cokernel.π_desc f (𝟙 Y - g ≫ f) (by simp [Preadditive.comp_sub, h])
    have h0 : Abelian.image.ι f ≫ (𝟙 Y - g ≫ f) = 0 := by
      rw [← hc, ← Category.assoc, kernel.condition, zero_comp]
    rwa [Preadditive.comp_sub, Category.comp_id, sub_eq_zero, eq_comm] at h0
  refine ⟨⟨Abelian.image.ι f ≫ g ≫ Abelian.coimage.π f, ?_, ?_⟩⟩
  · exact (cancel_epi (Abelian.coimage.π f)).1 (by simpa using hπ)
  · exact (cancel_mono (Abelian.image.ι f)).1 (by simpa using hι)


/-- **Jannsen's decomposition**: in an additive category with split idempotents and semisimple
endomorphism rings, every object is a finite biproduct of simple objects. Semisimple rings are
semiperfect, so the category is Krull–Schmidt (`TauCeti.isKrullSchmidt_of_isSemiperfectRing_end`),
and a summand with local endomorphism ring has only the trivial idempotents, so it is simple. -/
theorem exists_biproduct_simples_of_isSemisimpleRing_end [HasFiniteBiproducts C]
    [IsIdempotentComplete C] [∀ X : C, IsSemisimpleRing (End X)] (X : C) :
    ∃ (ι : Type) (_ : Fintype ι) (f : ι → C) (_ : ∀ i, Simple (f i)) (_ : HasBiproduct f),
      Nonempty (X ≅ ⨁ f) := by
  have := hasBinaryBiproducts_of_finite_biproducts C
  have := isKrullSchmidt_of_isSemiperfectRing_end (C := C) fun _ ↦ inferInstance
  obtain ⟨n, P, hP, e⟩ := IsKrullSchmidt.exists_iso_biproduct X
  refine ⟨Fin n, inferInstance, P, fun i ↦ ?_, inferInstance, e⟩
  have := hP i
  exact simple_of_idempotent_eq_zero_or_id indecomposable_of_isLocalRing_end.1
    (fun p hp ↦ (IsIdempotentElem.eq_zero_or_eq_one_of_isLocalRing
      (a := End.of p) (End.ext (by simpa using hp))).imp (congrArg End.asHom) (congrArg End.asHom))
    fun _ f _ ↦ exists_comp_comp_eq_self_of_isSemisimpleRing_end f

variable (C) in
/-- **An additive category with split idempotents and semisimple endomorphism rings is abelian.**
The abelian structure has the given addition of morphisms
(`TauCeti.abelianOfIsSemisimpleRingEnd_toPreadditive`). Its body is exposed so that this
agreement holds by unfolding, which is what lets instances stated over the given preadditive
structure, such as a linear structure, be used together with it. -/
@[expose, instance_reducible]
def abelianOfIsSemisimpleRingEnd [HasFiniteBiproducts C] [IsIdempotentComplete C]
    [∀ X : C, IsSemisimpleRing (End X)] : Abelian C :=
  have : HasBinaryBiproducts C := hasBinaryBiproducts_of_finite_biproducts C
  have : HasKernels C := ⟨fun f ↦ (exists_comp_comp_eq_self_of_isSemisimpleRing_end f).elim
    fun _ h ↦ hasKernel_of_comp_comp_eq_self h⟩
  have : HasCokernels C := ⟨fun f ↦ (exists_comp_comp_eq_self_of_isSemisimpleRing_end f).elim
    fun _ h ↦ hasCokernel_of_comp_comp_eq_self h⟩
  have (X Y : C) (f : X ⟶ Y) : IsIso (Abelian.coimageImageComparison f) :=
    (exists_comp_comp_eq_self_of_isSemisimpleRing_end f).elim
      fun _ h ↦ isIso_coimageImageComparison_of_comp_comp_eq_self h
  Abelian.ofCoimageImageComparisonIsIso

/-- The abelian structure `TauCeti.abelianOfIsSemisimpleRingEnd` has the given addition of
morphisms. -/
theorem abelianOfIsSemisimpleRingEnd_toPreadditive [HasFiniteBiproducts C]
    [IsIdempotentComplete C] [∀ X : C, IsSemisimpleRing (End X)] :
    (abelianOfIsSemisimpleRingEnd C).toPreadditive = ‹Preadditive C› :=
  rfl

end Preadditive

section Abelian

variable [Abelian C]

/-- **In an abelian category where monomorphisms split, morphisms are von Neumann regular**:
every `f : X ⟶ Y` has some `g` with `f ≫ g ≫ f = f`. -/
theorem exists_comp_comp_eq_self_of_splitMonoCategory [SplitMonoCategory C] {X Y : C}
    (f : X ⟶ Y) : ∃ g : Y ⟶ X, f ≫ g ≫ f = f := by
  -- A retraction of the kernel of `f` gives a section `s` of its coimage, and a retraction of the
  -- image of `f` gives the rest.
  have := isSplitMono_of_mono (kernel.ι f)
  have := isSplitMono_of_mono (Abelian.image.ι f)
  let s : Abelian.coimage f ⟶ X := cokernel.desc (kernel.ι f)
    (𝟙 X - retraction (kernel.ι f) ≫ kernel.ι f) (by simp [Preadditive.comp_sub])
  have hf : Abelian.coimage.π f ≫ Abelian.coimageImageComparison f =
      f ≫ retraction (Abelian.image.ι f) := by
    simpa using Abelian.coimage_image_factorisation_assoc f (retraction (Abelian.image.ι f))
  refine ⟨retraction (Abelian.image.ι f) ≫ inv (Abelian.coimageImageComparison f) ≫ s, ?_⟩
  rw [Category.assoc, Category.assoc, ← Category.assoc f (retraction _), ← hf]
  simp [s, Preadditive.sub_comp]

/-- **An abelian category with semisimple endomorphism rings is finite semisimple.** -/
theorem IsFiniteSemisimpleCategory.of_isSemisimpleRing_end [∀ X : C, IsSemisimpleRing (End X)] :
    IsFiniteSemisimpleCategory C :=
  have := Abelian.hasFiniteBiproducts (C := C)
  ⟨exists_biproduct_simples_of_isSemisimpleRing_end⟩

/-- **Artinian endomorphism rings in an abelian category where monomorphisms split are
semisimple.** This applies in particular to a finite semisimple category
(`TauCeti.IsFiniteSemisimpleCategory.splitMonoCategory`). -/
theorem isSemisimpleRing_end_of_splitMonoCategory [SplitMonoCategory C] (X : C)
    [IsArtinianRing (End X)] : IsSemisimpleRing (End X) := by
  refine IsArtinianRing.isSemisimpleRing_of_forall_exists_mul_mul_eq_self fun a ↦ ?_
  obtain ⟨g, hg⟩ := exists_comp_comp_eq_self_of_splitMonoCategory a.asHom
  exact ⟨End.of g, End.ext (by simpa using hg)⟩

/-- **An abelian category linear over an Artinian ring, with finitely generated endomorphism
modules, is finite semisimple if and only if its endomorphism rings are semisimple.** This covers
finite-dimensional endomorphism spaces over a division ring. -/
theorem isFiniteSemisimpleCategory_iff_isSemisimpleRing_end (K : Type*) [Ring K] [IsArtinianRing K]
    [Linear K C] [∀ X : C, Module.Finite K (X ⟶ X)] :
    IsFiniteSemisimpleCategory C ↔ ∀ X : C, IsSemisimpleRing (End X) := by
  refine ⟨fun _ X ↦ ?_, fun _ ↦ IsFiniteSemisimpleCategory.of_isSemisimpleRing_end⟩
  have : Module.Finite K (End X) := Module.Finite.equiv (End.linearEquiv (R := K)).symm
  have : IsArtinianRing (End X) := IsArtinianRing.of_finite K (End X)
  exact isSemisimpleRing_end_of_splitMonoCategory X

end Abelian

/-- **Jannsen's criterion.** Let `C` be an additive category in which idempotents split. If every
endomorphism ring is semisimple, then `C` is abelian with the given addition
(`TauCeti.abelianOfIsSemisimpleRingEnd`), and every object is a finite biproduct of simple
objects. -/
theorem isFiniteSemisimpleCategory_abelianOfIsSemisimpleRingEnd [Preadditive C]
    [HasFiniteBiproducts C] [IsIdempotentComplete C] [∀ X : C, IsSemisimpleRing (End X)] :
    letI := abelianOfIsSemisimpleRingEnd C
    IsFiniteSemisimpleCategory C :=
  letI := abelianOfIsSemisimpleRingEnd C
  IsFiniteSemisimpleCategory.of_isSemisimpleRing_end


end TauCeti
