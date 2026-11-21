/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Linear.Basic
public import TauCeti.CategoryTheory.Semisimple.Basic
import TauCeti.CategoryTheory.Preadditive.Indecomposable
import TauCeti.RingTheory.Semisimple.Regular

/-!
# Finite semisimplicity from endomorphism rings

Let `C` be an additive category in which idempotents split. If the endomorphism ring of every
object is semisimple, then `C` is abelian, with the given addition of morphisms
(`TauCeti.abelianOfIsSemisimpleRingEnd`). If moreover `C` is linear over a division ring `K` and
endomorphism spaces are finite-dimensional, then every object is a finite biproduct of simple
objects (`TauCeti.exists_biproduct_simples_of_isSemisimpleRing_end`), so `C` is a finite
semisimple category (`TauCeti.isFiniteSemisimpleCategory_abelianOfIsSemisimpleRingEnd`).
Conversely, in a finite semisimple abelian category linear over a division ring, an object with
finite-dimensional endomorphisms has a semisimple endomorphism ring
(`TauCeti.IsFiniteSemisimpleCategory.isSemisimpleRing_end`).

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
`g ≫ f`, which must be `𝟙` (`TauCeti.simple_of_idempotent_eq_zero_or_id`). Any other object splits
along a nontrivial idempotent into two summands with endomorphism spaces of smaller dimension.

## Main results

* `TauCeti.abelianOfIsSemisimpleRingEnd`: an additive category with split idempotents and
  semisimple endomorphism rings is abelian.
* `TauCeti.exists_biproduct_simples_of_isSemisimpleRing_end`: an object of such a category with
  finite-dimensional endomorphisms is a finite biproduct of simple objects.
* `TauCeti.isFiniteSemisimpleCategory_abelianOfIsSemisimpleRingEnd`: Jannsen's criterion.
* `TauCeti.isFiniteSemisimpleCategory_iff_isSemisimpleRing_end`: an abelian category linear over a
  division ring with finite-dimensional endomorphism spaces is finite semisimple if and only if its
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


/-- **A proper retract has a smaller endomorphism space**: if `i ≫ r = 𝟙 Y` but `r ≫ i ≠ 𝟙 X`,
then `Y ⟶ Y` has smaller dimension than `X ⟶ X`. -/
theorem finrank_end_lt_of_comp_eq_id (K : Type*) [DivisionRing K] [Linear K C] {X Y : C}
    [FiniteDimensional K (X ⟶ X)] {i : Y ⟶ X} {r : X ⟶ Y} (hir : i ≫ r = 𝟙 Y)
    (hri : r ≫ i ≠ 𝟙 X) : Module.finrank K (Y ⟶ Y) < Module.finrank K (X ⟶ X) := by
  -- `h ↦ r ≫ h ≫ i` embeds `Y ⟶ Y` into `X ⟶ X`, and `𝟙 X` is not in its range.
  let L := (Linear.leftComp K X r).comp (Linear.rightComp K Y i)
  have hL : Function.Injective L := fun a b hab ↦ by
    simpa [L, reassoc_of% hir, hir] using congrArg (fun h ↦ i ≫ h ≫ r) hab
  rw [← LinearMap.finrank_range_of_inj hL]
  refine Submodule.finrank_lt fun htop ↦ hri ?_
  obtain ⟨a, ha⟩ := LinearMap.range_eq_top.1 htop (𝟙 X)
  simp only [L, LinearMap.coe_comp, Function.comp_apply, Linear.rightComp_apply,
    Linear.leftComp_apply] at ha
  rw [← Category.comp_id (r ≫ i), ← ha]
  simp [reassoc_of% hir]

/-- **Jannsen's decomposition**: in an additive category with split idempotents and semisimple
endomorphism rings, linear over a division ring `K`, an object with finite-dimensional
endomorphisms is a finite biproduct of simple objects. -/
theorem exists_biproduct_simples_of_isSemisimpleRing_end (K : Type*) [DivisionRing K] [Linear K C]
    [HasBinaryBiproducts C] [IsIdempotentComplete C] [∀ X : C, IsSemisimpleRing (End X)] (X : C)
    [FiniteDimensional K (X ⟶ X)] :
    ∃ (ι : Type) (_ : Fintype ι) (f : ι → C) (_ : ∀ i, Simple (f i)) (_ : HasBiproduct f),
      Nonempty (X ≅ ⨁ f) := by
  -- Strong induction on the dimension of `X ⟶ X`.
  induction hn : Module.finrank K (X ⟶ X) using Nat.strong_induction_on generalizing X with
  | _ n ih =>
  by_cases hX : IsZero X
  · exact IsFiniteSemisimpleCategory.exists_biproduct_simples_of_isZero hX
  by_cases hidem : ∀ e : X ⟶ X, e ≫ e = e → e = 0 ∨ e = 𝟙 X
  · have := simple_of_idempotent_eq_zero_or_id hX hidem fun _ f _ ↦
      exists_comp_comp_eq_self_of_isSemisimpleRing_end f
    exact IsFiniteSemisimpleCategory.exists_biproduct_simples_of_simple X
  -- Otherwise `X` splits along a nontrivial idempotent into two proper retracts.
  push Not at hidem
  obtain ⟨e, he, he0, he1⟩ := hidem
  have key {W : C} (i : W ⟶ X) (r : X ⟶ W) (hir : i ≫ r = 𝟙 W) (hri : r ≫ i ≠ 𝟙 X) :
      ∃ (ι : Type) (_ : Fintype ι) (f : ι → C) (_ : ∀ i, Simple (f i)) (_ : HasBiproduct f),
        Nonempty (W ≅ ⨁ f) := by
    have : FiniteDimensional K (W ⟶ W) :=
      Module.Finite.of_surjective ((Linear.leftComp K W i).comp (Linear.rightComp K X r))
        fun g ↦ ⟨r ≫ g ≫ i, by simp [reassoc_of% hir, hir]⟩
    exact ih _ (hn ▸ finrank_end_lt_of_comp_eq_id K hir hri) W rfl
  obtain ⟨Y, i₁, r₁, h₁, hr₁⟩ := IsIdempotentComplete.idempotents_split X e he
  obtain ⟨Z, i₂, r₂, h₂, hr₂⟩ := IsIdempotentComplete.idempotents_split X (𝟙 X - e) (by
    simp [Preadditive.sub_comp, Preadditive.comp_sub, he])
  have hsum : r₁ ≫ i₁ + r₂ ≫ i₂ = 𝟙 X := by rw [hr₁, hr₂]; abel
  obtain ⟨ι, _, f, hf, _, ⟨d⟩⟩ := IsFiniteSemisimpleCategory.exists_biproduct_simples_biprod
    (key i₁ r₁ h₁ (hr₁ ▸ he1)) (key i₂ r₂ h₂ (by rw [hr₂, Ne, sub_eq_self]; exact he0))
  exact ⟨ι, inferInstance, f, hf, inferInstance,
    ⟨isoBiprodOfRetracts i₁ r₁ i₂ r₂ h₁ h₂ hsum ≪≫ d⟩⟩

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

namespace IsFiniteSemisimpleCategory

/-- **An abelian category with semisimple, finite-dimensional endomorphism rings is finite
semisimple.** -/
theorem of_isSemisimpleRing_end (K : Type*) [DivisionRing K] [Linear K C]
    [∀ X : C, IsSemisimpleRing (End X)] [∀ X : C, FiniteDimensional K (X ⟶ X)] :
    IsFiniteSemisimpleCategory C :=
  have := Abelian.hasFiniteBiproducts (C := C)
  ⟨fun X ↦ exists_biproduct_simples_of_isSemisimpleRing_end K X⟩

/-- **Endomorphism rings in a finite semisimple category are semisimple**, for objects with
finite-dimensional endomorphisms over a division ring. -/
theorem isSemisimpleRing_end [IsFiniteSemisimpleCategory C] (K : Type*) [DivisionRing K]
    [Linear K C] (X : C) [FiniteDimensional K (X ⟶ X)] : IsSemisimpleRing (End X) := by
  have : Module.Finite K (End X) := Module.Finite.equiv (End.linearEquiv (R := K)).symm
  have : IsScalarTower K (End X) (End X) := ⟨fun k a b ↦ End.ext (by simp)⟩
  have : IsArtinianRing (End X) := IsArtinianRing.of_finite K (End X)
  refine IsArtinianRing.isSemisimpleRing_of_forall_exists_mul_mul_eq_self fun a ↦ ?_
  obtain ⟨g, hg⟩ := exists_comp_comp_eq_self_of_splitMonoCategory a.asHom
  exact ⟨End.of g, End.ext (by simpa using hg)⟩

end IsFiniteSemisimpleCategory

/-- **An abelian category with finite-dimensional endomorphism spaces over a division ring is
finite semisimple if and only if its endomorphism rings are semisimple.** -/
theorem isFiniteSemisimpleCategory_iff_isSemisimpleRing_end (K : Type*) [DivisionRing K]
    [Linear K C] [∀ X : C, FiniteDimensional K (X ⟶ X)] :
    IsFiniteSemisimpleCategory C ↔ ∀ X : C, IsSemisimpleRing (End X) :=
  ⟨fun _ X ↦ IsFiniteSemisimpleCategory.isSemisimpleRing_end K X,
    fun _ ↦ IsFiniteSemisimpleCategory.of_isSemisimpleRing_end K⟩

end Abelian

/-- **Jannsen's criterion.** Let `C` be an additive category in which idempotents split, linear
over a division ring `K`. If every endomorphism ring is semisimple and finite-dimensional over
`K`, then `C` is abelian with the given addition (`TauCeti.abelianOfIsSemisimpleRingEnd`), and
every object is a finite biproduct of simple objects. -/
theorem isFiniteSemisimpleCategory_abelianOfIsSemisimpleRingEnd (K : Type*) [DivisionRing K]
    [Preadditive C] [Linear K C] [HasFiniteBiproducts C] [IsIdempotentComplete C]
    [∀ X : C, IsSemisimpleRing (End X)] [∀ X : C, FiniteDimensional K (X ⟶ X)] :
    letI := abelianOfIsSemisimpleRingEnd C
    IsFiniteSemisimpleCategory C :=
  letI := abelianOfIsSemisimpleRingEnd C
  IsFiniteSemisimpleCategory.of_isSemisimpleRing_end K


end TauCeti
