/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Short exact kernel and cokernel sequences

This file records that the canonical kernel sequence of an epimorphism and the canonical cokernel
sequence of a monomorphism are short exact, and that a short complex of functors with values in
an abelian category is short exact as soon as it is short exact objectwise.

## Main statements

* `TauCeti.kernelSequence_shortExact`: the kernel sequence of an epimorphism is short exact.
* `TauCeti.cokernelSequence_shortExact`: the cokernel sequence of a monomorphism is short exact.
* `TauCeti.kernelCokernelCompSequence_snakeInput_L₃_shortExact`: for composable `a` and `b` with
  `b` a monomorphism, `cokernel a ⟶ cokernel (a ≫ b) ⟶ cokernel b` is short exact.
* `TauCeti.kernelCokernelCompSequence_snakeInput_L₀_shortExact`: for composable `a` and `b` with
  `a` an epimorphism, `kernel a ⟶ kernel (a ≫ b) ⟶ kernel b` is short exact.
* `TauCeti.cokernelOfLEKernelSubobjectIso`: for an epimorphism `a`, the quotient of the kernel of
  `a ≫ b` by the kernel of `a` is the kernel of `b`.
* `TauCeti.cokernelKernelSubobjectArrowIso`: for an epimorphism `a`, the quotient by the kernel of
  `a` is the target of `a`.
* `TauCeti.cokernelSequenceToSnakeInputL₃`: the morphism from `Y ⟶ Z ⟶ cokernel b` to that
  sequence.
* `CategoryTheory.ShortComplex.shortExact_of_forall_evaluation`: a short complex of functors is
  short exact if it is short exact after evaluation at every object.
* `CategoryTheory.ShortComplex.Exact.shortExact_factorThruImage`: an exact sequence
  `0 ⟶ X₁ ⟶ X₂ ⟶ X₃` gives the short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ image (X₂ ⟶ X₃) ⟶ 0`.
* `CategoryTheory.ShortComplex.shortExact_image_ι_cokernel_π`: the sequence
  `0 ⟶ image g ⟶ Y ⟶ cokernel g ⟶ 0` of a morphism `g : X ⟶ Y` is short exact.
* `CategoryTheory.ShortComplex.ShortExact.of_isColimit_cokernelCofork`: the cokernel of a morphism
  of short exact sequences whose third component is a monomorphism is short exact; the source
  only needs to be exact with an epimorphic second map.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The second map in the kernel sequence of an epimorphism is an epimorphism. -/
instance epi_kernelSequence_g {X Y : C} (f : X ⟶ Y) [Epi f] :
    Epi (ShortComplex.kernelSequence f).g :=
  (inferInstance : Epi f)

/-- The kernel sequence of an epimorphism is short exact. -/
lemma kernelSequence_shortExact {X Y : C} (f : X ⟶ Y) [Epi f] :
    (ShortComplex.kernelSequence f).ShortExact :=
  { exact := ShortComplex.kernelSequence_exact _ }

/-- The first map in the cokernel sequence of a monomorphism is a monomorphism. -/
instance mono_cokernelSequence_f {X Y : C} (f : X ⟶ Y) [Mono f] :
    Mono (ShortComplex.cokernelSequence f).f :=
  (inferInstance : Mono f)

/-- The cokernel sequence of a monomorphism is short exact. -/
lemma cokernelSequence_shortExact {X Y : C} (f : X ⟶ Y) [Mono f] :
    (ShortComplex.cokernelSequence f).ShortExact :=
  { exact := ShortComplex.cokernelSequence_exact _ }

section Comp

variable {X Y Z : C} (a : X ⟶ Y) (b : Y ⟶ Z)

/-- The sequence `cokernel a ⟶ cokernel (a ≫ b) ⟶ cokernel b`, the last row of Mathlib's
`kernelCokernelCompSequence.snakeInput a b`, is short exact when `b` is a monomorphism. -/
lemma kernelCokernelCompSequence_snakeInput_L₃_shortExact [Mono b] :
    (kernelCokernelCompSequence.snakeInput a b).L₃.ShortExact := by
  have hE := kernelCokernelCompSequence_exact a b
  refine ShortComplex.ShortExact.mk' (kernelCokernelCompSequence.snakeInput a b).L₃_exact ?_ ?_
  · exact (hE.exact 2).mono_g (by
      dsimp
      rw [kernelCokernelCompSequence.δ_fac, kernel.ι_of_mono, zero_comp, neg_zero])
  · have : Epi (kernelCokernelCompSequence.snakeInput a b).L₂.g :=
      inferInstanceAs (Epi (biprod.snd : Y ⊞ Z ⟶ Z))
    exact (kernelCokernelCompSequence.snakeInput a b).epi_L₃_g

/-- The sequence `kernel a ⟶ kernel (a ≫ b) ⟶ kernel b`, the first row of Mathlib's
`kernelCokernelCompSequence.snakeInput a b`, is short exact when `a` is an epimorphism. -/
lemma kernelCokernelCompSequence_snakeInput_L₀_shortExact [Epi a] :
    (kernelCokernelCompSequence.snakeInput a b).L₀.ShortExact := by
  refine ShortComplex.ShortExact.mk' (kernelCokernelCompSequence.snakeInput a b).L₀_exact ?_ ?_
  · exact (inferInstance : Mono (kernel.map a (a ≫ b) (𝟙 _) b (by simp)))
  · exact ((kernelCokernelCompSequence_exact a b).exact 1).epi_f
      ((isZero_cokernel_of_epi a).eq_of_tgt _ _)

variable {a b} in
/-- The short complex `S ⟶ T ⟶ kernel b` for subobjects `S = kernelSubobject a` and
`T = kernelSubobject (a ≫ b)`, the second map being induced by `a`. -/
private noncomputable abbrev ofLEKernelSubobjectShortComplex {S T : Subobject X}
    (hS : S = kernelSubobject a) (hT : T = kernelSubobject (a ≫ b)) (h : S ≤ T) :
    ShortComplex C :=
  ShortComplex.mk (Subobject.ofLE S T h)
    (kernel.lift b (T.arrow ≫ a)
      (by subst hT; rw [Category.assoc]; exact kernelSubobject_arrow_comp _)) (by
      subst hS hT
      rw [← cancel_mono (kernel.ι b)]
      simp)

variable {a b} in
private lemma ofLEKernelSubobjectShortComplex_shortExact [Epi a] {S T : Subobject X}
    (hS : S = kernelSubobject a) (hT : T = kernelSubobject (a ≫ b)) (h : S ≤ T) :
    (ofLEKernelSubobjectShortComplex hS hT h).ShortExact := by
  subst hS hT
  exact ShortComplex.shortExact_of_iso (S₁ := (kernelCokernelCompSequence.snakeInput a b).L₀)
    (ShortComplex.isoMk (kernelSubobjectIso a).symm (kernelSubobjectIso (a ≫ b)).symm (Iso.refl _)
      (by simp [← cancel_mono (kernelSubobject (a ≫ b)).arrow,
        kernelCokernelCompSequence.snakeInput])
      (by simp [← cancel_mono (kernel.ι b), kernelCokernelCompSequence.snakeInput]))
    (kernelCokernelCompSequence_snakeInput_L₀_shortExact a b)

/-- For an epimorphism `a`, the cokernel of the inclusion of the kernel of `a` into the kernel of
`a ≫ b` is the kernel of `b`, the isomorphism being induced by `a`
(`TauCeti.π_cokernelOfLEKernelSubobjectIso_hom_ι`). The two subobjects are given up to equality,
for flexibility. -/
noncomputable def cokernelOfLEKernelSubobjectIso [Epi a] {S T : Subobject X}
    (hS : S = kernelSubobject a) (hT : T = kernelSubobject (a ≫ b)) (h : S ≤ T) :
    cokernel (Subobject.ofLE S T h) ≅ kernel b :=
  (cokernelIsCokernel _).coconePointUniqueUpToIso
    (ofLEKernelSubobjectShortComplex_shortExact hS hT h).gIsCokernel

/-- The isomorphism `TauCeti.cokernelOfLEKernelSubobjectIso` is induced by `a`. -/
@[reassoc (attr := simp)]
lemma π_cokernelOfLEKernelSubobjectIso_hom_ι [Epi a] {S T : Subobject X}
    (hS : S = kernelSubobject a) (hT : T = kernelSubobject (a ≫ b)) (h : S ≤ T) :
    cokernel.π (Subobject.ofLE S T h) ≫ (cokernelOfLEKernelSubobjectIso a b hS hT h).hom ≫
      kernel.ι b = T.arrow ≫ a := by
  have := (cokernelIsCokernel _).comp_coconePointUniqueUpToIso_hom
    (ofLEKernelSubobjectShortComplex_shortExact hS hT h).gIsCokernel WalkingParallelPair.one
  dsimp at this
  rw [cokernelOfLEKernelSubobjectIso, reassoc_of% this, kernel.lift_ι]

/-- For an epimorphism `a`, the cokernel of the inclusion of the kernel of `a` is the target of
`a`, the isomorphism being induced by `a` (`TauCeti.π_cokernelKernelSubobjectArrowIso_hom`). The
subobject is given up to equality, for flexibility. -/
noncomputable def cokernelKernelSubobjectArrowIso [Epi a] {S : Subobject X}
    (hS : S = kernelSubobject a) : cokernel S.arrow ≅ Y :=
  (cokernelIsCokernel _).coconePointUniqueUpToIso
    (Abelian.epiIsCokernelOfKernel _ (IsKernel.isoKernel _ _ (kernelIsKernel a)
      ((Subobject.isoOfEq _ _ hS).trans (kernelSubobjectIso a)) (by subst hS; simp)))

/-- The isomorphism `TauCeti.cokernelKernelSubobjectArrowIso` is induced by `a`. -/
@[reassoc (attr := simp)]
lemma π_cokernelKernelSubobjectArrowIso_hom [Epi a] {S : Subobject X}
    (hS : S = kernelSubobject a) :
    cokernel.π S.arrow ≫ (cokernelKernelSubobjectArrowIso a hS).hom = a :=
  (cokernelIsCokernel _).comp_coconePointUniqueUpToIso_hom _ WalkingParallelPair.one

/-- The morphism of short complexes from `Y ⟶ Z ⟶ cokernel b` to
`cokernel a ⟶ cokernel (a ≫ b) ⟶ cokernel b` given by the cokernel projections of `a` and
`a ≫ b` and the identity of `cokernel b`. -/
noncomputable def cokernelSequenceToSnakeInputL₃ :
    ShortComplex.cokernelSequence b ⟶ (kernelCokernelCompSequence.snakeInput a b).L₃ where
  τ₁ := cokernel.π a
  τ₂ := cokernel.π (a ≫ b)
  τ₃ := 𝟙 _
  comm₁₂ := cokernel.π_desc _ _ _
  comm₂₃ := (cokernel.π_desc _ _ _).trans ((Category.id_comp _).trans (Category.comp_id _).symm)

@[simp]
lemma cokernelSequenceToSnakeInputL₃_τ₁ :
    (cokernelSequenceToSnakeInputL₃ a b).τ₁ = cokernel.π a := by
  rw [cokernelSequenceToSnakeInputL₃]

@[simp]
lemma cokernelSequenceToSnakeInputL₃_τ₂ :
    (cokernelSequenceToSnakeInputL₃ a b).τ₂ = cokernel.π (a ≫ b) := by
  rw [cokernelSequenceToSnakeInputL₃]

@[simp]
lemma cokernelSequenceToSnakeInputL₃_τ₃ : (cokernelSequenceToSnakeInputL₃ a b).τ₃ = 𝟙 _ := by
  rw [cokernelSequenceToSnakeInputL₃]

end Comp

end TauCeti

namespace CategoryTheory.ShortComplex

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **Short exactness of functors is checked objectwise.** A short complex of functors with values
in an abelian category is short exact if it becomes short exact after evaluation at every object.
-/
lemma shortExact_of_forall_evaluation {J : Type*} [Category* J] (S : ShortComplex (J ⥤ C))
    (h : ∀ j, (S.map ((evaluation J C).obj j)).ShortExact) : S.ShortExact := by
  have (j : J) : Mono (S.f.app j) := (h j).mono_f
  have (j : J) : Epi (S.g.app j) := (h j).epi_g
  have : Mono S.f := NatTrans.mono_of_mono_app S.f
  have : Epi S.g := NatTrans.epi_of_epi_app S.g
  refine ShortExact.mk' ?_ inferInstance inferInstance
  rw [exact_iff_isZero_homology]
  exact Functor.isZero _ fun j ↦ ((exact_iff_isZero_homology _).1 (h j).exact).of_iso
    (S.mapHomologyIso ((evaluation J C).obj j)).symm

/-- If `X₁ ⟶ X₂ ⟶ X₃` is exact and `X₁ ⟶ X₂` is a monomorphism, then
`0 ⟶ X₁ ⟶ X₂ ⟶ image (X₂ ⟶ X₃) ⟶ 0` is short exact. -/
lemma Exact.shortExact_factorThruImage {S : ShortComplex C} (hS : S.Exact) [Mono S.f] :
    (ShortComplex.mk S.f (factorThruImage S.g) (comp_factorThruImage_eq_zero S.zero)).ShortExact
    where
  exact := exact_of_g_is_cokernel _ hS.isColimitImage

/-- For a morphism `g : X ⟶ Y`, the sequence `0 ⟶ image g ⟶ Y ⟶ cokernel g ⟶ 0` is short
exact. -/
lemma shortExact_image_ι_cokernel_π {X Y : C} (g : X ⟶ Y) :
    (ShortComplex.mk (image.ι g) (cokernel.π g)
      (image_ι_comp_eq_zero (cokernel.condition g))).ShortExact where
  exact := exact_of_f_is_kernel _ (exact_cokernel g).isLimitImage'

/-- **The cokernel of a morphism into a short exact sequence.** Let `v : L₁ ⟶ L₂` be a morphism
from an exact sequence `L₁` whose second map is an epimorphism to a short exact sequence `L₂`, and
suppose that the third component of `v` is a monomorphism. Then the cokernel `L₃` of `v`, computed
componentwise, is short exact. This is the snake lemma in the case where the kernel of the third
component, and hence the connecting morphism, vanishes. -/
lemma ShortExact.of_isColimit_cokernelCofork {L₁ L₂ L₃ : ShortComplex C} (h₂ : L₂.ShortExact)
    (h₁ : L₁.Exact) [Epi L₁.g] (v : L₁ ⟶ L₂) [Mono v.τ₃] (π : L₂ ⟶ L₃) (w : v ≫ π = 0)
    (hπ : IsColimit (CokernelCofork.ofπ π w)) : L₃.ShortExact := by
  have := h₂.epi_g
  let S : SnakeInput C :=
    { L₀ := kernel v
      L₁ := L₁
      L₂ := L₂
      L₃ := L₃
      v₀₁ := kernel.ι v
      v₁₂ := v
      v₂₃ := π
      h₀ := kernelIsKernel v
      h₃ := hπ
      L₁_exact := h₁
      epi_L₁_g := inferInstance
      L₂_exact := h₂.exact
      mono_L₂_f := h₂.mono_f }
  have hδ : S.δ = 0 := (KernelFork.IsLimit.isZero_of_mono S.h₀τ₃).eq_of_src _ _
  exact ShortExact.mk' S.L₃_exact (S.L₂'_exact.mono_g hδ) S.epi_L₃_g

end CategoryTheory.ShortComplex
