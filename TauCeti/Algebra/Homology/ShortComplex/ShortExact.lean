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
public import TauCeti.Algebra.Homology.ShortComplex.Biproduct
import TauCeti.CategoryTheory.Exact.KernelCokernelPair

/-!
# Short exact kernel and cokernel sequences

This file records that the canonical kernel sequence of an epimorphism and the canonical cokernel
sequence of a monomorphism are short exact, and that a short complex of functors with values in
an abelian category is short exact as soon as it is short exact objectwise. Componentwise binary
direct sums also preserve short exactness. The two maps of a short exact sequence split
simultaneously.

## Main statements

* `CategoryTheory.ShortComplex.ShortExact.isSplitMono_f_iff_isSplitEpi_g`: the initial map splits
  if and only if the final map splits.
* `CategoryTheory.ShortComplex.Exact.isIso_cokernelDesc`: in an exact sequence with epimorphic
  final map, the final map induces an isomorphism from the cokernel of the initial map.
* `TauCeti.kernelSequence_shortExact`: the kernel sequence of an epimorphism is short exact.
* `TauCeti.cokernelSequence_shortExact`: the cokernel sequence of a monomorphism is short exact.
* `TauCeti.cokernelCompSequence`: the sequence `cokernel a ⟶ cokernel (a ≫ b) ⟶ cokernel b` of
  composable `a` and `b`, with `TauCeti.cokernelCompSequence_shortExact` its short exactness when
  `b` is a monomorphism.
* `TauCeti.kernelCokernelCompSequence_snakeInput_L₀_shortExact`: for composable `a` and `b` with
  `a` an epimorphism, `kernel a ⟶ kernel (a ≫ b) ⟶ kernel b` is short exact.
* `TauCeti.kernelCokernelCompSequence_shortExact_of_mono_of_epi`: for composable `a` and `b` with
  `a` a monomorphism and `a ≫ b` an epimorphism, `kernel (a ≫ b) ⟶ kernel b ⟶ cokernel a` is
  short exact.
* `TauCeti.cokernelOfLEKernelSubobjectIso`: for an epimorphism `a`, the quotient of the kernel of
  `a ≫ b` by the kernel of `a` is the kernel of `b`.
* `TauCeti.cokernelKernelSubobjectArrowIso`: for an epimorphism `a`, the quotient by the kernel of
  `a` is the target of `a`.
* `TauCeti.cokernelSequenceToCokernelCompSequence`: the morphism from `Y ⟶ Z ⟶ cokernel b` to
  that sequence.
* `TauCeti.cokernelCompSequenceMap`: the morphism between two such sequences induced by a
  commutative ladder between the composable pairs.
* `CategoryTheory.ShortComplex.shortExact_of_forall_evaluation`: a short complex of functors is
  short exact if it is short exact after evaluation at every object.
* `CategoryTheory.ShortComplex.Exact.shortExact_factorThruImage`: an exact sequence
  `0 ⟶ X₁ ⟶ X₂ ⟶ X₃` gives the short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ image (X₂ ⟶ X₃) ⟶ 0`.
* `CategoryTheory.ShortComplex.shortExact_image_ι_cokernel_π`: the sequence
  `0 ⟶ image g ⟶ Y ⟶ cokernel g ⟶ 0` of a morphism `g : X ⟶ Y` is short exact.
* `CategoryTheory.ShortComplex.ShortExact.biprod`: a componentwise binary direct sum of short
  exact sequences is short exact.
* `CategoryTheory.ShortComplex.exact_of_eq_epi_comp_of_eq_comp_mono`: precomposing the first map
  of an exact sequence with an epimorphism and postcomposing the second with a monomorphism keeps
  it exact.
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

/-- The sequence `cokernel a ⟶ cokernel (a ≫ b) ⟶ cokernel b` of the composable pair `(a, b)`,
whose maps are induced by `b` and by `𝟙 Z`. It is the last row of Mathlib's
`kernelCokernelCompSequence.snakeInput a b` (`TauCeti.cokernelCompSequence_eq`), with its objects
written as cokernels. -/
@[simps]
noncomputable abbrev cokernelCompSequence : ShortComplex C :=
  ShortComplex.mk (cokernel.map a (a ≫ b) (𝟙 _) b (by simp))
    (cokernel.map (a ≫ b) b a (𝟙 _) (by simp)) (by ext; simp)

/-- The sequence `TauCeti.cokernelCompSequence a b` is the last row of Mathlib's
`kernelCokernelCompSequence.snakeInput a b`. -/
lemma cokernelCompSequence_eq :
    cokernelCompSequence a b = (kernelCokernelCompSequence.snakeInput a b).L₃ :=
  rfl

/-- The sequence `cokernel a ⟶ cokernel (a ≫ b) ⟶ cokernel b` is short exact when `b` is a
monomorphism. -/
lemma cokernelCompSequence_shortExact [Mono b] : (cokernelCompSequence a b).ShortExact := by
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

/-- The sequence `kernel (a ≫ b) ⟶ kernel b ⟶ cokernel a`, whose second map is
`kernel.ι b ≫ cokernel.π a`, is short exact when `a` is a monomorphism and `a ≫ b` is an
epimorphism. Up to the sign of its second map, it is the middle of Mathlib's
`kernelCokernelCompSequence a b`, whose two outer terms `kernel a` and `cokernel (a ≫ b)` then
vanish. -/
lemma kernelCokernelCompSequence_shortExact_of_mono_of_epi [Mono a] [Epi (a ≫ b)] :
    (ShortComplex.mk (kernel.map (a ≫ b) b a (𝟙 _) (by simp)) (kernel.ι b ≫ cokernel.π a)
      (by simp)).ShortExact := by
  have hE := kernelCokernelCompSequence_exact a b
  -- The middle of Mathlib's sequence, whose second map is the connecting map
  -- `δ = -(kernel.ι b ≫ cokernel.π a)`.
  have hS : ((kernelCokernelCompSequence a b).sc hE.toIsComplex 1).ShortExact :=
    ShortComplex.ShortExact.mk' (hE.exact 1)
      ((hE.exact 0).mono_g ((isZero_kernel_of_mono a).eq_of_src _ _))
      ((hE.exact 2).epi_f ((isZero_cokernel_of_epi (a ≫ b)).eq_of_tgt _ _))
  refine ShortComplex.shortExact_of_iso (ShortComplex.isoMk
    (S₁ := (kernelCokernelCompSequence a b).sc hE.toIsComplex 1) (Iso.refl _) (Iso.refl _)
    { hom := -𝟙 _, inv := -𝟙 _ } ?_ ?_) hS
  · simp
  · dsimp
    rw [kernelCokernelCompSequence.δ_fac]
    simp

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
noncomputable def cokernelSequenceToCokernelCompSequence :
    ShortComplex.cokernelSequence b ⟶ cokernelCompSequence a b where
  τ₁ := cokernel.π a
  τ₂ := cokernel.π (a ≫ b)
  τ₃ := 𝟙 _
  comm₁₂ := cokernel.π_desc _ _ _
  comm₂₃ := (cokernel.π_desc _ _ _).trans ((Category.id_comp _).trans (Category.comp_id _).symm)

@[simp]
lemma cokernelSequenceToCokernelCompSequence_τ₁ :
    (cokernelSequenceToCokernelCompSequence a b).τ₁ = cokernel.π a := by
  rw [cokernelSequenceToCokernelCompSequence]

@[simp]
lemma cokernelSequenceToCokernelCompSequence_τ₂ :
    (cokernelSequenceToCokernelCompSequence a b).τ₂ = cokernel.π (a ≫ b) := by
  rw [cokernelSequenceToCokernelCompSequence]

@[simp]
lemma cokernelSequenceToCokernelCompSequence_τ₃ :
    (cokernelSequenceToCokernelCompSequence a b).τ₃ = 𝟙 _ := by
  rw [cokernelSequenceToCokernelCompSequence]

variable {a b} {X' Y' Z' : C} {a' : X' ⟶ Y'} {b' : Y' ⟶ Z'} (u₁ : X ⟶ X') (u₂ : Y ⟶ Y')
  (u₃ : Z ⟶ Z') (w₁ : u₁ ≫ a' = a ≫ u₂) (w₂ : u₂ ≫ b' = b ≫ u₃)

/-- A commutative ladder `u₁, u₂, u₃` from the composable pair `(a, b)` to the composable pair
`(a', b')` induces a morphism of short complexes from
`cokernel a ⟶ cokernel (a ≫ b) ⟶ cokernel b` to `cokernel a' ⟶ cokernel (a' ≫ b') ⟶ cokernel b'`,
whose components are the maps of cokernels induced by the ladder. -/
noncomputable def cokernelCompSequenceMap :
    cokernelCompSequence a b ⟶ cokernelCompSequence a' b' where
  τ₁ := cokernel.map a a' u₁ u₂ w₁
  τ₂ := cokernel.map (a ≫ b) (a' ≫ b') u₁ u₃ (by rw [Category.assoc, ← w₂, reassoc_of% w₁])
  τ₃ := cokernel.map b b' u₂ u₃ w₂
  comm₁₂ := by
    ext
    simp [reassoc_of% w₂]
  comm₂₃ := by
    ext
    simp

@[simp]
lemma cokernelCompSequenceMap_τ₁ :
    (cokernelCompSequenceMap u₁ u₂ u₃ w₁ w₂).τ₁ = cokernel.map a a' u₁ u₂ w₁ := by
  rw [cokernelCompSequenceMap]

@[simp]
lemma cokernelCompSequenceMap_τ₂ :
    (cokernelCompSequenceMap u₁ u₂ u₃ w₁ w₂).τ₂ =
      cokernel.map (a ≫ b) (a' ≫ b') u₁ u₃ (by rw [Category.assoc, ← w₂, reassoc_of% w₁]) := by
  rw [cokernelCompSequenceMap]

@[simp]
lemma cokernelCompSequenceMap_τ₃ :
    (cokernelCompSequenceMap u₁ u₂ u₃ w₁ w₂).τ₃ = cokernel.map b b' u₂ u₃ w₂ := by
  rw [cokernelCompSequenceMap]

end Comp

end TauCeti

namespace CategoryTheory.ShortComplex

open Limits

/-- In a short exact sequence, the initial map is a split monomorphism exactly when the final
map is a split epimorphism. -/
theorem ShortExact.isSplitMono_f_iff_isSplitEpi_g {C : Type u} [Category.{v} C] [Preadditive C]
    [Balanced C] {S : ShortComplex C} (hS : S.ShortExact) :
    IsSplitMono S.f ↔ IsSplitEpi S.g := by
  constructor
  · intro hf
    exact (Splitting.ofExactOfRetraction S hS.exact
      (retraction S.f) (IsSplitMono.id S.f) hS.epi_g).isSplitEpi_g
  · intro hg
    exact (Splitting.ofExactOfSection S hS.exact
      (section_ S.g) (IsSplitEpi.id S.g) hS.mono_f).isSplitMono_f

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- In an exact sequence whose final map is an epimorphism, the final map induces an isomorphism
from the cokernel of the initial map. -/
lemma Exact.isIso_cokernelDesc {S : ShortComplex C} (hS : S.Exact) [Epi S.g] :
    IsIso (cokernel.desc S.f S.g S.zero) := by
  have := hS.mono_cokernelDesc
  have : Epi (cokernel.desc S.f S.g S.zero) := epi_of_epi_fac (cokernel.π_desc S.f S.g S.zero)
  exact isIso_of_mono_of_epi _

/-- A componentwise direct sum of short exact sequences is short exact. -/
lemma ShortExact.biprod {S T : ShortComplex C} (hS : S.ShortExact) (hT : T.ShortExact) :
    (S.biprod T).ShortExact :=
  ((TauCeti.IsKernelCokernelPair.of_shortExact hS).biprod
    (TauCeti.IsKernelCokernelPair.of_shortExact hT)).shortExact

/-- Exactness of a short complex of functors is checked objectwise. -/
lemma exact_of_forall_evaluation {J : Type*} [Category* J] (S : ShortComplex (J ⥤ C))
    (h : ∀ j, (S.map ((evaluation J C).obj j)).Exact) : S.Exact := by
  rw [exact_iff_isZero_homology]
  exact Functor.isZero _ fun j ↦ ((exact_iff_isZero_homology _).1 (h j)).of_iso
    (S.mapHomologyIso ((evaluation J C).obj j)).symm

/-- **Short exactness of functors is checked objectwise.** A short complex of functors with values
in an abelian category is short exact if it becomes short exact after evaluation at every object.
-/
lemma shortExact_of_forall_evaluation {J : Type*} [Category* J] (S : ShortComplex (J ⥤ C))
    (h : ∀ j, (S.map ((evaluation J C).obj j)).ShortExact) : S.ShortExact := by
  have (j : J) : Mono (S.f.app j) := (h j).mono_f
  have (j : J) : Epi (S.g.app j) := (h j).epi_g
  have : Mono S.f := NatTrans.mono_of_mono_app S.f
  have : Epi S.g := NatTrans.epi_of_epi_app S.g
  exact ShortExact.mk' (exact_of_forall_evaluation S fun j ↦ (h j).exact)
    inferInstance inferInstance

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

/-- An exact sequence `A₁ ⟶ X₂ ⟶ A₂` stays exact after precomposing its first map with an
epimorphism `X₁ ⟶ A₁` and postcomposing its second map with a monomorphism `A₂ ⟶ X₃`. -/
lemma exact_of_eq_epi_comp_of_eq_comp_mono {X₁ A₁ X₂ A₂ X₃ : C} {f : X₁ ⟶ X₂}
    {g : X₂ ⟶ X₃} (zero : f ≫ g = 0) (e : X₁ ⟶ A₁) (i : A₁ ⟶ X₂) (g' : X₂ ⟶ A₂)
    (m : A₂ ⟶ X₃) [Epi e] [Mono m] (hf : f = e ≫ i)
    (hg : g = g' ≫ m) (w : i ≫ g' = 0) (h : (ShortComplex.mk i g' w).Exact) :
    (ShortComplex.mk f g zero).Exact := by
  subst hf hg
  have h₁ : (ShortComplex.mk (e ≫ i) g' (by simp [w])).Exact :=
    (exact_iff_of_epi_of_isIso_of_mono
      (S₁ := ShortComplex.mk (e ≫ i) g' (by simp [w])) (S₂ := ShortComplex.mk i g' w)
      { τ₁ := e, τ₂ := 𝟙 _, τ₃ := 𝟙 _ }).2 h
  exact (exact_iff_of_epi_of_isIso_of_mono
    (S₁ := ShortComplex.mk (e ≫ i) g' (by simp [w]))
    (S₂ := ShortComplex.mk (e ≫ i) (g' ≫ m) zero) { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := m }).1 h₁

end CategoryTheory.ShortComplex
