/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp

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
* `TauCeti.cokernelSequenceToSnakeInputL₃`: the morphism from `Y ⟶ Z ⟶ cokernel b` to that
  sequence.
* `CategoryTheory.ShortComplex.shortExact_of_forall_evaluation`: a short complex of functors is
  short exact if it is short exact after evaluation at every object.
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
