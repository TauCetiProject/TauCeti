/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp

/-!
# The kernel of a composite modulo the kernel of its second map

For composable morphisms `a : X ⟶ Y` and `b : Y ⟶ Z` in an abelian category, Mathlib's
`CategoryTheory.kernelCokernelCompSequence a b` is the exact sequence

`0 ⟶ ker a ⟶ ker (a ≫ b) ⟶ ker b ⟶ coker a ⟶ coker (a ≫ b) ⟶ coker b ⟶ 0`.

When `a` is a monomorphism and `a ≫ b` an epimorphism, its two outer terms vanish, and its middle

`0 ⟶ ker (a ≫ b) ⟶ ker b ⟶ coker a ⟶ 0`

is short exact (`TauCeti.kernelCokernelCompSequence_shortExact_of_mono_of_epi`), with second map
`ker b ⟶ Y ⟶ coker a`. For complexes, where `a` is the inclusion of a subcomplex and `b` a
quasi-isomorphism, this computes the homology of `coker a` from that of `ker (a ≫ b)`.
-/

public section

open CategoryTheory Limits

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [Abelian C] {X Y Z : C} (a : X ⟶ Y) (b : Y ⟶ Z)

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

end TauCeti
