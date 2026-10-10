/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.AlmostSplit.Minimal

/-!
# Completing minimal almost-split morphisms

In a category with enough projectives, a right almost-split morphism is epic exactly when
its target is not projective. Dually, with enough injectives a left almost-split morphism
is monic exactly when its source is not injective.

Consequently, in an abelian category a right minimal right almost-split morphism to a
non-projective object completes to an almost-split sequence by taking its kernel. The
dual construction takes the cokernel of a left minimal left almost-split morphism from
a non-injective object. These constructions turn existence of minimal almost-split maps
into existence of almost-split sequences, without separate epimorphicity or monomorphicity
assumptions.

## References

* M. Auslander, I. Reiten, S. Smalø, *Representation Theory of Artin Algebras*, V.1.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti

universe u v

variable {C : Type u} [Category.{v} C] {X Y : C} {f : X ⟶ Y}

variable [Abelian C]

/-- Taking the kernel of a right minimal right almost-split morphism to a non-projective
object gives an almost-split sequence. -/
theorem IsRightAlmostSplit.isAlmostSplit_kernelSequence [EnoughProjectives C]
    (hf : IsRightAlmostSplit f) (hY : ¬ Projective Y)
    (hmin : ∀ b : X ⟶ X, b ≫ f = f → IsIso b) :
    (ShortComplex.kernelSequence f).IsAlmostSplit := by
  have hS : (ShortComplex.kernelSequence f).ShortExact :=
    { exact := ShortComplex.kernelSequence_exact f
      -- The kernel-sequence constructor identifies its final map with `f`.
      epi_g := by simpa only [ShortComplex.kernelSequence] using
        hf.epi_iff_not_projective.mpr hY }
  exact hS.isAlmostSplit_of_isRightAlmostSplit hf hmin

/-- Taking the cokernel of a left minimal left almost-split morphism from a non-injective
object gives an almost-split sequence. -/
theorem IsLeftAlmostSplit.isAlmostSplit_cokernelSequence [EnoughInjectives C]
    (hf : IsLeftAlmostSplit f) (hX : ¬ Injective X)
    (hmin : ∀ b : Y ⟶ Y, f ≫ b = f → IsIso b) :
    (ShortComplex.cokernelSequence f).IsAlmostSplit := by
  have hS : (ShortComplex.cokernelSequence f).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact f
      -- The cokernel-sequence constructor identifies its initial map with `f`.
      mono_f := by simpa only [ShortComplex.cokernelSequence] using
        hf.mono_iff_not_injective.mpr hX }
  exact hS.isAlmostSplit_of_isLeftAlmostSplit hf hmin

end TauCeti
