/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.EpiWithInjectiveKernel
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
import TauCeti.CategoryTheory.Limits.Shapes.Pullback.Kernel

/-!
# Epimorphisms with an injective kernel are the injective fibrations

In an abelian category, a morphism is an epimorphism with an injective kernel (Mathlib's
`CategoryTheory.Abelian.epiWithInjectiveKernel`) if and only if it has the right lifting property
with respect to every monomorphism
(`CategoryTheory.Abelian.epiWithInjectiveKernel_iff_rlp_monomorphisms`). Mathlib proves the
forward implication as `CategoryTheory.Abelian.epiWithInjectiveKernel.hasLiftingProperty`; the
converse lifts against `0 ⟶ Y` to split `p : X ⟶ Y`, and the kernel of `p` inherits the lifting
property as a base change of `p`. This is the degreewise form of the fibrations of the injective
model structure on cochain complexes.
-/

public section

namespace CategoryTheory.Abelian

open Limits ZeroObject MorphismProperty

variable {C : Type*} [Category* C] [Abelian C]

/-- A morphism of an abelian category is an epimorphism with an injective kernel if and only if
it has the right lifting property with respect to every monomorphism. -/
theorem epiWithInjectiveKernel_iff_rlp_monomorphisms {X Y : C} (p : X ⟶ Y) :
    epiWithInjectiveKernel p ↔ (monomorphisms C).rlp p := by
  refine ⟨fun hp _ _ i (_ : Mono i) ↦ hp.hasLiftingProperty i, fun hp ↦ ⟨?_, ?_⟩⟩
  · have := hp (0 : (0 : C) ⟶ Y) (monomorphisms.infer_property _)
    have sq : CommSq (0 : 0 ⟶ X) 0 p (𝟙 Y) := ⟨by simp⟩
    exact epi_of_epi_fac sq.fac_right
  · rw [injective_iff_rlp_monomorphisms_of_isZero (0 : kernel p ⟶ 0) (isZero_zero C)]
    exact IsStableUnderBaseChange.of_isPullback (IsPullback.kernel_ι p) hp

end CategoryTheory.Abelian
