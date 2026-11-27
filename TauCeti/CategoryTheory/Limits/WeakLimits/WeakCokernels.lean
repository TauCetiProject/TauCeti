/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.WeakLimits.WeakKernels

/-!
# Weak cokernels

A weak cokernel is a weak kernel in the opposite category. In terms of the
original category, it is a morphism through which every morphism annihilating
the given arrow factors. Crawley-Boevey uses the term pseudo-cokernel in
*Locally finitely presented additive categories*, §1.2.
-/

public section

open CategoryTheory Limits Opposite

namespace TauCeti

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

/-- A weak cokernel of `f` is a weak kernel of `f.op` in the opposite category. -/
def IsWeakCokernel {X Y Z : C} (f : X ⟶ Y) (q : Y ⟶ Z) : Prop :=
  ∃ h : q.op ≫ f.op = 0, Nonempty (IsWeakLimit (KernelFork.ofι q.op h))

/-- A weak kernel fork in the opposite category gives a weak cokernel. -/
theorem IsWeakCokernel.of_isWeakLimit {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {i : Z ⟶ X}
    {h : i ≫ f = 0} (hi : IsWeakLimit (KernelFork.ofι i h)) :
    IsWeakCokernel f.unop i.unop :=
  ⟨by simpa only [Quiver.Hom.op_unop] using h, ⟨by simpa only [Quiver.Hom.op_unop] using hi⟩⟩

/-- A weak cokernel kills the given arrow and factors every morphism that does so. -/
theorem isWeakCokernel_iff {X Y Z : C} {f : X ⟶ Y} {q : Y ⟶ Z} :
    IsWeakCokernel f q ↔ f ≫ q = 0 ∧
      ∀ ⦃W : C⦄ (k : Y ⟶ W), f ≫ k = 0 → ∃ l : Z ⟶ W, q ≫ l = k := by
  constructor
  · rintro ⟨h, ⟨hq⟩⟩
    refine ⟨Quiver.Hom.op_inj (by simpa only [op_comp, op_zero] using h), ?_⟩
    intro W k hk
    let s : KernelFork f.op := KernelFork.ofι k.op (by simp [← op_comp, hk])
    refine ⟨(hq.lift s).unop, Quiver.Hom.op_inj ?_⟩
    have hl : hq.lift s ≫ (KernelFork.ofι q.op h).ι = s.ι :=
      hq.fac s WalkingParallelPair.zero
    simpa only [op_comp, Quiver.Hom.op_unop, s, KernelFork.ι_ofι] using hl
  · rintro ⟨h, hq⟩
    refine ⟨by simp [← op_comp, h], ⟨Fork.IsWeakLimit.mk' _ ?_⟩⟩
    intro s
    have hl := hq s.ι.unop (by
      simpa only [unop_comp, unop_zero, Quiver.Hom.unop_op] using
        congrArg Quiver.Hom.unop (KernelFork.condition s))
    refine ⟨hl.choose.op, ?_⟩
    simpa only [KernelFork.ι_ofι, op_comp, Quiver.Hom.op_unop] using
      congrArg Quiver.Hom.op hl.choose_spec

/-- Weak kernels in the opposite category supply weak cokernels in the original category. -/
theorem exists_isWeakCokernel [HasWeakKernels Cᵒᵖ] {X Y : C} (f : X ⟶ Y) :
    ∃ (Z : C) (q : Y ⟶ Z), IsWeakCokernel f q :=
  ⟨_, _, IsWeakCokernel.of_isWeakLimit (h := weakKernel.condition f.op)
    (weakKernelIsWeakKernel f.op)⟩

end TauCeti
