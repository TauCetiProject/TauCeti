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
theorem _root_.CategoryTheory.Limits.IsWeakLimit.isWeakCokernel
    {X Y : Cᵒᵖ} {f : X ⟶ Y} {s : KernelFork f} (hs : IsWeakLimit s) :
    IsWeakCokernel f.unop s.ι.unop :=
  ⟨by simpa only [Quiver.Hom.op_unop] using KernelFork.condition s,
    ⟨by simpa only [Quiver.Hom.op_unop] using hs.ofIsoWeakLimit (isoOfι s)⟩⟩

/-- A weak cokernel kills the given arrow. -/
@[reassoc (attr := simp)]
theorem IsWeakCokernel.comp_eq_zero {X Y Z : C} {f : X ⟶ Y} {q : Y ⟶ Z}
    (hq : IsWeakCokernel f q) : f ≫ q = 0 :=
  Quiver.Hom.op_inj (by simpa only [op_comp, op_zero] using hq.choose)

/-- A weak cokernel gives a weak kernel fork in the opposite category. -/
theorem IsWeakCokernel.nonempty_isWeakLimit {X Y Z : C} {f : X ⟶ Y} {q : Y ⟶ Z}
    (hq : IsWeakCokernel f q) :
    Nonempty (IsWeakLimit (KernelFork.ofι (f := f.op) q.op (by
      simpa only [op_comp, op_zero] using congrArg Quiver.Hom.op hq.comp_eq_zero))) :=
  hq.choose_spec

/-- A weak cokernel witnesses the existence of a weak kernel in the opposite category. -/
theorem IsWeakCokernel.hasWeakKernel {X Y Z : C} {f : X ⟶ Y} {q : Y ⟶ Z}
    (hq : IsWeakCokernel f q) : HasWeakKernel f.op := by
  obtain ⟨h⟩ := hq.nonempty_isWeakLimit
  exact HasWeakLimit.mk ⟨_, h⟩

/-- Every morphism that kills the given arrow factors through its weak cokernel. -/
theorem IsWeakCokernel.exists_desc {X Y Z W : C} {f : X ⟶ Y} {q : Y ⟶ Z}
    (hq : IsWeakCokernel f q) (k : Y ⟶ W) (hk : f ≫ k = 0) : ∃ l : Z ⟶ W, q ≫ l = k := by
  obtain ⟨h⟩ := hq.nonempty_isWeakLimit
  let s : KernelFork f.op := KernelFork.ofι k.op (by simp [← op_comp, hk])
  refine ⟨(h.lift s).unop, Quiver.Hom.op_inj ?_⟩
  have hl : h.lift s ≫ q.op = k.op := h.fac s WalkingParallelPair.zero
  simpa only [op_comp, Quiver.Hom.op_unop] using hl

/-- A weak cokernel kills the given arrow and factors every morphism that does so. -/
theorem isWeakCokernel_iff {X Y Z : C} {f : X ⟶ Y} {q : Y ⟶ Z} :
    IsWeakCokernel f q ↔ f ≫ q = 0 ∧
      ∀ ⦃W : C⦄ (k : Y ⟶ W), f ≫ k = 0 → ∃ l : Z ⟶ W, q ≫ l = k := by
  constructor
  · exact fun hq ↦ ⟨hq.comp_eq_zero, fun _ k hk ↦ hq.exists_desc k hk⟩
  · rintro ⟨h, hq⟩
    refine ⟨by simp [← op_comp, h], ⟨Fork.IsWeakLimit.mk' _ ?_⟩⟩
    intro s
    have hl := hq s.ι.unop (by
      simpa only [unop_comp, unop_zero, Quiver.Hom.unop_op] using
        congrArg Quiver.Hom.unop (KernelFork.condition s))
    refine ⟨hl.choose.op, ?_⟩
    simpa only [KernelFork.ι_ofι, op_comp, Quiver.Hom.op_unop] using
      congrArg Quiver.Hom.op hl.choose_spec

/-- A colimiting cokernel cofork gives a weak cokernel. -/
theorem _root_.CategoryTheory.Limits.IsColimit.isWeakCokernel
    {X Y : C} {f : X ⟶ Y} {s : CokernelCofork f}
    (hs : IsColimit s) : IsWeakCokernel f s.π := by
  refine isWeakCokernel_iff.mpr ⟨CokernelCofork.condition s, fun _ k hk ↦ ?_⟩
  obtain ⟨l, hl⟩ := CokernelCofork.IsColimit.desc' hs k hk
  exact ⟨l, hl⟩

/-- A limiting kernel fork in the opposite category gives a weak cokernel. -/
theorem _root_.CategoryTheory.Limits.IsLimit.isWeakCokernel
    {X Y : Cᵒᵖ} {f : X ⟶ Y} {s : KernelFork f} (hs : IsLimit s) :
    IsWeakCokernel f.unop s.ι.unop :=
  hs.isWeakLimit.isWeakCokernel

/-- The zero endomorphism of the target is a weak cokernel of an epimorphism. -/
theorem IsWeakCokernel.zero_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] :
    IsWeakCokernel f (0 : Y ⟶ Y) :=
  isWeakCokernel_iff.mpr ⟨comp_zero, fun _ k hk ↦ ⟨0, by simp [zero_of_epi_comp f hk]⟩⟩

/-- Weak kernels in the opposite category supply weak cokernels in the original category. -/
theorem exists_isWeakCokernel {X Y : C} (f : X ⟶ Y) [HasWeakKernel f.op] :
    ∃ (Z : C) (q : Y ⟶ Z), IsWeakCokernel f q := by
  refine ⟨_, (weakKernel.ι f.op).unop, ?_⟩
  simpa only [Fork.ι_ofι, Quiver.Hom.unop_op] using
    (weakKernelIsWeakKernel f.op).isWeakCokernel

end TauCeti
