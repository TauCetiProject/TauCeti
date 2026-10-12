/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Kernels from torsor squares of group objects

If the kernel pair of `q : G ⟶ Q` is `G × N`, with its two maps given by
`(g, n) ↦ g` and `(g, n) ↦ g i(n)`, then `i : N ⟶ G` is the categorical
kernel of `q`. This criterion applies in any cartesian monoidal category, in particular
to group objects in sheaves, without assuming that quotient sections lift globally.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace CategoryTheory.Grp

variable {C : Type*} [Category C] [CartesianMonoidalCategory C]
variable {N G Q : Grp C} (i : N ⟶ G) (q : G ⟶ Q)

/-- Commutativity of a torsor square forces the subgroup map to have trivial composite
with the projection. -/
theorem comp_eq_zero_of_commSq
    (h : CommSq (fst G.X N.X)
      (fst G.X N.X * (snd G.X N.X ≫ i.hom.hom)) q.hom.hom q.hom.hom) :
    i ≫ q = 0 := by
  apply Grp.hom_ext
  have hw := congrArg (fun f ↦ lift (1 : N.X ⟶ G.X) (𝟙 N.X) ≫ f) h.w
  simp only [← Category.assoc, MonObj.comp_mul, lift_fst, lift_snd,
    Category.id_comp, one_mul, MonObj.one_comp] at hw
  simpa [Hom.one_def] using hw.symm

/-- The subgroup in a torsor kernel-pair square is the categorical kernel of the
projection. -/
noncomputable def isLimitKernelForkOfIsPullback
    (h : IsPullback (fst G.X N.X)
      (fst G.X N.X * (snd G.X N.X ≫ i.hom.hom)) q.hom.hom q.hom.hom) :
    IsLimit (KernelFork.ofι i (comp_eq_zero_of_commSq i q h.toCommSq)) := by
  have hi : Mono i.hom.hom := ⟨fun {T} a b hab ↦ by
    have he : lift (1 : T ⟶ G.X) a = lift (1 : T ⟶ G.X) b := by
      apply h.hom_ext
      · simp
      · simpa [MonObj.comp_mul] using hab
    simpa using congrArg (fun f ↦ f ≫ snd G.X N.X) he⟩
  have : Mono i := ⟨fun {T} a b hab ↦ Grp.hom_ext _ _
    ((cancel_mono i.hom.hom).mp (congrArg (fun f ↦ f.hom.hom) hab))⟩
  apply KernelFork.IsLimit.ofι'
  intro T f hf
  have hf' : f.hom.hom ≫ q.hom.hom = 1 := by
    simpa [Hom.one_def] using congrArg (fun f ↦ f.hom.hom) hf
  let l := h.lift (1 : T.X ⟶ G.X) f.hom.hom (by simp [hf'])
  have hl : (l ≫ snd G.X N.X) ≫ i.hom.hom = f.hom.hom := by
    have hs := h.lift_snd (1 : T.X ⟶ G.X) f.hom.hom (by simp [hf'])
    simpa [l, MonObj.comp_mul, ← Category.assoc] using hs
  let : IsMonHom (l ≫ snd G.X N.X) := {
    one_hom := by
      apply (cancel_mono i.hom.hom).mp
      simp [Category.assoc, hl]
    mul_hom := by
      apply (cancel_mono i.hom.hom).mp
      simp only [Category.assoc, hl, IsMonHom.mul_hom]
      rw [← Category.assoc, tensorHom_comp_tensorHom, hl] }
  exact ⟨Grp.homMk (l ≫ snd G.X N.X), Grp.hom_ext _ _ hl⟩

end CategoryTheory.Grp
