/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import TauCeti.CategoryTheory.Monoidal.Grp.Basic

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
  have hw := congrArg (lift (1 : N.X ⟶ G.X) (𝟙 N.X) ≫ ·) h.w
  simp only [← Category.assoc, MonObj.comp_mul, lift_fst, one_mul] at hw
  simpa [Hom.one_def] using hw.symm

/-- The subgroup in a torsor kernel-pair square is the categorical kernel of the
projection. -/
noncomputable def isLimitKernelForkOfIsPullback
    (h : IsPullback (fst G.X N.X)
      (fst G.X N.X * (snd G.X N.X ≫ i.hom.hom)) q.hom.hom q.hom.hom) :
    IsLimit (KernelFork.ofι i (comp_eq_zero_of_commSq i q h.toCommSq)) := by
  have : Mono i.hom.hom := ⟨fun {T} a b hab ↦ by
    have he : lift (1 : T ⟶ G.X) a = lift (1 : T ⟶ G.X) b :=
      h.hom_ext (by simp) (by simpa [MonObj.comp_mul] using hab)
    simpa using congrArg (· ≫ snd G.X N.X) he⟩
  refine KernelFork.IsLimit.ofι' _ _ fun {T} f hf ↦ ?_
  have hw : (1 : T.X ⟶ G.X) ≫ q.hom.hom = f.hom.hom ≫ q.hom.hom := by
    simpa [Hom.one_def] using (congrArg (fun f ↦ f.hom.hom) hf).symm
  let l := h.lift 1 f.hom.hom hw
  have hl : (l ≫ snd G.X N.X) ≫ i.hom.hom = f.hom.hom := by
    simpa [l, MonObj.comp_mul, ← Category.assoc] using h.lift_snd 1 f.hom.hom hw
  have : IsMonHom (l ≫ snd G.X N.X) :=
    { one_hom := (cancel_mono i.hom.hom).mp (by simp [hl])
      mul_hom := (cancel_mono i.hom.hom).mp (by simp [hl]) }
  exact ⟨Grp.homMk (l ≫ snd G.X N.X), Grp.hom_ext _ _ hl⟩

end CategoryTheory.Grp
