/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono

/-!
# Cokernels from torsor squares

An effective epimorphism of group objects whose kernel pair is the translation action of a
subgroup is the cokernel of that subgroup's inclusion. The descent of the underlying morphism
preserves multiplication when the square of the quotient map is epi. This criterion applies to
group objects in sheaves, including quotients which are not representable.

The construction uses Mathlib's `isColimitCoforkOfEffectiveEpi` to descend morphisms of carriers.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace CategoryTheory.Grp

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C]
variable {N G Q : Grp C}

/-- A torsor projection which is effective epi on carriers is the cokernel of its subgroup
inclusion, provided its product with itself is epi. -/
noncomputable def isColimitCokernelCoforkOfTorsor
    (i : N ⟶ G) (q : G ⟶ Q) (w : i ≫ q = 0)
    (h : IsPullback (fst G.X N.X)
      (fst G.X N.X * (snd G.X N.X ≫ i.hom.hom)) q.hom.hom q.hom.hom)
    [EffectiveEpi q.hom.hom] [Epi (q.hom.hom ⊗ₘ q.hom.hom)] :
    IsColimit (CokernelCofork.ofπ q w) := by
  letI : Epi q := ⟨fun f g hfg ↦ Grp.hom_ext _ _
    ((cancel_epi q.hom.hom).mp (congrArg (fun a ↦ a.hom.hom) hfg))⟩
  apply CokernelCofork.IsColimit.ofπ' q w
  intro T f hf
  have hf' : i.hom.hom ≫ f.hom.hom = 1 := by
    simpa [Hom.one_def] using congrArg (fun a ↦ a.hom.hom) hf
  have heq : fst G.X N.X ≫ f.hom.hom =
      (fst G.X N.X * (snd G.X N.X ≫ i.hom.hom)) ≫ f.hom.hom := by
    simp [MonObj.mul_comp, Category.assoc, hf']
  let lift := Cofork.IsColimit.desc'
    (isColimitCoforkOfEffectiveEpi q.hom.hom _ h.isLimit) f.hom.hom heq
  let d : Q.X ⟶ T.X := lift.1
  have hd' : q.hom.hom ≫ d = f.hom.hom := lift.2
  letI : IsMonHom d := {
    one_hom := by
      rw [← IsMonHom.one_hom q.hom.hom, Category.assoc, hd', IsMonHom.one_hom]
    mul_hom := by
      apply (cancel_epi (q.hom.hom ⊗ₘ q.hom.hom)).mp
      simp only [← Category.assoc, ← IsMonHom.mul_hom q.hom.hom]
      simp only [Category.assoc, hd', IsMonHom.mul_hom f.hom.hom]
      rw [← Category.assoc, tensorHom_comp_tensorHom, hd'] }
  exact ⟨Grp.homMk d, Grp.hom_ext _ _ hd'⟩

end CategoryTheory.Grp
