/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import TauCeti.CategoryTheory.Preadditive.Radical.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import TauCeti.CategoryTheory.Limits.Shapes.Kernels

/-!
# The radical criterion for minimal morphisms

In a preadditive category, right minimality of `g : Y ⟶ Z` means that every endomorphism
`b : Y ⟶ Y` with `b ≫ g = g` is invertible. If `X ⟶ Y ⟶ Z` induces an exact sequence
on applying `Hom(Y, -)`, this is equivalent to the first map lying in the radical. The dual
criterion tests left minimality of the first map using `Hom(-, Y)`.

The underlying criterion for `p : F.obj Y ⟶ T` tests the endomorphisms of `Y` killed by
`F.map (-) ≫ p`, where `F` is additive. It also applies to representable projective covers.

The kernel and cokernel forms apply to conflations in an exact category.

## References

* G. Jasso and S. Kvamme, *An introduction to higher Auslander–Reiten theory*,
  Bull. Lond. Math. Soc. **51** (2019), 1–24, Lemma 1.1.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite

namespace TauCeti

variable {C : Type*} [Category* C] [Preadditive C] {X Y Z : C}
  {f : X ⟶ Y} {g : Y ⟶ Z}

/-- All endomorphisms of `Y` fixing `p` under `F.map (-) ≫ p` are invertible exactly when
all endomorphisms killed by this operation lie in the radical. -/
theorem _root_.CategoryTheory.Functor.isIso_of_map_comp_eq_self_iff_forall_mem_jacobsonRadical
    {D : Type*} [Category* D] [Preadditive D] (F : C ⥤ D) [F.Additive]
    {T : D} (p : F.obj Y ⟶ T) :
    (∀ b : Y ⟶ Y, F.map b ≫ p = p → IsIso b) ↔
      ∀ a : Y ⟶ Y, F.map a ≫ p = 0 → a ∈ jacobsonRadical Y Y := by
  constructor
  · intro hmin a ha
    refine mem_jacobsonRadical_iff_isIso_id_sub_comp_left.mpr fun b ↦ hmin _ ?_
    simp [sub_comp, ha]
  · intro hrad b hb
    have ha := hrad (𝟙 Y - b) (by simp [sub_comp, hb])
    simpa using mem_jacobsonRadical_iff_isIso_id_sub_comp_right.mp ha (𝟙 Y)

/-- If `Hom(Y, X) ⟶ Hom(Y, Y) ⟶ Hom(Y, Z)` is exact, then `g` is right minimal
exactly when `f` lies in the radical. -/
theorem _root_.Function.Exact.right_minimal_iff_mem_jacobsonRadical
    (h : Function.Exact (fun a : Y ⟶ X ↦ a ≫ f) (fun b : Y ⟶ Y ↦ b ≫ g)) :
    (∀ b : Y ⟶ Y, b ≫ g = g → IsIso b) ↔ f ∈ jacobsonRadical X Y := by
  have hmin : (∀ b : Y ⟶ Y, b ≫ g = g → IsIso b) ↔
      ∀ a : Y ⟶ Y, a ≫ g = 0 → a ∈ jacobsonRadical Y Y := by
    simpa only [Functor.id_map] using
      (𝟭 C).isIso_of_map_comp_eq_self_iff_forall_mem_jacobsonRadical g
  rw [hmin]
  constructor
  · intro hrad
    refine mem_jacobsonRadical_iff_isIso_id_sub_comp_left.mpr fun a ↦ ?_
    simpa using mem_jacobsonRadical_iff_isIso_id_sub_comp_left.mp
      (hrad (a ≫ f) (h.apply_apply_eq_zero a)) (𝟙 Y)
  · intro hf b hb
    obtain ⟨a, rfl⟩ := (h b).mp hb
    exact comp_mem_jacobsonRadical_left a hf

/-- A morphism is left minimal exactly when the endomorphisms it kills by precomposition
lie in the radical. -/
theorem _root_.Quiver.Hom.left_minimal_iff_forall_mem_jacobsonRadical (f : X ⟶ Y) :
    (∀ b : Y ⟶ Y, f ≫ b = f → IsIso b) ↔
      ∀ a : Y ⟶ Y, f ≫ a = 0 → a ∈ jacobsonRadical Y Y := by
  rw [← (opEquiv (op Y) (op Y)).forall_congr_right,
    ← (opEquiv (op Y) (op Y)).forall_congr_right]
  simp only [opEquiv_apply (op Y) (op Y), isIso_unop_iff]
  simpa only [Functor.id_map, ← Quiver.Hom.unop_inj.eq_iff, unop_comp,
    Quiver.Hom.unop_op, unop_zero, mem_jacobsonRadical_iff_unop] using
    (𝟭 Cᵒᵖ).isIso_of_map_comp_eq_self_iff_forall_mem_jacobsonRadical f.op

/-- If `Hom(Z, Y) ⟶ Hom(Y, Y) ⟶ Hom(X, Y)` is exact, then `f` is left minimal
exactly when `g` lies in the radical. -/
theorem _root_.Function.Exact.left_minimal_iff_mem_jacobsonRadical
    (h : Function.Exact (fun a : Z ⟶ Y ↦ g ≫ a) (fun b : Y ⟶ Y ↦ f ≫ b)) :
    (∀ b : Y ⟶ Y, f ≫ b = f → IsIso b) ↔ g ∈ jacobsonRadical Y Z := by
  rw [f.left_minimal_iff_forall_mem_jacobsonRadical]
  constructor
  · intro hrad
    refine mem_jacobsonRadical_iff_isIso_id_sub_comp_right.mpr fun a ↦ ?_
    simpa using mem_jacobsonRadical_iff_isIso_id_sub_comp_right.mp
      (hrad (g ≫ a) (h.apply_apply_eq_zero a)) (𝟙 Y)
  · intro hg b hb
    obtain ⟨a, rfl⟩ := (h b).mp hb
    exact comp_mem_jacobsonRadical_right hg a

/-- A map with a kernel is right minimal exactly when its kernel map lies in the radical. -/
theorem _root_.CategoryTheory.Limits.IsLimit.right_minimal_iff_mem_jacobsonRadical
    {s : KernelFork g} (h : IsLimit s) :
    (∀ b : Y ⟶ Y, b ≫ g = g → IsIso b) ↔ s.ι ∈ jacobsonRadical s.pt Y :=
  (h.exact_postcomp Y).right_minimal_iff_mem_jacobsonRadical

/-- A map with a cokernel is left minimal exactly when its cokernel map lies in the radical. -/
theorem _root_.CategoryTheory.Limits.IsColimit.left_minimal_iff_mem_jacobsonRadical
    {s : CokernelCofork f} (h : IsColimit s) :
    (∀ b : Y ⟶ Y, f ≫ b = f → IsIso b) ↔ s.π ∈ jacobsonRadical Y s.pt :=
  (h.exact_precomp Y).left_minimal_iff_mem_jacobsonRadical

end TauCeti
