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
theorem _root_.CategoryTheory.Functor.right_minimal_iff_map_comp_eq_zero
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
    simpa only [Functor.id_map] using (𝟭 C).right_minimal_iff_map_comp_eq_zero g
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
  let e := opEquiv (op Y) (op Y)
  have hrad (a : op Y ⟶ op Y) :
      a ∈ jacobsonRadical (op Y) (op Y) ↔ a.unop ∈ jacobsonRadical Y Y := by
    rw [mem_jacobsonRadical_iff_isIso_id_sub_comp_left,
      mem_jacobsonRadical_iff_isIso_id_sub_comp_right]
    exact e.forall_congr fun b ↦ by
      simp only [e, opEquiv, Equiv.coe_fn_mk, ← isIso_unop_iff, unop_sub, unop_id, unop_comp]
  rw [← e.forall_congr_right, ← e.forall_congr_right]
  simpa only [e, opEquiv, Equiv.coe_fn_mk, Functor.id_map, ← Quiver.Hom.unop_inj.eq_iff,
    unop_comp, Quiver.Hom.unop_op, unop_zero, isIso_unop_iff, hrad] using
    (𝟭 Cᵒᵖ).right_minimal_iff_map_comp_eq_zero f.op

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
theorem _root_.CategoryTheory.Limits.IsLimit.right_minimal_iff_mem_jacobsonRadical {w : f ≫ g = 0}
    (h : IsLimit (KernelFork.ofι f w)) :
    (∀ b : Y ⟶ Y, b ≫ g = g → IsIso b) ↔ f ∈ jacobsonRadical X Y :=
  (h.exact_postcomp Y).right_minimal_iff_mem_jacobsonRadical

/-- A map with a cokernel is left minimal exactly when its cokernel map lies in the radical. -/
theorem _root_.CategoryTheory.Limits.IsColimit.left_minimal_iff_mem_jacobsonRadical {w : f ≫ g = 0}
    (h : IsColimit (CokernelCofork.ofπ g w)) :
    (∀ b : Y ⟶ Y, f ≫ b = f → IsIso b) ↔ g ∈ jacobsonRadical Y Z :=
  (h.exact_precomp Y).left_minimal_iff_mem_jacobsonRadical

end TauCeti
