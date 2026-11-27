/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import TauCeti.CategoryTheory.Preadditive.Radical.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# The radical criterion for minimal morphisms

In a preadditive category, right minimality of `g : Y ⟶ Z` means that every endomorphism
`b : Y ⟶ Y` with `b ≫ g = g` is invertible. If `X ⟶ Y ⟶ Z` induces an exact sequence
on applying `Hom(Y, -)`, this is equivalent to the first map lying in the radical. The dual
criterion tests left minimality of the first map using `Hom(-, Y)`.

The kernel and cokernel forms apply to conflations in an exact category.

## References

* G. Jasso and S. Kvamme, *An introduction to higher Auslander–Reiten theory*,
  Bull. Lond. Math. Soc. **51** (2019), 1–24, Lemma 1.1.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

namespace TauCeti

variable {C : Type*} [Category* C] [Preadditive C] {X Y Z : C}
  {f : X ⟶ Y} {g : Y ⟶ Z}

/-- If `Hom(Y, X) ⟶ Hom(Y, Y) ⟶ Hom(Y, Z)` is exact, then `g` is right minimal
exactly when `f` lies in the radical. -/
theorem right_minimal_iff_mem_jacobsonRadical
    (h : Function.Exact (fun a : Y ⟶ X ↦ a ≫ f) (fun b : Y ⟶ Y ↦ b ≫ g)) :
    (∀ b : Y ⟶ Y, b ≫ g = g → IsIso b) ↔ f ∈ jacobsonRadical X Y := by
  rw [mem_jacobsonRadical_iff_isIso_id_sub_comp_left]
  constructor
  · intro hmin a
    exact hmin _ (by simp [sub_comp, h.apply_apply_eq_zero a])
  · intro hrad b hb
    obtain ⟨a, ha⟩ := (h (𝟙 Y - b)).mp (by simp [sub_comp, hb])
    simpa [ha] using hrad a

/-- If `Hom(Z, Y) ⟶ Hom(Y, Y) ⟶ Hom(X, Y)` is exact, then `f` is left minimal
exactly when `g` lies in the radical. -/
theorem left_minimal_iff_mem_jacobsonRadical
    (h : Function.Exact (fun a : Z ⟶ Y ↦ g ≫ a) (fun b : Y ⟶ Y ↦ f ≫ b)) :
    (∀ b : Y ⟶ Y, f ≫ b = f → IsIso b) ↔ g ∈ jacobsonRadical Y Z := by
  rw [mem_jacobsonRadical_iff_isIso_id_sub_comp_right]
  constructor
  · intro hmin a
    exact hmin _ (by simp [comp_sub, h.apply_apply_eq_zero a])
  · intro hrad b hb
    obtain ⟨a, ha⟩ := (h (𝟙 Y - b)).mp (by simp [comp_sub, hb])
    simpa [ha] using hrad a

/-- A map with a kernel is right minimal exactly when its kernel map lies in the radical. -/
theorem _root_.CategoryTheory.Limits.IsLimit.right_minimal_iff_mem_jacobsonRadical {w : f ≫ g = 0}
    (h : IsLimit (KernelFork.ofι f w)) :
    (∀ b : Y ⟶ Y, b ≫ g = g → IsIso b) ↔ f ∈ jacobsonRadical X Y := by
  refine TauCeti.right_minimal_iff_mem_jacobsonRadical fun b ↦ ⟨?_, ?_⟩
  · intro hb
    obtain ⟨a, ha⟩ := KernelFork.IsLimit.lift' h b hb
    exact ⟨a, ha⟩
  · rintro ⟨a, rfl⟩
    simp [Category.assoc, w]

/-- A map with a cokernel is left minimal exactly when its cokernel map lies in the radical. -/
theorem _root_.CategoryTheory.Limits.IsColimit.left_minimal_iff_mem_jacobsonRadical {w : f ≫ g = 0}
    (h : IsColimit (CokernelCofork.ofπ g w)) :
    (∀ b : Y ⟶ Y, f ≫ b = f → IsIso b) ↔ g ∈ jacobsonRadical Y Z := by
  refine TauCeti.left_minimal_iff_mem_jacobsonRadical fun b ↦ ⟨?_, ?_⟩
  · intro hb
    obtain ⟨a, ha⟩ := CokernelCofork.IsColimit.desc' h b hb
    exact ⟨a, ha⟩
  · rintro ⟨a, rfl⟩
    simp [← Category.assoc, w]

end TauCeti
