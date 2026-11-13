/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.GroupTheory.CoprodI

/-!
# Splitting off one factor of a free product

For a family of monoids `M : ι → Type*` and an index `i`, the indexed free product `∗ⱼ Mⱼ` is the
free product of `Mᵢ` and of the indexed free product of the other factors. A trivial factor of a
binary free product can be dropped: if `N` is trivial, the inclusion of `M` into `M ∗ N` is onto.

## Main definitions

* `Monoid.CoprodI.ofCoprodNe`: the homomorphism `Mᵢ ∗ (∗_{j ≠ i} Mⱼ) →* ∗ⱼ Mⱼ`.

## Main results

* `Monoid.CoprodI.ofCoprodNe_bijective`: it is bijective.
* `Monoid.Coprod.inl_surjective`, `Monoid.Coprod.inr_surjective`: if one factor of a free product
  `M ∗ N` is trivial, the inclusion of the other one is onto.
-/

public section

open Function
open scoped Monoid.Coprod

namespace Monoid.Coprod

variable {M N : Type*} [MulOneClass M] [MulOneClass N]

/-- If `N` is trivial, every element of the free product `M ∗ N` comes from `M`. -/
theorem inl_surjective [Subsingleton N] : Surjective (inl : M →* M ∗ N) := fun x ↦ by
  induction x using induction_on with
  | inl m => exact ⟨m, rfl⟩
  | inr n => exact ⟨1, by simp [Subsingleton.elim n 1]⟩
  | mul x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a * b, map_mul _ _ _⟩

/-- If `M` is trivial, every element of the free product `M ∗ N` comes from `N`. -/
theorem inr_surjective [Subsingleton M] : Surjective (inr : N →* M ∗ N) := by
  rw [← swap_comp_inl, MonoidHom.coe_comp]
  exact swap_surjective.comp inl_surjective

end Monoid.Coprod

namespace Monoid.CoprodI

variable {ι : Type*} (M : ι → Type*) [∀ i, Monoid (M i)] (i : ι)

/-- The homomorphism from the free product of `M i` and of the indexed free product of the other
factors to the indexed free product of all the factors. -/
def ofCoprodNe : M i ∗ (CoprodI fun j : {j // j ≠ i} ↦ M j) →* CoprodI M :=
  Coprod.lift of (lift fun j ↦ of (i := j.1))

@[simp]
theorem ofCoprodNe_inl (m : M i) : ofCoprodNe M i (Coprod.inl m) = of m := by
  simp [ofCoprodNe]

@[simp]
theorem ofCoprodNe_inr_of (j : {j // j ≠ i}) (m : M j) :
    ofCoprodNe M i (Coprod.inr (of m)) = of (i := j.1) m := by
  simp [ofCoprodNe]

/-- An indexed free product is the free product of any one of its factors and of the indexed free
product of the others. -/
theorem ofCoprodNe_bijective : Bijective (ofCoprodNe M i) := by
  classical
  -- the inverse sends `M i` to the left factor and each `M j`, `j ≠ i`, to the right one
  let g : CoprodI M →* M i ∗ (CoprodI fun j : {j // j ≠ i} ↦ M j) :=
    lift fun j ↦ if h : j = i then h ▸ Coprod.inl
      else Coprod.inr.comp (of (M := fun j : {j // j ≠ i} ↦ M j) (i := ⟨j, h⟩))
  have hg : (ofCoprodNe M i).comp g = .id _ := ext_hom _ _ fun j ↦ by
    by_cases h : j = i
    · subst h; ext m; simp [g]
    · ext m; simp [g, h]
  have hg' : g.comp (ofCoprodNe M i) = .id _ :=
    Coprod.hom_ext (by ext m; simp [g]) (ext_hom _ _ fun j ↦ by ext m; simp [g, j.2])
  exact bijective_iff_has_inverse.2 ⟨g, DFunLike.congr_fun hg', DFunLike.congr_fun hg⟩

end Monoid.CoprodI
