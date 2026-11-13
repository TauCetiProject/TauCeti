/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Projection

/-!
# Projections along the range of `L` onto the kernel of `P`

Let `L : X →ₗ[R] Y` and `P : Y →ₗ[R] Z` be linear maps whose composite `P ∘ L` is bijective. Then
the range of `L` and the kernel of `P` are complementary submodules of `Y`
(`LinearMap.isCompl_range_ker_of_bijective_comp`), and conversely `P ∘ L` is bijective exactly
when `L` is injective, `P` is surjective and these two submodules are complementary
(`LinearMap.bijective_comp_iff`). Writing `A : X ≃ₗ[R] Z` for the equivalence given by `P ∘ L`,
the two projections of the splitting `Y = range L ⊕ ker P` are explicit:

* `L A⁻¹ P` is the projection onto `range L` along `ker P`
  (`LinearMap.comp_comp_eq_projection`);
* `id - L A⁻¹ P` is the projection onto `ker P` along `range L`
  (`LinearMap.id_sub_comp_comp_eq_projection`).

In particular `L A⁻¹ P` and `A⁻¹ P` depend only on `L` and on the kernel `W = ker P`, not on `P`
itself (`LinearMap.comp_comp_eq_of_ker_eq`, `LinearMap.symm_comp_eq_of_ker_eq`).

This is the algebra of the Lyapunov–Schmidt reduction. To solve `L f + S = 0` for an injective
linear map `L` (in practice, `L` restricted to a complement of its kernel) whose range has a
complement `W`, choose any surjective `P` with kernel `W`; then `A = P L` is invertible by
`LinearMap.bijective_comp_iff`.
The vector `f = -A⁻¹ P S` is the unique one with `L f + S ∈ W`
(`LinearMap.add_mem_ker_iff_eq_neg_symm`), and then `L f + S = S - L A⁻¹ P S` is the projection of
`S` onto `W` along `range L`. That projection vanishes exactly when `S ∈ range L`
(`LinearMap.sub_apply_symm_apply_eq_zero_iff`), so the equation `L f + S = 0` is reduced to an
equation in `W`.

## References

* S.-N. Chow and J. K. Hale, *Methods of Bifurcation Theory*, Springer, 1982, §2.4.
-/

public section

namespace LinearMap

open Submodule

variable {R X Y Z : Type*} [Ring R] [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
  [AddCommGroup Z] [Module R Z] {L : X →ₗ[R] Y} {P : Y →ₗ[R] Z}

/-- If `P ∘ L` is bijective, then the range of `L` and the kernel of `P` are complementary. -/
theorem isCompl_range_ker_of_bijective_comp (h : Function.Bijective (P ∘ₗ L)) :
    IsCompl (range L) (ker P) := by
  refine ⟨?_, ?_⟩
  · rw [Submodule.disjoint_def]
    rintro _ ⟨x, rfl⟩ hx
    have hx0 : x = 0 := h.1 (by simpa using hx)
    simp [hx0]
  · rw [codisjoint_iff_le_sup]
    intro y _
    obtain ⟨x, hx⟩ := h.2 (P y)
    refine Submodule.mem_sup.2 ⟨L x, mem_range_self L x, y - L x, ?_, add_sub_cancel _ _⟩
    simpa [sub_eq_zero] using hx.symm

/-- `P ∘ L` is bijective exactly when `L` is injective, `P` is surjective, and the range of `L`
is complementary to the kernel of `P`. -/
theorem bijective_comp_iff :
    Function.Bijective (P ∘ₗ L) ↔
      Function.Injective L ∧ Function.Surjective P ∧ IsCompl (range L) (ker P) := by
  refine ⟨fun h => ?_, ?_⟩
  · have h' := h
    rw [coe_comp] at h'
    exact ⟨h'.1.of_comp, h'.2.of_comp, isCompl_range_ker_of_bijective_comp h⟩
  rintro ⟨hL, hP, hc⟩
  refine ⟨fun x x' hxx' => hL ?_, fun z => ?_⟩
  · have hmem : L (x - x') ∈ range L ⊓ ker P :=
      ⟨mem_range_self L _, by simpa [sub_eq_zero] using hxx'⟩
    rw [hc.inf_eq_bot, Submodule.mem_bot, map_sub, sub_eq_zero] at hmem
    exact hmem
  · obtain ⟨y, rfl⟩ := hP z
    obtain ⟨_, ⟨x, rfl⟩, k, hk, hy⟩ :=
      Submodule.mem_sup.1 (hc.sup_eq_top ▸ Submodule.mem_top (x := y))
    refine ⟨x, ?_⟩
    rw [mem_ker] at hk
    simp [← hy, hk]

variable (A : X ≃ₗ[R] Z) (hA : P ∘ₗ L = A)
include hA

/-- If `P ∘ L` is the equivalence `A`, then `P (L x) = A x`. -/
private theorem apply_apply_eq_of_comp_eq (x : X) : P (L x) = A x :=
  congr($hA x)

/-- If `P ∘ L` is the equivalence `A`, then `L A⁻¹ P` is the projection onto the range of `L`
along the kernel of `P`. -/
theorem comp_comp_eq_projection :
    L ∘ₗ A.symm.toLinearMap ∘ₗ P =
      (range L).projection (ker P) (isCompl_range_ker_of_bijective_comp (hA ▸ A.bijective)) := by
  ext y
  have hk : y - L (A.symm (P y)) ∈ ker P := by
    simp [mem_ker, apply_apply_eq_of_comp_eq A hA]
  conv_rhs => rw [← add_sub_cancel (L (A.symm (P y))) y]
  rw [map_add, projection_apply_of_mem_left _ (mem_range_self L _),
    projection_apply_of_mem_right _ hk, add_zero]
  simp

/-- If `P ∘ L` is the equivalence `A`, then `id - L A⁻¹ P` is the projection onto the kernel of
`P` along the range of `L`. -/
theorem id_sub_comp_comp_eq_projection :
    LinearMap.id - L ∘ₗ A.symm.toLinearMap ∘ₗ P =
      (ker P).projection (range L)
        (isCompl_range_ker_of_bijective_comp (hA ▸ A.bijective)).symm := by
  rw [comp_comp_eq_projection A hA]
  exact (projection_eq_id_sub_projection _).symm

/-- If `P ∘ L` is the equivalence `A`, then `y - L A⁻¹ P y` vanishes exactly when `y` lies in the
range of `L`. -/
theorem sub_apply_symm_apply_eq_zero_iff {y : Y} : y - L (A.symm (P y)) = 0 ↔ y ∈ range L := by
  rw [← projection_apply_eq_zero_iff
      (isCompl_range_ker_of_bijective_comp (L := L) (P := P) (hA ▸ A.bijective)).symm,
    ← id_sub_comp_comp_eq_projection A hA]
  simp

/-- If `P ∘ L` is the equivalence `A`, then `x = -A⁻¹ P y` is the unique vector with
`L x + y ∈ ker P`. -/
theorem add_mem_ker_iff_eq_neg_symm {x : X} {y : Y} :
    L x + y ∈ ker P ↔ x = -A.symm (P y) := by
  rw [mem_ker, map_add, apply_apply_eq_of_comp_eq A hA, add_eq_zero_iff_eq_neg,
    ← map_neg A.symm, A.eq_symm_apply]

omit hA in
/-- The projection `L A⁻¹ P` onto the range of `L` depends on `P` only through its kernel: if
`P ∘ L = A` and `P' ∘ L = A'` are equivalences and `ker P = ker P'`, then
`L A⁻¹ P = L A'⁻¹ P'`. -/
theorem comp_comp_eq_of_ker_eq {Z' : Type*} [AddCommGroup Z'] [Module R Z'] {P' : Y →ₗ[R] Z'}
    (A' : X ≃ₗ[R] Z') (hA : P ∘ₗ L = A) (hA' : P' ∘ₗ L = A') (hker : ker P = ker P') :
    L ∘ₗ A.symm.toLinearMap ∘ₗ P = L ∘ₗ A'.symm.toLinearMap ∘ₗ P' := by
  simp only [comp_comp_eq_projection A hA, comp_comp_eq_projection A' hA', hker]

omit hA in
/-- The map `A⁻¹ P` depends on `P` only through its kernel: if `P ∘ L = A` and `P' ∘ L = A'` are
equivalences and `ker P = ker P'`, then `A⁻¹ P = A'⁻¹ P'`. -/
theorem symm_comp_eq_of_ker_eq {Z' : Type*} [AddCommGroup Z'] [Module R Z'] {P' : Y →ₗ[R] Z'}
    (A' : X ≃ₗ[R] Z') (hA : P ∘ₗ L = A) (hA' : P' ∘ₗ L = A') (hker : ker P = ker P') :
    A.symm.toLinearMap ∘ₗ P = A'.symm.toLinearMap ∘ₗ P' := by
  have hL : Function.Injective L := (bijective_comp_iff.1 (by rw [hA]; exact A.bijective)).1
  ext y
  exact hL congr($(comp_comp_eq_of_ker_eq A A' hA hA' hker) y)

end LinearMap
