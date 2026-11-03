/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.MulAction

/-!
# Strict generating systems of norm one

Let `N` be a submodule of a normed module `M` over a normed ring `A`. A finite set `F` of nonzero
elements of `N` generates `N` *strictly* when every `y ∈ N` is a combination `∑ x ∈ F, a x • x`
with `‖a x‖ * ‖x‖ ≤ ‖y‖`, so that no cancellation between the terms is needed to represent `y`.

When the norm of `A` is multiplicative and ultrametric, the action of `A` on `M` multiplies norms,
and the norm of every nonzero element of `N` is the norm of a unit of `A`, each generator can be
divided by such a unit. This gives a strict generating system of elements of norm one, with
coefficients bounded by `‖y‖` (`Submodule.exists_finset_norm_eq_one_of_exists_finset_eq_sum_smul`).
For ideals and submodules of finite free modules over a Tate algebra at unit polyradius the units
used for this normalisation can be chosen to be nonzero constants, whose norms are all the values
of the Gauss norm.
-/

public section

namespace Submodule

variable {A M : Type*} [NormedRing A] [NormMulClass A] [NormOneClass A] [IsUltrametricDist A]
  [SeminormedAddCommGroup M] [Module A M] [NormSMulClass A M]

/-- **Normalising a strict generating system.** Let `N` be a submodule of a normed module over
a ring with a multiplicative ultrametric norm, such that the norm of every nonzero element of `N`
is the norm of a unit. If finitely many nonzero elements `x` of `N` generate it strictly, with each
`y ∈ N` a combination `∑ x, a x • x` with `‖a x‖ * ‖x‖ ≤ ‖y‖`, then finitely many elements of `N`
of norm one generate it with coefficients `‖a x‖ ≤ ‖y‖`. -/
theorem exists_finset_norm_eq_one_of_exists_finset_eq_sum_smul {N : Submodule A M}
    (hunit : ∀ x ∈ N, x ≠ 0 → ∃ u : A, IsUnit u ∧ ‖u‖ = ‖x‖)
    (hN : ∃ F : Finset M, (∀ x ∈ F, x ∈ N ∧ x ≠ 0) ∧
      ∀ y ∈ N, ∃ a : M → A, y = ∑ x ∈ F, a x • x ∧ ∀ x ∈ F, ‖a x‖ * ‖x‖ ≤ ‖y‖) :
    ∃ F : Finset M, (∀ x ∈ F, x ∈ N ∧ ‖x‖ = 1) ∧
      ∀ y ∈ N, ∃ a : M → A, y = ∑ x ∈ F, a x • x ∧ ∀ x ∈ F, ‖a x‖ ≤ ‖y‖ := by
  classical
  obtain ⟨F, hFN, hF⟩ := hN
  have hunit' (x) (hx : x ∈ F) : ∃ u : Aˣ, ‖(u : A)‖ = ‖x‖ := by
    obtain ⟨u, hu, hux⟩ := hunit x (hFN x hx).1 (hFN x hx).2
    exact ⟨hu.unit, hux⟩
  choose! u hu using hunit'
  -- Dividing each generator `x` by the unit `u x`, of the same norm, normalises it to norm one.
  let g x := (↑(u x)⁻¹ : A) • x
  refine ⟨F.image g, ?_, fun y hy ↦ ?_⟩
  · simp only [Finset.mem_image, forall_exists_index, and_imp]
    rintro _ x hx rfl
    refine ⟨N.smul_mem _ (hFN x hx).1, ?_⟩
    simp only [g]
    rw [norm_smul, ← hu x hx, ← norm_mul, Units.inv_mul, norm_one]
  obtain ⟨a, rfl, ha⟩ := hF y hy
  refine ⟨fun z ↦ ∑ x ∈ F with g x = z, a x * u x, ?_, fun z _ ↦ ?_⟩
  · simp only [Finset.sum_smul]
    calc ∑ x ∈ F, a x • x = ∑ x ∈ F, (a x * u x) • g x :=
          Finset.sum_congr rfl fun x _ ↦ by
            simp only [g]
            rw [mul_smul, ← mul_smul (u x : A), Units.mul_inv, one_smul]
      _ = ∑ z ∈ F.image g, ∑ x ∈ F with g x = z, (a x * u x) • g x :=
          (Finset.sum_fiberwise_of_maps_to (fun x hx ↦ Finset.mem_image_of_mem g hx) _).symm
      _ = ∑ z ∈ F.image g, ∑ x ∈ F with g x = z, (a x * u x) • z :=
          Finset.sum_congr rfl fun z _ ↦ Finset.sum_congr rfl fun x hx ↦ by
            rw [(Finset.mem_filter.mp hx).2]
  · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun x hx ↦ ?_
    rw [norm_mul, hu x (Finset.mem_filter.mp hx).1]
    exact ha x (Finset.mem_filter.mp hx).1

end Submodule
