/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.Order.Interval.Set.Fin
public import TauCeti.LinearAlgebra.ExtendByZero

/-!
# Inclusion of finite coordinate spaces into finitely supported functions

For an `R`-module `M`, the coordinate inclusion `Finsupp.coordinateInclusion` embeds `Fin n → M`
into `ℕ →₀ M`, with range the functions supported on `Set.Iio n`. It commutes with extension by
zero between finite coordinate spaces. The coordinate restriction
`Finsupp.coordinateRestriction` is a left inverse, and an inverse on the functions supported on
`Finset.range n`.
These maps realize finite coordinate stages inside the countable coordinate space.
-/

public section

namespace Finsupp

open Set

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- The coordinate inclusion `M^n → ℕ →₀ M`, sending the `i`-th coordinate vector to the
`i`-th coordinate vector. -/
noncomputable def coordinateInclusion (n : ℕ) : (Fin n → M) →ₗ[R] (ℕ →₀ M) :=
  Finsupp.lmapDomain M R Fin.val ∘ₗ (Finsupp.linearEquivFunOnFinite R M (Fin n)).symm.toLinearMap

@[simp]
theorem coordinateInclusion_single (n : ℕ) (i : Fin n) (a : M) :
    coordinateInclusion (R := R) n (Pi.single i a) = Finsupp.single (i : ℕ) a := by
  simp [coordinateInclusion]

/-- The coordinate inclusion of `v` is the sum of the coordinate vectors `single i (v i)`. -/
theorem coordinateInclusion_eq_sum (n : ℕ) (v : Fin n → M) :
    coordinateInclusion (R := R) n v = ∑ i : Fin n, Finsupp.single (i : ℕ) (v i) := by
  simp [coordinateInclusion, Finsupp.mapDomain, Finsupp.sum_fintype]

@[simp]
theorem coordinateInclusion_apply_val {n : ℕ} (v : Fin n → M) (i : Fin n) :
    coordinateInclusion (R := R) n v i = v i := by
  simp [coordinateInclusion, Finsupp.mapDomain_apply_of_injective Fin.val_injective]

theorem coordinateInclusion_apply_of_le {n : ℕ} (v : Fin n → M) {i : ℕ} (hi : n ≤ i) :
    coordinateInclusion (R := R) n v i = 0 := by
  simp only [coordinateInclusion, LinearMap.coe_comp, Function.comp_apply,
    Finsupp.lmapDomain_apply]
  exact Finsupp.mapDomain_of_notMem_range _ _ (by simpa [Fin.range_val] using hi)

/-- The coordinates of `coordinateInclusion n v`: those of `v` below `n`, and `0` from `n` on. -/
theorem coordinateInclusion_apply {n : ℕ} (v : Fin n → M) (i : ℕ) :
    coordinateInclusion (R := R) n v i = if h : i < n then v ⟨i, h⟩ else 0 := by
  split_ifs with h
  · exact coordinateInclusion_apply_val v ⟨i, h⟩
  · exact coordinateInclusion_apply_of_le v (Nat.le_of_not_gt h)

theorem coordinateInclusion_injective (n : ℕ) :
    Function.Injective (coordinateInclusion (R := R) (M := M) n) :=
  (Finsupp.mapDomain_injective Fin.val_injective).comp
    (Finsupp.linearEquivFunOnFinite R M (Fin n)).symm.injective

/-- The image of the coordinate inclusion of `R^n` consists of the finitely supported functions
vanishing from coordinate `n` on. -/
theorem range_coordinateInclusion (n : ℕ) :
    LinearMap.range (coordinateInclusion (R := R) (M := M) n) = Finsupp.supported M R (Iio n) := by
  simpa [coordinateInclusion, LinearMap.range_comp, Fin.range_val] using
    Finsupp.lmapDomain_supported M R (Fin.val : Fin n → ℕ) univ

/-- Every vector in the image of `coordinateInclusion n` has support contained in
`Finset.range n`. -/
theorem support_coordinateInclusion_subset_range (n : ℕ) (v : Fin n → M) :
    (coordinateInclusion (R := R) n v).support ⊆ Finset.range n := fun _ hi ↦
  Finset.mem_range.2 <| lt_of_not_ge fun hni ↦
    Finsupp.mem_support_iff.1 hi (coordinateInclusion_apply_of_le v hni)

/-- A finitely supported function whose support lies in `Finset.range n` is recovered by restricting
to `Fin n` and applying `coordinateInclusion n`. -/
theorem coordinateInclusion_of_support_subset_range {n : ℕ} {v : ℕ →₀ M}
    (hv : v.support ⊆ Finset.range n) :
    coordinateInclusion (R := R) n (fun i : Fin n ↦ v i) = v := by
  ext m
  by_cases hm : m < n
  · exact coordinateInclusion_apply_val (fun i : Fin n ↦ v i) ⟨m, hm⟩
  · rw [coordinateInclusion_apply_of_le _ (Nat.le_of_not_gt hm)]
    exact (Finsupp.notMem_support_iff.1 fun hmem ↦ hm (Finset.mem_range.1 (hv hmem))).symm

/-- The coordinate inclusions are compatible with the inclusions `R^m → R^n` onto the first
coordinates. -/
@[simp]
theorem coordinateInclusion_comp_extendByZero_castLE {m n : ℕ} (h : m ≤ n) :
    coordinateInclusion (R := R) (M := M) n ∘ₗ Function.ExtendByZero.linearMap R M (Fin.castLE h) =
      coordinateInclusion m := by
  refine LinearMap.pi_ext fun i a ↦ ?_
  simp [Function.ExtendByZero.linearMap_single R (Fin.castLE_injective h)]

/-- The coordinate restriction `ℕ →₀ M → M^n`, keeping the first `n` coordinates. -/
noncomputable def coordinateRestriction (n : ℕ) : (ℕ →₀ M) →ₗ[R] (Fin n → M) :=
  LinearMap.pi fun i : Fin n ↦ Finsupp.lapply (i : ℕ)

@[simp]
theorem coordinateRestriction_apply (n : ℕ) (v : ℕ →₀ M) (i : Fin n) :
    coordinateRestriction (R := R) n v i = v i := by
  simp [coordinateRestriction]

/-- Restricting to the first `n` coordinates undoes the coordinate inclusion. -/
@[simp]
theorem coordinateRestriction_comp_coordinateInclusion (n : ℕ) :
    coordinateRestriction (R := R) (M := M) n ∘ₗ coordinateInclusion n = LinearMap.id :=
  LinearMap.ext fun v ↦ funext fun i ↦ by simp

/-- A finitely supported function vanishing from coordinate `n` on is recovered from its first
`n` coordinates. -/
theorem coordinateInclusion_coordinateRestriction {n : ℕ} {v : ℕ →₀ M}
    (hv : v ∈ Finsupp.supported M R (Finset.range n : Set ℕ)) :
    coordinateInclusion (R := R) n (coordinateRestriction (R := R) n v) = v :=
  coordinateInclusion_of_support_subset_range (by exact_mod_cast (mem_supported R v).1 hv)

end Finsupp
