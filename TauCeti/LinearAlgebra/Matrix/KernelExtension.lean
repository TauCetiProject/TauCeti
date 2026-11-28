/-
Copyright (c) 2026 TauCeti Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Kernel extensions of left-invertible matrix bases

Given a matrix `A : Matrix σ P k`, a matrix `x : Matrix P σ k` with `(A * x).det ≠ 0`, and a
subspace `L ≤ P → k` containing the column span of `x`, this file constructs a matrix
`y : Matrix P (Fin s) k` whose columns form a basis of `L ⊓ ker A` and extend `x` to a
left-invertible basis `[x | y]` of `L`.

## Main definitions and results

* `TauCeti.mul_eq_zero_of_range_mulVecLin_le_ker`: if the column span of `y` lies in `ker A`,
  then `A * y = 0`.
* `TauCeti.exists_leftInv_range_mulVecLin_eq`: every subspace `L ≤ P → k` is the column span of a
  left-invertible matrix `y : Matrix P (Fin (Module.finrank k L)) k`.
* `TauCeti.IsKernelExtension`: predicate packaging a basis `y` of `L ⊓ ker A` extending `x` to a
  basis of `L`.
* `TauCeti.exists_isKernelExtension`: existence of a kernel extension whenever `(A * x).det ≠ 0`
  and `range x.mulVecLin ≤ L`.

## Provenance

Adapted from `grh-lean` (`https://github.com/lsernau/grh-lean`, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), file `src/New/Spanning/RemainingTerms/SiegelLemma.lean`
(`New.Filling.mul_eq_zero_of_colSpan_le_ker`, `New.Filling.IsKernelExtension`,
`New.Filling.exists_isKernelExtension`).
-/

@[expose] public section

namespace TauCeti

open Matrix

section KernelExtension

variable {k σ P τ : Type*} [Field k] [Fintype P]

/-- If the column span of `y` lies in the kernel of `A`, then `A * y = 0`. -/
theorem mul_eq_zero_of_range_mulVecLin_le_ker [Fintype τ] {y : Matrix P τ k} {A : Matrix σ P k}
    (h_le : LinearMap.range y.mulVecLin ≤ LinearMap.ker A.mulVecLin) : A * y = 0 := by
  classical
  ext i j
  have hcol : y *ᵥ Pi.single j 1 ∈ LinearMap.ker A.mulVecLin := h_le ⟨Pi.single j 1, rfl⟩
  have hzero : (A * y) *ᵥ Pi.single j 1 = 0 := by
    rw [← mulVec_mulVec]
    exact hcol
  simpa [mulVec_single] using congrFun hzero i

/-- Every subspace `L` of `P → k` is the column span of a left-invertible matrix `y` indexed by
`Fin (Module.finrank k L)`. -/
theorem exists_leftInv_range_mulVecLin_eq (L : Submodule k (P → k)) :
    ∃ y : Matrix P (Fin (Module.finrank k L)) k,
      (∃ l : Matrix (Fin (Module.finrank k L)) P k, l * y = 1) ∧
      LinearMap.range y.mulVecLin = L := by
  classical
  let b := Module.finBasis k L
  let f : (Fin (Module.finrank k L) → k) →ₗ[k] (P → k) :=
    L.subtype.comp b.equivFun.symm.toLinearMap
  let y : Matrix P (Fin (Module.finrank k L)) k := LinearMap.toMatrix' f
  have hf_eq : y.mulVecLin = f := Matrix.toLin'_toMatrix' f
  have hf_inj : Function.Injective f :=
    Subtype.val_injective.comp b.equivFun.symm.injective
  obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hf_inj)
  refine ⟨y, ⟨LinearMap.toMatrix' g, ?_⟩, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]
  · rw [hf_eq, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]

/-- The columns of `y` lie in `L ⊓ ker A` and, together with the columns of `x`, form a
left-invertible basis of `L`. -/
structure IsKernelExtension [Fintype σ] [DecidableEq σ] (A : Matrix σ P k) (x : Matrix P σ k)
    (L : Submodule k (P → k)) {s : ℕ} (y : Matrix P (Fin s) k) : Prop where
  /-- The horizontally concatenated matrix `[x | y]` has a left inverse. -/
  exists_leftInv :
    ∃ l : Matrix (σ ⊕ Fin s) P k, l * Matrix.of (fun i ↦ Sum.elim (x i) (y i)) = 1
  /-- The columns of `x` and `y` together span `L`. -/
  range_concat :
    LinearMap.range (Matrix.of (fun i ↦ Sum.elim (x i) (y i))).mulVecLin = L
  /-- The columns of `y` lie in `L`. -/
  range_le : LinearMap.range y.mulVecLin ≤ L
  /-- The columns of `y` lie in the kernel of `A`. -/
  mul_eq_zero : A * y = 0
  /-- Only the trivial linear combination of the columns of `y` lies in the column span of `x`. -/
  eq_zero_of_mulVec_mem : ∀ t : Fin s → k, y *ᵥ t ∈ LinearMap.range x.mulVecLin → t = 0

/-- If `A * x` is invertible and a subspace `L` contains the columns of `x`, then those columns
extend to a basis of `L` by a matrix `y` whose columns form a basis of `L ⊓ ker A`. -/
theorem exists_isKernelExtension [Fintype σ] [DecidableEq σ]
    {A : Matrix σ P k} {x : Matrix P σ k} (h_det : (A * x).det ≠ 0)
    {L : Submodule k (P → k)} (hL : LinearMap.range x.mulVecLin ≤ L) :
    ∃ s : ℕ, ∃ y : Matrix P (Fin s) k, IsKernelExtension A x L y := by
  obtain ⟨y, ⟨l, hl⟩, hy⟩ := exists_leftInv_range_mulVecLin_eq (L ⊓ LinearMap.ker A.mulVecLin)
  have hyL : LinearMap.range y.mulVecLin ≤ L := hy.le.trans inf_le_left
  have hAy : A * y = 0 := mul_eq_zero_of_range_mulVecLin_le_ker (hy.le.trans inf_le_right)
  let C : Matrix σ P k := (A * x)⁻¹ * A
  let D : Matrix (Fin _) P k := l - l * x * C
  have hCx : C * x = 1 := by simp [C, Matrix.mul_assoc, h_det]
  have hCy : C * y = 0 := by simp [C, Matrix.mul_assoc, hAy]
  have hDx : D * x = 0 := by simp [D, Matrix.sub_mul, Matrix.mul_assoc, hCx]
  have hDy : D * y = 1 := by simp [D, Matrix.sub_mul, Matrix.mul_assoc, hCy, hl]
  have h_left : Matrix.of (Sum.elim C D) * Matrix.of (fun i ↦ Sum.elim (x i) (y i)) = 1 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simpa [Matrix.mul_apply, Matrix.one_apply, Sum.elim] using congrFun (congrFun hCx i) j
    · simpa [Matrix.mul_apply, Matrix.one_apply, Sum.elim] using congrFun (congrFun hCy i) j
    · simpa [Matrix.mul_apply, Matrix.one_apply, Sum.elim] using congrFun (congrFun hDx i) j
    · simpa [Matrix.mul_apply, Matrix.one_apply, Sum.elim] using congrFun (congrFun hDy i) j
  refine ⟨_, y, ⟨⟨_, h_left⟩, le_antisymm ?_ fun v hv ↦ ?_, hyL, hAy, ?_⟩⟩
  · rintro _ ⟨c, rfl⟩
    have hmul : Matrix.of (fun i ↦ Sum.elim (x i) (y i)) *ᵥ c =
        x *ᵥ (c ∘ Sum.inl) + y *ᵥ (c ∘ Sum.inr) := by
      ext i; simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
    rw [mulVecLin_apply, hmul]
    exact add_mem (hL ⟨c ∘ Sum.inl, rfl⟩) (hyL ⟨c ∘ Sum.inr, rfl⟩)
  · have h_ker : A *ᵥ (v - x *ᵥ (C *ᵥ v)) = 0 := by
      rw [mulVec_sub, mulVec_mulVec, mulVec_mulVec]
      simp [C, ← Matrix.mul_assoc, h_det]
    obtain ⟨d, hd⟩ : v - x *ᵥ (C *ᵥ v) ∈ LinearMap.range y.mulVecLin :=
      hy.ge ⟨sub_mem hv (hL ⟨C *ᵥ v, rfl⟩), h_ker⟩
    refine ⟨Sum.elim (C *ᵥ v) d, ?_⟩
    ext i
    have hi := congrFun (add_eq_of_eq_sub' hd) i
    simpa only [mulVecLin_apply, Matrix.mulVec, dotProduct, of_apply, Fintype.sum_sum_type,
      Sum.elim_inl, Sum.elim_inr, Pi.add_apply] using hi
  · rintro t ⟨r, hr : x *ᵥ r = y *ᵥ t⟩
    calc t = D *ᵥ (y *ᵥ t) := by rw [mulVec_mulVec, hDy, one_mulVec]
      _ = 0 := by rw [← hr, mulVec_mulVec, hDx, zero_mulVec]

end KernelExtension

end TauCeti
