/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import TauCeti.Analysis.Normed.Lp.Reindex
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Countable Hilbert bases and reindexing

This file provides countability, reindexing, and `ℓ²(ℕ, 𝕜)`-identification results for orthonormal
families and Hilbert bases in separable inner product spaces:

* `Orthonormal.norm_sub_eq`, `Orthonormal.dist_eq`: distinct members of an orthonormal family sit at
  norm and metric distance `√2`.
* `Orthonormal.countable`, `HilbertBasis.countable`: in a separable inner product space, every
  orthonormal family—and in particular every Hilbert basis—has a countable index type.
* `HilbertBasis.reindex`: reindexes a Hilbert basis along any bijection of index types without
  requiring completeness of the ambient space.
* `HilbertBasis.finite_iff`: the index type of a Hilbert basis is finite if and only if the space is
  finite-dimensional.
* `TauCeti.nonempty_hilbertBasis_nat`, `TauCeti.nonempty_linearIsometryEquiv_lp_nat`: every
  infinite-dimensional separable complete inner product space admits a Hilbert basis indexed by `ℕ`
  and is linearly isometric to `ℓ²(ℕ, 𝕜)`.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer GTM 96, 1990, §I.4.
-/

public section

open scoped InnerProductSpace lp

section Orthonormal

variable {ι 𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {v : ι → E}

/-- Distinct members of an orthonormal family sit at norm distance `√2`. -/
theorem Orthonormal.norm_sub_eq (hv : Orthonormal 𝕜 v) {i j : ι} (hij : i ≠ j) :
    ‖v i - v j‖ = √2 := by
  have hsq : ‖v i - v j‖ ^ 2 = 2 := by
    rw [@norm_sub_sq 𝕜, hv.inner_eq_zero hij, hv.norm_eq_one, hv.norm_eq_one]
    simp; norm_num
  rw [← Real.sqrt_sq (norm_nonneg _), hsq]

/-- Distinct members of an orthonormal family sit at metric distance `√2`. -/
theorem Orthonormal.dist_eq (hv : Orthonormal 𝕜 v) {i j : ι} (hij : i ≠ j) :
    dist (v i) (v j) = √2 := by
  rw [dist_eq_norm, hv.norm_sub_eq hij]

/-- Every orthonormal family in a separable inner product space has a countable index type. -/
theorem Orthonormal.countable [TopologicalSpace.SeparableSpace E] (hv : Orthonormal 𝕜 v) :
    Countable ι := by
  have hdisj : Pairwise (Function.onFun Disjoint fun i ↦ Metric.ball (v i) (1 / 2 : ℝ)) :=
    fun i j hij ↦ Metric.ball_disjoint_ball <| by
      rw [hv.dist_eq hij]
      linarith [Real.one_lt_sqrt_two]
  exact hdisj.countable_of_isOpen_disjoint (fun _ ↦ Metric.isOpen_ball) fun i ↦
    ⟨v i, Metric.mem_ball_self (by positivity)⟩

end Orthonormal

namespace HilbertBasis

variable {ι κ μ 𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Every Hilbert basis of a separable inner product space has a countable index type. -/
protected theorem countable [TopologicalSpace.SeparableSpace E] (b : HilbertBasis ι 𝕜 E) :
    Countable ι :=
  b.orthonormal.countable

/-- Reindex a Hilbert basis along an equivalence `e : ι ≃ κ`, the infinite-dimensional counterpart
of `OrthonormalBasis.reindex`. Completeness of `E` is not needed. -/
protected noncomputable def reindex (b : HilbertBasis ι 𝕜 E) (e : ι ≃ κ) : HilbertBasis κ 𝕜 E :=
  ofRepr (b.repr.trans (LinearIsometryEquiv.lpCongrLeft 2 𝕜 𝕜 e))

@[simp]
theorem repr_reindex (b : HilbertBasis ι 𝕜 E) (e : ι ≃ κ) :
    (b.reindex e).repr = b.repr.trans (LinearIsometryEquiv.lpCongrLeft 2 𝕜 𝕜 e) :=
  (rfl)

@[simp]
theorem reindex_apply (b : HilbertBasis ι 𝕜 E) (e : ι ≃ κ) (k : κ) :
    b.reindex e k = b (e.symm k) := by
  classical
  simp only [← HilbertBasis.repr_symm_single, repr_reindex, LinearIsometryEquiv.symm_trans,
    LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.lpCongrLeft_symm,
    LinearIsometryEquiv.lpCongrLeft_single]

@[simp]
theorem coe_reindex (b : HilbertBasis ι 𝕜 E) (e : ι ≃ κ) :
    ⇑(b.reindex e) = b ∘ e.symm :=
  funext (b.reindex_apply e)

@[simp]
theorem reindex_refl (b : HilbertBasis ι 𝕜 E) :
    b.reindex (Equiv.refl ι) = b :=
  DFunLike.ext _ _ fun _ ↦ by simp

@[simp]
theorem reindex_trans (b : HilbertBasis ι 𝕜 E) (e : ι ≃ κ) (f : κ ≃ μ) :
    (b.reindex e).reindex f = b.reindex (e.trans f) :=
  DFunLike.ext _ _ fun _ ↦ by simp

theorem reindex_reindex_symm (b : HilbertBasis ι 𝕜 E) (e : ι ≃ κ) :
    (b.reindex e).reindex e.symm = b := by
  simp

theorem reindex_symm_reindex (b : HilbertBasis κ 𝕜 E) (e : ι ≃ κ) :
    (b.reindex e.symm).reindex e = b := by
  simp

/-- A Hilbert basis has a finite index type if and only if the space is finite-dimensional. -/
theorem finite_iff (b : HilbertBasis ι 𝕜 E) : Finite ι ↔ Module.Finite 𝕜 E := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ b.orthonormal.linearIndependent.finite⟩
  cases nonempty_fintype ι
  exact Module.Finite.of_basis b.toOrthonormalBasis.toBasis

end HilbertBasis

namespace TauCeti

variable (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] [TopologicalSpace.SeparableSpace E]

/-- Every infinite-dimensional separable complete inner product space admits a Hilbert basis indexed
by `ℕ`. -/
theorem nonempty_hilbertBasis_nat (hinf : ¬ Module.Finite 𝕜 E) :
    Nonempty (HilbertBasis ℕ 𝕜 E) := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 E
  have : Countable w := b.countable
  have : Infinite w := not_finite_iff_infinite.mp (b.finite_iff.not.mpr hinf)
  obtain ⟨_⟩ := nonempty_denumerable w
  exact ⟨b.reindex (Denumerable.eqv w)⟩

/-- Every infinite-dimensional separable complete inner product space is linearly isometric to
`ℓ²(ℕ, 𝕜)`. -/
theorem nonempty_linearIsometryEquiv_lp_nat (hinf : ¬ Module.Finite 𝕜 E) :
    Nonempty (E ≃ₗᵢ[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2) :=
  let ⟨b⟩ := nonempty_hilbertBasis_nat 𝕜 E hinf
  ⟨b.repr⟩

end TauCeti
