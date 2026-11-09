/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
public import TauCeti.Analysis.CStarAlgebra.ProjectionDilation
public import TauCeti.Analysis.InnerProductSpace.PartialIsometry

/-!
# Weak operator limits of projections

On a complete inner product space `E`, order intervals `Set.Icc a b` of bounded operators, for
the Loewner order, are closed in the weak operator topology. On an infinite-dimensional complex
Hilbert space `H` the weak operator closure of the orthogonal projections is exactly the set of
positive contractions `0 ≤ a ≤ 1`.

Projections are positive contractions, and positive contractions form a weak operator closed
set. Conversely, fix a positive contraction `a` and a finite-dimensional subspace `K`. When the
orthogonal complement `Kᗮ` contains a copy of `K`, there is a projection `p` with
`P_K p P_K = P_K a P_K`, where `P_K` is the orthogonal projection onto `K`. Here `p` is the
projection dilation of `P_K a P_K` along a partial isometry from `K` onto an orthogonal copy;
see `IsStarProjection.exists_isStarProjection_mul_mul_eq`. Thus `p` has the same matrix
coefficients `⟪y, p x⟫` as `a` for `x, y ∈ K`. Indexing these projections by finite sets of
vectors gives a net converging to `a` in the weak operator topology. No separability is needed.

The dimension hypothesis cannot be dropped: on `ℂ` the projections are `0` and `1`, while `1/2`
is a positive contraction.

## Main statements

* `Submodule.exists_isStarProjection_starProjection_mul_mul_eq`: if `Kᗮ` is at least as large
  as the finite-dimensional subspace `K`, every positive contraction has the same compression to
  `K` as some projection. The partial isometry it uses comes from
  `Submodule.exists_star_mul_self_eq_starProjection_and_starProjection_mul_eq_zero`.
* `ContinuousLinearMapWOT.isClosed_setOf_isPositive`: the positive operators form a weak
  operator closed set.
* `ContinuousLinearMapWOT.isClosed_image_ofCLM_Icc`: order intervals are weak operator closed.
* `ContinuousLinearMapWOT.closure_isStarProjection_eq_positive_contractions`: on an
  infinite-dimensional complex Hilbert space, the weak operator closure of the projections is the
  set of positive contractions.

## References

* V. F. R. Jones, *Von Neumann Algebras*, lecture notes, Chapter 3, p. 13.
-/

public section

open Filter Module
open scoped ComplexOrder InnerProductSpace Topology

namespace Submodule

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- If the orthogonal complement of a finite-dimensional subspace `K` has dimension at least
`finrank ℂ K`, every positive contraction `a` has the same compression to `K` as some orthogonal
projection `p`: `P_K p P_K = P_K a P_K`. In particular `⟪y, p x⟫ = ⟪y, a x⟫` for `x, y ∈ K`. -/
theorem exists_isStarProjection_starProjection_mul_mul_eq (K : Submodule ℂ H)
    [FiniteDimensional ℂ K] (hK : (finrank ℂ K : Cardinal) ≤ Module.rank ℂ Kᗮ)
    {a : H →L[ℂ] H} (ha : a ∈ Set.Icc 0 1) :
    ∃ p : H →L[ℂ] H, IsStarProjection p ∧
      K.starProjection * p * K.starProjection = K.starProjection * a * K.starProjection := by
  obtain ⟨u, hu, hKu⟩ := K.exists_star_mul_self_eq_starProjection_and_starProjection_mul_eq_zero hK
  exact isStarProjection_starProjection.exists_isStarProjection_mul_mul_eq hu hKu ha

end Submodule

namespace ContinuousLinearMapWOT

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- The positive operators, cut out by closed conditions on matrix coefficients, form a weak
operator closed set. -/
theorem isClosed_setOf_isPositive : IsClosed {T : E →WOT[𝕜] E | (toCLM T).IsPositive} := by
  have hl : ∀ x y, Continuous fun T : E →WOT[𝕜] E => ⟪x, T y⟫_𝕜 :=
    fun x y => continuous_inner_apply continuous_id y x
  have hr : ∀ x y, Continuous fun T : E →WOT[𝕜] E => ⟪T x, y⟫_𝕜 := fun x y => by
    exact (RCLike.continuous_conj.comp (hl y x)).congr fun T => inner_conj_symm _ _
  have h : {T : E →WOT[𝕜] E | (toCLM T).IsPositive} =
      (⋂ x, ⋂ y, {T | ⟪T x, y⟫_𝕜 = ⟪x, T y⟫_𝕜}) ∩ ⋂ x, {T | 0 ≤ ⟪T x, x⟫_𝕜} := by
    ext T
    simp [ContinuousLinearMap.isPositive_iff, LinearMap.IsSymmetric]
  rw [h]
  exact (isClosed_iInter fun x => isClosed_iInter fun y => isClosed_eq (hr x y) (hl x y)).inter
    (isClosed_iInter fun x => isClosed_le continuous_const (hr x x))

/-- The set of operators above `a` in the Loewner order is weak operator closed. -/
theorem isClosed_image_ofCLM_Ici {a : E →L[𝕜] E} :
    IsClosed (ofCLM '' Set.Ici a) := by
  convert isClosed_setOf_isPositive.preimage (continuous_sub_right (ofCLM a)) using 1
  ext T
  obtain ⟨T, rfl⟩ := ofCLM_surjective T
  simp [ofCLM_injective.mem_set_image, ContinuousLinearMap.le_def]

/-- The set of operators below `b` in the Loewner order is weak operator closed. -/
theorem isClosed_image_ofCLM_Iic {b : E →L[𝕜] E} :
    IsClosed (ofCLM '' Set.Iic b) := by
  convert isClosed_image_ofCLM_Ici (a := -b).preimage continuous_neg using 1
  ext T
  obtain ⟨T, rfl⟩ := ofCLM_surjective T
  simp [ofCLM_injective.mem_set_image, ← ofCLM_neg]

/-- Order intervals of operators, for the Loewner order, are weak operator closed. -/
theorem isClosed_image_ofCLM_Icc {a b : E →L[𝕜] E} :
    IsClosed (ofCLM '' Set.Icc a b) := by
  rw [← Set.Ici_inter_Iic, Set.image_inter ofCLM_injective]
  exact isClosed_image_ofCLM_Ici.inter isClosed_image_ofCLM_Iic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Weak limits of projections.** On an infinite-dimensional complex Hilbert space, the weak
operator closure of the orthogonal projections is the set of positive contractions
`0 ≤ a ≤ 1`. -/
theorem closure_isStarProjection_eq_positive_contractions (hH : ¬ FiniteDimensional ℂ H) :
    closure (ofCLM '' {p : H →L[ℂ] H | IsStarProjection p}) = ofCLM '' Set.Icc 0 1 := by
  refine subset_antisymm
    (closure_minimal (Set.image_mono fun p hp => hp.mem_Icc) isClosed_image_ofCLM_Icc) ?_
  rintro _ ⟨a, ha, rfl⟩
  classical
  -- For every finite set `s` of vectors, some projection has the matrix coefficients of `a`
  -- on `span ℂ s`.
  have key : ∀ s : Finset H, ∃ p : H →L[ℂ] H, IsStarProjection p ∧
      ∀ x ∈ s, ∀ y ∈ s, ⟪y, p x⟫_ℂ = ⟪y, a x⟫_ℂ := by
    intro s
    let K := Submodule.span ℂ (s : Set H)
    have hK : (finrank ℂ K : Cardinal) ≤ Module.rank ℂ Kᗮ := by
      have hinf : ¬ FiniteDimensional ℂ Kᗮ := fun h =>
        hH (Module.Finite.equiv (Submodule.prodEquivOfIsCompl K Kᗮ K.isCompl_orthogonal))
      exact (Cardinal.natCast_lt_aleph0).le.trans
        (not_lt.mp (mt Module.rank_lt_aleph0_iff.mp hinf))
    obtain ⟨p, hp, hpa⟩ := K.exists_isStarProjection_starProjection_mul_mul_eq hK ha
    refine ⟨p, hp, fun x hx y hy => ?_⟩
    have hxK : K.starProjection x = x :=
      Submodule.starProjection_eq_self_iff.mpr (Submodule.subset_span hx)
    have hyK : K.starProjection y = y :=
      Submodule.starProjection_eq_self_iff.mpr (Submodule.subset_span hy)
    have h := congrArg (fun T : H →L[ℂ] H => ⟪y, T x⟫_ℂ) hpa
    simpa only [mul_apply_eq_comp, hxK, ← K.inner_starProjection_left_eq_right,
      hyK] using h
  choose p hp hpa using key
  refine mem_closure_of_tendsto (f := fun s => ofCLM (p s)) (b := atTop) ?_
    (Eventually.of_forall fun s => ⟨p s, hp s, rfl⟩)
  rw [tendsto_iff_forall_inner_apply_tendsto]
  intro x y
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop {x, y}] with s hs
  exact (hpa s x (hs (by simp)) y (hs (by simp))).symm

end ContinuousLinearMapWOT
