/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Module
public import Mathlib.Topology.Algebra.Valued.LocallyCompact

import Mathlib.Analysis.Normed.Operator.NNNorm

/-!
# The valuation ring of a nonarchimedean normed field

Let `K` be a nontrivially normed field with an ultrametric norm, with valuation ring `𝒪[K]` (the
closed unit ball) and maximal ideal `𝓂[K]` (the open unit ball).

Every `𝒪[K]`-linear map between finite products of copies of `K` is `K`-linear, since `K` is the
fraction field of `𝒪[K]`; hence it is continuous and carries bounded sets to bounded sets. If the
norm of `K` is dense, for instance if its value group is all of `ℝ_{>0}`, the maximal ideal
`𝓂[K]` is not finitely generated.

## Main results

* `Valued.integer.mem_maximalIdeal_iff`: the maximal ideal of `𝒪[K]` is the open unit ball.
* `Valued.integer.smul_def`: on a `K`-module, `𝒪[K]` acts through the inclusion `𝒪[K] → K`.
* `Valued.integer.dvd_iff_norm_le`: divisibility in `𝒪[K]` is comparison of norms.
* `Valued.integer.submodule_mem_of_norm_le`: an `𝒪[K]`-submodule of `K` contains every element
  of norm at most that of one of its elements.
* `Valued.integer.exists_eq_mul_of_linearMap_maximalIdeal`: every `𝒪[K]`-linear map
  `𝓂[K] → K` is multiplication by an element of `K`.
* `Valued.integer.exists_seq_mem_maximalIdeal`: for a densely normed field, `𝓂[K]` contains a
  sequence of nonzero elements of increasing norm which is cofinal for the norm.
* `LinearMap.continuous_of_integer`: an `𝒪[K]`-linear map from `ι → K`, `ι` finite, to a normed
  `K`-space is continuous.
* `LinearEquiv.isBounded_image_iff_of_integer`: `𝒪[K]`-linear equivalences between finite
  products of `K` preserve and reflect bounded sets.
* `TauCeti.not_fg_maximalIdeal_integer`: for a densely normed field the maximal ideal of `𝒪[K]`
  is not finitely generated.
-/

public section

open IsLocalRing Bornology
open scoped NormedField

section Integer

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

/-- An element of the valuation ring of a nonarchimedean field lies in its maximal ideal exactly
when its norm is less than `1`. -/
theorem Valued.integer.mem_maximalIdeal_iff {x : Valued.integer K} :
    x ∈ IsLocalRing.maximalIdeal (Valued.integer K) ↔ ‖x‖ < 1 := by
  rw [mem_maximalIdeal, mem_nonunits_iff, Valued.integer.isUnit_iff_norm_eq_one,
    (Valued.integer.norm_le_one x).lt_iff_ne]

/-- On a `K`-module `E` with a compatible `𝒪[K]`-module structure, `𝒪[K]` acts through the
inclusion `𝒪[K] → K`. -/
theorem Valued.integer.smul_def {E : Type*} [AddCommMonoid E] [Module K E]
    [Module (Valued.integer K) E] [IsScalarTower (Valued.integer K) K E] (c : Valued.integer K)
    (v : E) : c • v = (c : K) • v :=
  (algebraMap_smul K c v).symm

/-- In the valuation ring of a nonarchimedean field, `b` divides `a` exactly when
`‖a‖ ≤ ‖b‖`. -/
theorem Valued.integer.dvd_iff_norm_le {a b : Valued.integer K} :
    b ∣ a ↔ ‖(a : K)‖ ≤ ‖(b : K)‖ := by
  rw [(Valuation.integer.integers _).dvd_iff_le]
  simp [NormedField.v_eq_valuation, Algebra.algebraMap_ofSubsemiring_apply, ← NNReal.coe_le_coe]

/-- An `𝒪[K]`-submodule of `K` containing `y` contains every `x` with `‖x‖ ≤ ‖y‖`. -/
theorem Valued.integer.submodule_mem_of_norm_le {M : Submodule (Valued.integer K) K} {x y : K}
    (hy : y ∈ M) (h : ‖x‖ ≤ ‖y‖) : x ∈ M :=
  Valuation.leSubmodule_v_le_of_mem NormedField.valuation hy (NNReal.coe_le_coe.1 h)

/-- Every `𝒪[K]`-linear map from the maximal ideal `𝓂[K]` to `K` is multiplication by an element
of `K`. -/
theorem Valued.integer.exists_eq_mul_of_linearMap_maximalIdeal
    (f : IsLocalRing.maximalIdeal (Valued.integer K) →ₗ[Valued.integer K] K) :
    ∃ q : K, ∀ c : IsLocalRing.maximalIdeal (Valued.integer K),
      f c = ((c : Valued.integer K) : K) * q := by
  obtain ⟨a, ha0, ha1⟩ := Valued.integer.exists_norm_coe_lt_one (K := K)
  have ham : a ∈ IsLocalRing.maximalIdeal (Valued.integer K) :=
    Valued.integer.mem_maximalIdeal_iff.2 ha1
  refine ⟨f ⟨a, ham⟩ / a, fun c ↦ ?_⟩
  -- `f` is linear, so `a * f c = f (a * c) = c * f a`.
  have h : (a : K) * f c = (c : K) * f ⟨a, ham⟩ := by
    have hac : a • c = (c : Valued.integer K) • (⟨a, ham⟩ : IsLocalRing.maximalIdeal _) :=
      Subtype.ext (mul_comm _ _)
    simpa only [map_smul, Valued.integer.smul_def, smul_eq_mul] using congrArg f hac
  field_simp [norm_pos_iff.1 ha0]
  linear_combination h

variable {ι F : Type*} [NormedAddCommGroup F] [NormedSpace K F] [Module (Valued.integer K) F]
  [IsScalarTower (Valued.integer K) K F]

/-- An `𝒪[K]`-linear map from a finite product of copies of `K` to a normed `K`-space is
continuous: it is `K`-linear, since `K` is the fraction field of `𝒪[K]`. -/
theorem LinearMap.continuous_of_integer [Finite ι] (f : (ι → K) →ₗ[Valued.integer K] F) :
    Continuous f :=
  (f.extendScalarsOfIsLocalization (nonZeroDivisors (Valued.integer K)) K).continuous_on_pi

/-- An `𝒪[K]`-linear map from a finite product of copies of `K` to a normed `K`-space carries
bounded sets to bounded sets. -/
theorem LinearMap.isBounded_image_of_integer [Finite ι] (f : (ι → K) →ₗ[Valued.integer K] F)
    {s : Set (ι → K)} (hs : IsBounded s) : IsBounded (f '' s) := by
  cases nonempty_fintype ι
  let g : (ι → K) →L[K] F :=
    ⟨f.extendScalarsOfIsLocalization (nonZeroDivisors (Valued.integer K)) K,
      f.continuous_of_integer⟩
  have hg : (g : (ι → K) → F) = f := by
    simp only [g]
    exact funext (LinearMap.extendScalarsOfIsLocalization_apply' (nonZeroDivisors _) K f)
  exact hg ▸ g.lipschitzWith.isBounded_image hs

/-- An `𝒪[K]`-linear equivalence between finite products of copies of `K` preserves and reflects
bounded sets. In particular a submodule `M` is bounded exactly when `M.map e` is. -/
theorem LinearEquiv.isBounded_image_iff_of_integer [Finite ι] {ι' : Type*} [Finite ι']
    (e : (ι → K) ≃ₗ[Valued.integer K] (ι' → K)) {s : Set (ι → K)} :
    IsBounded (e '' s) ↔ IsBounded s := by
  cases nonempty_fintype ι
  cases nonempty_fintype ι'
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa [Set.image_image] using e.symm.toLinearMap.isBounded_image_of_integer (F := ι → K) h
  · simpa using e.toLinearMap.isBounded_image_of_integer (F := ι' → K) h

end Integer

section DenselyNormed

variable {K : Type*} [DenselyNormedField K] [IsUltrametricDist K]

/-- Over a densely normed field, the maximal ideal of `𝒪[K]` contains a sequence of nonzero
elements of increasing norm which is cofinal for the norm. -/
theorem Valued.integer.exists_seq_mem_maximalIdeal :
    ∃ a : ℕ → Valued.integer K, (∀ n, (a n : K) ≠ 0) ∧
      (∀ n, a n ∈ IsLocalRing.maximalIdeal (Valued.integer K)) ∧ Monotone (fun n ↦ ‖(a n : K)‖) ∧
      ∀ b ∈ IsLocalRing.maximalIdeal (Valued.integer K), ∃ n, ‖(b : K)‖ ≤ ‖(a n : K)‖ := by
  set S := (fun x : K ↦ ‖x‖) '' {x | 0 < ‖x‖ ∧ ‖x‖ < 1}
  obtain ⟨x₀, hx₀⟩ := NormedField.exists_lt_norm_lt K le_rfl zero_lt_one
  have hS1 : ∀ y ∈ S, y ≤ 1 := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx.2.le
  have hne : S.Nonempty := ⟨_, x₀, hx₀, rfl⟩
  have hsup : sSup S = 1 := by
    refine csSup_eq_of_forall_le_of_forall_lt_exists_gt hne hS1 fun w hw ↦ ?_
    obtain ⟨x, hx1, hx2⟩ :=
      NormedField.exists_lt_norm_lt K (le_max_right w 0) (max_lt hw zero_lt_one)
    exact ⟨‖x‖, ⟨x, ⟨(le_max_right w 0).trans_lt hx1, hx2⟩, rfl⟩, (le_max_left w 0).trans_lt hx1⟩
  obtain ⟨u, hu, hlim, huS⟩ := exists_seq_tendsto_sSup hne ⟨1, hS1⟩
  choose x hx hxu using huS
  simp only at hxu
  refine ⟨fun n ↦ ⟨x n, Valued.integer.mem_iff.2 (hx n).2.le⟩, fun n ↦ norm_pos_iff.1 (hx n).1,
    fun n ↦ Valued.integer.mem_maximalIdeal_iff.2 (hx n).2, fun m n hmn ↦ ?_, fun b hb ↦ ?_⟩
  · simpa [hxu] using hu hmn
  · rw [hsup] at hlim
    obtain ⟨n, hn⟩ :=
      ((tendsto_order.1 hlim).1 _ (Valued.integer.mem_maximalIdeal_iff.1 hb)).exists
    exact ⟨n, hn.le.trans_eq (hxu n).symm⟩

end DenselyNormed

namespace TauCeti

variable {K : Type*} [DenselyNormedField K] [IsUltrametricDist K]

/-- The maximal ideal of the valuation ring of a densely normed nonarchimedean field is not
finitely generated: a generator would bound the norms of all elements of the open unit ball. -/
theorem not_fg_maximalIdeal_integer : ¬ (maximalIdeal (Valued.integer K)).FG := by
  intro hfg
  obtain ⟨π, hπ⟩ := (IsBezout.isPrincipal_of_FG _ hfg).principal
  have hπm : π ∈ maximalIdeal (Valued.integer K) := hπ ▸ Submodule.mem_span_singleton_self π
  obtain ⟨x, hπx, hx1⟩ :=
    NormedField.exists_lt_norm_lt K (norm_nonneg π) (Valued.integer.mem_maximalIdeal_iff.1 hπm)
  -- The element `y = x` of `𝒪[K]` lies in the open unit ball, but not in the closed ball of
  -- radius `‖π‖` that `Ideal.span {π}` is.
  let y : Valued.integer K := ⟨x, Valued.integer.mem_iff.2 hx1.le⟩
  have hy : ‖y‖ = ‖x‖ := AddSubgroupClass.coe_norm (Valued.integer K) y
  have hym : y ∈ Submodule.span (Valued.integer K) {π} :=
    hπ ▸ Valued.integer.mem_maximalIdeal_iff.2 (hy ▸ hx1)
  have hyπ : y ∈ Metric.closedBall 0 ‖π‖ :=
    Valued.integer.coe_span_singleton_eq_closedBall π ▸ SetLike.mem_coe.2 hym
  rw [mem_closedBall_zero_iff, hy] at hyπ
  exact hyπ.not_gt hπx

end TauCeti
