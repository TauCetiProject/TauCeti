/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Module
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import TauCeti.RingTheory.Valuation.SaturatedModule

import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Saturated lattices over a nonarchimedean field

Let `K` be a nontrivially normed field with an ultrametric norm, with valuation ring `𝒪[K]` (the
closed unit ball) and maximal ideal `𝓂[K]` (the open unit ball). This file relates the
`𝓂[K]`-saturation of `TauCeti.IsValuationSaturated` to the metric structure of `K`.

Bounded `𝒪[K]`-submodules of `ι → K` are transported along `𝒪[K]`-linear equivalences: every
`𝒪[K]`-linear map between such spaces is `K`-linear, hence continuous, so it carries bounded sets
to bounded sets. Saturation is transported by `TauCeti.isValuationSaturated_congr`.

If the norm of `K` is dense, for instance if its value group is all of `ℝ_{>0}`, the maximal
ideal `𝓂[K]` is not finitely generated, so `𝒪[K]` and every principal lattice `a • 𝒪[K]` in `K`
are `𝓂[K]`-saturated. For a discretely valued field such as `ℚ_p` this fails: `ℤ_p` is not
saturated with respect to its maximal ideal `p ℤ_p`.

## Main results

* `LinearMap.continuous_of_integer`: an `𝒪[K]`-linear map from `ι → K`, `ι` finite, to a normed
  `K`-space is continuous.
* `LinearEquiv.isBounded_image_iff_of_integer`: `𝒪[K]`-linear equivalences between finite
  products of `K` preserve and reflect bounded sets.
* `Valued.integer.mem_maximalIdeal_iff`: the maximal ideal of `𝒪[K]` is the open unit ball.
* `TauCeti.not_fg_maximalIdeal_integer`: for a densely normed field the maximal ideal of `𝒪[K]`
  is not finitely generated.
* `TauCeti.isValuationSaturated_integer`, `TauCeti.isValuationSaturated_integer_span_singleton`:
  for a densely normed field, `𝒪[K]` and every principal lattice `a • 𝒪[K]` in `K` are
  `𝓂[K]`-saturated.
* `TauCeti.not_isValuationSaturated_maximalIdeal_integer`: the open unit ball `𝓂[K]` is not
  `𝓂[K]`-saturated.

## References

* B. Bhatt and P. Scholze, *Projectivity of the Witt vector affine Grassmannian*,
  Invent. Math. 209 (2017), Lemma 6.14.
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

namespace TauCeti

/-- Over a nontrivially normed nonarchimedean field, the open unit ball `𝓂[K]` is not saturated
with respect to itself. -/
theorem not_isValuationSaturated_maximalIdeal_integer {K : Type*} [NontriviallyNormedField K]
    [IsUltrametricDist K] :
    ¬ IsValuationSaturated (Valued.integer K) (maximalIdeal (Valued.integer K))
      (maximalIdeal (Valued.integer K)) := by
  refine not_isValuationSaturated_self (fun h ↦ ?_) (maximalIdeal.isMaximal _).ne_top
  obtain ⟨x, hx0, hx1⟩ := Valued.integer.exists_norm_lt_one (K := K)
  have hx : x ∈ maximalIdeal (Valued.integer K) := Valued.integer.mem_maximalIdeal_iff.2 hx1
  rw [h, Ideal.mem_bot] at hx
  simp [hx] at hx0

section DenselyNormed

variable {K : Type*} [DenselyNormedField K] [IsUltrametricDist K]

/-- The maximal ideal of the valuation ring of a densely normed nonarchimedean field is not
finitely generated: a generator would bound the norms of all elements of the open unit ball. -/
theorem not_fg_maximalIdeal_integer : ¬ (maximalIdeal (Valued.integer K)).FG := by
  intro hfg
  obtain ⟨π, hπ⟩ := (IsBezout.isPrincipal_of_FG _ hfg).principal
  have hπm : π ∈ maximalIdeal (Valued.integer K) := hπ ▸ Submodule.mem_span_singleton_self π
  obtain ⟨x, hπx, hx1⟩ :=
    NormedField.exists_lt_norm_lt K (norm_nonneg π) (Valued.integer.mem_maximalIdeal_iff.1 hπm)
  let y : Valued.integer K := ⟨x, Valued.integer.mem_iff.2 hx1.le⟩
  have hy : y ∈ Submodule.span (Valued.integer K) {π} := hπ ▸
    Valued.integer.mem_maximalIdeal_iff.2 hx1
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hy
  have hnorm : ‖x‖ = ‖c‖ * ‖π‖ := by
    rw [← norm_mul]
    exact congrArg norm (congrArg Subtype.val hc).symm
  have := mul_le_of_le_one_left (norm_nonneg π) (Valued.integer.norm_le_one c)
  linarith

/-- Over a densely normed nonarchimedean field `K`, the valuation ring `𝒪[K]` is saturated with
respect to its maximal ideal. -/
theorem isValuationSaturated_integer :
    IsValuationSaturated (Valued.integer K) (maximalIdeal (Valued.integer K)) (Valued.integer K) :=
  isValuationSaturated_maximalIdeal_self not_fg_maximalIdeal_integer

/-- Over a densely normed nonarchimedean field `K`, every principal lattice `a • 𝒪[K]` in `K`,
including `a = 0`, is saturated with respect to the maximal ideal of `𝒪[K]`. -/
theorem isValuationSaturated_integer_span_singleton (a : K) :
    IsValuationSaturated (Valued.integer K) (maximalIdeal (Valued.integer K))
      (Valued.integer K ∙ a) :=
  isValuationSaturated_span_singleton not_fg_maximalIdeal_integer a

end DenselyNormed

/-- The ring `ℤ_[p]` of `p`-adic integers is not saturated with respect to its maximal ideal
`p ℤ_[p]`, since that ideal is finitely generated. -/
example (p : ℕ) [Fact p.Prime] :
    ¬ IsValuationSaturated ℤ_[p] (maximalIdeal ℤ_[p]) ℤ_[p] := fun h ↦
  isValuationSaturated_maximalIdeal_self_iff.1 h (IsNoetherian.noetherian _)

end TauCeti
