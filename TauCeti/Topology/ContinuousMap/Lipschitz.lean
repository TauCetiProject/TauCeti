/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import TauCeti.Analysis.Normed.Operator.Holder
public import TauCeti.Topology.MetricSpace.Holder

/-!
# The Lipschitz seminorm on continuous functions

On a metric space `X`, the Lipschitz seminorm of a function `f` is Mathlib's Hölder seminorm
`eHolderNorm 1 f` in `ℝ≥0∞`: it is the least Lipschitz constant of `f`
(`eHolderNorm_one_le_coe_iff`), the supremum of the difference quotients `d(f x, f y) / d(x, y)`
(`eHolderNorm_eq_iSup`), and `∞` exactly when `f` is not Lipschitz. By Kantorovich–Rubinstein
duality, the distance it induces between probability measures on a compact metric space is the
`1`-Wasserstein distance.

This file proves the properties of this seminorm that concern the metric of `X` and the space of
continuous functions on it.

* It recovers the metric: the distance between two points is the supremum of `d(f x, f y)` over
  the bounded continuous real functions `f` with Lipschitz seminorm at most `1`, attained by
  `z ↦ min (d(z, x)) (d(x, y))`. The witnesses are bounded, which matters on a noncompact space,
  where continuous functions need not be.
* On a compact metric space its finite domain, the Lipschitz functions, is a star subalgebra of
  `C(X, 𝕜)` for `RCLike 𝕜`. It separates points, so it is dense by the Stone–Weierstrass theorem.

The algebraic laws of the seminorm are Mathlib's `eHolderNorm_add_le`, `eHolderNorm_smul` and
`eHolderNorm_eq_zero`, together with the star invariance `eHolderNorm_star` and the Leibniz
estimate `eHolderNorm_mul_le`; its lower semicontinuity is `lowerSemicontinuous_eHolderNorm`.

## Main declarations

* `TauCeti.edist_eq_iSup_eHolderNorm_one_le_one`: the distance formula.
* `TauCeti.lipschitzStarSubalgebra 𝕜 X`: the Lipschitz functions in `C(X, 𝕜)`.
* `TauCeti.dense_lipschitzStarSubalgebra`: the Lipschitz functions are dense in `C(X, 𝕜)`.

## References

* M. A. Rieffel, *Metrics on state spaces*, Doc. Math. 4 (1999), 559–600, §8.
* N. Weaver, *Lipschitz algebras*, World Scientific, 1999.
-/

public section

noncomputable section

open Set
open scoped BoundedContinuousFunction ENNReal NNReal

namespace TauCeti

variable {𝕜 X : Type*}

section DistanceFormula

/-- For two points `x` and `y` of a pseudometric space, the bounded continuous real function
`z ↦ min (d(z, x)) (d(x, y))` is `1`-Lipschitz, vanishes at `x` and takes the value `d(x, y)` at
`y`. -/
theorem exists_boundedContinuousFunction_lipschitzWith_one_eq_dist [PseudoMetricSpace X] (x y : X) :
    ∃ f : X →ᵇ ℝ, LipschitzWith 1 f ∧ f x = 0 ∧ f y = dist x y := by
  refine ⟨BoundedContinuousFunction.ofNormedAddCommGroup (fun z ↦ min (dist z x) (dist x y))
    (by fun_prop) (dist x y) fun z ↦ ?_, ?_, by simp, by simp [dist_comm y x]⟩
  · rw [Real.norm_of_nonneg (le_min dist_nonneg dist_nonneg)]
    exact min_le_right _ _
  · simpa using (LipschitzWith.dist_left x).min (LipschitzWith.const (α := X) (dist x y))

/-- **The distance formula.** The extended distance between two points of a metric space is the
supremum of `edist (f x) (f y)` over the bounded continuous real functions `f` with Lipschitz
seminorm `eHolderNorm 1 f ≤ 1`. The supremum is attained, by the function of
`exists_boundedContinuousFunction_lipschitzWith_one_eq_dist`. -/
theorem edist_eq_iSup_eHolderNorm_one_le_one [MetricSpace X] (x y : X) :
    edist x y = ⨆ (f : X →ᵇ ℝ) (_ : eHolderNorm 1 ⇑f ≤ 1), edist (f x) (f y) := by
  refine le_antisymm ?_ (iSup₂_le fun f hf ↦ ?_)
  · obtain ⟨f, hf, hfx, hfy⟩ := exists_boundedContinuousFunction_lipschitzWith_one_eq_dist x y
    refine le_iSup₂_of_le (f := fun (f : X →ᵇ ℝ) (_ : eHolderNorm 1 ⇑f ≤ 1) ↦
      edist (f x) (f y)) f (by simpa using eHolderNorm_one_le_coe_iff.2 hf) (le_of_eq ?_)
    rw [edist_dist, edist_dist, hfx, hfy, Real.dist_eq, zero_sub, abs_neg,
      abs_of_nonneg dist_nonneg]
  · have hf' : LipschitzWith 1 f := eHolderNorm_one_le_coe_iff.1 (by simpa using hf)
    simpa using hf'.edist_le_mul x y

end DistanceFormula

section LipschitzStarSubalgebra

variable (𝕜 X)
variable [RCLike 𝕜] [MetricSpace X] [CompactSpace X]

/-- The Lipschitz functions in `C(X, 𝕜)` on a compact metric space, as a star subalgebra. It is
the finite domain of the Lipschitz seminorm `eHolderNorm 1`
(`mem_lipschitzStarSubalgebra_iff_eHolderNorm_ne_top`). Compactness makes the functions bounded,
so that products of Lipschitz functions are Lipschitz. -/
def lipschitzStarSubalgebra : StarSubalgebra 𝕜 C(X, 𝕜) where
  carrier := {f | ∃ K, LipschitzWith K f}
  mul_mem' := by
    rintro f g ⟨K, hK⟩ ⟨L, hL⟩
    -- The Leibniz bound for the multiplication map, with the uniform norms as bounds.
    have h := (ContinuousLinearMap.mul 𝕜 𝕜).holderWith_comp₂ (holderWith_one.2 hK)
      (holderWith_one.2 hL) (Mf := ‖f‖₊) (Mg := ‖g‖₊) (fun x ↦ by simpa using f.norm_coe_le_norm x)
      (fun x ↦ by simpa using g.norm_coe_le_norm x)
    have hfg : (fun x ↦ ContinuousLinearMap.mul 𝕜 𝕜 (f x) (g x)) = ⇑(f * g) := by
      ext x
      simp
    rw [hfg] at h
    exact ⟨_, holderWith_one.1 h⟩
  add_mem' := by
    rintro f g ⟨K, hK⟩ ⟨L, hL⟩
    exact ⟨K + L, by simpa [Pi.add_def] using hK.add hL⟩
  algebraMap_mem' c := ⟨0, by simp⟩
  star_mem' := by
    rintro f ⟨K, hK⟩
    exact ⟨K, by simpa [Pi.star_def, Function.comp_def] using star_isometry.lipschitzWith.comp hK⟩

variable {𝕜 X}

/-- A continuous function belongs to the Lipschitz star subalgebra exactly when it is Lipschitz. -/
@[simp]
theorem mem_lipschitzStarSubalgebra {f : C(X, 𝕜)} :
    f ∈ lipschitzStarSubalgebra 𝕜 X ↔ ∃ K, LipschitzWith K f :=
  Iff.rfl

/-- The Lipschitz star subalgebra is the finite domain of the Lipschitz seminorm. -/
theorem mem_lipschitzStarSubalgebra_iff_eHolderNorm_ne_top {f : C(X, 𝕜)} :
    f ∈ lipschitzStarSubalgebra 𝕜 X ↔ eHolderNorm 1 ⇑f ≠ ∞ := by
  simp [MemHolder, holderWith_one]

variable (𝕜 X)

/-- The Lipschitz functions separate the points of a compact metric space: `z ↦ d(z, x)` vanishes
at `x` and nowhere else. -/
theorem lipschitzStarSubalgebra_separatesPoints :
    (lipschitzStarSubalgebra 𝕜 X).SeparatesPoints := by
  intro x y hxy
  refine ⟨_, ⟨⟨fun z ↦ (dist z x : 𝕜), by fun_prop⟩, ⟨1, ?_⟩, rfl⟩, ?_⟩
  · simpa [Function.comp_def] using RCLike.lipschitzWith_ofReal.comp (LipschitzWith.dist_left x)
  · simpa [eq_comm (a := (0 : 𝕜)), dist_eq_zero] using hxy.symm

/-- **The Lipschitz functions are dense** in the continuous functions on a compact metric space,
by the Stone–Weierstrass theorem. -/
theorem lipschitzStarSubalgebra_topologicalClosure :
    (lipschitzStarSubalgebra 𝕜 X).topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
    (lipschitzStarSubalgebra_separatesPoints 𝕜 X)

/-- **The Lipschitz functions are dense** in the continuous functions on a compact metric space:
the finite domain of the Lipschitz seminorm is dense. -/
theorem dense_lipschitzStarSubalgebra : Dense (lipschitzStarSubalgebra 𝕜 X : Set C(X, 𝕜)) := by
  rw [dense_iff_closure_eq, ← StarSubalgebra.topologicalClosure_coe,
    lipschitzStarSubalgebra_topologicalClosure, StarSubalgebra.coe_top]

end LipschitzStarSubalgebra

end TauCeti
