/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Half-spaces, epigraphs, and graphs in an ℓ² product

This file defines the open normal half-space and the open region above the graph of a continuous
function in `WithLp 2 (ℝ × E)`. These are the model domains used by graph flattening and Sobolev
trace theory. It also defines the normal graph parametrization `y ↦ (φ y, y)` and records its
elementary metric properties.

## Main declarations

* `TauCeti.normalHalfSpace`: the region above a constant normal coordinate.
* `TauCeti.normalEpigraph`: the region above the graph of a continuous function.
* `TauCeti.normalGraphEmbedding`: the normal graph parametrization `y ↦ (φ y, y)`.
* `LipschitzWith.normalGraphEmbedding`: a `K`-Lipschitz function has a `(K + 1)`-Lipschitz
  graph parametrization.
-/

public section

namespace TauCeti

open Set TopologicalSpace
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E]

/-- The open half-space to the right of the normal coordinate `a` in the ℓ² product `ℝ × E`. -/
def normalHalfSpace (a : ℝ) : Opens (WithLp 2 (ℝ × E)) :=
  ⟨{x | a < (WithLp.ofLp x).1},
    isOpen_lt continuous_const (WithLp.prod_continuous_ofLp 2 ℝ E).fst⟩

/-- Membership in the normal-coordinate half-space is a strict inequality. -/
@[simp]
theorem mem_normalHalfSpace (a : ℝ) (x : WithLp 2 (ℝ × E)) :
    x ∈ normalHalfSpace (E := E) a ↔ a < (WithLp.ofLp x).1 := Iff.rfl

/-- As a set, the right normal half-space is `{x | a < x.fst}`. -/
theorem coe_normalHalfSpace (a : ℝ) :
    (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) =
      {x | a < (WithLp.ofLp x).1} :=
  Set.ext (mem_normalHalfSpace a)

/-- The open region `{x | φ x.snd < x.fst}` above the graph of a continuous function
`φ : E → ℝ` in the ℓ² product `ℝ × E`. -/
def normalEpigraph (φ : C(E, ℝ)) : Opens (WithLp 2 (ℝ × E)) :=
  ⟨{x | φ x.snd < x.fst}, isOpen_lt (by fun_prop) (by fun_prop)⟩

/-- Membership in the region above the graph is a strict inequality. -/
@[simp]
theorem mem_normalEpigraph (φ : C(E, ℝ)) (x : WithLp 2 (ℝ × E)) :
    x ∈ normalEpigraph φ ↔ φ x.snd < x.fst :=
  Iff.rfl

/-- As a set, the region above the graph is `{x | φ x.snd < x.fst}`. -/
theorem coe_normalEpigraph (φ : C(E, ℝ)) :
    (normalEpigraph φ : Set (WithLp 2 (ℝ × E))) = {x | φ x.snd < x.fst} :=
  Set.ext (mem_normalEpigraph φ)

/-- The region above the graph of `0` is the half-space `{0 < t}`. -/
@[simp]
theorem normalEpigraph_zero : normalEpigraph (0 : C(E, ℝ)) = normalHalfSpace 0 := by
  ext x
  simp

/-- The normal graph parametrization `y ↦ (φ y, y)` in the Euclidean product `ℝ × E`. -/
def normalGraphEmbedding (φ : E → ℝ) (y : E) : WithLp 2 (ℝ × E) :=
  WithLp.toLp 2 (φ y, y)

omit [NormedAddCommGroup E] in
/-- The normal coordinate of the graph parametrization is the graphing function. -/
@[simp]
theorem normalGraphEmbedding_fst (φ : E → ℝ) (y : E) :
    (normalGraphEmbedding φ y).fst = φ y :=
  (rfl)

omit [NormedAddCommGroup E] in
/-- The tangential coordinate of the graph parametrization is its argument. -/
@[simp]
theorem normalGraphEmbedding_snd (φ : E → ℝ) (y : E) :
    (normalGraphEmbedding φ y).snd = y :=
  (rfl)

omit [NormedAddCommGroup E] in
/-- The normal graph parametrization is injective. -/
theorem injective_normalGraphEmbedding (φ : E → ℝ) :
    Function.Injective (normalGraphEmbedding φ) := fun _ _ h ↦ by
  simpa using congrArg WithLp.snd h

omit [NormedAddCommGroup E] in
/-- The range of the normal graph parametrization is the graph equation `t = φ y`. -/
theorem range_normalGraphEmbedding (φ : E → ℝ) :
    range (normalGraphEmbedding φ) = {x | x.fst = φ x.snd} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    simp
  · intro hx
    refine ⟨x.snd, (WithLp.ext_iff 2).2 ?_⟩
    exact Prod.ext hx.symm rfl

/-- The second projection is a `1`-Lipschitz inverse to the graph parametrization on its range. -/
theorem antilipschitzWith_normalGraphEmbedding (φ : E → ℝ) :
    AntilipschitzWith 1 (normalGraphEmbedding φ) := by
  refine AntilipschitzWith.of_le_mul_dist fun x y ↦ ?_
  simpa only [NNReal.coe_one, one_mul, normalGraphEmbedding_snd] using
    WithLp.dist_snd_le (normalGraphEmbedding φ x) (normalGraphEmbedding φ y)

/-- A `K`-Lipschitz function has a `(K + 1)`-Lipschitz normal graph parametrization. -/
theorem _root_.LipschitzWith.normalGraphEmbedding {K : ℝ≥0} {φ : E → ℝ}
    (hφ : LipschitzWith K φ) :
    LipschitzWith (K + 1) (TauCeti.normalGraphEmbedding φ) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  calc
    dist (TauCeti.normalGraphEmbedding φ x) (TauCeti.normalGraphEmbedding φ y) ≤
        dist (TauCeti.normalGraphEmbedding φ x) (WithLp.toLp 2 (φ y, x)) +
          dist (WithLp.toLp 2 (φ y, x)) (TauCeti.normalGraphEmbedding φ y) :=
      dist_triangle _ _ _
    _ = dist (φ x) (φ y) + dist x y := by
      simp [TauCeti.normalGraphEmbedding, WithLp.prod_dist_eq_of_L2]
    _ ≤ K * dist x y + dist x y := add_le_add (hφ.dist_le_mul x y) le_rfl
    _ = (K + 1) * dist x y := by ring

/-- A continuous normal graph is closed in the Euclidean product. -/
theorem _root_.Continuous.isClosed_range_normalGraphEmbedding {φ : E → ℝ} (hφ : Continuous φ) :
    IsClosed (range (TauCeti.normalGraphEmbedding φ)) := by
  rw [range_normalGraphEmbedding]
  exact isClosed_eq (WithLp.prod_continuous_ofLp 2 ℝ E).fst
    (hφ.comp (WithLp.prod_continuous_ofLp 2 ℝ E).snd)

end TauCeti

end
