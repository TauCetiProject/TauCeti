/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Chart.Basic
public import TauCeti.Geometry.Manifold.Morse.Index
import Mathlib.LinearAlgebra.Dimension.Constructions
import TauCeti.Analysis.Calculus.Morse.Pi
import TauCeti.Geometry.Manifold.Morse.Hessian
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The stable subspace and the index of a Morse–Bott chart

In a Morse–Bott chart `φ` for `f` at `x` (`TauCeti.MorseBottChart`), `f` is the diagonal quadratic
form `f x + (1/2) Σᵢ wᵢ zᵢ²` in the coordinates `z`, with weights `wᵢ ∈ {-1, 0, 1}`. The negative
gradient flow of this normal form, `z ↦ (e^{-wᵢ t} zᵢ)ᵢ`, converges as `t → ∞` exactly from the
points whose coordinates of negative weight vanish. These points form the **stable subspace** of
the chart (`TauCeti.MorseBottChart.stableSubspace`), the model of the stable manifold of the
critical set near `x`: it contains the coordinates of weight `0`, along the critical set, and those
of weight `1`, the positive normal directions.

The number of coordinates of negative weight is the Morse index of `f` at the centre of the chart
(`TauCeti.MorseBottChart.manifoldMorseIndex_eq_ncard_weight_neg`): the Hessian of the normal form is
the diagonal form `Σᵢ wᵢ zᵢ²`, whose negative index is the number of negative weights. So the
stable subspace has dimension `n - λ`, where `λ` is the Morse index at the centre
(`TauCeti.MorseBottChart.finrank_stableSubspace_add_manifoldMorseIndex`). For the chart of `-f`
with the opposite weights (`TauCeti.MorseBottChart.neg`), the stable subspace is the unstable
subspace of `φ`, of dimension `n` minus the Morse index of `-f`, that is `λ` plus the dimension of
the critical set.

A Morse chart (`TauCeti.MorseChart`) is a Morse–Bott chart with no weight `0`, so the
statements here apply to Morse charts as well.

## Main declarations

* `TauCeti.MorseBottChart.negativeCoord`: the coordinates of negative weight, as a linear map.
* `TauCeti.MorseBottChart.stableSubspace`: the vectors whose coordinates of negative weight
  vanish.
* `TauCeti.MorseBottChart.finrank_stableSubspace_add_ncard_weight_neg`: the stable subspace has
  codimension the number of negative weights.
* `TauCeti.MorseBottChart.manifoldMorseIndex_eq_ncard_weight_neg`: the Morse index at the centre is
  the number of negative weights.
* `TauCeti.MorseBottChart.finrank_stableSubspace_add_manifoldMorseIndex`: the stable subspace has
  dimension `n - λ`.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, Section 6.2 (Morse–Bott functions and their gradient flows).
-/

public section

open Function Set Filter Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {x : M}

namespace MorseBottChart

variable (φ : MorseBottChart E f x)

/-- The coordinates of negative weight of a Morse–Bott chart, as a linear map. -/
noncomputable def negativeCoord : E →ₗ[ℝ] ({i // φ.weight i < 0} → ℝ) :=
  LinearMap.funLeft ℝ ℝ (Subtype.val : {i // φ.weight i < 0} → Fin (Module.finrank ℝ E)) ∘ₗ
    (φ.coord : E →ₗ[ℝ] (Fin (Module.finrank ℝ E) → ℝ))

/-- The coordinates of negative weight of a vector. -/
@[simp]
theorem negativeCoord_apply (v : E) (i : {i // φ.weight i < 0}) :
    φ.negativeCoord v i = φ.coord v i := by
  simp [negativeCoord, LinearMap.funLeft_apply]

/-- The coordinates of negative weight of a Morse–Bott chart can take any value. -/
theorem surjective_negativeCoord : Surjective φ.negativeCoord :=
  (LinearMap.funLeft_surjective_of_injective ℝ ℝ _ Subtype.val_injective).comp φ.coord.surjective

/-- The **stable subspace** of a Morse–Bott chart: the vectors whose coordinates of negative weight
vanish. -/
noncomputable def stableSubspace : Submodule ℝ E :=
  LinearMap.ker φ.negativeCoord

/-- A vector lies in the stable subspace when its coordinates of negative weight vanish. -/
@[simp]
theorem mem_stableSubspace {v : E} :
    v ∈ φ.stableSubspace ↔ ∀ i, φ.weight i < 0 → φ.coord v i = 0 := by
  rw [stableSubspace, LinearMap.mem_ker, negativeCoord, funext_iff]
  simp [LinearMap.funLeft_apply]

/-- A vector lies in the stable subspace exactly when its coordinates of negative weight vanish. -/
theorem mem_stableSubspace_iff_negativeCoord_eq_zero {v : E} :
    v ∈ φ.stableSubspace ↔ φ.negativeCoord v = 0 := by
  simp [funext_iff]

/-- The stable subspace has codimension the number of coordinates of negative weight. -/
theorem finrank_stableSubspace_add_ncard_weight_neg :
    Module.finrank ℝ φ.stableSubspace + {i | φ.weight i < 0}.ncard = Module.finrank ℝ E := by
  have := φ.finiteDimensional
  have h := LinearMap.finrank_range_add_finrank_ker φ.negativeCoord
  rw [LinearMap.range_eq_top.2 φ.surjective_negativeCoord, finrank_top,
    Module.finrank_fintype_fun_eq_card, Fintype.card_subtype] at h
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred, add_comm]
  exact h

/-- **The Morse index at the centre of a Morse–Bott chart** is the number of coordinates of
negative weight: in the chart, `f` is `f x` plus the diagonal quadratic form `(1/2) Σᵢ wᵢ zᵢ²`,
whose Hessian has negative index the number of negative weights. -/
theorem manifoldMorseIndex_eq_ncard_weight_neg :
    manifoldMorseIndex 𝓘(ℝ, E) f x = {i | φ.weight i < 0}.ncard := by
  have := φ.finiteDimensional
  have he : φ.toChart ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 2 M :=
    IsManifold.maximalAtlas_subset_of_le (by norm_num) φ.mem_maximalAtlas
  have hcrit : mvfderiv 𝓘(ℝ, E) f x = 0 := mvfderiv_eq_zero_iff.2 φ.mfderiv_self
  rw [manifoldMorseIndex_eq_morseIndex_of_mem_maximalAtlas he φ.mem_source
    ((φ.contMDiffAt φ.mem_source).of_le (by norm_num)) hcrit]
  -- In the chart, `f` is the quadratic normal form near the centre.
  have heq : f ∘ (φ.toChart.extend 𝓘(ℝ, E)).symm =ᶠ[𝓝 (φ.toChart.extend 𝓘(ℝ, E) x)]
      φ.quadratic := by
    simp only [OpenPartialHomeomorph.extend_coe_symm, OpenPartialHomeomorph.extend_coe,
      modelWithCornersSelf_coe_symm, modelWithCornersSelf_coe, Function.comp_apply, id_eq,
      Function.comp_id]
    filter_upwards [φ.toChart.open_target.mem_nhds (φ.toChart.map_source φ.mem_source)] with v hv
    rw [comp_apply, φ.eqOn_quadratic (φ.toChart.map_target hv), comp_apply,
      φ.toChart.right_inv hv]
  rw [morseIndex_congr_of_eventuallyEq heq]
  -- The normal form is the diagonal quadratic function of the weights, read through `L`.
  have hq : φ.quadratic = (fun u ↦ f x + diagonalQuadratic φ.weight u) ∘ φ.coordL := by
    funext z
    simp only [quadratic_apply, comp_apply, coordL_apply, diagonalQuadratic_apply,
      Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hdiff : ContDiffAt ℝ 2 (fun u ↦ f x + diagonalQuadratic φ.weight u) (φ.coordL 0) :=
    contDiffAt_const.add (contDiff_diagonalQuadratic _).contDiffAt
  have hcrit₀ : fderiv ℝ (fun u ↦ f x + diagonalQuadratic φ.weight u) (φ.coordL 0) = 0 := by
    rw [fderiv_const_add, (hasFDerivAt_diagonalQuadratic _ _).fderiv]
    simp
  simp only [OpenPartialHomeomorph.extend_coe, modelWithCornersSelf_coe, comp_apply, id_eq,
    φ.apply_self, hq]
  rw [morseIndex_comp hdiff φ.coordL.contDiff.contDiffAt hcrit₀
    (by rw [φ.coordL.fderiv]; exact ContinuousLinearMap.isInvertible_equiv), morseIndex_const_add,
    morseIndex_diagonalQuadratic, ← Set.ncard_coe_finset, Finset.coe_filter]
  simp

/-- The stable subspace of a Morse–Bott chart has dimension `n - λ`, where `λ` is the Morse index
at the centre. -/
theorem finrank_stableSubspace_add_manifoldMorseIndex :
    Module.finrank ℝ φ.stableSubspace + manifoldMorseIndex 𝓘(ℝ, E) f x = Module.finrank ℝ E := by
  rw [φ.manifoldMorseIndex_eq_ncard_weight_neg, φ.finrank_stableSubspace_add_ncard_weight_neg]

end MorseBottChart

end TauCeti
