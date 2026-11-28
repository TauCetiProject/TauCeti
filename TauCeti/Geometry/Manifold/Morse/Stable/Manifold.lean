/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Local.Basic
public import TauCeti.Geometry.Manifold.Morse.Bott.Chart.StableSubspace
public import TauCeti.Geometry.Manifold.LinearSlice
public import TauCeti.LinearAlgebra.ExtendByZero
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.Normed.Module.Complemented

/-!
# Stable and unstable manifolds of an adapted pseudo-gradient

Let `f` be a function on a compact boundaryless manifold `M` of dimension `n`, and `X` a
pseudo-gradient field adapted to `f`. For every critical point `x` of index `k`, the stable set
`W^s(x)` of the flow of `X` is flattened by charts of `M` onto a linear subspace of dimension
`n - k` (`TauCeti.IsAdaptedPseudoGradient.exists_stableSet_chart`). These slice charts make
`W^s(x)` a smooth manifold of dimension `n - k`, with the subspace topology and a smooth inclusion
into `M`.
When `f` is a Morse function, the same holds for the unstable set `W^u(x)`, in dimension `k`.

The slice charts come from the local picture: near `x`, `W^s(x)` is a coordinate subspace of a Morse
chart (`TauCeti.IsAdaptedPseudoGradient.exists_forall_mem_stableSet_iff`). A point `p` of `W^s(x)`
reaches that neighbourhood at some time `T`, and the Morse chart composed with the time-`T` map of
the flow is a slice chart at `p`. The unstable side follows by reversing time: `-X` is a
pseudo-gradient adapted to `-f` (`TauCeti.IsAdaptedPseudoGradient.neg`), and its flow is the
reversed flow.

## Main declarations

* `TauCeti.MorseChart.negativeExtend`: the vector with given coordinates of negative weight and
  zero coordinates of positive weight, a right inverse of the coordinates of negative weight
  `TauCeti.MorseBottChart.negativeCoord`. The stable subspace of a Morse chart, where the
  coordinates of negative weight vanish, is `TauCeti.MorseBottChart.stableSubspace`, of dimension
  `n - k`.
* `TauCeti.MorseChart.exp_neg_smul_coord_symm_linearFlow`: the linear flow, rescaled by `e^{-s}`,
  is the projection onto the coordinates of negative weight plus `e^{-2s}` times its complement.
* `TauCeti.IsAdaptedPseudoGradient.exists_isSliceChart_stableSet_flow`: the slice charts of `W^s(x)`
  given by a Morse chart composed with the time-`T` maps of the flow.
* `TauCeti.IsAdaptedPseudoGradient.exists_stableSet_chart`: slice charts for `W^s(x)`.
* `TauCeti.IsAdaptedPseudoGradient.exists_isSliceChart_stableSet` and
  `TauCeti.IsAdaptedPseudoGradient.exists_isSliceChart_unstableSet`: slice charts for `W^s(x)` and,
  for a Morse function, `W^u(x)`, onto subspaces of dimensions `n - k` and `k`.
* `TauCeti.IsAdaptedPseudoGradient.isOpen_stableSet_of_manifoldMorseIndex_eq_zero` and
  `TauCeti.IsAdaptedPseudoGradient.isOpen_unstableSet_of_manifoldMorseIndex_eq_finrank`: `W^s(x)`
  is open when `x` has index `0`, and `W^u(x)` when `x` has index `n`.
* `TauCeti.IsAdaptedPseudoGradient.unstableSet_eq_singleton_of_manifoldMorseIndex_eq_zero` and
  `TauCeti.IsAdaptedPseudoGradient.stableSet_eq_singleton_of_manifoldMorseIndex_eq_finrank`: the
  unstable manifold of a critical point of index `0` of a Morse function is the point itself, and
  so is the stable manifold of a critical point of index `n`.
* `TauCeti.IsAdaptedPseudoGradient.exists_stableSet_isManifold` and
  `TauCeti.IsAdaptedPseudoGradient.exists_unstableSet_isManifold`: the manifold structures, of
  dimensions `n - k` and `k`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Section 2.1.
-/

public section

open Filter Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {x : M} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace MorseChart

variable (φ : MorseChart E f x)

/-- The space of coordinates of negative weight of a Morse chart has the dimension of the Morse
index. -/
theorem finrank_negativeWeight_fun :
    Module.finrank ℝ ({i // φ.weight i < 0} → ℝ) = manifoldMorseIndex 𝓘(ℝ, E) f x := by
  rw [Module.finrank_fintype_fun_eq_card, ← φ.ncard_weight_neg, Set.ncard_eq_toFinset_card',
    Fintype.card_subtype, Set.toFinset_ofPred]

/-- The number of orientation coordinates is the dimension of the space of coordinates of negative
weight, so that its orientations are opposite to each other. -/
theorem card_fin_manifoldMorseIndex_eq_finrank :
    Fintype.card (Fin (manifoldMorseIndex 𝓘(ℝ, E) f x)) =
      Module.finrank ℝ ({i // φ.weight i < 0} → ℝ) := by
  rw [Fintype.card_fin, φ.finrank_negativeWeight_fun]

/-- The product of `ℝ` with the coordinates of negative weight has dimension one more than the
Morse index. -/
theorem finrank_prod_negativeWeight_fun :
    Module.finrank ℝ (ℝ × ({i // φ.weight i < 0} → ℝ)) = 1 + manifoldMorseIndex 𝓘(ℝ, E) f x := by
  rw [Module.finrank_prod, Module.finrank_self, φ.finrank_negativeWeight_fun]

/-- A Morse chart at a critical point of index `n - 1` has exactly one coordinate of positive
weight. -/
theorem exists_weight_eq_one_of_add_one_eq_finrank
    (hx : manifoldMorseIndex 𝓘(ℝ, E) f x + 1 = Module.finrank ℝ E) :
    ∃ j, φ.weight j = 1 ∧ ∀ i, i ≠ j → φ.weight i < 0 := by
  classical
  set s := Finset.univ.filter fun i ↦ φ.weight i < 0
  have hs : s.card = manifoldMorseIndex 𝓘(ℝ, E) f x := by
    rw [← φ.ncard_weight_neg, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  obtain ⟨j, hj⟩ := Finset.card_eq_one.1 (show sᶜ.card = 1 by
    rw [Finset.card_compl, Fintype.card_fin]
    omega)
  have hmem (i : Fin (Module.finrank ℝ E)) : i ∈ sᶜ ↔ i = j := by rw [hj, Finset.mem_singleton]
  refine ⟨j, ?_, fun i hi ↦ ?_⟩
  · have h := (hmem j).2 rfl
    simp only [s, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact (φ.weight_eq_neg_one_or_eq_one j).resolve_left fun h' ↦ h (by rw [h']; norm_num)
  · by_contra h
    exact hi ((hmem i).1 (by simpa [s] using h))

/-- The vector of the model whose coordinates in the Morse chart `φ` are `c` in the directions of
negative weight and `0` in the directions of positive weight. -/
noncomputable def negativeExtend : ({i // φ.weight i < 0} → ℝ) →ₗ[ℝ] E :=
  (φ.coord.symm : (Fin (Module.finrank ℝ E) → ℝ) →ₗ[ℝ] E) ∘ₗ
    Function.ExtendByZero.linearMap ℝ ℝ Subtype.val

/-- The coordinates of negative weight of `φ.negativeExtend c` are `c`. -/
@[simp]
theorem coord_negativeExtend_of_weight_neg (c : {i // φ.weight i < 0} → ℝ)
    (i : {i // φ.weight i < 0}) : φ.coord (φ.negativeExtend c) i = c i := by
  simp [negativeExtend, Function.ExtendByZero.linearMap_apply_of_injective ℝ
    Subtype.val_injective]

/-- The coordinates of positive weight of `φ.negativeExtend c` vanish. -/
theorem coord_negativeExtend_of_not_weight_neg (c : {i // φ.weight i < 0} → ℝ)
    {i : Fin (Module.finrank ℝ E)} (hi : ¬φ.weight i < 0) : φ.coord (φ.negativeExtend c) i = 0 := by
  simp only [negativeExtend, LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply,
    LinearEquiv.apply_symm_apply]
  exact Function.ExtendByZero.linearMap_apply_of_notMem_range ℝ c fun ⟨j, hj⟩ ↦ hi (hj ▸ j.property)

/-- `negativeExtend` is a right inverse of the coordinates of negative weight. -/
@[simp]
theorem negativeCoord_negativeExtend (c : {i // φ.weight i < 0} → ℝ) :
    φ.negativeCoord (φ.negativeExtend c) = c := by
  funext i
  rw [φ.negativeCoord_apply, coord_negativeExtend_of_weight_neg]

/-- `negativeExtend` is injective. -/
theorem injective_negativeExtend : Injective φ.negativeExtend :=
  LeftInverse.injective φ.negativeCoord_negativeExtend

/-- A point of the chart whose coordinates are `c ≠ 0` in the directions of negative weight and `0`
elsewhere is not the centre of the chart. -/
theorem toChart_symm_negativeExtend_ne {c : {i // φ.weight i < 0} → ℝ} (hc : c ≠ 0)
    (hT : φ.negativeExtend c ∈ φ.toChart.target) : φ.toChart.symm (φ.negativeExtend c) ≠ x := by
  intro h
  have h0 : φ.negativeExtend c = 0 := by
    rw [← φ.toChart.right_inv hT, h, φ.apply_self]
  exact hc (φ.injective_negativeExtend (h0.trans (map_zero _).symm))

/-- A vector whose coordinates of positive weight vanish is recovered from its coordinates of
negative weight. -/
theorem negativeExtend_negativeCoord {v : E}
    (hv : ∀ i, ¬φ.weight i < 0 → φ.coord v i = 0) : φ.negativeExtend (φ.negativeCoord v) = v := by
  refine φ.coord.injective (funext fun i ↦ ?_)
  by_cases hi : φ.weight i < 0
  · exact (φ.coord_negativeExtend_of_weight_neg _ ⟨i, hi⟩).trans (φ.negativeCoord_apply _ _)
  · rw [φ.coord_negativeExtend_of_not_weight_neg _ hi, hv i hi]

/-- The linear flow multiplies `φ.negativeExtend c` by `e^{t}` at time `t`. -/
theorem linearFlow_coord_negativeExtend (t : ℝ) (c : {i // φ.weight i < 0} → ℝ) :
    φ.linearFlow t (φ.coord (φ.negativeExtend c)) =
      Real.exp t • φ.coord (φ.negativeExtend c) := by
  funext i
  rw [Pi.smul_apply, smul_eq_mul]
  rcases φ.weight_eq_neg_one_or_eq_one i with hi | hi
  · rw [φ.linearFlow_of_weight_eq_neg_one hi]
  · rw [MorseBottChart.linearFlow_apply,
      φ.coord_negativeExtend_of_not_weight_neg c (by rw [hi]; norm_num), mul_zero, mul_zero]

/-- **The rescaled linear flow.** Read in the coordinates of a Morse chart, the linear flow for the
time `s`, multiplied by `e^{-s}`, keeps the coordinates of negative weight and multiplies those of
positive weight by `e^{-2s}`: it is the projection `v ↦ φ.negativeExtend (φ.negativeCoord v)`
plus `e^{-2s}` times the complementary projection. -/
theorem exp_neg_smul_coord_symm_linearFlow (s : ℝ) (v : E) :
    Real.exp (-s) • φ.coord.symm (φ.linearFlow s (φ.coord v)) =
      φ.negativeExtend (φ.negativeCoord v) +
        Real.exp (-(2 * s)) • (v - φ.negativeExtend (φ.negativeCoord v)) := by
  refine φ.coord.injective (funext fun i ↦ ?_)
  simp only [map_smul, map_add, map_sub, LinearEquiv.apply_symm_apply, Pi.smul_apply,
    Pi.add_apply, Pi.sub_apply, smul_eq_mul]
  rcases φ.weight_eq_neg_one_or_eq_one i with hi | hi
  · have hneg : φ.weight i < 0 := by rw [hi]; norm_num
    rw [φ.linearFlow_of_weight_eq_neg_one hi,
      φ.coord_negativeExtend_of_weight_neg _ ⟨i, hneg⟩, φ.negativeCoord_apply, ← mul_assoc,
      ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul, sub_self, mul_zero, add_zero]
  · have hpos : ¬φ.weight i < 0 := by rw [hi]; norm_num
    rw [φ.linearFlow_of_weight_eq_one hi, φ.coord_negativeExtend_of_not_weight_neg _ hpos,
      ← mul_assoc, ← Real.exp_add, sub_zero, zero_add]
    congr 2
    ring

/-- If the coordinates of `a` are those of `b` moved by the linear flow for the time `s`, the
coordinates of negative weight of `a` are `e^{s}` times those of `b`. -/
theorem negativeCoord_eq_exp_smul_of_coord_eq {s : ℝ} {a b : E}
    (h : φ.coord a = φ.linearFlow s (φ.coord b)) :
    φ.negativeCoord a = Real.exp s • φ.negativeCoord b := by
  funext i
  have hi : φ.weight i = -1 :=
    (φ.weight_eq_neg_one_or_eq_one i).resolve_right ((φ.weight_ne_one_iff i).2 i.property)
  rw [Pi.smul_apply, φ.negativeCoord_apply, φ.negativeCoord_apply, h, smul_eq_mul,
    φ.linearFlow_of_weight_eq_neg_one hi]

/-- The stable subspace of the negated Morse chart consists of the vectors whose coordinates of
positive weight vanish, the vectors `φ.negativeExtend c`. -/
theorem mem_neg_stableSubspace_iff (h : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x) {v : E} :
    v ∈ (φ.neg h).stableSubspace ↔ ∀ i, ¬φ.weight i < 0 → φ.coord v i = 0 := by
  rw [MorseBottChart.mem_stableSubspace, neg_coord, neg_weight]
  refine forall_congr' fun i ↦ ?_
  rcases φ.weight_eq_neg_one_or_eq_one i with hi | hi <;> simp [hi]

/-- The diagonal form `Σᵢ wᵢ (L u)ᵢ²` of a Morse chart is positive on the nonzero vectors of the
stable subspace, where the coordinates of negative weight vanish. -/
theorem sum_weight_mul_coord_sq_pos {u : E} (hu : u ∈ φ.stableSubspace) (hu0 : u ≠ 0) :
    0 < ∑ i, φ.weight i * φ.coord u i ^ 2 := by
  -- Each term is `(L u)ᵢ²`: for a negative weight, the coordinate vanishes.
  have hterm (i : Fin (Module.finrank ℝ E)) : φ.weight i * φ.coord u i ^ 2 = φ.coord u i ^ 2 := by
    rcases φ.weight_eq_neg_one_or_eq_one i with hi | hi
    · simp [φ.mem_stableSubspace.1 hu i (by rw [hi]; norm_num)]
    · rw [hi, one_mul]
  obtain ⟨j, hj⟩ : ∃ j, φ.coord u j ≠ 0 := by
    by_contra! h
    exact hu0 (φ.coord.injective (funext fun i ↦ by simpa using h i))
  simp only [hterm]
  exact Finset.sum_pos' (fun i _ ↦ sq_nonneg _) ⟨j, Finset.mem_univ j, by positivity⟩

/-- **The stable subspaces of a Morse chart and of its negation span the model space.** The stable
subspace of the negated chart is the subspace where the coordinates of positive weight vanish, so
every vector is the sum of a vector of each of the two subspaces. -/
theorem stableSubspace_sup_stableSubspace_neg
    (h : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x) :
    φ.stableSubspace ⊔ (φ.neg h).stableSubspace = ⊤ := by
  refine eq_top_iff.2 fun v _ ↦ ?_
  -- Split `v` into its coordinates of positive weight and its coordinates of negative weight.
  have hv : v = φ.coord.symm (fun i ↦ if φ.weight i < 0 then 0 else φ.coord v i) +
      φ.coord.symm (fun i ↦ if φ.weight i < 0 then φ.coord v i else 0) := by
    rw [← map_add, ← φ.coord.symm_apply_apply v]
    congr 1
    ext i
    simp only [LinearEquiv.apply_symm_apply, Pi.add_apply]
    split_ifs <;> simp
  rw [hv]
  refine Submodule.add_mem_sup (φ.mem_stableSubspace.2 fun i hi ↦ by simp [hi]) ?_
  rw [MorseBottChart.mem_stableSubspace, neg_weight, neg_coord]
  intro i hi
  simp [not_lt.2 (neg_neg_iff_pos.1 hi).le]

end MorseChart

namespace IsAdaptedPseudoGradient

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]

/-- **The slice charts of the stable manifold along the flow.** Let `φ` be a Morse chart at `x` in
which `X` is linear. There is an open neighbourhood `D` of `x` in the chart such that for every
time `T`, the chart `φ` restricted to `D`, composed with the time-`T` map of the flow, flattens
`W^s(x)` onto the stable subspace of `φ`. -/
theorem exists_isSliceChart_stableSet_flow (hX : IsAdaptedPseudoGradient f X)
    (φ : MorseChart E f x)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i)) :
    ∃ D : Set M, IsOpen D ∧ x ∈ D ∧ D ⊆ φ.toChart.source ∧ ∀ T : ℝ,
      IsSliceChart ((hX.flowDiffeomorph T).toHomeomorph.transOpenPartialHomeomorph
        (φ.toChart.restr D)) (φ.stableSubspace : Set E) (hX.flow.stableSet x) := by
  obtain ⟨ε, hε, hloc⟩ := hX.exists_forall_mem_stableSet_iff φ hφ
  set D := φ.toChart.source ∩ φ.toChart ⁻¹' {v : E | ‖φ.coord v‖ < ε}
  have hD : IsOpen D := φ.toChart.continuousOn.isOpen_inter_preimage φ.toChart.open_source
    (isOpen_lt (continuous_norm.comp φ.continuous_coord) continuous_const)
  refine ⟨D, hD, ⟨φ.mem_source, by simpa using hε⟩, inter_subset_left, fun T ↦ ?_⟩
  rw [← hX.isBottAdaptedPseudoGradient_flowDiffeomorph]
  exact hX.isBottAdaptedPseudoGradient.isSliceChart_flowDiffeomorph_trans_restr
    (fun t y ↦ by rw [hX.isBottAdaptedPseudoGradient_flow, Flow.apply_mem_stableSet_iff]) hD
    (fun y hy ↦ (hloc y hy.1 hy.2).trans φ.mem_stableSubspace.symm) T

/-- **Slice charts for the stable manifold.** Let `φ` be a Morse chart at `x` in which `X` is
linear. Every point of `W^s(x)` lies in the source of a chart of the maximal atlas that flattens
`W^s(x)` onto the stable subspace of `φ`. -/
theorem exists_stableSet_chart (hX : IsAdaptedPseudoGradient f X)
    (φ : MorseChart E f x)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {p : M} (hp : p ∈ hX.flow.stableSet x) :
    ∃ q : OpenPartialHomeomorph M E, p ∈ q.source ∧
      q ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M ∧
      ∀ z ∈ q.source, z ∈ hX.flow.stableSet x ↔ q z ∈ φ.stableSubspace := by
  obtain ⟨D, hD, hxD, hDs, hslice⟩ := hX.exists_isSliceChart_stableSet_flow φ hφ
  obtain ⟨T, hT⟩ := ((Flow.mem_stableSet.1 hp).eventually (hD.mem_nhds hxD)).exists
  obtain ⟨q, hpq, hq, hs⟩ := hX.isBottAdaptedPseudoGradient.exists_isSliceChart_of_flow_mem
    φ.mem_maximalAtlas hD hDs (hX.isBottAdaptedPseudoGradient_flowDiffeomorph T ▸ hslice T)
    (hX.isBottAdaptedPseudoGradient_flow ▸ hT)
  exact ⟨q, hpq, hq, isSliceChart_iff.1 hs⟩

/-- **Slice charts for the stable manifold of a critical point.** Every point of the stable
manifold of a critical point `x` lies in the source of a chart of the maximal atlas that flattens
`W^s(x)` onto a subspace of dimension `n - ind x`. -/
theorem exists_isSliceChart_stableSet (hX : IsAdaptedPseudoGradient f X)
    (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) {p : M}
    (hp : p ∈ hX.flow.stableSet x) :
    ∃ (L : Submodule ℝ E) (q : OpenPartialHomeomorph M E),
      Module.finrank ℝ L + manifoldMorseIndex 𝓘(ℝ, E) f x = Module.finrank ℝ E ∧
        p ∈ q.source ∧ q ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M ∧
        IsSliceChart q (L : Set E) (hX.flow.stableSet x) := by
  obtain ⟨φ, hφ⟩ := hX.exists_morseChart x hx
  obtain ⟨q, hpq, hq, hmem⟩ := hX.exists_stableSet_chart φ hφ hp
  exact ⟨φ.stableSubspace, q, φ.finrank_stableSubspace_add_manifoldMorseIndex, hpq, hq,
    isSliceChart_iff.2 hmem⟩

/-- **Slice charts for the unstable manifold of a critical point.** For a Morse function, every
point of the unstable manifold of a critical point `x` lies in the source of a chart of the maximal
atlas that flattens `W^u(x)` onto a subspace of dimension `ind x`. These are the slice charts of
the stable manifold of `x` for the reversed pseudo-gradient `-X`, adapted to `-f`. -/
theorem exists_isSliceChart_unstableSet (hX : IsAdaptedPseudoGradient f X)
    (hf : IsMorse 𝓘(ℝ, E) f) (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) {p : M}
    (hp : p ∈ hX.flow.unstableSet x) :
    ∃ (L : Submodule ℝ E) (q : OpenPartialHomeomorph M E),
      Module.finrank ℝ L = manifoldMorseIndex 𝓘(ℝ, E) f x ∧
        p ∈ q.source ∧ q ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M ∧
        IsSliceChart q (L : Set E) (hX.flow.unstableSet x) := by
  rw [hX.unstableSet_eq_stableSet_neg hf] at hp ⊢
  obtain ⟨L, q, hL, hpq, hq, hs⟩ :=
    (hX.neg hf).exists_isSliceChart_stableSet (mfderiv_neg_eq_zero_iff.2 hx) hp
  have hidx := (hf.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero hx
    ).manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
  exact ⟨L, q, by omega, hpq, hq, hs⟩

/-- **The stable manifold of a critical point of index `0` is open.** Its slice charts flatten it
onto a subspace of full dimension, so it contains the source of a chart around each of its
points. -/
theorem isOpen_stableSet_of_manifoldMorseIndex_eq_zero (hX : IsAdaptedPseudoGradient f X)
    (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) (hind : manifoldMorseIndex 𝓘(ℝ, E) f x = 0) :
    IsOpen (hX.flow.stableSet x) := by
  refine isOpen_iff_mem_nhds.2 fun p hp ↦ ?_
  obtain ⟨L, q, hL, hpq, -, hs⟩ := hX.exists_isSliceChart_stableSet hx hp
  have hLtop : L = ⊤ := Submodule.eq_top_of_finrank_eq (by omega)
  exact Filter.mem_of_superset (q.open_source.mem_nhds hpq) fun z hz ↦
    (isSliceChart_iff.1 hs z hz).2 (by simp [hLtop])

/-- **The unstable manifold of a critical point of top index is open.** Its slice charts flatten
it onto a subspace of full dimension, so it contains the source of a chart around each of its
points. -/
theorem isOpen_unstableSet_of_manifoldMorseIndex_eq_finrank (hX : IsAdaptedPseudoGradient f X)
    (hf : IsMorse 𝓘(ℝ, E) f) (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f x = Module.finrank ℝ E) :
    IsOpen (hX.flow.unstableSet x) := by
  refine isOpen_iff_mem_nhds.2 fun p hp ↦ ?_
  obtain ⟨L, q, hL, hpq, -, hs⟩ := hX.exists_isSliceChart_unstableSet hf hx hp
  have hLtop : L = ⊤ := Submodule.eq_top_of_finrank_eq (by omega)
  exact Filter.mem_of_superset (q.open_source.mem_nhds hpq) fun z hz ↦
    (isSliceChart_iff.1 hs z hz).2 (by simp [hLtop])

/-- **The stable manifold of a critical point of top index is a point.** For a critical point `x`
of index `n = dim M`, no other trajectory converges to `x` in forward time: near `x` the slice
charts flatten `W^s(x)` onto the zero subspace, and every trajectory converging to `x` in forward
time enters such a chart. -/
theorem stableSet_eq_singleton_of_manifoldMorseIndex_eq_finrank (hX : IsAdaptedPseudoGradient f X)
    (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f x = Module.finrank ℝ E) :
    hX.flow.stableSet x = {x} := by
  have hxs : x ∈ hX.flow.stableSet x := (hX.mem_unstableSet_inter_stableSet_self hx).2
  obtain ⟨L, φ, hL, hxφ, -, hs⟩ := hX.exists_isSliceChart_stableSet hx hxs
  obtain rfl : L = ⊥ := Submodule.finrank_eq_zero.1 (by omega)
  -- In the slice chart at `x`, the only point of `W^s(x)` is `x` itself.
  have hloc (z : M) (hz : z ∈ φ.source) (hzs : z ∈ hX.flow.stableSet x) : z = x := by
    have hz0 : φ z = 0 := by simpa using (isSliceChart_iff.1 hs z hz).1 hzs
    have hx0 : φ x = 0 := by simpa using (isSliceChart_iff.1 hs x hxφ).1 hxs
    exact φ.injOn hz hxφ (hz0.trans hx0.symm)
  refine subset_antisymm (fun p hp ↦ ?_) (singleton_subset_iff.2 hxs)
  obtain ⟨t, ht⟩ := ((Flow.mem_stableSet.1 hp).eventually
    (φ.open_source.mem_nhds hxφ)).exists
  have hpt := hloc _ ht ((Flow.apply_mem_stableSet_iff _ t).2 hp)
  rw [mem_singleton_iff, ← hX.flow.map_neg_apply_map t p, hpt,
    hX.flow_apply_of_mfderiv_eq_zero hx]

/-- **The unstable manifold of a critical point of index zero is a point.** For a critical point
`x` of index `0` of a Morse function, `W^u(x)` is the stable manifold of `x` for the reversed
pseudo-gradient `-X`, and `x` has top index for `-f`. -/
theorem unstableSet_eq_singleton_of_manifoldMorseIndex_eq_zero (hX : IsAdaptedPseudoGradient f X)
    (hf : IsMorse 𝓘(ℝ, E) f) (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f x = 0) :
    hX.flow.unstableSet x = {x} := by
  rw [hX.unstableSet_eq_stableSet_neg hf]
  have hidx := (hf.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero hx
    ).manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
  exact (hX.neg hf).stableSet_eq_singleton_of_manifoldMorseIndex_eq_finrank
    (mfderiv_neg_eq_zero_iff.2 hx) (by omega)

/-- **The stable set is a manifold of dimension `n - k`.** For a critical point `x` of index
`k`, the stable set `W^s(x)` of the flow of an adapted pseudo-gradient carries a smooth
manifold structure modelled on a subspace of dimension `n - k`, with its subspace topology and a
smooth inclusion into `M`. -/
theorem exists_stableSet_isManifold (hX : IsAdaptedPseudoGradient f X)
    (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) :
    ∃ L : Submodule ℝ E,
      Module.finrank ℝ L + manifoldMorseIndex 𝓘(ℝ, E) f x = Module.finrank ℝ E ∧
      ∃ C : ChartedSpace L (hX.flow.stableSet x), letI := C
        IsManifold 𝓘(ℝ, L) ∞ (hX.flow.stableSet x) ∧
        ContMDiff 𝓘(ℝ, L) 𝓘(ℝ, E) ∞ (Subtype.val : hX.flow.stableSet x → M) := by
  obtain ⟨φ, hφ⟩ := hX.exists_morseChart x hx
  obtain ⟨N, hN⟩ := φ.stableSubspace.exists_isCompl
  refine ⟨φ.stableSubspace, φ.finrank_stableSubspace_add_manifoldMorseIndex, ?_⟩
  refine exists_isManifold_of_linearSubspaceCharts
    (Submodule.IsCompl.isTopCompl_of_isClosed hN
      φ.stableSubspace.isClosed_of_finiteDimensional N.isClosed_of_finiteDimensional)
    fun y ↦ ?_
  obtain ⟨q, hyq, hq, hmem⟩ := hX.exists_stableSet_chart φ hφ y.property
  exact ⟨q, hyq, fun z hz ↦ contMDiffAt_of_mem_maximalAtlas hq hz,
    fun z hz ↦ contMDiffAt_symm_of_mem_maximalAtlas hq hz, hmem⟩

/-- **The unstable set is a manifold of dimension `k`.** For a critical point `x` of index
`k` of a Morse function, the unstable set `W^u(x)` of the flow of an adapted pseudo-gradient
carries a smooth manifold structure modelled on a subspace of dimension `k`, with its subspace
topology and a smooth inclusion into `M`. -/
theorem exists_unstableSet_isManifold (hX : IsAdaptedPseudoGradient f X)
    (hf : IsMorse 𝓘(ℝ, E) f) (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) :
    ∃ L : Submodule ℝ E, Module.finrank ℝ L = manifoldMorseIndex 𝓘(ℝ, E) f x ∧
      ∃ C : ChartedSpace L (hX.flow.unstableSet x), letI := C
        IsManifold 𝓘(ℝ, L) ∞ (hX.flow.unstableSet x) ∧
        ContMDiff 𝓘(ℝ, L) 𝓘(ℝ, E) ∞ (Subtype.val : hX.flow.unstableSet x → M) := by
  obtain ⟨L, hL, hman⟩ := (hX.neg hf).exists_stableSet_isManifold (mfderiv_neg_eq_zero_iff.2 hx)
  have hidx := (hf.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero hx
    ).manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
  rw [hX.unstableSet_eq_stableSet_neg hf]
  exact ⟨L, by omega, hman⟩

end IsAdaptedPseudoGradient

end TauCeti
