/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.ProdLp
public import TauCeti.Geometry.Manifold.Morse.Index
public import TauCeti.LinearAlgebra.Pi
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import TauCeti.Analysis.Calculus.Morse.LocalNormalForm
import TauCeti.Analysis.Normed.Lp.PiLp

/-!
# The Morse lemma on a smooth manifold

At a nondegenerate critical point `x` of a smooth function `f` on a boundaryless smooth manifold
modelled on a finite-dimensional real normed space `E`, there is a chart of the maximal atlas,
centred at `x`, in which `f` is a nondegenerate quadratic form: after a linear change of
coordinates `L : E ≃ (Fin n → ℝ)`,

`f y = f x + (1/2) Σᵢ wᵢ (L (ψ y))ᵢ²`, with every `wᵢ = ±1`,

and the number of negative weights is the manifold Morse index of `f` at `x`. Such a chart is
recorded as a `TauCeti.MorseChart`. A Morse chart puts the function in quadratic form; it is
used to choose an adapted pseudo-gradient field that is linear near the critical point, whose
stable and unstable manifolds are then studied.

## Main declarations

* `TauCeti.MorseChart`: a chart centred at a critical point in which the function is a diagonal
  nondegenerate quadratic form.
* `TauCeti.MorseChart.restr`: the restriction of a Morse chart to an open neighbourhood of its
  centre.
* `TauCeti.MorseChart.splitCoord`: the coordinates of a Morse chart, split by the sign of the
  weight.
* `TauCeti.MorseChart.splitCoordL`: the split coordinates as a continuous linear equivalence of
  the model.
* `TauCeti.MorseChart.max_norm_fst_norm_snd_splitCoord`: the sup norm of the coordinates is the
  larger of the norms of the two factors of the split coordinates.
* `TauCeti.MorseChart.apply_toChart_symm_coord_symm_splitCoord_symm`: the Morse normal form in
  split coordinates.
* `TauCeti.MorseChart.lt_apply_of_norm_fst_eq`, `TauCeti.MorseChart.apply_lt_of_norm_snd_eq`: `f`
  is above `f x` where the contracting split coordinate dominates and below `f x` where the
  expanding one dominates.
* `TauCeti.MorseChart.finrank_snd_splitCoord` and
  `TauCeti.MorseChart.finrank_fst_splitCoord_add_manifoldMorseIndex`: the expanding factor of the
  split coordinates has dimension the Morse index, and the contracting factor the complementary
  dimension.
* `TauCeti.MorseChart.neg`: a Morse chart for `f` is a Morse chart for `-f`, with the opposite
  weights.
* `TauCeti.IsManifoldNondegenerateCriticalPoint.nonempty_morseChart`: the Morse lemma on a
  manifold, for a function smooth near the critical point.
* `TauCeti.IsMorse.nonempty_morseChart`: every critical point of a Morse function has a Morse
  chart.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Theorem 1.3.1.
-/

public section

open Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {x : M}

variable (E) in
/-- A **Morse chart** for `f` at `x`: a chart of the maximal atlas, centred at `x`, together with
a linear change of coordinates `L : E ≃ (Fin n → ℝ)` and weights `wᵢ = ±1`, such that on the source
of the chart `f y = f x + (1/2) Σᵢ wᵢ (L (ψ y))ᵢ²`. The number of negative weights is the manifold
Morse index of `f` at `x`. -/
structure MorseChart (f : M → ℝ) (x : M) where
  /-- The chart. -/
  toChart : OpenPartialHomeomorph M E
  mem_maximalAtlas : toChart ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M
  mem_source : x ∈ toChart.source
  apply_self : toChart x = 0
  /-- The linear change of coordinates that diagonalizes the Hessian. -/
  coord : E ≃ₗ[ℝ] (Fin (Module.finrank ℝ E) → ℝ)
  /-- The diagonal weights of the Hessian. -/
  weight : Fin (Module.finrank ℝ E) → ℝ
  weight_eq_neg_one_or_eq_one : ∀ i, weight i = -1 ∨ weight i = 1
  ncard_weight_neg : {i | weight i < 0}.ncard = manifoldMorseIndex 𝓘(ℝ, E) f x
  eq_quadratic : ∀ y ∈ toChart.source,
    f y = f x + (2 : ℝ)⁻¹ * ∑ i, weight i * (coord (toChart y) i) ^ 2

attribute [simp] MorseChart.mem_source MorseChart.apply_self

namespace MorseChart

/-- The restriction of a Morse chart to an open neighbourhood `s` of its centre: the chart is
restricted to `s`, and the coordinates and weights are unchanged. -/
noncomputable def restr (φ : MorseChart E f x) {s : Set M} (hs : IsOpen s) (hx : x ∈ s) :
    MorseChart E f x where
  toChart := φ.toChart.restr s
  mem_maximalAtlas := restr_mem_maximalAtlas _ φ.mem_maximalAtlas hs
  mem_source := by rw [φ.toChart.restr_source' s hs]; exact ⟨φ.mem_source, hx⟩
  apply_self := φ.apply_self
  coord := φ.coord
  weight := φ.weight
  weight_eq_neg_one_or_eq_one := φ.weight_eq_neg_one_or_eq_one
  ncard_weight_neg := φ.ncard_weight_neg
  eq_quadratic y hy := φ.eq_quadratic y (by rw [φ.toChart.restr_source' s hs] at hy; exact hy.1)

variable (φ : MorseChart E f x) {s : Set M} (hs : IsOpen s) (hx : x ∈ s)

/-- The chart of a restricted Morse chart is the restricted chart. -/
@[simp]
theorem restr_toChart : (φ.restr hs hx).toChart = φ.toChart.restr s := by
  rw [restr]

/-- Restricting a Morse chart does not change its coordinates. -/
@[simp]
theorem restr_coord : (φ.restr hs hx).coord = φ.coord := by
  rw [restr]

/-- Restricting a Morse chart does not change its weights. -/
@[simp]
theorem restr_weight : (φ.restr hs hx).weight = φ.weight := by
  rw [restr]

/-- The source of a restricted Morse chart. -/
theorem restr_source : (φ.restr hs hx).toChart.source = φ.toChart.source ∩ s :=
  φ.toChart.restr_source' s hs

/-- A point of the chart is the point with its own coordinates. -/
theorem toChart_symm_coord_symm_coord {y : M} (hy : y ∈ φ.toChart.source) :
    φ.toChart.symm (φ.coord.symm (φ.coord (φ.toChart y))) = y := by
  rw [LinearEquiv.symm_apply_apply, φ.toChart.left_inv hy]

/-- The chart sends `0` back to the critical point. -/
@[simp]
theorem toChart_symm_zero : φ.toChart.symm 0 = x := by
  rw [← φ.apply_self, φ.toChart.left_inv φ.mem_source]

/-- The centre is the only point of the source sent to `0`. -/
theorem toChart_eq_zero_iff {y : M} (hy : y ∈ φ.toChart.source) : φ.toChart y = 0 ↔ y = x := by
  refine ⟨fun h ↦ φ.toChart.injOn hy φ.mem_source ?_, fun h ↦ h ▸ φ.apply_self⟩
  rw [h, φ.apply_self]

/-- The critical point is the point with coordinates `0`. -/
theorem toChart_symm_coord_symm_zero : φ.toChart.symm (φ.coord.symm 0) = x := by
  rw [map_zero, toChart_symm_zero]

/-- The chart of a Morse chart lies in the maximal atlas of class `C¹`. -/
theorem mem_maximalAtlas_one : φ.toChart ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M :=
  IsManifold.maximalAtlas_subset_of_le (by simp) φ.mem_maximalAtlas

/-- The chart of a Morse chart is differentiable on its source. -/
theorem mdifferentiableAt_toChart {y : M} (hy : y ∈ φ.toChart.source) :
    MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y :=
  mdifferentiableAt_of_mem_maximalAtlas φ.mem_maximalAtlas_one hy

/-- A coordinate of a Morse chart has weight different from `1` exactly when it has negative
weight. -/
theorem weight_ne_one_iff (i : Fin (Module.finrank ℝ E)) : ¬φ.weight i = 1 ↔ φ.weight i < 0 := by
  rcases φ.weight_eq_neg_one_or_eq_one i with hi | hi <;> norm_num [hi]

/-- A coordinate of a Morse chart has weight `1` exactly when it has positive weight. -/
theorem weight_eq_one_iff (i : Fin (Module.finrank ℝ E)) : φ.weight i = 1 ↔ 0 < φ.weight i := by
  rcases φ.weight_eq_neg_one_or_eq_one i with hi | hi <;> norm_num [hi]

/-- The **split coordinates** of a Morse chart: the pair formed by the coordinates of positive
weight and the remaining coordinates, of weight `-1`. Each factor carries the sup norm. -/
noncomputable def splitCoord :
    (Fin (Module.finrank ℝ E) → ℝ) ≃ₗ[ℝ]
      WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ)) :=
  (LinearEquiv.piEquivPiSubtypeProd ℝ (fun i ↦ φ.weight i = 1) fun _ ↦ ℝ).trans
    (WithLp.linearEquiv 2 ℝ _).symm

/-- The first factor of the split coordinates consists of the coordinates of positive weight. -/
@[simp]
theorem splitCoord_fst_apply (z : Fin (Module.finrank ℝ E) → ℝ) (i : {i // φ.weight i = 1}) :
    (φ.splitCoord z).fst i = z i := by
  simp [splitCoord]

/-- The second factor of the split coordinates consists of the coordinates of negative weight. -/
@[simp]
theorem splitCoord_snd_apply (z : Fin (Module.finrank ℝ E) → ℝ) (i : {i // ¬φ.weight i = 1}) :
    (φ.splitCoord z).snd i = z i := by
  simp [splitCoord]

/-- The coordinates of a point given in split coordinates. -/
@[simp]
theorem splitCoord_symm_apply
    (w : WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ)))
    (i : Fin (Module.finrank ℝ E)) :
    φ.splitCoord.symm w i = if h : φ.weight i = 1 then w.fst ⟨i, h⟩ else w.snd ⟨i, h⟩ := by
  simp [splitCoord]

/-- The sup norm of the coordinates of a Morse chart is the larger of the norms of the two factors
of the split coordinates. So the coordinate cube `‖z‖ ≤ ε` is the box `‖u‖ ≤ ε, ‖v‖ ≤ ε` of the
split model. -/
theorem max_norm_fst_norm_snd_splitCoord (z : Fin (Module.finrank ℝ E) → ℝ) :
    max ‖(φ.splitCoord z).fst‖ ‖(φ.splitCoord z).snd‖ = ‖z‖ := by
  refine le_antisymm (max_le ?_ ?_) ?_
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg z)).2 fun i ↦ by
      simpa using norm_le_pi_norm z i
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg z)).2 fun i ↦ by
      simpa using norm_le_pi_norm z i
  · refine (pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg _))).2 fun i ↦ ?_
    by_cases hi : φ.weight i = 1
    · exact le_max_of_le_left (by simpa using norm_le_pi_norm (φ.splitCoord z).fst ⟨i, hi⟩)
    · exact le_max_of_le_right (by simpa using norm_le_pi_norm (φ.splitCoord z).snd ⟨i, hi⟩)

/-- The expanding factor of the split coordinates of a Morse chart has dimension the Morse index. -/
theorem finrank_snd_splitCoord :
    Module.finrank ℝ ({i // ¬φ.weight i = 1} → ℝ) = manifoldMorseIndex 𝓘(ℝ, E) f x := by
  rw [Module.finrank_fintype_fun_eq_card, ← φ.ncard_weight_neg, ← Nat.card_eq_fintype_card,
    ← Nat.card_coe_set_eq]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun i ↦ ?_)
  rcases φ.weight_eq_neg_one_or_eq_one i with hi | hi <;> norm_num [hi]

/-- The contracting and expanding factors of the split coordinates of a Morse chart have
complementary dimensions. -/
theorem finrank_fst_splitCoord_add_manifoldMorseIndex :
    Module.finrank ℝ ({i // φ.weight i = 1} → ℝ) + manifoldMorseIndex 𝓘(ℝ, E) f x =
      Module.finrank ℝ E := by
  rw [← φ.finrank_snd_splitCoord, Module.finrank_fintype_fun_eq_card,
    Module.finrank_fintype_fun_eq_card, Fintype.card_subtype_compl, Fintype.card_fin]
  have := Fintype.card_subtype_le fun i ↦ φ.weight i = 1
  rw [Fintype.card_fin] at this
  omega

section SplitBox

/-- **The Morse normal form in split coordinates.** At the point with split coordinates `(u, v)`,
`f = f x + (Σᵢ uᵢ² - Σⱼ vⱼ²) / 2`. -/
theorem apply_toChart_symm_coord_symm_splitCoord_symm
    {z : WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ))}
    (hz : φ.coord.symm (φ.splitCoord.symm z) ∈ φ.toChart.target) :
    f (φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z))) =
      f x + 2⁻¹ * (∑ i, z.fst i ^ 2 - ∑ i, z.snd i ^ 2) := by
  rw [φ.eq_quadratic _ (φ.toChart.map_target hz), φ.toChart.right_inv hz,
    LinearEquiv.apply_symm_apply,
    ← Fintype.sum_subtype_add_sum_subtype (fun i ↦ φ.weight i = 1), sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  congr 2
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp [i.2]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp [(φ.weight_eq_neg_one_or_eq_one i).resolve_right i.2]
    norm_num

variable {φ}

/-- On the box, the split coordinates read a point of the chart. -/
theorem coord_symm_splitCoord_symm_mem_target_of_norm_le {ε : ℝ}
    (hε : ∀ z, ‖z‖ ≤ ε → φ.coord.symm z ∈ φ.toChart.target)
    {z : WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ))}
    (hfst : ‖z.fst‖ ≤ ε) (hsnd : ‖z.snd‖ ≤ ε) :
    φ.coord.symm (φ.splitCoord.symm z) ∈ φ.toChart.target :=
  hε _ <| by
    rw [← φ.max_norm_fst_norm_snd_splitCoord, LinearEquiv.apply_symm_apply]
    exact max_le hfst hsnd

variable (φ) in
/-- The point with given split coordinates determines them. -/
theorem injOn_toChart_symm_coord_symm_splitCoord_symm :
    InjOn (fun z ↦ φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z)))
      {z | φ.coord.symm (φ.splitCoord.symm z) ∈ φ.toChart.target} := fun z hz z' hz' h ↦
  φ.splitCoord.symm.injective (φ.coord.symm.injective
    (φ.toChart.symm.injOn (by simpa using hz) (by simpa using hz') h))

/-- **Above the critical value on the entrance face.** At a point of the chart whose contracting
split coordinate has norm `ε` and whose expanding one is small, `f` exceeds `f x`. -/
theorem lt_apply_of_norm_fst_eq {ε : ℝ}
    {z : WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ))}
    (hz : φ.coord.symm (φ.splitCoord.symm z) ∈ φ.toChart.target) (hfst : ‖z.fst‖ = ε)
    (hsnd : Module.finrank ℝ E * ‖z.snd‖ ^ 2 < ε ^ 2) :
    f x < f (φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z))) := by
  rw [φ.apply_toChart_symm_coord_symm_splitCoord_symm hz]
  -- Compare the sup norms of the split coordinates with their `L²` norms.
  have h₁ : ‖z.fst‖ ^ 2 ≤ ∑ i, z.fst i ^ 2 := by
    have h := PiLp.dist_ofLp_le (WithLp.toLp 2 z.fst) 0
    rw [dist_zero_right, WithLp.ofLp_toLp, WithLp.ofLp_zero, dist_zero_right] at h
    simpa [PiLp.norm_sq_eq_of_L2] using pow_le_pow_left₀ (norm_nonneg _) h 2
  have h₂ : ∑ i, z.snd i ^ 2 ≤ Fintype.card {i // ¬φ.weight i = 1} * ‖z.snd‖ ^ 2 := by
    have h := PiLp.dist_le_sqrt_card_mul_dist_ofLp (WithLp.toLp 2 z.snd) 0
    rw [dist_zero_right, WithLp.ofLp_toLp, WithLp.ofLp_zero, dist_zero_right] at h
    simpa [PiLp.norm_sq_eq_of_L2, mul_pow] using pow_le_pow_left₀ (norm_nonneg _) h 2
  have hcard : (Fintype.card {i // ¬φ.weight i = 1} : ℝ) ≤ Module.finrank ℝ E := by
    exact_mod_cast (Fintype.card_subtype_le _).trans (Fintype.card_fin _).le
  rw [hfst] at h₁
  nlinarith [mul_le_mul_of_nonneg_right hcard (sq_nonneg ‖z.snd‖)]

/-- **Below the critical value on the exit face.** At a point of the chart whose expanding split
coordinate has norm `ε` and whose contracting one is small, `f` is less than `f x`. -/
theorem apply_lt_of_norm_snd_eq {ε : ℝ}
    {z : WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ))}
    (hz : φ.coord.symm (φ.splitCoord.symm z) ∈ φ.toChart.target) (hsnd : ‖z.snd‖ = ε)
    (hfst : Module.finrank ℝ E * ‖z.fst‖ ^ 2 < ε ^ 2) :
    f (φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z))) < f x := by
  rw [φ.apply_toChart_symm_coord_symm_splitCoord_symm hz]
  -- Compare the sup norms of the split coordinates with their `L²` norms.
  have h₁ : ‖z.snd‖ ^ 2 ≤ ∑ i, z.snd i ^ 2 := by
    have h := PiLp.dist_ofLp_le (WithLp.toLp 2 z.snd) 0
    rw [dist_zero_right, WithLp.ofLp_toLp, WithLp.ofLp_zero, dist_zero_right] at h
    simpa [PiLp.norm_sq_eq_of_L2] using pow_le_pow_left₀ (norm_nonneg _) h 2
  have h₂ : ∑ i, z.fst i ^ 2 ≤ Fintype.card {i // φ.weight i = 1} * ‖z.fst‖ ^ 2 := by
    have h := PiLp.dist_le_sqrt_card_mul_dist_ofLp (WithLp.toLp 2 z.fst) 0
    rw [dist_zero_right, WithLp.ofLp_toLp, WithLp.ofLp_zero, dist_zero_right] at h
    simpa [PiLp.norm_sq_eq_of_L2, mul_pow] using pow_le_pow_left₀ (norm_nonneg _) h 2
  have hcard : (Fintype.card {i // φ.weight i = 1} : ℝ) ≤ Module.finrank ℝ E := by
    exact_mod_cast (Fintype.card_subtype_le _).trans (Fintype.card_fin _).le
  rw [hsnd] at h₁
  nlinarith [mul_le_mul_of_nonneg_right hcard (sq_nonneg ‖z.fst‖)]

end SplitBox

variable [FiniteDimensional ℝ E]

/-- The split coordinates of a Morse chart, as a continuous linear equivalence of the model. -/
noncomputable def splitCoordL :
    E ≃L[ℝ] WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ)) :=
  (φ.coord.trans φ.splitCoord).toContinuousLinearEquiv

/-- The continuous split coordinates of a point of the model are the split coordinates of its
coordinates. -/
@[simp]
theorem splitCoordL_apply (z : E) : φ.splitCoordL z = φ.splitCoord (φ.coord z) :=
  (rfl)

/-- The point of the model with given continuous split coordinates. -/
@[simp]
theorem splitCoordL_symm_apply
    (w : WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ))) :
    φ.splitCoordL.symm w = φ.coord.symm (φ.splitCoord.symm w) :=
  (rfl)

/-- A Morse chart for `f` at a nondegenerate critical point is a Morse chart for `-f`, with the
opposite weights. -/
noncomputable def neg (h : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x) :
    MorseChart E (-f) x where
  toChart := φ.toChart
  mem_maximalAtlas := φ.mem_maximalAtlas
  mem_source := φ.mem_source
  apply_self := φ.apply_self
  coord := φ.coord
  weight := -φ.weight
  weight_eq_neg_one_or_eq_one i := by
    rcases φ.weight_eq_neg_one_or_eq_one i with hi | hi <;> simp [hi]
  ncard_weight_neg := by
    have hidx := h.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
    have hset : {i | (-φ.weight) i < 0} = {i | φ.weight i < 0}ᶜ := by
      ext i
      rcases φ.weight_eq_neg_one_or_eq_one i with hi | hi <;> simp [hi]
    have hc := Set.ncard_add_ncard_compl {i | φ.weight i < 0}
    rw [Nat.card_eq_fintype_card, Fintype.card_fin, φ.ncard_weight_neg] at hc
    rw [hset]
    omega
  eq_quadratic y hy := by
    rw [Pi.neg_apply, Pi.neg_apply, φ.eq_quadratic y hy]
    simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
    ring

/-- The negated Morse chart has the same chart. -/
@[simp]
theorem neg_toChart (h : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x) :
    (φ.neg h).toChart = φ.toChart := by
  rw [neg]

/-- The negated Morse chart has the same coordinates. -/
@[simp]
theorem neg_coord (h : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x) :
    (φ.neg h).coord = φ.coord := by
  rw [neg]

/-- The negated Morse chart has the opposite weights. -/
@[simp]
theorem neg_weight (h : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x) :
    (φ.neg h).weight = -φ.weight := by
  rw [neg]

end MorseChart

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- **The Morse lemma on a manifold.** At a nondegenerate critical point `x` of a function `f`
that is smooth at every point of a neighbourhood of `x`, on a manifold modelled on a
finite-dimensional real normed space `E`, there is a Morse chart: a chart `ψ` of the maximal atlas,
centred at `x`, and a linear change of coordinates `L : E ≃ (Fin n → ℝ)` such that on the source
of `ψ`

`f y = f x + (1/2) Σᵢ wᵢ (L (ψ y))ᵢ²`,

where every weight `wᵢ` is `-1` or `1` and the number of negative weights is the manifold Morse
index of `f` at `x`. -/
theorem IsManifoldNondegenerateCriticalPoint.nonempty_morseChart
    (hf : ∀ᶠ y in 𝓝 x, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) ∞ f y)
    (h : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x) : Nonempty (MorseChart E f x) := by
  obtain ⟨s, hfs, hsopen, hxs⟩ := _root_.eventually_nhds_iff.1 hf
  replace hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞ f s := fun y hy ↦ (hfs y hy).contMDiffWithinAt
  set c := chartAt E x with hc
  set g : E → ℝ := f ∘ (extChartAt 𝓘(ℝ, E) x).symm with hgdef
  set a : E := extChartAt 𝓘(ℝ, E) x x
  set U := (extChartAt 𝓘(ℝ, E) x).target ∩ (extChartAt 𝓘(ℝ, E) x).symm ⁻¹' s
  have hU : IsOpen U := (continuousOn_extChartAt_symm x).isOpen_inter_preimage
    (isOpen_extChartAt_target x) hsopen
  have haU : a ∈ U := ⟨mem_extChartAt_target x, by
    rw [mem_preimage, extChartAt_to_inv]
    exact hxs⟩
  have hg : ContDiffOn ℝ ∞ g U :=
    (hf.comp ((contMDiffOn_extChartAt_symm x).mono inter_subset_left)
      fun _ hz ↦ hz.2).contDiffOn
  have h' : IsNondegenerateCriticalPoint g a := (isManifoldNondegenerateCriticalPoint_iff _).1 h
  obtain ⟨φ, -, haφ, hφa, hφ, hφsymm, hφg⟩ :=
    h'.exists_morse_chart_of_contDiffOn (n := ⊤) (hU.mem_nhds haU)
      (by simpa [← one_add_one_eq_two, ← add_assoc] using hg) (by simp)
  obtain ⟨w, hw, ⟨e⟩⟩ := h'.exists_hessianQuadraticForm_equivalent_weightedSumSquares
  have hext : ∀ y, extChartAt 𝓘(ℝ, E) x y = c y := fun y ↦ by simp [hc]
  have hleft : ∀ y ∈ c.source, g (c y) = f y := fun y hy ↦ by
    have hy' : y ∈ (extChartAt 𝓘(ℝ, E) x).source := by simpa [hc] using hy
    simp only [hgdef, comp_apply, ← hext, (extChartAt 𝓘(ℝ, E) x).left_inv hy']
  have hxc : x ∈ c.source := mem_chart_source E x
  have hca : c x = a := (hext x).symm
  refine ⟨⟨c.trans φ, ?_, ?_, ?_, e.toLinearEquiv, w, hw, ?_, ?_⟩⟩
  · rw [IsManifold.mem_maximalAtlas_iff_contMDiffOn]
    constructor
    · exact hφ.contMDiffOn.comp (contMDiffOn_chart.mono fun y hy ↦ hy.1) fun y hy ↦ hy.2
    · exact contMDiffOn_chart_symm.comp (hφsymm.contMDiffOn.mono fun y hy ↦ hy.1)
        fun y hy ↦ hy.2
  · refine ⟨hxc, ?_⟩
    rw [mem_preimage, OpenPartialHomeomorph.symm_symm, hca]
    exact haφ
  · simp [hca, hφa]
  · rw [manifoldMorseIndex_def, morseIndex_def]
    exact (QuadraticForm.sigNeg_of_equiv_weightedSumSquares ⟨e⟩).symm
  · intro y hy
    have hy1 : y ∈ c.source := hy.1
    have hy2 : c y ∈ φ.source := hy.2
    have hfx : g a = f x := by rw [← hca]; exact hleft x hxc
    rw [← hleft y hy1, hφg (c y) hy2, hfx]
    have hQ := e.map_app (φ (c y))
    rw [hessianQuadraticForm_apply] at hQ
    rw [← hQ, QuadraticMap.weightedSumSquares_apply]
    simp [sq]

/-- Every critical point of a Morse function has a Morse chart. -/
theorem IsMorse.nonempty_morseChart (hf : IsMorse 𝓘(ℝ, E) f) {x : M}
    (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) : Nonempty (MorseChart E f x) :=
  (hf.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero hx).nonempty_morseChart
    (Filter.Eventually.of_forall fun _ ↦ hf.contMDiff.contMDiffAt)

end TauCeti
