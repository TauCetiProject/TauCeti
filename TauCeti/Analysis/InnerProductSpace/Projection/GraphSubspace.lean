/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import TauCeti.Analysis.InnerProductSpace.Positive
public import TauCeti.Analysis.InnerProductSpace.Projection.Gap

/-!
# Angular operators and graph subspaces

Let `U` be a subspace of an inner product space `E` admitting an orthogonal projection `P_U`. An
*angular operator* from `U` to `Uᗮ` is a bounded operator `X` on `E` with `X P_U = X` and
`P_U X = 0`: it vanishes on `Uᗮ` and takes values in `Uᗮ`. Its *graph subspace* is
`graph(U, X) = {u + X u | u ∈ U}`, the subspace obtained by tilting `U` towards `Uᗮ` along `X`.

Graph subspaces are the standard coordinates for subspaces close to `U`: they turn statements
about the position of a subspace into statements about an operator, so that invariance of a graph
subspace becomes an operator Riccati equation and the angle it makes with `U` is measured by the
norm of `X`. This file computes the two quantities this description rests on.

* The gap between `U` and its graph subspace is `‖P_U - P_graph‖ = ‖X‖ / √(1 + ‖X‖²)`. In
  particular it is always less than `1`. The directed gap from the graph subspace to `U` attains
  this value, and the directed gap from `U` to the graph subspace is at most it. These are
  elementary distance computations; no completeness of `E` is needed.
* On a complete space, the orthogonal projection onto the graph subspace is
  `P_graph = A (1 + X†X)⁻¹ A†` with `A = P_U + X`, where `1 + X†X` is invertible because
  `⟪(1 + X†X) x, x⟫ = ‖x‖² + ‖X x‖²`.

The graph subspace is closed when `U` is complete, since `u ↦ u + X u` does not decrease norms on
`U` (`Submodule.IsAngularOperator.completeSpace_graphSubspace`).

## Main definitions

* `Submodule.IsAngularOperator U X`: `X` is an angular operator from `U` to `Uᗮ`.
* `Submodule.graphSubspace U X`: the graph subspace `{u + X u | u ∈ U}`.

## Main results

* `Submodule.IsAngularOperator.mem_graphSubspace_iff`: `y` lies in the graph subspace exactly when
  `P_{Uᗮ} y = X y`.
* `Submodule.IsAngularOperator.projectionGap_graphSubspace`: the exact gap
  `‖P_U - P_graph‖ = ‖X‖ / √(1 + ‖X‖²)`.
* `Submodule.IsAngularOperator.starProjection_graphSubspace`: the projection formula
  `P_graph = A (1 + X†X)⁻¹ A†`.

## References

* C. Davis, W. M. Kahan, *The rotation of eigenvectors by a perturbation. III*,
  SIAM J. Numer. Anal. **7** (1970), 1–46.
* V. Kostrykin, K. A. Makarov, A. K. Motovilov, *Existence and uniqueness of solutions to the
  operator Riccati equation. A geometric approach*, Contemp. Math. **327** (2003), 181–198.
-/

public section

noncomputable section

namespace Submodule

open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

section GraphSubspace

variable {U : Submodule 𝕜 E} {X : E →L[𝕜] E}

variable (U) in
/-- The graph subspace `{u + X u | u ∈ U}` of an operator `X` over a subspace `U`. It is the image
of `U` under `1 + X`. -/
def graphSubspace (X : E →L[𝕜] E) : Submodule 𝕜 E :=
  U.map ((1 + X : E →L[𝕜] E) : E →ₗ[𝕜] E)

@[simp]
theorem mem_graphSubspace {y : E} : y ∈ U.graphSubspace X ↔ ∃ u ∈ U, u + X u = y := by
  simp [graphSubspace]

theorem add_apply_mem_graphSubspace {u : E} (hu : u ∈ U) : u + X u ∈ U.graphSubspace X :=
  mem_graphSubspace.2 ⟨u, hu, rfl⟩

@[simp]
theorem graphSubspace_zero : U.graphSubspace 0 = U := by
  ext y
  simp

end GraphSubspace

section Angular

variable (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]

/-- An *angular operator* from `U` to `Uᗮ` is a bounded operator `X` on `E` with `X P_U = X` and
`P_U X = 0`, that is, `X` vanishes on `Uᗮ` and takes values in `Uᗮ`
(`Submodule.isAngularOperator_iff`). -/
structure IsAngularOperator (X : E →L[𝕜] E) : Prop where
  comp_starProjection : X ∘L U.starProjection = X
  starProjection_comp : U.starProjection ∘L X = 0

variable {U} {X : E →L[𝕜] E}

namespace IsAngularOperator

variable (hX : U.IsAngularOperator X)
include hX

theorem apply_starProjection (x : E) : X (U.starProjection x) = X x :=
  DFunLike.congr_fun hX.comp_starProjection x

theorem starProjection_apply_eq_zero (x : E) : U.starProjection (X x) = 0 :=
  DFunLike.congr_fun hX.starProjection_comp x

theorem apply_mem_orthogonal (x : E) : X x ∈ Uᗮ :=
  (starProjection_apply_eq_zero_iff U).mp (hX.starProjection_apply_eq_zero x)

theorem apply_eq_zero_of_mem_orthogonal {x : E} (hx : x ∈ Uᗮ) : X x = 0 := by
  rw [← hX.apply_starProjection, (starProjection_apply_eq_zero_iff U).mpr hx, map_zero]

theorem apply_apply_eq_zero (x : E) : X (X x) = 0 :=
  hX.apply_eq_zero_of_mem_orthogonal (hX.apply_mem_orthogonal x)

theorem starProjection_add_apply {u : E} (hu : u ∈ U) : U.starProjection (u + X u) = u := by
  rw [map_add, hX.starProjection_apply_eq_zero, add_zero, starProjection_eq_self_iff.mpr hu]

theorem starProjection_orthogonal_add_apply {u : E} (hu : u ∈ U) :
    Uᗮ.starProjection (u + X u) = X u := by
  rw [starProjection_orthogonal_val, hX.starProjection_add_apply hu, add_sub_cancel_left]

/-- Pythagoras on the graph subspace: `‖u + X u‖² = ‖u‖² + ‖X u‖²` for `u ∈ U`. -/
theorem norm_add_apply_sq {u : E} (hu : u ∈ U) : ‖u + X u‖ ^ 2 = ‖u‖ ^ 2 + ‖X u‖ ^ 2 := by
  rw [sq, sq, sq, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := 𝕜) _ _
    (inner_right_of_mem_orthogonal hu (hX.apply_mem_orthogonal u))]

theorem norm_le_norm_add_apply {u : E} (hu : u ∈ U) : ‖u‖ ≤ ‖u + X u‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp ?_
  rw [hX.norm_add_apply_sq hu]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- A vector lies in the graph subspace exactly when its component in `Uᗮ` is the image under `X`
of its component in `U`. -/
theorem mem_graphSubspace_iff {y : E} : y ∈ U.graphSubspace X ↔ Uᗮ.starProjection y = X y := by
  constructor
  · intro h
    obtain ⟨u, hu, rfl⟩ := mem_graphSubspace.1 h
    rw [hX.starProjection_orthogonal_add_apply hu, map_add, hX.apply_apply_eq_zero, add_zero]
  · intro h
    refine mem_graphSubspace.2 ⟨U.starProjection y, U.starProjection_apply_mem y, ?_⟩
    rw [hX.apply_starProjection, ← h, starProjection_add_starProjection_orthogonal]

/-- The graph subspace over a complete subspace is complete: `u ↦ u + X u` does not decrease
norms on `U`. -/
theorem completeSpace_graphSubspace [CompleteSpace U] : CompleteSpace (U.graphSubspace X) := by
  let f : U →L[𝕜] E := (1 + X) ∘L U.subtypeL
  have hf : AntilipschitzWith 1 f := AddMonoidHomClass.antilipschitz_of_bound f fun u => by
    simpa [f] using hX.norm_le_norm_add_apply u.2
  have hrange : Set.range f = U.graphSubspace X := by
    ext y
    simp [f, eq_comm]
  exact (hrange ▸ hf.isComplete_range f.uniformContinuous).completeSpace_coe

end IsAngularOperator

theorem isAngularOperator_iff :
    U.IsAngularOperator X ↔ (∀ x ∈ Uᗮ, X x = 0) ∧ ∀ x, X x ∈ Uᗮ := by
  refine ⟨fun hX => ⟨fun _ hx => hX.apply_eq_zero_of_mem_orthogonal hx, hX.apply_mem_orthogonal⟩,
    fun ⟨h₁, h₂⟩ => ⟨ContinuousLinearMap.ext fun x => ?_, ContinuousLinearMap.ext fun x => ?_⟩⟩
  · have h := h₁ _ (sub_starProjection_mem_orthogonal (K := U) x)
    rw [map_sub, sub_eq_zero] at h
    exact h.symm
  · exact (starProjection_apply_eq_zero_iff U).mpr (h₂ x)

variable (U) in
theorem isAngularOperator_zero : U.IsAngularOperator 0 :=
  ⟨by simp, by simp⟩

/-- Every bounded operator `Y : U → Uᗮ` defines an angular operator `x ↦ Y (P_U x)`. -/
theorem isAngularOperator_subtypeL_comp_comp_orthogonalProjectionOnto (Y : U →L[𝕜] Uᗮ) :
    U.IsAngularOperator (Uᗮ.subtypeL ∘L Y ∘L U.orthogonalProjectionOnto) := by
  rw [isAngularOperator_iff]
  exact ⟨fun x hx => by simp [orthogonalProjectionOnto_eq_zero_iff.mpr hx], fun x => (Y _).2⟩

end Angular

section Gap

variable {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] {X : E →L[𝕜] E}

namespace IsAngularOperator

variable (hX : U.IsAngularOperator X)
include hX

/-- The key estimate for a vector of the graph subspace: its `Uᗮ`-component `X u` satisfies
`‖X u‖ √(1 + ‖X‖²) ≤ ‖X‖ ‖u + X u‖`. -/
private theorem norm_apply_mul_sqrt_le {u : E} (hu : u ∈ U) :
    ‖X u‖ * √(1 + ‖X‖ ^ 2) ≤ ‖X‖ * ‖u + X u‖ := by
  refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp ?_
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), hX.norm_add_apply_sq hu]
  nlinarith [mul_self_le_mul_self (norm_nonneg _) (le_opNorm X u)]

/-- Conversely, a bound `‖X u‖ ≤ d ‖u + X u‖` on the graph subspace with `0 ≤ d < 1` forces
`‖X‖ / √(1 + ‖X‖²) ≤ d`. -/
private theorem div_sqrt_le_of_forall_norm_apply_le {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1)
    (h : ∀ u ∈ U, ‖X u‖ ≤ d * ‖u + X u‖) : ‖X‖ / √(1 + ‖X‖ ^ 2) ≤ d := by
  have hs : 0 < √(1 + ‖X‖ ^ 2) := Real.sqrt_pos.2 (by positivity)
  have ht : 0 < √(1 - d ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  -- Squaring `h` gives `‖X u‖² (1 - d²) ≤ d² ‖u‖²` on `U`, so `‖X‖ ≤ d / √(1 - d²)`.
  have hX' : ‖X‖ ≤ d / √(1 - d ^ 2) := by
    refine opNorm_le_bound _ (by positivity) fun x => ?_
    have hu : U.starProjection x ∈ U := U.starProjection_apply_mem x
    rw [← hX.apply_starProjection, div_mul_eq_mul_div, le_div_iff₀ ht]
    calc ‖X (U.starProjection x)‖ * √(1 - d ^ 2) ≤ d * ‖U.starProjection x‖ := by
          refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp ?_
          have h' := pow_le_pow_left₀ (norm_nonneg _) (h _ hu) 2
          rw [mul_pow, hX.norm_add_apply_sq hu] at h'
          rw [mul_pow, mul_pow, Real.sq_sqrt (by nlinarith)]
          nlinarith
      _ ≤ d * ‖x‖ := by
          gcongr
          exact norm_starProjection_apply_le _ _
  rw [div_le_iff₀ hs]
  rw [le_div_iff₀ ht] at hX'
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
  have h' := pow_le_pow_left₀ (by positivity) hX' 2
  rw [mul_pow, Real.sq_sqrt (by nlinarith)] at h'
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  nlinarith

/-- The directed gap from the graph subspace to `U` is `‖X‖ / √(1 + ‖X‖²)`. -/
theorem directedProjectionGap_graphSubspace_left
    [(U.graphSubspace X).HasOrthogonalProjection] :
    directedProjectionGap (U.graphSubspace X) U = ‖X‖ / √(1 + ‖X‖ ^ 2) := by
  rw [directedProjectionGap_def]
  set G := U.graphSubspace X
  have hs : 0 < √(1 + ‖X‖ ^ 2) := Real.sqrt_pos.2 (by positivity)
  -- `P_{Uᗮ} P_G` sends every `x` to the `Uᗮ`-component `X u` of `P_G x = u + X u`.
  have hle : ‖Uᗮ.starProjection ∘L G.starProjection‖ ≤ ‖X‖ / √(1 + ‖X‖ ^ 2) := by
    refine opNorm_le_bound _ (by positivity) fun x => ?_
    obtain ⟨u, hu, hux⟩ := mem_graphSubspace.1 (G.starProjection_apply_mem x)
    rw [comp_apply, ← hux, hX.starProjection_orthogonal_add_apply hu, div_mul_eq_mul_div,
      le_div_iff₀ hs]
    calc ‖X u‖ * √(1 + ‖X‖ ^ 2) ≤ ‖X‖ * ‖u + X u‖ := hX.norm_apply_mul_sqrt_le hu
      _ ≤ ‖X‖ * ‖x‖ := by
          rw [hux]
          gcongr
          exact norm_starProjection_apply_le _ _
  refine le_antisymm hle (hX.div_sqrt_le_of_forall_norm_apply_le (norm_nonneg _) ?_ fun u hu => ?_)
  · exact hle.trans_lt ((Real.tanh_arsinh _).symm.trans_lt (Real.tanh_lt_one _))
  · -- On `u + X u ∈ G`, the operator `P_{Uᗮ} P_G` returns `X u`.
    have h := le_opNorm (Uᗮ.starProjection ∘L G.starProjection) (u + X u)
    rwa [comp_apply, starProjection_eq_self_iff.mpr (add_apply_mem_graphSubspace hu),
      hX.starProjection_orthogonal_add_apply hu] at h

/-- The distance from a vector `u ∈ U` to the graph subspace is at most
`‖X‖ / √(1 + ‖X‖²) ‖u‖`, witnessed by the vector `(1 + ‖X‖²)⁻¹ (u + X u)` of the graph subspace. -/
private theorem norm_sub_starProjection_graphSubspace_mul_sqrt_le
    [(U.graphSubspace X).HasOrthogonalProjection] {u : E} (hu : u ∈ U) :
    ‖u - (U.graphSubspace X).starProjection u‖ * √(1 + ‖X‖ ^ 2) ≤ ‖X‖ * ‖u‖ := by
  set G := U.graphSubspace X
  set r := ‖X‖
  set g : E := ((1 + r ^ 2)⁻¹ : 𝕜) • (u + X u)
  have hg : g ∈ G := G.smul_mem _ (add_apply_mem_graphSubspace hu)
  -- `u - g = (1 + r²)⁻¹ (r² u - X u)`, an orthogonal combination of `u` and `X u`.
  have hug : u - g = ((1 + r ^ 2)⁻¹ : 𝕜) • ((r ^ 2 : 𝕜) • u - X u) := by
    have h1 : (1 + r ^ 2 : 𝕜) ≠ 0 := by exact_mod_cast (by positivity : (1 + r ^ 2 : ℝ) ≠ 0)
    have hc : (1 + (r : 𝕜) ^ 2)⁻¹ * (r : 𝕜) ^ 2 = 1 - (1 + (r : 𝕜) ^ 2)⁻¹ := by
      field_simp
      ring
    simp only [g, smul_sub, smul_add, smul_smul, hc, sub_smul, one_smul]
    abel
  have hpyth : ‖(r ^ 2 : 𝕜) • u - X u‖ ^ 2 = r ^ 4 * ‖u‖ ^ 2 + ‖X u‖ ^ 2 := by
    have horth : ⟪(r ^ 2 : 𝕜) • u, X u⟫_𝕜 = 0 :=
      inner_right_of_mem_orthogonal (U.smul_mem _ hu) (hX.apply_mem_orthogonal u)
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := 𝕜) ((r ^ 2 : 𝕜) • u)
      (-X u) (by rw [inner_neg_right, horth, neg_zero])
    rw [← sub_eq_add_neg, norm_neg, norm_smul, norm_pow, RCLike.norm_ofReal,
      abs_of_nonneg (norm_nonneg X)] at h
    rw [pow_two ‖(r ^ 2 : 𝕜) • u - X u‖, h]
    ring
  have hdist : ‖u - G.starProjection u‖ ≤ ‖u - g‖ := by
    rw [starProjection_minimal]
    exact ciInf_le ⟨0, Set.forall_mem_range.2 fun _ => norm_nonneg _⟩ (⟨g, hg⟩ : G)
  calc ‖u - G.starProjection u‖ * √(1 + r ^ 2) ≤ ‖u - g‖ * √(1 + r ^ 2) := by gcongr
    _ ≤ r * ‖u‖ := by
        refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp ?_
        have hpos : (0 : ℝ) < 1 + r ^ 2 := by positivity
        have hnorm : ‖(1 + r ^ 2 : 𝕜)‖ = 1 + r ^ 2 := by
          norm_cast
          exact abs_of_pos hpos
        rw [mul_pow, Real.sq_sqrt hpos.le, hug, norm_smul, mul_pow, hpyth, norm_inv, hnorm,
          inv_pow, mul_pow]
        field_simp
        nlinarith [mul_self_le_mul_self (norm_nonneg _) (le_opNorm X u)]

/-- The directed gap from `U` to its graph subspace is at most `‖X‖ / √(1 + ‖X‖²)`. -/
theorem directedProjectionGap_graphSubspace_right_le
    [(U.graphSubspace X).HasOrthogonalProjection] :
    directedProjectionGap U (U.graphSubspace X) ≤ ‖X‖ / √(1 + ‖X‖ ^ 2) := by
  rw [directedProjectionGap_def]
  refine opNorm_le_bound _ (by positivity) fun x => ?_
  rw [comp_apply, starProjection_orthogonal_val, div_mul_eq_mul_div,
    le_div_iff₀ (Real.sqrt_pos.2 (by positivity))]
  calc _ ≤ ‖X‖ * ‖U.starProjection x‖ :=
        hX.norm_sub_starProjection_graphSubspace_mul_sqrt_le (U.starProjection_apply_mem x)
    _ ≤ ‖X‖ * ‖x‖ := by
        gcongr
        exact norm_starProjection_apply_le _ _

/-- **The exact gap of a graph subspace**: `‖P_U - P_graph‖ = ‖X‖ / √(1 + ‖X‖²)`. -/
theorem projectionGap_graphSubspace [(U.graphSubspace X).HasOrthogonalProjection] :
    projectionGap U (U.graphSubspace X) = ‖X‖ / √(1 + ‖X‖ ^ 2) := by
  rw [projectionGap_eq_max, hX.directedProjectionGap_graphSubspace_left]
  exact max_eq_right hX.directedProjectionGap_graphSubspace_right_le

/-- The gap between `U` and a graph subspace over it is less than `1`. -/
theorem projectionGap_graphSubspace_lt_one [(U.graphSubspace X).HasOrthogonalProjection] :
    projectionGap U (U.graphSubspace X) < 1 := by
  rw [hX.projectionGap_graphSubspace]
  exact (Real.tanh_arsinh _).symm.trans_lt (Real.tanh_lt_one _)

end IsAngularOperator

end Gap

section Projection

variable [CompleteSpace E]

variable {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] {X : E →L[𝕜] E}

namespace IsAngularOperator

variable (hX : U.IsAngularOperator X)
include hX

/-- The adjoint of `X P_U = X`: an angular operator's adjoint takes values in `U`. -/
theorem starProjection_comp_adjoint : U.starProjection ∘L X† = X† := by
  rw [← (isSelfAdjoint_starProjection U).adjoint_eq, ← adjoint_comp, hX.comp_starProjection]

/-- The adjoint of `P_U X = 0`: an angular operator's adjoint vanishes on `U`. -/
theorem adjoint_comp_starProjection : X† ∘L U.starProjection = 0 := by
  rw [← (isSelfAdjoint_starProjection U).adjoint_eq, ← adjoint_comp, hX.starProjection_comp,
    map_zero]


/-- **The graph projection formula**: on a complete space, the orthogonal projection onto the graph
subspace is `A (1 + X†X)⁻¹ A†` with `A = P_U + X`. The operator `1 + X†X` is invertible by
`ContinuousLinearMap.IsPositive.isUnit_one_add`. -/
theorem starProjection_graphSubspace [(U.graphSubspace X).HasOrthogonalProjection] :
    (U.graphSubspace X).starProjection =
      (U.starProjection + X) ∘L Ring.inverse (1 + X† ∘L X) ∘L (U.starProjection + X)† := by
  have hP : (U.starProjection)† = U.starProjection := (isSelfAdjoint_starProjection U).adjoint_eq
  have hPP : U.starProjection ∘L U.starProjection = U.starProjection :=
    (isIdempotentElem_starProjection U).eq
  -- `A† A = P_U (1 + X† X)` for `A = P_U + X`.
  have hAA : ∀ y, adjoint (U.starProjection + X) ((U.starProjection + X) y) =
      U.starProjection ((1 + X† ∘L X) y) := fun y => by
    have h : (U.starProjection + X)† ∘L (U.starProjection + X) =
        U.starProjection ∘L (1 + X† ∘L X) := by
      simp only [map_add, hP, comp_add, add_comp, hPP, hX.adjoint_comp_starProjection,
        hX.starProjection_comp, one_def, comp_id, ← comp_assoc, hX.starProjection_comp_adjoint,
        zero_add, add_zero]
    exact DFunLike.congr_fun h y
  have hTT : ∀ y, (1 + X† ∘L X) (Ring.inverse (1 + X† ∘L X) y) = y := fun y =>
    DFunLike.congr_fun (Ring.mul_inverse_cancel _ X.isPositive_adjoint_comp_self.isUnit_one_add) y
  set A := U.starProjection + X
  set T := 1 + X† ∘L X
  ext x
  refine eq_starProjection_of_mem_of_inner_eq_zero ?_ fun w hw => ?_
  · -- `A v = P_U v + X (P_U v)` lies in the graph subspace.
    rw [comp_apply, comp_apply, add_apply, ← hX.apply_starProjection]
    exact add_apply_mem_graphSubspace (U.starProjection_apply_mem _)
  · obtain ⟨u, hu, rfl⟩ := mem_graphSubspace.1 hw
    have hAu : A u = u + X u := by
      rw [add_apply, starProjection_eq_self_iff.mpr hu]
    -- The key identity `⟪A T⁻¹ A† x, A u⟫ = ⟪x, A u⟫`, from `A† A = P_U T` and `P_U u = u`.
    have key : ⟪(A ∘L Ring.inverse T ∘L A†) x, A u⟫_𝕜 = ⟪x, A u⟫_𝕜 :=
      calc ⟪(A ∘L Ring.inverse T ∘L A†) x, A u⟫_𝕜
          = ⟪adjoint A (A (Ring.inverse T (adjoint A x))), u⟫_𝕜 := (adjoint_inner_left A u _).symm
        _ = ⟪U.starProjection (adjoint A x), u⟫_𝕜 := by rw [hAA, hTT]
        _ = ⟪adjoint A x, u⟫_𝕜 := by
          rw [inner_starProjection_left_eq_right, starProjection_eq_self_iff.mpr hu]
        _ = ⟪x, A u⟫_𝕜 := adjoint_inner_left A u x
    rw [← hAu, inner_sub_left, key, sub_self]

end IsAngularOperator

end Projection

end Submodule
