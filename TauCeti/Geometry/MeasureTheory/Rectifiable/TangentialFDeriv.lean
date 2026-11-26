/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Rectifiable.Tangent.Plane
public import TauCeti.Analysis.InnerProductSpace.NormDet
public import TauCeti.Analysis.InnerProductSpace.RangeProjection
import Mathlib.Topology.Instances.ENNReal.Lemmas
import TauCeti.Analysis.Calculus.FDeriv.Comp
import TauCeti.Analysis.Calculus.FDeriv.Remainder
import TauCeti.Analysis.Calculus.TangentCone.Haar
import TauCeti.Analysis.InnerProductSpace.Adjoint
import TauCeti.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.Geometry.Euclidean.Volume.Density
import TauCeti.LinearAlgebra.Dimension.Submodule
import TauCeti.MeasureTheory.OuterMeasure.DensityQuotient
import TauCeti.Topology.MetricSpace.Antilipschitz

/-!
# Tangential differentiation and the tangential Jacobian on rectifiable sets

At a point `x` where a set `E ⊆ V` has a unique approximate tangent `k`-plane
`P = approximateTangentPlane k E x`, a map `g : V → W` has approximate tangential derivative
`L : V →L[ℝ] W` (`HasTangentialFDerivAt k E g L x`) when `L` vanishes on `Pᗮ` and the relative
first-order error exceeds `ε * dist z x` on a subset of `E` with `k`-dimensional density zero at
`x`. Requiring `L ∘L π[k, E, x] = L` extends the derivative canonically from `P` to all of `V` by
zero on `Pᗮ`, making `L` unconditionally unique (`HasTangentialFDerivAt.unique`).

From uniqueness we define the canonical tangential derivative `tangentialFDeriv k E g x` (with
fallback `0` where none exists, commuting unconditionally with scalar multiplication and negation,
postcomposition with continuous linear maps, and addition at tangentially differentiable points)
and the `k`-dimensional tangential Jacobian `tangentialJacobian k E g x` (`normDet` of its
restriction to `P`, also defaulting to `0`). Both depend on `E` only up to `k`-density-zero
symmetric differences at `x` and on `g` only up to `k`-density-zero modifications away from `x`
(subsuming `μHE[k]`-null changes, local germs, and restrictions).

On an inverse-Lipschitz patch `f '' s ⊆ E` at a Lebesgue density-one point (without separately
assuming `Injective A`), `g` has relative Fréchet derivative `B ∘L A.gramLeftInverse` within
`f '' s` (`HasFDerivWithinAt.hasFDerivWithinAt_image_gramLeftInverse`), yielding the
parametrization chain rule for `tangentialFDeriv` and `tangentialJacobian`, while directional lower
Hausdorff density bounds `‖L‖ ≤ K`, `‖tangentialFDeriv‖ ≤ K`, and `tangentialJacobian ≤ K ^ k` for
any `LipschitzOnWith K g E` into arbitrary (possibly infinite-dimensional) targets without
assuming differentiability of `g ∘ f`.

## References

* H. Federer, *Geometric Measure Theory*, 3.2.16–3.2.19 (approximate differentials).
* L. Simon, *Lectures on Geometric Measure Theory*, §12 (tangential derivatives and Jacobians).
-/

public section

open Filter Function Metric MeasureTheory Measure Module Set
open scoped ENNReal NNReal Topology symmDiff RealInnerProductSpace
local notation "ω[" d "](" r ")" => volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) r)
local notation "𝓝₊" => 𝓝[>] (0 : ℝ)
local notation "cb" => Metric.closedBall
local notation "T[" k ", " E ", " x "]" => TauCeti.approximateTangentPlane k E x
local notation "π[" k ", " E ", " x "]" => TauCeti.approximateTangentProjection k E x

namespace TauCeti

section Defs
variable {V W W' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup W'] [NormedSpace ℝ W'] {k : ℕ}
    {E E₁ E₂ : Set V} {g g₁ g₂ : V → W} {L L₁ L₂ : V →L[ℝ] W} {x : V}

/-- `g` has approximate tangential derivative `L` along `E` at `x` in dimension `k`. -/
structure HasTangentialFDerivAt (k : ℕ) (E : Set V) (g : V → W) (L : V →L[ℝ] W) (x : V) : Prop where
  /-- `E` has a unique approximate tangent `k`-plane at `x`. -/
  existsUnique_plane : ∃! P : Submodule ℝ V, IsApproximateTangentPlane k E x P
  /-- `L` vanishes on `(approximateTangentPlane k E x)ᗮ`. -/
  comp_projection : L ∘L π[k, E, x] = L
  /-- Outside every relative-error cone, `E` has `k`-dimensional density zero at `x`. -/
  tendsto_outside_error : ∀ ε > (0 : ℝ), Tendsto (fun r =>
    μHE[k] {z ∈ E ∩ cb x r | ε * dist z x < ‖g z - g x - L (z - x)‖} / ω[k](r)) 𝓝₊ (𝓝 0)

/-- No map has a tangential derivative along the empty set. -/
@[simp] theorem not_hasTangentialFDerivAt_empty (k : ℕ) (g : V → W) (L : V →L[ℝ] W) (x : V) :
    ¬ HasTangentialFDerivAt k (∅ : Set V) g L x := fun h =>
  let ⟨P, hP, _⟩ := h.existsUnique_plane
  not_isApproximateTangentPlane_empty k x P hP

namespace HasTangentialFDerivAt

/-- `approximateTangentPlane k E x` is an approximate tangent plane from `HasTangentialFDerivAt`. -/
theorem isApproximateTangentPlane (h : HasTangentialFDerivAt k E g L x) :
    IsApproximateTangentPlane k E x (T[k, E, x]) :=
  isApproximateTangentPlane_approximateTangentPlane h.existsUnique_plane.exists

/-- Uniqueness of `approximateTangentPlane k E x` under `HasTangentialFDerivAt`. -/
theorem eq_approximateTangentPlane (h : HasTangentialFDerivAt k E g L x) {Q : Submodule ℝ V}
    (hQ : IsApproximateTangentPlane k E x Q) : Q = T[k, E, x] :=
  let ⟨_, hP, hu⟩ := h.existsUnique_plane; (hP.approximateTangentPlane_eq hu).symm ▸ hu Q hQ

/-- Two approximate tangential derivatives at `x` concentrate `E` into every cone around the
intersection of the tangent plane with `ker (L₁ - L₂)`. -/
private lemma densityZeroOutsideCones_inf_ker (h₁ : HasTangentialFDerivAt k E g L₁ x)
    (h₂ : HasTangentialFDerivAt k E g L₂ x) :
    DensityZeroOutsideCones k E x
      (T[k, E, x] ⊓ LinearMap.ker (L₁ - L₂).toLinearMap) := by
  let P := T[k, E, x]; set D := L₁ - L₂; set K₀ : Submodule ℝ V := P ⊓ LinearMap.ker D.toLinearMap
  have hD_proj : D ∘L P.starProjection = D := by
    rw [← approximateTangentProjection_eq, ContinuousLinearMap.sub_comp, h₁.comp_projection,
      h₂.comp_projection]
  obtain ⟨c, hc0, hinf_K₀⟩ := D.toLinearMap.exists_infDist_inf_ker_le P
  rw [densityZeroOutsideCones_iff]; intro ε hε
  -- Combine the tangent-plane cone condition with both first-order error cone conditions.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (by
      simpa only [add_zero] using ((densityZeroOutsideCones_iff.mp
        h₁.isApproximateTangentPlane.densityZeroOutsideCones (ε / 2) (by positivity)).add
        (h₁.tendsto_outside_error (ε / (4 * c)) (by positivity))).add
        (h₂.tendsto_outside_error (ε / (4 * c)) (by positivity)))
    (.of_forall fun _ => zero_le) (.of_forall fun r => ?_)
  rw [← ENNReal.add_div, ← ENNReal.add_div]
  refine ENNReal.div_le_div_right ((measure_mono ?_).trans ((measure_union_le _ _).trans
    (add_le_add (measure_union_le _ _) le_rfl))) _
  rintro z ⟨hzB, hzK⟩
  by_cases hP : (ε / 2) * dist z x < infDist (z - x) (P : Set V); · exact .inl (.inl ⟨hzB, hP⟩)
  by_cases h1 : (ε / (4 * c)) * dist z x < ‖g z - g x - L₁ (z - x)‖; · exact .inl (.inr ⟨hzB, h1⟩)
  refine Or.inr ⟨hzB, ?_⟩; by_contra! h2_le
  have hD_le : ‖D (z - x)‖ ≤ ‖g z - g x - L₁ (z - x)‖ + ‖g z - g x - L₂ (z - x)‖ :=
    (by simp [D] : D (z - x) = (g z - g x - L₂ (z - x)) - (g z - g x - L₁ (z - x))) ▸
      (norm_sub_le _ _).trans_eq (add_comm _ _)
  have hprod : (c : ℝ) * ((ε / (4 * c)) * dist z x) = (ε / 4) * dist z x := by field_simp
  have hc1 := (mul_le_mul_of_nonneg_left (not_lt.mp h1) c.coe_nonneg).trans_eq hprod
  have hc2 := (mul_le_mul_of_nonneg_left h2_le c.coe_nonneg).trans_eq hprod
  have hdist_z : infDist (z - x) (K₀ : Set V) ≤ infDist (z - x) (P : Set V) + c * ‖D (z - x)‖ := by
    simpa only [ContinuousLinearMap.coe_coe, ← ContinuousLinearMap.comp_apply, hD_proj] using
      hinf_K₀ (z - x)
  linarith [hdist_z.trans (add_le_add_right (mul_le_mul_of_nonneg_left hD_le c.coe_nonneg) _),
    not_lt.mp hP]

/-- Unconditional uniqueness of the approximate tangential derivative at `x`. -/
theorem unique (h₁ : HasTangentialFDerivAt k E g L₁ x) (h₂ : HasTangentialFDerivAt k E g L₂ x) :
    L₁ = L₂ := by
  by_contra hne; let P := T[k, E, x]; have hP := h₁.isApproximateTangentPlane; set D := L₁ - L₂
  have hD_proj : D ∘L P.starProjection = D := by
    rw [← approximateTangentProjection_eq, ContinuousLinearMap.sub_comp, h₁.comp_projection,
      h₂.comp_projection]
  -- If `L₁ ≠ L₂`, then `K₀ := P ⊓ ker (L₁ - L₂)` is a proper subspace of `P` with cone density 0.
  let K₀ : Submodule ℝ V := P ⊓ LinearMap.ker D.toLinearMap
  have hK₀_lt : K₀ < P := lt_of_le_of_ne inf_le_left fun h => hne <| sub_eq_zero.mp <|
    ContinuousLinearMap.ext fun v => by
      simpa only [D, ContinuousLinearMap.coe_coe, ← ContinuousLinearMap.comp_apply, hD_proj,
        zero_apply] using
        LinearMap.mem_ker.mp (h.symm ▸ P.starProjection_apply_mem v : P.starProjection v ∈ K₀).2
  have hK₀_cone := h₁.densityZeroOutsideCones_inf_ker h₂
  by_cases hP_top : P = ⊤
  · -- Full-dimension case `P = ⊤`: `K₀ < ⊤` contradicts positive upper density via shrinking slabs.
    obtain rfl : k = finrank ℝ V :=
      hP.finrank_eq.symm.trans (by dsimp only [P] at hP_top; rw [hP_top, finrank_top])
    exact not_tendsto_outside_cone_top_of_lt_top (hP_top ▸ hK₀_lt) hP.limsup_pos
      (densityZeroOutsideCones_iff.mp hK₀_cone)
  · -- Proper-subspace case `P ≠ ⊤`: enlarge `K₀` to a distinct `k`-plane `Q ≠ P`, contradicting
    -- uniqueness of the approximate tangent `k`-plane.
    obtain ⟨Q, hQ_dim, hK₀_le_Q, hQP⟩ := Submodule.exists_finrank_eq_and_le_and_ne hK₀_lt hP_top
    exact hQP (h₁.eq_approximateTangentPlane
      ⟨hQ_dim.trans hP.finrank_eq, hP.limsup_pos, hK₀_cone.mono_submodule hK₀_le_Q⟩)

/-- `HasTangentialFDerivAt` is preserved under `k`-density-zero set differences at `x`. -/
theorem of_tendsto_diff (h : HasTangentialFDerivAt k E₁ g L x)
    (h12 : Tendsto (fun r => μHE[k] ((E₁ \ E₂) ∩ cb x r) / ω[k](r)) 𝓝₊ (𝓝 0))
    (h21 : Tendsto (fun r => μHE[k] ((E₂ \ E₁) ∩ cb x r) / ω[k](r)) 𝓝₊ (𝓝 0)) :
    HasTangentialFDerivAt k E₂ g L x :=
  have hsym := tendsto_measure_symmDiff_inter_div_iff.mpr ⟨h12, h21⟩
  ⟨(existsUnique_congr fun P =>
      IsApproximateTangentPlane.congr_of_tendsto_symmDiff_div (P := P) hsym).mp
        h.existsUnique_plane,
    approximateTangentProjection_congr_of_tendsto_symmDiff_div (k := k) hsym ▸ h.comp_projection,
    fun ε hε => tendsto_measure_sep_inter_div_of_sdiff (h.tendsto_outside_error ε hε) h21⟩

/-- `HasTangentialFDerivAt` depends on `E` only up to `k`-density-zero symmetric differences. -/
theorem congr_of_tendsto_symmDiff_div
    (hsym : Tendsto (fun r => μHE[k] ((E₁ ∆ E₂) ∩ cb x r) / ω[k](r)) 𝓝₊ (𝓝 0)) :
    HasTangentialFDerivAt k E₁ g L x ↔ HasTangentialFDerivAt k E₂ g L x :=
  let ⟨h12, h21⟩ := tendsto_measure_symmDiff_inter_div_iff.mp hsym
  ⟨fun h => h.of_tendsto_diff h12 h21, fun h => h.of_tendsto_diff h21 h12⟩

/-- Null-set invariance of `HasTangentialFDerivAt` in the domain set `E`. -/
theorem congr_ae_set (h : E₁ =ᵐ[μHE[k]] E₂) :
    HasTangentialFDerivAt k E₁ g L x ↔ HasTangentialFDerivAt k E₂ g L x :=
  congr_of_tendsto_symmDiff_div
    (tendsto_measure_inter_div_of_measure_eq_zero Subset.rfl
      (measure_symmDiff_eq_zero_iff.2 h) _ _ _)

/-- Germ invariance of `HasTangentialFDerivAt` in the domain set `E`. -/
theorem congr_nhds_set (h : E₁ =ᶠ[𝓝 x] E₂) :
    HasTangentialFDerivAt k E₁ g L x ↔ HasTangentialFDerivAt k E₂ g L x :=
  congr_of_tendsto_symmDiff_div
    (tendsto_measure_symmDiff_inter_div_of_eventuallyEq h
      ((tendsto_closedBall_smallSets x).mono_left nhdsWithin_le_nhds) _)

/-- `HasTangentialFDerivAt` ignores `k`-density-zero modifications of `g` away from `x` on `E`. -/
theorem congr_of_tendsto_ne_div (hx : g₁ x = g₂ x)
    (hne : Tendsto (fun r => μHE[k] ({z ∈ E | g₁ z ≠ g₂ z} ∩ cb x r) / ω[k](r)) 𝓝₊ (𝓝 0)) :
    HasTangentialFDerivAt k E g₁ L x ↔ HasTangentialFDerivAt k E g₂ L x := by
  classical
  have aux {f₁ f₂ : V → W} (hfx : f₁ x = f₂ x)
      (hfn : Tendsto (fun r => μHE[k] ({z ∈ E | f₁ z ≠ f₂ z} ∩ cb x r) / ω[k](r)) 𝓝₊ (𝓝 0))
      (h₁ : HasTangentialFDerivAt k E f₁ L x) : HasTangentialFDerivAt k E f₂ L x :=
    ⟨h₁.existsUnique_plane, h₁.comp_projection, fun ε hε =>
      tendsto_measure_div_of_subset_union (h₁.tendsto_outside_error ε hε) hfn
        fun _ z ⟨⟨hzE, hzr⟩, hzerr⟩ =>
          if hfz : f₁ z = f₂ z then Or.inl ⟨⟨hzE, hzr⟩, by rwa [hfz, hfx]⟩
          else Or.inr ⟨⟨hzE, hfz⟩, hzr⟩⟩
  refine ⟨aux hx hne, aux hx.symm ?_⟩
  convert hne using 4 with r; ext; simp [ne_comm]

/-- Restriction invariance of `HasTangentialFDerivAt` at `x ∈ E`. -/
theorem congr_of_eqOn (hg : EqOn g₁ g₂ E) (hx : x ∈ E) :
    HasTangentialFDerivAt k E g₁ L x ↔ HasTangentialFDerivAt k E g₂ L x :=
  have hsub : {z ∈ E | g₁ z ≠ g₂ z} ⊆ ∅ := fun _ ⟨hzE, hne⟩ => hne (hg hzE)
  congr_of_tendsto_ne_div (hg hx)
    (tendsto_measure_inter_div_of_measure_eq_zero hsub measure_empty _ _ _)

/-- Almost-everywhere congruence of `HasTangentialFDerivAt` in `g` when `g₁ x = g₂ x`. -/
theorem congr_ae_fun (hg : g₁ =ᵐ[μHE[k].restrict E] g₂) (hx_eq : g₁ x = g₂ x) :
    HasTangentialFDerivAt k E g₁ L x ↔ HasTangentialFDerivAt k E g₂ L x := by
  have hsub : {z ∈ E | g₁ z ≠ g₂ z} ⊆ {z | g₁ z ≠ g₂ z} ∩ E := fun _ ⟨hzE, hne⟩ => ⟨hne, hzE⟩
  have hN : μHE[k] {z ∈ E | g₁ z ≠ g₂ z} = 0 := nonpos_iff_eq_zero.mp <|
    (measure_mono hsub).trans ((le_restrict_apply E {z | g₁ z ≠ g₂ z}).trans_eq (ae_iff.mp hg))
  exact congr_of_tendsto_ne_div hx_eq
    (tendsto_measure_inter_div_of_measure_eq_zero Subset.rfl hN _ _ _)

/-- Compatibility with `HasFDerivWithinAt` at points with a unique approximate tangent `k`-plane. -/
theorem of_hasFDerivWithinAt (hu : ∃! P : Submodule ℝ V, IsApproximateTangentPlane k E x P)
    (hg : HasFDerivWithinAt g L E x) : HasTangentialFDerivAt k E g (L ∘L π[k, E, x]) x := by
  let P := T[k, E, x]; have hP := isApproximateTangentPlane_approximateTangentPlane hu.exists
  refine ⟨hu, by ext v; simp [approximateTangentProjection_eq,
      Submodule.starProjection_eq_self_iff.2 (Submodule.starProjection_apply_mem _ _)],
    fun ε hε => ?_⟩
  obtain ⟨δ, hδ, hδb⟩ := hg.exists_ball_remainder_le (half_pos hε)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (densityZeroOutsideCones_iff.mp hP.densityZeroOutsideCones
      (ε / (2 * (‖L‖ + 1))) (by positivity))
    (.of_forall fun _ => zero_le) ?_
  filter_upwards [Ioo_mem_nhdsGT hδ] with r ⟨_, hrδ⟩
  refine ENNReal.div_le_div_right (measure_mono ?_) _
  rintro z ⟨⟨hzE, hzr⟩, hzerr⟩; refine ⟨⟨hzE, hzr⟩, ?_⟩
  have herr := hδb z (mem_ball.mpr ((mem_closedBall.mp hzr).trans_lt hrδ)) hzE
  have heq : g z - g x - (L ∘L π[k, E, x]) (z - x) =
      (g z - g x - L (z - x)) + L ((z - x) - P.starProjection (z - x)) := by
    simp only [ContinuousLinearMap.comp_apply, approximateTangentProjection_eq, map_sub]; abel
  have hnorm := (heq ▸ hzerr).trans_le ((norm_add_le _ _).trans (add_le_add herr (L.le_opNorm _)))
  rw [← dist_eq_norm (z - x), P.dist_starProjection_eq_infDist] at hnorm
  rw [dist_eq_norm] at hnorm ⊢; by_contra! hle
  have : ‖L‖ * infDist (z - x) (P : Set V) ≤ (ε / 2) * ‖z - x‖ := (mul_le_mul
    (le_add_of_nonneg_right zero_le_one) hle infDist_nonneg (by positivity)).trans_eq <| by
      field_simp
  linarith

/-- Compatibility with ambient `HasFDerivAt` at points with a unique approximate tangent
`k`-plane. -/
theorem of_hasFDerivAt (hu : ∃! P : Submodule ℝ V, IsApproximateTangentPlane k E x P)
    (hg : HasFDerivAt g L x) : HasTangentialFDerivAt k E g (L ∘L π[k, E, x]) x :=
  of_hasFDerivWithinAt hu hg.hasFDerivWithinAt

/-- Sum rule for approximate tangential derivatives. -/
theorem add (h₁ : HasTangentialFDerivAt k E g₁ L₁ x) (h₂ : HasTangentialFDerivAt k E g₂ L₂ x) :
    HasTangentialFDerivAt k E (fun z => g₁ z + g₂ z) (L₁ + L₂) x := by
  refine ⟨h₁.existsUnique_plane, by rw [ContinuousLinearMap.add_comp, h₁.comp_projection,
    h₂.comp_projection], fun ε hε => tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa only [add_zero] using (h₁.tendsto_outside_error (ε / 2) (half_pos hε)).add
            (h₂.tendsto_outside_error (ε / 2) (half_pos hε))) (.of_forall fun _ => zero_le)
      (.of_forall fun r => ?_)⟩
  rw [← ENNReal.add_div]
  refine ENNReal.div_le_div_right (le_trans (measure_mono ?_) (measure_union_le _ _)) _
  rintro z ⟨hzB, hz⟩
  by_cases h1 : (ε / 2) * dist z x < ‖g₁ z - g₁ x - L₁ (z - x)‖; · exact Or.inl ⟨hzB, h1⟩
  refine Or.inr ⟨hzB, ?_⟩
  linarith [((by simp only [add_apply]; abel : (g₁ z + g₂ z) - (g₁ x + g₂ x) - (L₁ + L₂) (z - x) =
    (g₁ z - g₁ x - L₁ (z - x)) + (g₂ z - g₂ x - L₂ (z - x))) ▸ hz).trans_le (norm_add_le _ _),
    not_lt.mp h1]

end HasTangentialFDerivAt

/-- Postcomposition with a continuous linear map commutes with `HasTangentialFDerivAt`. -/
theorem _root_.ContinuousLinearMap.comp_hasTangentialFDerivAt (C : W →L[ℝ] W')
    (h : HasTangentialFDerivAt k E g L x) : HasTangentialFDerivAt k E (C ∘ g) (C ∘L L) x where
  existsUnique_plane := h.existsUnique_plane
  comp_projection := by rw [ContinuousLinearMap.comp_assoc, h.comp_projection]
  tendsto_outside_error ε hε := by
    set M := max ‖C‖ 1
    have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    refine tendsto_measure_div_of_subset (h.tendsto_outside_error (ε / M) (by positivity))
      fun _ z ⟨hzE, hzerr⟩ => ⟨hzE, ?_⟩
    have heq : (C ∘ g) z - (C ∘ g) x - (C ∘L L) (z - x) = C (g z - g x - L (z - x)) := by
      simp [Function.comp_apply, map_sub]
    rw [heq] at hzerr
    have hle := hzerr.trans_le
      ((C.le_opNorm _).trans (mul_le_mul_of_nonneg_right (le_max_left ‖C‖ 1) (norm_nonneg _)))
    rw [div_mul_eq_mul_div, div_lt_iff₀ hM]; linarith

namespace HasTangentialFDerivAt

/-- Scalar multiplication rule for approximate tangential derivatives. -/
theorem const_smul (c : ℝ) (h : HasTangentialFDerivAt k E g L x) :
    HasTangentialFDerivAt k E (fun z => c • g z) (c • L) x := by
  simpa [Function.comp_def] using
    ContinuousLinearMap.comp_hasTangentialFDerivAt (c • ContinuousLinearMap.id ℝ W) h

/-- Negation rule for approximate tangential derivatives. -/
theorem neg (h : HasTangentialFDerivAt k E g L x) :
    HasTangentialFDerivAt k E (fun z => -g z) (-L) x := by simpa using h.const_smul (-1)

/-- Subtraction rule for approximate tangential derivatives. -/
theorem sub (h₁ : HasTangentialFDerivAt k E g₁ L₁ x) (h₂ : HasTangentialFDerivAt k E g₂ L₂ x) :
    HasTangentialFDerivAt k E (fun z => g₁ z - g₂ z) (L₁ - L₂) x := by
  simpa [sub_eq_add_neg] using h₁.add h₂.neg

end HasTangentialFDerivAt

/-- Constant functions have zero tangential derivative at points with a unique approximate tangent
`k`-plane. -/
theorem hasTangentialFDerivAt_const (c : W)
    (hu : ∃! P : Submodule ℝ V, IsApproximateTangentPlane k E x P) :
    HasTangentialFDerivAt k E (fun _ => c) 0 x := by
  simpa using HasTangentialFDerivAt.of_hasFDerivWithinAt hu (hasFDerivWithinAt_const c x E)

/-- The identity map has tangential derivative `approximateTangentProjection k E x` at points with
a unique approximate tangent `k`-plane. -/
theorem hasTangentialFDerivAt_id
    (hu : ∃! P : Submodule ℝ V, IsApproximateTangentPlane k E x P) :
    HasTangentialFDerivAt k E (id : V → V) π[k, E, x] x := by
  simpa using HasTangentialFDerivAt.of_hasFDerivWithinAt hu (hasFDerivWithinAt_id x E)

open Classical in
/-- Canonical approximate tangential derivative of `g` along `E` at `x` (`0` if none exists). -/
noncomputable def tangentialFDeriv (k : ℕ) (E : Set V) (g : V → W) (x : V) : V →L[ℝ] W :=
  if h : ∃ L : V →L[ℝ] W, HasTangentialFDerivAt k E g L x then h.choose else 0

local notation "TFD[" k ", " E ", " g ", " x "]" => TauCeti.tangentialFDeriv k E g x

/-- `HasTangentialFDerivAt k E g L x` identifies `tangentialFDeriv k E g x = L`. -/
theorem HasTangentialFDerivAt.tangentialFDeriv_eq (h : HasTangentialFDerivAt k E g L x) :
    TFD[k, E, g, x] = L := by
  have hex : ∃ L', HasTangentialFDerivAt k E g L' x := ⟨L, h⟩
  simp only [tangentialFDeriv, hex, ↓reduceDIte]; exact hex.choose_spec.unique h

/-- Specification of `tangentialFDeriv k E g x` when `g` is tangentially differentiable at `x`. -/
theorem hasTangentialFDerivAt_tangentialFDeriv
    (h : ∃ L : V →L[ℝ] W, HasTangentialFDerivAt k E g L x) :
    HasTangentialFDerivAt k E g TFD[k, E, g, x] x := by
  simp only [tangentialFDeriv, h, ↓reduceDIte]; exact h.choose_spec

/-- If `g` has no approximate tangential derivative along `E` at `x`, then
`tangentialFDeriv k E g x = 0`. -/
@[simp] theorem tangentialFDeriv_eq_zero_of_not_exists
    (h : ¬ ∃ L : V →L[ℝ] W, HasTangentialFDerivAt k E g L x) : TFD[k, E, g, x] = 0 := by
  simp [tangentialFDeriv, h]

/-- Along the empty set, `tangentialFDeriv` vanishes. -/
theorem tangentialFDeriv_empty (k : ℕ) (g : V → W) (x : V) :
    TFD[k, (∅ : Set V), g, x] = 0 := by simp

/-- Constant maps have zero `tangentialFDeriv` unconditionally. -/
@[simp] theorem tangentialFDeriv_const (k : ℕ) (E : Set V) (c : W) (x : V) :
    TFD[k, E, (fun _ => c), x] = 0 := by
  by_cases hu : ∃! P : Submodule ℝ V, IsApproximateTangentPlane k E x P
  · exact (hasTangentialFDerivAt_const c hu).tangentialFDeriv_eq
  · exact tangentialFDeriv_eq_zero_of_not_exists fun ⟨_, h⟩ => hu h.existsUnique_plane

/-- At points with a unique approximate tangent `k`-plane, `tangentialFDeriv` of `id` is
`approximateTangentProjection`. -/
theorem tangentialFDeriv_id (hu : ∃! P : Submodule ℝ V, IsApproximateTangentPlane k E x P) :
    TFD[k, E, (id : V → V), x] = π[k, E, x] :=
  (hasTangentialFDerivAt_id hu).tangentialFDeriv_eq

/-- Postcomposing a tangentially differentiable map with `C : W →L[ℝ] W'` postcomposes
`tangentialFDeriv`. -/
theorem _root_.ContinuousLinearMap.comp_tangentialFDeriv (C : W →L[ℝ] W')
    (h : ∃ L : V →L[ℝ] W, HasTangentialFDerivAt k E g L x) :
    TFD[k, E, C ∘ g, x] = C ∘L TFD[k, E, g, x] :=
  (ContinuousLinearMap.comp_hasTangentialFDerivAt C
    (hasTangentialFDerivAt_tangentialFDeriv h)).tangentialFDeriv_eq

/-- `tangentialFDeriv k E g x` vanishes on `(T[k, E, x])ᗮ`. -/
@[simp] theorem tangentialFDeriv_comp_approximateTangentProjection (k : ℕ) (E : Set V) (g : V → W)
    (x : V) : TFD[k, E, g, x] ∘L π[k, E, x] = TFD[k, E, g, x] := by
  by_cases h : ∃ L : V →L[ℝ] W, HasTangentialFDerivAt k E g L x
  exacts [(hasTangentialFDerivAt_tangentialFDeriv h).comp_projection, by simp [h]]

/-- In dimension zero, `tangentialFDeriv 0 E g x = 0`. -/
@[simp] theorem tangentialFDeriv_zero (E : Set V) (g : V → W) (x : V) : TFD[0, E, g, x] = 0 := by
  rw [← tangentialFDeriv_comp_approximateTangentProjection 0 E g x,
    approximateTangentProjection_zero, ContinuousLinearMap.comp_zero]

/-- Sum rule for `tangentialFDeriv` when both functions are tangentially differentiable at `x`. -/
theorem tangentialFDeriv_add (h₁ : ∃ L, HasTangentialFDerivAt k E g₁ L x)
    (h₂ : ∃ L, HasTangentialFDerivAt k E g₂ L x) :
    TFD[k, E, g₁ + g₂, x] = TFD[k, E, g₁, x] + TFD[k, E, g₂, x] :=
  ((hasTangentialFDerivAt_tangentialFDeriv h₁).add
    (hasTangentialFDerivAt_tangentialFDeriv h₂)).tangentialFDeriv_eq

/-- Scalar multiplication rule for `tangentialFDeriv`. Because `ℝ` is a field and `tangentialFDeriv`
defaults to `0`, no differentiability hypothesis is needed. -/
@[simp]
theorem tangentialFDeriv_const_smul (c : ℝ) (g : V → W) (x : V) :
    TFD[k, E, c • g, x] = c • TFD[k, E, g, x] := by
  obtain rfl | hc := eq_or_ne c 0
  · rw [zero_smul, zero_smul]; exact tangentialFDeriv_const k E 0 x
  · by_cases h : ∃ L : V →L[ℝ] W, HasTangentialFDerivAt k E g L x
    · exact ((hasTangentialFDerivAt_tangentialFDeriv h).const_smul c).tangentialFDeriv_eq
    · rw [tangentialFDeriv_eq_zero_of_not_exists h, smul_zero]
      exact tangentialFDeriv_eq_zero_of_not_exists fun ⟨L, hL⟩ =>
        h ⟨c⁻¹ • L, by simpa [inv_smul_smul₀ hc] using hL.const_smul c⁻¹⟩

/-- Negation rule for `tangentialFDeriv`, holding unconditionally without differentiability
hypotheses. -/
@[simp]
theorem tangentialFDeriv_neg (g : V → W) (x : V) :
    TFD[k, E, -g, x] = -TFD[k, E, g, x] := by
  simpa only [neg_one_smul] using tangentialFDeriv_const_smul (-1 : ℝ) g x

/-- Subtraction rule for `tangentialFDeriv` when both functions are tangentially differentiable
at `x`. -/
theorem tangentialFDeriv_sub (h₁ : ∃ L, HasTangentialFDerivAt k E g₁ L x)
    (h₂ : ∃ L, HasTangentialFDerivAt k E g₂ L x) :
    TFD[k, E, g₁ - g₂, x] = TFD[k, E, g₁, x] - TFD[k, E, g₂, x] :=
  ((hasTangentialFDerivAt_tangentialFDeriv h₁).sub
    (hasTangentialFDerivAt_tangentialFDeriv h₂)).tangentialFDeriv_eq

private lemma tangentialFDeriv_eq_of_iff {E₁ E₂ : Set V} {g₁ g₂ : V → W} {x : V}
    (hiff : ∀ L, HasTangentialFDerivAt k E₁ g₁ L x ↔ HasTangentialFDerivAt k E₂ g₂ L x) :
    TFD[k, E₁, g₁, x] = TFD[k, E₂, g₂, x] := by
  unfold tangentialFDeriv
  rw [funext fun L => propext (hiff L)]

/-- Symmetric-difference `k`-density-zero invariance of `tangentialFDeriv` in `E`. -/
theorem tangentialFDeriv_congr_of_tendsto_symmDiff_div
    (hsym : Tendsto (fun r => μHE[k] ((E₁ ∆ E₂) ∩ cb x r) / ω[k](r)) 𝓝₊ (𝓝 0)) (g : V → W) :
    TFD[k, E₁, g, x] = TFD[k, E₂, g, x] :=
  tangentialFDeriv_eq_of_iff fun _ => HasTangentialFDerivAt.congr_of_tendsto_symmDiff_div hsym

/-- Null-set invariance of `tangentialFDeriv` in `E`. -/
theorem tangentialFDeriv_congr_ae_set (h : E₁ =ᵐ[μHE[k]] E₂) (g : V → W) (x : V) :
    TFD[k, E₁, g, x] = TFD[k, E₂, g, x] :=
  tangentialFDeriv_eq_of_iff fun _ => HasTangentialFDerivAt.congr_ae_set h

/-- Germ invariance of `tangentialFDeriv` in `E`. -/
theorem tangentialFDeriv_congr_nhds_set (h : E₁ =ᶠ[𝓝 x] E₂) (g : V → W) :
    TFD[k, E₁, g, x] = TFD[k, E₂, g, x] :=
  tangentialFDeriv_eq_of_iff fun _ => HasTangentialFDerivAt.congr_nhds_set h

/-- `tangentialFDeriv` ignores `k`-density-zero modifications of `g` away from `x` on `E`. -/
theorem tangentialFDeriv_congr_of_tendsto_ne_div (hx : g₁ x = g₂ x)
    (hne : Tendsto (fun r => μHE[k] ({z ∈ E | g₁ z ≠ g₂ z} ∩ cb x r) / ω[k](r)) 𝓝₊ (𝓝 0)) :
    TFD[k, E, g₁, x] = TFD[k, E, g₂, x] :=
  tangentialFDeriv_eq_of_iff fun _ => HasTangentialFDerivAt.congr_of_tendsto_ne_div hx hne

/-- Restriction invariance of `tangentialFDeriv` at `x ∈ E`. -/
theorem tangentialFDeriv_congr_of_eqOn (hg : EqOn g₁ g₂ E) (hx : x ∈ E) :
    TFD[k, E, g₁, x] = TFD[k, E, g₂, x] :=
  tangentialFDeriv_eq_of_iff fun _ => HasTangentialFDerivAt.congr_of_eqOn hg hx

/-- Almost-everywhere congruence of `tangentialFDeriv` in `g`. -/
theorem tangentialFDeriv_congr_ae_fun (hg : g₁ =ᵐ[μHE[k].restrict E] g₂) :
    tangentialFDeriv k E g₁ =ᵐ[μHE[k].restrict E] tangentialFDeriv k E g₂ :=
  hg.mono fun _ hx => tangentialFDeriv_eq_of_iff fun _ => HasTangentialFDerivAt.congr_ae_fun hg hx

end Defs

section Jacobian
local notation "TFD[" k ", " E ", " g ", " x "]" => TauCeti.tangentialFDeriv k E g x
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup W] [InnerProductSpace ℝ W] {k : ℕ}
    {E E₁ E₂ : Set V} {g g₁ g₂ : V → W} {L : V →L[ℝ] W} {x : V}

open Classical in
/-- The `k`-dimensional tangential Jacobian of `g` along `E` at `x` (`0` if not differentiable). -/
noncomputable def tangentialJacobian (k : ℕ) (E : Set V) (g : V → W) (x : V) : ℝ :=
  if ∃ L : V →L[ℝ] W, HasTangentialFDerivAt k E g L x then
    ((tangentialFDeriv k E g x).toLinearMap.domRestrict (T[k, E, x])).normDet
  else 0

local notation "TJ[" k ", " E ", " g ", " x "]" => TauCeti.tangentialJacobian k E g x

/-- Nonnegativity of `tangentialJacobian`. -/
theorem tangentialJacobian_nonneg (k : ℕ) (E : Set V) (g : V → W) (x : V) : 0 ≤ TJ[k, E, g, x] := by
  unfold tangentialJacobian; split_ifs <;> [exact LinearMap.normDet_nonneg _; exact le_rfl]

/-- Explicit formula for `tangentialJacobian` when `HasTangentialFDerivAt k E g L x` holds. -/
theorem HasTangentialFDerivAt.tangentialJacobian_eq (h : HasTangentialFDerivAt k E g L x) :
    TJ[k, E, g, x] = (L.toLinearMap.domRestrict (T[k, E, x])).normDet := by
  have hL : ∃ L', HasTangentialFDerivAt k E g L' x := ⟨L, h⟩
  simp [tangentialJacobian, hL, h.tangentialFDeriv_eq]

/-- If `g` has no approximate tangential derivative along `E` at `x`, then
`tangentialJacobian k E g x = 0`. -/
@[simp] theorem tangentialJacobian_eq_zero_of_not_exists
    (h : ¬ ∃ L : V →L[ℝ] W, HasTangentialFDerivAt k E g L x) : TJ[k, E, g, x] = 0 := by
  simp [tangentialJacobian, h]

/-- Along the empty set, `tangentialJacobian` vanishes. -/
theorem tangentialJacobian_empty (k : ℕ) (g : V → W) (x : V) :
    TJ[k, (∅ : Set V), g, x] = 0 := by simp

/-- Bound `tangentialJacobian k E g x ≤ ‖L‖ ^ k` under `HasTangentialFDerivAt k E g L x`. -/
theorem HasTangentialFDerivAt.tangentialJacobian_le_opNorm_pow
    (h : HasTangentialFDerivAt k E g L x) : TJ[k, E, g, x] ≤ ‖L‖ ^ k := by
  let P := T[k, E, x]; rw [h.tangentialJacobian_eq]
  conv_rhs => rw [← h.isApproximateTangentPlane.finrank_eq]
  have heq : L.toLinearMap.domRestrict P = (L.comp P.subtypeL).toLinearMap := by ext y; rfl
  rw [heq]; exact (L.comp P.subtypeL).normDet_le_norm_pow.trans <| pow_le_pow_left₀ (norm_nonneg _)
    ((L.opNorm_comp_le P.subtypeL).trans (mul_le_of_le_one_right (norm_nonneg L)
      (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun _ => by simp))) _

/-- Unconditional bound `tangentialJacobian k E g x ≤ ‖tangentialFDeriv k E g x‖ ^ k` at every
point `x : V`. -/
theorem tangentialJacobian_le_norm_tangentialFDeriv_pow
    (k : ℕ) (E : Set V) (g : V → W) (x : V) : TJ[k, E, g, x] ≤ ‖TFD[k, E, g, x]‖ ^ k := by
  by_cases h : ∃ L : V →L[ℝ] W, HasTangentialFDerivAt k E g L x
  · exact (hasTangentialFDerivAt_tangentialFDeriv h).tangentialJacobian_le_opNorm_pow
  · rw [tangentialJacobian_eq_zero_of_not_exists h]; exact pow_nonneg (norm_nonneg _) k

/-- Rank-deficient tangential derivatives have zero `k`-dimensional tangential Jacobian. -/
theorem tangentialJacobian_eq_zero_of_finrank_range_lt
    (hrank : finrank ℝ (LinearMap.range (TFD[k, E, g, x]).toLinearMap) < k) :
    TJ[k, E, g, x] = 0 := by
  by_cases h : ∃ L : V →L[ℝ] W, HasTangentialFDerivAt k E g L x; swap; · simp [h]
  have ht := hasTangentialFDerivAt_tangentialFDeriv h
  rw [ht.tangentialJacobian_eq, LinearMap.normDet_eq_zero_iff_rank_range_ne,
    ht.isApproximateTangentPlane.finrank_eq]
  exact ((Submodule.finrank_mono (by rintro _ ⟨v, hv⟩; exact ⟨v.val, hv⟩)).trans_lt hrank).ne

open Classical in
private lemma tangentialJacobian_eq_of_iff {E₁ E₂ : Set V} {g₁ g₂ : V → W} {x : V}
    (hiff : ∀ L, HasTangentialFDerivAt k E₁ g₁ L x ↔ HasTangentialFDerivAt k E₂ g₂ L x)
    (hP : T[k, E₁, x] = T[k, E₂, x]) : TJ[k, E₁, g₁, x] = TJ[k, E₂, g₂, x] := by
  rw [tangentialJacobian, tangentialJacobian, tangentialFDeriv_eq_of_iff hiff]
  exact if_congr (exists_congr hiff) (congrArg (fun S : Submodule ℝ V =>
    ((TFD[k, E₂, g₂, x]).toLinearMap.domRestrict S).normDet) hP) rfl

/-- Symmetric-difference `k`-density-zero invariance of `tangentialJacobian` in `E`. -/
theorem tangentialJacobian_congr_of_tendsto_symmDiff_div
    (hsym : Tendsto (fun r => μHE[k] ((E₁ ∆ E₂) ∩ cb x r) / ω[k](r)) 𝓝₊ (𝓝 0)) (g : V → W) :
    TJ[k, E₁, g, x] = TJ[k, E₂, g, x] :=
  tangentialJacobian_eq_of_iff
    (fun _ => HasTangentialFDerivAt.congr_of_tendsto_symmDiff_div hsym)
    (approximateTangentPlane_congr_of_tendsto_symmDiff_div hsym)

/-- Null-set invariance of `tangentialJacobian` in `E`. -/
theorem tangentialJacobian_congr_ae_set (h : E₁ =ᵐ[μHE[k]] E₂) (g : V → W) (x : V) :
    TJ[k, E₁, g, x] = TJ[k, E₂, g, x] :=
  tangentialJacobian_eq_of_iff (fun _ => HasTangentialFDerivAt.congr_ae_set h)
    (approximateTangentPlane_congr_ae h x)

/-- Germ invariance of `tangentialJacobian` in `E`. -/
theorem tangentialJacobian_congr_nhds_set (h : E₁ =ᶠ[𝓝 x] E₂) (g : V → W) :
    TJ[k, E₁, g, x] = TJ[k, E₂, g, x] :=
  tangentialJacobian_eq_of_iff (fun _ => HasTangentialFDerivAt.congr_nhds_set h)
    (approximateTangentPlane_congr_nhds h)

/-- `tangentialJacobian` ignores `k`-density-zero modifications of `g` away from `x` on `E`. -/
theorem tangentialJacobian_congr_of_tendsto_ne_div (hx : g₁ x = g₂ x)
    (hne : Tendsto (fun r => μHE[k] ({z ∈ E | g₁ z ≠ g₂ z} ∩ cb x r) / ω[k](r)) 𝓝₊ (𝓝 0)) :
    TJ[k, E, g₁, x] = TJ[k, E, g₂, x] :=
  tangentialJacobian_eq_of_iff
    (fun _ => HasTangentialFDerivAt.congr_of_tendsto_ne_div hx hne) rfl

/-- Restriction invariance of `tangentialJacobian` at `x ∈ E`. -/
theorem tangentialJacobian_congr_of_eqOn (hg : EqOn g₁ g₂ E) (hx : x ∈ E) :
    TJ[k, E, g₁, x] = TJ[k, E, g₂, x] :=
  tangentialJacobian_eq_of_iff (fun _ => HasTangentialFDerivAt.congr_of_eqOn hg hx) rfl

/-- Almost-everywhere congruence of `tangentialJacobian` in `g`. -/
theorem tangentialJacobian_congr_ae_fun (hg : g₁ =ᵐ[μHE[k].restrict E] g₂) :
    tangentialJacobian k E g₁ =ᵐ[μHE[k].restrict E] tangentialJacobian k E g₂ :=
  hg.mono fun _ hx => tangentialJacobian_eq_of_iff
    (fun _ => HasTangentialFDerivAt.congr_ae_fun hg hx) rfl

end Jacobian
end TauCeti

local notation "TFD[" k ", " E ", " g ", " x "]" => TauCeti.tangentialFDeriv k E g x
local notation "TJ[" k ", " E ", " g ", " x "]" => TauCeti.tangentialJacobian k E g x

namespace HasFDerivWithinAt
open TauCeti
variable {U V W : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    [MeasurableSpace U] [BorelSpace U] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {f : U → V} {s : Set U} {A : U →L[ℝ] V} {u₀ : U} {L_f : ℝ≥0} {E : Set V}
    (hf : HasFDerivWithinAt f A s u₀) (hi : AntilipschitzWith L_f (s.domRestrict f)) (hu₀ : u₀ ∈ s)

section PatchOnly
variable [NormedAddCommGroup W] [NormedSpace ℝ W] {g : V → W} {B : U →L[ℝ] W}
include hf hi hu₀

omit [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] in
/-- On an inverse-Lipschitz patch `f '' s` at a Lebesgue density-one point `u₀ ∈ s`,
differentiability of `g ∘ f` within `s` pushes forward to genuine relative Fréchet
differentiability `HasFDerivWithinAt g (B ∘L A.gramLeftInverse) (f '' s) (f u₀)`. -/
theorem hasFDerivWithinAt_image_gramLeftInverse [CompleteSpace V]
    (hdens : Tendsto (fun r => volume (s ∩ cb u₀ r) / volume (cb (0 : U) r)) 𝓝₊ (𝓝 1))
    (hgf : HasFDerivWithinAt (g ∘ f) B s u₀) :
    HasFDerivWithinAt g (B ∘L A.gramLeftInverse) (f '' s) (f u₀) := by
  have hinj : Injective A := hf.injective_of_tendsto_inter_closedBall_div_zero volume hu₀ hi hdens
  have hU := (ContinuousLinearMap.isUnit_adjoint_comp_self_iff A).2 hinj
  exact hf.of_comp_antilipschitzWith hu₀ hi hgf fun u => by
    rw [ContinuousLinearMap.comp_apply, A.gramLeftInverse_apply_apply hU]

end PatchOnly

variable (hsub : f '' s ⊆ E)
  (hdens : Tendsto (fun r => volume (s ∩ cb u₀ r) / volume (cb (0 : U) r)) 𝓝₊ (𝓝 1))
  (hdiff : Tendsto (fun r => μHE[finrank ℝ U] ((E \ f '' s) ∩ cb (f u₀) r) /
    ω[finrank ℝ U](r)) 𝓝₊ (𝓝 0))
include hf hi hu₀ hsub hdens hdiff

section NormedTarget
variable [NormedAddCommGroup W] [NormedSpace ℝ W] {g : V → W} {B : U →L[ℝ] W} {K : ℝ≥0}

/-- Parametrization chain rule for `HasTangentialFDerivAt` on an inverse-Lipschitz patch, without
separately assuming `Injective A`. -/
theorem hasTangentialFDerivAt_of_comp (hgf : HasFDerivWithinAt (g ∘ f) B s u₀) :
    HasTangentialFDerivAt (finrank ℝ U) E g (B ∘L A.gramLeftInverse) (f u₀) := by
  have hinj : Injective A := hf.injective_of_tendsto_inter_closedBall_div_zero volume hu₀ hi hdens
  have hU := (ContinuousLinearMap.isUnit_adjoint_comp_self_iff A).2 hinj
  have himg_iff (Q) := hf.isApproximateTangentPlane_image_iff hi hu₀ hdens (Q := Q)
  have hproj :
      (B ∘L A.gramLeftInverse) ∘L π[finrank ℝ U, f '' s, f u₀] = B ∘L A.gramLeftInverse := by
    rw [approximateTangentProjection_eq, hf.approximateTangentPlane_image_eq_range hi hu₀ hdens,
      ContinuousLinearMap.starProjection_range_eq hU, ContinuousLinearMap.comp_assoc,
      ← ContinuousLinearMap.comp_assoc A.gramLeftInverse, A.gramLeftInverse_comp_self hU,
      ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]
  have himg := HasTangentialFDerivAt.of_hasFDerivWithinAt
    ⟨_, (himg_iff _).mpr rfl, fun Q hQ => (himg_iff Q).mp hQ⟩
    (hf.hasFDerivWithinAt_image_gramLeftInverse hi hu₀ hdens hgf)
  rw [hproj] at himg
  exact himg.of_tendsto_diff (by simp [sdiff_eq_empty.2 hsub]) hdiff

/-- Composing `tangentialFDeriv` at `f u₀` with `A` recovers the parameter derivative `B`. -/
theorem tangentialFDeriv_comp_eq (hgf : HasFDerivWithinAt (g ∘ f) B s u₀) :
    TFD[(finrank ℝ U), E, g, (f u₀)] ∘L A = B := by
  have hinj : Injective A := hf.injective_of_tendsto_inter_closedBall_div_zero volume hu₀ hi hdens
  rw [(hf.hasTangentialFDerivAt_of_comp hi hu₀ hsub hdens hdiff hgf).tangentialFDeriv_eq,
    ContinuousLinearMap.comp_assoc,
    A.gramLeftInverse_comp_self ((ContinuousLinearMap.isUnit_adjoint_comp_self_iff A).2 hinj),
    ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id]

omit hdiff in
private theorem norm_apply_le_of_hasTangentialFDerivAt {L : V →L[ℝ] W}
    (hg : LipschitzOnWith K g E)
    (hL : HasTangentialFDerivAt (finrank ℝ U) E g L (f u₀)) {u : U} (hu : ‖A u‖ = 1 / 2) :
    ‖L (A u)‖ ≤ (K : ℝ) / 2 := by
  refine le_of_forall_pos_lt_add fun δ hδ => ?_
  set M : ℝ := (K : ℝ) + ‖L‖ + 1
  have hM : 0 < M := by positivity
  set η : ℝ := δ / (3 * M)
  -- Pick `z ∈ E ∩ cb (f u₀) r` in the directional cone around `A u` outside the tangential-error
  -- exceptional set (positive lower density vs. zero density).
  have hlow := hf.liminf_euclideanHausdorffMeasure_directional_closedBall_pos hi hdens hsub
    (by linarith : ‖A u‖ < 1) (show 0 < η by positivity)
  have herr := (hL.tendsto_outside_error (δ / 3) (by positivity)).liminf_eq
  obtain ⟨r, hr, z, ⟨hzE, hzr⟩, hzd, hzerr⟩ : ∃ r > (0 : ℝ), ∃ z ∈ E ∩ cb (f u₀) r,
      ‖z - f u₀ - r • A u‖ ≤ r * η ∧
      ‖g z - g (f u₀) - L (z - f u₀)‖ ≤ (δ / 3) * dist z (f u₀) := by
    by_contra hall; refine hlow.ne' (le_antisymm ?_ zero_le)
    rw [← herr]; refine liminf_le_liminf ?_
    filter_upwards [self_mem_nhdsWithin] with r (_ : 0 < r)
    refine ENNReal.div_le_div_right (measure_mono ?_) _; rintro z ⟨hzE, hzd⟩
    exact ⟨hzE, not_le.1 fun hle => hall ⟨r, ‹_›, z, hzE, hzd, hle⟩⟩
  -- Bound `r * ‖L (A u)‖` via the Lipschitz increment, tangential remainder, and directional step.
  have hdist_le : dist z (f u₀) ≤ r * (1 / 2 + η) := by
    rw [dist_eq_norm, show z - f u₀ = (z - f u₀ - r • A u) + r • A u by abel]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hu]; linarith
  have hLip : ‖g z - g (f u₀)‖ ≤ (K : ℝ) * (r * (1 / 2 + η)) := by
    rw [← dist_eq_norm]
    exact (hg.dist_le_mul z hzE (f u₀) (hsub (mem_image_of_mem f hu₀))).trans
      (mul_le_mul_of_nonneg_left hdist_le K.coe_nonneg)
  have hLstep : ‖L (z - f u₀ - r • A u)‖ ≤ ‖L‖ * (r * η) :=
    (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left hzd (norm_nonneg L))
  have heq : r • L (A u) =
      (g z - g (f u₀)) - (g z - g (f u₀) - L (z - f u₀)) - L (z - f u₀ - r • A u) := by
    rw [sub_sub_cancel, ← map_sub L, sub_sub_cancel, map_smul L r]
  have htri : r * ‖L (A u)‖ ≤ ‖g z - g (f u₀)‖ + ‖g z - g (f u₀) - L (z - f u₀)‖ +
      ‖L (z - f u₀ - r • A u)‖ :=
    calc r * ‖L (A u)‖ = ‖r • L (A u)‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      _ ≤ _ := by rw [heq]; exact (norm_sub_le _ _).trans (by gcongr; exact norm_sub_le _ _)
  -- Cancel `r > 0` after absorbing the `η` and remainder terms into `δ`.
  have hKL_η : ((K : ℝ) + ‖L‖) * η < δ / 3 :=
    (mul_lt_mul_of_pos_right (show (K : ℝ) + ‖L‖ < M by simp [M]) (by positivity)).trans_eq
      (by simp only [η]; field_simp)
  have hzr' : ‖g z - g (f u₀) - L (z - f u₀)‖ ≤ (δ / 3) * r :=
    hzerr.trans (mul_le_mul_of_nonneg_left (mem_closedBall.1 hzr) (by positivity))
  refine lt_of_mul_lt_mul_left ?_ hr.le
  calc r * ‖L (A u)‖
      ≤ (K : ℝ) * (r * (1 / 2 + η)) + (δ / 3) * r + ‖L‖ * (r * η) :=
        htri.trans (add_le_add (add_le_add hLip hzr') hLstep)
    _ = r * ((K : ℝ) / 2 + (((K : ℝ) + ‖L‖) * η + δ / 3)) := by ring
    _ < r * ((K : ℝ) / 2 + (δ / 3 + δ / 3)) := by gcongr
    _ < r * ((K : ℝ) / 2 + δ) := mul_lt_mul_of_pos_left (by linarith) hr

omit hdiff in
/-- Sharp operator-norm bound `‖L‖ ≤ K` for any approximate tangential derivative of a
`K`-Lipschitz map along an inverse-Lipschitz patch, without requiring differentiability of `g ∘ f`
or finite-dimensionality of `W`. -/
theorem opNorm_le_of_hasTangentialFDerivAt {L : V →L[ℝ] W}
    (hg : LipschitzOnWith K g E)
    (hL : HasTangentialFDerivAt (finrank ℝ U) E g L (f u₀)) : ‖L‖ ≤ K := by
  have hinj : Injective A := hf.injective_of_tendsto_inter_closedBall_div_zero volume hu₀ hi hdens
  set P := T[(finrank ℝ U), E, (f u₀)] with hP_def
  have hPeq : P = LinearMap.range A.toLinearMap :=
    hf.eq_range_of_densityZeroOutsideCones hinj hi hsub hdens
      hL.isApproximateTangentPlane.finrank_eq.le
      hL.isApproximateTangentPlane.densityZeroOutsideCones
  refine L.opNorm_le_bound K.coe_nonneg fun z => ?_
  -- Project `z` onto `P = range A`, where `L z = L p` by `L ∘L π = L`.
  set p : V := P.starProjection z with hp_def
  have hLp : L p = L z := by
    rw [hp_def, hP_def, ← approximateTangentProjection_eq, ← ContinuousLinearMap.comp_apply,
      hL.comp_projection]
  rw [← hLp]
  by_cases hp : p = 0; · rw [hp, map_zero, norm_zero]; positivity
  -- Rescale a preimage `u` of `p` to `w` with `‖A w‖ = 1 / 2`, then apply the directional bound.
  have : 0 < ‖p‖ := norm_pos_iff.2 hp
  obtain ⟨u, hu⟩ : p ∈ LinearMap.range A.toLinearMap := hPeq ▸ P.starProjection_apply_mem z
  set w : U := (2 * ‖p‖)⁻¹ • u
  have hAw : A w = (2 * ‖p‖)⁻¹ • p := by rw [ContinuousLinearMap.coe_coe] at hu; simp [w, hu]
  have hAw_norm : ‖A w‖ = 1 / 2 := by
    rw [hAw, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]; field_simp
  have hhalf := hf.norm_apply_le_of_hasTangentialFDerivAt hi hu₀ hsub hdens hg hL hAw_norm
  rw [hAw, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)] at hhalf
  have hmul := mul_le_mul_of_nonneg_right hhalf (show 0 ≤ 2 * ‖p‖ by positivity)
  have h1 : (2 * ‖p‖)⁻¹ * ‖L p‖ * (2 * ‖p‖) = ‖L p‖ := by field_simp
  have hLp_le : ‖L p‖ ≤ K * ‖p‖ := by linarith
  exact hLp_le.trans (mul_le_mul_of_nonneg_left (P.norm_starProjection_apply_le z) K.coe_nonneg)

omit hdiff in
/-- Sharp bound `‖tangentialFDeriv (finrank ℝ U) E g (f u₀)‖ ≤ K` on a patch, without requiring
differentiability of `g ∘ f` or finite-dimensionality of `W`. -/
theorem norm_tangentialFDeriv_le_of_lipschitzOnWith (hg : LipschitzOnWith K g E) :
    ‖TFD[(finrank ℝ U), E, g, (f u₀)]‖ ≤ K := by
  by_cases h : ∃ L : V →L[ℝ] W, HasTangentialFDerivAt (finrank ℝ U) E g L (f u₀)
  · exact hf.opNorm_le_of_hasTangentialFDerivAt hi hu₀ hsub hdens hg
      (hasTangentialFDerivAt_tangentialFDeriv h)
  · rw [tangentialFDeriv_eq_zero_of_not_exists h, ContinuousLinearMap.opNorm_zero]
    exact K.coe_nonneg

end NormedTarget

section InnerProductTarget
variable [NormedAddCommGroup W] [InnerProductSpace ℝ W] {g : V → W} {B : U →L[ℝ] W} {K : ℝ≥0}

/-- Parametrization chain rule `tangentialJacobian * A.normDet = B.normDet`. -/
theorem tangentialJacobian_mul_normDet (hgf : HasFDerivWithinAt (g ∘ f) B s u₀) :
    TJ[(finrank ℝ U), E, g, (f u₀)] * A.toLinearMap.normDet = B.toLinearMap.normDet := by
  have htan := hf.hasTangentialFDerivAt_of_comp hi hu₀ hsub hdens hdiff hgf
  have hcomp : (TFD[(finrank ℝ U), E, g, (f u₀)]).toLinearMap ∘ₗ A.toLinearMap = B.toLinearMap :=
    congrArg ContinuousLinearMap.toLinearMap
      (hf.tangentialFDeriv_comp_eq hi hu₀ hsub hdens hdiff hgf)
  rw [← hcomp, LinearMap.normDet_comp, htan.tangentialJacobian_eq, ← htan.tangentialFDeriv_eq]
  exact congrArg (· * A.toLinearMap.normDet) (congrArg (fun S : Submodule ℝ V =>
    ((TFD[(finrank ℝ U), E, g, (f u₀)]).toLinearMap.domRestrict S).normDet)
    (hf.approximateTangentPlane_eq_range hi hu₀ hsub hdens hdiff))

omit hdiff in
/-- Sharp bound `tangentialJacobian (finrank ℝ U) E g (f u₀) ≤ K ^ finrank ℝ U` on a patch,
without requiring differentiability of `g ∘ f` or finite-dimensionality of `W`. -/
theorem tangentialJacobian_le_of_lipschitzOnWith (hg : LipschitzOnWith K g E) :
    TJ[(finrank ℝ U), E, g, (f u₀)] ≤ (K : ℝ) ^ finrank ℝ U :=
  (tangentialJacobian_le_norm_tangentialFDeriv_pow _ _ _ _).trans (pow_le_pow_left₀
    (norm_nonneg _) (hf.norm_tangentialFDeriv_le_of_lipschitzOnWith hi hu₀ hsub hdens hg) _)

end InnerProductTarget
end HasFDerivWithinAt
