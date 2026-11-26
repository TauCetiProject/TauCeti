/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Rectifiable.Tangent.Plane
public import TauCeti.Analysis.InnerProductSpace.NormDet
public import TauCeti.Analysis.InnerProductSpace.RangeProjection
import TauCeti.Analysis.Calculus.FDeriv.Remainder
import TauCeti.Analysis.InnerProductSpace.Adjoint
import TauCeti.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.Geometry.Euclidean.Volume.Density
import TauCeti.LinearAlgebra.Dimension.Submodule
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
fallback `0` where none exists, commuting unconditionally with scalar multiplication and negation
and additively at tangentially differentiable points) and the `k`-dimensional tangential Jacobian
`tangentialJacobian k E g x` (`normDet` of its restriction to `P`, also defaulting to `0`). Both
are invariant under `μHE[k]`-null changes and local germs of `E` as well as a.e. modifications of
`g`. On an inverse-Lipschitz patch `f '' s ⊆ E` at a regular density-one point with
`(E \ f '' s)`-density zero, the parametrization chain rule expresses the tangential derivative and
Jacobian via `fderiv` of `f` (using `ContinuousLinearMap.gramLeftInverse`) and `g ∘ f`, yielding
sharp Lipschitz bounds `‖L‖ ≤ K` and `J ≤ K ^ k` and feeding directly into
`Rectifiable.Rademacher` and `Rectifiable.AreaFormula`.

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
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup W] [NormedSpace ℝ W] {k : ℕ}
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

private lemma of_eventually_eq {E₁ E₂ : Set V} {g₁ g₂ : V → W}
    (hu : (∃! P, IsApproximateTangentPlane k E₁ x P) → ∃! P, IsApproximateTangentPlane k E₂ x P)
    (hp : π[k, E₁, x] = π[k, E₂, x])
    (he : ∀ ε > (0 : ℝ), ∀ᶠ r in 𝓝[>] (0 : ℝ),
      μHE[k] {z ∈ E₁ ∩ cb x r | ε * dist z x < ‖g₁ z - g₁ x - L (z - x)‖} =
        μHE[k] {z ∈ E₂ ∩ cb x r | ε * dist z x < ‖g₂ z - g₂ x - L (z - x)‖})
    (h : HasTangentialFDerivAt k E₁ g₁ L x) : HasTangentialFDerivAt k E₂ g₂ L x :=
  ⟨hu h.existsUnique_plane, hp ▸ h.comp_projection,
    fun ε hε => (h.tendsto_outside_error ε hε).congr' ((he ε hε).mono fun _ hr => by rw [hr])⟩

/-- Null-set invariance of `HasTangentialFDerivAt` in the domain set `E`. -/
theorem congr_ae_set (h : E₁ =ᵐ[μHE[k]] E₂) :
    HasTangentialFDerivAt k E₁ g L x ↔ HasTangentialFDerivAt k E₂ g L x :=
  have go {A B : Set V} (hab : A =ᵐ[μHE[k]] B) := of_eventually_eq (g₁ := g) (g₂ := g) (L := L)
    (existsUnique_congr fun P => IsApproximateTangentPlane.congr_ae (x := x) (P := P) hab).mp
    (approximateTangentProjection_congr_ae hab x) fun _ _ => .of_forall fun _ =>
      measure_congr (hab.mono fun _ hz => and_congr_left' (and_congr_left' hz))
  ⟨go h, go h.symm⟩

/-- Germ invariance of `HasTangentialFDerivAt` in the domain set `E`. -/
theorem congr_nhds_set (h : E₁ =ᶠ[𝓝 x] E₂) :
    HasTangentialFDerivAt k E₁ g L x ↔ HasTangentialFDerivAt k E₂ g L x := by
  obtain ⟨δ, hδ, hδeq⟩ := Metric.eventually_nhds_iff.mp h
  have hi : ∀ᶠ r in 𝓝[>] (0 : ℝ), E₁ ∩ cb x r = E₂ ∩ cb x r :=
    Filter.mem_of_superset (Ioo_mem_nhdsGT hδ) fun _ ⟨_, hr⟩ => Set.ext fun _ =>
      and_congr_left fun hzr => by simpa using hδeq ((mem_closedBall.mp hzr).trans_lt hr)
  have hex := existsUnique_congr fun P => IsApproximateTangentPlane.congr_nhds (k := k) (P := P) h
  have hp := approximateTangentProjection_congr_nhds (k := k) h
  exact ⟨of_eventually_eq hex.mp hp fun _ _ => hi.mono fun _ hr => by simp only [hr],
    of_eventually_eq hex.mpr hp.symm fun _ _ => hi.mono fun _ hr => by simp only [hr]⟩

/-- Restriction invariance of `HasTangentialFDerivAt` at `x ∈ E`. -/
theorem congr_of_eqOn (hg : EqOn g₁ g₂ E) (hx : x ∈ E) :
    HasTangentialFDerivAt k E g₁ L x ↔ HasTangentialFDerivAt k E g₂ L x := by
  have hset (ε r : ℝ) : {z ∈ E ∩ cb x r | ε * dist z x < ‖g₁ z - g₁ x - L (z - x)‖} =
      {z ∈ E ∩ cb x r | ε * dist z x < ‖g₂ z - g₂ x - L (z - x)‖} := Set.ext fun _ =>
    and_congr_right fun ⟨hzE, _⟩ => by rw [hg hzE, hg hx]
  exact ⟨of_eventually_eq id rfl fun ε _ => .of_forall fun r => by rw [hset ε r],
    of_eventually_eq id rfl fun ε _ => .of_forall fun r => by rw [hset ε r]⟩

/-- Almost-everywhere congruence of `HasTangentialFDerivAt` in `g` when `g₁ x = g₂ x`. -/
theorem congr_ae_fun (hg : g₁ =ᵐ[μHE[k].restrict E] g₂) (hx_eq : g₁ x = g₂ x) :
    HasTangentialFDerivAt k E g₁ L x ↔ HasTangentialFDerivAt k E g₂ L x := by
  have hN : μHE[k] ({z | g₁ z ≠ g₂ z} ∩ E) = 0 := nonpos_iff_eq_zero.mp <|
    (le_restrict_apply E {z | g₁ z ≠ g₂ z}).trans_eq (ae_iff.mp hg)
  have herr (ε r : ℝ) : μHE[k] {z ∈ E ∩ cb x r | ε * dist z x < ‖g₁ z - g₁ x - L (z - x)‖} =
      μHE[k] {z ∈ E ∩ cb x r | ε * dist z x < ‖g₂ z - g₂ x - L (z - x)‖} := by
    refine measure_congr <| measure_symmDiff_eq_zero_iff.mp <| measure_mono_null ?_ hN
    rintro z (⟨⟨⟨hzE, hzr⟩, h1⟩, h2⟩ | ⟨⟨⟨hzE, hzr⟩, h2⟩, h1⟩)
    exacts [⟨fun h => h2 ⟨⟨hzE, hzr⟩, by rwa [← h, ← hx_eq]⟩, hzE⟩,
      ⟨fun h => h1 ⟨⟨hzE, hzr⟩, by rwa [h, hx_eq]⟩, hzE⟩]
  exact ⟨of_eventually_eq id rfl fun ε _ => .of_forall (herr ε),
    of_eventually_eq id rfl fun ε _ => .of_forall fun r => (herr ε r).symm⟩

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

/-- Scalar multiplication rule for approximate tangential derivatives. -/
theorem const_smul (c : ℝ) (h : HasTangentialFDerivAt k E g L x) :
    HasTangentialFDerivAt k E (fun z => c • g z) (c • L) x := by
  refine ⟨h.existsUnique_plane, by rw [ContinuousLinearMap.smul_comp, h.comp_projection],
    fun ε hε => ?_⟩
  by_cases hc : c = 0
  · subst hc; refine tendsto_const_nhds.congr' (.of_forall fun r => ?_)
    refine (ENNReal.div_eq_zero_iff.mpr (.inl (measure_mono_null ?_ measure_empty))).symm
    rintro _ ⟨_, hlt⟩; simp [not_lt.mpr (mul_nonneg hε.le dist_nonneg)] at hlt
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (h.tendsto_outside_error (ε / |c|) (div_pos hε (abs_pos.mpr hc)))
      (.of_forall fun _ => zero_le) (.of_forall fun r => ENNReal.div_le_div_right
        (measure_mono ?_) _)
    rintro z ⟨hzB, hz⟩; refine ⟨hzB, ?_⟩
    rw [(by simp [smul_sub] : c • g z - c • g x - (c • L) (z - x) = c • (g z - g x - L (z - x))),
      norm_smul, Real.norm_eq_abs] at hz
    rwa [div_mul_eq_mul_div, div_lt_iff₀' (abs_pos.mpr hc)]

/-- Negation rule for approximate tangential derivatives. -/
theorem neg (h : HasTangentialFDerivAt k E g L x) :
    HasTangentialFDerivAt k E (fun z => -g z) (-L) x := by simpa using h.const_smul (-1)

/-- Subtraction rule for approximate tangential derivatives. -/
theorem sub (h₁ : HasTangentialFDerivAt k E g₁ L₁ x) (h₂ : HasTangentialFDerivAt k E g₂ L₂ x) :
    HasTangentialFDerivAt k E (fun z => g₁ z - g₂ z) (L₁ - L₂) x := by
  simpa [sub_eq_add_neg] using h₁.add h₂.neg

end HasTangentialFDerivAt

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
  · rw [zero_smul, zero_smul]
    by_cases h : ∃ L : V →L[ℝ] W, HasTangentialFDerivAt k E 0 L x
    · refine HasTangentialFDerivAt.tangentialFDeriv_eq ⟨h.choose_spec.existsUnique_plane,
        ContinuousLinearMap.zero_comp _, fun ε hε => tendsto_const_nhds.congr' (.of_forall fun _ =>
          (ENNReal.div_eq_zero_iff.mpr (.inl (measure_mono_null ?_ measure_empty))).symm)⟩
      rintro _ ⟨_, hlt⟩; simp [not_lt.mpr (mul_nonneg hε.le dist_nonneg)] at hlt
    · exact tangentialFDeriv_eq_zero_of_not_exists h
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

/-- Null-set invariance of `tangentialFDeriv` in `E`. -/
theorem tangentialFDeriv_congr_ae_set (h : E₁ =ᵐ[μHE[k]] E₂) (g : V → W) (x : V) :
    TFD[k, E₁, g, x] = TFD[k, E₂, g, x] :=
  tangentialFDeriv_eq_of_iff fun _ => HasTangentialFDerivAt.congr_ae_set h

/-- Germ invariance of `tangentialFDeriv` in `E`. -/
theorem tangentialFDeriv_congr_nhds_set (h : E₁ =ᶠ[𝓝 x] E₂) (g : V → W) :
    TFD[k, E₁, g, x] = TFD[k, E₂, g, x] :=
  tangentialFDeriv_eq_of_iff fun _ => HasTangentialFDerivAt.congr_nhds_set h

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

/-- Bound `tangentialJacobian k E g x ≤ ‖L‖ ^ k` under `HasTangentialFDerivAt k E g L x`. -/
theorem HasTangentialFDerivAt.tangentialJacobian_le_opNorm_pow
    (h : HasTangentialFDerivAt k E g L x) : TJ[k, E, g, x] ≤ ‖L‖ ^ k := by
  let P := T[k, E, x]; rw [h.tangentialJacobian_eq]
  conv_rhs => rw [← h.isApproximateTangentPlane.finrank_eq]
  have heq : L.toLinearMap.domRestrict P = (L.comp P.subtypeL).toLinearMap := by ext y; rfl
  rw [heq]; exact (L.comp P.subtypeL).normDet_le_norm_pow.trans <| pow_le_pow_left₀ (norm_nonneg _)
    ((L.opNorm_comp_le P.subtypeL).trans (mul_le_of_le_one_right (norm_nonneg L)
      (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun _ => by simp))) _

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
    (hf : HasFDerivWithinAt f A s u₀) (hinj : Injective A)
    (hi : AntilipschitzWith L_f (s.domRestrict f)) (hu₀ : u₀ ∈ s) (hsub : f '' s ⊆ E)
    (hdens : Tendsto (fun r => volume (s ∩ cb u₀ r) / volume (cb (0 : U) r)) 𝓝₊ (𝓝 1))
    (hdiff : Tendsto (fun r => μHE[finrank ℝ U] ((E \ f '' s) ∩ cb (f u₀) r) /
      ω[finrank ℝ U](r)) 𝓝₊ (𝓝 0))
include hf hinj hi hu₀ hsub hdens hdiff

section NormedTarget
variable [NormedAddCommGroup W] [NormedSpace ℝ W] {g : V → W} {B : U →L[ℝ] W} {K : ℝ≥0}

/-- Parametrization chain rule for `HasTangentialFDerivAt` on an inverse-Lipschitz patch. -/
theorem hasTangentialFDerivAt_of_comp (hgf : HasFDerivWithinAt (g ∘ f) B s u₀) :
    HasTangentialFDerivAt (finrank ℝ U) E g (B ∘L A.gramLeftInverse) (f u₀) := by
  -- Step 1: Identify `range A` as the unique approximate tangent plane and verify `L ∘L A = B`.
  let P := LinearMap.range A.toLinearMap; let L := B ∘L A.gramLeftInverse
  have htan_iff (Q) := hf.isApproximateTangentPlane_iff hinj hi hu₀ hsub hdens hdiff (Q := Q)
  have hU := (ContinuousLinearMap.isUnit_adjoint_comp_self_iff A).2 hinj
  have hLA : L ∘L A = B := by
    rw [ContinuousLinearMap.comp_assoc, A.gramLeftInverse_comp_self hU,
      ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id]
  refine ⟨⟨P, (htan_iff P).mpr rfl, fun Q hQ => (htan_iff Q).mp hQ⟩, ?_, fun ε hε => ?_⟩
  · -- Step 2: `L` factors through the orthogonal projection onto `range A` via `gramLeftInverse`.
    rw [approximateTangentProjection_eq,
      hf.approximateTangentPlane_eq_range hinj hi hu₀ hsub hdens hdiff,
      ContinuousLinearMap.starProjection_range_eq hU, ← ContinuousLinearMap.comp_assoc, hLA]
  · -- Step 3: On `f '' s`, `hi` and the Fréchet remainders of `g ∘ f` and `f` force the
    -- tangential error below `ε * dist z (f u₀)`, leaving `E \ f '' s` which has density zero.
    have hLf1 : (0 : ℝ) < (L_f : ℝ) + 1 := by positivity
    set η₁ := ε / (2 * ((L_f : ℝ) + 1)); set η₂ := ε / (2 * (‖L‖ + 1) * ((L_f : ℝ) + 1))
    obtain ⟨δ₁, hδ₁, hδ₁b⟩ := hgf.exists_ball_remainder_le (by positivity : 0 < η₁)
    obtain ⟨δ₂, hδ₂, hδ₂b⟩ := hf.exists_ball_remainder_le (by positivity : 0 < η₂)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdiff
      (.of_forall fun _ => zero_le) ?_
    filter_upwards [Ioo_mem_nhdsGT (div_pos (lt_min hδ₁ hδ₂) hLf1)] with r ⟨_, hrδ⟩
    gcongr; rintro z ⟨⟨hzE, hzr⟩, hzerr⟩; refine ⟨⟨hzE, ?_⟩, hzr⟩; rintro ⟨u, hus, rfl⟩
    have hnorm_u : ‖u - u₀‖ ≤ ((L_f : ℝ) + 1) * dist (f u) (f u₀) :=
      dist_eq_norm u u₀ ▸ hi.dist_le_add_one_mul_of_domRestrict hus hu₀
    have hu_lt : dist u u₀ < min δ₁ δ₂ := ((dist_eq_norm u u₀ ▸ hnorm_u).trans
      (mul_le_mul_of_nonneg_left (mem_closedBall.mp hzr) hLf1.le)).trans_lt
      ((lt_div_iff₀' hLf1).mp hrδ)
    have herr₁ := hδ₁b u (mem_ball.mpr (hu_lt.trans_le (min_le_left _ _))) hus
    have herr₂ := hδ₂b u (mem_ball.mpr (hu_lt.trans_le (min_le_right _ _))) hus
    refine hzerr.not_ge <| calc
      ‖g (f u) - g (f u₀) - L (f u - f u₀)‖
          ≤ ‖g (f u) - g (f u₀) - B (u - u₀)‖ + ‖L (f u - f u₀ - A (u - u₀))‖ :=
            (by simp only [← hLA, ContinuousLinearMap.comp_apply, map_sub]; abel : g (f u) -
              g (f u₀) - L (f u - f u₀) = (g (f u) - g (f u₀) - B (u - u₀)) -
                L (f u - f u₀ - A (u - u₀))) ▸ norm_sub_le _ _
      _ ≤ η₁ * ‖u - u₀‖ + ‖L‖ * (η₂ * ‖u - u₀‖) :=
            add_le_add (by simpa only [comp_apply] using herr₁) ((L.le_opNorm _).trans (by gcongr))
      _ ≤ η₁ * (((L_f : ℝ) + 1) * dist (f u) (f u₀)) +
            (‖L‖ + 1) * (η₂ * (((L_f : ℝ) + 1) * dist (f u) (f u₀))) := by gcongr; linarith
      _ = ε * dist (f u) (f u₀) := by dsimp [η₁, η₂]; field_simp; ring

/-- Composing `tangentialFDeriv` at `f u₀` with `A` recovers the parameter derivative `B`. -/
theorem tangentialFDeriv_comp_eq (hgf : HasFDerivWithinAt (g ∘ f) B s u₀) :
    TFD[(finrank ℝ U), E, g, (f u₀)] ∘L A = B := by
  rw [(hf.hasTangentialFDerivAt_of_comp hinj hi hu₀ hsub hdens hdiff hgf).tangentialFDeriv_eq,
    ContinuousLinearMap.comp_assoc,
    A.gramLeftInverse_comp_self ((ContinuousLinearMap.isUnit_adjoint_comp_self_iff A).2 hinj),
    ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id]

/-- Sharp bound `‖tangentialFDeriv (finrank ℝ U) E g (f u₀)‖ ≤ K` on a patch. -/
theorem norm_tangentialFDeriv_le_of_lipschitzOnWith (hgf : HasFDerivWithinAt (g ∘ f) B s u₀)
    (hg : LipschitzOnWith K g E) : ‖TFD[(finrank ℝ U), E, g, (f u₀)]‖ ≤ K := by
  refine ContinuousLinearMap.opNorm_le_bound _ K.coe_nonneg fun z => ?_
  let P := T[(finrank ℝ U), E, (f u₀)]
  obtain ⟨u, hu⟩ : P.starProjection z ∈ LinearMap.range A.toLinearMap :=
    hf.approximateTangentPlane_eq_range hinj hi hu₀ hsub hdens hdiff ▸ P.starProjection_apply_mem z
  calc ‖TFD[(finrank ℝ U), E, g, (f u₀)] z‖
      = ‖TFD[(finrank ℝ U), E, g, (f u₀)] (P.starProjection z)‖ := by
        rw [← approximateTangentProjection_eq, ← ContinuousLinearMap.comp_apply,
          tangentialFDeriv_comp_approximateTangentProjection]
    _ = ‖B u‖ := by rw [← hu, ContinuousLinearMap.coe_coe, ← ContinuousLinearMap.comp_apply,
          hf.tangentialFDeriv_comp_eq hinj hi hu₀ hsub hdens hdiff hgf]
    _ ≤ K * ‖A u‖ := hf.norm_comp_le_of_lipschitzOnWith hu₀ hsub hdens hgf hg u
    _ = K * ‖P.starProjection z‖ := by rw [← ContinuousLinearMap.coe_coe, hu]
    _ ≤ K * ‖z‖ := by gcongr; exact P.norm_starProjection_apply_le z

end NormedTarget

section InnerProductTarget
variable [NormedAddCommGroup W] [InnerProductSpace ℝ W] {g : V → W} {B : U →L[ℝ] W} {K : ℝ≥0}

/-- Parametrization chain rule `tangentialJacobian * A.normDet = B.normDet`. -/
theorem tangentialJacobian_mul_normDet (hgf : HasFDerivWithinAt (g ∘ f) B s u₀) :
    TJ[(finrank ℝ U), E, g, (f u₀)] * A.toLinearMap.normDet = B.toLinearMap.normDet := by
  have htan := hf.hasTangentialFDerivAt_of_comp hinj hi hu₀ hsub hdens hdiff hgf
  have hcomp : (TFD[(finrank ℝ U), E, g, (f u₀)]).toLinearMap ∘ₗ A.toLinearMap = B.toLinearMap :=
    congrArg ContinuousLinearMap.toLinearMap
      (hf.tangentialFDeriv_comp_eq hinj hi hu₀ hsub hdens hdiff hgf)
  rw [← hcomp, LinearMap.normDet_comp, htan.tangentialJacobian_eq, ← htan.tangentialFDeriv_eq]
  exact congrArg (· * A.toLinearMap.normDet) (congrArg (fun S : Submodule ℝ V =>
    ((TFD[(finrank ℝ U), E, g, (f u₀)]).toLinearMap.domRestrict S).normDet)
    (hf.approximateTangentPlane_eq_range hinj hi hu₀ hsub hdens hdiff))

/-- Sharp bound `tangentialJacobian (finrank ℝ U) E g (f u₀) ≤ K ^ finrank ℝ U` on a patch. -/
theorem tangentialJacobian_le_of_lipschitzOnWith (hgf : HasFDerivWithinAt (g ∘ f) B s u₀)
    (hg : LipschitzOnWith K g E) : TJ[(finrank ℝ U), E, g, (f u₀)] ≤ (K : ℝ) ^ finrank ℝ U := by
  have htan := hf.hasTangentialFDerivAt_of_comp hinj hi hu₀ hsub hdens hdiff hgf
  exact htan.tangentialJacobian_le_opNorm_pow.trans (pow_le_pow_left₀ (norm_nonneg _)
    (htan.tangentialFDeriv_eq ▸ hf.norm_tangentialFDeriv_le_of_lipschitzOnWith hinj hi hu₀ hsub
      hdens hdiff hgf hg) _)

end InnerProductTarget
end HasFDerivWithinAt
