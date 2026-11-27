/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Rectifiable.Tangent.Approximate
public import TauCeti.Geometry.MeasureTheory.Rectifiable.Tangent.Uniqueness
public import Mathlib.Order.LiminfLimsup
import TauCeti.Analysis.Calculus.FDeriv.Remainder
import TauCeti.Analysis.Normed.Module.FiniteDimension.Closedness
import TauCeti.Geometry.Euclidean.Volume.Density

/-!
# Canonical approximate tangent planes and projections

A countably `k`-rectifiable set with locally finite normalized Euclidean Hausdorff measure has,
almost everywhere, a unique approximate tangent `k`-plane: a `k`-plane with positive upper
`k`-dimensional density and `TauCeti.DensityZeroOutsideCones` (`IsApproximateTangentPlane`,
Mattila 15.17). Combining existence (`Rectifiable.Tangent.Approximate`), uniqueness
(`Rectifiable.Tangent.Uniqueness`), and the density-one theorem (`Rectifiable.Density`) yields
almost-everywhere existence and uniqueness
(`CountablyRectifiable.ae_existsUnique_isApproximateTangentPlane`) and defines the canonical plane
`approximateTangentPlane` (defaulting to `⊥` where none exists) and its orthogonal projection
`approximateTangentProjection` (defaulting to `0`), which is `μHE[k].restrict E`-a.e. measurable.

For inverse-Lipschitz parametrizations `f : U → V` differentiable within `s` at a Lebesgue
density-one point `x₀ ∈ s` (without assuming `f` is Lipschitz on `s`), any subspace with
cone-density zero contains `range A` (`HasFDerivWithinAt.range_le_of_densityZeroOutsideCones`),
identifying `approximateTangentPlane` on both general patches and differentiable normal graphs.
In particular, a set containing a line through `x` not contained in `P` fails
`TauCeti.DensityZeroOutsideCones 1` at `x` for `P` (`not_densityZeroOutsideCones_of_not_le`).
The canonical plane and projection provide the linear domain for tangential derivatives and
Jacobians in `Rectifiable.TangentialFDeriv`.

## References

* L. Simon, *Lectures on Geometric Measure Theory*, §11 (approximate tangents).
* P. Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Def. 15.17 and Thm. 15.19.
-/

public section

open Filter Function Metric MeasureTheory Measure Module Set
open scoped ENNReal NNReal Topology symmDiff
local notation "ω[" d "](" r ")" => volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) r)
local notation "𝓝₊" => 𝓝[>] (0 : ℝ)
local notation "cb" => Metric.closedBall

namespace HasFDerivWithinAt
open TauCeti
variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace U]
    [BorelSpace U] [MeasurableSpace V] [BorelSpace V] {f : U → V} {s : Set U} {A : U →L[ℝ] V}
    {x₀ : U} {L : ℝ≥0} {E : Set V} {Q : Submodule ℝ V}

omit [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U]
  [MeasurableSpace V] [BorelSpace V] in
private lemma image_shifted_closedBall_subset_outside_cone {u : U} (hu : ‖u‖ = 1)
    {d : ℝ} (hd_def : d = infDist (A u) (Q : Set V)) (hd0 : 0 < d) (hsub : f '' s ⊆ E)
    {ρ : ℝ} (hρ0 : 0 < ρ)
    (hδb : ∀ y, dist y x₀ ≤ ρ → y ∈ s → ‖f y - f x₀ - A (y - x₀)‖ ≤ min 1 (d / 16) * ‖y - x₀‖) :
    f '' (s ∩ cb (x₀ + (ρ / 2) • u) ((min (1 / 2) (d / (2 * (‖A‖ + 1))) / 4) * ρ)) ⊆
      {z ∈ E ∩ cb (f x₀) ((‖A‖ + 1) * ρ) |
        (d / (16 * (‖A‖ + 1))) * dist z (f x₀) < infDist (z - f x₀) (Q : Set V)} := by
  set η : ℝ := min (1 / 2) (d / (2 * (‖A‖ + 1)))
  have hηA : η * ‖A‖ ≤ d / 2 := (mul_le_mul (min_le_right _ _) (le_add_of_nonneg_right zero_le_one)
    (norm_nonneg A) (by positivity)).trans_eq (by field_simp)
  rintro _ ⟨x, ⟨hxs, hxD⟩, rfl⟩
  have hy : ‖x - (x₀ + (ρ / 2) • u)‖ ≤ (η / 4) * ρ := by simpa [dist_eq_norm] using hxD
  have hdist_x : ‖x - x₀‖ ≤ ρ := by
    have h1 := (by abel : x - (x₀ + (ρ / 2) • u) + (ρ / 2) • u = x - x₀) ▸
      norm_add_le (x - (x₀ + (ρ / 2) • u)) ((ρ / 2) • u)
    rw [norm_smul, Real.norm_of_nonneg (by positivity), hu] at h1
    nlinarith [min_le_left (1 / 2) (d / (2 * (‖A‖ + 1)))]
  have herr := hδb x (by simpa [dist_eq_norm] using hdist_x) hxs
  have herr1 : ‖f x - f x₀ - A (x - x₀)‖ ≤ ‖x - x₀‖ := by
    simpa using herr.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg _))
  have herr2 : ‖f x - f x₀ - A (x - x₀)‖ ≤ (d / 16) * ρ :=
    herr.trans ((mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)).trans (by gcongr))
  have hfx_dist : dist (f x) (f x₀) ≤ (‖A‖ + 1) * ρ :=
    (A.dist_le_add_one_mul_of_norm_sub_le herr1).trans (by rw [dist_eq_norm]; gcongr)
  refine ⟨⟨hsub (mem_image_of_mem f hxs), mem_closedBall.mpr hfx_dist⟩, ?_⟩
  have hAy : ‖A (x - (x₀ + (ρ / 2) • u))‖ ≤ (d / 8) * ρ :=
    (A.le_opNorm _).trans <| (mul_le_mul_of_nonneg_left hy (norm_nonneg A)).trans (by nlinarith)
  have hdiff : ‖(f x - f x₀) - (ρ / 2) • A u‖ ≤ (3 / 16) * d * ρ :=
    (by simp [map_sub, map_add, map_smul]; abel : (f x - f x₀) - (ρ / 2) • A u =
      (f x - f x₀ - A (x - x₀)) + A (x - (x₀ + (ρ / 2) • u))) ▸
      (norm_add_le _ _).trans (by linarith)
  have hsmul : infDist ((ρ / 2) • A u) (Q : Set V) = (ρ / 2) * d := by
    rw [hd_def, ← Q.dist_starProjection_eq_infDist, ← Q.dist_starProjection_eq_infDist,
      dist_eq_norm, dist_eq_norm, Q.starProjection.map_smul (ρ / 2), ← smul_sub, norm_smul,
      Real.norm_of_nonneg (by positivity)]
  have hlip := (lipschitz_infDist_pt (Q : Set V)).dist_le_mul (f x - f x₀) ((ρ / 2) • A u)
  rw [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm, hsmul] at hlip
  have hcone_lhs : (d / (16 * (‖A‖ + 1))) * dist (f x) (f x₀) ≤ (d / 16) * ρ :=
    (mul_le_mul_of_nonneg_left hfx_dist (by positivity)).trans_eq (by field_simp)
  linarith [neg_le_of_abs_le hlip, mul_pos hd0 hρ0]

/-- Patchwise lower bound `range A ≤ Q` on any cone-density-zero subspace `Q ≤ V`, without
requiring `f` to be Lipschitz on `s`. -/
theorem range_le_of_densityZeroOutsideCones (hf : HasFDerivWithinAt f A s x₀)
    (hi : AntilipschitzWith L (s.domRestrict f)) (hsub : f '' s ⊆ E)
    (hdens : Tendsto (fun r => volume (s ∩ cb x₀ r) / volume (cb (0 : U) r)) 𝓝₊ (𝓝 1))
    (hQ : DensityZeroOutsideCones (finrank ℝ U) E (f x₀) Q) :
    LinearMap.range A.toLinearMap ≤ Q := by
  by_contra hnot; obtain ⟨_, ⟨v, rfl⟩, hvQ⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  have hv0 : v ≠ 0 := fun h => hvQ (by simp [h])
  let u : U := ‖v‖⁻¹ • v; have hu : ‖u‖ = 1 := norm_smul_inv_norm hv0
  have hAu : A u ∉ Q := fun h => hvQ <| by
    simpa [u, smul_smul, norm_ne_zero_iff.mpr hv0] using Q.smul_mem ‖v‖ h
  set d := infDist (A u) (Q : Set V) with hd_def
  have hd0 : 0 < d := Q.infDist_pos_of_notMem hAu
  set η : ℝ := min (1 / 2) (d / (2 * (‖A‖ + 1)))
  have hη0 : 0 < η := lt_min (by norm_num) (by positivity)
  let C : ℝ≥0 := ⟨‖A‖ + 1, by positivity⟩; have hC0 : 0 < C := Subtype.mk_lt_mk.mpr (by positivity)
  obtain ⟨δ, hδ, hδb⟩ := hf.exists_ball_remainder_le (by positivity : (0 : ℝ) < min 1 (d / 16))
  refine not_tendsto_volume_inter_shifted_closedBall_div_zero hdens hu hη0 (min_le_left _ _) <|
    tendsto_volume_div_zero_of_antilipschitzWith hi hC0
      (densityZeroOutsideCones_iff.mp hQ (d / (16 * C))
        (div_pos hd0 (mul_pos (by norm_num) (NNReal.coe_pos.2 hC0)))) ?_
  filter_upwards [Ioo_mem_nhdsGT hδ] with ρ ⟨hρ0, hρδ⟩
  exact image_shifted_closedBall_subset_outside_cone hu hd_def hd0 hsub hρ0
    fun y hy => hδb y (mem_ball.mpr (hy.trans_lt hρδ))

/-- Patchwise uniqueness `Q = range A` when `A` is injective and `finrank ℝ Q ≤ finrank ℝ U`. -/
theorem eq_range_of_densityZeroOutsideCones (hf : HasFDerivWithinAt f A s x₀) (hinj : Injective A)
    (hi : AntilipschitzWith L (s.domRestrict f)) (hsub : f '' s ⊆ E)
    (hdens : Tendsto (fun r => volume (s ∩ cb x₀ r) / volume (cb (0 : U) r)) 𝓝₊ (𝓝 1))
    (hQdim : finrank ℝ Q ≤ finrank ℝ U) (hQ : DensityZeroOutsideCones (finrank ℝ U) E (f x₀) Q) :
    Q = LinearMap.range A.toLinearMap :=
  (Submodule.eq_of_le_of_finrank_le (hf.range_le_of_densityZeroOutsideCones hi hsub hdens hQ)
    (hQdim.trans_eq (LinearMap.finrank_range_of_inj hinj).symm)).symm

omit [FiniteDimensional ℝ V] in
/-- Positive upper `(dim U)`-density of `E` at `f x₀` on an inverse-Lipschitz patch. -/
theorem limsup_euclideanHausdorffMeasure_inter_closedBall_div_pos (hf : HasFDerivWithinAt f A s x₀)
    (hi : AntilipschitzWith L (s.domRestrict f)) (hsub : f '' s ⊆ E)
    (hdens : Tendsto (fun r => volume (s ∩ cb x₀ r) / volume (cb (0 : U) r)) 𝓝₊ (𝓝 1)) :
    0 < limsup (fun r => μHE[finrank ℝ U] (E ∩ cb (f x₀) r) / ω[finrank ℝ U](r)) 𝓝₊ := by
  by_contra! hle
  let C : ℝ≥0 := ⟨‖A‖ + 1, by positivity⟩
  obtain ⟨δ, hδ, hδb⟩ := hf.exists_ball_dist_le_add_one_mul
  refine one_ne_zero <| tendsto_nhds_unique hdens <| tendsto_volume_div_zero_of_antilipschitzWith hi
    (Subtype.mk_lt_mk.mpr (by positivity) : 0 < C)
    (tendsto_of_le_liminf_of_limsup_le zero_le (nonpos_iff_eq_zero.mp hle).le) ?_
  filter_upwards [Ioo_mem_nhdsGT hδ] with ρ ⟨_, hρδ⟩
  rintro _ ⟨x, ⟨hxs, hxB⟩, rfl⟩
  exact ⟨hsub (mem_image_of_mem f hxs), mem_closedBall.mpr <|
    (hδb x (mem_ball.mpr ((mem_closedBall.mp hxB).trans_lt hρδ)) hxs).trans
      (mul_le_mul_of_nonneg_left (mem_closedBall.mp hxB) (by positivity))⟩

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ V] [MeasurableSpace U] [BorelSpace U] in
/-- Zero `(dim U)`-density outside every cone around `range A` on an inverse-Lipschitz patch. -/
theorem densityZeroOutsideCones_range (hf : HasFDerivWithinAt f A s x₀)
    (hi : AntilipschitzWith L (s.domRestrict f)) (hx₀ : x₀ ∈ s)
    (hdiff : Tendsto (fun r => μHE[finrank ℝ U] ((E \ f '' s) ∩ cb (f x₀) r) /
      ω[finrank ℝ U](r)) 𝓝₊ (𝓝 0)) :
    DensityZeroOutsideCones (finrank ℝ U) E (f x₀) (LinearMap.range A.toLinearMap) := by
  rw [densityZeroOutsideCones_iff]; intro ε hε
  obtain ⟨r₀, hr₀, hcone⟩ := hf.exists_pos_forall_infDist_range_le hx₀ hi hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdiff
    (.of_forall fun _ => zero_le) ?_
  filter_upwards [Ioo_mem_nhdsGT hr₀] with r ⟨_, hrr₀⟩
  gcongr; rintro z ⟨⟨hzE, hzr⟩, hzcone⟩
  exact ⟨⟨hzE, fun hzs => hzcone.not_ge (hcone z hzs ((mem_closedBall.mp hzr).trans_lt hrr₀))⟩,
    hzr⟩

end HasFDerivWithinAt

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {k : ℕ} {E E₁ E₂ : Set V}

/-- If a set `E` contains the line `x + L` through `x`, where `L` is not contained in a subspace
`P`, then `E` does not have `1`-dimensional density zero outside the cones about `P` at `x`. -/
theorem not_densityZeroOutsideCones_of_not_le {x : V} {L P : Submodule ℝ V}
    (hLE : ∀ z ∈ L, x + z ∈ E) (hLP : ¬ L ≤ P) : ¬ DensityZeroOutsideCones 1 E x P := by
  -- Apply `HasFDerivWithinAt.range_le_of_densityZeroOutsideCones` to the parametrization
  -- `t ↦ x + t v` of the line through `x` in the direction of a vector `v ∈ L \ P`.
  intro h
  obtain ⟨v, hvL, hvP⟩ := IsConcreteLE.not_le_iff_exists.mp hLP
  have hv0 : v ≠ 0 := fun hv ↦ hvP (hv ▸ P.zero_mem)
  let A : ℝ →L[ℝ] V := ContinuousLinearMap.toSpanSingleton ℝ v
  have hf : HasFDerivWithinAt (fun t : ℝ ↦ x + A t) A univ 0 :=
    (A.hasFDerivAt.const_add x).hasFDerivWithinAt
  have hi : AntilipschitzWith ‖v‖₊⁻¹ ((univ : Set ℝ).domRestrict fun t ↦ x + A t) :=
    AntilipschitzWith.of_le_mul_dist fun s t ↦ by
      simp [A, Set.domRestrict_apply, Subtype.dist_eq, dist_eq_norm, ← sub_smul, norm_smul]
      field_simp [norm_ne_zero_iff.mpr hv0]
      exact le_rfl
  have hsub : (fun t : ℝ ↦ x + A t) '' univ ⊆ E := by
    rintro _ ⟨t, -, rfl⟩
    exact hLE _ (L.smul_mem t hvL)
  have hdens : Tendsto (fun r ↦ volume ((univ : Set ℝ) ∩ cb 0 r) / volume (cb (0 : ℝ) r)) 𝓝₊
      (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    rw [univ_inter, ENNReal.div_self (measure_closedBall_pos volume _ hr).ne'
      measure_closedBall_lt_top.ne]
  have hle := hf.range_le_of_densityZeroOutsideCones hi hsub hdens (by simpa using h)
  exact hvP (hle ⟨1, by simp [A]⟩)

/-- `P` is an approximate tangent `k`-plane to `E` at `x` (Mattila, Definition 15.17). -/
structure IsApproximateTangentPlane (k : ℕ) (E : Set V) (x : V) (P : Submodule ℝ V) : Prop where
  /-- `P` has dimension `k`. -/
  finrank_eq : finrank ℝ P = k
  /-- `E` has positive upper `k`-dimensional density at `x`. -/
  limsup_pos : 0 < limsup (fun r => μHE[k] (E ∩ cb x r) / ω[k](r)) 𝓝₊
  /-- Outside every cone around `P`, `E` has `k`-dimensional density zero at `x`. -/
  densityZeroOutsideCones : DensityZeroOutsideCones k E x P

namespace IsApproximateTangentPlane

/-- In dimension zero, any approximate tangent plane is `⊥`. -/
theorem eq_bot {x : V} {P : Submodule ℝ V} (h : IsApproximateTangentPlane 0 E x P) : P = ⊥ := by
  have := finrank_zero_iff.mp h.finrank_eq; exact Submodule.eq_bot_of_subsingleton

omit [FiniteDimensional ℝ V] in
private lemma of_eventually_eq_measure {x : V} {P : Submodule ℝ V}
    (hb : ∀ᶠ r in 𝓝[>] (0 : ℝ), μHE[k] (E₁ ∩ cb x r) = μHE[k] (E₂ ∩ cb x r))
    (hc : ∀ ε, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      μHE[k] {z ∈ E₁ ∩ cb x r | ε * dist z x < infDist (z - x) (P : Set V)} =
        μHE[k] {z ∈ E₂ ∩ cb x r | ε * dist z x < infDist (z - x) (P : Set V)})
    (h : IsApproximateTangentPlane k E₁ x P) :
    IsApproximateTangentPlane k E₂ x P :=
  ⟨h.finrank_eq, (limsup_congr (hb.mono fun _ hr => congrArg (· / _) hr)).symm ▸ h.limsup_pos,
    densityZeroOutsideCones_iff.mpr fun ε hε =>
      (densityZeroOutsideCones_iff.mp h.densityZeroOutsideCones ε hε).congr'
        ((hc ε).mono fun _ hr => by rw [hr])⟩

omit [FiniteDimensional ℝ V] in
/-- Modifying `E` by a `μHE[k]`-null set preserves approximate tangent planes at `x`. -/
theorem congr_ae (h : E₁ =ᵐ[μHE[k]] E₂) {x : V} {P : Submodule ℝ V} :
    IsApproximateTangentPlane k E₁ x P ↔ IsApproximateTangentPlane k E₂ x P :=
  have go {A B : Set V} (hab : A =ᵐ[μHE[k]] B) := of_eventually_eq_measure (x := x) (P := P)
    (.of_forall fun _ => measure_congr (hab.inter .rfl)) fun _ => .of_forall fun _ =>
      measure_congr (hab.mono fun _ hz => and_congr_left' (and_congr_left' hz))
  ⟨go h, go h.symm⟩

omit [FiniteDimensional ℝ V] in
/-- Approximate tangent planes depend only on the germ of `E` at `x`. -/
theorem congr_nhds {x : V} (h : E₁ =ᶠ[𝓝 x] E₂) {P : Submodule ℝ V} :
    IsApproximateTangentPlane k E₁ x P ↔ IsApproximateTangentPlane k E₂ x P := by
  obtain ⟨δ, hδ, hδeq⟩ := Metric.eventually_nhds_iff.mp h
  have hi : ∀ᶠ r in 𝓝[>] (0 : ℝ), E₁ ∩ cb x r = E₂ ∩ cb x r :=
    Filter.mem_of_superset (Ioo_mem_nhdsGT hδ) fun _ ⟨_, hr⟩ => Set.ext fun _ =>
      and_congr_left fun hzr => by simpa using hδeq ((mem_closedBall.mp hzr).trans_lt hr)
  exact ⟨of_eventually_eq_measure (hi.mono fun _ hr => by rw [hr]) (fun _ => hi.mono fun _ hr => by
      simp only [hr]), of_eventually_eq_measure (hi.mono fun _ hr => by rw [hr]) fun _ =>
    hi.mono fun _ hr => by simp only [hr]⟩

end IsApproximateTangentPlane

open Classical in
/-- Canonical approximate tangent `k`-plane to `E` at `x` (`⊥` if none exists). -/
noncomputable def approximateTangentPlane (k : ℕ) (E : Set V) (x : V) : Submodule ℝ V :=
  if h : ∃ P : Submodule ℝ V, IsApproximateTangentPlane k E x P then h.choose else ⊥

/-- Orthogonal projection onto `TauCeti.approximateTangentPlane k E x`. -/
noncomputable def approximateTangentProjection (k : ℕ) (E : Set V) (x : V) : V →L[ℝ] V :=
  (approximateTangentPlane k E x).starProjection

/-- Unfolding lemma for `approximateTangentProjection k E x`. -/
theorem approximateTangentProjection_eq (k : ℕ) (E : Set V) (x : V) :
    approximateTangentProjection k E x = (approximateTangentPlane k E x).starProjection := by rfl

omit [FiniteDimensional ℝ V] in
/-- Uniqueness identifies `approximateTangentPlane k E x` with `P`. -/
theorem IsApproximateTangentPlane.approximateTangentPlane_eq {x : V} {P : Submodule ℝ V}
    (hP : IsApproximateTangentPlane k E x P)
    (huniq : ∀ Q, IsApproximateTangentPlane k E x Q → Q = P) :
    approximateTangentPlane k E x = P := by
  have hex : ∃ Q, IsApproximateTangentPlane k E x Q := ⟨P, hP⟩
  simp only [approximateTangentPlane, hex, ↓reduceDIte]; exact huniq _ hex.choose_spec

/-- Uniqueness identifies `approximateTangentProjection k E x` with `P.starProjection`. -/
theorem IsApproximateTangentPlane.approximateTangentProjection_eq {x : V} {P : Submodule ℝ V}
    (hP : IsApproximateTangentPlane k E x P)
    (huniq : ∀ Q, IsApproximateTangentPlane k E x Q → Q = P) :
    approximateTangentProjection k E x = P.starProjection := by
  simp only [approximateTangentProjection, hP.approximateTangentPlane_eq huniq]

omit [FiniteDimensional ℝ V] in
/-- Specification of `approximateTangentPlane k E x` when a plane exists. -/
theorem isApproximateTangentPlane_approximateTangentPlane {x : V}
    (h : ∃ P : Submodule ℝ V, IsApproximateTangentPlane k E x P) :
    IsApproximateTangentPlane k E x (approximateTangentPlane k E x) := by
  simp only [approximateTangentPlane, h, ↓reduceDIte]; exact h.choose_spec

omit [FiniteDimensional ℝ V] in
/-- When no approximate tangent `k`-plane exists at `x`, `approximateTangentPlane k E x = ⊥`. -/
@[simp] theorem approximateTangentPlane_eq_bot_of_not_exists {x : V}
    (h : ¬ ∃ P : Submodule ℝ V, IsApproximateTangentPlane k E x P) :
    approximateTangentPlane k E x = ⊥ := by simp [approximateTangentPlane, h]

/-- If no approximate tangent `k`-plane exists at `x`, `approximateTangentProjection k E x = 0`. -/
@[simp] theorem approximateTangentProjection_eq_zero_of_not_exists {x : V}
    (h : ¬ ∃ P : Submodule ℝ V, IsApproximateTangentPlane k E x P) :
    approximateTangentProjection k E x = 0 := by simp [approximateTangentProjection, h]

/-- In dimension zero, `approximateTangentPlane 0 E x = ⊥`. -/
@[simp] theorem approximateTangentPlane_zero (E : Set V) (x : V) :
    approximateTangentPlane 0 E x = ⊥ := by
  by_cases h : ∃ P : Submodule ℝ V, IsApproximateTangentPlane 0 E x P
  exacts [(isApproximateTangentPlane_approximateTangentPlane h).eq_bot, by simp [h]]

/-- In dimension zero, `approximateTangentProjection 0 E x = 0`. -/
@[simp] theorem approximateTangentProjection_zero (E : Set V) (x : V) :
    approximateTangentProjection 0 E x = 0 := by simp [approximateTangentProjection]

omit [FiniteDimensional ℝ V] in
private lemma approximateTangentPlane_eq_of_iff {x : V}
    (hiff : ∀ P, IsApproximateTangentPlane k E₁ x P ↔ IsApproximateTangentPlane k E₂ x P) :
    approximateTangentPlane k E₁ x = approximateTangentPlane k E₂ x := by
  unfold approximateTangentPlane
  rw [funext fun P => propext (hiff P)]

omit [FiniteDimensional ℝ V] in
/-- Null-set invariance of `approximateTangentPlane`. -/
theorem approximateTangentPlane_congr_ae (h : E₁ =ᵐ[μHE[k]] E₂) (x : V) :
    approximateTangentPlane k E₁ x = approximateTangentPlane k E₂ x :=
  approximateTangentPlane_eq_of_iff fun _ => IsApproximateTangentPlane.congr_ae h

/-- Null-set invariance of `approximateTangentProjection`. -/
theorem approximateTangentProjection_congr_ae (h : E₁ =ᵐ[μHE[k]] E₂) (x : V) :
    approximateTangentProjection k E₁ x = approximateTangentProjection k E₂ x := by
  simp only [approximateTangentProjection, approximateTangentPlane_congr_ae h]

omit [FiniteDimensional ℝ V] in
/-- Germ invariance of `approximateTangentPlane`. -/
theorem approximateTangentPlane_congr_nhds {x : V} (h : E₁ =ᶠ[𝓝 x] E₂) :
    approximateTangentPlane k E₁ x = approximateTangentPlane k E₂ x :=
  approximateTangentPlane_eq_of_iff fun _ => IsApproximateTangentPlane.congr_nhds h

/-- Germ invariance of `approximateTangentProjection`. -/
theorem approximateTangentProjection_congr_nhds {x : V} (h : E₁ =ᶠ[𝓝 x] E₂) :
    approximateTangentProjection k E₁ x = approximateTangentProjection k E₂ x := by
  simp only [approximateTangentProjection, approximateTangentPlane_congr_nhds h]

section Rectifiable
variable (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
  [IsLocallyFiniteMeasure (μHE[k].restrict E)]
include hE hEm

/-- Almost-everywhere existence and uniqueness of approximate tangent `k`-planes. -/
theorem CountablyRectifiable.ae_existsUnique_isApproximateTangentPlane :
    ∀ᵐ x ∂μHE[k], x ∈ E → ∃! P : Submodule ℝ V, IsApproximateTangentPlane k E x P := by
  filter_upwards [hE.ae_exists_submodule_densityZeroOutsideCones hEm,
    hE.ae_eq_of_densityZeroOutsideCones hEm,
    hE.ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div hEm] with x hex huniq hdens hxE
  obtain ⟨P, hPdim, hPcone⟩ := hex hxE
  exact ⟨P, ⟨hPdim, by rw [(hdens hxE).limsup_eq]; exact zero_lt_one, hPcone⟩,
    fun Q hQ => huniq hxE Q P hQ.finrank_eq hPdim hQ.densityZeroOutsideCones hPcone⟩

/-- Almost everywhere on `E`, `approximateTangentPlane k E x` is an approximate tangent plane. -/
theorem CountablyRectifiable.ae_isApproximateTangentPlane_approximateTangentPlane :
    ∀ᵐ x ∂μHE[k], x ∈ E → IsApproximateTangentPlane k E x (approximateTangentPlane k E x) :=
  (hE.ae_existsUnique_isApproximateTangentPlane hEm).mono fun _ hx hxE =>
    isApproximateTangentPlane_approximateTangentPlane (hx hxE).exists

/-- `μHE[k].restrict E`-a.e. measurability of `approximateTangentProjection k E`. -/
theorem CountablyRectifiable.aemeasurable_approximateTangentProjection :
    AEMeasurable (approximateTangentProjection k E) (μHE[k].restrict E) := by
  obtain ⟨Q, hQm, hQ⟩ := hE.exists_measurable_approximate_tangent_projection hEm
  refine hQm.aemeasurable.congr <| (ae_restrict_iff'₀ hEm).mpr ?_
  filter_upwards [hQ, hE.ae_existsUnique_isApproximateTangentPlane hEm] with x hxQ huniq hxE
  obtain ⟨P, hPdim, hQP, hPcone⟩ := hxQ hxE; obtain ⟨P₀, hP₀, hP₀uniq⟩ := huniq hxE
  rw [hP₀.approximateTangentProjection_eq hP₀uniq,
    ← hP₀uniq P ⟨hPdim, hP₀.limsup_pos, hPcone⟩, hQP]

end Rectifiable
end TauCeti

namespace HasFDerivWithinAt
open TauCeti
variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace U]
    [BorelSpace U] [MeasurableSpace V] [BorelSpace V] {f : U → V} {s : Set U} {A : U →L[ℝ] V}
    {x₀ : U} {L : ℝ≥0} {E : Set V} {Q : Submodule ℝ V}
    (hf : HasFDerivWithinAt f A s x₀) (hinj : Injective A)
    (hi : AntilipschitzWith L (s.domRestrict f)) (hx₀ : x₀ ∈ s)
include hf hinj hi hx₀

section WithSub
variable (hsub : f '' s ⊆ E)
  (hdens : Tendsto (fun r => volume (s ∩ cb x₀ r) / volume (cb (0 : U) r)) 𝓝₊ (𝓝 1))
  (hdiff : Tendsto (fun r => μHE[finrank ℝ U] ((E \ f '' s) ∩ cb (f x₀) r) /
    ω[finrank ℝ U](r)) 𝓝₊ (𝓝 0))
include hsub hdens hdiff

/-- Characterization `IsApproximateTangentPlane (dim U) E (f x₀) Q ↔ Q = range A` on a patch. -/
theorem isApproximateTangentPlane_iff :
    IsApproximateTangentPlane (finrank ℝ U) E (f x₀) Q ↔ Q = LinearMap.range A.toLinearMap :=
  ⟨fun hQ => hf.eq_range_of_densityZeroOutsideCones hinj hi hsub hdens hQ.finrank_eq.le
      hQ.densityZeroOutsideCones,
    fun h => h ▸ ⟨LinearMap.finrank_range_of_inj hinj,
      hf.limsup_euclideanHausdorffMeasure_inter_closedBall_div_pos hi hsub hdens,
      hf.densityZeroOutsideCones_range hi hx₀ hdiff⟩⟩

/-- Formula `approximateTangentPlane (dim U) E (f x₀) = range A` on an inverse-Lipschitz patch. -/
theorem approximateTangentPlane_eq_range :
    approximateTangentPlane (finrank ℝ U) E (f x₀) = LinearMap.range A.toLinearMap := by
  have hiff := fun Q => hf.isApproximateTangentPlane_iff hinj hi hx₀ hsub hdens hdiff (Q := Q)
  exact ((hiff _).mpr rfl).approximateTangentPlane_eq fun Q hQ => (hiff Q).mp hQ

end WithSub

section ImageOnly
variable (hdens : Tendsto (fun r => volume (s ∩ cb x₀ r) / volume (cb (0 : U) r)) 𝓝₊ (𝓝 1))
include hdens

/-- Characterization of approximate tangent planes to `f '' s` at `f x₀`. -/
theorem isApproximateTangentPlane_image_iff :
    IsApproximateTangentPlane (finrank ℝ U) (f '' s) (f x₀) Q ↔
      Q = LinearMap.range A.toLinearMap :=
  hf.isApproximateTangentPlane_iff hinj hi hx₀ Subset.rfl hdens (by simp)

/-- Formula `approximateTangentPlane (dim U) (f '' s) (f x₀) = range A`. -/
theorem approximateTangentPlane_image_eq_range :
    approximateTangentPlane (finrank ℝ U) (f '' s) (f x₀) = LinearMap.range A.toLinearMap :=
  hf.approximateTangentPlane_eq_range hinj hi hx₀ Subset.rfl hdens (by simp)

end ImageOnly
end HasFDerivWithinAt
