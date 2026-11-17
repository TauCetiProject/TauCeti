/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Rectifiable.MeasurableTangent
public import Mathlib.Order.LiminfLimsup
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import TauCeti.Geometry.MeasureTheory.Rectifiable.Density
import TauCeti.Geometry.Euclidean.Volume.Density
import TauCeti.Geometry.Euclidean.Volume.Measure
import TauCeti.MeasureTheory.Function.AreaFormula.Lipschitz

/-!
# Approximate tangent planes of rectifiable sets

A countably `k`-rectifiable set with locally finite normalized Euclidean Hausdorff measure
has, almost everywhere, a unique approximate tangent `k`-plane: a `k`-plane with positive upper
`k`-dimensional density and density zero outside every cone about that plane
(`IsApproximateTangentPlane`, Mattila 15.17). Together with the density-one theorem in
`Rectifiable.Density` and bi-Lipschitz patch decomposition, this establishes a.e. existence and
uniqueness (`CountablyRectifiable.ae_existsUnique_isApproximateTangentPlane`) and defines the
canonical plane `approximateTangentPlane` (with fallback `⊥` where no plane exists) and its
orthogonal projection `approximateTangentProjection` (with fallback `0`), which is
`μHE[k].restrict E`-a.e. measurable.

The distinction from pointwise tangent cones is important: a rectifiable set can have other
patches accumulating at a point, so the whole set need not lie in a narrow cone. The canonical
approximate tangent plane and projection provide the linear domain on which tangential
derivatives and Jacobians are defined in `Rectifiable.TangentialFDeriv`. The global rectifiability
theorems assume `CountablyRectifiable k E`, `NullMeasurableSet E μHE[k]`, and
`IsLocallyFiniteMeasure (μHE[k].restrict E)`.

All densities use `μHE[k]` and the volume of a ball in `EuclideanSpace ℝ (Fin k)`; there is
no change to raw Hausdorff normalization. The result includes `k = 0`.

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
    [BorelSpace U] [MeasurableSpace V] [BorelSpace V] {f : U → V} {s : Set U} {A : U →L[ℝ] V} {x₀ :
    U} {L : ℝ≥0} {E : Set V} {Q : Submodule ℝ V}
/-- Patchwise lower bound `range A ≤ Q` on any cone-density-zero subspace `Q ≤ V`. -/
theorem range_le_of_tendsto_outside_cone (hf : HasFDerivWithinAt f A s x₀) (hi : AntilipschitzWith L
    (s.domRestrict f)) (hsub : f '' s ⊆ E) (hdens : Tendsto (fun r => volume (s ∩ cb x₀ r) / volume
    (cb (0 : U) r)) 𝓝₊ (𝓝 1)) (hQ : ∀ ε > (0 : ℝ), Tendsto (fun r => μHE[finrank ℝ U] {z ∈ E ∩ cb (f
    x₀) r | ε * dist z (f x₀) < infDist (z - f x₀) (Q : Set V)} / ω[finrank ℝ U](r)) 𝓝₊ (𝓝 0)) :
    LinearMap.range A.toLinearMap ≤ Q := by
  -- Pick a unit direction `u` with `A u ∉ Q`, so `d := infDist (A u) Q > 0`.
  by_contra hnot; obtain ⟨_, ⟨v, rfl⟩, hvQ⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  have hv0 : v ≠ 0 := fun h => hvQ (by simp [h])
  let u : U := ‖v‖⁻¹ • v; have hu : ‖u‖ = 1 := norm_smul_inv_norm hv0
  have hAu : A u ∉ Q := fun h => hvQ <| by
    simpa [u, smul_smul, norm_ne_zero_iff.mpr hv0] using Q.smul_mem ‖v‖ h
  set d := infDist (A u) (Q : Set V) with hd_def
  have hd0 : 0 < d := (Q.isClosed_of_finiteDimensional.notMem_iff_infDist_pos ⟨0, Q.zero_mem⟩).mp
    hAu
  -- Choose a shifted sub-ball scale `η` and Lipschitz factor `C = ‖A‖ + 1` so `f` sends the
  -- shifted sub-ball into `cb (f x₀) (C * ρ)` outside the `d / (16 * C)`-cone around `Q`.
  set η : ℝ := min (1 / 2) (d / (2 * (‖A‖ + 1)))
  have hη0 : 0 < η := lt_min (by norm_num) (by positivity)
  have hηA : η * ‖A‖ ≤ d / 2 := (mul_le_mul (min_le_right _ _) (le_add_of_nonneg_right zero_le_one)
    (norm_nonneg A) (by positivity)).trans_eq (by field_simp)
  let C : ℝ≥0 := ⟨‖A‖ + 1, by positivity⟩; have hC0 : 0 < C := Subtype.mk_lt_mk.mpr (by positivity)
  obtain ⟨δ, hδ, hδb⟩ := eventually_nhds_iff_ball.mp <| eventually_nhdsWithin_iff.mp <|
    hf.isLittleO.bound (by positivity : (0 : ℝ) < min 1 (d / 16))
  -- Pulling back the zero cone density contradicts non-vanishing shifted-ball density at `x₀`.
  refine not_tendsto_volume_inter_shifted_closedBall_div_zero hdens hu hη0 (min_le_left _ _) <|
    tendsto_volume_div_zero_of_antilipschitzWith hi hC0 (hQ (d / (16 * C)) (div_pos hd0 (mul_pos (by
    norm_num) (NNReal.coe_pos.2 hC0)))) ?_
  filter_upwards [Ioo_mem_nhdsGT hδ] with ρ ⟨hρ0, hρδ⟩
  rintro _ ⟨x, ⟨hxs, hxD⟩, rfl⟩
  have hy : ‖x - (x₀ + (ρ / 2) • u)‖ ≤ (η / 4) * ρ := by simpa [dist_eq_norm] using hxD
  have hdist_x : ‖x - x₀‖ ≤ ρ := by
    have h1 := (by abel : x - (x₀ + (ρ / 2) • u) + (ρ / 2) • u = x - x₀) ▸
      norm_add_le (x - (x₀ + (ρ / 2) • u)) ((ρ / 2) • u)
    rw [norm_smul, Real.norm_of_nonneg (by positivity), hu] at h1
    nlinarith [min_le_left (1 / 2) (d / (2 * (‖A‖ + 1)))]
  have herr := hδb x (mem_ball.mpr (by simpa [dist_eq_norm] using hdist_x.trans_lt hρδ)) hxs
  have herr1 : ‖f x - f x₀ - A (x - x₀)‖ ≤ ‖x - x₀‖ := by
    simpa using herr.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg _))
  have herr2 : ‖f x - f x₀ - A (x - x₀)‖ ≤ (d / 16) * ρ :=
    herr.trans ((mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)).trans (by gcongr))
  have hfx_dist : dist (f x) (f x₀) ≤ C * ρ := by
    have h1 := norm_add_le (f x - f x₀ - A (x - x₀)) (A (x - x₀)); rw [sub_add_cancel] at h1
    have hC : (C : ℝ) = ‖A‖ + 1 := rfl
    rw [dist_eq_norm]; exact h1.trans (by nlinarith [A.le_opNorm (x - x₀), norm_nonneg A])
  refine ⟨⟨hsub (mem_image_of_mem f hxs), mem_closedBall.mpr hfx_dist⟩, ?_⟩
  -- Compare `f x - f x₀` with `(ρ / 2) • A u`, whose distance to `Q` is `(ρ / 2) * d`.
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
  have hcone_lhs : (d / (16 * C)) * dist (f x) (f x₀) ≤ (d / 16) * ρ :=
    (mul_le_mul_of_nonneg_left hfx_dist (by positivity)).trans_eq
      (by have : (0 : ℝ) < C := NNReal.coe_pos.2 hC0; field_simp)
  linarith [neg_le_of_abs_le hlip, mul_pos hd0 hρ0]
/-- Patchwise uniqueness `Q = range A` when `A` is injective and `finrank ℝ Q ≤ finrank ℝ U`. -/
theorem eq_range_of_tendsto_outside_cone (hf : HasFDerivWithinAt f A s x₀) (hinj : Injective A) (hi
    : AntilipschitzWith L (s.domRestrict f)) (hsub : f '' s ⊆ E) (hdens : Tendsto (fun r => volume
    (s ∩ cb x₀ r) / volume (cb (0 : U) r)) 𝓝₊ (𝓝 1)) (hQdim : finrank ℝ Q ≤ finrank ℝ U) (hQ : ∀ ε >
    (0 : ℝ), Tendsto (fun r => μHE[finrank ℝ U] {z ∈ E ∩ cb (f x₀) r | ε * dist z (f x₀) < infDist
    (z - f x₀) (Q : Set V)} / ω[finrank ℝ U](r)) 𝓝₊ (𝓝 0)) : Q = LinearMap.range A.toLinearMap :=
    (Submodule.eq_of_le_of_finrank_le (hf.range_le_of_tendsto_outside_cone hi hsub hdens hQ)
    (hQdim.trans_eq (LinearMap.finrank_range_of_inj hinj).symm)).symm
omit [FiniteDimensional ℝ V] in
/-- Positive upper `(dim U)`-density of `E` at `f x₀` on an inverse-Lipschitz patch. -/
theorem limsup_euclideanHausdorffMeasure_inter_closedBall_div_pos (hf : HasFDerivWithinAt f A s x₀)
    (hi : AntilipschitzWith L (s.domRestrict f)) (hsub : f '' s ⊆ E) (hdens : Tendsto (fun r =>
    volume (s ∩ cb x₀ r) / volume (cb (0 : U) r)) 𝓝₊ (𝓝 1)) : 0 < limsup (fun r => μHE[finrank ℝ U]
    (E ∩ cb (f x₀) r) / ω[finrank ℝ U](r)) 𝓝₊ := by
  by_contra! hle
  let C : ℝ≥0 := ⟨‖A‖ + 1, by positivity⟩
  obtain ⟨δ, hδ, hδb⟩ := eventually_nhds_iff_ball.mp <| eventually_nhdsWithin_iff.mp <|
    hf.isLittleO.bound zero_lt_one
  refine one_ne_zero <| tendsto_nhds_unique hdens <| tendsto_volume_div_zero_of_antilipschitzWith hi
    (Subtype.mk_lt_mk.mpr (by positivity) : 0 < C)
    (tendsto_of_le_liminf_of_limsup_le zero_le (nonpos_iff_eq_zero.mp hle).le) ?_
  filter_upwards [Ioo_mem_nhdsGT hδ] with ρ ⟨_, hρδ⟩
  rintro _ ⟨x, ⟨hxs, hxB⟩, rfl⟩; refine ⟨hsub (mem_image_of_mem f hxs), mem_closedBall.mpr ?_⟩
  have herr := hδb x (mem_ball.mpr ((mem_closedBall.mp hxB).trans_lt hρδ)) hxs
  have hxρ : ‖x - x₀‖ ≤ ρ := by simpa [dist_eq_norm] using mem_closedBall.mp hxB
  have h1 := norm_add_le (f x - f x₀ - A (x - x₀)) (A (x - x₀)); rw [sub_add_cancel] at h1
  have hC : (C : ℝ) = ‖A‖ + 1 := rfl
  rw [dist_eq_norm]; exact h1.trans (by nlinarith [A.le_opNorm (x - x₀), norm_nonneg A])
omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ V] [MeasurableSpace U] [BorelSpace U] in
/-- Zero `(dim U)`-density outside every cone around `range A` on an inverse-Lipschitz patch. -/
theorem tendsto_outside_cone_range (hf : HasFDerivWithinAt f A s x₀) (hi : AntilipschitzWith L
    (s.domRestrict f)) (hx₀ : x₀ ∈ s) (hdiff : Tendsto (fun r => μHE[finrank ℝ U] ((E \ f '' s) ∩ cb
    (f x₀) r) / ω[finrank ℝ U](r)) 𝓝₊ (𝓝 0)) : ∀ ε > (0 : ℝ), Tendsto (fun r => μHE[finrank ℝ U] {z
    ∈ E ∩ cb (f x₀) r | ε * dist z (f x₀) < infDist (z - f x₀) (LinearMap.range A.toLinearMap : Set
    V)} / ω[finrank ℝ U](r)) 𝓝₊ (𝓝 0) := by
  intro ε hε; have hL1 : 0 < (L : ℝ) + 1 := by positivity
  obtain ⟨δ, hδ, hδb⟩ := eventually_nhds_iff_ball.mp <| eventually_nhdsWithin_iff.mp <|
    hf.isLittleO.bound (div_pos hε hL1)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdiff
    (.of_forall fun _ => zero_le) ?_
  filter_upwards [Ioo_mem_nhdsGT (div_pos hδ hL1)] with r ⟨_, hrδ⟩
  gcongr; rintro z ⟨⟨hzE, hzr⟩, hzcone⟩; refine ⟨⟨hzE, ?_⟩, hzr⟩; rintro ⟨x, hxs, rfl⟩
  have hdx : dist x x₀ ≤ ((L : ℝ) + 1) * dist (f x) (f x₀) := by
    have : dist x x₀ ≤ L * dist (f x) (f x₀) := by
      simpa [Subtype.dist_eq] using hi.le_mul_dist ⟨x, hxs⟩ ⟨x₀, hx₀⟩
    nlinarith [L.coe_nonneg, dist_nonneg (x := f x) (y := f x₀)]
  have hxδ : x ∈ ball x₀ δ := mem_ball.mpr <| (hdx.trans (mul_le_mul_of_nonneg_left
    (mem_closedBall.mp hzr) hL1.le)).trans_lt ((lt_div_iff₀' hL1).mp hrδ)
  refine hzcone.not_ge <| (infDist_le_dist_of_mem (⟨x - x₀, rfl⟩ : A (x - x₀) ∈ (LinearMap.range
    A.toLinearMap : Set V))).trans <| by
      rw [dist_eq_norm]
      exact (hδb x hxδ hxs).trans <| (mul_le_mul_of_nonneg_left (dist_eq_norm x x₀ ▸ hdx)
        (div_nonneg hε.le hL1.le)).trans_eq (by rw [← mul_assoc, div_mul_cancel₀ _ hL1.ne'])
end HasFDerivWithinAt
namespace TauCeti
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {k : ℕ} {E E₁ E₂ : Set V}
/-- `P` is an approximate tangent `k`-plane to `E` at `x` (Mattila, Definition 15.17). -/
structure IsApproximateTangentPlane (k : ℕ) (E : Set V) (x : V) (P : Submodule ℝ V) : Prop where
  /-- `P` has dimension `k`. -/
  finrank_eq : finrank ℝ P = k
  /-- `E` has positive upper `k`-dimensional density at `x`. -/
  limsup_pos : 0 < limsup (fun r => μHE[k] (E ∩ cb x r) / ω[k](r)) 𝓝₊
  /-- Outside every cone around `P`, `E` has `k`-dimensional density zero at `x`. -/
  tendsto_outside_cone : ∀ ε > (0 : ℝ), Tendsto (fun r =>
    μHE[k] {z ∈ E ∩ cb x r | ε * dist z x < infDist (z - x) (P : Set V)} / ω[k](r)) 𝓝₊ (𝓝 0)
namespace IsApproximateTangentPlane
/-- In dimension zero, any approximate tangent plane is `⊥`. -/
theorem eq_bot {x : V} {P : Submodule ℝ V} (h : IsApproximateTangentPlane 0 E x P) : P = ⊥ := by
  have := finrank_zero_iff.mp h.finrank_eq; exact Submodule.eq_bot_of_subsingleton
omit [FiniteDimensional ℝ V] in
private lemma of_eventually_eq_measure {x : V} {P : Submodule ℝ V} (hb : ∀ᶠ r in 𝓝[>] (0 : ℝ),
    μHE[k] (E₁ ∩ cb x r) = μHE[k] (E₂ ∩ cb x r)) (hc : ∀ ε, ∀ᶠ r in 𝓝[>] (0 : ℝ), μHE[k] {z ∈ E₁ ∩
    cb x r | ε * dist z x < infDist (z - x) (P : Set V)} = μHE[k] {z ∈ E₂ ∩ cb x r | ε * dist z x <
    infDist (z - x) (P : Set V)}) (h : IsApproximateTangentPlane k E₁ x P) :
    IsApproximateTangentPlane k E₂ x P :=
  ⟨h.1, (limsup_congr (hb.mono fun _ hr => congrArg (· / _) hr)).symm ▸ h.2,
    fun ε hε => (h.3 ε hε).congr' ((hc ε).mono fun _ hr => by rw [hr])⟩
omit [FiniteDimensional ℝ V] in
/-- Modifying `E` by a `μHE[k]`-null set preserves approximate tangent planes at `x`. -/
theorem congr_ae (h : E₁ =ᵐ[μHE[k]] E₂) {x : V} {P : Submodule ℝ V} : IsApproximateTangentPlane k E₁
    x P ↔ IsApproximateTangentPlane k E₂ x P :=
  have go {A B : Set V} (hab : A =ᵐ[μHE[k]] B) := of_eventually_eq_measure (x := x) (P := P)
    (.of_forall fun _ => measure_congr (hab.inter .rfl)) fun _ => .of_forall fun _ =>
      measure_congr (hab.mono fun _ hz => and_congr_left' (and_congr_left' hz))
  ⟨go h, go h.symm⟩
omit [FiniteDimensional ℝ V] in
/-- Approximate tangent planes depend only on the germ of `E` at `x`. -/
theorem congr_nhds {x : V} (h : E₁ =ᶠ[𝓝 x] E₂) {P : Submodule ℝ V} : IsApproximateTangentPlane k E₁
    x P ↔ IsApproximateTangentPlane k E₂ x P := by
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
noncomputable def approximateTangentPlane (k : ℕ) (E : Set V) (x : V) : Submodule ℝ V := if h : ∃ P
    : Submodule ℝ V, IsApproximateTangentPlane k E x P then h.choose else ⊥
/-- Orthogonal projection onto `TauCeti.approximateTangentPlane k E x`. -/
noncomputable def approximateTangentProjection (k : ℕ) (E : Set V) (x : V) : V →L[ℝ] V :=
    (approximateTangentPlane k E x).starProjection
/-- Unfolding lemma for `approximateTangentProjection k E x`. -/
theorem approximateTangentProjection_eq (k : ℕ) (E : Set V) (x : V) :
    approximateTangentProjection k E x = (approximateTangentPlane k E x).starProjection := by rfl
omit [FiniteDimensional ℝ V] in
/-- Uniqueness identifies `approximateTangentPlane k E x` with `P`. -/
theorem IsApproximateTangentPlane.approximateTangentPlane_eq {x : V} {P : Submodule ℝ V} (hP :
    IsApproximateTangentPlane k E x P) (huniq : ∀ Q, IsApproximateTangentPlane k E x Q → Q = P) :
    approximateTangentPlane k E x = P := by
  have hex : ∃ Q, IsApproximateTangentPlane k E x Q := ⟨P, hP⟩
  simp only [approximateTangentPlane, hex, ↓reduceDIte]; exact huniq _ hex.choose_spec
/-- Uniqueness identifies `approximateTangentProjection k E x` with `P.starProjection`. -/
theorem IsApproximateTangentPlane.approximateTangentProjection_eq {x : V} {P : Submodule ℝ V} (hP :
    IsApproximateTangentPlane k E x P) (huniq : ∀ Q, IsApproximateTangentPlane k E x Q → Q = P) :
    approximateTangentProjection k E x = P.starProjection := by
  simp only [approximateTangentProjection, hP.approximateTangentPlane_eq huniq]
omit [FiniteDimensional ℝ V] in
/-- Specification of `approximateTangentPlane k E x` when a plane exists. -/
theorem isApproximateTangentPlane_approximateTangentPlane {x : V} (h : ∃ P : Submodule ℝ V,
    IsApproximateTangentPlane k E x P) : IsApproximateTangentPlane k E x (approximateTangentPlane k
    E x) := by simp only [approximateTangentPlane, h, ↓reduceDIte]; exact h.choose_spec
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
/-- Null-set invariance of `approximateTangentPlane`. -/
theorem approximateTangentPlane_congr_ae (h : E₁ =ᵐ[μHE[k]] E₂) (x : V) :
    approximateTangentPlane k E₁ x = approximateTangentPlane k E₂ x :=
  congrArg (fun p : Submodule ℝ V → Prop => by classical exact if h : ∃ P, p P then h.choose else ⊥)
    (funext fun _ => propext (IsApproximateTangentPlane.congr_ae h))
/-- Null-set invariance of `approximateTangentProjection`. -/
theorem approximateTangentProjection_congr_ae (h : E₁ =ᵐ[μHE[k]] E₂) (x : V) :
    approximateTangentProjection k E₁ x = approximateTangentProjection k E₂ x := by
  simp only [approximateTangentProjection, approximateTangentPlane_congr_ae h]
omit [FiniteDimensional ℝ V] in
/-- Germ invariance of `approximateTangentPlane`. -/
theorem approximateTangentPlane_congr_nhds {x : V} (h : E₁ =ᶠ[𝓝 x] E₂) :
    approximateTangentPlane k E₁ x = approximateTangentPlane k E₂ x :=
  congrArg (fun p : Submodule ℝ V → Prop => by classical exact if h : ∃ P, p P then h.choose else ⊥)
    (funext fun _ => propext (IsApproximateTangentPlane.congr_nhds h))
/-- Germ invariance of `approximateTangentProjection`. -/
theorem approximateTangentProjection_congr_nhds {x : V} (h : E₁ =ᶠ[𝓝 x] E₂) :
    approximateTangentProjection k E₁ x = approximateTangentProjection k E₂ x := by
  simp only [approximateTangentProjection, approximateTangentPlane_congr_nhds h]
section Rectifiable
variable (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k]) [IsLocallyFiniteMeasure
    (μHE[k].restrict E)]
include hE hEm
/-- Almost-everywhere existence of a cone-density-zero `k`-plane on a rectifiable set. -/
theorem CountablyRectifiable.ae_exists_submodule_tendsto_measure_outside_cone_div : ∀ᵐ x ∂μHE[k], x
    ∈ E → ∃ P : Submodule ℝ V, finrank ℝ P = k ∧ ∀ ε > (0 : ℝ), Tendsto (fun r => μHE[k] {z ∈ E ∩ cb
    x r | ε * dist z x < infDist (z - x) (P : Set V)} / ω[k](r)) 𝓝₊ (𝓝 0) :=
  let ⟨_, _, hQ⟩ := hE.exists_measurable_approximate_tangent_projection hEm
  hQ.mono fun _ hx hxE => let ⟨P, hdim, _, hP⟩ := hx hxE; ⟨P, hdim, hP⟩
/-- Almost-everywhere existence and uniqueness of the cone-density-zero `k`-plane. -/
theorem CountablyRectifiable.ae_existsUnique_submodule_tendsto_measure_outside_cone_div : ∀ᵐ x
    ∂μHE[k], x ∈ E → ∃! P : Submodule ℝ V, finrank ℝ P = k ∧ ∀ ε > (0 : ℝ), Tendsto (fun r => μHE[k]
    {z ∈ E ∩ cb x r | ε * dist z x < infDist (z - x) (P : Set V)} / ω[k](r)) 𝓝₊ (𝓝 0) := by
  let U := EuclideanSpace ℝ (Fin k); obtain ⟨A, f, _, hbi, hcover⟩ := hE.exists_bilipschitz_cover
  choose K L hLip hAnti using hbi; let s (n : ℕ) : Set U := A n ∩ (f n) ⁻¹' E
  have hpatch (n : ℕ) : ∀ᵐ x ∂μHE[k], x ∈ f n '' s n → ∃ u ∈ s n, f n u = x ∧ DifferentiableAt ℝ (f
    n) u ∧ Injective (fderiv ℝ (f n) u) ∧ Tendsto (fun r => volume (s n ∩ cb u r) / volume (cb (0 :
    U) r)) 𝓝₊ (𝓝 1) := by
    let S := {u | ¬ Tendsto (fun r => volume (s n ∩ cb u r) / volume (cb u r)) (𝓝[>] 0) (𝓝 1)}
    have hbadD : μHE[k] (f n '' (S ∩ s n)) = 0 := by
      have hv : volume (S ∩ s n) = 0 := nonpos_iff_eq_zero.mp <| (le_restrict_apply (s n) S
        ).trans_eq (ae_iff.mp (Besicovitch.ae_tendsto_measure_inter_div volume (s n)))
      simpa only [U, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, hv, mul_zero,
        nonpos_iff_eq_zero] using (hLip n).lipschitzOnWith.euclideanHausdorffMeasure_image_le k (s
        := S ∩ s n)
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hbadD, measure_eq_zero_iff_ae_notMem.mp
      (by simpa only [finrank_euclideanSpace_fin] using (hLip
        n).euclideanHausdorffMeasure_image_compl_setOf_regular)] with x hxD hxR
    rintro ⟨u, hu, rfl⟩; obtain ⟨hd, hdet⟩ := not_not.mp fun h => hxR ⟨u, h, rfl⟩
    exact ⟨u, hu, rfl, hd, ((fderiv ℝ (f n) u).toLinearMap.normDet_ne_zero_tfae.out 1 5).mp hdet,
      by simpa only [addHaar_closedBall_center] using not_not.mp fun h => hxD ⟨u, ⟨h, hu⟩, rfl⟩⟩
  filter_upwards [hE.ae_exists_submodule_tendsto_measure_outside_cone_div hEm,
    measure_eq_zero_iff_ae_notMem.mp hcover, ae_all_iff.mpr hpatch] with x hex hcov hxpatch hxE
  obtain ⟨P, hPdim, hPcone⟩ := hex hxE
  obtain ⟨n, u, huA, rfl⟩ := mem_iUnion.mp (not_not.mp fun h => hcov ⟨hxE, h⟩)
  obtain ⟨u', _, hfu', hdiff, hinj, hdens⟩ := hxpatch n ⟨u, ⟨huA, hxE⟩, rfl⟩
  have heq {S : Submodule ℝ V} (hSdim : finrank ℝ S = k) (hScone : ∀ ε > (0 : ℝ), Tendsto (fun r =>
      μHE[k] {z ∈ E ∩ cb (f n u') r | ε * dist z (f n u') < infDist (z - f n u') S} / ω[k](r)) 𝓝₊
      (𝓝 0)) : S = LinearMap.range (fderiv ℝ (f n) u').toLinearMap :=
    (hdiff.hasFDerivAt.hasFDerivWithinAt (s := A n ∩ f n ⁻¹' E)).eq_range_of_tendsto_outside_cone
      hinj (fun a b => hAnti n ⟨a, a.2.1⟩ ⟨b, b.2.1⟩) (by rintro _ ⟨_, hu, rfl⟩; exact hu.2) hdens
      (by simpa only [U, finrank_euclideanSpace_fin] using hSdim.le) fun ε hε => by
        simpa only [U, finrank_euclideanSpace_fin, ← volume_closedBall_eq_euclidean (0 : U)] using
          hScone ε hε
  exact ⟨P, ⟨hPdim, hPcone⟩, fun Q ⟨hQdim, hQcone⟩ =>
    (heq hQdim (hfu'.symm ▸ hQcone)).trans (heq hPdim (hfu'.symm ▸ hPcone)).symm⟩
/-- Almost-everywhere existence and uniqueness of approximate tangent `k`-planes. -/
theorem CountablyRectifiable.ae_existsUnique_isApproximateTangentPlane : ∀ᵐ x ∂μHE[k], x ∈ E → ∃! P
    : Submodule ℝ V, IsApproximateTangentPlane k E x P := by
  filter_upwards [hE.ae_existsUnique_submodule_tendsto_measure_outside_cone_div hEm,
    hE.ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div hEm] with x huniq hdens hxE
  obtain ⟨P, ⟨hPdim, hPcone⟩, hPuniq⟩ := huniq hxE
  exact ⟨P, ⟨hPdim, by rw [(hdens hxE).limsup_eq]; exact zero_lt_one, hPcone⟩,
    fun Q hQ => hPuniq Q ⟨hQ.finrank_eq, hQ.tendsto_outside_cone⟩⟩
/-- Almost everywhere on `E`, `approximateTangentPlane k E x` is an approximate tangent plane. -/
theorem CountablyRectifiable.ae_isApproximateTangentPlane_approximateTangentPlane : ∀ᵐ x ∂μHE[k], x
    ∈ E → IsApproximateTangentPlane k E x (approximateTangentPlane k E x) :=
    (hE.ae_existsUnique_isApproximateTangentPlane hEm).mono fun _ hx hxE =>
    isApproximateTangentPlane_approximateTangentPlane (hx hxE).exists
/-- `μHE[k].restrict E`-a.e. measurability of `approximateTangentProjection k E`. -/
theorem CountablyRectifiable.aemeasurable_approximateTangentProjection : AEMeasurable
    (approximateTangentProjection k E) (μHE[k].restrict E) := by
  obtain ⟨Q, hQm, hQ⟩ := hE.exists_measurable_approximate_tangent_projection hEm
  refine hQm.aemeasurable.congr <| (ae_restrict_iff'₀ hEm).mpr ?_
  filter_upwards [hQ, hE.ae_existsUnique_isApproximateTangentPlane hEm] with x hxQ huniq hxE
  obtain ⟨P, hPdim, hQP, hPcone⟩ := hxQ hxE; obtain ⟨P₀, hP₀, hP₀uniq⟩ := huniq hxE
  rw [hP₀.approximateTangentProjection_eq hP₀uniq, ← hP₀uniq P ⟨hPdim, hP₀.limsup_pos, hPcone⟩, hQP]
end Rectifiable
end TauCeti
namespace HasFDerivWithinAt
open TauCeti
variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace U]
    [BorelSpace U] [MeasurableSpace V] [BorelSpace V] {f : U → V} {s : Set U} {A : U →L[ℝ] V} {x₀ :
    U} {L : ℝ≥0} {E : Set V} {Q : Submodule ℝ V} (hf : HasFDerivWithinAt f A s x₀) (hinj : Injective
    A) (hi : AntilipschitzWith L (s.domRestrict f)) (hx₀ : x₀ ∈ s)
include hf hinj hi hx₀
section WithSub
variable (hsub : f '' s ⊆ E) (hdens : Tendsto (fun r => volume (s ∩ cb x₀ r) / volume (cb (0 : U)
    r)) 𝓝₊ (𝓝 1)) (hdiff : Tendsto (fun r => μHE[finrank ℝ U] ((E \ f '' s) ∩ cb (f x₀) r) /
    ω[finrank ℝ U](r)) 𝓝₊ (𝓝 0))
include hsub hdens hdiff
/-- Characterization `IsApproximateTangentPlane (dim U) E (f x₀) Q ↔ Q = range A` on a patch. -/
theorem isApproximateTangentPlane_iff : IsApproximateTangentPlane (finrank ℝ U) E (f x₀) Q ↔ Q =
    LinearMap.range A.toLinearMap := ⟨fun hQ => hf.eq_range_of_tendsto_outside_cone hinj hi hsub
    hdens hQ.finrank_eq.le hQ.tendsto_outside_cone, fun h => h ▸ ⟨LinearMap.finrank_range_of_inj
    hinj, hf.limsup_euclideanHausdorffMeasure_inter_closedBall_div_pos hi hsub hdens,
    hf.tendsto_outside_cone_range hi hx₀ hdiff⟩⟩
/-- Formula `approximateTangentPlane (dim U) E (f x₀) = range A` on an inverse-Lipschitz patch. -/
theorem approximateTangentPlane_eq_range : approximateTangentPlane (finrank ℝ U) E (f x₀) =
    LinearMap.range A.toLinearMap := by
  have hiff := fun Q => hf.isApproximateTangentPlane_iff hinj hi hx₀ hsub hdens hdiff (Q := Q)
  exact ((hiff _).mpr rfl).approximateTangentPlane_eq fun Q hQ => (hiff Q).mp hQ
end WithSub
section ImageOnly
variable (hdens : Tendsto (fun r => volume (s ∩ cb x₀ r) / volume (cb (0 : U) r)) 𝓝₊ (𝓝 1))
include hdens
/-- Characterization of approximate tangent planes to `f '' s` at `f x₀`. -/
theorem isApproximateTangentPlane_image_iff : IsApproximateTangentPlane (finrank ℝ U) (f '' s) (f
    x₀) Q ↔ Q = LinearMap.range A.toLinearMap := hf.isApproximateTangentPlane_iff hinj hi hx₀
    Subset.rfl hdens (by simp)
/-- Formula `approximateTangentPlane (dim U) (f '' s) (f x₀) = range A`. -/
theorem approximateTangentPlane_image_eq_range : approximateTangentPlane (finrank ℝ U) (f '' s) (f
    x₀) = LinearMap.range A.toLinearMap := hf.approximateTangentPlane_eq_range hinj hi hx₀
    Subset.rfl hdens (by simp)
end ImageOnly
end HasFDerivWithinAt
