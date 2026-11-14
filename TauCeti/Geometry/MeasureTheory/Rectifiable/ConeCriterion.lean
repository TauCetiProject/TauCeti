/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Rectifiable.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
import TauCeti.Geometry.MeasureTheory.Rectifiable.Subspace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# The geometric cone criterion for countable rectifiability

If the difference vectors of a subset `s` of a real inner product space `V` form an angle bounded
away from zero with the orthogonal complement of a fixed `d`-dimensional subspace `P` — concretely,
`infDist (y - x) P ≤ θ ‖y - x‖` for some `θ < 1` and all `x, y ∈ s` — then orthogonal projection
onto `P` has a Lipschitz inverse on its image, so `s` is countably `d`-rectifiable
(`TauCeti.CountablyRectifiable.of_forall_infDist_sub_le`).

When `V` is second-countable, the subspace `P`, the cone constant `θ < 1`, and a neighbourhood
radius `r > 0` may vary from point to point
(`TauCeti.CountablyRectifiable.of_forall_exists_submodule_infDist_sub_le`).
Stratifying by the dimension `d ≤ k` of `P`, a lower bound `1 / (m + 1)` on `r`, and an upper bound
`1 - 1 / (l + 2)` on `θ`, we choose an orthonormal basis in `Fin d → V` for each point's subspace.
Because `u ↦ ∑ i, rankOne ℝ (u i) (u i)` is continuous from the second-countable space `Fin d → V`
into `V →L[ℝ] V`, countably many reference subspaces approximate all projections in the stratum
within `(1 - θ_l) / 2` in operator norm; subdividing further into balls of radius `1 / (2 (m + 1))`
ensures that every pair of points in a piece lies within the local radius of each, reducing each
piece to the single-cone lemma. Ambient finite dimensionality is not required.

In a finite-dimensional inner product space `V`, taking `P = (ℝ ∙ ν)ᗮ` for a nonzero normal `ν`
yields the codimension-one cone criterion
(`TauCeti.CountablyRectifiable.of_forall_exists_abs_inner_sub_le`).

## Main statements

* `TauCeti.CountablyRectifiable.of_forall_infDist_sub_le`: a set whose secants satisfy
  `infDist (y - x) P ≤ θ ‖y - x‖` (`θ < 1`) for a fixed finite-dimensional subspace `P` is
  countably `(dim P)`-rectifiable.
* `TauCeti.CountablyRectifiable.of_forall_exists_submodule_infDist_sub_le`: the local pointwise cone
  criterion in any second-countable real inner product space.
* `TauCeti.CountablyRectifiable.of_forall_exists_abs_inner_sub_le`: the codimension-one normal cone
  criterion in a finite-dimensional real inner product space.

## References

* H. Federer, *Geometric Measure Theory*, 3.3.5 and 3.3.13.
* L. Simon, *Lectures on Geometric Measure Theory*, §11, Lemma 11.1.
* P. Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Lemma 15.13 and Theorem 15.21.
-/

public section

open Metric Module Set TopologicalSpace
open scoped NNReal RealInnerProductSpace

namespace TauCeti

namespace CountablyRectifiable

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- **Single-cone rectifiability.** If `P` is a finite-dimensional subspace of a real inner product
space `V`, `θ < 1`, and `infDist (y - x) P ≤ θ ‖y - x‖` for all `x, y ∈ s`, then `s` is countably
`(dim P)`-rectifiable: orthogonal projection onto `P` is antilipschitz on `s`, so `s` is a Lipschitz
image of a subset of `P`. -/
theorem of_forall_infDist_sub_le {s : Set V} (P : Submodule ℝ V) [FiniteDimensional ℝ P]
    {θ : ℝ} (hθ : θ < 1)
    (hs : ∀ x ∈ s, ∀ y ∈ s, infDist (y - x) (P : Set V) ≤ θ * ‖y - x‖) :
    CountablyRectifiable (finrank ℝ P) s := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact empty
  set θ' : ℝ := max θ 0
  have hθ'1 : 0 < 1 - θ' := sub_pos.2 (max_lt hθ zero_lt_one)
  let c : ℝ≥0 := ⟨1 - θ', hθ'1.le⟩
  let f : s → P := s.domRestrict P.orthogonalProjectionOnto
  have hanti : AntilipschitzWith c⁻¹ f := by
    refine AntilipschitzWith.of_le_mul_dist fun x y ↦ ?_
    rw [NNReal.coe_inv, ← div_eq_inv_mul]
    change dist x y ≤ dist (f x) (f y) / (1 - θ')
    rw [le_div_iff₀' hθ'1]
    have hdist : ‖(y : V) - x - P.starProjection ((y : V) - x)‖ ≤ θ' * ‖(y : V) - x‖ := by
      rw [← dist_eq_norm, P.dist_starProjection_eq_infDist]
      exact (hs x x.2 y y.2).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    have htri : ‖(y : V) - x‖ ≤
        ‖P.starProjection ((y : V) - x)‖ + ‖(y : V) - x - P.starProjection ((y : V) - x)‖ := by
      simpa only [add_sub_cancel] using norm_add_le (P.starProjection ((y : V) - x))
        ((y : V) - x - P.starProjection ((y : V) - x))
    have hproj : ‖P.starProjection ((y : V) - x)‖ = dist (f y) (f x) := by
      simp [f, ← map_sub, dist_eq_norm]
    rw [Subtype.dist_eq, dist_eq_norm (x : V), norm_sub_rev (x : V), dist_comm (f x)]
    linarith
  have : Nonempty s := hne.to_subtype
  have hinv : RightInvOn (Function.invFun f) f (range f) :=
    fun _ hy ↦ Function.invFun_eq hy
  have hlip : LipschitzOnWith c⁻¹ (Subtype.val ∘ Function.invFun f) (range f) := by
    simpa only [one_mul] using (LipschitzWith.subtype_val s).comp_lipschitzOnWith
      (lipschitzOnWith_iff_restrict.2 (hanti.to_rightInvOn hinv))
  have himg : (Subtype.val ∘ Function.invFun f) '' range f = s := by
    ext z
    simp only [mem_image, mem_range, Function.comp_apply, exists_exists_eq_and]
    refine ⟨by rintro ⟨x, rfl⟩; rw [Function.leftInverse_invFun hanti.injective x]; exact x.2,
      fun hz ↦ ⟨⟨z, hz⟩, by rw [Function.leftInverse_invFun hanti.injective ⟨z, hz⟩]⟩⟩
  rw [← himg]
  exact (of_finiteDimensional (range f)).image hlip

omit [MeasurableSpace V] [BorelSpace V] in
/-- Perturbing a subspace `P₁` to `P₂` within `ε` in projection operator norm increases the relative
distance of a vector `w` to the subspace by at most `ε`. -/
private theorem infDist_le_of_opNorm_starProjection_sub_le
    {P₁ P₂ : Submodule ℝ V} [P₁.HasOrthogonalProjection] [P₂.HasOrthogonalProjection]
    {w : V} {θ₀ ε : ℝ} (hw : infDist w (P₁ : Set V) ≤ θ₀ * ‖w‖)
    (hdiff : ‖P₁.starProjection - P₂.starProjection‖ ≤ ε) :
    infDist w (P₂ : Set V) ≤ (θ₀ + ε) * ‖w‖ := by
  have hw' : ‖w - P₁.starProjection w‖ ≤ θ₀ * ‖w‖ := by
    rwa [← dist_eq_norm, P₁.dist_starProjection_eq_infDist]
  have hvec : ‖P₁.starProjection w - P₂.starProjection w‖ ≤ ε * ‖w‖ := by
    simpa only [sub_apply] using (P₁.starProjection - P₂.starProjection).le_of_opNorm_le hdiff w
  rw [← P₂.dist_starProjection_eq_infDist, dist_eq_norm]
  calc ‖w - P₂.starProjection w‖
      ≤ ‖w - P₁.starProjection w‖ + ‖P₁.starProjection w - P₂.starProjection w‖ := by
        simpa only [sub_add_sub_cancel] using
          norm_add_le (w - P₁.starProjection w) (P₁.starProjection w - P₂.starProjection w)
    _ ≤ θ₀ * ‖w‖ + ε * ‖w‖ := add_le_add hw' hvec
    _ = (θ₀ + ε) * ‖w‖ := (add_mul θ₀ ε ‖w‖).symm

/-- On a stratum where every point `x ∈ T` has a `d`-dimensional subspace `P x`, radius at least
`r₀ > 0`, and cone constant at most `θ₀ < 1`, the set `T` is countably `d`-rectifiable. -/
private theorem of_stratum [SecondCountableTopology V] {d : ℕ} {T : Set V}
    {P : T → Submodule ℝ V} [∀ x, FiniteDimensional ℝ (P x)] (hdim : ∀ x, finrank ℝ (P x) = d)
    {r₀ θ₀ : ℝ} (hr₀ : 0 < r₀) (hθ₀ : θ₀ < 1)
    (hcone : ∀ x : T, ∀ y ∈ T, dist y x.1 < r₀ →
      infDist (y - x.1) (P x : Set V) ≤ θ₀ * dist y x.1) :
    CountablyRectifiable d T := by
  classical
  let b (x : T) : OrthonormalBasis (Fin d) ℝ (P x) :=
    (stdOrthonormalBasis ℝ (P x)).reindex (finCongr (hdim x))
  let u (x : T) : Fin d → V := fun i ↦ b x i
  let Φ : (Fin d → V) → (V →L[ℝ] V) := fun v ↦ ∑ i : Fin d, InnerProductSpace.rankOne ℝ (v i) (v i)
  have hΦ : Continuous Φ := continuous_finsetSum _ fun i _ ↦
    ((InnerProductSpace.rankOne ℝ).continuous.comp (continuous_apply i)).clm_apply
      (continuous_apply i)
  set ε : ℝ := (1 - θ₀) / 2
  obtain ⟨U, hU_sub, hU_cnt, hU_cov⟩ := countable_cover_nhdsWithin (s := range u)
    (f := fun v ↦ Φ ⁻¹' ball (Φ v) ε) fun v _ ↦ nhdsWithin_le_nhds
      (hΦ.continuousAt.preimage_mem_nhds (ball_mem_nhds _ (half_pos (sub_pos.2 hθ₀))))
  have := hU_cnt.to_subtype
  choose x₀ hx₀ using fun v : U ↦ hU_sub v.2
  let S (v : U) : Set V := {y : V | ∃ hy : y ∈ T, u ⟨y, hy⟩ ∈ Φ ⁻¹' ball (Φ v.1) ε}
  have hT_eq : T = ⋃ v : U, S v := by
    ext y
    simp only [S, mem_iUnion, mem_ofPred_eq]
    refine ⟨fun hy ↦ ?_, fun ⟨_, hy, _⟩ ↦ hy⟩
    obtain ⟨w, hwU, hwu⟩ := mem_iUnion₂.1 (hU_cov (mem_range_self ⟨y, hy⟩))
    exact ⟨⟨w, hwU⟩, hy, hwu⟩
  rw [hT_eq]
  refine CountablyRectifiable.iUnion fun v : U ↦ ?_
  obtain ⟨C, _, hC_cnt, hC_cov⟩ := countable_cover_nhdsWithin (s := S v)
    (f := fun z ↦ ball z (r₀ / 2)) fun z _ ↦ nhdsWithin_le_nhds (ball_mem_nhds z (half_pos hr₀))
  have := hC_cnt.to_subtype
  have hSv_eq : S v = ⋃ z : C, S v ∩ ball z.1 (r₀ / 2) := by
    ext y; simp only [mem_iUnion, mem_inter_iff]
    exact ⟨fun hy ↦ let ⟨z, hzC, hyz⟩ := mem_iUnion₂.1 (hC_cov hy); ⟨⟨z, hzC⟩, hy, hyz⟩,
      fun ⟨_, hy, _⟩ ↦ hy⟩
  rw [hSv_eq, ← hdim (x₀ v)]
  refine CountablyRectifiable.iUnion fun z : C ↦
    of_forall_infDist_sub_le (P (x₀ v)) (θ := θ₀ + ε) (by simp [ε]; linarith) fun p hp q hq ↦ ?_
  obtain ⟨hpT, hpu⟩ := hp.1
  have hpq : dist q p < r₀ := (dist_triangle_right q p z.1).trans_lt
    ((add_lt_add hq.2 hp.2).trans_eq (add_halves r₀))
  have hdiff : ‖(P ⟨p, hpT⟩).starProjection - (P (x₀ v)).starProjection‖ ≤ ε := by
    rw [(b ⟨p, hpT⟩).starProjection_eq_sum_rankOne, (b (x₀ v)).starProjection_eq_sum_rankOne]
    change ‖Φ (u ⟨p, hpT⟩) - Φ (u (x₀ v))‖ ≤ ε
    rw [hx₀ v, ← dist_eq_norm]
    exact (mem_ball.1 hpu).le
  exact infDist_le_of_opNorm_starProjection_sub_le
    (by simpa only [dist_eq_norm] using hcone ⟨p, hpT⟩ q hq.1.1 hpq) hdiff

/-- **The geometric cone criterion for countable rectifiability.** Let `V` be a second-countable
real inner product space and `s ⊆ V`. If for every `x ∈ s` there exist a subspace `P` of dimension
at most `k`, a constant `θ < 1`, and a radius `r > 0` such that `infDist (y - x) P ≤ θ * dist y x`
for all `y ∈ s ∩ ball x r`, then `s` is countably `k`-rectifiable. -/
theorem of_forall_exists_submodule_infDist_sub_le [SecondCountableTopology V] {k : ℕ} {s : Set V}
    (h : ∀ x ∈ s, ∃ P : Submodule ℝ V, FiniteDimensional ℝ P ∧ finrank ℝ P ≤ k ∧
      ∃ θ < (1 : ℝ), ∃ r > (0 : ℝ),
        ∀ y ∈ s, dist y x < r → infDist (y - x) (P : Set V) ≤ θ * dist y x) :
    CountablyRectifiable k s := by
  classical
  choose P hPfin hPdim θ hθ r hr hcone using fun x : s ↦ h x.1 x.2
  let r₀ (m : ℕ) : ℝ := 1 / ((m : ℝ) + 1)
  let θ₀ (l : ℕ) : ℝ := 1 - 1 / ((l : ℝ) + 2)
  let T (d : Fin (k + 1)) (m l : ℕ) : Set V :=
    {x : V | ∃ hx : x ∈ s, finrank ℝ (P ⟨x, hx⟩) = d.1 ∧ r₀ m ≤ r ⟨x, hx⟩ ∧ θ ⟨x, hx⟩ ≤ θ₀ l}
  have hs_eq : s = ⋃ (d : Fin (k + 1)) (m : ℕ) (l : ℕ), T d m l := by
    ext x
    simp only [T, mem_iUnion, mem_ofPred_eq]
    refine ⟨fun hx ↦ ?_, fun ⟨_, _, _, hx, _⟩ ↦ hx⟩
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (hr ⟨x, hx⟩)
    obtain ⟨l, hl⟩ := exists_nat_one_div_lt (sub_pos.2 (hθ ⟨x, hx⟩))
    refine ⟨⟨finrank ℝ (P ⟨x, hx⟩), Nat.lt_succ_of_le (hPdim ⟨x, hx⟩)⟩, m, l, hx, rfl, hm.le, ?_⟩
    have hl' : 1 / ((l : ℝ) + 2) < 1 - θ ⟨x, hx⟩ :=
      lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) (by linarith)) hl
    linarith [show θ₀ l = 1 - 1 / ((l : ℝ) + 2) from rfl]
  rw [hs_eq]
  refine CountablyRectifiable.iUnion fun d ↦ CountablyRectifiable.iUnion fun m ↦
    CountablyRectifiable.iUnion fun l ↦ ?_
  have hr₀ : 0 < r₀ m := Nat.one_div_pos_of_nat
  have hθ₀ : θ₀ l < 1 := sub_lt_self 1 (by positivity)
  let P' (x : T d m l) : Submodule ℝ V := P ⟨x.1, x.2.choose⟩
  have hP'fin (x : T d m l) : FiniteDimensional ℝ (P' x) := hPfin ⟨x.1, x.2.choose⟩
  have hP'dim (x : T d m l) : finrank ℝ (P' x) = d.1 := x.2.choose_spec.1
  refine (of_stratum (P := P') hP'dim hr₀ hθ₀ fun x y hy hyx ↦ ?_).mono_dim
    (Nat.lt_succ_iff.1 d.2)
  obtain ⟨hrx, hθx⟩ := x.2.choose_spec.2
  exact (hcone ⟨x.1, x.2.choose⟩ y hy.choose (hyx.trans_le hrx)).trans
    (mul_le_mul_of_nonneg_right hθx dist_nonneg)

/-- **The codimension-one cone criterion.** In a finite-dimensional real inner product space `V`, if
at every `x ∈ s` there exist a nonzero vector `ν`, a constant `θ < 1`, and a radius `r > 0` such
that `|⟪y - x, ν⟫| ≤ θ * ‖y - x‖ * ‖ν‖` for all `y ∈ s ∩ ball x r`, then `s` is countably
`(dim V - 1)`-rectifiable. -/
theorem of_forall_exists_abs_inner_sub_le [FiniteDimensional ℝ V] {s : Set V}
    (h : ∀ x ∈ s, ∃ ν : V, ν ≠ 0 ∧ ∃ θ < (1 : ℝ), ∃ r > (0 : ℝ),
      ∀ y ∈ s, dist y x < r → |⟪y - x, ν⟫| ≤ θ * ‖y - x‖ * ‖ν‖) :
    CountablyRectifiable (finrank ℝ V - 1) s := by
  refine of_forall_exists_submodule_infDist_sub_le fun x hx ↦ ?_
  obtain ⟨ν, hν, θ, hθ, r, hr, hcone⟩ := h x hx
  let P : Submodule ℝ V := (ℝ ∙ ν)ᗮ
  have hdim : finrank ℝ P = finrank ℝ V - 1 := by
    have hsum := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ ν)
    rw [finrank_span_singleton hν] at hsum
    exact Nat.eq_sub_of_add_eq' hsum
  refine ⟨P, inferInstance, hdim.le, θ, hθ, r, hr, fun y hy hyr ↦ ?_⟩
  have hν_pos : 0 < ‖ν‖ := norm_pos_iff.2 hν
  set u : V := ‖ν‖⁻¹ • ν
  have hp_mem : (y - x) - ⟪y - x, u⟫ • u ∈ P := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    simp only [u, inner_sub_left, inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq,
      RCLike.conj_to_real]
    have hne : ‖ν‖ ≠ 0 := hν_pos.ne'
    field_simp
    ring
  have hdist : infDist (y - x) (P : Set V) ≤ |⟪y - x, ν⟫| / ‖ν‖ := by
    refine (infDist_le_dist_of_mem hp_mem).trans ?_
    rw [dist_eq_norm, sub_sub_cancel, norm_smul, Real.norm_eq_abs]
    simp only [u, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_mul, abs_inv, abs_norm]
    have hne : ‖ν‖ ≠ 0 := hν_pos.ne'
    exact le_of_eq (by field_simp)
  rw [dist_eq_norm]
  exact hdist.trans ((div_le_iff₀ hν_pos).2 (hcone y hy hyr))

end CountablyRectifiable

end TauCeti
