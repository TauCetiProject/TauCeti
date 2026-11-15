/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Rectifiable.ApproximateTangent
public import TauCeti.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import TauCeti.Geometry.Euclidean.Volume.Measure
import TauCeti.MeasureTheory.Measure.Haar.Lipschitz

/-!
# Tangential differentiation and the tangential Jacobian on rectifiable sets

Definitions, uniqueness, invariance, chain rule, and Lipschitz bounds for tangential derivatives.
-/

public section

open Filter Function Metric MeasureTheory Measure Module Set
open scoped ENNReal NNReal Pointwise Topology symmDiff RealInnerProductSpace
local notation "ω[" d "](" r ")" => volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) r)

/-- Bound `T.toLinearMap.normDet ≤ ‖T‖ ^ finrank ℝ U` for `T : U →L[ℝ] W`. -/
theorem ContinuousLinearMap.normDet_le_opNorm_pow {U W : Type*} [NormedAddCommGroup U]
    [InnerProductSpace ℝ U] [FiniteDimensional ℝ U] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (T : U →L[ℝ] W) : T.toLinearMap.normDet ≤ ‖T‖ ^ finrank ℝ U := by
  let _ : MeasurableSpace U := borel U; have : BorelSpace U := ⟨rfl⟩
  let _ : MeasurableSpace W := borel W; have : BorelSpace W := ⟨rfl⟩
  have hv0 := (measure_ball_pos volume (0 : U) zero_lt_one).ne'
  have h1 : ENNReal.ofReal T.toLinearMap.normDet * volume (ball (0 : U) 1) ≤ ENNReal.ofReal (‖T‖ ^
    finrank ℝ U) * volume (ball (0 : U) 1) := by
    rw [← T.toLinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume, ←
      InnerProductSpace.euclideanHausdorffMeasure_eq_volume, ENNReal.ofReal_pow (norm_nonneg T), ←
      coe_nnNorm, ENNReal.ofReal_coe_nnreal]
    exact T.lipschitzWith.lipschitzOnWith.euclideanHausdorffMeasure_image_le (finrank ℝ U)
  have h2 := ENNReal.div_le_div_right h1 (volume (ball (0 : U) 1))
  rw [ENNReal.mul_div_cancel_right hv0 measure_ball_lt_top.ne, ENNReal.mul_div_cancel_right hv0
    measure_ball_lt_top.ne] at h2
  exact (ENNReal.ofReal_le_ofReal_iff (pow_nonneg (norm_nonneg T) _)).mp h2
local notation "𝓝₊" => 𝓝[>] (0 : ℝ)
local notation "cb" => Metric.closedBall
local notation "T[" k ", " E ", " x "]" => TauCeti.approximateTangentPlane k E x
local notation "π[" k ", " E ", " x "]" => TauCeti.approximateTangentProjection k E x
namespace TauCeti
private lemma not_tendsto_outside_cone_top_of_lt_top {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {E : Set V}
    {x : V} {K₀ : Submodule ℝ V} (hK₀ : K₀ < ⊤) (hpos : 0 < limsup (fun r => μHE[finrank ℝ V] (E ∩
    cb x r) / ω[finrank ℝ V](r)) 𝓝₊) (hcone : ∀ ε > (0 : ℝ), Tendsto (fun r => μHE[finrank ℝ V] {z ∈
    E ∩ cb x r | ε * dist z x < infDist (z - x) (K₀ : Set V)} / ω[finrank ℝ V](r)) 𝓝₊ (𝓝 0)) : False
    := by
  let S (ε : ℝ) : Set V := {w ∈ cb (0 : V) 1 | infDist w (K₀ : Set V) ≤ ε}
  let B₀ (r : ℝ) := ω[finrank ℝ V](r)
  have hS_meas (ε : ℝ) : MeasurableSet (S ε) := measurableSet_closedBall.inter (isClosed_le
    (continuous_infDist_pt (K₀ : Set V)) continuous_const).measurableSet
  have hslab (ε r : ℝ) (hr : 0 < r) : μHE[finrank ℝ V] {z ∈ cb x r | infDist (z - x) (K₀ : Set V) ≤
    ε * r} / B₀ r ≤ volume (S ε) / volume (cb (0 : V) 1) := by
    have hinc : {z ∈ cb x r | infDist (z - x) (K₀ : Set V) ≤ ε * r} ⊆ (IsometryEquiv.vaddConst x) ''
      (r • S ε) := fun z ⟨hzB, hzK⟩ => by
      refine ⟨z - x, ⟨r⁻¹ • (z - x), ⟨?_, ?_⟩, smul_inv_smul₀ hr.ne' (z - x)⟩,
        by simp [IsometryEquiv.vaddConst]⟩
      · rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le),
          ← dist_eq_norm]
        exact (inv_mul_le_iff₀ hr).mpr (by simpa using mem_closedBall.mp hzB)
      · rw [← K₀.dist_starProjection_eq_infDist, dist_eq_norm, map_smul, ← smul_sub, norm_smul,
          Real.norm_of_nonneg (inv_nonneg.mpr hr.le), ← dist_eq_norm,
          K₀.dist_starProjection_eq_infDist]
        exact (inv_mul_le_iff₀ hr).mpr (by linarith)
    have hvol_r : volume (cb (0 : V) r) = ENNReal.ofReal (r ^ finrank ℝ V) * volume (cb (0 : V) 1)
      := by
      simpa only [mul_one, ENNReal.ofReal_pow hr.le] using addHaar_closedBall_mul volume (0 : V)
        hr.le zero_le_one
    refine (ENNReal.div_le_div_right (measure_mono hinc) _).trans_eq ?_
    rw [(IsometryEquiv.vaddConst x).isometry.euclideanHausdorffMeasure_image,
      InnerProductSpace.euclideanHausdorffMeasure_eq_volume, addHaar_smul_of_nonneg volume hr.le]
    dsimp only [B₀]
    rw [← volume_closedBall_eq_euclidean (0 : V) r, hvol_r, ENNReal.mul_div_mul_left _ _
      (ENNReal.ofReal_pos.mpr (pow_pos hr _)).ne' ENNReal.ofReal_ne_top]
  have hlimsup_le (ε : ℝ) (hε : 0 < ε) :
      limsup (fun r => μHE[finrank ℝ V] (E ∩ cb x r) / B₀ r) 𝓝₊ ≤
        volume (S ε) / volume (cb (0 : V) 1) := calc
    limsup (fun r => μHE[finrank ℝ V] (E ∩ cb x r) / B₀ r) 𝓝₊
        ≤ limsup (fun r =>
            μHE[finrank ℝ V] {z ∈ cb x r | infDist (z - x) (K₀ : Set V) ≤ ε * r} / B₀ r +
            μHE[finrank ℝ V] {z ∈ E ∩ cb x r |
              ε * dist z x < infDist (z - x) (K₀ : Set V)} / B₀ r) 𝓝₊ := by
          refine limsup_le_limsup (Eventually.of_forall fun r => ?_)
          rw [← ENNReal.add_div]; apply ENNReal.div_le_div_right
          refine (measure_mono ?_).trans (measure_union_le _ _); rintro z ⟨hzE, hzr⟩
          by_cases hz : ε * dist z x < infDist (z - x) (K₀ : Set V)
          · exact Or.inr ⟨⟨hzE, hzr⟩, hz⟩
          · exact Or.inl ⟨hzr, (not_lt.mp hz).trans
              (mul_le_mul_of_nonneg_left (mem_closedBall.mp hzr) hε.le)⟩
      _ = limsup (fun r => μHE[finrank ℝ V]
            {z ∈ cb x r | infDist (z - x) (K₀ : Set V) ≤ ε * r} / B₀ r) 𝓝₊ :=
          ENNReal.limsup_add_of_right_tendsto_zero (hcone ε hε) _
      _ ≤ volume (S ε) / volume (cb (0 : V) 1) :=
          (limsup_le_limsup (eventually_mem_nhdsWithin.mono (hslab ε))).trans_eq (limsup_const _)
  let seq (n : ℕ) : Set V := S (1 / ((n : ℝ) + 1))
  have hanti : Antitone seq := fun m n hmn w hw => ⟨hw.1, hw.2.trans (one_div_le_one_div_of_le (by
    positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1))⟩
  have hiInter : volume (⋂ n, seq n) = 0 := by
    refine measure_mono_null (fun w hw => ?_) (addHaar_submodule volume K₀ hK₀.ne)
    exact (K₀.isClosed_of_finiteDimensional.mem_iff_infDist_zero ⟨0, K₀.zero_mem⟩).mpr <|
      le_antisymm (ge_of_tendsto' tendsto_one_div_add_atTop_nhds_zero_nat fun n => (mem_iInter.mp hw
      n).2) infDist_nonneg
  have hfin0 : volume (seq 0) ≠ ∞ := ((measure_mono (fun _ h => h.1 : seq 0 ⊆ cb 0 1)).trans_lt
    measure_closedBall_lt_top).ne
  have htend : Tendsto (volume ∘ seq) atTop (𝓝 0) := hiInter ▸ tendsto_measure_iInter_atTop (fun n
    => (hS_meas _).nullMeasurableSet) hanti ⟨0, hfin0⟩
  have hV1_pos : 0 < volume (cb (0 : V) 1) := measure_closedBall_pos volume 0 zero_lt_one
  exact (ENNReal.mul_pos hpos.ne' hV1_pos.ne').not_ge <| ge_of_tendsto' htend fun _ =>
    (ENNReal.le_div_iff_mul_le (.inl hV1_pos.ne') (.inl measure_closedBall_lt_top.ne)).mp
    (hlimsup_le _ Nat.one_div_pos_of_nat)
private lemma exists_orthogonal_hyperplane_rotation {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {P K₀ : Submodule ℝ V} {k : ℕ} (hK₀_lt : K₀ < P)
    (hP_dim : finrank ℝ P = k) (hcodim : k < finrank ℝ V) : ∃ Q : Submodule ℝ V, finrank ℝ Q = k ∧
    K₀ ≤ Q ∧ Q ≠ P := by
  have hP_orth_ne : Pᗮ ≠ ⊥ := fun hbot => hcodim.ne <| by
    have h := Submodule.finrank_add_finrank_orthogonal P
    rw [hP_dim, hbot, finrank_bot, add_zero] at h; exact h
  obtain ⟨n, hnP, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP_orth_ne
  have hM_ne : (P ⊓ K₀ᗮ : Submodule ℝ V) ≠ ⊥ := fun hbot => hK₀_lt.ne <| le_antisymm hK₀_lt.le fun p
    hp => by
      have hm0 : p - K₀.starProjection p = 0 := (Submodule.mem_bot ℝ).mp <| hbot ▸
        ⟨P.sub_mem hp (hK₀_lt.le (K₀.starProjection_apply_mem p)),
          K₀.sub_starProjection_mem_orthogonal p⟩
      exact sub_eq_zero.mp hm0 ▸ K₀.starProjection_apply_mem p
  obtain ⟨u₀, ⟨hu₀P, hu₀K⟩, hu₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM_ne
  let H : Submodule ℝ V := P ⊓ (ℝ ∙ u₀)ᗮ
  have hK₀_le_H : K₀ ≤ H := le_inf hK₀_lt.le fun x hx =>
    Submodule.mem_orthogonal_singleton_iff_inner_left.mpr (Submodule.inner_right_of_mem_orthogonal
    hx hu₀K)
  have hu₀_le_P : ℝ ∙ u₀ ≤ P := (Submodule.span_singleton_le_iff_mem u₀ P).mpr hu₀P
  have hH_sup_u : H ⊔ (ℝ ∙ u₀) = P := le_antisymm (sup_le inf_le_left hu₀_le_P) fun p hp => by
    have hproj := (ℝ ∙ u₀).starProjection_apply_mem p
    have hdiff : p - (ℝ ∙ u₀).starProjection p ∈ H := ⟨P.sub_mem hp (hu₀_le_P hproj), (ℝ ∙
      u₀).sub_starProjection_mem_orthogonal p⟩
    simpa using Submodule.add_mem_sup hdiff hproj
  have hH_inf_u : H ⊓ (ℝ ∙ u₀) = ⊥ := eq_bot_iff.mpr <| (inf_le_inf_right (ℝ ∙ u₀)
    inf_le_right).trans (by rw [inf_comm, Submodule.inf_orthogonal_eq_bot])
  have hH_inf_n : H ⊓ (ℝ ∙ n) = ⊥ := eq_bot_iff.mpr <| (inf_le_inf inf_le_left
    ((Submodule.span_singleton_le_iff_mem n Pᗮ).mpr hnP)).trans (Submodule.inf_orthogonal_eq_bot
    P).le
  have hQ_dim : finrank ℝ (H ⊔ (ℝ ∙ n) : Submodule ℝ V) = k := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq H (ℝ ∙ u₀)
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq H (ℝ ∙ n)
    rw [hH_sup_u, hH_inf_u, finrank_bot, add_zero, finrank_span_singleton hu₀0, hP_dim] at h1
    rw [hH_inf_n, finrank_bot, add_zero, finrank_span_singleton hn0] at h2; exact h2.trans h1.symm
  refine ⟨H ⊔ (ℝ ∙ n), hQ_dim, hK₀_le_H.trans le_sup_left, fun hQP => hn0 ?_⟩
  have hn_bot : n ∈ P ⊓ Pᗮ := ⟨hQP ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self n),
    hnP⟩
  exact (Submodule.mem_bot ℝ).mp (Submodule.inf_orthogonal_eq_bot P ▸ hn_bot)
section Defs
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup W] [NormedSpace ℝ W] {k : ℕ} {E E₁ E₂ :
    Set V} {g g₁ g₂ : V → W} {L L₁ L₂ : V →L[ℝ] W} {x : V}
/-- `g` has approximate tangential derivative `L` along `E` at `x` in dimension `k`. -/
structure HasTangentialFDerivAt (k : ℕ) (E : Set V) (g : V → W) (L : V →L[ℝ] W) (x : V) : Prop where
  /-- `E` has a unique approximate tangent `k`-plane at `x`. -/
  existsUnique_plane : ∃! P : Submodule ℝ V, IsApproximateTangentPlane k E x P
  /-- `L` vanishes on `(approximateTangentPlane k E x)ᗮ`. -/
  comp_projection : L ∘L π[k, E, x] = L
  /-- Outside every relative-error cone, `E` has `k`-dimensional density zero at `x`. -/
  tendsto_outside_error : ∀ ε > (0 : ℝ), Tendsto (fun r =>
    μHE[k] {z ∈ E ∩ cb x r | ε * dist z x < ‖g z - g x - L (z - x)‖} /
      ω[k](r)) 𝓝₊ (𝓝 0)
namespace HasTangentialFDerivAt
/-- `approximateTangentPlane k E x` is an approximate tangent plane from `HasTangentialFDerivAt`. -/
theorem isApproximateTangentPlane (h : HasTangentialFDerivAt k E g L x) : IsApproximateTangentPlane
    k E x (T[k, E, x]) := isApproximateTangentPlane_approximateTangentPlane
    h.existsUnique_plane.exists
/-- Uniqueness of `approximateTangentPlane k E x` under `HasTangentialFDerivAt`. -/
theorem eq_approximateTangentPlane (h : HasTangentialFDerivAt k E g L x) {Q : Submodule ℝ V} (hQ :
    IsApproximateTangentPlane k E x Q) : Q = T[k, E, x] := by
  obtain ⟨P, hP, hPuniq⟩ := h.existsUnique_plane
  rw [hP.approximateTangentPlane_eq hPuniq]; exact hPuniq Q hQ
/-- Unconditional uniqueness of the approximate tangential derivative at `x`. -/
theorem unique (h₁ : HasTangentialFDerivAt k E g L₁ x) (h₂ : HasTangentialFDerivAt k E g L₂ x) : L₁
    = L₂ := by
  by_contra hne; let P : Submodule ℝ V := T[k, E, x]
  have hP : IsApproximateTangentPlane k E x P := h₁.isApproximateTangentPlane
  set D : V →L[ℝ] W := L₁ - L₂
  have hD_proj : D ∘L P.starProjection = D := by
    rw [← approximateTangentProjection_eq, ContinuousLinearMap.sub_comp, h₁.comp_projection,
      h₂.comp_projection]
  let K₀ : Submodule ℝ V := P ⊓ LinearMap.ker D.toLinearMap
  have hK₀_lt : K₀ < P := lt_of_le_of_ne inf_le_left fun h => hne <| sub_eq_zero.mp <|
    ContinuousLinearMap.ext fun v => by
      change D v = 0; rw [← hD_proj, ContinuousLinearMap.comp_apply]
      exact (h.symm ▸ P.starProjection_apply_mem v : P.starProjection v ∈ K₀).2
  let M : Submodule ℝ V := P ⊓ K₀ᗮ
  have hM_inj : LinearMap.ker (D.toLinearMap.comp M.subtype) = ⊥ := by
    rw [LinearMap.ker_eq_bot]; rintro ⟨m, hmP, hmK⟩ ⟨n, hnP, hnK⟩ hmn; ext
    have hsub : m - n ∈ K₀ ⊓ K₀ᗮ := ⟨⟨P.sub_mem hmP hnP, LinearMap.mem_ker.mpr
      (by simpa [map_sub, sub_eq_zero] using hmn)⟩, K₀ᗮ.sub_mem hmK hnK⟩
    exact sub_eq_zero.mp ((Submodule.mem_bot ℝ).mp (Submodule.inf_orthogonal_eq_bot K₀ ▸ hsub))
  obtain ⟨c, hc0, hc_anti⟩ := (D.toLinearMap.comp M.subtype).exists_antilipschitzWith hM_inj
  have hinf_K₀ (w : V) : infDist w (K₀ : Set V) ≤ infDist w (P : Set V) + c * ‖D w‖ := by
    let p : V := P.starProjection w; let q : V := K₀.starProjection p
    have hqK : q ∈ K₀ := K₀.starProjection_apply_mem p
    have hmM : p - q ∈ M := ⟨P.sub_mem (P.starProjection_apply_mem w) (hK₀_lt.le hqK),
      K₀.sub_starProjection_mem_orthogonal p⟩
    have hDw : D (p - q) = D w := by
      rw [map_sub, show D q = 0 from hqK.2, sub_zero, ← ContinuousLinearMap.comp_apply, hD_proj]
    have hnorm_m : ‖p - q‖ ≤ c * ‖D w‖ := by
      simpa [Subtype.dist_eq, hDw] using hc_anti.le_mul_dist ⟨p - q, hmM⟩ 0
    calc infDist w (K₀ : Set V) ≤ dist w p + dist p q :=
          (infDist_le_dist_of_mem hqK).trans (dist_triangle w p q)
      _ = infDist w (P : Set V) + ‖p - q‖ := by
          rw [P.dist_starProjection_eq_infDist w, dist_eq_norm]
      _ ≤ infDist w (P : Set V) + c * ‖D w‖ := by gcongr
  have hK₀_cone : ∀ ε > (0 : ℝ), Tendsto (fun r => μHE[k] {z ∈ E ∩ cb x r | ε * dist z x < infDist
    (z - x) (K₀ : Set V)} / ω[k](r)) 𝓝₊ (𝓝 0) := fun ε hε => by
    have hsum := ((hP.tendsto_outside_cone (ε / 2) (by positivity)).add (h₁.tendsto_outside_error (ε
      / (4 * c)) (by positivity))).add (h₂.tendsto_outside_error (ε / (4 * c)) (by positivity))
    simp only [add_zero] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum (Eventually.of_forall
      fun _ => zero_le) (Eventually.of_forall fun r => ?_)
    rw [← ENNReal.add_div, ← ENNReal.add_div]
    have hsub_u : {z ∈ E ∩ cb x r | ε * dist z x < infDist (z - x) (K₀ : Set V)} ⊆ ({z ∈ E ∩ cb x r
      | (ε / 2) * dist z x < infDist (z - x) (P : Set V)} ∪ {z ∈ E ∩ cb x r | (ε / (4 * c)) * dist z
      x < ‖g z - g x - L₁ (z - x)‖}) ∪ {z ∈ E ∩ cb x r | (ε / (4 * c)) * dist z x < ‖g z - g x - L₂
      (z - x)‖} := by
      rintro z ⟨hzB, hzK⟩
      by_cases hP_out : (ε / 2) * dist z x < infDist (z - x) (P : Set V)
      · exact Or.inl (Or.inl ⟨hzB, hP_out⟩)
      by_cases h1_out : (ε / (4 * c)) * dist z x < ‖g z - g x - L₁ (z - x)‖
      · exact Or.inl (Or.inr ⟨hzB, h1_out⟩)
      refine Or.inr ⟨hzB, ?_⟩; by_contra! h2_le
      have hD_le : ‖D (z - x)‖ ≤ ‖g z - g x - L₁ (z - x)‖ + ‖g z - g x - L₂ (z - x)‖ := by
        have : D (z - x) = (g z - g x - L₂ (z - x)) - (g z - g x - L₁ (z - x)) := by simp [D]
        exact this ▸ (norm_sub_le _ _).trans_eq (add_comm _ _)
      have hprod : (c : ℝ) * ((ε / (4 * c)) * dist z x) = (ε / 4) * dist z x := by field_simp
      have hc1 := (mul_le_mul_of_nonneg_left (not_lt.mp h1_out) c.coe_nonneg).trans_eq hprod
      have hc2 := (mul_le_mul_of_nonneg_left h2_le c.coe_nonneg).trans_eq hprod
      linarith [(hinf_K₀ (z - x)).trans
        (add_le_add_right (mul_le_mul_of_nonneg_left hD_le c.coe_nonneg) _), not_lt.mp hP_out]
    exact ENNReal.div_le_div_right ((measure_mono hsub_u).trans ((measure_union_le _ _).trans
      (add_le_add (measure_union_le _ _) le_rfl))) _
  by_cases hcodim : k < finrank ℝ V
  · obtain ⟨Q, hQ_dim, hK₀_le_Q, hQP⟩ :=
      exists_orthogonal_hyperplane_rotation hK₀_lt hP.finrank_eq hcodim
    refine hQP (h₁.eq_approximateTangentPlane ⟨hQ_dim, hP.limsup_pos, fun ε hε => ?_⟩)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hK₀_cone ε hε)
      (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun r => ?_)
    apply ENNReal.div_le_div_right; refine measure_mono ?_; rintro z ⟨hzB, hzQ⟩
    exact ⟨hzB, hzQ.trans_le (infDist_le_infDist_of_subset (SetLike.coe_subset_coe.mpr hK₀_le_Q) ⟨0,
      Submodule.zero_mem _⟩)⟩
  · have hk_eq : k = finrank ℝ V :=
      le_antisymm (hP.finrank_eq ▸ Submodule.finrank_le _) (not_lt.mp hcodim)
    subst hk_eq
    exact not_tendsto_outside_cone_top_of_lt_top (Submodule.eq_top_of_finrank_eq hP.finrank_eq ▸
      hK₀_lt) hP.limsup_pos hK₀_cone
private lemma of_eventually_eq {E₁ E₂ : Set V} {g₁ g₂ : V → W}
    (hu : (∃! P, IsApproximateTangentPlane k E₁ x P) → ∃! P, IsApproximateTangentPlane k E₂ x P)
    (hp : π[k, E₁, x] = π[k, E₂, x])
    (he : ∀ ε > (0 : ℝ), ∀ᶠ r in 𝓝[>] (0 : ℝ),
      μHE[k] {z ∈ E₁ ∩ cb x r | ε * dist z x < ‖g₁ z - g₁ x - L (z - x)‖} =
        μHE[k] {z ∈ E₂ ∩ cb x r | ε * dist z x < ‖g₂ z - g₂ x - L (z - x)‖})
    (h : HasTangentialFDerivAt k E₁ g₁ L x) : HasTangentialFDerivAt k E₂ g₂ L x :=
  ⟨hu h.1, hp ▸ h.2, fun ε hε => (h.3 ε hε).congr' ((he ε hε).mono fun _ hr => by rw [hr])⟩
/-- Null-set invariance of `HasTangentialFDerivAt` in the domain set `E`. -/
theorem congr_ae_set (h : E₁ =ᵐ[μHE[k]] E₂) : HasTangentialFDerivAt k E₁ g L x ↔
    HasTangentialFDerivAt k E₂ g L x := by
  have hnull : μHE[k] (E₁ ∆ E₂) = 0 := measure_symmDiff_eq_zero_iff.mpr h
  have herr_eq (ε r : ℝ) :
      μHE[k] {z ∈ E₁ ∩ cb x r | ε * dist z x < ‖g z - g x - L (z - x)‖} =
        μHE[k] {z ∈ E₂ ∩ cb x r | ε * dist z x < ‖g z - g x - L (z - x)‖} :=
    measure_congr <| measure_symmDiff_eq_zero_iff.mp <| measure_mono_null
      (fun z hz => by simp only [mem_symmDiff, mem_ofPred_eq, mem_inter_iff] at hz ⊢; tauto) hnull
  have hex := existsUnique_congr fun P : Submodule ℝ V => IsApproximateTangentPlane.congr_ae (x :=
    x) (P := P) h
  have hp := approximateTangentProjection_congr_ae h x
  exact ⟨of_eventually_eq hex.mp hp fun ε _ => .of_forall (herr_eq ε), of_eventually_eq hex.mpr
    hp.symm fun ε _ => .of_forall fun r => (herr_eq ε r).symm⟩
/-- Germ invariance of `HasTangentialFDerivAt` in the domain set `E`. -/
theorem congr_nhds_set (h : E₁ =ᶠ[𝓝 x] E₂) : HasTangentialFDerivAt k E₁ g L x ↔
    HasTangentialFDerivAt k E₂ g L x := by
  obtain ⟨δ, hδ, hδeq⟩ := Metric.eventually_nhds_iff.mp h
  have hinter : ∀ᶠ r in 𝓝[>] (0 : ℝ), E₁ ∩ cb x r = E₂ ∩ cb x r := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with r ⟨_, hr⟩
    ext z; simp only [mem_inter_iff, mem_closedBall]
    exact and_congr_left fun hzr => by simpa using hδeq (hzr.trans_lt hr)
  have hex := existsUnique_congr fun P : Submodule ℝ V => IsApproximateTangentPlane.congr_nhds (k :=
    k) (P := P) h
  have hp := approximateTangentProjection_congr_nhds (k := k) h
  exact ⟨of_eventually_eq hex.mp hp fun _ _ => hinter.mono fun _ hr => by simp only [hr],
    of_eventually_eq hex.mpr hp.symm fun _ _ => hinter.mono fun _ hr => by simp only [hr]⟩
/-- Restriction invariance of `HasTangentialFDerivAt` at `x ∈ E`. -/
theorem congr_of_eqOn (hg : EqOn g₁ g₂ E) (hx : x ∈ E) : HasTangentialFDerivAt k E g₁ L x ↔
    HasTangentialFDerivAt k E g₂ L x := by
  have hset (ε r : ℝ) : {z ∈ E ∩ cb x r | ε * dist z x < ‖g₁ z - g₁ x - L (z - x)‖} = {z ∈ E ∩ cb x
    r | ε * dist z x < ‖g₂ z - g₂ x - L (z - x)‖} := by
    ext z; simp only [mem_ofPred_eq, mem_inter_iff]
    exact and_congr_right fun ⟨hzE, _⟩ => by rw [hg hzE, hg hx]
  exact ⟨of_eventually_eq id rfl fun ε _ => .of_forall fun r => by rw [hset ε r],
    of_eventually_eq id rfl fun ε _ => .of_forall fun r => by rw [hset ε r]⟩
/-- Almost-everywhere congruence of `HasTangentialFDerivAt` in `g` when `g₁ x = g₂ x`. -/
theorem congr_ae_fun (hg : g₁ =ᵐ[μHE[k].restrict E] g₂) (hx_eq : g₁ x = g₂ x) :
    HasTangentialFDerivAt k E g₁ L x ↔ HasTangentialFDerivAt k E g₂ L x := by
  have hN : μHE[k] ({z | g₁ z ≠ g₂ z} ∩ E) = 0 := nonpos_iff_eq_zero.mp <| (le_restrict_apply E {z |
    g₁ z ≠ g₂ z}).trans_eq (ae_iff.mp hg)
  have herr_eq (ε r : ℝ) : μHE[k] {z ∈ E ∩ cb x r | ε * dist z x < ‖g₁ z - g₁ x - L (z - x)‖} =
    μHE[k] {z ∈ E ∩ cb x r | ε * dist z x < ‖g₂ z - g₂ x - L (z - x)‖} := by
    refine measure_congr <| measure_symmDiff_eq_zero_iff.mp <| measure_mono_null ?_ hN
    rintro z (⟨⟨⟨hzE, hzr⟩, h1⟩, h2⟩ | ⟨⟨⟨hzE, hzr⟩, h2⟩, h1⟩) <;> refine ⟨fun hzeq => ?_, hzE⟩
    · exact h2 ⟨⟨hzE, hzr⟩, by rwa [← hzeq, ← hx_eq]⟩
    · exact h1 ⟨⟨hzE, hzr⟩, by rwa [hzeq, hx_eq]⟩
  exact ⟨of_eventually_eq id rfl fun ε _ => .of_forall (herr_eq ε), of_eventually_eq id rfl fun ε _
    => .of_forall fun r => (herr_eq ε r).symm⟩
/-- Compatibility with `HasFDerivWithinAt` at points with a unique approximate tangent `k`-plane. -/
theorem of_hasFDerivWithinAt (hu : ∃! P : Submodule ℝ V, IsApproximateTangentPlane k E x P) (hg :
    HasFDerivWithinAt g L E x) : HasTangentialFDerivAt k E g (L ∘L π[k, E, x]) x := by
  let P : Submodule ℝ V := T[k, E, x]
  have hP := isApproximateTangentPlane_approximateTangentPlane hu.exists
  refine ⟨hu, ?_, fun ε hε => ?_⟩
  · ext v; simp only [ContinuousLinearMap.comp_apply, approximateTangentProjection_eq]
    exact congrArg L (Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _
      v))
  · obtain ⟨δ, hδ, hδb⟩ := eventually_nhds_iff_ball.mp
      (eventually_nhdsWithin_iff.mp (hg.isLittleO.bound (half_pos hε)))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hP.tendsto_outside_cone (ε
      / (2 * (‖L‖ + 1))) (by positivity)) (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [Ioo_mem_nhdsGT hδ] with r ⟨_, hrδ⟩
    refine ENNReal.div_le_div_right (measure_mono ?_) _; rintro z ⟨⟨hzE, hzr⟩, hzerr⟩
    refine ⟨⟨hzE, hzr⟩, ?_⟩
    have herr := hδb z (mem_ball.mpr ((mem_closedBall.mp hzr).trans_lt hrδ)) hzE
    have hdecomp : g z - g x - (L ∘L π[k, E, x]) (z - x) = (g z - g x - L (z - x)) + L ((z - x) -
      P.starProjection (z - x)) := by
      simp only [ContinuousLinearMap.comp_apply, approximateTangentProjection_eq, map_sub]; abel
    have hnorm := (hdecomp ▸ hzerr).trans_le ((norm_add_le _ _).trans (add_le_add herr (L.le_opNorm
      _)))
    rw [← dist_eq_norm (z - x), P.dist_starProjection_eq_infDist] at hnorm
    rw [dist_eq_norm] at hnorm ⊢; by_contra! hle
    have hL_le : ‖L‖ * infDist (z - x) (P : Set V) ≤ (ε / 2) * ‖z - x‖ := (mul_le_mul
      (le_add_of_nonneg_right zero_le_one) hle infDist_nonneg (by positivity)).trans_eq (by
      field_simp)
    linarith
/-- Sum rule for approximate tangential derivatives. -/
theorem add (h₁ : HasTangentialFDerivAt k E g₁ L₁ x) (h₂ : HasTangentialFDerivAt k E g₂ L₂ x) :
    HasTangentialFDerivAt k E (fun z => g₁ z + g₂ z) (L₁ + L₂) x := by
  refine ⟨h₁.existsUnique_plane,
    by rw [ContinuousLinearMap.add_comp, h₁.comp_projection, h₂.comp_projection], fun ε hε => ?_⟩
  have hsum := (h₁.tendsto_outside_error (ε / 2) (half_pos hε)).add (h₂.tendsto_outside_error (ε /
    2) (half_pos hε))
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum (Eventually.of_forall
    fun _ => zero_le) (Eventually.of_forall fun r => ?_)
  rw [← ENNReal.add_div]
  apply ENNReal.div_le_div_right; refine (measure_mono ?_).trans (measure_union_le _ _)
  rintro z ⟨hzB, hz⟩
  by_cases h1 : (ε / 2) * dist z x < ‖g₁ z - g₁ x - L₁ (z - x)‖
  · exact Or.inl ⟨hzB, h1⟩
  refine Or.inr ⟨hzB, ?_⟩
  have hdecomp : (g₁ z + g₂ z) - (g₁ x + g₂ x) - (L₁ + L₂) (z - x) =
      (g₁ z - g₁ x - L₁ (z - x)) + (g₂ z - g₂ x - L₂ (z - x)) := by simp only [add_apply]; abel
  linarith [(hdecomp ▸ hz).trans_le (norm_add_le _ _), not_lt.mp h1]
/-- Scalar multiplication rule for approximate tangential derivatives. -/
theorem const_smul (c : ℝ) (h : HasTangentialFDerivAt k E g L x) : HasTangentialFDerivAt k E (fun z
    => c • g z) (c • L) x := by
  refine ⟨h.existsUnique_plane, by rw [ContinuousLinearMap.smul_comp, h.comp_projection],
    fun ε hε => ?_⟩
  by_cases hc : c = 0
  · subst hc; refine tendsto_const_nhds.congr' (Eventually.of_forall fun r => ?_)
    have hempty : {z ∈ E ∩ cb x r | ε * dist z x < ‖(0 : ℝ) • g z - (0 : ℝ) • g x - ((0 : ℝ) • L) (z
      - x)‖} = ∅ := by
      ext z; simp only [zero_smul, sub_self, zero_apply, norm_zero,
        mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      exact fun _ => not_lt.mpr (mul_nonneg hε.le dist_nonneg)
    dsimp only; rw [hempty, measure_empty, ENNReal.zero_div]
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (h.tendsto_outside_error (ε / |c|) (div_pos hε (abs_pos.mpr hc)))
      (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun r => ?_)
    refine ENNReal.div_le_div_right (measure_mono ?_) _; rintro z ⟨hzB, hz⟩; refine ⟨hzB, ?_⟩
    have hdecomp : c • g z - c • g x - (c • L) (z - x) = c • (g z - g x - L (z - x)) := by
      simp [smul_sub]
    rw [hdecomp, norm_smul, Real.norm_eq_abs] at hz
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
noncomputable def tangentialFDeriv (k : ℕ) (E : Set V) (g : V → W) (x : V) : V →L[ℝ] W := if h : ∃ L
    : V →L[ℝ] W, HasTangentialFDerivAt k E g L x then h.choose else 0
/-- `HasTangentialFDerivAt k E g L x` identifies `tangentialFDeriv k E g x = L`. -/
theorem HasTangentialFDerivAt.tangentialFDeriv_eq (h : HasTangentialFDerivAt k E g L x) :
    tangentialFDeriv k E g x = L := by
  have hex : ∃ L', HasTangentialFDerivAt k E g L' x := ⟨L, h⟩
  simp only [tangentialFDeriv, hex, ↓reduceDIte]; exact hex.choose_spec.unique h
/-- Specification of `tangentialFDeriv k E g x` when `g` is tangentially differentiable at `x`. -/
theorem hasTangentialFDerivAt_tangentialFDeriv (h : ∃ L : V →L[ℝ] W, HasTangentialFDerivAt k E g L
    x) : HasTangentialFDerivAt k E g (tangentialFDeriv k E g x) x := by
  simp only [tangentialFDeriv, h, ↓reduceDIte]; exact h.choose_spec
local notation "TFD[" k ", " E ", " g ", " x "]" => TauCeti.tangentialFDeriv k E g x
/-- `tangentialFDeriv k E g x` vanishes on `(T[k, E, x])ᗮ`. -/
@[simp] theorem tangentialFDeriv_comp_approximateTangentProjection (k : ℕ) (E : Set V) (g : V → W)
    (x : V) : TFD[k, E, g, x] ∘L π[k, E, x] = TFD[k, E, g, x] := by
  by_cases h : ∃ L : V →L[ℝ] W, HasTangentialFDerivAt k E g L x
  · exact (hasTangentialFDerivAt_tangentialFDeriv h).comp_projection
  · simp [tangentialFDeriv, h]
/-- In dimension zero, `tangentialFDeriv 0 E g x = 0`. -/
@[simp] theorem tangentialFDeriv_zero (E : Set V) (g : V → W) (x : V) : TFD[0, E, g, x] = 0 := by
  rw [← tangentialFDeriv_comp_approximateTangentProjection 0 E g x,
    approximateTangentProjection_zero, ContinuousLinearMap.comp_zero]
private lemma tangentialFDeriv_eq_of_iff {E₁ E₂ : Set V} {g₁ g₂ : V → W} {x : V}
    (hiff : ∀ L, HasTangentialFDerivAt k E₁ g₁ L x ↔ HasTangentialFDerivAt k E₂ g₂ L x) :
    TFD[k, E₁, g₁, x] = TFD[k, E₂, g₂, x] :=
  congrArg (fun p : (V →L[ℝ] W) → Prop => by classical exact if h : ∃ L, p L then h.choose else 0)
    (funext fun L => propext (hiff L))
/-- Null-set invariance of `tangentialFDeriv` in `E`. -/
theorem tangentialFDeriv_congr_ae_set (h : E₁ =ᵐ[μHE[k]] E₂) (g : V → W) (x : V) : TFD[k, E₁, g, x]
    = TFD[k, E₂, g, x] := tangentialFDeriv_eq_of_iff fun _ => HasTangentialFDerivAt.congr_ae_set h
/-- Germ invariance of `tangentialFDeriv` in `E`. -/
theorem tangentialFDeriv_congr_nhds_set (h : E₁ =ᶠ[𝓝 x] E₂) (g : V → W) : TFD[k, E₁, g, x] = TFD[k,
    E₂, g, x] := tangentialFDeriv_eq_of_iff fun _ => HasTangentialFDerivAt.congr_nhds_set h
/-- Restriction invariance of `tangentialFDeriv` at `x ∈ E`. -/
theorem tangentialFDeriv_congr_of_eqOn (hg : EqOn g₁ g₂ E) (hx : x ∈ E) : TFD[k, E, g₁, x] = TFD[k,
    E, g₂, x] := tangentialFDeriv_eq_of_iff fun _ => HasTangentialFDerivAt.congr_of_eqOn hg hx
/-- Almost-everywhere congruence of `tangentialFDeriv` in `g`. -/
theorem tangentialFDeriv_congr_ae_fun (hg : g₁ =ᵐ[μHE[k].restrict E] g₂) : tangentialFDeriv k E g₁
    =ᵐ[μHE[k].restrict E] tangentialFDeriv k E g₂ := hg.mono fun _ hx => tangentialFDeriv_eq_of_iff
    fun _ => HasTangentialFDerivAt.congr_ae_fun hg hx
end Defs
section Jacobian
local notation "TFD[" k ", " E ", " g ", " x "]" => TauCeti.tangentialFDeriv k E g x
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup W] [InnerProductSpace ℝ W] {k : ℕ} {E E₁
    E₂ : Set V} {g g₁ g₂ : V → W} {L : V →L[ℝ] W} {x : V}
open Classical in
/-- The `k`-dimensional tangential Jacobian of `g` along `E` at `x` (`0` if not differentiable). -/
noncomputable def tangentialJacobian (k : ℕ) (E : Set V) (g : V → W) (x : V) : ℝ := if ∃ L : V →L[ℝ]
    W, HasTangentialFDerivAt k E g L x then ((tangentialFDeriv k E g x).toLinearMap.domRestrict
    (T[k, E, x])).normDet else 0
local notation "TJ[" k ", " E ", " g ", " x "]" => TauCeti.tangentialJacobian k E g x
/-- Nonnegativity of `tangentialJacobian`. -/
theorem tangentialJacobian_nonneg (k : ℕ) (E : Set V) (g : V → W) (x : V) : 0 ≤ TJ[k, E, g, x] := by
  unfold tangentialJacobian; split_ifs <;> [exact LinearMap.normDet_nonneg _; exact le_rfl]
/-- Explicit formula for `tangentialJacobian` when `HasTangentialFDerivAt k E g L x` holds. -/
theorem HasTangentialFDerivAt.tangentialJacobian_eq (h : HasTangentialFDerivAt k E g L x) : TJ[k, E,
    g, x] = (L.toLinearMap.domRestrict (T[k, E, x])).normDet := by
  have hex : ∃ L', HasTangentialFDerivAt k E g L' x := ⟨L, h⟩
  simp only [tangentialJacobian, hex, ↓reduceIte, h.tangentialFDeriv_eq]
/-- Bound `tangentialJacobian k E g x ≤ ‖L‖ ^ k` under `HasTangentialFDerivAt k E g L x`. -/
theorem HasTangentialFDerivAt.tangentialJacobian_le_opNorm_pow (h : HasTangentialFDerivAt k E g L x)
    : TJ[k, E, g, x] ≤ ‖L‖ ^ k := by
  let P := T[k, E, x]
  have hdim : finrank ℝ P = k := h.isApproximateTangentPlane.finrank_eq
  have heq : L.toLinearMap.domRestrict P = (L.comp P.subtypeL).toLinearMap := by ext y; rfl
  rw [h.tangentialJacobian_eq, heq]; conv_rhs => rw [← hdim]
  have hnorm : ‖L.comp P.subtypeL‖ ≤ ‖L‖ :=
    (L.opNorm_comp_le P.subtypeL).trans (mul_le_of_le_one_right (norm_nonneg L)
      (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by simp))
  exact (L.comp P.subtypeL).normDet_le_opNorm_pow.trans (pow_le_pow_left₀ (norm_nonneg _) hnorm _)
/-- Rank-deficient tangential derivatives have zero `k`-dimensional tangential Jacobian. -/
theorem tangentialJacobian_eq_zero_of_finrank_range_lt (hrank : finrank ℝ (LinearMap.range (TFD[k,
    E, g, x]).toLinearMap) < k) : TJ[k, E, g, x] = 0 := by
  by_cases h : ∃ L : V →L[ℝ] W, HasTangentialFDerivAt k E g L x
  · simp only [tangentialJacobian, h, ↓reduceIte]
    apply ((TFD[k, E, g, x]).toLinearMap.domRestrict (T[k, E,
      x])).normDet_eq_zero_iff_rank_range_ne.mpr
    rw [(hasTangentialFDerivAt_tangentialFDeriv h).isApproximateTangentPlane.finrank_eq]
    have hmono : LinearMap.range ((TFD[k, E, g, x]).toLinearMap.domRestrict (T[k, E, x])) ≤
      LinearMap.range (TFD[k, E, g, x]).toLinearMap := by
      rintro _ ⟨v, rfl⟩; exact ⟨v, rfl⟩
    exact ((Submodule.finrank_mono hmono).trans_lt hrank).ne
  · simp [tangentialJacobian, h]
open Classical in
private lemma tangentialJacobian_eq_of_iff {E₁ E₂ : Set V} {g₁ g₂ : V → W} {x : V} (hiff : ∀ L,
    HasTangentialFDerivAt k E₁ g₁ L x ↔ HasTangentialFDerivAt k E₂ g₂ L x) (hP : T[k, E₁, x] = T[k,
    E₂, x]) : TJ[k, E₁, g₁, x] = TJ[k, E₂, g₂, x] := by
  rw [tangentialJacobian, tangentialJacobian, tangentialFDeriv_eq_of_iff hiff]
  exact if_congr (exists_congr hiff) (congrArg (fun S : Submodule ℝ V => ((TFD[k, E₂, g₂,
    x]).toLinearMap.domRestrict S).normDet) hP) rfl
/-- Null-set invariance of `tangentialJacobian` in `E`. -/
theorem tangentialJacobian_congr_ae_set (h : E₁ =ᵐ[μHE[k]] E₂) (g : V → W) (x : V) : TJ[k, E₁, g, x]
    = TJ[k, E₂, g, x] := tangentialJacobian_eq_of_iff (fun _ => HasTangentialFDerivAt.congr_ae_set
    h) (approximateTangentPlane_congr_ae h x)
/-- Germ invariance of `tangentialJacobian` in `E`. -/
theorem tangentialJacobian_congr_nhds_set (h : E₁ =ᶠ[𝓝 x] E₂) (g : V → W) : TJ[k, E₁, g, x] = TJ[k,
    E₂, g, x] := tangentialJacobian_eq_of_iff (fun _ => HasTangentialFDerivAt.congr_nhds_set h)
    (approximateTangentPlane_congr_nhds h)
/-- Restriction invariance of `tangentialJacobian` at `x ∈ E`. -/
theorem tangentialJacobian_congr_of_eqOn (hg : EqOn g₁ g₂ E) (hx : x ∈ E) : TJ[k, E, g₁, x] = TJ[k,
    E, g₂, x] := tangentialJacobian_eq_of_iff (fun _ => HasTangentialFDerivAt.congr_of_eqOn hg hx)
    rfl
/-- Almost-everywhere congruence of `tangentialJacobian` in `g`. -/
theorem tangentialJacobian_congr_ae_fun (hg : g₁ =ᵐ[μHE[k].restrict E] g₂) : tangentialJacobian k E
    g₁ =ᵐ[μHE[k].restrict E] tangentialJacobian k E g₂ := hg.mono fun _ hx =>
    tangentialJacobian_eq_of_iff (fun _ => HasTangentialFDerivAt.congr_ae_fun hg hx) rfl
end Jacobian
end TauCeti
local notation "TFD[" k ", " E ", " g ", " x "]" => TauCeti.tangentialFDeriv k E g x
local notation "TJ[" k ", " E ", " g ", " x "]" => TauCeti.tangentialJacobian k E g x
namespace HasFDerivWithinAt
open TauCeti
variable {U V W : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    [MeasurableSpace U] [BorelSpace U] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
omit [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V] in
private lemma ringInverse_adjoint_comp_self {A : U →L[ℝ] V} (hinj : Injective A) : Ring.inverse
    (A.adjoint ∘L A) ∘L (A.adjoint ∘L A) = ContinuousLinearMap.id ℝ U := by
  let G : U →L[ℝ] U := A.adjoint ∘L A
  have hG_det : G.det ≠ 0 := by
    have hsq := A.normDet_sq; simp only [RCLike.ofReal_real_eq_id, id_eq] at hsq
    exact hsq ▸ pow_ne_zero 2 ((A.toLinearMap.normDet_ne_zero_tfae.out 5 1).mp hinj)
  let eG := G.toContinuousLinearEquivOfDetNeZero hG_det
  have hcoe : (eG : U →L[ℝ] U) = G := G.coe_toContinuousLinearEquivOfDetNeZero hG_det
  exact Ring.inverse_mul_cancel G ⟨⟨G, eG.symm,
    by rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def, ← hcoe]
       exact eG.coe_comp_coe_symm,
    by rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def, ← hcoe]
       exact eG.coe_symm_comp_coe⟩, rfl⟩
section NormedOnly
variable [NormedAddCommGroup W] [NormedSpace ℝ W] {f : U → V} {s : Set U} {A : U →L[ℝ] V} {u₀ : U}
    {E : Set V} {g : V → W} {B : U →L[ℝ] W} {K : ℝ≥0}
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- Directional bound `‖B v‖ ≤ K * ‖A v‖` at a density-one point under `LipschitzOnWith`. -/
theorem norm_comp_le_of_lipschitzOnWith (hf : HasFDerivWithinAt f A s u₀) (hu₀ : u₀ ∈ s) (hsub : f
    '' s ⊆ E) (hdens : Tendsto (fun r => volume (s ∩ cb u₀ r) / volume (cb (0 : U) r)) 𝓝₊ (𝓝 1))
    (hgf : HasFDerivWithinAt (g ∘ f) B s u₀) (hg : LipschitzOnWith K g E) (v : U) : ‖B v‖ ≤ K * ‖A
    v‖ := by
  by_cases hv0 : v = 0
  · simp [hv0]
  let w : U := ‖v‖⁻¹ • v; have hw : ‖w‖ = 1 := norm_smul_inv_norm hv0
  let η (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)
  have hη0 (n : ℕ) : 0 < η n := by positivity
  have hη_half (n : ℕ) : η n ≤ 1 / 2 :=
    one_div_le_one_div_of_le zero_lt_two (le_add_of_nonneg_left (Nat.cast_nonneg n))
  have hex (n : ℕ) : ∃ ρ ∈ Ioo 0 (η n), (s ∩ cb (u₀ + (ρ / 2) • w) ((η n / 4) * ρ)).Nonempty := by
    by_contra! hemp
    exact not_tendsto_volume_inter_shifted_closedBall_div_zero hdens hw (hη0 n) (hη_half n)
      (tendsto_const_nhds.congr'
        (Filter.Eventually.mono (Ioo_mem_nhdsGT (hη0 n)) fun ρ hρ => by simp [hemp ρ hρ]))
  choose ρ hρ u husD using hex; let d (n : ℕ) : U := u n - u₀
  let c (n : ℕ) : ℝ := ‖v‖ * (ρ n / 2)⁻¹
  have hy (n : ℕ) : ‖d n - (ρ n / 2) • w‖ ≤ (η n / 4) * ρ n := by
    simpa only [d, dist_eq_norm, sub_sub] using mem_closedBall.mp (husD n).2
  have htend_η : Tendsto η atTop (𝓝 0) := by
    simpa only [η, Function.comp_def, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two]
      using tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
  have hdlim : Tendsto d atTop (𝓝 0) := squeeze_zero_norm (fun n => calc
    ‖d n‖ = ‖(d n - (ρ n / 2) • w) + (ρ n / 2) • w‖ := by abel_nf
    _ ≤ (η n / 4) * ρ n + (ρ n / 2) * 1 := (norm_add_le _ _).trans (add_le_add (hy n)
        (by rw [norm_smul, Real.norm_of_nonneg (half_pos (hρ n).1).le, hw]))
    _ ≤ ρ n := by nlinarith [hη_half n, (hρ n).1]
    _ ≤ η n := (hρ n).2.le) htend_η
  have hcd : Tendsto (fun n => c n • d n) atTop (𝓝 v) := by
    rw [← tendsto_sub_nhds_zero_iff]
    refine squeeze_zero_norm (fun n => ?_) (by simpa using htend_η.const_mul (‖v‖ / 2))
    have hρ0 := (hρ n).1
    have hv_eq : c n • ((ρ n / 2) • w) = v := by
      simp only [c, w, smul_smul, mul_assoc]
      rw [inv_mul_cancel_left₀ (half_pos hρ0).ne', mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv0),
        one_smul]
    have hc0 : 0 ≤ c n := mul_nonneg (norm_nonneg v) (inv_nonneg.mpr (half_pos hρ0).le)
    have hsub_eq : c n • d n - v = c n • (d n - (ρ n / 2) • w) := (congrArg (c n • d n - ·)
      hv_eq.symm).trans (smul_sub _ _ _).symm
    rw [hsub_eq, norm_smul, Real.norm_of_nonneg hc0]
    exact (mul_le_mul_of_nonneg_left (hy n) hc0).trans_eq (by simp only [c]; field_simp; ring)
  have hdtop : ∀ᶠ n in atTop, u₀ + d n ∈ s := .of_forall fun n => by simpa [d] using (husD n).1
  exact le_of_tendsto_of_tendsto (hgf.lim hdlim hdtop hcd).norm ((hf.lim hdlim hdtop
    hcd).norm.const_mul (K : ℝ)) <| .of_forall fun n => by
      dsimp only; rw [norm_smul, norm_smul, mul_left_comm]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      simpa only [comp_apply, ← dist_eq_norm] using hg.dist_le_mul _
        (hsub (mem_image_of_mem f (by simpa [d] using (husD n).1))) _
        (hsub (mem_image_of_mem f hu₀))
end NormedOnly
section PatchChainRule
variable {f : U → V} {s : Set U} {A : U →L[ℝ] V} {u₀ : U} {L_f : ℝ≥0} {E : Set V} (hf :
    HasFDerivWithinAt f A s u₀) (hinj : Injective A) (hi : AntilipschitzWith L_f (s.domRestrict f))
    (hu₀ : u₀ ∈ s) (hsub : f '' s ⊆ E) (hdens : Tendsto (fun r => volume (s ∩ cb u₀ r) / volume (cb
    (0 : U) r)) 𝓝₊ (𝓝 1)) (hdiff : Tendsto (fun r => μHE[finrank ℝ U] ((E \ f '' s) ∩ cb (f u₀) r) /
    ω[finrank ℝ U](r)) 𝓝₊ (𝓝 0))
include hf hinj hi hu₀ hsub hdens hdiff
section NormedTarget
variable [NormedAddCommGroup W] [NormedSpace ℝ W] {g : V → W} {B : U →L[ℝ] W} {K : ℝ≥0}
/-- Parametrization chain rule for `HasTangentialFDerivAt` on an inverse-Lipschitz patch. -/
theorem hasTangentialFDerivAt_of_comp (hgf : HasFDerivWithinAt (g ∘ f) B s u₀) :
    HasTangentialFDerivAt (finrank ℝ U) E g (B ∘L Ring.inverse (A.adjoint ∘L A) ∘L A.adjoint) (f u₀)
    := by
  let P : Submodule ℝ V := LinearMap.range A.toLinearMap
  have htan_iff := fun Q => hf.isApproximateTangentPlane_iff hinj hi hu₀ hsub hdens hdiff (Q := Q)
  have hu : ∃! Q : Submodule ℝ V, IsApproximateTangentPlane (finrank ℝ U) E (f u₀) Q := ⟨P,
    (htan_iff P).mpr rfl, fun Q hQ => (htan_iff Q).mp hQ⟩
  have hP_eq := hf.approximateTangentPlane_eq_range hinj hi hu₀ hsub hdens hdiff
  let L : V →L[ℝ] W := B ∘L Ring.inverse (A.adjoint ∘L A) ∘L A.adjoint
  have hLA (u : U) : L (A u) = B u := by
    have h1 := congrArg (fun T : U →L[ℝ] U => T u) (ringInverse_adjoint_comp_self hinj)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h1
    simp only [L, ContinuousLinearMap.comp_apply, h1]
  have hAadj (v : V) : A.adjoint (P.starProjection v) = A.adjoint v := by
    symm; refine sub_eq_zero.mp (ext_inner_left ℝ fun u => ?_)
    rw [inner_zero_right, ← map_sub, A.adjoint_inner_right]
    exact Submodule.inner_right_of_mem_orthogonal (K := P) ⟨u, rfl⟩
      (P.sub_starProjection_mem_orthogonal v)
  refine ⟨hu, ?_, fun ε hε => ?_⟩
  · ext v; rw [ContinuousLinearMap.comp_apply, approximateTangentProjection_eq, hP_eq]
    exact congrArg (fun w => B (Ring.inverse (A.adjoint ∘L A) w)) (hAadj v)
  · have hLf1 : (0 : ℝ) < (L_f : ℝ) + 1 := by positivity
    set η₁ : ℝ := ε / (2 * ((L_f : ℝ) + 1)); set η₂ : ℝ := ε / (2 * (‖L‖ + 1) * ((L_f : ℝ) + 1))
    obtain ⟨δ₁, hδ₁, hδ₁b⟩ := eventually_nhds_iff_ball.mp (eventually_nhdsWithin_iff.mp
      (hgf.isLittleO.bound (by positivity : 0 < η₁)))
    obtain ⟨δ₂, hδ₂, hδ₂b⟩ := eventually_nhds_iff_ball.mp (eventually_nhdsWithin_iff.mp
      (hf.isLittleO.bound (by positivity : 0 < η₂)))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdiff (Eventually.of_forall
      fun _ => zero_le) ?_
    filter_upwards [Ioo_mem_nhdsGT (div_pos (lt_min hδ₁ hδ₂) hLf1)] with r ⟨_, hrδ⟩
    gcongr; rintro z ⟨⟨hzE, hzr⟩, hzerr⟩; refine ⟨⟨hzE, ?_⟩, hzr⟩; rintro ⟨u, hus, rfl⟩
    have hdu : dist u u₀ ≤ L_f * dist (f u) (f u₀) := by
      simpa [Subtype.dist_eq] using hi.le_mul_dist ⟨u, hus⟩ ⟨u₀, hu₀⟩
    have hnorm_u : ‖u - u₀‖ ≤ ((L_f : ℝ) + 1) * dist (f u) (f u₀) := by
      rw [← dist_eq_norm]; nlinarith [L_f.coe_nonneg, dist_nonneg (x := f u) (y := f u₀)]
    have hu_lt : dist u u₀ < min δ₁ δ₂ := ((dist_eq_norm u u₀ ▸ hnorm_u).trans
      (mul_le_mul_of_nonneg_left (mem_closedBall.mp hzr) hLf1.le)).trans_lt ((lt_div_iff₀' hLf1).mp
      hrδ)
    have herr₁ := hδ₁b u (mem_ball.mpr (hu_lt.trans_le (min_le_left _ _))) hus
    have herr₂ := hδ₂b u (mem_ball.mpr (hu_lt.trans_le (min_le_right _ _))) hus
    have hdecomp : g (f u) - g (f u₀) - L (f u - f u₀) = (g (f u) - g (f u₀) - B (u - u₀)) - L (f u
      - f u₀ - A (u - u₀)) := by
      simp only [← hLA (u - u₀), map_sub]; abel
    refine hzerr.not_ge <| calc
      ‖g (f u) - g (f u₀) - L (f u - f u₀)‖
          ≤ ‖g (f u) - g (f u₀) - B (u - u₀)‖ + ‖L (f u - f u₀ - A (u - u₀))‖ :=
            hdecomp ▸ norm_sub_le _ _
      _ ≤ η₁ * ‖u - u₀‖ + ‖L‖ * (η₂ * ‖u - u₀‖) :=
            add_le_add (by simpa only [comp_apply] using herr₁) ((L.le_opNorm _).trans (by gcongr))
      _ ≤ η₁ * (((L_f : ℝ) + 1) * dist (f u) (f u₀)) +
            (‖L‖ + 1) * (η₂ * (((L_f : ℝ) + 1) * dist (f u) (f u₀))) := by gcongr; linarith
      _ = ε * dist (f u) (f u₀) := by dsimp [η₁, η₂]; field_simp; ring
/-- Composing `tangentialFDeriv` at `f u₀` with `A` recovers the parameter derivative `B`. -/
theorem tangentialFDeriv_comp_eq (hgf : HasFDerivWithinAt (g ∘ f) B s u₀) : TFD[(finrank ℝ U), E, g,
    (f u₀)] ∘L A = B := by
  rw [(hf.hasTangentialFDerivAt_of_comp hinj hi hu₀ hsub hdens hdiff hgf).tangentialFDeriv_eq]
  ext u; have h1 := congrArg (fun T : U →L[ℝ] U => T u) (ringInverse_adjoint_comp_self hinj)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h1 ⊢; rw [h1]
/-- Sharp bound `‖tangentialFDeriv (finrank ℝ U) E g (f u₀)‖ ≤ K` on a patch. -/
theorem norm_tangentialFDeriv_le_of_lipschitzOnWith (hgf : HasFDerivWithinAt (g ∘ f) B s u₀) (hg :
    LipschitzOnWith K g E) : ‖TFD[(finrank ℝ U), E, g, (f u₀)]‖ ≤ K := by
  refine ContinuousLinearMap.opNorm_le_bound _ K.coe_nonneg fun z => ?_
  have hcomp := hf.tangentialFDeriv_comp_eq hinj hi hu₀ hsub hdens hdiff hgf
  have hP_eq := hf.approximateTangentPlane_eq_range hinj hi hu₀ hsub hdens hdiff
  let P := T[(finrank ℝ U), E, (f u₀)]
  obtain ⟨u, hu⟩ : P.starProjection z ∈ LinearMap.range A.toLinearMap := hP_eq ▸
    P.starProjection_apply_mem z
  calc ‖TFD[(finrank ℝ U), E, g, (f u₀)] z‖
      = ‖TFD[(finrank ℝ U), E, g, (f u₀)] (P.starProjection z)‖ := by
        rw [← approximateTangentProjection_eq, ← ContinuousLinearMap.comp_apply,
          tangentialFDeriv_comp_approximateTangentProjection]
    _ = ‖B u‖ := by rw [← hu, ContinuousLinearMap.coe_coe, ← ContinuousLinearMap.comp_apply, hcomp]
    _ ≤ K * ‖A u‖ := hf.norm_comp_le_of_lipschitzOnWith hu₀ hsub hdens hgf hg u
    _ = K * ‖P.starProjection z‖ := by rw [← ContinuousLinearMap.coe_coe, hu]
    _ ≤ K * ‖z‖ := by gcongr; exact P.norm_starProjection_apply_le z
end NormedTarget
section InnerProductTarget
variable [NormedAddCommGroup W] [InnerProductSpace ℝ W] {g : V → W} {B : U →L[ℝ] W} {K : ℝ≥0}
/-- Parametrization chain rule `tangentialJacobian * A.normDet = B.normDet`. -/
theorem tangentialJacobian_mul_normDet (hgf : HasFDerivWithinAt (g ∘ f) B s u₀) : TJ[(finrank ℝ U),
    E, g, (f u₀)] * A.toLinearMap.normDet = B.toLinearMap.normDet := by
  have htan := hf.hasTangentialFDerivAt_of_comp hinj hi hu₀ hsub hdens hdiff hgf
  have hcomp : (TFD[(finrank ℝ U), E, g, (f u₀)]).toLinearMap ∘ₗ A.toLinearMap = B.toLinearMap :=
    congrArg ContinuousLinearMap.toLinearMap (hf.tangentialFDeriv_comp_eq hinj hi hu₀ hsub hdens
    hdiff hgf)
  rw [← hcomp, LinearMap.normDet_comp, htan.tangentialJacobian_eq, ← htan.tangentialFDeriv_eq]
  exact congrArg (· * A.toLinearMap.normDet) (congrArg (fun S : Submodule ℝ V => ((TFD[(finrank ℝ
    U), E, g, (f u₀)]).toLinearMap.domRestrict S).normDet) (hf.approximateTangentPlane_eq_range hinj
    hi hu₀ hsub hdens hdiff))
/-- Sharp bound `tangentialJacobian (finrank ℝ U) E g (f u₀) ≤ K ^ finrank ℝ U` on a patch. -/
theorem tangentialJacobian_le_of_lipschitzOnWith (hgf : HasFDerivWithinAt (g ∘ f) B s u₀) (hg :
    LipschitzOnWith K g E) : TJ[(finrank ℝ U), E, g, (f u₀)] ≤ (K : ℝ) ^ finrank ℝ U := by
  have htan := hf.hasTangentialFDerivAt_of_comp hinj hi hu₀ hsub hdens hdiff hgf
  have hnorm := hf.norm_tangentialFDeriv_le_of_lipschitzOnWith hinj hi hu₀ hsub hdens hdiff hgf hg
  rw [htan.tangentialFDeriv_eq] at hnorm
  exact htan.tangentialJacobian_le_opNorm_pow.trans (pow_le_pow_left₀ (norm_nonneg _) hnorm _)
end InnerProductTarget
end PatchChainRule
end HasFDerivWithinAt
