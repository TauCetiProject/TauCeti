/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearIsometry
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Graph patches over hyperplanes are Lipschitz charts

Let `F` be a real inner product space, `ν ≠ 0` a vector of `F` and `γ : F → ℝ` a Lipschitz
function invariant under translation along `ν`. Near a point `x`, a set `Ω ⊆ F` has a *graph
patch* when

`ball x r ∩ Ω = ball x r ∩ {z | γ z < ⟪z, ν⟫}`,

that is, near `x` the set `Ω` is the region above the graph of a function over the hyperplane
`ν^⊥`. This is how domains with `C^k` boundary are described in the Schauder theory: graphs over
hyperplanes of `F` itself, with no separate coordinate space. This file shows that such a patch
is a Lipschitz boundary chart in the sense of `Set.IsLipschitzChart`, in the coordinates
`z ↦ (⟪z - x, ν⟫, z - x projected to ν^⊥)` for unit `ν`, so that a set with a graph patch at every
frontier point is a Lipschitz domain. The analysis of Lipschitz domains (segment chains, Hölder
bounds from derivative bounds, the Sobolev theory) then applies to it.

## Main declarations

* `TauCeti.exists_isLipschitzChart_of_ball_inter_eq`: a graph patch around `x` over the
  hyperplane `ν^⊥` of a unit vector `ν` is a Lipschitz chart centred at `x`, modelled on any space
  linearly isometric to `ν^⊥`.
* `TauCeti.isLipschitzDomain_of_forall_ball_inter_eq`: a set in an inner product space of
  dimension `n + 1` with a graph patch at every frontier point is a Lipschitz domain modelled on
  `EuclideanSpace ℝ (Fin n)`.
-/

public section

namespace TauCeti

open Metric Set Module
open scoped NNReal InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **A graph patch is a Lipschitz chart.** Let `ν` be a unit vector of a real inner product
space `F`, identified on its orthogonal hyperplane `ν^⊥` with a normed space `E` by a linear
isometry `ψ`, and let `γ : F → ℝ` be `G`-Lipschitz and invariant under translation along `ν`. If
`ball x r ∩ Ω = ball x r ∩ {z | γ z < ⟪z, ν⟫}` with `r > 0`, then `Ω` has a Lipschitz chart centred
at `x`, with constant `G`, on the cylinder of half-height `r / 2` and radius `r / 2`. -/
theorem exists_isLipschitzChart_of_ball_inter_eq {Ω : Set F} {x ν : F} {γ : F → ℝ} {G : ℝ≥0}
    {r : ℝ} (ψ : (ℝ ∙ ν)ᗮ ≃ₗᵢ[ℝ] E) (hν : ‖ν‖ = 1) (hγ : LipschitzWith G γ)
    (hγν : ∀ z (t : ℝ), γ (z + t • ν) = γ z) (hr : 0 < r)
    (hΩ : ball x r ∩ Ω = ball x r ∩ {z | γ z < ⟪z, ν⟫_ℝ}) :
    ∃ (e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (φ : E → ℝ),
      e x = 0 ∧ Ω.IsLipschitzChart e φ G (r / 2) (r / 2) := by
  -- The coordinates `z ↦ (⟪z - x, ν⟫, ψ (z - x projected to ν^⊥))`, inverse to
  -- `(t, w) ↦ x + ψ⁻¹ w + t ν`, and the graph `φ` over `ν^⊥`.
  set L : F ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E) := (orthogonalLineIsometry ν hν).symm.trans
    ((LinearIsometryEquiv.withLpProdComm 2 ℝ _ _).trans
      (LinearIsometryEquiv.withLpProdCongr 2 (.refl ℝ ℝ) ψ))
  set e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E) :=
    (AffineIsometryEquiv.vaddConst ℝ x).symm.trans L.toAffineIsometryEquiv
  have hex : e x = 0 := by simp [e]
  have he : ∀ w, e.symm w = ((ψ.symm w.snd : (ℝ ∙ ν)ᗮ) : F) + w.fst • ν + x := fun w => by
    have hL : L.symm w = ((ψ.symm w.snd : (ℝ ∙ ν)ᗮ) : F) + w.fst • ν := by
      -- Write `w` as the pair of its two coordinates.
      obtain ⟨⟨t, y⟩⟩ := w
      rw [LinearIsometryEquiv.symm_apply_eq, ← orthogonalLineIsometry_apply ν hν]
      simp only [L, LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_apply_apply,
        LinearIsometryEquiv.withLpProdComm_apply, LinearIsometryEquiv.withLpProdCongr_apply,
        WithLp.toLp_fst, WithLp.toLp_snd, LinearIsometryEquiv.coe_refl, id_eq,
        LinearIsometryEquiv.apply_symm_apply]
    rw [AffineIsometryEquiv.symm_apply_eq, ← hL]
    simp [e]
  set φ : E → ℝ := fun w => γ (x + ψ.symm w) - ⟪x, ν⟫_ℝ
  have hφ : LipschitzWith G φ := LipschitzWith.of_dist_le_mul fun w w' => by
    simp only [φ, Real.dist_eq, sub_sub_sub_cancel_right]
    rw [← Real.dist_eq]
    refine (hγ.dist_le_mul _ _).trans_eq ?_
    rw [dist_add_left, ← Subtype.dist_eq, LinearIsometryEquiv.dist_map]
  refine ⟨e, φ, hex, isLipschitzChart_of_forall_mem_iff (half_pos hr) (half_pos hr) hφ
    fun w hw => ?_⟩
  -- A point of the cylinder lies in `ball x r`, where `Ω` is the region above the graph.
  rw [mem_normalCylinder] at hw
  have hball : e.symm w ∈ ball x r := by
    rw [mem_ball, ← e.symm_apply_eq.2 hex.symm, e.symm.dist_map, dist_zero_right]
    have h1 : ‖w‖ ^ 2 < r ^ 2 := by
      rw [WithLp.prod_norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]
      nlinarith [norm_nonneg w.snd]
    exact lt_of_pow_lt_pow_left₀ 2 hr.le h1
  have hmem : e.symm w ∈ Ω ↔ γ (e.symm w) < ⟪e.symm w, ν⟫_ℝ := by
    simpa only [mem_inter_iff, hball, true_and, mem_ofPred_eq] using Set.ext_iff.1 hΩ (e.symm w)
  -- `γ` is invariant along `ν`, and the `ν`-coordinate of `e.symm w - x` is `w.fst`.
  have hγw : γ (((ψ.symm w.snd : (ℝ ∙ ν)ᗮ) : F) + w.fst • ν + x) = γ (x + ψ.symm w.snd) := by
    rw [show ((ψ.symm w.snd : (ℝ ∙ ν)ᗮ) : F) + w.fst • ν + x = x + ψ.symm w.snd + w.fst • ν by
      abel, hγν]
  have hinner : ⟪((ψ.symm w.snd : (ℝ ∙ ν)ᗮ) : F) + w.fst • ν + x, ν⟫_ℝ = w.fst + ⟪x, ν⟫_ℝ := by
    rw [inner_add_left, real_inner_comm ν, inner_add_smul ν hν]
  rw [hmem, he, hγw, hinner]
  simp only [φ]
  constructor <;> intro h <;> linarith

/-- **Graph patches make a Lipschitz domain.** Let `F` be a real inner product space of dimension
`n + 1` and `Ω ⊆ F` a set such that near each point `x` of its frontier it is the region above a
Lipschitz graph over a hyperplane: `ball x r ∩ Ω = ball x r ∩ {z | γ z < ⟪z, ν⟫}` for some `r > 0`,
some `ν ≠ 0` and some Lipschitz `γ : F → ℝ` invariant under translation along `ν`. Then `Ω` is a
Lipschitz domain modelled on `EuclideanSpace ℝ (Fin n)`. -/
theorem isLipschitzDomain_of_forall_ball_inter_eq {n : ℕ} (hF : finrank ℝ F = n + 1) {Ω : Set F}
    (h : ∀ x ∈ frontier Ω, ∃ (ν : F) (γ : F → ℝ) (G : ℝ≥0) (r : ℝ), ν ≠ 0 ∧
      LipschitzWith G γ ∧ (∀ z (t : ℝ), γ (z + t • ν) = γ z) ∧ 0 < r ∧
      ball x r ∩ Ω = ball x r ∩ {z | γ z < ⟪z, ν⟫_ℝ}) :
    Ω.IsLipschitzDomain (EuclideanSpace ℝ (Fin n)) := by
  have : Fact (finrank ℝ F = n + 1) := ⟨hF⟩
  refine Set.isLipschitzDomain_iff_exists_mem_normalCylinder.2 fun x hx => ?_
  obtain ⟨ν, γ, G, r, hν, hγ, hγν, hr, hΩ⟩ := h x hx
  -- Normalize `ν` to the unit vector `ν' = ‖ν‖⁻¹ • ν`, and `γ` accordingly.
  set c : ℝ := ‖ν‖⁻¹
  have hc : 0 < c := inv_pos.2 (norm_pos_iff.2 hν)
  have hν' : ‖c • ν‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg hc.le, inv_mul_cancel₀ (norm_ne_zero_iff.2 hν)]
  obtain ⟨e, φ, hex, hchart⟩ := exists_isLipschitzChart_of_ball_inter_eq (γ := fun z => c * γ z)
    (OrthonormalBasis.fromOrthogonalSpanSingleton n (norm_ne_zero_iff.1 (by simp [hν']))).repr
    hν' ((lipschitzWith_smul c).comp hγ) (fun z t => by rw [smul_smul, hγν]) hr (by
      ext z
      simp only [mem_inter_iff, mem_ofPred_eq, inner_smul_right, mul_lt_mul_iff_right₀ hc]
      exact Set.ext_iff.1 hΩ z)
  exact ⟨e, φ, _, _, _, hchart, hex ▸ zero_mem_normalCylinder hchart.height_pos hchart.radius_pos⟩

end TauCeti
