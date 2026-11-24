/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Normal.Rescaling

/-!
# Taming forms for the normal linearization along a pseudoholomorphic curve

Let `C` be an embedded pseudoholomorphic curve in an almost complex four-manifold, read in
coordinates `(z, W) ∈ E × N` in which `C` is the zero section, and let
`J_N(z, W) (v, n) = (j(z) v, ∂_W J_NE(z, 0)[W] v + J_NN(z, 0) n)` be the normal linearization of the
almost complex structure along `C` (`TauCeti.normalLinearization`). In Taubes's analysis of
Seiberg–Witten solutions concentrating along `C`, the normalized currents near `C` are
approximately positive `(1,1)`-currents for `J_N`, and their mass is controlled by their pairing
with a closed two-form `Ω` taming `J_N`. Such a form is built as

`Ω = K π^* ω_C + dλ`,

where `ω_C` is an area form on the curve, `π` is the projection to the curve, `dλ` restricts to an
area form on each normal fibre, and `K` is a large constant. This file proves that `Ω` tames `J_N`
on a disk bundle `{‖W‖ ≤ R}` once `K` is large compared with `R`, and that the taming persists for
the normal dilations of `J` at small scale.

The block `E → N` of `J_N(z, W)`, which is linear in `W`, is the only obstruction: the vertical
directions `{0} × N` are `J_N`-invariant and the projection to `E` intertwines `J_N` with `j(z)`,
so on a vector `u = (v, n)` the pairing `Ω(u, J_N u)` is `K ω_C(v, j v)` plus the vertical term
`dλ((0, n), J_N (0, n))` plus cross terms bounded by `‖dλ‖ ‖J_N‖ ‖v‖ (‖v‖ + 2 ‖n‖)`. If both
taming terms are at least `m` times the squared norms, then
`Ω(u, J_N u) ≥ (m / 2) ‖u‖²` as soon as `K ≥ 1 / 2 + t + 2 t²` with `t = ‖dλ‖ ‖J_N‖ / m`, by
completing the square. The operator norm of `J_N(z, W)` grows at most linearly in `‖W‖`
(`TauCeti.norm_normalLinearization_le`), so on the disk bundle of radius `R` the required `K` is
of order `R²`.

The qualitative form of this statement, for a linear complex structure with a complex-linear
projection on a finite-dimensional space, is
`TauCeti.SymplecticForm.eventually_exists_pos_forall_mul_norm_sq_le_mul_apply_add_apply` in
`TauCeti.Geometry.Symplectic.AlmostComplex.Projection`, proved by compactness. The estimate here is
the explicit refinement for the splitting `E × N`: it gives the constants `m / 2` and
`K ≥ 1 / 2 + t + 2 t²`, and it needs neither finite dimension, nor `J_N² = -1`, nor `ω`
symplectic. Applying the compactness result to `J_N` would require `J` to be differentiable along
the curve, to square to `-1` near it and to preserve `E × {0}` there, which make `J_N(z, W)` a
complex structure (`TauCeti.normalLinearization_apply_normalLinearization_apply`).

## Main results

* `TauCeti.div_two_mul_norm_sq_le_mul_apply_add_apply`: for an endomorphism `L` of `E × N` that
  preserves `{0} × N`, if `ω` tames the block of `L` on `E` and `σ` tames it on `{0} × N`, both
  with constant `m > 0`, then `K π^* ω + σ` tames `L` with constant `m / 2` for every
  `K ≥ 1 / 2 + t + 2 t²`, `t = ‖σ‖ ‖L‖ / m`.
* `TauCeti.div_two_mul_norm_sq_le_mul_apply_add_apply_normalLinearization`: the same for
  `J_N(z, W)`, with the hypotheses read off from `J(z, 0)` and `‖J_N(z, W)‖` replaced by its
  bound `‖J(z, 0)‖ + ‖dJ(z, 0)‖ ‖W‖`.
* `TauCeti.exists_forall_div_two_mul_norm_sq_le_normalLinearization`: over a compact set `B` of
  base points and a disk bundle `{‖W‖ ≤ R}`, one constant `K₀` works for all `K ≥ K₀`, uniformly.
* `TauCeti.eventually_forall_div_two_mul_norm_sq_le_apply_normalDilation`: a family of forms
  taming `J_N` with constant `c` on a compact set tames the normal dilations `δ_a^* J` with constant
  `c / 2` for all small `a ≠ 0`.

Forms are represented by continuous bilinear maps; closedness of `Ω` and the identification of
`dλ` with the curvature data of a Hermitian connection on the normal bundle are not treated here.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

open Filter Topology

namespace TauCeti

variable {E N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup N]
  [NormedSpace ℝ N]

/-! ### Taming by a large multiple of a base form -/

/-- **A large multiple of a base form plus a vertical taming form tames.** Let `L` be an
endomorphism of `E × N` preserving `{0} × N`, let `ω` tame its block on `E`,
`ω(v, (L (v, 0)).1) ≥ m ‖v‖²`, and let `σ` tame it on `{0} × N`,
`σ((0, n), L (0, n)) ≥ m ‖n‖²`, with `m > 0`. If `‖σ‖ ‖L‖ ≤ s` and
`K ≥ 1 / 2 + s / m + 2 (s / m)²`, then `K π^* ω + σ` tames `L` with constant `m / 2`. -/
theorem div_two_mul_norm_sq_le_mul_apply_add_apply {L : E × N →L[ℝ] E × N}
    {ω : E →L[ℝ] E →L[ℝ] ℝ} {σ : E × N →L[ℝ] E × N →L[ℝ] ℝ} {m s K : ℝ} (hm : 0 < m)
    (hL : ∀ n, (L (0, n)).1 = 0) (hω : ∀ v, m * ‖v‖ ^ 2 ≤ ω v (L (v, 0)).1)
    (hσ : ∀ n, m * ‖n‖ ^ 2 ≤ σ (0, n) (L (0, n))) (hs : ‖σ‖ * ‖L‖ ≤ s)
    (hK : 1 / 2 + s / m + 2 * (s / m) ^ 2 ≤ K) (u : E × N) :
    m / 2 * ‖u‖ ^ 2 ≤ K * ω u.1 (L u).1 + σ u (L u) := by
  obtain ⟨v, n⟩ := u
  have hu : ((v, n) : E × N) = (v, 0) + (0, n) := by simp
  have hLu : (L (v, n)).1 = (L (v, 0)).1 := by rw [hu, map_add, Prod.fst_add, hL, add_zero]
  have hσu : σ (v, n) (L (v, n)) = σ (v, 0) (L (v, 0)) + σ (v, 0) (L (0, n)) +
      σ (0, n) (L (v, 0)) + σ (0, n) (L (0, n)) := by
    rw [hu, map_add, map_add, add_apply, map_add, map_add]
    ring
  -- Each cross term is at most `s` times the product of the norms.
  have hcross (x y : E × N) : -(s * ‖x‖ * ‖y‖) ≤ σ x (L y) := by
    refine neg_le_of_abs_le ?_
    calc |σ x (L y)| = ‖σ x (L y)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖σ‖ * ‖x‖ * (‖L‖ * ‖y‖) :=
        (σ.le_opNorm₂ x (L y)).trans (by gcongr; exact L.le_opNorm y)
      _ = ‖σ‖ * ‖L‖ * (‖x‖ * ‖y‖) := by ring
      _ ≤ s * (‖x‖ * ‖y‖) := by gcongr
      _ = s * ‖x‖ * ‖y‖ := by ring
  have hv : ‖((v, 0) : E × N)‖ = ‖v‖ := by simp
  have hn : ‖((0, n) : E × N)‖ = ‖n‖ := by simp
  have h₁ := hcross (v, 0) (v, 0)
  have h₂ := hcross (v, 0) (0, n)
  have h₃ := hcross (0, n) (v, 0)
  rw [hv] at h₁ h₂ h₃
  rw [hn] at h₂ h₃
  have hnorm : ‖((v, n) : E × N)‖ ^ 2 ≤ ‖v‖ ^ 2 + ‖n‖ ^ 2 := by
    rw [Prod.norm_mk]
    rcases le_total ‖v‖ ‖n‖ with h | h
    · rw [max_eq_right h]; nlinarith [sq_nonneg ‖v‖]
    · rw [max_eq_left h]; nlinarith [sq_nonneg ‖n‖]
  -- Complete the square, writing `s = t m`.
  set t := s / m
  have hst : s = t * m := (div_mul_cancel₀ s hm.ne').symm
  have ht : 0 ≤ t := div_nonneg ((by positivity : 0 ≤ ‖σ‖ * ‖L‖).trans hs) hm.le
  have hK₀ : 0 ≤ K := by nlinarith [sq_nonneg t]
  have hωK : K * (m * ‖v‖ ^ 2) ≤ K * ω v (L (v, 0)).1 := mul_le_mul_of_nonneg_left (hω v) hK₀
  have hsq : 0 ≤ m * (2 * t * ‖v‖ - ‖n‖) ^ 2 := by positivity
  have hKt : 0 ≤ (K - (1 / 2 + t + 2 * t ^ 2)) * (m * ‖v‖ ^ 2) :=
    mul_nonneg (by linarith) (by positivity)
  simp only at hLu ⊢
  rw [hLu, hσu]
  rw [hst] at h₁ h₂ h₃
  nlinarith [hσ n]

/-- **A taming form for the normal linearization.** Let `ω` tame the structure `j(z)` of the zero
section at `z`, `ω(v, (J(z, 0) (v, 0)).1) ≥ m ‖v‖²`, and let `σ` tame the normal block of
`J(z, 0)`, `σ((0, n), (0, (J(z, 0) (0, n)).2)) ≥ m ‖n‖²`, with `m > 0`. If
`‖σ‖ (‖J(z, 0)‖ + ‖dJ(z, 0)‖ ‖W‖) ≤ s` and `K ≥ 1 / 2 + s / m + 2 (s / m)²`, then
`K π^* ω + σ` tames `J_N(z, W)` with constant `m / 2`. -/
theorem div_two_mul_norm_sq_le_mul_apply_add_apply_normalLinearization
    {J : E × N → E × N →L[ℝ] E × N} {ω : E →L[ℝ] E →L[ℝ] ℝ} {σ : E × N →L[ℝ] E × N →L[ℝ] ℝ}
    {z : E} {W : N} {m s K : ℝ} (hm : 0 < m) (hω : ∀ v, m * ‖v‖ ^ 2 ≤ ω v (J (z, 0) (v, 0)).1)
    (hσ : ∀ n, m * ‖n‖ ^ 2 ≤ σ (0, n) (0, (J (z, 0) (0, n)).2))
    (hs : ‖σ‖ * (‖J (z, 0)‖ + ‖fderiv ℝ J (z, 0)‖ * ‖W‖) ≤ s)
    (hK : 1 / 2 + s / m + 2 * (s / m) ^ 2 ≤ K) (u : E × N) :
    m / 2 * ‖u‖ ^ 2 ≤
      K * ω u.1 (normalLinearization J (z, W) u).1 + σ u (normalLinearization J (z, W) u) := by
  refine div_two_mul_norm_sq_le_mul_apply_add_apply hm (fun n ↦ by simp [Prod.mk_zero_zero])
    (fun v ↦ by simpa using hω v) (fun n ↦ by simpa [Prod.mk_zero_zero] using hσ n) ?_ hK u
  exact (mul_le_mul_of_nonneg_left (norm_normalLinearization_le J (z, W)) (norm_nonneg σ)).trans hs

/-- **A uniform taming form on a disk bundle over a compact window.** Let `z ↦ J(z, 0)` and
`z ↦ dJ(z, 0)` be continuous on a compact set `B`, let the forms `ω z` tame `j(z)` and the forms
`σ (z, W)` tame the normal blocks of `J(z, 0)`, uniformly with constant `m > 0`, for `z ∈ B` and
`‖W‖ ≤ R`, and let `‖σ (z, W)‖ ≤ S` there. Then for all `K` large enough, `K π^* ω + σ` tames
`J_N` with constant `m / 2` at every point of the disk bundle of radius `R` over `B`. -/
theorem exists_forall_div_two_mul_norm_sq_le_normalLinearization
    {J : E × N → E × N →L[ℝ] E × N} {ω : E → E →L[ℝ] E →L[ℝ] ℝ}
    {σ : E × N → E × N →L[ℝ] E × N →L[ℝ] ℝ} {B : Set E} {m R S : ℝ} (hB : IsCompact B)
    (hJ : ContinuousOn (fun z ↦ J (z, 0)) B) (hdJ : ContinuousOn (fun z ↦ fderiv ℝ J (z, 0)) B)
    (hm : 0 < m) (hω : ∀ z ∈ B, ∀ v, m * ‖v‖ ^ 2 ≤ ω z v (J (z, 0) (v, 0)).1)
    (hσ : ∀ z ∈ B, ∀ W : N, ‖W‖ ≤ R → ∀ n,
      m * ‖n‖ ^ 2 ≤ σ (z, W) (0, n) (0, (J (z, 0) (0, n)).2))
    (hS : ∀ z ∈ B, ∀ W : N, ‖W‖ ≤ R → ‖σ (z, W)‖ ≤ S) :
    ∃ K₀, ∀ K, K₀ ≤ K → ∀ z ∈ B, ∀ W : N, ‖W‖ ≤ R → ∀ u : E × N,
      m / 2 * ‖u‖ ^ 2 ≤ K * ω z u.1 (normalLinearization J (z, W) u).1 +
        σ (z, W) u (normalLinearization J (z, W) u) := by
  obtain ⟨A, hA⟩ := hB.exists_bound_of_continuousOn hJ
  -- The codomain is named to select its norm topology.
  obtain ⟨A', hA'⟩ :=
    hB.exists_bound_of_continuousOn (E := E × N →L[ℝ] E × N →L[ℝ] E × N) hdJ
  set s := max S 0 * (max A 0 + max A' 0 * max R 0)
  refine ⟨1 / 2 + s / m + 2 * (s / m) ^ 2, fun K hK z hz W hW u ↦ ?_⟩
  refine div_two_mul_norm_sq_le_mul_apply_add_apply_normalLinearization hm (hω z hz)
    (hσ z hz W hW) ?_ hK u
  have hJz : ‖J (z, 0)‖ + ‖fderiv ℝ J (z, 0)‖ * ‖W‖ ≤ max A 0 + max A' 0 * max R 0 := by
    gcongr
    · exact (hA z hz).trans (le_max_left _ _)
    · exact (hA' z hz).trans (le_max_left _ _)
    · exact hW.trans (le_max_left _ _)
  exact mul_le_mul ((hS z hz W hW).trans (le_max_left _ _)) hJz (by positivity) (by positivity)

/-! ### Persistence under normal dilation -/

/-- **Taming persists under normal dilation.** Let `J` be `C¹` on an open set `U` with the zero
section `J`-holomorphic where it meets `U`, and let `K` be a compact set with `(z, 0) ∈ U` for
`(z, W) ∈ K`. If forms `Ω p` with `‖Ω p‖ ≤ M` tame `J_N` with constant `c > 0` at every `p ∈ K`,
then they tame the normal dilations `δ_a^* J` with constant `c / 2` on `K` for all small `a ≠ 0`. -/
theorem eventually_forall_div_two_mul_norm_sq_le_apply_normalDilation
    {J : E × N → E × N →L[ℝ] E × N} {Ω : E × N → E × N →L[ℝ] E × N →L[ℝ] ℝ}
    {U K : Set (E × N)} {c M : ℝ} [CompleteSpace N] (hU : IsOpen U) (hJ : ContDiffOn ℝ 1 J U)
    (hJ₀ : ∀ z, (z, 0) ∈ U → ∀ v, (J (z, 0) (v, 0)).2 = 0) (hK : IsCompact K)
    (hKU : ∀ p ∈ K, (p.1, 0) ∈ U) (hc : 0 < c) (hΩ : ∀ p ∈ K, ‖Ω p‖ ≤ M)
    (hJN : ∀ p ∈ K, ∀ u, c * ‖u‖ ^ 2 ≤ Ω p u (normalLinearization J p u)) :
    ∀ᶠ a in 𝓝[≠] 0, ∀ p ∈ K, ∀ u, c / 2 * ‖u‖ ^ 2 ≤ Ω p u (normalDilation J a p u) := by
  set δ := c / (2 * (|M| + 1))
  have hδ : 0 < δ := by positivity
  filter_upwards [Metric.tendstoUniformlyOn_iff.1
    (tendstoUniformlyOn_normalDilation_of_isOpen hU hJ hJ₀ hK hKU) δ hδ] with a ha p hp u
  -- The defect `Ω p u ((J_N p - δ_a^* J p) u)` is at most `|M| δ ‖u‖² ≤ (c / 2) ‖u‖²`.
  have hd : ‖normalLinearization J p - normalDilation J a p‖ ≤ δ := by
    rw [← dist_eq_norm]; exact (ha p hp).le
  have hdefect : Ω p u ((normalLinearization J p - normalDilation J a p) u) ≤
      |M| * δ * ‖u‖ ^ 2 := by
    calc Ω p u ((normalLinearization J p - normalDilation J a p) u)
        ≤ ‖Ω p u ((normalLinearization J p - normalDilation J a p) u)‖ := Real.le_norm_self _
      _ ≤ ‖Ω p‖ * ‖u‖ * (‖normalLinearization J p - normalDilation J a p‖ * ‖u‖) :=
        ((Ω p).le_opNorm₂ _ _).trans (by gcongr; exact ContinuousLinearMap.le_opNorm _ _)
      _ ≤ |M| * ‖u‖ * (δ * ‖u‖) := by
        gcongr
        exact (hΩ p hp).trans (le_abs_self M)
      _ = |M| * δ * ‖u‖ ^ 2 := by ring
  have hMδ : |M| * δ ≤ c / 2 := by
    rw [show |M| * δ = c / 2 * (|M| / (|M| + 1)) by
      simp only [δ]; field_simp]
    exact mul_le_of_le_one_right (by positivity)
      ((div_le_one (by positivity)).2 (by linarith))
  have hsplit : Ω p u (normalDilation J a p u) = Ω p u (normalLinearization J p u) -
      Ω p u ((normalLinearization J p - normalDilation J a p) u) := by
    rw [sub_apply, map_sub]; ring
  rw [hsplit]
  nlinarith [hJN p hp u, sq_nonneg ‖u‖]

end TauCeti
