/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import TauCeti.Analysis.InnerProductSpace.Laplacian.LocalExtr

/-!
# The minimum principle for lower envelopes and least eigenvalues

Let `q : E → ι → ℝ` be a family of functions on a finite-dimensional real inner product space `E`,
indexed by a compact set `S` of parameters, jointly continuous and `C²` in the first variable. Its
**lower envelope** `x ↦ min_{s ∈ S} q x s` is continuous but in general not differentiable, so the
maximum principle cannot be applied to it directly. It can be tested instead: if `(x₀, s₀)`
minimizes `q` over `K × S` with `x₀` in the interior of `K`, then `x₀` is an interior local minimum
of the single `C²` function `y ↦ q y s₀`, whose Laplacian is therefore nonnegative at `x₀`
(`TauCeti.laplacian_nonneg_of_isMinOn_prod`). The parameter `s₀` is a minimizing parameter at
`x₀`, so a differential inequality need only be checked at minimizing parameters.

This gives a quantitative minimum principle for lower envelopes
(`TauCeti.min_le_of_laplacian_le_mul_add_of_isMinOn`). Suppose that `q ≥ m` on `frontier K`
and that, at each interior point `x` and each parameter `s` minimizing `q x` with `q x s < m`,

`Δ (q · s) x ≤ c x · q x s + k`,  `c x ≥ c₀ > 0`,  `k ≥ 0`.

Then `q ≥ min m (-k / c₀)` on `K × S`. At a minimizing point the Laplacian is nonnegative, so a
negative minimum `μ` satisfies `0 ≤ c₀ μ + k`.

The main application is to the **least eigenvalue** of a field of symmetric bilinear forms
`B : E → BilinForm ℝ V` on a finite-dimensional inner product space `V`. It is the lower envelope
of `(x, v) ↦ B x v v` over the unit sphere of `V`, a minimizing parameter at `x` is a unit
eigenvector for the least eigenvalue of `B x`, and the conclusion is the lower bound
`B x v v ≥ min m (-k / c₀) ‖v‖²` for every `v`
(`TauCeti.min_mul_norm_sq_le_of_laplacian_le_mul_add_of_isMinOn`). Testing with a fixed minimizing
eigenvector avoids any regularization of the least eigenvalue across eigenvalue crossings. This
is the elliptic form of Hamilton's maximum principle for tensors, the mechanism by which Taubes
bounds the Hermitian part of the curvature of large-parameter Seiberg–Witten solutions from below.

## Main results

* `TauCeti.laplacian_nonneg_of_isMinOn_prod`: the Laplacian of `q · s₀` is nonnegative at an
  interior minimizer `(x₀, s₀)` of `q` over `K × S`.
* `TauCeti.min_le_of_laplacian_le_mul_add_of_isMinOn`: the quantitative minimum principle for
  lower envelopes.
* `TauCeti.min_mul_norm_sq_le_of_laplacian_le_mul_add_of_isMinOn`: the minimum principle for the
  least eigenvalue of a field of bilinear forms.

## References

* R. S. Hamilton, *Four-manifolds with positive curvature operator*, J. Differential Geom. 24
  (1986), 153–179, §4.
* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian Set Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [TopologicalSpace ι]

omit [TopologicalSpace ι] in
/-- **The minimum test for a lower envelope.** If `(x, s)` minimizes `q` over `K × S` and `x` lies
in the interior of `K`, then the Laplacian of the `C²` function `q · s` is nonnegative at `x`. -/
theorem laplacian_nonneg_of_isMinOn_prod {K : Set E} {S : Set ι} {q : E → ι → ℝ} {x : E} {s : ι}
    (hx : x ∈ interior K) (hs : s ∈ S)
    (hmin : IsMinOn (fun p : E × ι ↦ q p.1 p.2) (K ×ˢ S) (x, s))
    (hcd : ContDiffAt ℝ 2 (fun y ↦ q y s) x) :
    0 ≤ Δ (fun y ↦ q y s) x := by
  refine laplacian_nonneg_of_isLocalMin hcd ?_
  filter_upwards [mem_interior_iff_mem_nhds.1 hx] with y hy
  exact isMinOn_iff.1 hmin (y, s) ⟨hy, hs⟩

/-- **The minimum principle for lower envelopes.** Let `K` and `S` be compact and let `q` be
jointly continuous on `K × S` and `C²` in its first variable on `interior K`. Suppose that
`q ≥ m` on `frontier K × S`, and that at each interior point `x` and each parameter `s` minimizing
`q x` over `S` with `q x s < m`, the differential inequality `Δ (q · s) x ≤ c x · q x s + k` holds,
with `c ≥ c₀ > 0` and `k ≥ 0`. Then `q ≥ min m (-k / c₀)` on `K × S`. -/
theorem min_le_of_laplacian_le_mul_add_of_isMinOn {K : Set E} (hK : IsCompact K) {S : Set ι}
    (hS : IsCompact S) {q : E → ι → ℝ} {c : E → ℝ} {m k c₀ : ℝ} (hc₀ : 0 < c₀) (hk : 0 ≤ k)
    (hcont : ContinuousOn (fun p : E × ι ↦ q p.1 p.2) (K ×ˢ S))
    (hcd : ∀ ⦃x⦄, x ∈ interior K → ∀ ⦃s⦄, s ∈ S → ContDiffAt ℝ 2 (fun y ↦ q y s) x)
    (hc : ∀ ⦃x⦄, x ∈ interior K → c₀ ≤ c x)
    (hsuper : ∀ ⦃x⦄, x ∈ interior K → ∀ ⦃s⦄, s ∈ S → IsMinOn (q x) S s → q x s < m →
      Δ (fun y ↦ q y s) x ≤ c x * q x s + k)
    (hbdry : ∀ ⦃x⦄, x ∈ frontier K → ∀ ⦃s⦄, s ∈ S → m ≤ q x s) :
    ∀ ⦃x⦄, x ∈ K → ∀ ⦃s⦄, s ∈ S → min m (-(k / c₀)) ≤ q x s := by
  intro x hx s hs
  -- Compare with the value `μ` of `q` at a minimizer `(x₀, s₀)` over `K × S`.
  obtain ⟨⟨x₀, s₀⟩, ⟨hx₀, hs₀⟩, hmin⟩ := (hK.prod hS).exists_isMinOn ⟨(x, s), hx, hs⟩ hcont
  refine le_trans ?_ (isMinOn_iff.1 hmin (x, s) ⟨hx, hs⟩)
  dsimp only
  by_cases hfr : x₀ ∈ frontier K
  · exact min_le_of_left_le (hbdry hfr hs₀)
  have hint : x₀ ∈ interior K := by
    by_contra h
    exact hfr ⟨subset_closure hx₀, h⟩
  by_cases hm : m ≤ q x₀ s₀
  · exact min_le_of_left_le hm
  rw [not_le] at hm
  -- At the interior minimizer, `0 ≤ Δ (q · s₀) x₀ ≤ c x₀ μ + k`.
  have hlap := laplacian_nonneg_of_isMinOn_prod hint hs₀ hmin (hcd hint hs₀)
  have hle := hsuper hint hs₀ (fun t ht ↦ isMinOn_iff.1 hmin (x₀, t) ⟨hx₀, ht⟩) hm
  refine min_le_of_right_le ?_
  rcases le_or_gt 0 (q x₀ s₀) with hμ | hμ
  · linarith [div_nonneg hk hc₀.le]
  · have h₁ : c x₀ * q x₀ s₀ ≤ c₀ * q x₀ s₀ := mul_le_mul_of_nonpos_right (hc hint) hμ.le
    rw [neg_le, le_div_iff₀ hc₀]
    nlinarith

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The minimum principle for the least eigenvalue.** Let `B` be a field of bilinear forms on
`V` over a compact set `K`, with `(x, v) ↦ B x v v` continuous on `K × sphere 0 1` and `C²` in `x`
on `interior K` for each unit `v`. Suppose that `B x v v ≥ m` for `x ∈ frontier K` and unit `v`,
and that at each interior point `x` and each unit `v` minimizing `B x w w` over the unit sphere
with `B x v v < m`, the differential inequality `Δ (B · v v) x ≤ c x · B x v v + k` holds, with
`c ≥ c₀ > 0` and `k ≥ 0`. Then `B x v v ≥ min m (-k / c₀) ‖v‖²` on `K` for every `v`. -/
theorem min_mul_norm_sq_le_of_laplacian_le_mul_add_of_isMinOn {K : Set E} (hK : IsCompact K)
    {B : E → LinearMap.BilinForm ℝ V} {c : E → ℝ} {m k c₀ : ℝ} (hc₀ : 0 < c₀) (hk : 0 ≤ k)
    (hcont : ContinuousOn (fun p : E × V ↦ B p.1 p.2 p.2) (K ×ˢ sphere 0 1))
    (hcd : ∀ ⦃x⦄, x ∈ interior K → ∀ ⦃v⦄, v ∈ sphere (0 : V) 1 →
      ContDiffAt ℝ 2 (fun y ↦ B y v v) x)
    (hc : ∀ ⦃x⦄, x ∈ interior K → c₀ ≤ c x)
    (hsuper : ∀ ⦃x⦄, x ∈ interior K → ∀ ⦃v⦄, v ∈ sphere (0 : V) 1 →
      IsMinOn (fun w ↦ B x w w) (sphere 0 1) v → B x v v < m →
      Δ (fun y ↦ B y v v) x ≤ c x * B x v v + k)
    (hbdry : ∀ ⦃x⦄, x ∈ frontier K → ∀ ⦃v⦄, v ∈ sphere (0 : V) 1 → m ≤ B x v v) :
    ∀ ⦃x⦄, x ∈ K → ∀ v, min m (-(k / c₀)) * ‖v‖ ^ 2 ≤ B x v v := by
  intro x hx v
  have hunit := min_le_of_laplacian_le_mul_add_of_isMinOn (q := fun y w ↦ B y w w) hK
    (isCompact_sphere 0 1) hc₀ hk hcont hcd hc hsuper hbdry hx
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  -- Rescale `v` to the unit vector `u = ‖v‖⁻¹ v`, for which `B x v v = ‖v‖² B x u u`.
  have hv' : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
  have hu : ‖v‖⁻¹ • v ∈ sphere (0 : V) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hv']
  have hBv : B x v v = ‖v‖ ^ 2 * B x (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) := by
    rw [LinearMap.map_smul₂, LinearMap.map_smul, smul_eq_mul, smul_eq_mul]
    field_simp
  rw [hBv, mul_comm]
  exact mul_le_mul_of_nonneg_left (hunit hu) (sq_nonneg _)

end TauCeti
