/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Laplacian.LocalExtr

/-!
# The minimum principle for lower envelopes and least eigenvalues

Let `q : E → ι → ℝ` be a family of functions on a finite-dimensional real inner product space `E`,
indexed by a compact set `S` of parameters and jointly continuous. Its **lower envelope**
`x ↦ min_{s ∈ S} q x s` is continuous but in general not differentiable, so the maximum principle
cannot be applied to it directly. It can be tested instead: if `(x₀, s₀)` minimizes `q` over
`K × S` with `x₀` in the interior of `K`, and `γ` is a local section of `S` through `s₀`, then `x₀`
is an interior local minimum of `y ↦ q y (γ y)` (`TauCeti.isLocalMin_of_isMinOn_prod`). If this
function is `C²` at `x₀`, its first derivative vanishes and its Laplacian is nonnegative there
(`TauCeti.laplacian_nonneg_of_isMinOn_prod`). The parameter `s₀` is a minimizing parameter at
`x₀`, so a differential inequality need only be checked at minimizing parameters, along any
convenient section through them, for instance a moving frame.

This gives a strict minimum principle for lower envelopes
(`TauCeti.le_of_laplacian_add_fderiv_neg_of_isMinOn`): if `q ≥ m` on `frontier K` and, at each
interior point `x` and each parameter `s` minimizing `q x` with `q x s < m`, some section `γ`
through `s` and some drift vector `b` satisfy `Δ (q · γ) x + D (q · γ) x b < 0`, then `q ≥ m` on
`K × S`. Its quantitative form (`TauCeti.min_le_of_laplacian_le_mul_add_of_isMinOn`) assumes, at
minimizing parameters with `q x s < min m (-k / c₀)`,

`Δ (q · γ) x + D (q · γ) x b ≤ c x · q x s + k`,  `c x ≥ c₀ > 0`,  `k ≥ 0`,

and concludes `q ≥ min m (-k / c₀)` on `K × S`. At a minimizing point the Laplacian is nonnegative
and the derivative vanishes, so a negative minimum `μ` satisfies `0 ≤ c₀ μ + k`.

The main application is to a field of bilinear forms `B : E → BilinForm ℝ V` on a proper real
normed space `V`. The quadratic form `(x, v) ↦ B x v v` restricted to the unit sphere of `V` is a
family as above, and the conclusion is the lower bound `B x v v ≥ min m (-k / c₀) ‖v‖²` for every
`v` (`TauCeti.min_mul_norm_sq_le_of_laplacian_le_mul_add_of_isMinOn`). When `V` is an inner
product space and `B x` is symmetric, the lower envelope is the **least eigenvalue** of `B x`, a
minimizing parameter is a unit eigenvector for it, and the conclusion bounds the least eigenvalue
from below. Testing with a minimizing eigenvector avoids any regularization of the least
eigenvalue across eigenvalue crossings. This is the elliptic form of Hamilton's maximum principle
for tensors, the mechanism by which Taubes bounds the Hermitian part of the curvature of
large-parameter Seiberg–Witten solutions from below.

## Main results

* `TauCeti.isLocalMin_of_isMinOn_prod`, `TauCeti.laplacian_nonneg_of_isMinOn_prod`: an interior
  minimizer `(x₀, s₀)` of `q` over `K × S` is a local minimum of `q · γ` for every local section
  `γ` of `S` through `s₀`, so the Laplacian of `q · γ` is nonnegative at `x₀`.
* `TauCeti.le_of_laplacian_add_fderiv_neg_of_isMinOn`: the strict minimum principle for lower
  envelopes.
* `TauCeti.min_le_of_laplacian_le_mul_add_of_isMinOn`: the quantitative minimum principle for
  lower envelopes.
* `TauCeti.min_mul_norm_sq_le_of_laplacian_le_mul_add_of_isMinOn`: the minimum principle for the
  quadratic form of a field of bilinear forms, a lower bound on the least eigenvalue when the
  forms are symmetric.

## References

* R. S. Hamilton, *Four-manifolds with positive curvature operator*, J. Differential Geom. 24
  (1986), 153–179, §4.
* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian Set Metric Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [TopologicalSpace ι]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace ι] in
/-- **The minimum test for a lower envelope.** If `(x, s)` minimizes `q` over `K × S` and `x` lies
in the interior of `K`, then `x` is a local minimum of `y ↦ q y (γ y)` for every local section `γ`
of `S` through `s`. -/
theorem isLocalMin_of_isMinOn_prod {K : Set E} {S : Set ι} {q : E → ι → ℝ} {x : E} {s : ι}
    {γ : E → ι} (hx : x ∈ interior K) (hmin : IsMinOn (fun p : E × ι ↦ q p.1 p.2) (K ×ˢ S) (x, s))
    (hγx : γ x = s) (hγ : ∀ᶠ y in 𝓝 x, γ y ∈ S) :
    IsLocalMin (fun y ↦ q y (γ y)) x := by
  filter_upwards [mem_interior_iff_mem_nhds.1 hx, hγ] with y hy hγy
  rw [hγx]
  exact isMinOn_iff.1 hmin (y, γ y) ⟨hy, hγy⟩

omit [TopologicalSpace ι] in
/-- **The Laplacian test for a lower envelope.** If `(x, s)` minimizes `q` over `K × S` and `x`
lies in the interior of `K`, then for every local section `γ` of `S` through `s` such that
`y ↦ q y (γ y)` is `C²` at `x`, the Laplacian of `y ↦ q y (γ y)` is nonnegative at `x`. -/
theorem laplacian_nonneg_of_isMinOn_prod {K : Set E} {S : Set ι} {q : E → ι → ℝ} {x : E} {s : ι}
    {γ : E → ι} (hx : x ∈ interior K) (hmin : IsMinOn (fun p : E × ι ↦ q p.1 p.2) (K ×ˢ S) (x, s))
    (hγx : γ x = s) (hγ : ∀ᶠ y in 𝓝 x, γ y ∈ S) (hcd : ContDiffAt ℝ 2 (fun y ↦ q y (γ y)) x) :
    0 ≤ Δ (fun y ↦ q y (γ y)) x :=
  laplacian_nonneg_of_isLocalMin hcd (isLocalMin_of_isMinOn_prod hx hmin hγx hγ)

/-- **The strict minimum principle for lower envelopes.** Let `K` and `S` be compact and let `q` be
jointly continuous on `K × S`. Suppose that `q ≥ m` on `frontier K × S`, and that at each interior
point `x` and each parameter `s` minimizing `q x` over `S` with `q x s < m`, there are a local
section `γ` of `S` through `s`, with `y ↦ q y (γ y)` `C²` at `x`, and a drift vector `b` such that
`Δ (q · γ) x + D (q · γ) x b < 0`. Then `q ≥ m` on `K × S`. -/
theorem le_of_laplacian_add_fderiv_neg_of_isMinOn {K : Set E} (hK : IsCompact K) {S : Set ι}
    (hS : IsCompact S) {q : E → ι → ℝ} {m : ℝ}
    (hcont : ContinuousOn (fun p : E × ι ↦ q p.1 p.2) (K ×ˢ S))
    (hsub : ∀ ⦃x⦄, x ∈ interior K → ∀ ⦃s⦄, s ∈ S → IsMinOn (q x) S s → q x s < m →
      ∃ γ : E → ι, γ x = s ∧ (∀ᶠ y in 𝓝 x, γ y ∈ S) ∧ ContDiffAt ℝ 2 (fun y ↦ q y (γ y)) x ∧
        ∃ b : E, Δ (fun y ↦ q y (γ y)) x + fderiv ℝ (fun y ↦ q y (γ y)) x b < 0)
    (hbdry : ∀ ⦃x⦄, x ∈ frontier K → ∀ ⦃s⦄, s ∈ S → m ≤ q x s) :
    ∀ ⦃x⦄, x ∈ K → ∀ ⦃s⦄, s ∈ S → m ≤ q x s := by
  intro x hx s hs
  -- Compare with the value of `q` at a minimizer `(x₀, s₀)` over `K × S`.
  obtain ⟨⟨x₀, s₀⟩, ⟨hx₀, hs₀⟩, hmin⟩ := (hK.prod hS).exists_isMinOn ⟨(x, s), hx, hs⟩ hcont
  refine le_trans ?_ (isMinOn_iff.1 hmin (x, s) ⟨hx, hs⟩)
  dsimp only
  by_cases hfr : x₀ ∈ frontier K
  · exact hbdry hfr hs₀
  have hint : x₀ ∈ interior K := by
    by_contra h
    exact hfr ⟨subset_closure hx₀, h⟩
  by_contra! hm
  obtain ⟨γ, hγx, hγ, hcd, b, hlt⟩ :=
    hsub hint hs₀ (fun t ht ↦ isMinOn_iff.1 hmin (x₀, t) ⟨hx₀, ht⟩) hm
  -- At the interior minimizer the derivative vanishes and the Laplacian is nonnegative.
  have hloc := isLocalMin_of_isMinOn_prod hint hmin hγx hγ
  have hlap := laplacian_nonneg_of_isLocalMin hcd hloc
  rw [hloc.fderiv_eq_zero, zero_apply, add_zero] at hlt
  exact hlt.not_ge hlap

/-- **The minimum principle for lower envelopes.** Let `K` and `S` be compact and let `q` be
jointly continuous on `K × S`. Suppose that `q ≥ m` on `frontier K × S`, and that at each interior
point `x` and each parameter `s` minimizing `q x` over `S` with `q x s < min m (-k / c₀)`, we have
`c x ≥ c₀` and there are a local section `γ` of `S` through `s`, with `y ↦ q y (γ y)` `C²` at `x`,
and a drift vector `b` such that `Δ (q · γ) x + D (q · γ) x b ≤ c x · q x s + k`, where `c₀ > 0`
and `k ≥ 0`. Then `q ≥ min m (-k / c₀)` on `K × S`. -/
theorem min_le_of_laplacian_le_mul_add_of_isMinOn {K : Set E} (hK : IsCompact K) {S : Set ι}
    (hS : IsCompact S) {q : E → ι → ℝ} {c : E → ℝ} {m k c₀ : ℝ} (hc₀ : 0 < c₀) (hk : 0 ≤ k)
    (hcont : ContinuousOn (fun p : E × ι ↦ q p.1 p.2) (K ×ˢ S))
    (hc : ∀ ⦃x⦄, x ∈ interior K → ∀ ⦃s⦄, s ∈ S → IsMinOn (q x) S s →
      q x s < min m (-(k / c₀)) → c₀ ≤ c x)
    (hsuper : ∀ ⦃x⦄, x ∈ interior K → ∀ ⦃s⦄, s ∈ S → IsMinOn (q x) S s →
      q x s < min m (-(k / c₀)) →
      ∃ γ : E → ι, γ x = s ∧ (∀ᶠ y in 𝓝 x, γ y ∈ S) ∧ ContDiffAt ℝ 2 (fun y ↦ q y (γ y)) x ∧
        ∃ b : E, Δ (fun y ↦ q y (γ y)) x + fderiv ℝ (fun y ↦ q y (γ y)) x b ≤ c x * q x s + k)
    (hbdry : ∀ ⦃x⦄, x ∈ frontier K → ∀ ⦃s⦄, s ∈ S → m ≤ q x s) :
    ∀ ⦃x⦄, x ∈ K → ∀ ⦃s⦄, s ∈ S → min m (-(k / c₀)) ≤ q x s := by
  refine le_of_laplacian_add_fderiv_neg_of_isMinOn hK hS hcont (fun x hx s hs hmin hlt ↦ ?_)
    (fun x hx s hs ↦ min_le_of_left_le (hbdry hx hs))
  obtain ⟨γ, hγx, hγ, hcd, b, hle⟩ := hsuper hx hs hmin hlt
  refine ⟨γ, hγx, hγ, hcd, b, hle.trans_lt ?_⟩
  -- Below `-k / c₀ ≤ 0` the barrier satisfies `c x · μ + k ≤ c₀ μ + k < 0`.
  have hμ : q x s < -(k / c₀) := hlt.trans_le (min_le_right _ _)
  have h₁ : c x * q x s ≤ c₀ * q x s :=
    mul_le_mul_of_nonpos_right (hc hx hs hmin hlt)
      (hμ.le.trans (neg_nonpos.2 (div_nonneg hk hc₀.le)))
  rw [lt_neg, div_lt_iff₀ hc₀] at hμ
  linarith

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V]

/-- **The minimum principle for the quadratic form of a field of bilinear forms.** Let `B` be a
field of bilinear forms on `V` over a compact set `K`, with `(x, v) ↦ B x v v` continuous on
`K × sphere 0 1`. Suppose that `B x v v ≥ m` for `x ∈ frontier K` and unit `v`, and that at each
interior point `x` and each unit `v` minimizing `B x u u` over the unit sphere with
`B x v v < min m (-k / c₀)`, we have `c x ≥ c₀` and there are a local section `w` of the unit
sphere through `v`, with `y ↦ B y (w y) (w y)` `C²` at `x`, and a drift vector `b` such that the
differential inequality `Δ (B · (w ·) (w ·)) x + D (B · (w ·) (w ·)) x b ≤ c x · B x v v + k`
holds, where `c₀ > 0` and `k ≥ 0`. Then `B x v v ≥ min m (-k / c₀) ‖v‖²` on `K` for every `v`.
When `V` is an inner product space and each `B x` is symmetric, this bounds the least eigenvalue
of `B x` from below, and the minimizing `v` are its unit eigenvectors. -/
theorem min_mul_norm_sq_le_of_laplacian_le_mul_add_of_isMinOn {K : Set E} (hK : IsCompact K)
    {B : E → LinearMap.BilinForm ℝ V} {c : E → ℝ} {m k c₀ : ℝ} (hc₀ : 0 < c₀) (hk : 0 ≤ k)
    (hcont : ContinuousOn (fun p : E × V ↦ B p.1 p.2 p.2) (K ×ˢ sphere 0 1))
    (hc : ∀ ⦃x⦄, x ∈ interior K → ∀ ⦃v⦄, v ∈ sphere (0 : V) 1 →
      IsMinOn (fun u ↦ B x u u) (sphere 0 1) v → B x v v < min m (-(k / c₀)) → c₀ ≤ c x)
    (hsuper : ∀ ⦃x⦄, x ∈ interior K → ∀ ⦃v⦄, v ∈ sphere (0 : V) 1 →
      IsMinOn (fun u ↦ B x u u) (sphere 0 1) v → B x v v < min m (-(k / c₀)) →
      ∃ w : E → V, w x = v ∧ (∀ᶠ y in 𝓝 x, w y ∈ sphere (0 : V) 1) ∧
        ContDiffAt ℝ 2 (fun y ↦ B y (w y) (w y)) x ∧
        ∃ b : E, Δ (fun y ↦ B y (w y) (w y)) x + fderiv ℝ (fun y ↦ B y (w y) (w y)) x b ≤
          c x * B x v v + k)
    (hbdry : ∀ ⦃x⦄, x ∈ frontier K → ∀ ⦃v⦄, v ∈ sphere (0 : V) 1 → m ≤ B x v v) :
    ∀ ⦃x⦄, x ∈ K → ∀ v, min m (-(k / c₀)) * ‖v‖ ^ 2 ≤ B x v v := by
  intro x hx v
  have hunit := min_le_of_laplacian_le_mul_add_of_isMinOn (q := fun y u ↦ B y u u) hK
    (isCompact_sphere 0 1) hc₀ hk hcont hc hsuper hbdry hx
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
