/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Hermitian
public import TauCeti.Analysis.InnerProductSpace.Laplacian.LowerEnvelope

/-!
# The minimum principle for the Hermitian part of a field of two-forms

Let `V` be a finite-dimensional real inner product space with an almost complex structure `J`, and
let `F : E → ⋀² V` be a field of two-vectors on a finite-dimensional real inner product space `E`,
such as the curvature `i F_a` of a connection read in a flat chart. Its Hermitian part
`B_x(v, w) = (F x (v, J w) + F x (w, J v)) / 2` (`TauCeti.AlmostComplexStructure.hermitianForm`)
is a field of symmetric bilinear forms, and a lower bound `B ≥ -C g` controls the anti-self-dual
part of `F` in dimension four
(`TauCeti.AlmostComplexStructure.norm_smul_sub_hodgeStar_le_of_forall_le_hermitianForm_apply_self`).
For the curvature of large-parameter Seiberg–Witten solutions this gives Taubes's refined bound
`|F_a⁻| ≤ (r / (4 √2)) w₊ + C` (`TauCeti.SeibergWitten.norm_smul_sub_hodgeStar_le`).

This file proves the lower bound on `B` by the minimum principle for its least eigenvalue
(`TauCeti.min_mul_norm_sq_le_of_laplacian_le_mul_add_of_isMinOn`). Over a compact set `K`, if
`B ≥ m` on unit vectors over `frontier K`, and at each interior point `x` and each unit vector `v`
minimizing `B_x(w, w)` over the unit sphere with `B_x(v, v) < min m (-k / c₀)` there are a local
unit section `w` through `v`, `C²` at `x`, and a drift vector `b` satisfying the barrier inequality

`Δ (B_· (w ·, w ·)) x + D (B_· (w ·, w ·)) x b ≤ c x · B_x(v, v) + k`,  `c x ≥ c₀ > 0`,  `k ≥ 0`,

then `B_x(v, v) ≥ min m (-k / c₀) ‖v‖²` throughout `K`
(`TauCeti.AlmostComplexStructure.min_mul_norm_sq_le_hermitianForm_apply_self_of_laplacian_le`).
The barrier inequality is only required at minimizing unit vectors, that is at eigenvectors for the
least eigenvalue of `B_x`; no regularity of that eigenvalue across eigenvalue crossings is needed.
The section `w` may be chosen freely, for instance as a moving frame adapted to a nonconstant `J`.
The regularity hypotheses are on `F` itself: continuity on `K`, and `C²` regularity at the interior
points where the least eigenvalue drops below `min m (-k / c₀)`.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
* R. S. Hamilton, *Four-manifolds with positive curvature operator*, J. Differential Geom. 24
  (1986), 153–179, §4.
-/

public section

open InnerProductSpace Laplacian Metric Filter Topology

namespace TauCeti.AlmostComplexStructure

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The minimum principle for the Hermitian part of a field of two-forms.** Let `F` be continuous
on a compact set `K`, with Hermitian part `B_x = J.hermitianForm (F x)`. Suppose that
`B_x(v, v) ≥ m` for `x ∈ frontier K` and unit `v`, and that at each interior point `x` and each
unit `v` minimizing `B_x(u, u)` over the unit sphere with `B_x(v, v) < min m (-k / c₀)`, `F` is `C²`
at `x`, `c x ≥ c₀`, and there are a local section `w` of the unit sphere through `v`, `C²` at `x`,
and a drift vector `b` with `Δ (B_· (w ·, w ·)) x + D (B_· (w ·, w ·)) x b ≤ c x · B_x(v, v) + k`,
where `c₀ > 0` and `k ≥ 0`. Then `B_x(v, v) ≥ min m (-k / c₀) ‖v‖²` for every `x ∈ K` and every
`v`. -/
theorem min_mul_norm_sq_le_hermitianForm_apply_self_of_laplacian_le (J : AlmostComplexStructure V)
    {K : Set E} (hK : IsCompact K) {F : E → ⋀[ℝ]^2 V} {c : E → ℝ} {m k c₀ : ℝ} (hc₀ : 0 < c₀)
    (hk : 0 ≤ k) (hFc : ContinuousOn F K)
    (hFd : ∀ ⦃x⦄, x ∈ interior K → ∀ ⦃v⦄, v ∈ sphere (0 : V) 1 →
      IsMinOn (fun u ↦ J.hermitianForm (F x) u u) (sphere 0 1) v →
      J.hermitianForm (F x) v v < min m (-(k / c₀)) → ContDiffAt ℝ 2 F x)
    (hc : ∀ ⦃x⦄, x ∈ interior K → ∀ ⦃v⦄, v ∈ sphere (0 : V) 1 →
      IsMinOn (fun u ↦ J.hermitianForm (F x) u u) (sphere 0 1) v →
      J.hermitianForm (F x) v v < min m (-(k / c₀)) → c₀ ≤ c x)
    (hsuper : ∀ ⦃x⦄, x ∈ interior K → ∀ ⦃v⦄, v ∈ sphere (0 : V) 1 →
      IsMinOn (fun u ↦ J.hermitianForm (F x) u u) (sphere 0 1) v →
      J.hermitianForm (F x) v v < min m (-(k / c₀)) →
      ∃ w : E → V, w x = v ∧ (∀ᶠ y in 𝓝 x, w y ∈ sphere (0 : V) 1) ∧ ContDiffAt ℝ 2 w x ∧
        ∃ b : E, Δ (fun y ↦ J.hermitianForm (F y) (w y) (w y)) x +
          fderiv ℝ (fun y ↦ J.hermitianForm (F y) (w y) (w y)) x b ≤
            c x * J.hermitianForm (F x) v v + k)
    (hbdry : ∀ ⦃x⦄, x ∈ frontier K → ∀ ⦃v⦄, v ∈ sphere (0 : V) 1 →
      m ≤ J.hermitianForm (F x) v v) :
    ∀ ⦃x⦄, x ∈ K → ∀ v, min m (-(k / c₀)) * ‖v‖ ^ 2 ≤ J.hermitianForm (F x) v v := by
  refine min_mul_norm_sq_le_of_laplacian_le_mul_add_of_isMinOn (B := fun x ↦ J.hermitianForm (F x))
    hK hc₀ hk ?_ hc (fun x hx v hv hmin hlt ↦ ?_) hbdry
  · simpa using ((J.continuousHermitianForm.continuous.comp_continuousOn
      (hFc.comp continuousOn_fst Set.mapsTo_fst_prod)).clm_apply continuousOn_snd).clm_apply
        continuousOn_snd
  · obtain ⟨w, hwx, hw, hwd, b, hle⟩ := hsuper hx hv hmin hlt
    refine ⟨w, hwx, hw, ?_, b, hle⟩
    simpa using ((J.continuousHermitianForm.contDiff.contDiffAt.comp x
      (hFd hx hv hmin hlt)).clm_apply hwd).clm_apply hwd

end TauCeti.AlmostComplexStructure
