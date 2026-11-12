/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
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
minimizing `B_x(w, w)` over the unit sphere with `B_x(v, v) < m` the barrier inequality

`Δ (B_· (v, v)) x ≤ c x · B_x(v, v) + k`,  `c ≥ c₀ > 0`,  `k ≥ 0`,

holds, then `B_x(v, v) ≥ min m (-k / c₀) ‖v‖²` throughout `K`
(`TauCeti.AlmostComplexStructure.min_mul_norm_sq_le_hermitianForm_apply_self_of_laplacian_le`).
The barrier inequality is only required at minimizing unit vectors, that is at eigenvectors for the
least eigenvalue of `B_x`; no regularity of that eigenvalue across eigenvalue crossings is needed.
The regularity hypotheses are on `F` itself: continuity on `K` and `C²` regularity on its interior.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
* R. S. Hamilton, *Four-manifolds with positive curvature operator*, J. Differential Geom. 24
  (1986), 153–179, §4.
-/

public section

open InnerProductSpace Laplacian Metric

namespace TauCeti.AlmostComplexStructure

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The minimum principle for the Hermitian part of a field of two-forms.** Let `F` be continuous
on a compact set `K` and `C²` on its interior, with Hermitian part `B_x = J.hermitianForm (F x)`.
Suppose that `B_x(v, v) ≥ m` for `x ∈ frontier K` and unit `v`, and that at each interior point `x`
and each unit `v` minimizing `B_x(w, w)` over the unit sphere with `B_x(v, v) < m`, the barrier
inequality `Δ (B_· (v, v)) x ≤ c x · B_x(v, v) + k` holds, with `c ≥ c₀ > 0` and `k ≥ 0`. Then
`B_x(v, v) ≥ min m (-k / c₀) ‖v‖²` for every `x ∈ K` and every `v`. -/
theorem min_mul_norm_sq_le_hermitianForm_apply_self_of_laplacian_le (J : AlmostComplexStructure V)
    {K : Set E} (hK : IsCompact K) {F : E → ⋀[ℝ]^2 V} {c : E → ℝ} {m k c₀ : ℝ} (hc₀ : 0 < c₀)
    (hk : 0 ≤ k) (hFc : ContinuousOn F K) (hFd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 F x)
    (hc : ∀ ⦃x⦄, x ∈ interior K → c₀ ≤ c x)
    (hsuper : ∀ ⦃x⦄, x ∈ interior K → ∀ ⦃v⦄, v ∈ sphere (0 : V) 1 →
      IsMinOn (fun w ↦ J.hermitianForm (F x) w w) (sphere 0 1) v →
      J.hermitianForm (F x) v v < m →
      Δ (fun y ↦ J.hermitianForm (F y) v v) x ≤ c x * J.hermitianForm (F x) v v + k)
    (hbdry : ∀ ⦃x⦄, x ∈ frontier K → ∀ ⦃v⦄, v ∈ sphere (0 : V) 1 →
      m ≤ J.hermitianForm (F x) v v) :
    ∀ ⦃x⦄, x ∈ K → ∀ v, min m (-(k / c₀)) * ‖v‖ ^ 2 ≤ J.hermitianForm (F x) v v := by
  refine min_mul_norm_sq_le_of_laplacian_le_mul_add_of_isMinOn (B := fun x ↦ J.hermitianForm (F x))
    hK hc₀ hk ?_ (fun x hx v _ ↦ ?_) hc hsuper hbdry
  · exact J.continuous_hermitianForm_apply.comp_continuousOn
      ((hFc.comp continuousOn_fst Set.mapsTo_fst_prod).prodMk
        (continuousOn_snd.prodMk continuousOn_snd))
  · simp_rw [hermitianForm_apply_self]
    exact (hFd hx).inner ℝ contDiffAt_const

end TauCeti.AlmostComplexStructure
