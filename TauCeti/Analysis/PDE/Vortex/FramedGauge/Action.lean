/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Regularity

/-!
# The smooth Sobolev gauges acting on the affine field space

The framed degree-`m` plane vortex fields form the affine space
`A_m^n = x_m + H^n(ℂ; iT*ℂ ⊕ ℂ)` (`TauCeti.Vortex.framedFieldSpace`), and its gauge group is the
Sobolev framed gauge group `G_(n+1) = {1 + h : h ∈ H^(n+1)(ℂ; ℂ), |1 + h| = 1}`
(`TauCeti.Vortex.sobolevGaugeGroup`), acting by `(a, α) ↦ (a - u⁻¹ du, u α)`
(`TauCeti.Vortex.gaugeTransform`). For `n ≥ 2` this action preserves `A_m^n`
(`TauCeti.Vortex.gaugeTransform_mem_framedFieldSpace`), and a `C²` gauge maps one field of `A_m^n`
into `A_m^n` exactly when it lies in `G_(n+1)`
(`TauCeti.Vortex.gaugeTransform_mem_framedFieldSpace_iff`).

This file restricts the action to the smooth elements of `G_(n+1)`, a subgroup of the smooth
framed gauge group (`TauCeti.Vortex.framedFieldSubMulAction`), and shows that two fields of
`A_m^n` lie in the same orbit of this action exactly when they lie in the same orbit of the whole
smooth framed gauge group (`TauCeti.Vortex.mem_orbit_framedFieldSubMulAction_iff`).

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Module TemperedDistribution
open scoped ContDiff

/-- **The action of the smooth Sobolev gauges on the framed field space.** For an integer
`n ≥ 2`, the smooth elements of `G_(n+1)`, a subgroup of the smooth framed gauge group, act on
the affine field space `A_m^n` by `(a, α) ↦ (a - u⁻¹ du, u α)`. -/
def framedFieldSubMulAction (f : ContDiffBump (0 : ℝ)) (m : ℕ) {n : ℕ} (hn : 1 < n) :
    SubMulAction
      ((sobolevGaugeGroup (s := n + 1) (by norm_cast; omega)).subgroupOf framedGaugeGroup)
      (ℂ → EuclideanSpace ℝ (Fin 4)) where
  carrier := framedFieldSpace f m n
  smul_mem' u x hx := by
    rw [Subgroup.smul_def, framedGaugeGroup_smul]
    exact gaugeTransform_mem_framedFieldSpace hn (Subgroup.mem_subgroupOf.1 u.2) hx

/-- The fields acted on by `framedFieldSubMulAction f m hn` are those of `A_m^n`. -/
@[simp]
theorem mem_framedFieldSubMulAction {f : ContDiffBump (0 : ℝ)} {m n : ℕ} {hn : 1 < n}
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} :
    x ∈ framedFieldSubMulAction f m hn ↔ x ∈ framedFieldSpace f m n :=
  Iff.rfl

/-- **Orbits in the framed field space.** For an integer `n ≥ 2`, two fields of `A_m^n` lie in the
same orbit of the smooth elements of `G_(n+1)` exactly when they lie in the same orbit of the
whole smooth framed gauge group. So the orbit space of `A_m^n` under the smooth Sobolev gauges
embeds in the space of smooth framed gauge orbits of fields. -/
theorem mem_orbit_framedFieldSubMulAction_iff {f : ContDiffBump (0 : ℝ)} {m n : ℕ}
    {hn : 1 < n} {x y : framedFieldSubMulAction f m hn} :
    y ∈ MulAction.orbit
        ((sobolevGaugeGroup (s := n + 1) (by norm_cast; omega)).subgroupOf framedGaugeGroup) x ↔
      (y : ℂ → EuclideanSpace ℝ (Fin 4)) ∈ MulAction.orbit framedGaugeGroup
        (x : ℂ → EuclideanSpace ℝ (Fin 4)) := by
  simp only [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u, by rw [SubMulAction.val_smul, Subgroup.smul_def]⟩
  · rintro ⟨u, hu⟩
    have hsmooth := ((mem_framedGaugeGroup _).1 u.2).1
    have hy : gaugeTransform u x ∈ framedFieldSpace f m n := by
      rw [← framedGaugeGroup_smul, hu]
      exact y.2
    refine ⟨⟨u, Subgroup.mem_subgroupOf.2 (mem_sobolevGaugeGroup_of_mem_framedFieldSpace hn x.2
      (hsmooth.of_le (by simp)) hy)⟩, Subtype.ext ?_⟩
    rw [SubMulAction.val_smul, Subgroup.smul_def, hu]

end TauCeti.Vortex
