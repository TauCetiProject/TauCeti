/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Basic
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# From continuously differentiable boundary graphs to Lipschitz charts

A boundary described in rigid coordinates by a `C¹` graph is locally Lipschitz. More precisely,
every constant strictly larger than the norm of the derivative at the chart centre is a
Lipschitz constant after shrinking the tangential radius. The normal radius and rigid
coordinates need not change. The locally defined graph is extended to the whole tangential
space, as required by `Set.IsLipschitzChartWith`, without changing its Lipschitz constant.

The domain comparison accepts local graph descriptions directly, rather than introducing
another boundary-regularity predicate. In coordinates tangent to a `C¹` boundary, the graph
has derivative zero at the centre. Such descriptions give `Set.IsLipschitzDomainWith` with
any prescribed positive Lipschitz constant. The chart radii may depend on the boundary point;
neither boundedness of the domain nor compactness of its boundary is needed for this comparison.

The analytic inputs are Mathlib's
`ContDiffAt.exists_lipschitzOnWith_of_nnnorm_lt` and `LipschitzOnWith.extend_real`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.5.
* W. McLean, *Strongly Elliptic Systems and Boundary Integral Equations*, §3.1.
-/

public section

noncomputable section

namespace TauCeti

open Metric Set Topology
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L : ℝ≥0}

section Chart

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {Omega : Set F}
  {e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {φ : E → ℝ} {a b : ℝ}

/-- A `C¹` boundary graph becomes a Lipschitz chart on a smaller tangential ball. Any constant
strictly exceeding the derivative norm at the centre is allowed. The extended graph agrees
with the original one throughout the smaller ball, and the normal radius stays unchanged. -/
theorem exists_isLipschitzChartWith_of_contDiffAt (ha : 0 < a) (hb : 0 < b)
    (hφ0 : φ 0 = 0) (hφ : ContDiffAt ℝ 1 φ 0) (hL : ‖fderiv ℝ φ 0‖₊ < L)
    (hgraph : ∀ z ∈ normalCylinder a b, (e.symm z ∈ Omega ↔ φ z.snd < z.fst)) :
    ∃ (ψ : E → ℝ) (b' : ℝ), 0 < b' ∧ b' ≤ b ∧ EqOn φ ψ (ball 0 b') ∧
      Omega.IsLipschitzChartWith L e ψ a b' := by
  obtain ⟨t, ht, hφt⟩ := hφ.exists_lipschitzOnWith_of_nnnorm_lt L hL
  obtain ⟨r, hr, hrt⟩ := Metric.mem_nhds_iff.mp ht
  let b' := min b r
  have hb' : 0 < b' := lt_min hb hr
  have hφb' : LipschitzOnWith L φ (ball 0 b') :=
    hφt.mono ((ball_subset_ball (min_le_right b r)).trans hrt)
  obtain ⟨ψ, heq, hchart⟩ := exists_isLipschitzChartWith_of_lipschitzOnWith ha hb' hφ0 hφb'
    (fun z hz ↦ hgraph z (normalCylinder_mono le_rfl (min_le_left b r) hz))
  exact ⟨ψ, b', hb', min_le_left b r, heq, hchart⟩

end Chart

variable {Omega : Set (WithLp 2 (ℝ × E))}

/-- An open set with `C¹` local boundary graphs is a Lipschitz domain whenever the derivative
norm at every chart centre is strictly below the same constant `L`.

The graph functions need only be `C¹` at the centres, and need not be globally Lipschitz.
Both the coordinates and the positive radii are allowed to depend on the boundary point. -/
theorem isLipschitzDomainWith_of_contDiffAt (hOmega : IsOpen Omega)
    (h : ∀ x ∈ frontier Omega,
      ∃ (e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (φ : E → ℝ) (a b : ℝ),
        e x = 0 ∧ 0 < a ∧ 0 < b ∧ φ 0 = 0 ∧ ContDiffAt ℝ 1 φ 0 ∧
          ‖fderiv ℝ φ 0‖₊ < L ∧
          ∀ z ∈ normalCylinder a b, (e.symm z ∈ Omega ↔ φ z.snd < z.fst)) :
    Omega.IsLipschitzDomainWith L := by
  refine (isLipschitzDomainWith_iff ..).mpr ⟨hOmega, fun x hx ↦ ?_⟩
  obtain ⟨e, φ, a, b, hex, ha, hb, hφ0, hφ, hL, hgraph⟩ := h x hx
  obtain ⟨ψ, b', _, _, _, hchart⟩ :=
    exists_isLipschitzChartWith_of_contDiffAt ha hb hφ0 hφ hL hgraph
  exact (isLipschitzDomainAtWith_iff ..).mpr ⟨e, ψ, a, b', hex, hchart⟩

/-- In rigid coordinates tangent to a `C¹` boundary the local graph has derivative zero at
the centre. Such boundary descriptions make the domain Lipschitz with any positive constant,
by choosing the chart radii sufficiently small at each point. -/
theorem isLipschitzDomainWith_of_contDiffAt_fderiv_eq_zero (hOmega : IsOpen Omega)
    (hL : 0 < L)
    (h : ∀ x ∈ frontier Omega,
      ∃ (e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (φ : E → ℝ) (a b : ℝ),
        e x = 0 ∧ 0 < a ∧ 0 < b ∧ φ 0 = 0 ∧ ContDiffAt ℝ 1 φ 0 ∧
          fderiv ℝ φ 0 = 0 ∧
          ∀ z ∈ normalCylinder a b, (e.symm z ∈ Omega ↔ φ z.snd < z.fst)) :
    Omega.IsLipschitzDomainWith L := by
  apply isLipschitzDomainWith_of_contDiffAt hOmega
  intro x hx
  obtain ⟨e, φ, a, b, hex, ha, hb, hφ0, hφ, hdφ, hgraph⟩ := h x hx
  exact ⟨e, φ, a, b, hex, ha, hb, hφ0, hφ, by simpa only [hdφ, nnnorm_zero] using hL,
    hgraph⟩

end TauCeti
