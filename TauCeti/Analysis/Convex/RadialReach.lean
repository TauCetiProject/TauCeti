/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Intrinsic

/-!
# Radial reach of a convex set

From an intrinsic interior point `c` of a closed bounded convex set `C`, each unit direction
in its affine span meets `C` in a closed segment. The endpoint parameter
`compactConvexRadialReach C c u` is defined geometrically as a supremum. It is positive,
attained, and continuous in `u`, and equals the inverse of the gauge of the translated set
in the affine direction. In particular, it is a finite real number, not an extended length.

The homeomorphism `TauCeti.convexClosedBallHomeomorph` sends `t • u` to
`c + (t * compactConvexRadialReach C c u) • u`. It takes the unit sphere precisely to the
intrinsic frontier, including when the affine span has dimension zero: both boundaries are
then empty. These comparisons specify the geometry of the disk model used to transport the
fixed-point property to compact convex sets. Closedness and boundedness suffice; compactness
and finite dimension are not needed for these radial comparisons.

The proofs use Mathlib's `gauge_pos`, `continuous_gauge` and gauge sublevel/frontier
characterizations, and the gauge-rescaling homeomorphism of Yury Kudryashov.

## References

* R. Schneider, *Convex Bodies: The Brunn–Minkowski Theory*, Section 1.7.
-/

public section

noncomputable section

open Set Metric Bornology Topology
open scoped Pointwise

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (C : Set E) (c : E)

/-- The last nonnegative parameter of the ray from `c` in unit direction `u` that lies in `C`.
For a closed bounded convex set and an intrinsic interior center it is positive and attained. -/
def compactConvexRadialReach
    (u : sphere (0 : (affineSpan ℝ C).direction) 1) : ℝ :=
  sSup {t : ℝ | 0 ≤ t ∧ c + t • (u.1 : E) ∈ C}

/-- The radial reach is the supremum of the admissible nonnegative ray parameters. -/
lemma compactConvexRadialReach_def
    (u : sphere (0 : (affineSpan ℝ C).direction) 1) :
    compactConvexRadialReach C c u = sSup {t : ℝ | 0 ≤ t ∧ c + t • (u.1 : E) ∈ C} := (rfl)

variable {C c} (hconv : Convex ℝ C) (hcl : IsClosed C) (hb : IsBounded C)
  (hc : c ∈ intrinsicInterior ℝ C)

include hconv hcl hb hc

omit hconv hcl in
private lemma gauge_pos_of_mem_sphere
    (u : sphere (0 : (affineSpan ℝ C).direction) 1) :
    0 < gauge {v : (affineSpan ℝ C).direction | c + (v : E) ∈ C} u.1 :=
  (gauge_setOf_add_mem_pos_iff hb hc u.1).2
    (ne_of_mem_sphere u.property one_ne_zero)

private lemma ray_parameters_eq_Icc_inv_gauge
    (u : sphere (0 : (affineSpan ℝ C).direction) 1) :
    {t : ℝ | 0 ≤ t ∧ c + t • (u.1 : E) ∈ C} =
      Icc 0 (gauge {v : (affineSpan ℝ C).direction | c + (v : E) ∈ C} u.1)⁻¹ := by
  have hpos := gauge_pos_of_mem_sphere hb hc u
  ext t
  by_cases ht : 0 ≤ t
  · have hmem := gauge_le_one_iff_mem_closure (convex_setOf_add_mem hconv)
      (setOf_add_mem_mem_nhds_of_mem_intrinsicInterior hc) (x := t • u.1)
    rw [(isClosed_setOf_add_mem hcl).closure_eq, gauge_smul_of_nonneg ht,
      smul_eq_mul] at hmem
    simpa only [mem_ofPred_eq, mem_Icc, ht, true_and, one_div, Submodule.coe_smul] using
      hmem.symm.trans (le_div_iff₀ hpos).symm
  · simp [ht]

/-- The geometric supremum is the inverse gauge of the translated set, computed in the
native direction space of its affine span. -/
theorem compactConvexRadialReach_eq_inv_gauge
    (u : sphere (0 : (affineSpan ℝ C).direction) 1) :
    compactConvexRadialReach C c u =
      (gauge {v : (affineSpan ℝ C).direction | c + (v : E) ∈ C} u.1)⁻¹ := by
  rw [compactConvexRadialReach_def, ray_parameters_eq_Icc_inv_gauge hconv hcl hb hc]
  exact csSup_Icc (inv_nonneg.mpr (gauge_nonneg _))

/-- Every unit direction has strictly positive radial reach. -/
theorem compactConvexRadialReach_pos
    (u : sphere (0 : (affineSpan ℝ C).direction) 1) :
    0 < compactConvexRadialReach C c u := by
  rw [compactConvexRadialReach_eq_inv_gauge hconv hcl hb hc]
  exact inv_pos.mpr (gauge_pos_of_mem_sphere hb hc u)

/-- The nonnegative parameters for which a ray stays in the set form exactly the closed
interval from zero to its radial reach. This also gives a finite bound on all such parameters. -/
theorem setOf_ray_mem_eq_Icc_compactConvexRadialReach
    (u : sphere (0 : (affineSpan ℝ C).direction) 1) :
    {t : ℝ | 0 ≤ t ∧ c + t • (u.1 : E) ∈ C} = Icc 0 (compactConvexRadialReach C c u) := by
  rw [compactConvexRadialReach_eq_inv_gauge hconv hcl hb hc]
  exact ray_parameters_eq_Icc_inv_gauge hconv hcl hb hc u

/-- A nonnegative ray parameter stays in the set exactly when it is at most the radial reach. -/
theorem add_smul_mem_iff_le_compactConvexRadialReach
    (u : sphere (0 : (affineSpan ℝ C).direction) 1) {t : ℝ} (ht : 0 ≤ t) :
    c + t • (u.1 : E) ∈ C ↔ t ≤ compactConvexRadialReach C c u := by
  have h := congrArg (fun s : Set ℝ ↦ t ∈ s)
    (setOf_ray_mem_eq_Icc_compactConvexRadialReach hconv hcl hb hc u)
  simpa only [mem_ofPred_eq, mem_Icc, ht, true_and] using h.to_iff

/-- The last point on a ray belongs to the set. -/
theorem add_compactConvexRadialReach_smul_mem
    (u : sphere (0 : (affineSpan ℝ C).direction) 1) :
    c + compactConvexRadialReach C c u • (u.1 : E) ∈ C := by
  exact (add_smul_mem_iff_le_compactConvexRadialReach hconv hcl hb hc u
    (compactConvexRadialReach_pos hconv hcl hb hc u).le).2 le_rfl

/-- Radial reach varies continuously on the unit sphere of the affine direction, even if
`C` has empty ambient interior. -/
theorem continuous_compactConvexRadialReach :
    Continuous (compactConvexRadialReach C c) := by
  have heq : compactConvexRadialReach C c = fun u ↦
      (gauge {v : (affineSpan ℝ C).direction | c + (v : E) ∈ C} u.1)⁻¹ :=
    funext (compactConvexRadialReach_eq_inv_gauge hconv hcl hb hc)
  rw [heq]
  exact ((continuous_gauge (convex_setOf_add_mem hconv)
    (setOf_add_mem_mem_nhds_of_mem_intrinsicInterior hc)).comp continuous_subtype_val).inv₀
      (fun u ↦ (gauge_pos_of_mem_sphere hb hc u).ne')

/-- The convex-ball homeomorphism has the positive radial-reach formula on every segment
from the center to a unit direction. -/
theorem coe_convexClosedBallHomeomorph_smul
    (u : sphere (0 : (affineSpan ℝ C).direction) 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (convexClosedBallHomeomorph hconv hcl hb hc
      ⟨t • u.1, by simpa [mem_closedBall_zero_iff, norm_smul, abs_of_nonneg ht.1,
        mem_sphere_zero_iff_norm.mp u.property] using ht.2⟩ : E) =
      c + (t * compactConvexRadialReach C c u) • (u.1 : E) := by
  rw [coe_convexClosedBallHomeomorph_apply]
  simp only [Submodule.coe_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1,
    Submodule.norm_coe, mem_sphere_zero_iff_norm.mp u.property, mul_one,
    gauge_smul_of_nonneg ht.1, smul_eq_mul, ← gauge_setOf_add_mem,
    compactConvexRadialReach_eq_inv_gauge hconv hcl hb hc]
  by_cases ht0 : t = 0
  · simp [ht0]
  · simp [div_mul_eq_div_mul_one_div, ht0, smul_smul, mul_comm]

/-- The endpoint realizing the radial reach lies in the intrinsic frontier. -/
theorem add_compactConvexRadialReach_smul_mem_intrinsicFrontier
    (u : sphere (0 : (affineSpan ℝ C).direction) 1) :
    c + compactConvexRadialReach C c u • (u.1 : E) ∈ intrinsicFrontier ℝ C := by
  have h := coe_convexClosedBallHomeomorph_mem_intrinsicFrontier_iff hconv hcl hb hc
    ⟨u.1, by simp⟩
  have hf := coe_convexClosedBallHomeomorph_smul hconv hcl hb hc u
    (t := 1) ⟨zero_le_one, le_rfl⟩
  simp only [one_smul, one_mul] at hf
  rw [hf] at h
  exact h.mpr (mem_sphere_zero_iff_norm.mp u.property)

end TauCeti
