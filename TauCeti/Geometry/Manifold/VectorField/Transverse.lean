/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue.Scalar.Level
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import TauCeti.Geometry.Manifold.MFDeriv.Curve

/-!
# Vector fields transverse to a map

A vector field `Z` on a manifold `M` is **transverse along** a map `ι : S → M`
(`TauCeti.IsTransverseAlong`) when at every point `s` of `S` the vector `Z (ι s)` is not tangent
to `ι`: it does not lie in the range of the differential `dι_s`. When `ι` is an embedded
hypersurface, so that this range has codimension one, this is transversality of `Z` to the
hypersurface in the usual sense: `Z (ι s)` and the tangent space of the hypersurface at `s` span
the tangent space of `M` at `ι s`. A transverse vector field does not vanish along `ι`
(`TauCeti.IsTransverseAlong.ne_zero`).

For a regular level `f⁻¹(c)` of a scalar function, with its preferred atlas
`TauCeti.scalarRegularLevelChartedSpace`, the tangent space at `x` is the kernel of `df_x`
(`TauCeti.range_mfderiv_coe_scalarRegularLevel`). So a vector field is transverse along the
inclusion of the level exactly when `df(Z) ≠ 0` at every point of the level
(`TauCeti.isTransverseAlong_coe_scalarRegularLevel_iff`). This is how transversality to the
hypersurfaces of symplectic geometry (energy levels, boundaries of domains, cosphere bundles) is
checked in practice.

A vector field crossing a level of `f` in the direction of increasing `f`, `df(Z) > 0`, leaves the
sublevel set there: along its integral curves `f` increases, so every point of the level is a limit
of points where `f` is larger (`TauCeti.mem_closure_setOf_lt_of_mvfderiv_pos`). Hence the frontier
of the sublevel set `{f ≤ c}` is exactly the level `f⁻¹(c)` when `df(Z) > 0` along it
(`TauCeti.frontier_setOf_le_eq_of_mvfderiv_pos`). This identifies the boundary of a domain whose
boundary is crossed outwards by a vector field, as for Liouville domains.

## Main definitions

* `TauCeti.IsTransverseAlong`: `Z (ι s)` is outside the range of `dι_s` for every `s`.

## Main results

* `TauCeti.isTransverseAlong_coe_scalarRegularLevel_iff`: transversality along a regular level is
  the nonvanishing of `df(Z)` on the level.
* `TauCeti.frontier_setOf_le_eq_of_mvfderiv_pos`: the frontier of a sublevel set whose level is
  crossed outwards by a vector field is the level.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 5
  (vector fields transverse to a hypersurface).
-/

public section

open Filter Module Set
open scoped Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]

variable (J) in
/-- A vector field `Z` on `M` is **transverse along** a map `ι : S → M` when at every point `s`
the vector `Z (ι s)` is not tangent to `ι`, that is, not in the range of the differential `dι_s`.
For an embedded hypersurface this is transversality of `Z` to the hypersurface. -/
def IsTransverseAlong (Z : (x : M) → TangentSpace I x) (ι : S → M) : Prop :=
  ∀ s, Z (ι s) ∉ (mfderiv J I ι s).range

/-- The defining characterization of a vector field transverse along a map. -/
theorem isTransverseAlong_iff {Z : (x : M) → TangentSpace I x} {ι : S → M} :
    IsTransverseAlong J Z ι ↔ ∀ s, Z (ι s) ∉ (mfderiv J I ι s).range :=
  Iff.rfl

/-- A vector field transverse along `ι` does not vanish at the points of the image of `ι`. -/
theorem IsTransverseAlong.ne_zero {Z : (x : M) → TangentSpace I x} {ι : S → M}
    (h : IsTransverseAlong J Z ι) (s : S) : Z (ι s) ≠ 0 :=
  fun h0 ↦ h s (h0 ▸ Submodule.zero_mem _)

/-! ### Vector fields crossing a level outwards -/

section Crossing

variable [CompleteSpace E] [I.Boundaryless] [IsManifold I 1 M]

/-- **A vector field increasing a function leaves its sublevel set.** If a `C¹` vector field `Z` on
a boundaryless manifold satisfies `df_x(Z x) > 0` at a point `x` where `f` is differentiable, then
`x` lies in the closure of the set `{y | f x < f y}`: the integral curve of `Z` through `x` enters
this set immediately after time `0`. -/
theorem mem_closure_setOf_lt_of_mvfderiv_pos {Z : (x : M) → TangentSpace I x} {f : M → ℝ} {x : M}
    (hZ : ContMDiffAt I I.tangent 1 (T% Z) x) (hf : MDifferentiableAt I 𝓘(ℝ) f x)
    (hpos : 0 < mvfderiv I f x (Z x)) : x ∈ closure {y | f x < f y} := by
  obtain ⟨γ, rfl, hγ⟩ := exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless 0 hZ
  have hγ' := hγ.self_of_nhds
  -- Along the integral curve, `f` has derivative `df_x(Z x) > 0` at time `0`.
  have hd : HasDerivAt (f ∘ γ) (mvfderiv I f (γ 0) (Z (γ 0))) 0 :=
    Manifold.hasDerivAt_comp_curve hf hγ'
  have hlt : ∀ᶠ t in 𝓝[>] (0 : ℝ), f (γ 0) < f (γ t) := by
    filter_upwards [(hd.tendsto_slope.mono_left (nhdsGT_le_nhdsNE 0)).eventually
      (lt_mem_nhds hpos), self_mem_nhdsWithin] with t ht ht0
    exact (slope_pos_iff_of_le (Set.mem_Ioi.1 ht0).le).1 ht
  exact mem_closure_of_tendsto (hγ'.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hlt

/-- **The frontier of a sublevel set crossed outwards by a vector field.** Let `f` be continuous,
and differentiable at the points of the level `f⁻¹(c)`, and let `Z` be a vector field, `C¹` along
the level, with `df(Z) > 0` there. Then the frontier of the sublevel set `{f ≤ c}` is exactly the
level `f⁻¹(c)`. -/
theorem frontier_setOf_le_eq_of_mvfderiv_pos {Z : (x : M) → TangentSpace I x} {f : M → ℝ}
    {c : ℝ} (hfc : Continuous f) (hZ : ∀ x, f x = c → ContMDiffAt I I.tangent 1 (T% Z) x)
    (hf : ∀ x, f x = c → MDifferentiableAt I 𝓘(ℝ) f x)
    (hpos : ∀ x, f x = c → 0 < mvfderiv I f x (Z x)) :
    frontier {x | f x ≤ c} = {x | f x = c} := by
  refine (frontier_le_subset_eq hfc continuous_const).antisymm fun x (hx : f x = c) ↦ ?_
  rw [frontier_eq_closure_inter_closure]
  exact ⟨subset_closure hx.le, closure_mono (fun y hy ↦ by simpa [← hx] using hy)
    (mem_closure_setOf_lt_of_mvfderiv_pos (hZ x hx) (hf x hx) (hpos x hx))⟩

end Crossing

variable {f : M → ℝ} {c : ℝ} [I.Boundaryless] [FiniteDimensional ℝ E] [IsManifold I 1 M]
  (hf : ∀ x, f x = c → ContMDiffAt I 𝓘(ℝ) 1 f x) (hreg : IsRegularValue I 𝓘(ℝ) f c)

/-- **Transversality to a regular level.** A vector field `Z` is transverse along the inclusion of
a regular level `f⁻¹(c)`, with its preferred atlas `TauCeti.scalarRegularLevelChartedSpace`,
exactly when `df(Z) ≠ 0` at every point of the level. -/
theorem isTransverseAlong_coe_scalarRegularLevel_iff {Z : (x : M) → TangentSpace I x} :
    letI := scalarRegularLevelChartedSpace hf hreg
    IsTransverseAlong 𝓘(ℝ, Fin (finrank ℝ E - 1) → ℝ) Z (Subtype.val : {x : M // f x = c} → M) ↔
      ∀ x, f x = c → mfderiv I 𝓘(ℝ) f x (Z x) ≠ 0 := by
  let := scalarRegularLevelChartedSpace hf hreg
  simp only [isTransverseAlong_iff, range_mfderiv_coe_scalarRegularLevel hf hreg,
    LinearMap.mem_ker, ContinuousLinearMap.coe_coe, Subtype.forall]

end TauCeti
