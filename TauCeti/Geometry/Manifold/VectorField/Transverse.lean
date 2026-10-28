/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue.Scalar.Level
import TauCeti.Geometry.Manifold.Morse.CriticalPoints

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
sublevel set there: a point where `df` does not vanish is not a local maximum, by Fermat's theorem,
so every point of the level is a limit of points where `f` is larger
(`TauCeti.mem_closure_setOf_lt_of_mvfderiv_pos`). Hence the frontier of the sublevel set `{f ≤ c}`
is exactly the level `f⁻¹(c)` when `df(Z) > 0` along it
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

variable [I.Boundaryless]

/-- **A direction increasing a function leaves its sublevel set.** If a tangent vector `v` at a
point `x` of a boundaryless manifold satisfies `df_x(v) > 0`, then `x` lies in the closure of the
set `{y | f x < f y}`: otherwise `x` would be a local maximum of `f`, hence a critical point by
Fermat's theorem (`IsLocalMax.mem_criticalPoints`), and `df_x` would vanish. -/
theorem mem_closure_setOf_lt_of_mvfderiv_pos {f : M → ℝ} {x : M} {v : TangentSpace I x}
    (hpos : 0 < mvfderiv I f x v) : x ∈ closure {y | f x < f y} := by
  by_contra h
  rw [mem_closure_iff_frequently, not_frequently] at h
  have hmax : IsLocalMax f x := h.mono fun y hy ↦ not_lt.1 hy
  simp [mem_criticalPoints.1 (hmax.mem_criticalPoints (I := I))] at hpos

/-- **The frontier of a sublevel set crossed outwards by a vector field.** Let `f` be continuous,
and let `Z` be a vector field with `df(Z) > 0` along the level `f⁻¹(c)`. Then the frontier of the
sublevel set `{f ≤ c}` is exactly the level `f⁻¹(c)`. -/
theorem frontier_setOf_le_eq_of_mvfderiv_pos {Z : (x : M) → TangentSpace I x} {f : M → ℝ}
    {c : ℝ} (hfc : Continuous f) (hpos : ∀ x, f x = c → 0 < mvfderiv I f x (Z x)) :
    frontier {x | f x ≤ c} = {x | f x = c} := by
  refine (frontier_le_subset_eq hfc continuous_const).antisymm fun x (hx : f x = c) ↦ ?_
  rw [frontier_eq_closure_inter_closure]
  exact ⟨subset_closure hx.le, closure_mono (fun y hy ↦ by simpa [← hx] using hy)
    (mem_closure_setOf_lt_of_mvfderiv_pos (hpos x hx))⟩

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
