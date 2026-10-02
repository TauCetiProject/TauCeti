/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SymmetricPower.BasepointIntersection.Basic
import TauCeti.Geometry.Manifold.SymmetricPower.BasepointIntersection.Compact
import TauCeti.Topology.Sym.Cons

/-!
# The identity principle for the basepoint divisor along a connected curve

A curve in a symmetric power with locally analytic symmetric-chart coordinates meets the basepoint
divisor, near each intersection, where one analytic scalar equation vanishes. Along a connected
parameter set this gives a dichotomy: either the whole curve lies in the divisor, or the curve is
not locally contained in the divisor at any of its intersections, which are then isolated. One
parameter outside the divisor therefore rules out local containment everywhere, and a compact
parameter set then carries only finitely many intersections. The curve may cross any number of
symmetric charts.

For a holomorphic disk in `Sym^g(Σ)` with boundary on the tori `T_α`, `T_β` and a basepoint `z`
off the attaching curves, the boundary condition supplies, by continuity, the parameter outside
the divisor. This is the
local noncontainment input to the basepoint multiplicity `n_z` of such a disk, the sum of its
chart-independent local intersection orders `TauCeti.basepointIntersectionOrder`; forming that sum
is a separate step.

The local analytic equation is `TauCeti.basepointDivisor_intersection_order`, and the compact
finiteness statement that these results feed is
`TauCeti.finite_basepointDivisor_intersections_of_not_eventually_mem`. The geometric interpretation
follows Ozsváth--Szabó, *Holomorphic disks and topological invariants for closed three-manifolds*,
Section 2.

## Main declarations

* `TauCeti.mapsTo_basepointDivisor_of_isPreconnected_of_eventually_mem`: a curve locally
  contained in the basepoint divisor near one parameter of a preconnected set lies in the divisor
  on all of it.
* `TauCeti.eventually_notMem_basepointDivisor_of_isPreconnected`: if the curve leaves the
  divisor somewhere on a preconnected set, each intersection in that set is isolated.
* `TauCeti.finite_basepointDivisor_intersections_of_isPreconnected`: such a curve meets the divisor
  at only finitely many parameters of each compact subset.
-/

public section

open Filter Set
open scoped Topology

namespace TauCeti

variable {α : Type*} [TopologicalSpace α] [T2Space α] [ChartedSpace ℂ α] {n : ℕ}
variable {f : ℂ → Sym α n} {U K : Set ℂ}

/-- **Identity principle for the basepoint divisor.** Let `f` be continuous on a preconnected
parameter set `U`, with analytic symmetric-chart coordinates at each parameter of `U` sent into the
basepoint divisor of `z`. If `f` lies in the divisor on a neighbourhood of one parameter of `U`,
then it lies in the divisor at every parameter of `U`. -/
theorem mapsTo_basepointDivisor_of_isPreconnected_of_eventually_mem (z : α)
    (hU : IsPreconnected U) (hf : ∀ w ∈ U, ContinuousAt f w)
    (ha : ∀ w ∈ U, f w ∈ Sym.basepointDivisor z →
      AnalyticAt ℂ (fun t => symChartAt (K := ℂ) (f w) (f t)) w)
    {w : ℂ} (hw : w ∈ U) (hev : ∀ᶠ t in 𝓝 w, f t ∈ Sym.basepointDivisor z) :
    MapsTo f U (Sym.basepointDivisor z) := by
  -- the parameters near which `f` is contained in the divisor form an open set `S`; it suffices to
  -- show that `S` is relatively closed in `U`, since `U` is preconnected and meets `S` at `w`
  set S : Set ℂ := {t | ∀ᶠ s in 𝓝 t, f s ∈ Sym.basepointDivisor z} with hS
  have hSD : S ⊆ f ⁻¹' Sym.basepointDivisor z := fun s hs => hs.self_of_nhds
  suffices hsub : U ⊆ S from fun t ht => hSD (hsub ht)
  refine hU.subset_of_closure_inter_subset isOpen_setOfPred_eventually_nhds ⟨w, hw, hev⟩ ?_
  rintro t ⟨htS, htU⟩
  -- a closure point `t ∈ U` of `S` is an intersection, by continuity and closedness of the divisor
  have htD : f t ∈ Sym.basepointDivisor z :=
    ((Sym.isClosed_basepointDivisor z).closure_subset_iff.mpr (image_subset_iff.mpr hSD))
      (mem_closure_image (hf t htU) htS)
  -- the local equation at `t` has zeros accumulating at `t`, so its order there is infinite
  obtain ⟨_, _, g, _, _, _, _, _, htop, hisolated⟩ :=
    basepointDivisor_intersection_order z f t (hf t htU) (ha t htU htD) htD
  by_contra htS'
  have hfreq : ∃ᶠ s in 𝓝[≠] t, s ∈ S :=
    frequently_nhdsWithin_iff.mpr <| (mem_closure_iff_frequently.mp htS).mono fun s hs =>
      ⟨hs, fun hst => htS' (mem_singleton_iff.mp hst ▸ hs)⟩
  obtain ⟨s, hsS, hsD⟩ :=
    (hfreq.and_eventually (hisolated fun htop' => htS' (htop.mp htop'))).exists
  exact hsD (hSD hsS)

/-- If a curve with analytic symmetric-chart coordinates leaves the basepoint divisor at some
parameter of a preconnected set `U`, then each of its intersections with the divisor in `U` is
isolated: the curve avoids the divisor at all sufficiently close other parameters. -/
theorem eventually_notMem_basepointDivisor_of_isPreconnected (z : α)
    (hU : IsPreconnected U)
    (hf : ∀ w ∈ U, ContinuousAt f w)
    (ha : ∀ w ∈ U, f w ∈ Sym.basepointDivisor z →
      AnalyticAt ℂ (fun t => symChartAt (K := ℂ) (f w) (f t)) w)
    (houtside : ∃ t ∈ U, f t ∉ Sym.basepointDivisor z)
    {w : ℂ} (hw : w ∈ U) (hwD : f w ∈ Sym.basepointDivisor z) :
    ∀ᶠ t in 𝓝[≠] w, f t ∉ Sym.basepointDivisor z := by
  obtain ⟨_, _, g, _, _, _, _, _, htop, hisolated⟩ :=
    basepointDivisor_intersection_order z f w (hf w hw) (ha w hw hwD) hwD
  refine hisolated fun htop' => ?_
  obtain ⟨t, htU, htD⟩ := houtside
  exact htD (mapsTo_basepointDivisor_of_isPreconnected_of_eventually_mem z hU hf ha hw
    (htop.mp htop') htU)

/-- A curve with analytic symmetric-chart coordinates on a preconnected parameter set, leaving the
basepoint divisor at some parameter of that set, meets the divisor at only finitely many parameters
of each compact subset. No single chart is required to contain the image of the compact subset. -/
theorem finite_basepointDivisor_intersections_of_isPreconnected (z : α) (hU : IsPreconnected U)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hf : ∀ w ∈ U, ContinuousAt f w)
    (ha : ∀ w ∈ U, f w ∈ Sym.basepointDivisor z →
      AnalyticAt ℂ (fun t => symChartAt (K := ℂ) (f w) (f t)) w)
    (houtside : ∃ t ∈ U, f t ∉ Sym.basepointDivisor z) :
    (K ∩ f ⁻¹' Sym.basepointDivisor z).Finite := by
  refine finite_basepointDivisor_intersections_of_not_eventually_mem z hK
    (fun w hw => hf w (hKU hw)) (fun w hw => ha w (hKU hw)) fun w hw _ hev => ?_
  obtain ⟨t, htU, htD⟩ := houtside
  exact htD (mapsTo_basepointDivisor_of_isPreconnected_of_eventually_mem z hU hf ha (hKU hw) hev
    htU)

end TauCeti

end
