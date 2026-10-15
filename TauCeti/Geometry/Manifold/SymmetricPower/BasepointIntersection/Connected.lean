/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SymmetricPower.BasepointIntersection.Basic
public import TauCeti.Geometry.Manifold.SymmetricPower.BasepointIntersection.Order
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
chart-independent local intersection orders `TauCeti.basepointIntersectionOrder`, which is
`TauCeti.basepointIntersectionNumber`.

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
* `TauCeti.basepointIntersectionOrder_ne_top_of_isPreconnected`: each of its intersection orders
  is finite.
* `TauCeti.finite_basepointDivisor_intersections_of_frontier`: a curve on a bounded connected open
  set, sending the frontier off the divisor, meets the divisor at only finitely many parameters.
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
  set S : Set ℂ := {t | ∀ᶠ s in 𝓝 t, f s ∈ Sym.basepointDivisor z}
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

/-- At a parameter of a preconnected set `U` on which the curve leaves the basepoint divisor
somewhere, a curve continuous on `U` with analytic chart coordinates at its intersections meets
the divisor to finite order. -/
theorem basepointIntersectionOrder_ne_top_of_isPreconnected {z : α} {w : ℂ}
    (hU : IsPreconnected U) (hf : ∀ w ∈ U, ContinuousAt f w)
    (ha : ∀ w ∈ U, f w ∈ Sym.basepointDivisor z →
      AnalyticAt ℂ (fun t => symChartAt (K := ℂ) (f w) (f t)) w)
    (houtside : ∃ t ∈ U, f t ∉ Sym.basepointDivisor z) (hw : w ∈ U) :
    basepointIntersectionOrder z f w ≠ ⊤ := by
  rw [Ne, basepointIntersectionOrder_eq_top_iff (hf w hw)]
  intro hev
  obtain ⟨t, htU, htD⟩ := houtside
  exact htD (mapsTo_basepointDivisor_of_isPreconnected_of_eventually_mem z hU hf ha hw hev htU)

omit [ChartedSpace ℂ α] in
/-- A curve continuous on the closure of a nonempty bounded set `U ⊆ ℂ`, sending its frontier off
the basepoint divisor, leaves the divisor at some parameter of `U`. -/
theorem exists_mem_notMem_basepointDivisor_of_frontier {z : α} (hU₀ : U.Nonempty)
    (hUc : IsCompact (closure U)) (hf : ContinuousOn f (closure U))
    (hfr : ∀ w ∈ frontier U, f w ∉ Sym.basepointDivisor z) :
    ∃ t ∈ U, f t ∉ Sym.basepointDivisor z := by
  -- `U` is not all of the noncompact plane, so its frontier is nonempty
  have hne : U ≠ univ := by
    rintro rfl
    exact noncompact_univ ℂ (closure_univ (X := ℂ) ▸ hUc)
  obtain ⟨w₀, hw₀⟩ := nonempty_frontier_iff.2 ⟨hU₀, hne⟩
  have hcl : w₀ ∈ closure U := frontier_subset_closure hw₀
  -- near the frontier point `w₀`, the curve stays off the closed divisor
  have hev : ∀ᶠ t in 𝓝[U] w₀, f t ∉ Sym.basepointDivisor z :=
    nhdsWithin_mono w₀ subset_closure <|
      (hf w₀ hcl).eventually_mem ((Sym.isClosed_basepointDivisor z).isOpen_compl.mem_nhds
        (hfr w₀ hw₀))
  have := mem_closure_iff_nhdsWithin_neBot.1 hcl
  obtain ⟨t, htD, htU⟩ := (hev.and self_mem_nhdsWithin).exists
  exact ⟨t, htU, htD⟩

/-- **Finitely many intersections on a bounded domain.** Let `U ⊆ ℂ` be a bounded connected open
set and `f` continuous on its closure, with analytic chart coordinates at each parameter of `U`
sent into the basepoint divisor. If `f` sends the frontier of `U` off the divisor, then `f` meets
the divisor at only finitely many parameters of `U`. -/
theorem finite_basepointDivisor_intersections_of_frontier (z : α) (hUo : IsOpen U)
    (hU : IsPreconnected U) (hUc : IsCompact (closure U)) (hf : ContinuousOn f (closure U))
    (ha : ∀ w ∈ U, f w ∈ Sym.basepointDivisor z →
      AnalyticAt ℂ (fun t => symChartAt (K := ℂ) (f w) (f t)) w)
    (hfr : ∀ w ∈ frontier U, f w ∉ Sym.basepointDivisor z) :
    (U ∩ f ⁻¹' Sym.basepointDivisor z).Finite := by
  rcases U.eq_empty_or_nonempty with rfl | hU₀
  · simp
  -- the intersections in the closure form a compact set, which avoids the frontier and so lies in
  -- `U`
  set K := closure U ∩ f ⁻¹' Sym.basepointDivisor z
  have hK : IsCompact K := hUc.of_isClosed_subset
    (hf.preimage_isClosed_of_isClosed isClosed_closure (Sym.isClosed_basepointDivisor z))
    inter_subset_left
  have hKU : K ⊆ U := fun w ⟨hwcl, hwD⟩ => by
    by_contra hwU
    exact hfr w ⟨hwcl, by rwa [hUo.interior_eq]⟩ hwD
  have hcont : ∀ w ∈ U, ContinuousAt f w := fun w hw =>
    hf.continuousAt (mem_of_superset (hUo.mem_nhds hw) subset_closure)
  exact (finite_basepointDivisor_intersections_of_isPreconnected z hU hK hKU hcont ha
    (exists_mem_notMem_basepointDivisor_of_frontier hU₀ hUc hf hfr)).subset
    fun w ⟨hwU, hwD⟩ => ⟨⟨subset_closure hwU, hwD⟩, hwD⟩

end TauCeti

end
