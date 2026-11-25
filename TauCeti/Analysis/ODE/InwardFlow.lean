/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.LocalFlow
public import TauCeti.Analysis.Sobolev.Trace.Reflection.Seeley
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Local flows of inward-pointing fields on a closed half-space

Let `v` be a vector field defined only on the closed half-space `{x | 0 ≤ x.1}` of `ℝ × F`, of
class `C^(n+1)` there near a point `a` of the half-space, and pointing strictly inward at `a`:
`0 < (v a).1`. Then the integral curves of `v` starting at points of the half-space near `a` exist
for a uniform positive time, stay in the half-space, and depend smoothly on the initial point and
time (`TauCeti.ODE.exists_contDiffOn_localFlow_upperHalfSpace`). Their first coordinate is
strictly increasing, so the curves through boundary points enter the open half-space at once.

The field is cut off near `a` and extended across the boundary hyperplane by Seeley's extension
operator `TauCeti.HalfSpaceExtension.seeleyExtension`; the local flow of the extension, from
`ODE.exists_contDiffOn_localFlow`, is the flow. Since the extended field still points strictly
inward near `a`, its integral curves through the half-space never leave it in forward time, and
there the extension agrees with `v`.

This is the coordinate form of the statement that an inward-pointing vector field on a manifold
with boundary can be flowed forward from the boundary, the analytic input to the construction of
collars by flowing the boundary inward.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 4, Theorem 6.1.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Theorem 9.24.
* R. T. Seeley, *Extension of `C^∞` functions defined in a half space*,
  Proc. Amer. Math. Soc. **15** (1964), 625–626.
-/

public section

open Filter Metric Set Topology
open scoped ContDiff

namespace TauCeti.ODE

open TauCeti.HalfSpaceExtension

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **Local flows of inward-pointing fields on a closed half-space.** Let `v` be `C^(n+1)` on the
part of a neighbourhood `s` of `a` in the closed half-space `{x | 0 ≤ x.1}`, with `a` in the
half-space and `v a` pointing strictly inward. Then there are a family `Φ x t`, jointly
`C^(n+1)` on `U × (-ε, ε)` for a neighbourhood `U` of `a`, starting at `x` and satisfying the flow
law, whose first coordinate `t ↦ (Φ x t).1` is strictly increasing on `(-ε, ε)` for `x ∈ U`, and
whose forward curves `t ↦ Φ x t`, `0 ≤ t < ε`, through points `x ∈ U` of the half-space stay in
`s` and in the half-space and are integral curves of `v` there. -/
theorem exists_contDiffOn_localFlow_upperHalfSpace {n : ℕ∞} {v : ℝ × F → ℝ × F}
    {a : ℝ × F} {s : Set (ℝ × F)} (hv : ContDiffOn ℝ (n + 1) v (s ∩ upperHalfSpace F))
    (hs : s ∈ 𝓝 a) (ha : a ∈ upperHalfSpace F) (hva : 0 < (v a).1) :
    ∃ Φ : ℝ × F → ℝ → ℝ × F, ∃ U ∈ 𝓝 a, ∃ ε > 0,
      ContDiffOn ℝ (n + 1) (fun p : (ℝ × F) × ℝ ↦ Φ p.1 p.2) (U ×ˢ Ioo (-ε) ε) ∧
      (∀ x, Φ x 0 = x) ∧ (∀ x t u, Φ x (t + u) = Φ (Φ x t) u) ∧
      (∀ x ∈ U, StrictMonoOn (fun t ↦ (Φ x t).1) (Ioo (-ε) ε)) ∧
      ∀ x ∈ U ∩ upperHalfSpace F, ∀ t ∈ Ico 0 ε,
        Φ x t ∈ s ∩ upperHalfSpace F ∧ HasDerivAt (Φ x) (v (Φ x t)) t := by
  -- Cut the field off near `a` and extend it across the boundary hyperplane.
  obtain ⟨W, r, hr, hrs, hW, hWv⟩ :=
    exists_contDiff_eqOn_upperHalfSpace (n := n + 1) (by exact_mod_cast hv) hs
  obtain ⟨Φ, O, hO, haO, hΦ, hΦ0, hΦadd, hderiv⟩ :=
    ODE.exists_contDiffOn_localFlow W hW.contDiffOn univ_mem
  -- Near `a`, the extended field agrees with `v` on the half-space and points strictly inward.
  let N : Set (ℝ × F) := ball a r ∩ {y | 0 < (W y).1}
  have hN : IsOpen N :=
    isOpen_ball.inter (isOpen_lt continuous_const (continuous_fst.comp hW.continuous))
  have haN : a ∈ N := ⟨mem_ball_self hr, by simpa [hWv ⟨mem_ball_self hr, ha⟩] using hva⟩
  have hΦc : ContinuousAt (fun p : (ℝ × F) × ℝ ↦ Φ p.1 p.2) (a, 0) :=
    (hΦ.continuousOn.continuousAt (hO.mem_nhds haO))
  have hgood : ∀ᶠ p in 𝓝 ((a, 0) : (ℝ × F) × ℝ), p ∈ O ∧ Φ p.1 p.2 ∈ N ∧
      HasDerivAt (Φ p.1) (W (Φ p.1 p.2)) p.2 :=
    (hO.eventually_mem haO).and
      ((hΦc.eventually_mem (by simpa [hΦ0] using hN.mem_nhds haN)).and hderiv)
  obtain ⟨U, hU, T, hT, hUT⟩ := mem_nhds_prod_iff.mp hgood
  obtain ⟨ε, hε, hεT⟩ := Metric.mem_nhds_iff.mp hT
  have hIoo : Ioo (-ε) ε ⊆ T := by
    intro t ht
    apply hεT
    rw [Real.ball_eq_Ioo, zero_sub, zero_add]
    exact ht
  have hUT' {x : ℝ × F} {t : ℝ} (hx : x ∈ U) (ht : t ∈ Ioo (-ε) ε) :=
    hUT (mk_mem_prod hx (hIoo ht))
  have hmono : ∀ x ∈ U, StrictMonoOn (fun t ↦ (Φ x t).1) (Ioo (-ε) ε) := by
    intro x hx
    have hd (t : ℝ) (ht : t ∈ Ioo (-ε) ε) :
        HasDerivAt (fun t ↦ (Φ x t).1) (W (Φ x t)).1 t :=
      ((ContinuousLinearMap.fst ℝ ℝ F).hasFDerivAt.comp_hasDerivAt t (hUT' hx ht).2.2 :)
    refine strictMonoOn_of_deriv_pos (convex_Ioo _ _)
      (fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt) fun t ht ↦ ?_
    rw [interior_Ioo] at ht
    rw [(hd t ht).deriv]
    exact (hUT' hx ht).2.1.2
  refine ⟨Φ, U, hU, ε, hε, hΦ.mono fun p hp ↦ (hUT' hp.1 hp.2).1, hΦ0, hΦadd, hmono, ?_⟩
  rintro x ⟨hxU, hxH⟩ t ⟨ht0, htε⟩
  have ht : t ∈ Ioo (-ε) ε := ⟨by linarith, htε⟩
  have hgood := hUT' hxU ht
  -- The first coordinate does not decrease in forward time, so the curve stays in the half-space.
  have hH : Φ x t ∈ upperHalfSpace F := by
    rw [mem_upperHalfSpace]
    refine (mem_upperHalfSpace.mp hxH).trans ?_
    simpa [hΦ0] using (hmono x hxU).monotoneOn ⟨neg_lt_zero.mpr hε, hε⟩ ht ht0
  refine ⟨⟨hrs hgood.2.1.1, hH⟩, ?_⟩
  rw [← hWv ⟨hgood.2.1.1, hH⟩]
  exact hgood.2.2

end TauCeti.ODE
