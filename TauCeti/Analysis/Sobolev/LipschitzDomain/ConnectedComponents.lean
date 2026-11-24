/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Basic
public import TauCeti.Topology.Connected.FiniteComponents
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Connected components of a Lipschitz domain

A Lipschitz domain with compact frontier, in particular a bounded Lipschitz domain in a proper
space such as `ℝⁿ`, has only finitely many connected components
(`Set.IsLipschitzDomain.finite_connectedComponents`,
`Set.IsLipschitzDomain.finite_connectedComponents_of_isBounded`). This is what makes the kernel
of the Neumann Laplacian, the locally constant functions on the domain, finite-dimensional, with
dimension the number of components.

The local input is that the domain is connected near each of its frontier points: inside the
cylinder of a chart centred at a frontier point, after shrinking the radius so that the graph
stays below the top of the cylinder, the domain is the region between the graph and the top,
which is connected (`TauCeti.isPreconnected_setOf_lt_fst_inter_normalCylinder`,
`Set.IsLipschitzDomain.exists_mem_nhds_isPreconnected_inter`). Each component other than the
whole space reaches the frontier, so it contains the part of the domain in one of the finitely
many chart cylinders covering the compact frontier
(`TauCeti.finite_connectedComponents_of_isCompact_frontier`).

Some boundary regularity is needed: the union of the disjoint open discs of radius `4⁻⁽ᵏ⁺¹⁾`
centred at `(2⁻ᵏ, 0)`, `k ∈ ℕ`, in the plane is bounded with infinitely many components; it is not
a Lipschitz domain at the origin, where the discs accumulate.

## Main declarations

* `TauCeti.isPreconnected_setOf_lt_fst_inter_normalCylinder`: the part of a normal cylinder
  above a continuous graph which stays below the top of the cylinder is preconnected.
* `Set.IsLipschitzDomain.exists_mem_nhds_isPreconnected_inter`: a Lipschitz domain is connected
  near each frontier point.
* `Set.IsLipschitzDomain.finite_connectedComponents`: a Lipschitz domain with compact frontier
  has finitely many connected components.
* `Set.IsLipschitzDomain.finite_connectedComponents_of_isBounded`: so does a bounded Lipschitz
  domain in a proper space.
-/

public section

open Metric Set Topology TauCeti

namespace TauCeti

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The region above a graph in a cylinder is connected.** If `γ : E → ℝ` is continuous on the
ball of radius `r` and stays below the height `h` there, then the part of the normal cylinder
`normalCylinder h r` strictly above the graph of `γ` is preconnected. -/
theorem isPreconnected_setOf_lt_fst_inter_normalCylinder {γ : E → ℝ} {h r : ℝ}
    (hγ : ContinuousOn γ (ball 0 r)) (hlt : ∀ y ∈ ball (0 : E) r, γ y < h) :
    IsPreconnected ({x : WithLp 2 (ℝ × E) | γ x.snd < x.fst} ∩ normalCylinder h r) := by
  rcases le_or_gt h 0 with hh | hh
  · -- The cylinder is empty.
    convert isPreconnected_empty
    refine eq_empty_of_forall_notMem fun x hx ↦ ?_
    rw [mem_inter_iff, mem_normalCylinder] at hx
    linarith [hx.2.1, hx.2.2.1]
  -- The region is the image of the convex set `ball 0 r ×ˢ Ioo 0 1` under the map `φ` sending
  -- `(y, s)` to the point at relative height `s` of the vertical fibre `(b y, h)` over `y`, whose
  -- bottom `b y` lies below its top `h`.
  set b : E → ℝ := fun y ↦ max (γ y) (-h)
  have hbh : ∀ y ∈ ball (0 : E) r, b y < h := fun y hy ↦ max_lt (hlt y hy) (by linarith)
  set φ : E × ℝ → WithLp 2 (ℝ × E) := fun q ↦ WithLp.toLp 2 (b q.1 + q.2 * (h - b q.1), q.1)
  have himage : {x : WithLp 2 (ℝ × E) | γ x.snd < x.fst} ∩ normalCylinder h r =
      φ '' (ball 0 r ×ˢ Ioo 0 1) := by
    ext x
    constructor
    · rintro ⟨hx, hxC⟩
      rw [mem_normalCylinder] at hxC
      have hy : x.snd ∈ ball (0 : E) r := mem_ball_zero_iff.2 hxC.2.2
      have hbx : b x.snd < x.fst := max_lt hx hxC.1
      have hpos := sub_pos.2 (hbh _ hy)
      refine ⟨(x.snd, (x.fst - b x.snd) / (h - b x.snd)),
        ⟨hy, div_pos (sub_pos.2 hbx) hpos, (div_lt_one hpos).2 (by linarith)⟩, ?_⟩
      exact WithLp.ofLp_injective 2 (by simp [φ, Prod.ext_iff, div_mul_cancel₀ _ hpos.ne'])
    · rintro ⟨⟨y, s⟩, ⟨hy, hs0, hs1⟩, rfl⟩
      have hpos := sub_pos.2 (hbh y hy)
      have h1 := le_max_left (γ y) (-h)
      have h2 := le_max_right (γ y) (-h)
      have h3 : 0 < s * (h - b y) := mul_pos hs0 hpos
      have h4 : s * (h - b y) < h - b y := mul_lt_of_lt_one_left hpos hs1
      refine ⟨?_, ?_⟩
      · simp only [φ, mem_ofPred_eq, WithLp.toLp_fst, WithLp.toLp_snd]
        linarith
      · rw [mem_normalCylinder]
        simp only [φ, WithLp.toLp_fst, WithLp.toLp_snd]
        exact ⟨by linarith, by linarith, mem_ball_zero_iff.1 hy⟩
  have hb : ContinuousOn (fun q : E × ℝ ↦ b q.1) (ball 0 r ×ˢ Ioo 0 1) :=
    (hγ.comp continuousOn_fst fun _ hq ↦ (mem_prod.1 hq).1).sup continuousOn_const
  rw [himage]
  exact ((convex_ball 0 r).prod (convex_Ioo 0 1)).isPreconnected.image φ <|
    (WithLp.prod_continuous_toLp 2 ℝ E).comp_continuousOn
      ((hb.add (continuousOn_snd.mul (continuousOn_const.sub hb))).prodMk continuousOn_fst)

end TauCeti

namespace Set.IsLipschitzDomain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Set F}

/-- **A Lipschitz domain is connected near each frontier point.** Every frontier point `x` of a
Lipschitz domain `Ω` has a neighbourhood `N` for which `N ∩ Ω` is preconnected. -/
theorem exists_mem_nhds_isPreconnected_inter (hΩ : Ω.IsLipschitzDomain E) {x : F}
    (hx : x ∈ frontier Ω) : ∃ N ∈ 𝓝 x, IsPreconnected (N ∩ Ω) := by
  obtain ⟨e₀, γ₀, K, h₀, r₀, hc₀, hxC⟩ :=
    isLipschitzDomain_iff_exists_mem_normalCylinder.1 hΩ x hx
  obtain ⟨e, γ, h, r, hc, hex⟩ := hc₀.exists_isLipschitzChart_eq_zero hxC
  have hγ0 := hc.apply_zero_of_mem_frontier hx hex
  -- Take `N` to be the cylinder of a chart centred at `x`, shrunk to a radius `r' ≤ h / (K + 1)`
  -- so that `γ y ≤ K ‖y‖ < h` on the ball of radius `r'`: the graph stays below the top.
  set r' := min r (h / (K + 1))
  have hr' : 0 < r' := lt_min hc.radius_pos (by have := hc.height_pos; positivity)
  have hc' := hc.mono hc.height_pos hr' le_rfl (min_le_left _ _)
  refine ⟨e ⁻¹' normalCylinder h r', ((isOpen_normalCylinder h r').preimage e.continuous).mem_nhds
    (by simpa [hex] using zero_mem_normalCylinder (E := E) hc.height_pos hr'), ?_⟩
  rw [← e.toHomeomorph.isPreconnected_image, AffineIsometryEquiv.coe_toHomeomorph,
    image_preimage_inter, inter_comm, hc'.image_inter_normalCylinder]
  refine isPreconnected_setOf_lt_fst_inter_normalCylinder hc.lipschitzWith.continuous.continuousOn
    fun y hy ↦ ?_
  have hy' : (K + 1) * ‖y‖ < h := by
    have := (lt_min_iff.1 (mem_ball_zero_iff.1 hy)).2
    rwa [lt_div_iff₀ (by positivity), mul_comm] at this
  have hlip := hc.lipschitzWith.dist_le_mul y 0
  rw [hγ0, Real.dist_eq, sub_zero, dist_zero_right] at hlip
  nlinarith [le_abs_self (γ y), norm_nonneg y]

/-- **A Lipschitz domain with compact frontier has finitely many connected components.** This
includes exterior domains, whose frontier is compact although they are unbounded. -/
theorem finite_connectedComponents (hΩ : Ω.IsLipschitzDomain E) (hc : IsCompact (frontier Ω)) :
    Finite (ConnectedComponents Ω) :=
  TauCeti.finite_connectedComponents_of_isCompact_frontier hc fun _ hx ↦
    hΩ.exists_mem_nhds_isPreconnected_inter hx

/-- **A bounded Lipschitz domain has finitely many connected components**, in a proper space such
as `ℝⁿ`. -/
theorem finite_connectedComponents_of_isBounded [ProperSpace F] (hΩ : Ω.IsLipschitzDomain E)
    (hb : Bornology.IsBounded Ω) : Finite (ConnectedComponents Ω) :=
  hΩ.finite_connectedComponents <| isCompact_of_isClosed_isBounded isClosed_frontier
    (hb.closure.subset frontier_subset_closure)

end Set.IsLipschitzDomain
