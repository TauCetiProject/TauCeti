/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.LocalMultiplicity
public import TauCeti.Analysis.Complex.LocalNormalForm
public import TauCeti.Topology.Covering.LocalPower
import TauCeti.Analysis.Complex.RiemannSurface.IdentityTheorem

/-!
# Local power coordinates for holomorphic maps of Riemann surfaces

A map holomorphic and nonconstant near a point has the local expression `u ↦ u ^ m`, where
`m` is its local multiplicity. Given any target chart at the image, we construct a source chart
in the maximal holomorphic atlas, centered at the source point. Subtracting the coordinate of the
image centers the target chart. The power identity holds on the entire source chart domain,
and that domain maps into the given target chart. It can be chosen inside any prescribed
neighbourhood of the source point.

This supplies actual biholomorphic coordinates at ramification points, rather than just a count
of nearby fibres. They are the local models used to remove and replace branch discs in the
branched-cover Euler-characteristic argument. The theorem
`TauCeti.RiemannSurface.isLocalPowerAt_localMultiplicity` packages the same coordinates in the
topological `TauCeti.IsLocalPowerAt` vocabulary used by branched covers. In particular, on a
connected Riemann surface every fibre of a nonconstant holomorphic map is discrete
(`TauCeti.RiemannSurface.eventually_apply_ne_of_ne_const`).

## References

* Otto Forster, *Lectures on Riemann Surfaces*, §2, the local normal form theorem.
* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Chapter II, §4.
-/

public noncomputable section

open Filter Function IsManifold Set Topology
open scoped Manifold

namespace TauCeti.RiemannSurface

variable {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ) 1 X] [IsManifold 𝓘(ℂ) 1 Y] {f : X → Y} {x : X}

/-- **The local power-map normal form.** For any target chart at the image of a point where a
holomorphic map is not locally constant, there is a centered source chart in which the map is
the power with exponent its local multiplicity. The identity holds on the whole source chart
and its image lies in the target chart domain. The source chart can be chosen inside any
prescribed neighbourhood. -/
theorem exists_chart_eq_pow_localMultiplicity
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y)
    (hne : ¬ EventuallyConst f (𝓝 x)) {e' : OpenPartialHomeomorph Y ℂ}
    (he' : e' ∈ maximalAtlas 𝓘(ℂ) 1 Y) (hfx : f x ∈ e'.source)
    {W : Set X} (hW : W ∈ 𝓝 x) :
    ∃ e : OpenPartialHomeomorph X ℂ, e ∈ maximalAtlas 𝓘(ℂ) 1 X ∧
      x ∈ e.source ∧ e x = 0 ∧ e.source ⊆ W ∧ ∀ y ∈ e.source,
        f y ∈ e'.source ∧ e' (f y) - e' (f x) = e y ^ localMultiplicity f x := by
  -- Apply the planar normal form to the recentred representative in existing charts.
  let c := chartAt ℂ x
  have hc : c ∈ maximalAtlas 𝓘(ℂ) 1 X := chart_mem_maximalAtlas x
  have hx : x ∈ c.source := mem_chart_source ℂ x
  let F : ℂ → ℂ := fun z ↦ e' (f (c.symm z))
  have hF : AnalyticAt ℂ F (c x) :=
    analyticAt_chart_comp_comp_symm hc he' hx hfx hf
  have hm : 0 < localMultiplicity f x := (localMultiplicity_pos_iff hf).2 hne
  have hmult : localMultiplicity f x =
      analyticOrderNatAt (fun z ↦ F z - F (c x)) (c x) := by
    simpa only [F, c.left_inv hx] using
      localMultiplicity_eq_analyticOrderNatAt hc he' hx hfx hf
  have hFtop : analyticOrderAt (fun z ↦ F z - F (c x)) (c x) ≠ ⊤ := by
    intro ht
    rw [hmult, analyticOrderNatAt, ht, ENat.toNat_top] at hm
    exact Nat.lt_irrefl 0 hm
  have horder : analyticOrderAt (fun z ↦ F z - F (c x)) (c x) = localMultiplicity f x := by
    rw [hmult, Nat.cast_analyticOrderNatAt hFtop]
  -- Prescribe a coordinate neighbourhood inside W and the preimage of the target chart domain.
  have htarget : (f ⁻¹' e'.source) ∩ W ∈ 𝓝 x :=
    inter_mem
      (hf.self_of_nhds.continuousAt.preimage_mem_nhds (e'.open_source.mem_nhds hfx)) hW
  have hcoord : c.symm ⁻¹' ((f ⁻¹' e'.source) ∩ W) ∈ 𝓝 (c x) := by
    apply (c.continuousAt_symm (c.map_source hx)).preimage_mem_nhds
    rwa [c.left_inv hx]
  obtain ⟨a, hxa, ha0, hasub, ha, hai, hpow⟩ :=
    hF.exists_openPartialHomeomorph_sub_eq_pow hm horder hcoord
  -- The analytic coordinate and its inverse give a chart in the maximal holomorphic atlas.
  let b := c.trans a
  have hb : b ∈ maximalAtlas 𝓘(ℂ) 1 X := by
    apply b.mem_maximalAtlas_of_contMDiffOn
    · exact ha.contDiffOn_of_completeSpace.contMDiffOn.comp
        ((contMDiffOn_of_mem_maximalAtlas hc).mono inter_subset_left) inter_subset_right
    · exact (contMDiffOn_symm_of_mem_maximalAtlas hc).comp
        (hai.contDiffOn_of_completeSpace.contMDiffOn.mono inter_subset_left)
        inter_subset_right
  have hbsub : ∀ y ∈ b.source, f y ∈ e'.source ∧ y ∈ W := by
    intro y hy
    have h : c y ∈ c.symm ⁻¹' ((f ⁻¹' e'.source) ∩ W) := hasub hy.2
    rw [mem_preimage, c.left_inv hy.1] at h
    exact h
  refine ⟨b, hb, ⟨hx, hxa⟩, ?_, ?_, ?_⟩
  · simpa only [b, OpenPartialHomeomorph.trans_apply] using ha0
  · intro y hy
    exact (hbsub y hy).2
  · intro y hy
    refine ⟨(hbsub y hy).1, ?_⟩
    have h := hpow (c y) hy.2
    simpa only [F, c.left_inv hy.1, c.left_inv hx, b,
      OpenPartialHomeomorph.trans_apply] using h

/-- A holomorphic map that is nonconstant near `x` is locally the power map whose exponent is
its local multiplicity. This is the topological local-power formulation of
`exists_chart_eq_pow_localMultiplicity`. -/
theorem isLocalPowerAt_localMultiplicity
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y)
    (hne : ¬ EventuallyConst f (𝓝 x)) : IsLocalPowerAt f x (localMultiplicity f x) := by
  let e' := chartAt ℂ (f x)
  let τ := Homeomorph.addRight (-e' (f x))
  let ψ := e'.trans τ.toOpenPartialHomeomorph
  obtain ⟨e, -, hxe, hex, -, hpow⟩ := exists_chart_eq_pow_localMultiplicity hf hne
    (chart_mem_maximalAtlas (f x)) (mem_chart_source ℂ (f x)) univ_mem
  have hψ (y) : ψ y = e' y - e' (f x) := by
    rw [OpenPartialHomeomorph.trans_apply, sub_eq_add_neg]
    rfl
  have hψ_source : ψ.source = e'.source := by
    rw [OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
      preimage_univ, inter_univ]
  rw [isLocalPowerAt_iff]
  refine ⟨e, ψ, hxe, ?_, hex, ?_, ?_⟩
  · intro y hy
    rw [hψ_source]
    exact (hpow y hy).1
  · rw [hψ, sub_self]
  · intro w hw
    have hy : e.symm w ∈ e.source := e.map_target hw
    rw [hψ]
    simpa only [e.right_inv hw] using (hpow _ hy).2

/-- **Discreteness of the fibres.** On a connected Riemann surface, a holomorphic map other than the
constant map with value `y₀` takes the value `y₀` at no point of a punctured neighbourhood of any
point. -/
theorem eventually_apply_ne_of_ne_const [PreconnectedSpace X]
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) {y₀ : Y} (h : f ≠ fun _ ↦ y₀) (x : X) :
    ∀ᶠ y in 𝓝[≠] x, f y ≠ y₀ := by
  have := ChartedSpace.t1Space ℂ Y
  rcases eq_or_ne (f x) y₀ with hx | hx
  · obtain ⟨x₁, hx₁⟩ : ∃ x₁, f x₁ ≠ f x := by
      by_contra! hc
      exact h (funext fun y ↦ (hc y).trans hx)
    exact hx ▸ (isLocalPowerAt_localMultiplicity (.of_forall hf)
      (not_eventuallyConst_of_ne hf hx₁ x)).eventually_ne
  · exact nhdsWithin_le_nhds ((hf x).continuousAt.eventually (isOpen_ne.mem_nhds hx))

end TauCeti.RiemannSurface
