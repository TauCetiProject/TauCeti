/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.GeneralizedGeodesic.Convex
import TauCeti.Data.EReal.Operations
import TauCeti.Topology.Instances.EReal

/-!
# Stability of convexity along generalized geodesics

Convexity witnessed by some generalized-geodesic plan is not in general stable under addition:
two energies may choose different plans. `TauCeti.ConvexAlongGeneralizedGeodesics` requires the
convexity inequality along every such plan based at a fixed law. On separable Banach spaces it
implies `TauCeti.GeneralizedGeodesicallyConvex`. The every-plan condition is stable under sums
of energies that never take `⊥`, nonnegative multiples, suprema and pointwise limits. Adding
such an energy to a `TauCeti.GeneralizedGeodesicallyConvex` energy preserves the latter
condition, with the sum of the convexity parameters, provided neither energy takes `⊥`.
These rules allow composite energies to use the uniqueness theorem for the
Jordan–Kinderlehrer–Otto step without assuming a common witnessing plan.

The correction uses the quadratic cost of the endpoint coupling carried by the three-plan,
not the squared Wasserstein distance of its endpoints. In a separable Hilbert space the squared
distance from the base law satisfies the every-plan condition with parameter `2`.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, §9.2 and Chapter 4, Assumption 4.0.1.
-/

public section

open MeasureTheory Set Filter Topology

namespace TauCeti

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  {m m' : ℝ} {φ ψ : WassersteinSpace 2 E → EReal} {μ : WassersteinSpace 2 E}
  {ν₀ ν₁ : WassersteinSpace 2 E} {γ : Measure (E × E × E)}

/-- Energies convex along the same three-plan add, with the sum of their parameters. -/
theorem ConvexAlongGeneralizedGeodesicPlan.add
    (hφ : ConvexAlongGeneralizedGeodesicPlan m φ ν₀ ν₁ γ)
    (hψ : ConvexAlongGeneralizedGeodesicPlan m' ψ ν₀ ν₁ γ) :
    ConvexAlongGeneralizedGeodesicPlan (m + m') (φ + ψ) ν₀ ν₁ γ := by
  rw [convexAlongGeneralizedGeodesicPlan_def] at hφ hψ ⊢
  intro t ht ν hν
  calc (φ + ψ) ν = φ ν + ψ ν := rfl
    _ ≤ _ := add_le_add (hφ t ht ν hν) (hψ t ht ν hν)
    _ = _ := by
      rw [EReal.coe_mul_add_coe_mul_sub_add_sub_comm _ _ _ _ (sub_nonneg.2 ht.2) ht.1]
      congr 2
      ring

/-- Nonnegative multiples preserve convexity along a fixed three-plan, multiplying the
parameter by the same scalar. -/
theorem ConvexAlongGeneralizedGeodesicPlan.const_mul
    (h : ConvexAlongGeneralizedGeodesicPlan m φ ν₀ ν₁ γ) {c : ℝ} (hc : 0 ≤ c) :
    ConvexAlongGeneralizedGeodesicPlan (c * m) (fun ν ↦ (c : EReal) * φ ν) ν₀ ν₁ γ := by
  rw [convexAlongGeneralizedGeodesicPlan_def] at h ⊢
  intro t ht ν hν
  calc (c : EReal) * φ ν ≤ (c : EReal) * (((1 - t : ℝ) : EReal) * φ ν₀ +
        (t : EReal) * φ ν₁ - ((m / 2 * t * (1 - t) * ∫ z, ‖z.1 - z.2‖ ^ 2 ∂γ.snd : ℝ) : EReal)) :=
      mul_le_mul_of_nonneg_left (h t ht ν hν) (EReal.coe_nonneg.2 hc)
    _ = _ := by
      rw [EReal.coe_mul_coe_mul_add_coe_mul_sub _ _ hc]
      congr 2
      ring

/-- The pointwise supremum of energies convex along a fixed three-plan, with a common
parameter, is convex along that plan. The index type may be empty. -/
theorem ConvexAlongGeneralizedGeodesicPlan.iSup {ι : Sort*}
    {φs : ι → WassersteinSpace 2 E → EReal}
    (h : ∀ i, ConvexAlongGeneralizedGeodesicPlan m (φs i) ν₀ ν₁ γ) :
    ConvexAlongGeneralizedGeodesicPlan m (⨆ i, φs i) ν₀ ν₁ γ := by
  simp_rw [convexAlongGeneralizedGeodesicPlan_def] at h ⊢
  intro t ht ν hν
  simp only [iSup_apply]
  refine iSup_le fun i ↦ (h i t ht ν hν).trans ?_
  exact EReal.coe_mul_add_coe_mul_sub_le_of_le (le_iSup (fun i ↦ φs i ν₀) i)
    (le_iSup (fun i ↦ φs i ν₁) i) (sub_nonneg.2 ht.2) ht.1 _

/-- Convexity along a fixed three-plan passes to pointwise limits whose endpoint energies
are different from `⊤`. -/
theorem ConvexAlongGeneralizedGeodesicPlan.of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {φs : ι → WassersteinSpace 2 E → EReal}
    (h : ∀ᶠ i in l, ConvexAlongGeneralizedGeodesicPlan m (φs i) ν₀ ν₁ γ)
    (hφ : ∀ ν, Tendsto (fun i ↦ φs i ν) l (𝓝 (φ ν)))
    (h₀ : φ ν₀ ≠ ⊤) (h₁ : φ ν₁ ≠ ⊤) :
    ConvexAlongGeneralizedGeodesicPlan m φ ν₀ ν₁ γ := by
  simp_rw [convexAlongGeneralizedGeodesicPlan_def] at h ⊢
  intro t ht ν hν
  exact le_of_tendsto_of_tendsto (hφ ν)
    (EReal.tendsto_coe_mul_add_coe_mul_sub (hφ ν₀) (hφ ν₁) h₀ h₁
      (sub_nonneg.2 ht.2) ht.1 _)
    (h.mono fun i hi ↦ hi t ht ν hν)

/-- Sums of energies convex along every generalized-geodesic plan have the sum parameter.
Excluding `⊥` ensures that finite energy of the sum implies finite energy of both summands. -/
theorem ConvexAlongGeneralizedGeodesics.add (hφ : ConvexAlongGeneralizedGeodesics m φ μ)
    (hψ : ConvexAlongGeneralizedGeodesics m' ψ μ) (hφ' : ∀ ν, φ ν ≠ ⊥)
    (hψ' : ∀ ν, ψ ν ≠ ⊥) : ConvexAlongGeneralizedGeodesics (m + m') (φ + ψ) μ := by
  rw [convexAlongGeneralizedGeodesics_def] at hφ hψ ⊢
  exact fun ν₀ ν₁ h₀ h₁ _ hγ ↦
    have h₀' := (EReal.add_ne_top_iff_ne_top₂ (hφ' ν₀) (hψ' ν₀)).1 h₀
    have h₁' := (EReal.add_ne_top_iff_ne_top₂ (hφ' ν₁) (hψ' ν₁)).1 h₁
    (hφ h₀'.1 h₁'.1 hγ).add (hψ h₀'.2 h₁'.2 hγ)

/-- Adding an energy convex along every generalized-geodesic plan preserves convexity along
some plan, using the witnessing plan of the first energy. Neither energy may take `⊥`. -/
theorem GeneralizedGeodesicallyConvex.add_convexAlongGeneralizedGeodesics
    (hφ : GeneralizedGeodesicallyConvex m φ μ) (hψ : ConvexAlongGeneralizedGeodesics m' ψ μ)
    (hφ' : ∀ ν, φ ν ≠ ⊥) (hψ' : ∀ ν, ψ ν ≠ ⊥) :
    GeneralizedGeodesicallyConvex (m + m') (φ + ψ) μ := by
  rw [generalizedGeodesicallyConvex_def] at hφ ⊢
  rw [convexAlongGeneralizedGeodesics_def] at hψ
  exact fun ν₀ ν₁ h₀ h₁ ↦
    have h₀' := (EReal.add_ne_top_iff_ne_top₂ (hφ' ν₀) (hψ' ν₀)).1 h₀
    have h₁' := (EReal.add_ne_top_iff_ne_top₂ (hφ' ν₁) (hψ' ν₁)).1 h₁
    (hφ h₀'.1 h₁'.1).imp fun _ hγ ↦ ⟨hγ.1, hγ.2.add (hψ h₀'.2 h₁'.2 hγ.1)⟩

/-- Nonnegative multiples preserve convexity along every generalized-geodesic plan, multiplying
the parameter by the same scalar. At scalar zero the energy is identically zero. -/
theorem ConvexAlongGeneralizedGeodesics.const_mul (h : ConvexAlongGeneralizedGeodesics m φ μ)
    {c : ℝ} (hc : 0 ≤ c) :
    ConvexAlongGeneralizedGeodesics (c * m) (fun ν ↦ (c : EReal) * φ ν) μ := by
  rw [convexAlongGeneralizedGeodesics_def] at h ⊢
  rcases hc.eq_or_lt with rfl | hc
  · intro _ _ _ _ _ _
    rw [convexAlongGeneralizedGeodesicPlan_def]
    intro t _ ν _
    simp
  exact fun _ _ h₀ h₁ _ hγ ↦
    (h (EReal.ne_top_of_coe_mul_ne_top hc h₀) (EReal.ne_top_of_coe_mul_ne_top hc h₁) hγ).const_mul
      hc.le

/-- Positive multiples preserve convexity witnessed by some generalized-geodesic plan. -/
theorem GeneralizedGeodesicallyConvex.const_mul (h : GeneralizedGeodesicallyConvex m φ μ)
    {c : ℝ} (hc : 0 < c) :
    GeneralizedGeodesicallyConvex (c * m) (fun ν ↦ (c : EReal) * φ ν) μ := by
  rw [generalizedGeodesicallyConvex_def] at h ⊢
  exact fun _ _ h₀ h₁ ↦
    (h (EReal.ne_top_of_coe_mul_ne_top hc h₀) (EReal.ne_top_of_coe_mul_ne_top hc h₁)).imp
      fun _ hγ ↦ ⟨hγ.1, hγ.2.const_mul hc.le⟩

/-- The pointwise supremum preserves convexity along every generalized-geodesic plan with a
common parameter. This includes the empty supremum, the energy identically `⊥`. -/
theorem ConvexAlongGeneralizedGeodesics.iSup {ι : Sort*} {φs : ι → WassersteinSpace 2 E → EReal}
    (h : ∀ i, ConvexAlongGeneralizedGeodesics m (φs i) μ) :
    ConvexAlongGeneralizedGeodesics m (⨆ i, φs i) μ := by
  simp_rw [convexAlongGeneralizedGeodesics_def] at h ⊢
  exact fun ν₀ ν₁ h₀ h₁ _ hγ ↦
    ConvexAlongGeneralizedGeodesicPlan.iSup fun i ↦
      h i (ne_top_of_le_ne_top h₀ (by rw [iSup_apply]; exact le_iSup (fun i ↦ φs i ν₀) i))
        (ne_top_of_le_ne_top h₁ (by rw [iSup_apply]; exact le_iSup (fun i ↦ φs i ν₁) i)) hγ

/-- Convexity along every generalized-geodesic plan passes to pointwise limits. No compactness
or convergence of witnessing plans is needed, because the inequality holds along each fixed plan. -/
theorem ConvexAlongGeneralizedGeodesics.of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {φs : ι → WassersteinSpace 2 E → EReal}
    (h : ∀ᶠ i in l, ConvexAlongGeneralizedGeodesics m (φs i) μ)
    (hφ : ∀ ν, Tendsto (fun i ↦ φs i ν) l (𝓝 (φ ν))) :
    ConvexAlongGeneralizedGeodesics m φ μ := by
  simp_rw [convexAlongGeneralizedGeodesics_def] at h ⊢
  intro ν₀ ν₁ h₀ h₁ γ hγ
  have hev {z : WassersteinSpace 2 E} (hz : φ z ≠ ⊤) : ∀ᶠ i in l, φs i z ≠ ⊤ :=
    ((hφ z).eventually (gt_mem_nhds hz.lt_top)).mono fun _ hi ↦ hi.ne
  exact ConvexAlongGeneralizedGeodesicPlan.of_tendsto
    ((h.and ((hev h₀).and (hev h₁))).mono fun i hi ↦ hi.1 hi.2.1 hi.2.2 hγ) hφ h₀ h₁

end NormedSpace

end TauCeti
