/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.GeneralizedGeodesic.Convex
import TauCeti.Data.EReal.Operations

/-!
# Stability of convexity along generalized geodesics

Convexity witnessed by some generalized-geodesic plan is not in general stable under addition:
two energies may choose different plans. `TauCeti.ConvexAlongGeneralizedGeodesics` requires the
convexity inequality along every such plan based at a fixed law. This stronger condition is
stable under sums, nonnegative multiples, suprema and pointwise limits. Adding such an energy
to a `TauCeti.GeneralizedGeodesicallyConvex` energy preserves the latter condition, with the
sum of the convexity parameters. These rules allow composite energies to use the uniqueness
theorem for the Jordan–Kinderlehrer–Otto step without assuming a common witnessing plan.

The correction uses the quadratic cost of the endpoint coupling carried by the three-plan,
not the squared Wasserstein distance of its endpoints. In a separable Hilbert space the squared
distance from the base law satisfies the stronger condition with parameter `2`.

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

/-- The energy `φ` is `m`-convex along every quadratic generalized-geodesic plan based at `μ`
whose endpoints have energy different from `⊤`. The remainder uses the quadratic cost of the
endpoint coupling carried by the plan; endpoint energy `⊥` is allowed. -/
def ConvexAlongGeneralizedGeodesics (m : ℝ) (φ : WassersteinSpace 2 E → EReal)
    (μ : WassersteinSpace 2 E) : Prop :=
  ∀ ⦃ν₀ ν₁ : WassersteinSpace 2 E⦄, φ ν₀ ≠ ⊤ → φ ν₁ ≠ ⊤ →
    ∀ ⦃γ : Measure (E × E × E)⦄,
      IsGeneralizedGeodesicPlan 2 γ ((μ : ProbabilityMeasure E) : Measure E)
        ((ν₀ : ProbabilityMeasure E) : Measure E) ((ν₁ : ProbabilityMeasure E) : Measure E) →
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ ν : WassersteinSpace 2 E,
        ((ν : ProbabilityMeasure E) : Measure E) = generalizedGeodesic γ t →
        φ ν ≤ ((1 - t : ℝ) : EReal) * φ ν₀ + (t : EReal) * φ ν₁ -
          ((m / 2 * t * (1 - t) * ∫ z, ‖z.1 - z.2‖ ^ 2 ∂γ.snd : ℝ) : EReal)

/-- The defining inequality for convexity along every generalized-geodesic plan. -/
theorem convexAlongGeneralizedGeodesics_def :
    ConvexAlongGeneralizedGeodesics m φ μ ↔
      ∀ ⦃ν₀ ν₁ : WassersteinSpace 2 E⦄, φ ν₀ ≠ ⊤ → φ ν₁ ≠ ⊤ →
        ∀ ⦃γ : Measure (E × E × E)⦄,
          IsGeneralizedGeodesicPlan 2 γ ((μ : ProbabilityMeasure E) : Measure E)
            ((ν₀ : ProbabilityMeasure E) : Measure E) ((ν₁ : ProbabilityMeasure E) : Measure E) →
          ∀ t ∈ Icc (0 : ℝ) 1, ∀ ν : WassersteinSpace 2 E,
            ((ν : ProbabilityMeasure E) : Measure E) = generalizedGeodesic γ t →
            φ ν ≤ ((1 - t : ℝ) : EReal) * φ ν₀ + (t : EReal) * φ ν₁ -
              ((m / 2 * t * (1 - t) * ∫ z, ‖z.1 - z.2‖ ^ 2 ∂γ.snd : ℝ) : EReal) :=
  Iff.rfl

/-- The effective domain is preserved along every generalized-geodesic plan. -/
theorem ConvexAlongGeneralizedGeodesics.apply_ne_top
    (h : ConvexAlongGeneralizedGeodesics m φ μ) {ν₀ ν₁ ν : WassersteinSpace 2 E}
    (h₀ : φ ν₀ ≠ ⊤) (h₁ : φ ν₁ ≠ ⊤) {γ : Measure (E × E × E)}
    (hγ : IsGeneralizedGeodesicPlan 2 γ ((μ : ProbabilityMeasure E) : Measure E)
      ((ν₀ : ProbabilityMeasure E) : Measure E) ((ν₁ : ProbabilityMeasure E) : Measure E))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hν : ((ν : ProbabilityMeasure E) : Measure E) = generalizedGeodesic γ t) : φ ν ≠ ⊤ :=
  ne_top_of_le_ne_top
    (EReal.coe_mul_add_coe_mul_sub_coe_ne_top h₀ h₁ (sub_nonneg.2 ht.2) ht.1)
    (h h₀ h₁ hγ t ht ν hν)

/-- Convexity along every generalized-geodesic plan persists with a smaller parameter. -/
theorem ConvexAlongGeneralizedGeodesics.mono (h : ConvexAlongGeneralizedGeodesics m φ μ)
    (hm : m' ≤ m) : ConvexAlongGeneralizedGeodesics m' φ μ := by
  intro ν₀ ν₁ h₀ h₁ γ hγ t ht ν hν
  refine (h h₀ h₁ hγ t ht ν hν).trans (EReal.sub_le_sub le_rfl ?_)
  apply EReal.coe_le_coe_iff.2
  have : 0 ≤ t * (1 - t) * ∫ z, ‖z.1 - z.2‖ ^ 2 ∂γ.snd :=
    mul_nonneg (mul_nonneg ht.1 (sub_nonneg.2 ht.2)) (integral_nonneg fun _ ↦ by positivity)
  nlinarith

/-- Sums of energies convex along every generalized-geodesic plan have the sum parameter.
Excluding `⊥` ensures that finite energy of the sum implies finite energy of both summands. -/
theorem ConvexAlongGeneralizedGeodesics.add (hφ : ConvexAlongGeneralizedGeodesics m φ μ)
    (hψ : ConvexAlongGeneralizedGeodesics m' ψ μ) (hφ' : ∀ ν, φ ν ≠ ⊥)
    (hψ' : ∀ ν, ψ ν ≠ ⊥) : ConvexAlongGeneralizedGeodesics (m + m') (φ + ψ) μ := by
  intro ν₀ ν₁ h₀ h₁ γ hγ t ht ν hν
  have h₀' := (EReal.add_ne_top_iff_ne_top₂ (hφ' ν₀) (hψ' ν₀)).1 h₀
  have h₁' := (EReal.add_ne_top_iff_ne_top₂ (hφ' ν₁) (hψ' ν₁)).1 h₁
  calc (φ + ψ) ν = φ ν + ψ ν := rfl
    _ ≤ _ := add_le_add (hφ h₀'.1 h₁'.1 hγ t ht ν hν) (hψ h₀'.2 h₁'.2 hγ t ht ν hν)
    _ = _ := by
      rw [EReal.coe_mul_add_coe_mul_sub_add_sub_comm _ _ _ _ (sub_nonneg.2 ht.2) ht.1]
      congr 2
      ring

/-- Adding an energy convex along every generalized-geodesic plan preserves convexity along
some plan, using the witnessing plan of the first energy. Neither energy may take `⊥`. -/
theorem GeneralizedGeodesicallyConvex.add_convexAlongGeneralizedGeodesics
    (hφ : GeneralizedGeodesicallyConvex m φ μ) (hψ : ConvexAlongGeneralizedGeodesics m' ψ μ)
    (hφ' : ∀ ν, φ ν ≠ ⊥) (hψ' : ∀ ν, ψ ν ≠ ⊥) :
    GeneralizedGeodesicallyConvex (m + m') (φ + ψ) μ := by
  rw [generalizedGeodesicallyConvex_def] at hφ ⊢
  intro ν₀ ν₁ h₀ h₁
  have h₀' := (EReal.add_ne_top_iff_ne_top₂ (hφ' ν₀) (hψ' ν₀)).1 h₀
  have h₁' := (EReal.add_ne_top_iff_ne_top₂ (hφ' ν₁) (hψ' ν₁)).1 h₁
  obtain ⟨γ, hγ, hconv⟩ := hφ h₀'.1 h₁'.1
  refine ⟨γ, hγ, fun t ht ν hν ↦ ?_⟩
  calc (φ + ψ) ν = φ ν + ψ ν := rfl
    _ ≤ _ := add_le_add (hconv t ht ν hν) (hψ h₀'.2 h₁'.2 hγ t ht ν hν)
    _ = _ := by
      rw [EReal.coe_mul_add_coe_mul_sub_add_sub_comm _ _ _ _ (sub_nonneg.2 ht.2) ht.1]
      congr 2
      ring

/-- Nonnegative multiples preserve convexity along every generalized-geodesic plan, multiplying
the parameter by the same scalar. At scalar zero the energy is identically zero. -/
theorem ConvexAlongGeneralizedGeodesics.const_mul (h : ConvexAlongGeneralizedGeodesics m φ μ)
    {c : ℝ} (hc : 0 ≤ c) :
    ConvexAlongGeneralizedGeodesics (c * m) (fun ν ↦ (c : EReal) * φ ν) μ := by
  rcases hc.eq_or_lt with rfl | hc
  · intro _ _ _ _ _ _ t _ ν _
    simp
  intro ν₀ ν₁ h₀ h₁ γ hγ t ht ν hν
  have hne {d : EReal} (hd : (c : EReal) * d ≠ ⊤) : d ≠ ⊤ := by
    rintro rfl
    exact hd (EReal.coe_mul_top_of_pos hc)
  calc (c : EReal) * φ ν ≤ (c : EReal) * (((1 - t : ℝ) : EReal) * φ ν₀ +
        (t : EReal) * φ ν₁ - ((m / 2 * t * (1 - t) * ∫ z, ‖z.1 - z.2‖ ^ 2 ∂γ.snd : ℝ) : EReal)) :=
      mul_le_mul_of_nonneg_left (h (hne h₀) (hne h₁) hγ t ht ν hν) (EReal.coe_nonneg.2 hc.le)
    _ = _ := by
      rw [EReal.mul_sub_of_nonneg_of_ne_top (EReal.coe_nonneg.2 hc.le) (EReal.coe_ne_top _),
        EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.2 hc.le) (EReal.coe_ne_top _),
        mul_left_comm, mul_left_comm (c : EReal) (t : EReal), ← EReal.coe_mul]
      congr 2
      ring

/-- Positive multiples preserve convexity witnessed by some generalized-geodesic plan. -/
theorem GeneralizedGeodesicallyConvex.const_mul (h : GeneralizedGeodesicallyConvex m φ μ)
    {c : ℝ} (hc : 0 < c) :
    GeneralizedGeodesicallyConvex (c * m) (fun ν ↦ (c : EReal) * φ ν) μ := by
  rw [generalizedGeodesicallyConvex_def] at h ⊢
  intro ν₀ ν₁ h₀ h₁
  have hne {d : EReal} (hd : (c : EReal) * d ≠ ⊤) : d ≠ ⊤ := by
    rintro rfl
    exact hd (EReal.coe_mul_top_of_pos hc)
  obtain ⟨γ, hγ, hconv⟩ := h (hne h₀) (hne h₁)
  refine ⟨γ, hγ, fun t ht ν hν ↦ ?_⟩
  calc (c : EReal) * φ ν ≤ (c : EReal) * (((1 - t : ℝ) : EReal) * φ ν₀ +
        (t : EReal) * φ ν₁ - ((m / 2 * t * (1 - t) * ∫ z, ‖z.1 - z.2‖ ^ 2 ∂γ.snd : ℝ) : EReal)) :=
      mul_le_mul_of_nonneg_left (hconv t ht ν hν) (EReal.coe_nonneg.2 hc.le)
    _ = _ := by
      rw [EReal.mul_sub_of_nonneg_of_ne_top (EReal.coe_nonneg.2 hc.le) (EReal.coe_ne_top _),
        EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.2 hc.le) (EReal.coe_ne_top _),
        mul_left_comm, mul_left_comm (c : EReal) (t : EReal), ← EReal.coe_mul]
      congr 2
      ring

/-- The pointwise supremum preserves convexity along every generalized-geodesic plan with a
common parameter. This includes the empty supremum, the energy identically `⊥`. -/
theorem ConvexAlongGeneralizedGeodesics.iSup {ι : Sort*} {φs : ι → WassersteinSpace 2 E → EReal}
    (h : ∀ i, ConvexAlongGeneralizedGeodesics m (φs i) μ) :
    ConvexAlongGeneralizedGeodesics m (⨆ i, φs i) μ := by
  intro ν₀ ν₁ h₀ h₁ γ hγ t ht ν hν
  simp only [iSup_apply] at h₀ h₁ ⊢
  refine iSup_le fun i ↦ (h i
    (ne_top_of_le_ne_top h₀ (le_iSup (fun i ↦ φs i ν₀) i))
    (ne_top_of_le_ne_top h₁ (le_iSup (fun i ↦ φs i ν₁) i)) hγ t ht ν hν).trans ?_
  exact EReal.sub_le_sub (add_le_add
    (mul_le_mul_of_nonneg_left (le_iSup (fun i ↦ φs i ν₀) i)
      (EReal.coe_nonneg.2 (sub_nonneg.2 ht.2)))
    (mul_le_mul_of_nonneg_left (le_iSup (fun i ↦ φs i ν₁) i) (EReal.coe_nonneg.2 ht.1))) le_rfl

/-- Convexity along every generalized-geodesic plan passes to pointwise limits. No compactness
or convergence of witnessing plans is needed, because the inequality holds along each fixed plan. -/
theorem ConvexAlongGeneralizedGeodesics.of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {φs : ι → WassersteinSpace 2 E → EReal}
    (h : ∀ᶠ i in l, ConvexAlongGeneralizedGeodesics m (φs i) μ)
    (hφ : ∀ ν, Tendsto (fun i ↦ φs i ν) l (𝓝 (φ ν))) :
    ConvexAlongGeneralizedGeodesics m φ μ := by
  intro ν₀ ν₁ h₀ h₁ γ hγ t ht ν hν
  have hev {z : WassersteinSpace 2 E} (hz : φ z ≠ ⊤) : ∀ᶠ i in l, φs i z ≠ ⊤ :=
    ((hφ z).eventually (gt_mem_nhds hz.lt_top)).mono fun _ hi ↦ hi.ne
  have hmul (s : ℝ) (z : WassersteinSpace 2 E) :=
    EReal.Tendsto.const_mul (hφ z) (.inl (EReal.coe_ne_bot s)) (.inl (EReal.coe_ne_top s))
  have hne {c : ℝ} (hc : 0 ≤ c) {d : EReal} (hd : d ≠ ⊤) : (c : EReal) * d ≠ ⊤ := by
    simp [EReal.mul_ne_top, hc, hd]
  have ha := hne (sub_nonneg.2 ht.2) h₀
  have hb := hne ht.1 h₁
  -- Finite-above endpoint values prevent the indeterminate sum `⊤ + ⊥` in the limit bound.
  have hadd := (EReal.continuousAt_add (.inl ha) (.inr hb)).tendsto.comp
    ((hmul (1 - t) ν₀).prodMk_nhds (hmul t ν₁))
  have hR := (EReal.continuousAt_add (.inl (EReal.add_ne_top ha hb))
    (.inr (EReal.coe_ne_top (-(m / 2 * t * (1 - t) *
      ∫ z, ‖z.1 - z.2‖ ^ 2 ∂γ.snd))))).tendsto.comp
        (hadd.prodMk_nhds (tendsto_const_nhds
          (x := ((-(m / 2 * t * (1 - t) * ∫ z, ‖z.1 - z.2‖ ^ 2 ∂γ.snd) : ℝ) : EReal))))
  simp only [EReal.coe_neg] at hR
  exact le_of_tendsto_of_tendsto (hφ ν) hR
    ((h.and ((hev h₀).and (hev h₁))).mono fun i hi ↦ hi.1 hi.2.1 hi.2.2 hγ t ht ν hν)

section Polish

variable [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]

/-- On a separable Banach space, convexity along every generalized-geodesic plan implies
convexity witnessed by some plan, since optimal plans out of the base law can be glued. -/
theorem ConvexAlongGeneralizedGeodesics.generalizedGeodesicallyConvex
    (h : ConvexAlongGeneralizedGeodesics m φ μ) : GeneralizedGeodesicallyConvex m φ μ := by
  rw [generalizedGeodesicallyConvex_def]
  intro ν₀ ν₁ h₀ h₁
  obtain ⟨γ, hγ⟩ := exists_isGeneralizedGeodesicPlan two_ne_zero
    ((μ : ProbabilityMeasure E) : Measure E) ((ν₀ : ProbabilityMeasure E) : Measure E)
    ((ν₁ : ProbabilityMeasure E) : Measure E) ⟨_, isCoupling_prod _ _⟩ ⟨_, isCoupling_prod _ _⟩
  exact ⟨γ, hγ, h h₀ h₁ hγ⟩

end Polish

end NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]

/-- In a separable Hilbert space, the squared Wasserstein distance from the base law is
`2`-convex along every generalized-geodesic plan based at that law. -/
theorem convexAlongGeneralizedGeodesics_dist_sq (μ : WassersteinSpace 2 E) :
    ConvexAlongGeneralizedGeodesics 2 (fun ν ↦ ((dist μ ν ^ 2 : ℝ) : EReal)) μ := by
  intro ν₀ ν₁ _ _ γ hγ t ht ν hν
  have hd := hγ.dist_sq_add_le ht hν
  have : dist μ ν ^ 2 ≤ (1 - t) * dist μ ν₀ ^ 2 + t * dist μ ν₁ ^ 2 -
      2 / 2 * t * (1 - t) * ∫ z, ‖z.1 - z.2‖ ^ 2 ∂γ.snd := by linarith
  simpa only [← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_sub, EReal.coe_le_coe_iff]
    using this

end TauCeti
