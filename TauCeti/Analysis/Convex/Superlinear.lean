/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.SubgradientImage
public import TauCeti.Analysis.Convex.Differentiability
public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Conjugates of superlinear convex functions

A real function is superlinear here when `h x / ‖x‖` tends to infinity outside compact
sets. Subtracting a continuous linear functional then gives a coercive function. Thus a
continuous superlinear function on a proper normed space attains every tilted minimum.
For a strictly convex function the minimizer is unique. In finite-dimensional real inner
product spaces this identifies the gradient of the Legendre–Fenchel conjugate with the
unique point at which the conjugate supremum is attained, without assuming that the
original function is differentiable.

The conjugate and subgradient reciprocity are those of `TauCeti.Analysis.Convex.Conjugate`
and `TauCeti.Analysis.Convex.Subdifferential`. Tilted-minimum attainment uses Mathlib's
`Continuous.exists_forall_le`; continuity of the minimizer uses the local boundedness of
conjugate subgradients and `IsCompact.tendsto_nhds_of_unique_mapClusterPt`.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §26.
* W. Gangbo and R. J. McCann, *The geometry of optimal transportation*, Acta Math. 177
  (1996), for the inverse subgradient in strictly convex displacement costs.
-/

public section

noncomputable section

namespace TauCeti

open Filter Set Metric
open scoped Topology

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  {h : E → ℝ}

/-- Subtracting a continuous linear functional from a superlinear function is coercive. -/
theorem tendsto_sub_atTop_of_superlinear
    (hh : Tendsto (fun x => h x / ‖x‖) (cocompact E) atTop) (ℓ : E →L[ℝ] ℝ) :
    Tendsto (fun x => h x - ℓ x) (cocompact E) atTop := by
  refine tendsto_atTop_mono' (cocompact E) ?_ tendsto_norm_cocompact_atTop
  filter_upwards [hh.eventually_ge_atTop (‖ℓ‖ + 1),
    tendsto_norm_cocompact_atTop.eventually_ge_atTop (1 : ℝ)] with x hx hn
  have hp : 0 < ‖x‖ := lt_of_lt_of_le zero_lt_one hn
  have hb := (le_div_iff₀ hp).1 hx
  have hl : ℓ x ≤ ‖ℓ‖ * ‖x‖ := (le_abs_self _).trans (ℓ.le_opNorm x)
  nlinarith

/-- A continuous superlinear function attains every minimum after a linear tilt. -/
theorem exists_isMinOn_sub_of_superlinear (hc : Continuous h)
    (hh : Tendsto (fun x => h x / ‖x‖) (cocompact E) atTop) (ℓ : E →L[ℝ] ℝ) :
    ∃ x, IsMinOn (fun z => h z - ℓ z) univ x := by
  obtain ⟨x, hx⟩ := (hc.sub ℓ.continuous).exists_forall_le
    (tendsto_sub_atTop_of_superlinear hh ℓ)
  exact ⟨x, fun z _ => hx z⟩

/-- A strictly convex continuous superlinear function has a unique tilted minimizer. -/
theorem existsUnique_isMinOn_sub_of_superlinear (hc : Continuous h)
    (hs : StrictConvexOn ℝ univ h)
    (hh : Tendsto (fun x => h x / ‖x‖) (cocompact E) atTop) (ℓ : E →L[ℝ] ℝ) :
    ∃! x, IsMinOn (fun z => h z - ℓ z) univ x := by
  obtain ⟨x, hx⟩ := exists_isMinOn_sub_of_superlinear hc hh ℓ
  exact ⟨x, hx, fun y hy =>
    (hs.sub_concaveOn (ℓ.toLinearMap.concaveOn convex_univ)).eq_of_isMinOn hy hx
      (mem_univ _) (mem_univ _)⟩

end Normed

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
  {h : E → ℝ}

/-- The conjugate supremum of a continuous superlinear function is attained and finite. -/
theorem exists_fenchelConjugate_eq_of_superlinear (hc : Continuous h)
    (hh : Tendsto (fun x => h x / ‖x‖) (cocompact E) atTop) (y : E) :
    ∃ x, fenchelConjugate (innerₗ E) (fun z => (h z : EReal)) y =
      ((inner ℝ x y - h x : ℝ) : EReal) := by
  obtain ⟨x, hx⟩ := exists_isMinOn_sub_of_superlinear hc hh
    (InnerProductSpace.toDual ℝ E y)
  have hsub : y ∈ subdifferential (innerₗ E) (fun z => (h z : EReal)) x := by
    apply (mem_subdifferential_coe_iff_isMinOn_sub (innerₗ E) h).2
    simpa only [InnerProductSpace.toDual_apply_apply, real_inner_comm, innerₗ_apply_apply]
      using hx
  exact ⟨x, by simpa only [innerₗ_apply_apply, ← EReal.coe_sub] using
    fenchelConjugate_eq_of_mem_subdifferential (innerₗ E) hsub⟩

end InnerProduct

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {h : E → ℝ} {T : E → E}

/-- A selection of the tilted minimizers of a strictly convex function is
continuous, provided a minimizer exists for every tilt. -/
theorem continuous_of_isMinOn_sub_inner (hs : StrictConvexOn ℝ univ h)
    (hT : ∀ y, IsMinOn (fun z => h z - inner ℝ z y) univ (T y)) : Continuous T := by
  have hc : Continuous h := continuousOn_univ.1 (hs.convexOn.continuousOn isOpen_univ)
  let g := fenchelConjugate (innerₗ E) (fun z => (h z : EReal))
  have hprimal : ∀ y, y ∈ subdifferential (innerₗ E) (fun z => (h z : EReal)) (T y) :=
    fun y => (mem_subdifferential_coe_iff_isMinOn_sub (innerₗ E) h).2 (hT y)
  have hsub : ∀ y, T y ∈ subdifferential (innerₗ E) g y := fun y => by
    simpa only [flip_innerₗ] using
      mem_subdifferential_fenchelConjugate_of_mem_subdifferential (innerₗ E)
        (hprimal y)
  have hbot : ∀ y, g y ≠ ⊥ := fun y => ne_bot_of_mem_subdifferential _ (hsub y)
  have htop : ∀ y, g y ≠ ⊤ := fun y => ne_top_of_mem_subdifferential _ (hsub y)
  have hdom : interior {y | g y ≠ ⊤} = univ := by simp [htop]
  apply continuous_iff_continuousAt.2
  intro y
  obtain ⟨R, hR⟩ := exists_norm_le_of_mem_subdifferential
    (convex_epigraph_fenchelConjugate (innerₗ E) _) hbot
    (isCompact_closedBall y 1) (by simpa only [g] using
      (hdom.symm ▸ subset_univ (closedBall y 1)))
  refine (isCompact_closedBall (0 : E) R).tendsto_nhds_of_unique_mapClusterPt
    (eventually_of_mem (closedBall_mem_nhds y zero_lt_one) fun z hz =>
      mem_closedBall_zero_iff.2 (hR z hz (T z) (hsub z))) ?_
  intro x _ hx
  obtain ⟨u, hTu, hu⟩ := hx.exists_seq_tendsto
  have hmin : IsMinOn (fun z => h z - inner ℝ z y) univ x := by
    rw [isMinOn_iff]
    intro z _
    exact le_of_tendsto_of_tendsto
      ((hc.continuousAt.tendsto.comp hTu).sub (hTu.inner hu))
      (tendsto_const_nhds.sub (tendsto_const_nhds.inner hu))
      (Eventually.of_forall fun n => isMinOn_iff.1 (hT (u n)) z (mem_univ z))
  exact (hs.sub_concaveOn (((innerₗ E).flip y).concaveOn convex_univ)).eq_of_isMinOn
    hmin (hT y) (mem_univ _) (mem_univ _)

/-- The conjugate of a strictly convex superlinear function is differentiable
everywhere. Its gradient is the continuous, unique maximizer of the conjugate supremum. -/
theorem exists_continuous_hasGradientAt_fenchelConjugate_of_superlinear
    (hs : StrictConvexOn ℝ univ h)
    (hh : Tendsto (fun x => h x / ‖x‖) (cocompact E) atTop) :
    ∃ T : E → E, Continuous T ∧
      ∀ y, HasGradientAt
          (fun z => (fenchelConjugate (innerₗ E) (fun x => (h x : EReal)) z).toReal)
          (T y) y ∧
        ∀ x, (y ∈ subdifferential (innerₗ E) (fun z => (h z : EReal)) x ↔ x = T y) := by
  have hc : Continuous h := continuousOn_univ.1 (hs.convexOn.continuousOn isOpen_univ)
  have hex : ∀ y, ∃ x, IsMinOn (fun z => h z - inner ℝ z y) univ x := fun y => by
    simpa only [InnerProductSpace.toDual_apply_apply, real_inner_comm] using
      exists_isMinOn_sub_of_superlinear hc hh (InnerProductSpace.toDual ℝ E y)
  choose T hT using hex
  have hcont := continuous_of_isMinOn_sub_inner hs hT
  have hsub : ∀ y, y ∈ subdifferential (innerₗ E) (fun z => (h z : EReal)) (T y) :=
    fun y => (mem_subdifferential_coe_iff_isMinOn_sub (innerₗ E) h).2 (hT y)
  refine ⟨T, hcont, fun y => ⟨?_, fun x => ?_⟩⟩
  · apply hasGradientAt_toReal_of_continuousAt_subgradient hcont.continuousAt
    exact Eventually.of_forall fun z => by
      simpa only [flip_innerₗ] using
        mem_subdifferential_fenchelConjugate_of_mem_subdifferential (innerₗ E) (hsub z)
  · constructor
    · intro hx
      have hmin : IsMinOn (fun z => h z - inner ℝ z y) univ x :=
        (mem_subdifferential_coe_iff_isMinOn_sub (innerₗ E) h).1 hx
      exact (hs.sub_concaveOn (((innerₗ E).flip y).concaveOn convex_univ)).eq_of_isMinOn
        hmin (hT y) (mem_univ _) (mem_univ _)
    · rintro rfl
      exact hsub y

/-- The real representative of the conjugate of a strictly convex superlinear
function is continuously differentiable. -/
theorem contDiff_fenchelConjugate_toReal_of_superlinear
    (hs : StrictConvexOn ℝ univ h)
    (hh : Tendsto (fun x => h x / ‖x‖) (cocompact E) atTop) :
    ContDiff ℝ 1
      (fun y => (fenchelConjugate (innerₗ E) (fun x => (h x : EReal)) y).toReal) := by
  obtain ⟨T, hT, hgrad⟩ := exists_continuous_hasGradientAt_fenchelConjugate_of_superlinear hs hh
  exact contDiff_one_iff_hasFDerivAt.2 ⟨fun y => InnerProductSpace.toDual ℝ E (T y),
    (InnerProductSpace.toDual ℝ E).continuous.comp hT,
    fun y => hasGradientAt_iff_hasFDerivAt.1 (hgrad y).1⟩

/-- For a strictly convex superlinear cost, the gradient of its conjugate is
the inverse of its subgradient relation. No differentiability of the cost is assumed. -/
theorem mem_subdifferential_iff_eq_gradient_fenchelConjugate_of_superlinear
    (hs : StrictConvexOn ℝ univ h)
    (hh : Tendsto (fun x => h x / ‖x‖) (cocompact E) atTop) (x y : E) :
    y ∈ subdifferential (innerₗ E) (fun z => (h z : EReal)) x ↔
      x = gradient
        (fun z => (fenchelConjugate (innerₗ E) (fun w => (h w : EReal)) z).toReal) y := by
  obtain ⟨T, _, hgrad⟩ := exists_continuous_hasGradientAt_fenchelConjugate_of_superlinear hs hh
  rw [(hgrad y).1.gradient]
  exact (hgrad y).2 x

end FiniteDimensional

end TauCeti
