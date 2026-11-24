/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
public import TauCeti.Geometry.Manifold.VectorField.Prod
import TauCeti.Analysis.Calculus.Deriv.LevelCrossing
import TauCeti.Geometry.Manifold.IntegralCurve.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Curve

/-!
# Integral curves of product vector fields

For vector fields `X` on `M` and `Y` on `N`, a curve in `M × N` is an integral curve of the
product field `TauCeti.Manifold.prodVectorField X Y` exactly when its two components are integral
curves of `X` and of `Y`. So the flow of a product field is the product of the flows, and its
trajectories are the pairs of trajectories of the factors, run with the same time.

For an arbitrary vector field `V` on a product `M × F` with a normed space `F`, the second component
of an integral curve is differentiable, with derivative the second component of `V`
(`IsMIntegralCurve.hasDerivAt_snd`). For `F = ℝ`, if the second component of `V` is positive on a
level `t = c`, an integral curve whose second component runs from below `c` to above `c` crosses
that level exactly once (`IsMIntegralCurve.existsUnique_snd_eq`).

## Main results

* `TauCeti.Manifold.isMIntegralCurveOn_prodVectorField_iff`: integral curves on a set of times.
* `TauCeti.Manifold.isMIntegralCurve_prodVectorField_iff`: global integral curves.
* `IsMIntegralCurve.hasDerivAt_snd`: the derivative of the second component of an integral curve
  in `M × F`.
* `IsMIntegralCurve.existsUnique_snd_eq`: an integral curve in `M × ℝ` crosses a level exactly once
  when the field points upwards there.
-/

public section

open Filter Set Topology
open scoped Manifold

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {X : Π x : M, TangentSpace I x} {Y : Π y : N, TangentSpace J y} {γ : ℝ → M × N}

/-- **Integral curves of a product field** on a set of times are the pairs of integral curves of
the two factors. -/
theorem isMIntegralCurveOn_prodVectorField_iff {s : Set ℝ} :
    IsMIntegralCurveOn γ (prodVectorField X Y) s ↔
      IsMIntegralCurveOn (fun t ↦ (γ t).1) X s ∧ IsMIntegralCurveOn (fun t ↦ (γ t).2) Y s := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨h₁, h₂⟩ t ht ↦ ?_⟩
  · exact h.map_of_mfderiv_eq (f := Prod.fst) (fun _ _ ↦ mdifferentiableAt_fst)
      fun t _ ↦ by rw [mfderiv_fst]; exact prodVectorField_fst X Y (γ t)
  · exact h.map_of_mfderiv_eq (f := Prod.snd) (fun _ _ ↦ mdifferentiableAt_snd)
      fun t _ ↦ by rw [mfderiv_snd]; exact prodVectorField_snd X Y (γ t)
  · refine HasMFDerivWithinAt.prodMk_curve (v := prodVectorField X Y (γ t)) ?_ ?_
    · rw [prodVectorField_fst]
      exact h₁ t ht
    · rw [prodVectorField_snd]
      exact h₂ t ht

/-- **Integral curves of a product field** are the pairs of integral curves of the two factors. -/
theorem isMIntegralCurve_prodVectorField_iff :
    IsMIntegralCurve γ (prodVectorField X Y) ↔
      IsMIntegralCurve (fun t ↦ (γ t).1) X ∧ IsMIntegralCurve (fun t ↦ (γ t).2) Y := by
  simp only [isMIntegralCurve_iff_isMIntegralCurveOn, isMIntegralCurveOn_prodVectorField_iff]

/-- **The second component of an integral curve in `M × F`** is differentiable, with derivative the
second component of the field: for an integral curve `γ` of a vector field `V` on `M × F`,
`(γ s).2` has derivative `(V (γ s)).2` at `s`. -/
theorem _root_.IsMIntegralCurve.hasDerivAt_snd {V : Π z : M × E', TangentSpace (I.prod 𝓘(ℝ, E')) z}
    {γ : ℝ → M × E'} (hγ : IsMIntegralCurve γ V) (s : ℝ) :
    HasDerivAt (fun s ↦ (γ s).2) (V (γ s) : E × E').2 s :=
  hasDerivAt_iff_hasFDerivAt.2 (hasMFDerivAt_iff_hasFDerivAt.1 (hγ s).snd_curve)

/-- **An integral curve crosses a level exactly once.** If the second component of the vector
field `V` on `M × ℝ` is positive on the level `t = c`, then an integral curve of `V` whose second
component tends to `a < c` at `-∞` and to `b > c` at `+∞` meets this level at exactly one time. -/
theorem _root_.IsMIntegralCurve.existsUnique_snd_eq
    {V : Π z : M × ℝ, TangentSpace (I.prod 𝓘(ℝ)) z} {γ : ℝ → M × ℝ} (hγ : IsMIntegralCurve γ V)
    {a b c : ℝ} (hac : a < c) (hcb : c < b) (hV : ∀ x, 0 < (V (x, c) : E × ℝ).2)
    (h₀ : Tendsto (fun s ↦ (γ s).2) atBot (𝓝 a)) (h₁ : Tendsto (fun s ↦ (γ s).2) atTop (𝓝 b)) :
    ∃! s, (γ s).2 = c := by
  have hd := hγ.hasDerivAt_snd
  have hcont : Continuous fun s ↦ (γ s).2 :=
    continuous_iff_continuousAt.2 fun s ↦ (hd s).continuousAt
  -- On the level, the second component of `V`, the derivative of that of `γ`, is positive.
  have hpos : ∀ z : M × ℝ, z.2 = c → 0 < (V z : E × ℝ).2 := by
    rintro ⟨x, t⟩ (rfl : t = c)
    exact hV x
  obtain ⟨s₀, hs₀⟩ := (h₀.eventually (gt_mem_nhds hac)).exists
  obtain ⟨s₁, hs₁⟩ := (h₁.eventually (lt_mem_nhds hcb)).exists
  obtain ⟨s, hs⟩ := intermediate_value_univ s₀ s₁ hcont ⟨hs₀.le, hs₁.le⟩
  refine ⟨s, hs, fun s' hs' ↦ ?_⟩
  -- Two crossings would give a crossing downwards between them.
  have hcross : ∀ {s₁ s₂ : ℝ}, s₁ < s₂ → (γ s₁).2 = c → (γ s₂).2 ≠ c :=
    fun {s₁ s₂} h12 h₁ ↦ (lt_image_of_deriv_pos_boundary hcont.continuousOn
      (fun t _ ht ↦ ⟨hd t, hpos (γ t) ht⟩) h₁.ge ⟨h12, le_rfl⟩).ne'
  rcases lt_trichotomy s' s with h | h | h
  · exact absurd hs (hcross h hs')
  · exact h
  · exact absurd hs' (hcross h hs)

end TauCeti.Manifold
