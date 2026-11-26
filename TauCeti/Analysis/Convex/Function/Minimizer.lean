/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Strong
public import Mathlib.Topology.Semicontinuity.Defs

import TauCeti.Analysis.Convex.Function.LowerBound
import TauCeti.Analysis.Convex.Function.Uniform
import TauCeti.Topology.MetricSpace.Pseudo.Cauchy
import TauCeti.Topology.Order.IsLUB
import TauCeti.Topology.Semicontinuity.Sequences

/-!
# Minimizers of uniformly and strongly convex functions

A lower semicontinuous strongly convex function with positive modulus attains its
minimum uniquely on a nonempty complete set.

The Cauchy and attainment arguments also apply to bounded-below uniformly convex
functions whose modulus is positive at every positive radius.
They use the same midpoint estimate as the resolvent proof
`TauCeti.moreauYosidaResolvent_nonempty_of_convexAlong`. See Ambrosio, Gigli and
Savaré, *Gradient Flows in Metric Spaces and in the Space of Probability Measures*,
2nd ed., Section 2.4, Lemma 4.1.1 and Theorem 4.1.2.
-/

public section

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {s : Set E} {f : E → ℝ} {μ : ℝ} {x y : E}

/-- A sequence in the domain whose objective values tend to a lower bound on that
domain is Cauchy if the uniform modulus is positive at every positive radius. -/
theorem UniformConvexOn.cauchySeq_of_tendsto_comp {φ : ℝ → ℝ} (hf : UniformConvexOn s φ f)
    (hφ : ∀ r > 0, 0 < φ r)
    {ι : Type*} [Nonempty ι] [SemilatticeSup ι]
    {a : ℝ} (hlower : ∀ z ∈ s, a ≤ f z) {u : ι → E} (hu : ∀ i, u i ∈ s)
    (hlim : Tendsto (f ∘ u) atTop (𝓝 a)) : CauchySeq u := by
  refine TauCeti.cauchySeq_of_le_max_sub (fun ε hε ↦ ?_) hlim
  refine ⟨φ ε / 4, by positivity [hφ ε hε], fun i j hd ↦ ?_⟩
  have hnorm : 0 < ‖u i - u j‖ := by
    rw [← dist_eq_norm]
    exact hε.trans_le hd
  exact hf.div_four_le_max_sub hlower (hu i) (hu j) (hφ _ hnorm).le hε hd

/-- A bounded-below uniformly convex function attains its minimum uniquely on a nonempty
complete domain if it is lower semicontinuous there and its modulus is positive at every
positive radius. -/
theorem UniformConvexOn.existsUnique_isMinOn_of_bddBelow {φ : ℝ → ℝ} (hf : UniformConvexOn s φ f)
    (hφ : ∀ r > 0, 0 < φ r)
    (hs : IsComplete s) (hne : s.Nonempty) (hlsc : LowerSemicontinuousOn f s)
    (hbdd : BddBelow (f '' s)) : ∃! x, x ∈ s ∧ IsMinOn f s x := by
  obtain ⟨u, hu, -, hulim⟩ := TauCeti.exists_seq_forall_mem_and_tendsto_sInf hne hbdd
  have hlower : ∀ z ∈ s, sInf (f '' s) ≤ f z := fun z hz ↦ csInf_le hbdd ⟨z, hz, rfl⟩
  have hcauchy := hf.cauchySeq_of_tendsto_comp hφ hlower hu hulim
  obtain ⟨x, hx, hux⟩ := cauchySeq_tendsto_of_isComplete hs hu hcauchy
  have hmin : IsMinOn f s x :=
    hlsc.seqLowerSemicontinuousOn.isMinOn_of_tendsto hx hu hux
      (fun v hv c hc ↦ hulim.eventually (gt_mem_nhds ((hlower v hv).trans_lt hc)))
  -- Mathlib's strictness lemma asks for positivity at every nonzero real argument.
  have hf' : UniformConvexOn s (fun r ↦ φ |r|) f :=
    ⟨hf.1, fun _ hx _ hy _ _ ha hb hab ↦ by
      simpa only [abs_norm] using hf.2 hx hy ha hb hab⟩
  have hstrict := hf'.strictConvexOn (fun r hr ↦ hφ |r| (abs_pos.mpr hr))
  exact ⟨x, ⟨hx, hmin⟩, fun y hy ↦ hstrict.eq_of_isMinOn hy.2 hmin hy.1 hx⟩

/-- A lower semicontinuous strongly convex function with positive modulus on a nonempty
complete set has a unique constrained minimizer. -/
theorem StrongConvexOn.existsUnique_isMinOn (hf : StrongConvexOn s μ f) (hμ : 0 < μ)
    (hs : IsComplete s) (hne : s.Nonempty) (hlsc : LowerSemicontinuousOn f s) :
    ∃! x, x ∈ s ∧ IsMinOn f s x := by
  have hbdd : BddBelow (f '' s) := by
    obtain ⟨z, hz⟩ := hne
    have hlow : ∀ᶠ y in 𝓝[s] z, f z - 1 ≤ f y :=
      ((lowerSemicontinuousWithinAt_iff.mp (hlsc z hz)) (f z - 1) (by linarith)).mono
        fun _ hy ↦ hy.le
    exact hf.bddBelow_image_of_eventually_le hμ hz hlow
  have hmod : ∀ r > (0 : ℝ), 0 < μ / 2 * r ^ 2 := by
    intro r hr
    positivity
  exact UniformConvexOn.existsUnique_isMinOn_of_bddBelow hf hmod hs hne hlsc hbdd
