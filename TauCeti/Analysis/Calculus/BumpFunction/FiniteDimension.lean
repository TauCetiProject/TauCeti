/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Extending finite-dimensional smooth germs

A function smooth on an open set has a globally smooth, compactly supported representative
which agrees with it near a prescribed compact subset, has topological support in that open set,
and vanishes wherever the original function does. This allows local smooth fields to be used in
global integral identities, and lets cut-off vector fields keep the rest points of the original.

A function which is smooth, of finite or infinite order, on a neighbourhood of a point of a
finite-dimensional real normed space agrees near that point with a globally smooth function of
the same order. A smooth bump function performs the extension while preserving the original
function near the base point. Since the bump is compactly supported, so is the representative,
and a representative of order at least one is moreover globally Lipschitz.

These general calculus lemmas are used by the parameter-dependent ODE construction for the
Lie-group exponential, and by the construction of a local flow out of the global solution of a
globally Lipschitz field.
-/

public section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A function smooth on an open set has a globally smooth, compactly supported representative
agreeing with it near every point of any prescribed compact subset of that set. The representative
vanishes wherever the function does. -/
theorem ContDiffOn.exists_contDiff_eventuallyEq_on_isCompact [FiniteDimensional ℝ E]
    {n : ℕ∞} {f : E → F} {K U : Set E} (hf : ContDiffOn ℝ n f U)
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ g : E → F, ContDiff ℝ n g ∧ HasCompactSupport g ∧ tsupport g ⊆ U ∧
      Function.support g ⊆ Function.support f ∧ ∀ x ∈ K, g =ᶠ[nhds x] f := by
  obtain ⟨ψ, hψ, -, hψone, hψcpt, hψsupp⟩ := hK.exists_contDiff_cutoff_eventuallyEq_one hU hKU
  have hg : ContDiff ℝ n (fun x ↦ ψ x • f x) := by
    apply ContMDiff.contDiff
    refine contMDiff_of_tsupport fun x hx ↦ ?_
    have hxU : x ∈ U := hψsupp (tsupport_smul_subset_left ψ f hx)
    exact ((hψ.of_le (by simp)).contDiffAt.smul
      ((hf x hxU).contDiffAt (hU.mem_nhds hxU))).contMDiffAt
  refine ⟨fun x ↦ ψ x • f x, hg, hψcpt.smul_right,
    (tsupport_smul_subset_left ψ f).trans hψsupp, Function.support_smul_subset_right ψ f, ?_⟩
  intro x hx
  filter_upwards [hψone x hx] with y hy
  simp only [hy, one_smul]

/-- A function which is smooth on a neighbourhood of a point of a finite-dimensional real normed
space agrees near that point with a compactly supported globally smooth function of the same
order. -/
theorem ContDiffOn.exists_contDiff_eventuallyEq_of_finiteDimensional
    [FiniteDimensional ℝ E] {n : ℕ∞} {f : E → F} {x : E} {s : Set E}
    (hfs : ContDiffOn ℝ n f s) (hs : s ∈ nhds x) :
    ∃ g : E → F, ContDiff ℝ n g ∧ HasCompactSupport g ∧ g =ᶠ[nhds x] f := by
  obtain ⟨U, hUs, hU, hxU⟩ := mem_nhds_iff.mp hs
  obtain ⟨g, hg, hgc, -, -, hgf⟩ :=
    (hfs.mono hUs).exists_contDiff_eventuallyEq_on_isCompact isCompact_singleton hU
      (Set.singleton_subset_iff.mpr hxU)
  exact ⟨g, hg, hgc, hgf x (Set.mem_singleton x)⟩

/-- A finite-order smooth germ on a finite-dimensional real normed space has a compactly supported
globally smooth representative of the same order. -/
theorem ContDiffAt.exists_contDiff_eventuallyEq_of_finiteDimensional
    [FiniteDimensional ℝ E] (n : ℕ) {f : E → F} {x : E}
    (hf : ContDiffAt ℝ n f x) :
    ∃ g : E → F, ContDiff ℝ n g ∧ HasCompactSupport g ∧ g =ᶠ[nhds x] f :=
  let ⟨s, hs, hfs⟩ := hf.contDiffOn le_rfl (by simp)
  hfs.exists_contDiff_eventuallyEq_of_finiteDimensional hs

/-- A function which is smooth of order at least one on a neighbourhood of a point of a
finite-dimensional real normed space agrees near that point with a globally smooth **and globally
Lipschitz** function of the same order: the compactly supported representative above has a bounded
derivative. -/
theorem ContDiffOn.exists_lipschitzWith_contDiff_eventuallyEq_of_finiteDimensional
    [FiniteDimensional ℝ E] {n : ℕ∞} {f : E → F} {x : E} {s : Set E}
    (hf : ContDiffOn ℝ (n + 1) f s) (hs : s ∈ nhds x) :
    ∃ (g : E → F) (K : NNReal), ContDiff ℝ (n + 1) g ∧ LipschitzWith K g ∧ g =ᶠ[nhds x] f := by
  obtain ⟨g, hg, hgsupp, hgf⟩ := hf.exists_contDiff_eventuallyEq_of_finiteDimensional hs
  obtain ⟨C, hC⟩ := hg.lipschitzWith_of_hasCompactSupport hgsupp (by simp)
  exact ⟨g, C, hg, hC, hgf⟩
