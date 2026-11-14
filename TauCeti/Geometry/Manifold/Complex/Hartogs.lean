/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.MFDeriv.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.DiscreteSubset
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Topology.Piecewise
import TauCeti.Analysis.Complex.Hartogs
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.ContMDiff.Analytic
import TauCeti.Geometry.Manifold.ExtChartAt
import TauCeti.Geometry.Manifold.ModelWithCorners.Perfect
import TauCeti.Topology.DiscreteSubset

/-!
# Hartogs' extension theorem on complex manifolds

On a boundaryless complex manifold of complex dimension at least two, holomorphic maps into a
complete complex normed space have no isolated singularities: a map holomorphic on a punctured
neighbourhood of a point `p` has a limit at `p` and extends analytically (hence holomorphically)
across `p`, with no boundedness, Hausdorffness, or second-countability hypothesis on the manifold.

Reading a map in the preferred extended chart at `p` reduces the local removable singularity
statement to `TauCeti.exists_analyticAt_and_eventuallyEq_nhdsNE` on the model space `E`, via
`mdifferentiableWithinAt_extChartAt_symm` and the coordinate characterization
`TauCeti.contMDiffAt_omega_iff_analyticAt`, while the isolated-zeros theorem uses the chart-free
regularity equivalence `TauCeti.contMDiffAt_iff_eventually_mdifferentiableAt`. Patching pointwise
punctured limits then extends holomorphic maps across arbitrary discrete subsets that are closed in
an open set `U`, in particular across finite sets and single points (using `I.t1Space M`).

## Main results

* `TauCeti.exists_contMDiffAt_omega_and_eventuallyEq_nhdsNE`,
  `TauCeti.contMDiffAt_omega_update_limUnder_of_eventually_mdifferentiableAt`,
  `TauCeti.tendsto_limUnder_of_eventually_mdifferentiableAt`: **local Hartogs
  removable singularity** at a point of a complex manifold of dimension at least two.
* `TauCeti.exists_mdifferentiableOn_eqOn_sdiff_of_isDiscrete`,
  `TauCeti.exists_mdifferentiableOn_eqOn_sdiff_of_finite`,
  `TauCeti.exists_mdifferentiableOn_eqOn_sdiff_singleton`: extension of holomorphic maps on `U \ S`
  to `U` across closed discrete, finite, and singleton subsets of an open set `U`.
* `TauCeti.exists_mdifferentiable_eqOn_compl_of_codiscrete`,
  `TauCeti.exists_mdifferentiable_eqOn_compl_singleton`: global holomorphic extension across closed
  discrete sets and single points.
* `TauCeti.frequently_nhdsNE_eq_zero_of_eventually_mdifferentiableAt`: **holomorphic functions on a
  complex manifold of dimension at least two have no isolated zeros.**

## References

* R. C. Gunning, H. Rossi, *Analytic Functions of Several Complex Variables*, Chapter I, §B,
  Theorem 5.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, §2.3, Theorem 2.3.2.
* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter II, §4.
-/

public section

open Filter Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- **Hartogs' local removable singularity theorem on complex manifolds.** On a boundaryless complex
manifold modelled on `E` with `2 ≤ Module.finrank ℂ E`, any map `f : M → F` into a complete complex
normed space that is holomorphic on a punctured neighbourhood of `p` agrees on a punctured
neighbourhood of `p` with a map `C^ω` at `p`. -/
theorem exists_contMDiffAt_omega_and_eventuallyEq_nhdsNE (hE : 2 ≤ Module.finrank ℂ E) {f : M → F}
    {p : M} (hf : ∀ᶠ x in 𝓝[≠] p, MDifferentiableAt I 𝓘(ℂ, F) f x) :
    ∃ g : M → F, ContMDiffAt I 𝓘(ℂ, F) ω g p ∧ g =ᶠ[𝓝[≠] p] f := by
  set e := extChartAt I p
  have htgt : e.target ∈ 𝓝 (e p) := extChartAt_target_mem_nhds p
  have hd : ∀ᶠ z in 𝓝[≠] (e p), DifferentiableAt ℂ (f ∘ e.symm) z := by
    filter_upwards [nhdsWithin_le_nhds htgt,
      (I.tendsto_extChartAt_symm_nhdsNE p).eventually hf] with z hzt hmd
    exact ((hmd.comp_mdifferentiableWithinAt z
      (mdifferentiableWithinAt_extChartAt_symm hzt)).mdifferentiableAt
      (I.range_eq_univ ▸ univ_mem)).differentiableAt
  obtain ⟨G, hG_an, hG_eq⟩ := exists_analyticAt_and_eventuallyEq_nhdsNE hE hd
  refine ⟨G ∘ e, contMDiffAt_omega_iff_analyticAt.2 (hG_an.congr ?_), ?_⟩
  · filter_upwards [htgt] with z hzt
    exact (congrArg G (e.right_inv hzt)).symm
  · exact EventuallyEq.trans ((I.tendsto_extChartAt_nhdsNE p).eventually hG_eq)
      ((comp_extChartAt_symm_comp_extChartAt_eventuallyEq f p).filter_mono nhdsWithin_le_nhds)

/-- On a boundaryless complex manifold of dimension at least two, updating `f` at `p` by its
punctured limit produces a map `C^ω` at `p`, with no boundedness hypothesis. -/
theorem contMDiffAt_omega_update_limUnder_of_eventually_mdifferentiableAt [DecidableEq M]
    (hE : 2 ≤ Module.finrank ℂ E) {f : M → F} {p : M}
    (hf : ∀ᶠ x in 𝓝[≠] p, MDifferentiableAt I 𝓘(ℂ, F) f x) :
    ContMDiffAt I 𝓘(ℂ, F) ω (update f p (limUnder (𝓝[≠] p) f)) p := by
  obtain ⟨g, hg, hgf⟩ := exists_contMDiffAt_omega_and_eventuallyEq_nhdsNE hE hf
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank ℂ E)
  have := I.perfectSpace M
  have hlim : Tendsto f (𝓝[≠] p) (𝓝 (g p)) :=
    (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hgf
  exact hg.congr_of_eventuallyEq (eventuallyEq_nhds_of_eventuallyEq_nhdsNE
    (((Function.update_eventuallyEq f p _).filter_mono inf_le_right).trans hgf.symm)
    (by simp [hlim.limUnder_eq]))

/-- On a boundaryless complex manifold of dimension at least two, a map into a complete complex
normed space that is holomorphic on a punctured neighbourhood of `p` automatically has a limit at
`p`. -/
theorem tendsto_limUnder_of_eventually_mdifferentiableAt (hE : 2 ≤ Module.finrank ℂ E) {f : M → F}
    {p : M} (hf : ∀ᶠ x in 𝓝[≠] p, MDifferentiableAt I 𝓘(ℂ, F) f x) :
    Tendsto f (𝓝[≠] p) (𝓝 (limUnder (𝓝[≠] p) f)) := by
  classical
  exact continuousAt_update_same.1
    (contMDiffAt_omega_update_limUnder_of_eventually_mdifferentiableAt hE hf).continuousAt

/-- **Hartogs' extension theorem across a closed discrete set on a complex manifold.** Let `M` be a
boundaryless complex manifold modelled on `E` with `2 ≤ Module.finrank ℂ E`, `U ⊆ M` an open set,
and `S ⊆ M` a set such that `U \ S` is open and `U ∩ S` is discrete. Every map `f : M → F` into a
complete complex normed space that is holomorphic on `U \ S` extends to a holomorphic map on `U`
(hence `C^ω` on `U` by `MDifferentiableOn.contMDiffOn`). -/
theorem exists_mdifferentiableOn_eqOn_sdiff_of_isDiscrete (hE : 2 ≤ Module.finrank ℂ E) {f : M → F}
    {U S : Set M} (hU : IsOpen U) (hUS : IsOpen (U \ S)) (hS : IsDiscrete (U ∩ S))
    (hf : MDifferentiableOn I 𝓘(ℂ, F) f (U \ S)) :
    ∃ g : M → F, MDifferentiableOn I 𝓘(ℂ, F) g U ∧ EqOn g f (U \ S) := by
  classical
  set g : M → F := fun x ↦ if x ∈ U ∩ S then limUnder (𝓝[≠] x) f else f x
  have hgf : EqOn g f (U \ S) := fun x hx ↦ by
    have hx' : x ∉ U ∩ S := fun h ↦ hx.2 h.2
    simp only [g, hx', ↓reduceIte]
  refine ⟨g, fun x hx ↦ ?_, hgf⟩
  by_cases hxS : x ∈ S
  · have hmem : U \ S ∈ 𝓝[≠] x := hU.sdiff_mem_nhdsNE_of_isDiscrete hS hx hxS
    have hdiff_nhds : ∀ᶠ y in 𝓝[≠] x, MDifferentiableAt I 𝓘(ℂ, F) f y :=
      eventually_of_mem hmem fun y hy ↦ (hf y hy).mdifferentiableAt (hUS.mem_nhds hy)
    have hupd := contMDiffAt_omega_update_limUnder_of_eventually_mdifferentiableAt hE hdiff_nhds
    refine ((hupd.congr_of_eventuallyEq
      (eventuallyEq_nhds_of_eventuallyEq_nhdsNE ?_ (by simp [g, hx, hxS]))).mdifferentiableAt
      (by simp)).mdifferentiableWithinAt
    exact (eventuallyEq_of_mem hmem hgf).trans
      ((Function.update_eventuallyEq f x _).filter_mono inf_le_right).symm
  · refine ((hf x ⟨hx, hxS⟩).mdifferentiableAt (hUS.mem_nhds ⟨hx, hxS⟩)
      |>.congr_of_eventuallyEq ?_).mdifferentiableWithinAt
    filter_upwards [hUS.mem_nhds ⟨hx, hxS⟩] with y hy
    exact hgf hy

/-- **Hartogs' extension theorem across a finite set on a complex manifold.** If
`2 ≤ Module.finrank ℂ E`, `U ⊆ M` is open, and `S ⊆ M` is finite, every map `f : M → F` holomorphic
on `U \ S` extends to a holomorphic map on `U`. No `T₂` assumption on `M` is needed. -/
theorem exists_mdifferentiableOn_eqOn_sdiff_of_finite (hE : 2 ≤ Module.finrank ℂ E) {f : M → F}
    {U S : Set M} (hU : IsOpen U) (hS : S.Finite) (hf : MDifferentiableOn I 𝓘(ℂ, F) f (U \ S)) :
    ∃ g : M → F, MDifferentiableOn I 𝓘(ℂ, F) g U ∧ EqOn g f (U \ S) := by
  have := I.t1Space M
  exact exists_mdifferentiableOn_eqOn_sdiff_of_isDiscrete hE hU (hU.sdiff hS.isClosed)
    (hS.subset inter_subset_right).isDiscrete hf

/-- **Hartogs' extension theorem across a point on a complex manifold.** If
`2 ≤ Module.finrank ℂ E` and `U ⊆ M` is open, every map `f : M → F` holomorphic on `U \ {p}`
extends to a holomorphic map on `U`. -/
theorem exists_mdifferentiableOn_eqOn_sdiff_singleton (hE : 2 ≤ Module.finrank ℂ E) {f : M → F}
    {U : Set M} (hU : IsOpen U) (p : M) (hf : MDifferentiableOn I 𝓘(ℂ, F) f (U \ {p})) :
    ∃ g : M → F, MDifferentiableOn I 𝓘(ℂ, F) g U ∧ EqOn g f (U \ {p}) :=
  exists_mdifferentiableOn_eqOn_sdiff_of_finite hE hU (finite_singleton p) hf

/-- **Global Hartogs extension across a closed discrete set on a complex manifold.** If
`2 ≤ Module.finrank ℂ E` and `Sᶜ ∈ codiscrete M`, every map `f : M → F` holomorphic on `Sᶜ` extends
to a globally holomorphic map on `M`. -/
theorem exists_mdifferentiable_eqOn_compl_of_codiscrete (hE : 2 ≤ Module.finrank ℂ E) {f : M → F}
    {S : Set M} (hS : Sᶜ ∈ codiscrete M) (hf : MDifferentiableOn I 𝓘(ℂ, F) f Sᶜ) :
    ∃ g : M → F, MDifferentiable I 𝓘(ℂ, F) g ∧ EqOn g f Sᶜ := by
  obtain ⟨hS_closed, hS_disc⟩ := compl_mem_codiscrete_iff.1 hS
  have hf' : MDifferentiableOn I 𝓘(ℂ, F) f (univ \ S) := by simpa [compl_eq_univ_sdiff] using hf
  obtain ⟨g, hg, hgf⟩ := exists_mdifferentiableOn_eqOn_sdiff_of_isDiscrete hE isOpen_univ
    (isOpen_univ.sdiff hS_closed) (by simpa using hS_disc) hf'
  exact ⟨g, mdifferentiableOn_univ.1 hg, by simpa [compl_eq_univ_sdiff] using hgf⟩

/-- **Global Hartogs extension across a point on a complex manifold.** If `2 ≤ Module.finrank ℂ E`,
every map `f : M → F` holomorphic on `{p}ᶜ` extends to a globally holomorphic map on `M`. -/
theorem exists_mdifferentiable_eqOn_compl_singleton (hE : 2 ≤ Module.finrank ℂ E) {f : M → F}
    (p : M) (hf : MDifferentiableOn I 𝓘(ℂ, F) f {p}ᶜ) :
    ∃ g : M → F, MDifferentiable I 𝓘(ℂ, F) g ∧ EqOn g f {p}ᶜ := by
  have := I.t1Space M
  exact exists_mdifferentiable_eqOn_compl_of_codiscrete hE
    (finite_singleton p).compl_mem_codiscrete hf

/-- **Holomorphic functions on a complex manifold of dimension at least two have no isolated
zeros.** If `2 ≤ Module.finrank ℂ E`, `f : M → ℂ` is holomorphic near `p`, and `f p = 0`, then `p`
is an accumulation point of `{x | f x = 0}`. -/
theorem frequently_nhdsNE_eq_zero_of_eventually_mdifferentiableAt (hE : 2 ≤ Module.finrank ℂ E)
    {f : M → ℂ} {p : M} (hf : ∀ᶠ x in 𝓝 p, MDifferentiableAt I 𝓘(ℂ) f x) (hfp : f p = 0) :
    ∃ᶠ x in 𝓝[≠] p, f x = 0 := by
  have hcont : ContMDiffAt I 𝓘(ℂ) ω f p :=
    (contMDiffAt_iff_eventually_mdifferentiableAt (n := ω) (by simp)).2 hf
  have han : AnalyticAt ℂ (f ∘ (extChartAt I p).symm) (extChartAt I p p) :=
    contMDiffAt_omega_iff_analyticAt.1 hcont
  have h0 : (f ∘ (extChartAt I p).symm) (extChartAt I p p) = 0 := by
    simpa [Function.comp_apply, extChartAt_to_inv] using hfp
  exact (I.tendsto_extChartAt_symm_nhdsNE p).frequently
    (frequently_nhdsNE_eq_zero_of_analyticAt hE han h0)

end Manifold

end TauCeti
