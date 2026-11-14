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
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Topology.Algebra.Module.PerfectSpace
import TauCeti.Analysis.Complex.Hartogs
import TauCeti.Geometry.Manifold.ChartedSpace
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.ContMDiff.Analytic
import TauCeti.Topology.Perfect

/-!
# Hartogs' extension theorem on complex manifolds

On a boundaryless complex manifold of complex dimension at least two, holomorphic maps into a
complete complex normed space have no isolated singularities: a map holomorphic on a punctured
neighbourhood of a point `p` has a limit at `p` and extends analytically (hence holomorphically)
across `p`, with no boundedness, Hausdorffness, or second-countability hypothesis on the manifold.

Reading a map in the preferred extended chart at `p` reduces the local removable singularity
statement to `TauCeti.exists_analyticAt_and_eventuallyEq_nhdsNE` on the model space `E`, via the
coordinate characterizations `TauCeti.contMDiffAt_omega_iff_analyticAt` and
`TauCeti.contMDiffAt_iff_eventually_mdifferentiableAt`. Patching pointwise punctured limits then
extends holomorphic maps across arbitrary discrete subsets that are closed in an open set `U`, in
particular across finite sets and single points (using `I.t1Space M`).

## Main results

* `TauCeti.exists_contMDiffAt_omega_and_eventuallyEq_nhdsNE`,
  `TauCeti.tendsto_limUnder_of_eventually_mdifferentiableAt`,
  `TauCeti.contMDiffAt_omega_update_limUnder_of_eventually_mdifferentiableAt`: **local Hartogs
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
* `TauCeti.not_exists_mdifferentiable_and_eqOn_inv_compl_zero`: in dimension one, `z ↦ z⁻¹` on
  `{0}ᶜ ⊆ ℂ` has no globally holomorphic extension.

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
  have hI : range I = univ := ModelWithCorners.Boundaryless.range_eq_univ
  have H₁ : 𝓝[range I] (e p) = 𝓝 (e p) := by rw [hI, nhdsWithin_univ]
  have H₂ : map e.symm (𝓝 (e p)) = 𝓝 p := by
    rw [← map_extChartAt_symm_nhdsWithin_range (I := I) p, H₁]
  have htgt : e.target ∈ 𝓝 (e p) := H₁ ▸ extChartAt_target_mem_nhdsWithin p
  have hd : ∀ᶠ z in 𝓝[≠] (e p), DifferentiableAt ℂ (f ∘ e.symm) z := by
    filter_upwards [nhdsWithin_le_nhds htgt,
      nhdsWithin_le_nhds (Tendsto.eventually H₂.le (eventually_nhdsWithin_iff.1 hf)),
      self_mem_nhdsWithin] with z hzt hfz hzne
    have hne : e.symm z ≠ p := fun h ↦
      mem_compl_singleton_iff.1 hzne ((e.right_inv hzt).symm.trans (congrArg e h))
    have hmd : MDifferentiableAt I 𝓘(ℂ, F) f (e.symm z) := hfz (mem_compl_singleton_iff.2 hne)
    have hys : e.symm z ∈ (chartAt H p).source := by
      rw [← extChartAt_source I p]
      exact e.map_target hzt
    have hfy : f (e.symm z) ∈ (chartAt F (0 : F)).source := mem_univ _
    rw [mdifferentiableAt_iff_of_mem_source hys hfy, hI, differentiableWithinAt_univ,
      e.right_inv hzt] at hmd
    exact hmd.2
  obtain ⟨G, hG_an, hG_eq⟩ := exists_analyticAt_and_eventuallyEq_nhdsNE hE hd
  refine ⟨G ∘ e, contMDiffAt_omega_iff_analyticAt.2 (hG_an.congr ?_), ?_⟩
  · filter_upwards [htgt] with z hzt
    exact (congrArg G (e.right_inv hzt)).symm
  · filter_upwards [nhdsWithin_le_nhds (extChartAt_source_mem_nhds (I := I) p),
      nhdsWithin_le_nhds
        ((continuousAt_extChartAt (I := I) p).eventually (eventuallyEq_nhdsWithin_iff.1 hG_eq)),
      self_mem_nhdsWithin] with x hxs hGx hxne
    have hex_ne : e x ≠ e p := fun h ↦
      mem_compl_singleton_iff.1 hxne (e.injOn hxs (mem_extChartAt_source p) h)
    calc
      G (e x) = f (e.symm (e x)) := hGx (mem_compl_singleton_iff.2 hex_ne)
      _ = f x := congrArg f (e.left_inv hxs)

/-- On a boundaryless complex manifold of dimension at least two, a map into a complete complex
normed space that is holomorphic on a punctured neighbourhood of `p` automatically has a limit at
`p`. -/
theorem tendsto_limUnder_of_eventually_mdifferentiableAt (hE : 2 ≤ Module.finrank ℂ E) {f : M → F}
    {p : M} (hf : ∀ᶠ x in 𝓝[≠] p, MDifferentiableAt I 𝓘(ℂ, F) f x) :
    Tendsto f (𝓝[≠] p) (𝓝 (limUnder (𝓝[≠] p) f)) := by
  obtain ⟨g, hg, hgf⟩ := exists_contMDiffAt_omega_and_eventuallyEq_nhdsNE hE hf
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank ℂ E)
  have : PerfectSpace E := perfectSpace_of_module ℂ E
  have : PerfectSpace H := I.toHomeomorph.symm.perfectSpace
  have : PerfectSpace M := ChartedSpace.perfectSpace (H := H)
  have hlim : Tendsto f (𝓝[≠] p) (𝓝 (g p)) :=
    (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hgf
  rwa [hlim.limUnder_eq]

/-- On a boundaryless complex manifold of dimension at least two, updating `f` at `p` by its
punctured limit produces a map `C^ω` at `p`, with no boundedness hypothesis. -/
theorem contMDiffAt_omega_update_limUnder_of_eventually_mdifferentiableAt [DecidableEq M]
    (hE : 2 ≤ Module.finrank ℂ E) {f : M → F} {p : M}
    (hf : ∀ᶠ x in 𝓝[≠] p, MDifferentiableAt I 𝓘(ℂ, F) f x) :
    ContMDiffAt I 𝓘(ℂ, F) ω (update f p (limUnder (𝓝[≠] p) f)) p := by
  obtain ⟨g, hg, hgf⟩ := exists_contMDiffAt_omega_and_eventuallyEq_nhdsNE hE hf
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank ℂ E)
  have : PerfectSpace E := perfectSpace_of_module ℂ E
  have : PerfectSpace H := I.toHomeomorph.symm.perfectSpace
  have : PerfectSpace M := ChartedSpace.perfectSpace (H := H)
  have hlim : Tendsto f (𝓝[≠] p) (𝓝 (g p)) :=
    (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hgf
  refine hg.congr_of_eventuallyEq ?_
  rw [eventuallyEq_nhdsWithin_iff] at hgf
  filter_upwards [hgf] with x hx
  rcases eq_or_ne x p with rfl | hne
  · simp [hlim.limUnder_eq]
  · simp [hne, (hx hne).symm]

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
  · obtain ⟨W, hW_open, hW_eq⟩ := isDiscrete_iff_forall_mem_exists_isOpen.1 hS x ⟨hx, hxS⟩
    have hxW : x ∈ W := (hW_eq.symm ▸ mem_singleton x : x ∈ W ∩ (U ∩ S)).1
    have hUW : ∀ y ∈ (U ∩ W) \ {x}, y ∈ U \ S := by
      rintro y ⟨⟨hyU, hyW⟩, hyx⟩
      refine ⟨hyU, fun hyS ↦ hyx ?_⟩
      have : y ∈ W ∩ (U ∩ S) := ⟨hyW, hyU, hyS⟩
      rwa [hW_eq, mem_singleton_iff] at this
    have hdiff_nhds : ∀ᶠ y in 𝓝[≠] x, MDifferentiableAt I 𝓘(ℂ, F) f y := by
      filter_upwards [nhdsWithin_le_nhds ((hU.inter hW_open).mem_nhds ⟨hx, hxW⟩),
        self_mem_nhdsWithin] with y hyU hyx
      exact (hf y (hUW y ⟨hyU, hyx⟩)).mdifferentiableAt (hUS.mem_nhds (hUW y ⟨hyU, hyx⟩))
    have hupd := contMDiffAt_omega_update_limUnder_of_eventually_mdifferentiableAt hE hdiff_nhds
    refine ((hupd.congr_of_eventuallyEq ?_).mdifferentiableAt (by simp)).mdifferentiableWithinAt
    filter_upwards [(hU.inter hW_open).mem_nhds ⟨hx, hxW⟩] with y hy
    rcases eq_or_ne y x with rfl | hyx
    · simp [g, hx, hxS]
    · rw [update_of_ne hyx, hgf (hUW y ⟨hy, hyx⟩)]
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
  have hfreq := frequently_nhdsNE_eq_zero_of_analyticAt hE han h0
  set e := extChartAt I p
  have hI : range I = univ := ModelWithCorners.Boundaryless.range_eq_univ
  have H₁ : 𝓝[range I] (e p) = 𝓝 (e p) := by rw [hI, nhdsWithin_univ]
  have htgt : e.target ∈ 𝓝 (e p) := H₁ ▸ extChartAt_target_mem_nhdsWithin p
  have hsymm_nhds : Tendsto e.symm (𝓝 (e p)) (𝓝 p) := by
    have := (continuousAt_extChartAt_symm (I := I) p).tendsto
    rwa [extChartAt_to_inv] at this
  have hsymm_ne : Tendsto e.symm (𝓝[≠] (e p)) (𝓝[≠] p) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within e.symm
      (hsymm_nhds.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [nhdsWithin_le_nhds htgt, self_mem_nhdsWithin] with z hzt hzne
    exact mem_compl_singleton_iff.2 fun h ↦
      mem_compl_singleton_iff.1 hzne ((e.right_inv hzt).symm.trans (congrArg e h))
  by_contra hne
  rw [Filter.not_frequently] at hne
  exact hfreq (hsymm_ne.eventually hne)

end Manifold

/-- In complex dimension one, `z ↦ z⁻¹` on `{0}ᶜ ⊆ ℂ` admits no globally holomorphic extension in
the manifold sense either. -/
theorem not_exists_mdifferentiable_and_eqOn_inv_compl_zero :
    ¬ ∃ g : ℂ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g ∧ EqOn g Inv.inv {(0 : ℂ)}ᶜ := by
  rintro ⟨g, hg, hgf⟩
  exact not_exists_differentiable_and_eqOn_inv_compl_zero
    ⟨g, fun z ↦ mdifferentiableAt_iff_differentiableAt.1 (hg z), hgf⟩

end TauCeti
