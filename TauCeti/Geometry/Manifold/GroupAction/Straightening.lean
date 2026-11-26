/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import TauCeti.Geometry.Manifold.GroupAction.Linearization

import TauCeti.Analysis.Calculus.FDeriv.Comp
import TauCeti.Analysis.Calculus.GroupAction.Submersion
import TauCeti.Geometry.Manifold.MFDeriv.Submersion

/-!
# Equivariant straightened charts

Let a finite group `G` act by `C^n` maps, `1 ≤ n`, on a manifold `M` without boundary, modelled
on a real Banach space, and let `x` be a common fixed point. Finitely many locally invariant
functions `ρ i`, vanishing at `x`, `C¹` at `x` and with linearly independent differentials at `x`,
are the linear coordinates of a chart at `x` in which the action is linear
(`TauCeti.exists_equivariant_straightened_chart`). Such a chart is `C¹` in both directions.

The chart composes smooth Bochner linearization (`TauCeti.exists_equivariant_contMDiff_chart`)
with equivariant straightening of the defining functions read in the linear chart
(`ContRepresentation.exists_equivariant_straightening`).

## Main results

* `TauCeti.exists_equivariant_straightened_chart`: invariant functions vanishing at `x` with
  linearly independent differentials are linear coordinates of a chart at `x` in which the action
  is linear.

## References

* S. Bochner, *Compact groups of differentiable transformations*, Ann. of Math. (2) 46
  (1945), 372–381.
-/

public section

open Set Filter Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M G ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] {n : WithTop ℕ∞} [IsManifold I n M]
  [Group G] [Finite G] [MulAction G M] [Finite ι]

/-- **Equivariant straightened charts.** Let a finite group act by `C^n` maps, `1 ≤ n`, fixing
`x`, and let the functions `ρ i` vanish at `x`, be locally invariant and `C¹` at `x`, with
linearly independent differentials at `x`. Then some chart `χ` centred at `x`, `C¹` in both
directions and with invariant source, makes the action linear through a representation `σ` and
the functions `ρ i` linear coordinates: they are the components of a surjective continuous linear
map `q`, which is invariant under `σ`. -/
theorem exists_equivariant_straightened_chart
    (hsmooth : ∀ g : G, ContMDiff I I n fun y : M ↦ g • y) (hn : 1 ≤ n)
    {x : M} (hx : ∀ g : G, g • x = x) {ρ : ι → M → ℝ} (h0 : ∀ i, ρ i x = 0)
    (hρ : ∀ i, ContMDiffAt I 𝓘(ℝ) 1 (ρ i) x)
    (hinv : ∀ i (g : G), ∀ᶠ y in 𝓝 x, ρ i (g • y) = ρ i y)
    (hlin : LinearIndependent ℝ fun i ↦ mvfderiv I (ρ i) x) :
    ∃ (σ : ContRepresentation ℝ G E) (χ : OpenPartialHomeomorph M E) (q : E →L[ℝ] ι → ℝ),
      x ∈ χ.source ∧ χ x = 0 ∧
      ContMDiffOn I 𝓘(ℝ, E) 1 χ χ.source ∧ ContMDiffOn 𝓘(ℝ, E) I 1 χ.symm χ.target ∧
      (∀ g : G, ∀ z ∈ χ.source, g • z ∈ χ.source ∧ χ (g • z) = σ g (χ z)) ∧
      Function.Surjective q ∧ (∀ g : G, q.comp (σ g) = q) ∧
      ∀ z ∈ χ.source, ∀ i, q (χ z) i = ρ i z := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hn0 : n ≠ 0 := (zero_lt_one.trans_le hn).ne'
  -- Linearize the action in a smooth chart `e` centred at `x`.
  obtain ⟨σ, e, hxe, hex, hes, het, he, -⟩ :=
    exists_equivariant_contMDiff_chart (𝕜 := ℝ) hsmooth hn hx
  have h0t : (0 : E) ∈ e.target := hex ▸ e.map_source hxe
  have hsymm0 : e.symm 0 = x := by rw [← hex, e.left_inv hxe]
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I 1 e.symm 0 :=
    (het.contMDiffAt (e.open_target.mem_nhds h0t)).of_le hn
  have hsymmT : Tendsto e.symm (𝓝 0) (𝓝 x) := hsymm0 ▸ e.continuousAt_symm h0t
  have hesmul (g : G) {v : E} (hv : v ∈ e.target) : e.symm (σ g v) = g • e.symm v := by
    obtain ⟨hmem, heq⟩ := he g _ (e.map_target hv)
    rw [← e.left_inv hmem, heq, e.right_inv hv]
  -- The defining functions read in the chart.
  let r : E → ι → ℝ := fun v i ↦ ρ i (e.symm v)
  have hr0 : r 0 = 0 := funext fun i ↦ by simp only [r, hsymm0, h0, Pi.zero_apply]
  have hrC : ContDiffAt ℝ 1 r 0 := contDiffAt_pi.mpr fun i ↦
    contMDiffAt_iff_contDiffAt.mp ((hρ i).comp_of_eq hsymm hsymm0)
  obtain ⟨U, hUsub, hU, h0U⟩ := mem_nhds_iff.mp (hrC.eventually (by simp))
  have hrU : ContDiffOn ℝ 1 r U := fun v hv ↦ (hUsub hv).contDiffWithinAt
  -- Its derivative is surjective, since `e.symm` is a local diffeomorphism at `0`.
  let q : E →L[ℝ] ι → ℝ := fderiv ℝ r 0
  have hd : HasFDerivAt r q 0 := (hrC.differentiableAt one_ne_zero).hasFDerivAt
  have hq : Function.Surjective q := e.surjective_fderiv_pi_comp_symm h0t
    (hsymm0 ▸ (hes.contMDiffAt (e.open_source.mem_nhds hxe)).mdifferentiableAt hn0)
    (hsymm.mdifferentiableAt one_ne_zero) (hsymm0 ▸ hlin)
  -- Local invariance of the defining functions, read in the linear chart.
  have hinvr (g : G) : r ∘ σ g =ᶠ[𝓝 0] r := by
    filter_upwards [e.open_target.mem_nhds h0t,
      hsymmT.eventually (eventually_all.mpr fun i ↦ hinv i g)] with v hv hvinv
    funext i
    simp only [Function.comp_apply, r, hesmul g hv, hvinv i]
  have hqσ (g : G) : q.comp (σ g) = q :=
    hd.comp_eq_of_eventuallyEq (σ g).hasFDerivAt (map_zero _) (hinvr g)
  -- Straighten the defining functions equivariantly, and compose the charts.
  obtain ⟨e', h0e', he'0, -, -, he'C, he'Cs, hqe', -, he's, -⟩ :=
    σ.exists_equivariant_straightening hrU hU h0U le_rfl hr0 hd hq hinvr
  refine ⟨σ, e.trans e', q, ⟨hxe, by simpa [hex] using h0e'⟩, by simp [hex, he'0], ?_, ?_,
    fun g z hz ↦ ?_, hq, hqσ, fun z hz i ↦ ?_⟩
  · rw [OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.trans_source]
    exact he'C.contMDiffOn.comp ((hes.of_le hn).mono inter_subset_left) fun _ hz ↦ hz.2
  · rw [OpenPartialHomeomorph.coe_trans_symm, OpenPartialHomeomorph.trans_target]
    exact (het.of_le hn).comp (he'Cs.contMDiffOn.mono inter_subset_left) fun _ hz ↦ hz.2
  · obtain ⟨hgz, hegz⟩ := he g z hz.1
    obtain ⟨hσz, he'σz⟩ := he's g _ hz.2
    refine ⟨⟨hgz, by simpa [hegz] using hσz⟩, ?_⟩
    simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply, hegz]
    exact he'σz
  · simpa [r, e.left_inv hz.1] using congrFun (hqe' _ hz.2) i

end TauCeti
