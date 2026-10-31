/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.BumpFunction
public import TauCeti.Analysis.Calculus.Morse.Generic
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.ManifoldFamily
public import TauCeti.Geometry.Manifold.Morse.Persistence

/-!
# Morse functions are dense

On a boundaryless finite-dimensional Hausdorff manifold `M`, every smooth function can be
approximated, in the weak Whitney topology on `C^∞⟮I, M; 𝓘(ℝ), ℝ⟯`, by smooth functions which are
Morse on a prescribed compact set `K`. On a compact manifold this says that Morse functions are
dense; together with `TauCeti.isOpen_setOf_isMorse` they form an open dense set, and in particular
every compact manifold carries a Morse function. On a compact manifold the weak Whitney topology is
also the strong one, so this is the compact case of the Morse approximation theorem.

The proof is the classical one. Near a point `c`, choose a smooth bump function `β` at `c` and
perturb a smooth function `g` to `y ↦ g y - a (β y • φ y)`, where `φ` is the extended chart at `c`
and `a` is a continuous linear functional. On the open set `W` where `β = 1` inside the chart
source, this is `g - a ∘ φ`, so in coordinates it is a linear perturbation of `g ∘ φ.symm`, and
for a dense set of `a` it has only nondegenerate critical points there
(`TauCeti.dense_setOfPred_hasNondegenerateCriticalPointsOn_sub`). The perturbation is jointly
smooth in `a` and `y`, hence continuous in `a` for the weak Whitney topology
(`ContMDiff.continuous_manifoldWeakWhitney`), so small `a` keep it in any prescribed neighbourhood
of `g`, and, by the openness of nondegeneracy on compact sets
(`TauCeti.eventually_forall_isManifoldNondegenerateCriticalPoint`), keep it Morse on the compact set
where `g` already was. Covering `K` by finitely many such `W` and perturbing one chart at a time
gives a function Morse on all of `K`.

## Main results

* `TauCeti.dense_setOf_isMorseOn`: for a compact set `K`, the smooth functions which are Morse on
  `K` are dense in the weak Whitney topology.
* `TauCeti.dense_setOf_isMorse`: on a compact manifold, **Morse functions are dense**.
* `TauCeti.exists_isMorse`: a compact manifold carries a Morse function.

## References

* M. Hirsch, *Differential Topology*, GTM 33, Springer, 1976, Chapter 6, §1, where Morse
  functions are shown to form a dense open set by local linear perturbations.
* V. Guillemin and A. Pollack, *Differential Topology*, Prentice-Hall, 1974, Chapter 1, §7.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §6, for the existence of Morse functions by embedding the manifold in Euclidean space.
-/

public section

open Filter Set
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M]

section WeakWhitney

open scoped TauCeti.ManifoldWeakWhitney

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]

/-- A smooth function perturbed by the linear functional `a` in the coordinates of the chart at
`c`, cut off by the bump function `β`: the function `y ↦ g y - a (β y • extChartAt I c y)`. -/
private noncomputable def bumpPerturbation {c : M} (β : SmoothBumpFunction I c)
    (g : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) (a : E →L[ℝ] ℝ) : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯ :=
  ⟨fun y ↦ g y - a (β y • extChartAt I c y),
    g.contMDiff.sub (contMDiff_const.clm_apply (β.contMDiff_smul contMDiffOn_extChartAt))⟩

omit [I.Boundaryless] in
private theorem bumpPerturbation_apply {c : M} (β : SmoothBumpFunction I c)
    (g : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) (a : E →L[ℝ] ℝ) (y : M) :
    bumpPerturbation β g a y = g y - a (β y • extChartAt I c y) := (rfl)

omit [I.Boundaryless] in
/-- The bump perturbation depends continuously on the functional, for the weak Whitney
topology. -/
private theorem continuous_bumpPerturbation {c : M} (β : SmoothBumpFunction I c)
    (g : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) : Continuous (bumpPerturbation β g) :=
  ContMDiff.continuous_manifoldWeakWhitney <|
    (g.contMDiff.comp contMDiff_snd).sub (contMDiff_fst.clm_apply
      ((β.contMDiff_smul contMDiffOn_extChartAt).comp contMDiff_snd))

/-- **One chart of the approximation.** Every point `c` has an open neighbourhood `W` such that
a smooth function which is Morse on a compact set `A` can be perturbed, inside any prescribed
weak Whitney neighbourhood, to a smooth function which is Morse on both `A` and `W`. -/
private theorem exists_isOpen_forall_exists_isMorseOn (c : M) :
    ∃ W : Set M, IsOpen W ∧ c ∈ W ∧ ∀ (g : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) (A : Set M), IsCompact A →
      IsMorseOn I g A → ∀ 𝒰 ∈ 𝓝 g, ∃ g' ∈ 𝒰, IsMorseOn I g' A ∧ IsMorseOn I g' W := by
  obtain ⟨β⟩ : Nonempty (SmoothBumpFunction I c) := inferInstance
  set φ := extChartAt I c
  set e := chartAt H c
  -- On `W` the bump function is identically `1`, so the perturbation is `g - a ∘ φ` there.
  set W := e.source ∩ interior {y | β y = 1}
  have hWo : IsOpen W := e.open_source.inter isOpen_interior
  have hWs : W ⊆ e.source := inter_subset_left
  have hβW {y : M} (hy : y ∈ W) : β y = 1 := interior_subset hy.2
  refine ⟨W, hWo, ⟨mem_chart_source H c, mem_interior_iff_mem_nhds.2 β.eventuallyEq_one⟩,
    fun g A hA hgA 𝒰 h𝒰 ↦ ?_⟩
  have he : e ∈ IsManifold.maximalAtlas I 2 M := IsManifold.chart_mem_maximalAtlas c
  have hφe : e.extend I = φ := rfl
  -- The chart image of `W`, an open subset of the chart target.
  set U := φ '' W
  have hUeq : U = φ.target ∩ φ.symm ⁻¹' W :=
    φ.image_eq_target_inter_inv_preimage (by rwa [extChartAt_source])
  have hUo : IsOpen U := hUeq ▸
    (continuousOn_extChartAt_symm c).isOpen_inter_preimage (isOpen_extChartAt_target c) hWo
  have hgU : ContDiffOn ℝ 2 (g ∘ φ.symm) U :=
    ((contMDiffOn_iff_contDiffOn.1 (g.contMDiff.comp_contMDiffOn
      (contMDiffOn_extChartAt_symm c))).of_le (by simp)).mono (hUeq ▸ inter_subset_left)
  -- Small functionals keep the perturbation in `𝒰` and Morse on `A`; a dense set of them makes
  -- its coordinate expression have only nondegenerate critical points on `U`.
  have hnear : ∀ᶠ a in 𝓝 (0 : E →L[ℝ] ℝ), bumpPerturbation β g a ∈ 𝒰 ∧
      IsMorseOn I (bumpPerturbation β g a) A := by
    have h0 : bumpPerturbation β g 0 = g := by ext y; simp [bumpPerturbation_apply]
    have ht := (continuous_bumpPerturbation β g).tendsto 0
    rw [h0] at ht
    rw [isMorseOn_iff_criticalPoints] at hgA
    have hev := eventually_forall_isManifoldNondegenerateCriticalPoint (by simp) hA hgA.2
    filter_upwards [ht h𝒰, ht hev] with a ha𝒰 haA
    exact ⟨ha𝒰, isMorseOn_iff_criticalPoints.2
      ⟨(bumpPerturbation β g a).contMDiff.contMDiffOn, haA⟩⟩
  obtain ⟨a, ⟨ha𝒰, haA⟩, haU⟩ := (hnear.and_frequently (mem_closure_iff_frequently.1
    ((dense_setOfPred_hasNondegenerateCriticalPointsOn_sub hUo hgU) 0))).exists
  refine ⟨_, ha𝒰, haA, (isMorseOn_iff_of_mem_maximalAtlas he
    (fun y _ ↦ (bumpPerturbation β g a).contMDiff y) hWs).2 ?_⟩
  rw [hφe]
  -- On `U` the coordinate expression of the perturbation is `g ∘ φ.symm - a`.
  have hloc {z : E} (hz : z ∈ U) :
      (fun w ↦ (g ∘ φ.symm) w - a w) =ᶠ[𝓝 z] bumpPerturbation β g a ∘ φ.symm := by
    filter_upwards [hUo.mem_nhds hz] with w hw
    rw [hUeq] at hw
    simp only [Function.comp_apply, bumpPerturbation_apply, hβW hw.2, one_smul]
    rw [φ.right_inv hw.1]
  refine hasNondegenerateCriticalPointsOn_iff.2 fun z hz hz₀ ↦ ?_
  exact (hasNondegenerateCriticalPointsOn_iff.1 haU hz (by rwa [(hloc hz).fderiv_eq])
    ).congr_of_eventuallyEq (hloc hz)

/-- **Morse functions on a compact set are dense.** For a compact set `K` of a boundaryless
finite-dimensional Hausdorff manifold, every smooth function is a limit, in the weak Whitney
topology, of smooth functions which are Morse on `K`. -/
theorem dense_setOf_isMorseOn {K : Set M} (hK : IsCompact K) :
    Dense {f : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯ | IsMorseOn I f K} := by
  classical
  choose W hWo hcW hW using exists_isOpen_forall_exists_isMorseOn (I := I) (M := M)
  -- Cover `K` by finitely many compact pieces `L x ⊆ W x`.
  obtain ⟨t, -, hKt⟩ := hK.elim_nhds_subcover W fun x _ ↦ (hWo x).mem_nhds (hcW x)
  obtain ⟨L, hLc, hLW, rfl⟩ := hK.finite_compact_cover t W (fun x _ ↦ hWo x) hKt
  refine dense_iff_inter_open.2 fun 𝒰 h𝒰 ⟨f, hf⟩ ↦ ?_
  -- Perturb one piece at a time, staying in `𝒰`.
  suffices ∀ s : Finset M, ∃ g ∈ 𝒰, IsMorseOn I g (⋃ x ∈ s, L x) from this t
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨f, hf, isMorseOn_iff_criticalPoints.2 ⟨f.contMDiff.contMDiffOn, by simp⟩⟩
  | insert x s _ ih =>
    obtain ⟨g, hg𝒰, hg⟩ := ih
    obtain ⟨g', hg'𝒰, hg'A, hg'W⟩ := hW x g _
      (s.finite_toSet.isCompact_biUnion fun y _ ↦ hLc y) hg 𝒰 (h𝒰.mem_nhds hg𝒰)
    refine ⟨g', hg'𝒰, ?_⟩
    rw [Finset.set_biUnion_insert, isMorseOn_iff_criticalPoints]
    refine ⟨g'.contMDiff.contMDiffOn, fun y hy hyc ↦ hy.elim (fun hy ↦ ?_) fun hy ↦ ?_⟩
    · exact hg'W.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints (hLW x hy) hyc
    · exact hg'A.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints hy hyc

/-- **Morse functions are dense** in the smooth functions on a compact boundaryless
finite-dimensional Hausdorff manifold, for the weak Whitney topology. -/
theorem dense_setOf_isMorse [CompactSpace M] :
    Dense {f : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯ | IsMorse I f} := by
  simpa only [isMorseOn_univ] using dense_setOf_isMorseOn (I := I) isCompact_univ

end WeakWhitney

/-- **Every compact manifold carries a Morse function**: a compact boundaryless
finite-dimensional Hausdorff manifold has a smooth function all of whose critical points are
nondegenerate. -/
theorem exists_isMorse [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [CompactSpace M] :
    ∃ f : M → ℝ, IsMorse I f := by
  open scoped TauCeti.ManifoldWeakWhitney in
  obtain ⟨f, hf⟩ := (dense_setOf_isMorse (I := I) (M := M)).nonempty_iff.2
    ⟨ContMDiffMap.const 0⟩
  exact ⟨f, hf⟩

end TauCeti
