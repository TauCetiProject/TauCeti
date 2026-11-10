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

On a boundaryless finite-dimensional Hausdorff manifold `M`, every `C^n` function, `2 ≤ n ≤ ∞`, can
be approximated, in the weak Whitney topology on `C^n⟮I, M; 𝓘(ℝ), ℝ⟯`, by `C^n` functions all of
whose critical points in a prescribed compact set `K` are nondegenerate. On a compact manifold
these functions form an open dense set, by the openness theorem
`TauCeti.isOpen_setOf_forall_mem_criticalPoints_isManifoldNondegenerateCriticalPoint`, and hence a
residual one. For smooth functions this says that Morse functions are dense; together with
`TauCeti.isOpen_setOf_isMorse` they form an open dense set, and in particular every compact
manifold carries a Morse function. On a compact manifold the weak Whitney topology is also the
strong one, so this is the compact case of the Morse approximation theorem. The finite-order
statement is the one used for genericity in Banach spaces of `C^k` functions: Morse functions in
the sense of `TauCeti.IsMorse` are smooth, so for finite `n` the property is stated directly with
`TauCeti.IsManifoldNondegenerateCriticalPoint`. The bound `n ≥ 2` is needed for the openness, and
the manifold is smooth, so that bump functions and charts are available at every order.

The proof is the classical one. Near a point `c`, choose a smooth bump function `β` at `c` and
perturb a `C^n` function `g` to `y ↦ g y - a (β y • φ y)`, where `φ` is the extended chart at `c`
and `a` is a continuous linear functional. On the open set `W` where `β = 1` inside the chart
source, this is `g - a ∘ φ`, so in coordinates it is a linear perturbation of `g ∘ φ.symm`, and
for a dense set of `a` it has only nondegenerate critical points there
(`TauCeti.dense_setOfPred_hasNondegenerateCriticalPointsOn_sub`, which needs only `C²`). The
perturbation is jointly `C^n` in `a` and `y`, hence continuous in `a` for the weak Whitney topology
(`ContMDiff.continuous_manifoldWeakWhitney`), so small `a` keep it in any prescribed neighbourhood
of `g`, and, by the openness of nondegeneracy on compact sets
(`TauCeti.eventually_forall_isManifoldNondegenerateCriticalPoint`), keep its critical points
nondegenerate on the compact set where those of `g` already were. Covering `K` by finitely many
such `W` and perturbing one chart at a time gives a function whose critical points in all of `K`
are nondegenerate.

## Main results

* `ContMDiffMap.exists_forall_isManifoldNondegenerateCriticalPoint_hasCompactSupport_sub`: make the
  critical points of a `C^n` function in a compact set nondegenerate by a compactly supported
  perturbation inside a prescribed open set, keeping this property on an already treated compact
  set; `ContMDiffMap.exists_isMorseOn_union_hasCompactSupport_sub` is its smooth form.
* `TauCeti.dense_setOf_forall_isManifoldNondegenerateCriticalPoint`: for a compact set `K`, the
  `C^n` functions with only nondegenerate critical points in `K` are dense in the weak Whitney
  topology, and `TauCeti.dense_setOf_isMorseOn` is its smooth form.
* `TauCeti.dense_setOf_forall_mem_criticalPoints_isManifoldNondegenerateCriticalPoint`: on a compact
  manifold, the `C^n` functions with only nondegenerate critical points are dense.
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

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] {n : ℕ∞} [IsManifold I n M]

/-- A `C^n` function perturbed by the linear functional `a` in the coordinates of the chart at
`c`, cut off by the bump function `β`: the function `y ↦ g y - a (β y • extChartAt I c y)`. -/
private noncomputable def bumpPerturbation {c : M} (β : SmoothBumpFunction I c)
    (g : C^n⟮I, M; 𝓘(ℝ), ℝ⟯) (a : E →L[ℝ] ℝ) : C^n⟮I, M; 𝓘(ℝ), ℝ⟯ :=
  ⟨fun y ↦ g y - a (β y • extChartAt I c y),
    g.contMDiff.sub (contMDiff_const.clm_apply
      ((β.contMDiff_smul contMDiffOn_extChartAt).of_le (WithTop.coe_le_coe.2 le_top)))⟩

omit [I.Boundaryless] [IsManifold I n M] in
private theorem bumpPerturbation_apply {c : M} (β : SmoothBumpFunction I c)
    (g : C^n⟮I, M; 𝓘(ℝ), ℝ⟯) (a : E →L[ℝ] ℝ) (y : M) :
    bumpPerturbation β g a y = g y - a (β y • extChartAt I c y) := (rfl)

omit [I.Boundaryless] in
/-- The bump perturbation depends continuously on the functional, for the weak Whitney
topology. -/
private theorem continuous_bumpPerturbation {c : M} (β : SmoothBumpFunction I c)
    (g : C^n⟮I, M; 𝓘(ℝ), ℝ⟯) : Continuous (bumpPerturbation β g) :=
  ContMDiff.continuous_manifoldWeakWhitney <|
    (g.contMDiff.comp contMDiff_snd).sub (contMDiff_fst.clm_apply
      (((β.contMDiff_smul contMDiffOn_extChartAt).of_le (WithTop.coe_le_coe.2 le_top)).comp
        contMDiff_snd))

omit [I.Boundaryless] [IsManifold I n M] in
/-- The difference between the bump perturbation and the function itself is supported in the
support of the bump function. -/
private theorem tsupport_bumpPerturbation_sub_subset {c : M} (β : SmoothBumpFunction I c)
    (g : C^n⟮I, M; 𝓘(ℝ), ℝ⟯) (a : E →L[ℝ] ℝ) :
    tsupport (fun y ↦ bumpPerturbation β g a y - g y) ⊆ tsupport β := by
  have hdiff : (fun y ↦ bumpPerturbation β g a y - g y) =
      (fun y ↦ β y * (-a (extChartAt I c y))) := by
    ext y
    simp only [bumpPerturbation_apply, map_smul, smul_eq_mul]
    ring
  rw [hdiff]
  exact tsupport_mul_subset_left

/-- One local perturbation, with its support confined to a prescribed neighbourhood. -/
private theorem exists_isOpen_forall_exists_isManifoldNondegenerateCriticalPoint (hn : 2 ≤ n)
    (c : M) {U : Set M} (hU : U ∈ 𝓝 c) :
    ∃ W : Set M, IsOpen W ∧ c ∈ W ∧ ∀ (g : C^n⟮I, M; 𝓘(ℝ), ℝ⟯) (A : Set M), IsCompact A →
      (∀ x ∈ A, x ∈ criticalPoints I g → IsManifoldNondegenerateCriticalPoint I g x) →
      ∀ 𝒰 ∈ 𝓝 g, ∃ g' ∈ 𝒰,
        (∀ x ∈ A, x ∈ criticalPoints I g' → IsManifoldNondegenerateCriticalPoint I g' x) ∧
        (∀ x ∈ W, x ∈ criticalPoints I g' → IsManifoldNondegenerateCriticalPoint I g' x) ∧
        HasCompactSupport (fun y ↦ g' y - g y) ∧ tsupport (fun y ↦ g' y - g y) ⊆ U := by
  obtain ⟨β, -, hβU⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) c).mem_iff.mp hU
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
  have he₁ : e ∈ IsManifold.maximalAtlas I 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by norm_num) he
  have hφe : e.extend I = φ := rfl
  -- The chart image of `W`, an open subset of the chart target.
  set U := φ '' W
  have hUeq : U = φ.target ∩ φ.symm ⁻¹' W :=
    φ.image_eq_target_inter_inv_preimage (by rwa [extChartAt_source])
  have hUo : IsOpen U := hUeq ▸
    (continuousOn_extChartAt_symm c).isOpen_inter_preimage (isOpen_extChartAt_target c) hWo
  have hgU : ContDiffOn ℝ 2 (g ∘ φ.symm) U :=
    ((contMDiffOn_iff_contDiffOn.1 (g.contMDiff.comp_contMDiffOn
      (contMDiffOn_extChartAt_symm c))).of_le (WithTop.coe_le_coe.2 hn)).mono
        (hUeq ▸ inter_subset_left)
  -- Small functionals keep the perturbation in `𝒰` and nondegenerate on `A`; a dense set of them
  -- makes its coordinate expression have only nondegenerate critical points on `U`.
  have hnear : ∀ᶠ a in 𝓝 (0 : E →L[ℝ] ℝ), bumpPerturbation β g a ∈ 𝒰 ∧
      ∀ x ∈ A, x ∈ criticalPoints I (bumpPerturbation β g a) →
        IsManifoldNondegenerateCriticalPoint I (bumpPerturbation β g a) x := by
    have h0 : bumpPerturbation β g 0 = g := by ext y; simp [bumpPerturbation_apply]
    have ht := (continuous_bumpPerturbation β g).tendsto 0
    rw [h0] at ht
    filter_upwards [ht h𝒰, ht (eventually_forall_isManifoldNondegenerateCriticalPoint
      (WithTop.coe_le_coe.2 hn) hA hgA)] with a ha𝒰 haA using ⟨ha𝒰, haA⟩
  obtain ⟨a, ⟨ha𝒰, haA⟩, haU⟩ := (hnear.and_frequently (mem_closure_iff_frequently.1
    ((dense_setOfPred_hasNondegenerateCriticalPointsOn_sub hUo hgU) 0))).exists
  have hsupp := tsupport_bumpPerturbation_sub_subset β g a
  refine ⟨_, ha𝒰, haA, fun x hx hxc ↦ ?_,
    β.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _) hsupp, hsupp.trans hβU⟩
  -- On `U` the coordinate expression of the perturbation is `g ∘ φ.symm - a`.
  have hloc {z : E} (hz : z ∈ U) :
      (fun w ↦ (g ∘ φ.symm) w - a w) =ᶠ[𝓝 z] bumpPerturbation β g a ∘ φ.symm := by
    filter_upwards [hUo.mem_nhds hz] with w hw
    rw [hUeq] at hw
    simp only [Function.comp_apply, bumpPerturbation_apply, hβW hw.2, one_smul]
    rw [φ.right_inv hw.1]
  have hxU : φ x ∈ U := mem_image_of_mem _ hx
  have hcrit : fderiv ℝ (bumpPerturbation β g a ∘ φ.symm) (φ x) = 0 := by
    rw [← hφe]
    exact (mvfderiv_eq_zero_iff_fderiv_comp_extend_symm_eq_zero he₁ (hWs hx)).1
      (mem_criticalPoints.1 hxc)
  refine (isManifoldNondegenerateCriticalPoint_iff_of_mem_maximalAtlas he (hWs hx)).2 ?_
  rw [hφe]
  exact (hasNondegenerateCriticalPointsOn_iff.1 haU hxU (by rwa [(hloc hxU).fderiv_eq])
    ).congr_of_eventuallyEq (hloc hxU)

/-- For `n ≥ 2`, a `C^n` function can be perturbed, by an arbitrarily small weak Whitney
perturbation with compact support inside any open neighbourhood `U` of a compact set `K`, to have
only nondegenerate critical points in `K`. The perturbed function keeps this property on a
specified compact set `A` on which the original function already had it. In particular it is
unchanged on a neighbourhood of every point outside `U`. -/
theorem _root_.ContMDiffMap.exists_forall_isManifoldNondegenerateCriticalPoint_hasCompactSupport_sub
    (hn : 2 ≤ n) (f : C^n⟮I, M; 𝓘(ℝ), ℝ⟯) {K U A : Set M} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) (hA : IsCompact A)
    (hfA : ∀ x ∈ A, x ∈ criticalPoints I f → IsManifoldNondegenerateCriticalPoint I f x)
    {𝒰 : Set C^n⟮I, M; 𝓘(ℝ), ℝ⟯} (h𝒰 : 𝒰 ∈ 𝓝 f) :
    ∃ g ∈ 𝒰, (∀ x ∈ A ∪ K, x ∈ criticalPoints I g → IsManifoldNondegenerateCriticalPoint I g x) ∧
      HasCompactSupport (fun y ↦ g y - f y) ∧ tsupport (fun y ↦ g y - f y) ⊆ U := by
  classical
  obtain ⟨𝒱, h𝒱𝒰, h𝒱, hf𝒱⟩ := mem_nhds_iff.mp h𝒰
  choose W hWo hcW hW using fun x : K ↦
    exists_isOpen_forall_exists_isManifoldNondegenerateCriticalPoint (I := I) hn (x : M)
      (hU.mem_nhds (hKU x.2))
  -- Cover only the compact region to be treated; every local cutoff stays inside `U`.
  obtain ⟨t, hKt⟩ := hK.elim_finite_subcover W hWo fun x hx ↦
    mem_iUnion.mpr ⟨⟨x, hx⟩, hcW ⟨x, hx⟩⟩
  obtain ⟨L, hLc, hLW, hKL⟩ := hK.finite_compact_cover t W (fun x _ ↦ hWo x) hKt
  suffices ∀ s : Finset K, ∃ g ∈ 𝒱, (∀ x ∈ A ∪ ⋃ x ∈ s, L x,
      x ∈ criticalPoints I g → IsManifoldNondegenerateCriticalPoint I g x) ∧
      HasCompactSupport (fun y ↦ g y - f y) ∧ tsupport (fun y ↦ g y - f y) ⊆ U by
    obtain ⟨g, hg, hgm, hgc, hgs⟩ := this t
    exact ⟨g, h𝒱𝒰 hg, hKL ▸ hgm, hgc, hgs⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨f, hf𝒱, by simpa using hfA, by simp [HasCompactSupport], by simp⟩
  | insert x s _ ih =>
    obtain ⟨g, hg𝒱, hg, hgc, hgs⟩ := ih
    obtain ⟨g', hg'𝒱, hg'A, hg'W, hg'c, hg's⟩ := hW x g _
      (hA.union (s.finite_toSet.isCompact_biUnion fun y _ ↦ hLc y)) hg
      𝒱 (h𝒱.mem_nhds hg𝒱)
    have hsub : (fun y ↦ g' y - f y) =
        (fun y ↦ g' y - g y) + (fun y ↦ g y - f y) := by ext y; simp
    refine ⟨g', hg'𝒱, fun y hy hyc ↦ ?_, hsub ▸ hg'c.add hgc, ?_⟩
    · rw [Finset.set_biUnion_insert, union_left_comm] at hy
      exact hy.elim (fun hy ↦ hg'W y (hLW x hy) hyc) (fun hy ↦ hg'A y hy hyc)
    · rw [hsub]
      exact (tsupport_add _ _).trans (union_subset hg's hgs)

/-- A smooth function can be made Morse on a compact set `K` by an arbitrarily small weak
Whitney perturbation with compact support inside any open neighbourhood `U` of `K`. The
perturbed function remains Morse on a specified compact set `A` on which it already was Morse.
In particular it is unchanged on a neighbourhood of every point outside `U`. -/
theorem _root_.ContMDiffMap.exists_isMorseOn_union_hasCompactSupport_sub
    (f : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) {K U A : Set M} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) (hA : IsCompact A) (hfA : IsMorseOn I f A)
    {𝒰 : Set C^∞⟮I, M; 𝓘(ℝ), ℝ⟯} (h𝒰 : 𝒰 ∈ 𝓝 f) :
    ∃ g ∈ 𝒰, IsMorseOn I g (A ∪ K) ∧ HasCompactSupport (fun y ↦ g y - f y) ∧
      tsupport (fun y ↦ g y - f y) ⊆ U := by
  obtain ⟨g, hg, hgm, hgc, hgs⟩ :=
    f.exists_forall_isManifoldNondegenerateCriticalPoint_hasCompactSupport_sub (by simp) hK hU
      hKU hA (isMorseOn_iff_criticalPoints.1 hfA).2 h𝒰
  exact ⟨g, hg, isMorseOn_iff_criticalPoints.2 ⟨g.contMDiff.contMDiffOn, hgm⟩, hgc, hgs⟩

/-- **Nondegenerate critical points on a compact set are dense.** For a compact set `K` of a
boundaryless finite-dimensional Hausdorff manifold and `n ≥ 2`, every `C^n` function is a limit,
in the weak Whitney topology, of `C^n` functions all of whose critical points in `K` are
nondegenerate. -/
theorem dense_setOf_forall_isManifoldNondegenerateCriticalPoint (hn : 2 ≤ n) {K : Set M}
    (hK : IsCompact K) :
    Dense {f : C^n⟮I, M; 𝓘(ℝ), ℝ⟯ |
      ∀ x ∈ K, x ∈ criticalPoints I f → IsManifoldNondegenerateCriticalPoint I f x} := by
  refine dense_iff_inter_open.2 fun 𝒰 h𝒰 ⟨f, hf⟩ ↦ ?_
  obtain ⟨g, hg, hgm, -, -⟩ :=
    f.exists_forall_isManifoldNondegenerateCriticalPoint_hasCompactSupport_sub hn hK isOpen_univ
      (subset_univ _) isCompact_empty (by simp) (h𝒰.mem_nhds hf)
  exact ⟨g, hg, by simpa using hgm⟩

/-- **Functions with only nondegenerate critical points are dense** in the `C^n` functions,
`n ≥ 2`, on a compact boundaryless finite-dimensional Hausdorff manifold, for the weak Whitney
topology. With `TauCeti.isOpen_setOf_forall_mem_criticalPoints_isManifoldNondegenerateCriticalPoint`
they form an open dense set, hence a residual one (`residual_of_dense_open`). -/
theorem dense_setOf_forall_mem_criticalPoints_isManifoldNondegenerateCriticalPoint
    [CompactSpace M] (hn : 2 ≤ n) :
    Dense {f : C^n⟮I, M; 𝓘(ℝ), ℝ⟯ |
      ∀ x ∈ criticalPoints I f, IsManifoldNondegenerateCriticalPoint I f x} := by
  simpa using dense_setOf_forall_isManifoldNondegenerateCriticalPoint (I := I) hn isCompact_univ

/-- **Morse functions on a compact set are dense.** For a compact set `K` of a boundaryless
finite-dimensional Hausdorff manifold, every smooth function is a limit, in the weak Whitney
topology, of smooth functions which are Morse on `K`. -/
theorem dense_setOf_isMorseOn {K : Set M} (hK : IsCompact K) :
    Dense {f : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯ | IsMorseOn I f K} := by
  convert dense_setOf_forall_isManifoldNondegenerateCriticalPoint (I := I) (n := ⊤) le_top hK
    using 1
  ext f
  exact isMorseOn_iff_criticalPoints.trans (and_iff_right f.contMDiff.contMDiffOn)

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
