/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Action
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Homogeneity
public import TauCeti.Geometry.Diffeomorphism.Inversion
public import TauCeti.Topology.Algebra.GroupAction.OrbitTrivialization
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Local sections of evaluation on the diffeomorphism group

Let `M` be a compact boundaryless `C^n` manifold modelled on a finite-dimensional space, let
`1 ≤ m` with `m + 1 ≤ n`, and give the group `Diff(M)` of `C^m` self-diffeomorphisms of `M` the
weak Whitney topology. Evaluation at a point
`x`, `g ↦ g x`, has continuous local sections: there are an open neighbourhood `U` of `x` and a
map `s : M → Diff(M)`, continuous on `U`, with `s z x = z` for `z ∈ U` and `s x = 1`
(`TauCeti.exists_continuousOn_diffeomorph_apply_eq`). The diffeomorphisms `s z` can moreover be
chosen to fix every point outside a compact subset of any prescribed neighbourhood of `x`.

The section is built from coordinate-ball motions. Fix a basis `b₁, …, bₖ` of the model space
and a bump function `ρ` equal to `1` near `x` in the chart at `x`. The constant field `bᵢ` read in
the chart and cut off by `ρ` is a compactly supported vector field on `M`; let `φᵢ(t)` be its
time-`t` map. Near `x` its flow lines are straight lines in the chart, so for `z` close to `x`
with `e z - e x = ∑ dᵢ bᵢ`, where `e` is the chart, the composite `φ₁(d₁) ∘ ⋯ ∘ φₖ(dₖ)` carries
`x` to `z`. Each `φᵢ(t)` depends smoothly on `t` and the point, so the composite is a jointly
smooth family of diffeomorphisms parametrized by `d`, hence a continuous map into `Diff(M)`.

Consequently evaluation at `x₀` is a locally trivial principal bundle over the orbit `O` of `x₀`,
with structure group the stabilizer `H` of `x₀`: over a neighbourhood of each point of `O` it has
the trivialization `g ↦ (g x₀, σ (g x₀)⁻¹ * g)` with inverse `(z, h) ↦ σ z * h`, for a local
section `σ` (`TauCeti.exists_trivialization_diffeomorph_apply`), and these trivializations are
equivariant for right multiplication by `H`. The local sections also show that every orbit is
open, hence open and closed in `M` (`TauCeti.isClopen_orbit_diffeomorph`), so the orbit is all of
`M` when `M` is connected (`TauCeti.orbit_diffeomorph_eq_univ`).

## Main results

* `TauCeti.exists_continuousOn_diffeomorph_apply_eq`: evaluation `Diff(M) → M` at a point has a
  continuous local section through the identity, by diffeomorphisms supported in a prescribed
  neighbourhood.
* `TauCeti.exists_trivialization_diffeomorph_apply`: evaluation at `x₀` is trivial, with fibre the
  stabilizer of `x₀` and equivariantly for its right action, over a neighbourhood of each point of
  the orbit of `x₀`.
* `TauCeti.isClopen_orbit_diffeomorph`: the orbits of `Diff(M)` are open and closed.
* `TauCeti.orbit_diffeomorph_eq_univ`: on a connected manifold, `Diff(M)` acts transitively.

## References

* R. Palais, *Local triviality of the restriction map for embeddings*, Comment. Math. Helv. 34
  (1960), 305–312.
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia
  (1965), §4, Homogeneity Lemma.
-/

public section

open Set Filter Topology MulAction
open scoped Manifold ContDiff TauCeti.DiffeomorphWeakWhitney

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [BoundarylessManifold I M] {n : ℕ∞ω} [IsManifold I n M] {m : ℕ∞}

/-! ### Products of smooth families of diffeomorphisms -/

omit [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] [IsManifold I n M] in
/-- A finite product of jointly `C^m` families of diffeomorphisms is jointly `C^m`. -/
private theorem contMDiff_list_prod_apply {E' H' P : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace P]
    [ChartedSpace H' P] (l : List (P → M ≃ₘ^m⟮I, I⟯ M))
    (hl : ∀ f ∈ l, ContMDiff (I'.prod I) I m fun q : P × M ↦ f q.1 q.2) :
    ContMDiff (I'.prod I) I m fun q : P × M ↦ (l.map (· q.1)).prod q.2 := by
  induction l with
  | nil => exact contMDiff_snd
  | cons f l ih =>
    simp only [List.map_cons, List.prod_cons, Diffeomorph.mul_apply]
    exact (hl f List.mem_cons_self).comp
      (contMDiff_fst.prodMk (ih fun g hg ↦ hl g (List.mem_cons_of_mem f hg)))

/-! ### Coordinate motions -/

section ChartMotion

variable (x : M) (ρ : ContDiffBump (extChartAt I x x)) (v : E)

/-- The constant vector field `v` read in the chart at `x` and cut off by the bump function `ρ`. -/
private noncomputable def bumpField (z : M) : TangentSpace I z :=
  chartField x (fun p : E ↦ ((ρ p : ℝ) • v : E)) z

variable {x ρ}

omit [T2Space M] [BoundarylessManifold I M] [IsManifold I n M] in
/-- The compact set of `M` outside which the cut-off fields vanish: the image under the inverse
chart of the closed ball of radius `ρ.rOut`. -/
private theorem isCompact_image_closedBall
    (hρ : Metric.closedBall (extChartAt I x x) ρ.rOut ⊆ (extChartAt I x).target) :
    IsCompact ((extChartAt I x).symm '' Metric.closedBall (extChartAt I x x) ρ.rOut) :=
  (isCompact_closedBall _ _).image_of_continuousOn ((continuousOn_extChartAt_symm x).mono hρ)

omit [T2Space M] [BoundarylessManifold I M] [IsManifold I n M] in
private theorem bump_smul_eq_zero {p : E} (hp : p ∉ Metric.closedBall (extChartAt I x x) ρ.rOut) :
    ((ρ p : ℝ) • v : E) = 0 := by
  have hρp : ρ p = 0 := Function.notMem_support.1 fun h ↦
    hp (Metric.ball_subset_closedBall (ρ.support_eq ▸ h))
  rw [hρp, zero_smul]

omit [T2Space M] [BoundarylessManifold I M] [IsManifold I n M] in
private theorem bumpField_eq_zero {z : M}
    (hz : z ∉ (extChartAt I x).symm '' Metric.closedBall (extChartAt I x x) ρ.rOut) :
    bumpField x ρ v z = 0 :=
  chartField_eq_zero (fun _ hp ↦ bump_smul_eq_zero v hp) hz

variable [IsManifold I 1 M]

omit [BoundarylessManifold I M] in
private theorem contMDiff_bumpField (hmn : (m : ℕ∞ω) + 1 ≤ n)
    (hρ : Metric.closedBall (extChartAt I x x) ρ.rOut ⊆ (extChartAt I x).target) :
    ContMDiff I I.tangent m fun z ↦ (⟨z, bumpField x ρ v z⟩ : TangentBundle I M) := by
  have hw : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent m
      (fun p ↦ (⟨p, ((ρ p : ℝ) • v : E)⟩ : TangentBundle 𝓘(ℝ, E) E)) :=
    contMDiff_vectorSpace_iff_contDiff.2 (ρ.contDiff.smul contDiff_const)
  exact contMDiff_chartField hmn hw (isCompact_closedBall _ _) hρ fun _ hp ↦
    bump_smul_eq_zero v hp

private theorem isCompleteVectorField_bumpField (hm : 1 ≤ m) (hmn : (m : ℕ∞ω) + 1 ≤ n)
    (hρ : Metric.closedBall (extChartAt I x x) ρ.rOut ⊆ (extChartAt I x).target) :
    IsCompleteVectorField (bumpField x ρ v) :=
  isCompleteVectorField_of_isCompact_of_eq_zero_off
    ((contMDiff_bumpField v hmn hρ).of_le (by exact_mod_cast hm)) (isCompact_image_closedBall hρ)
    fun _ hz ↦ bumpField_eq_zero v hz

variable [IsManifold I m M]

/-- The time-`t` map of the cut-off coordinate field `bumpField x ρ v`. -/
private noncomputable def bumpFlow (hm : 1 ≤ m) (hmn : (m : ℕ∞ω) + 1 ≤ n)
    (hρ : Metric.closedBall (extChartAt I x x) ρ.rOut ⊆ (extChartAt I x).target) (v : E)
    (t : ℝ) : M ≃ₘ^m⟮I, I⟯ M :=
  globalFlowDiffeomorph (isCompleteVectorField_bumpField v hm hmn hρ) hm
    (contMDiff_bumpField v hmn hρ) t

variable {hm : 1 ≤ m} {hmn : (m : ℕ∞ω) + 1 ≤ n}
  {hρ : Metric.closedBall (extChartAt I x x) ρ.rOut ⊆ (extChartAt I x).target}

private theorem bumpFlow_apply (t : ℝ) (z : M) :
    bumpFlow hm hmn hρ v t z = maximalIntegralCurve (bumpField x ρ v) z t := by
  rw [bumpFlow, globalFlowDiffeomorph_apply, globalFlow_apply]

/-- The time-`t` maps of a cut-off coordinate field are jointly `C^m` in the time and the point. -/
private theorem contMDiff_bumpFlow :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I m fun p : ℝ × M ↦ bumpFlow hm hmn hρ v p.1 p.2 := by
  refine (contMDiff_globalFlow_uncurry (isCompleteVectorField_bumpField v hm hmn hρ) hm
    (contMDiff_bumpField v hmn hρ)).congr fun p ↦ ?_
  rw [bumpFlow, globalFlowDiffeomorph_apply]

/-- The cut-off coordinate motions fix every point outside the support of the bump function. -/
private theorem bumpFlow_apply_of_notMem {z : M}
    (hz : z ∉ (extChartAt I x).symm '' Metric.closedBall (extChartAt I x x) ρ.rOut) (t : ℝ) :
    bumpFlow hm hmn hρ v t z = z := by
  rw [bumpFlow, globalFlowDiffeomorph_apply]
  exact globalFlow_eq_of_isMIntegralCurve _ _ (isMIntegralCurve_const (bumpField_eq_zero v hz)) t

/-- Near `x`, the cut-off coordinate motion along `v` is translation by `t • v` in the chart. -/
private theorem bumpFlow_extChartAt_symm {c : E} {t : ℝ}
    (hc : ‖c - extChartAt I x x‖ + |t| * (‖v‖ + 1) < ρ.rIn) :
    bumpFlow hm hmn hρ v t ((extChartAt I x).symm c) = (extChartAt I x).symm (c + t • v) := by
  -- The segment `s ↦ c + s • v` stays in the ball where `ρ = 1` for `|s| < R`.
  set R := (ρ.rIn - ‖c - extChartAt I x x‖) / (‖v‖ + 1) with hR
  have hv1 : 0 < ‖v‖ + 1 := by positivity
  have htR : |t| < R := by rw [hR, lt_div_iff₀ hv1]; linarith
  have hseg : ∀ s ∈ Ioo (-R) R, c + s • v ∈ Metric.ball (extChartAt I x x) ρ.rIn := fun s hs ↦ by
    have hs' : |s| * (‖v‖ + 1) < ρ.rIn - ‖c - extChartAt I x x‖ := by
      rw [← lt_div_iff₀ hv1]
      exact abs_lt.2 hs
    rw [Metric.mem_ball, dist_eq_norm, add_sub_right_comm]
    calc ‖c - extChartAt I x x + s • v‖ ≤ ‖c - extChartAt I x x‖ + |s| * ‖v‖ := by
          rw [← Real.norm_eq_abs, ← norm_smul]; exact norm_add_le _ _
      _ < ρ.rIn := by nlinarith [abs_nonneg s]
  have hballt : Metric.ball (extChartAt I x x) ρ.rIn ⊆ (extChartAt I x).target :=
    (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall
      ρ.rIn_lt_rOut.le)).trans hρ
  have hcurve : IsMIntegralCurveOn (fun s ↦ (extChartAt I x).symm (c + s • v))
      (bumpField x ρ v) (Ioo (-R) R) := fun s hs ↦
    (hasMFDerivAt_chartField Metric.isOpen_ball hballt (fun p hp ↦ by
      -- `TangentSpace 𝓘(ℝ, E) p` is `E` by definition.
      simp only [ρ.one_of_mem_closedBall (Metric.ball_subset_closedBall hp), one_smul]
      rfl) (hseg s hs)).hasMFDerivWithinAt
  have hR0 : (0 : ℝ) ∈ Ioo (-R) R := ⟨by linarith [abs_nonneg t], by linarith [abs_nonneg t]⟩
  rw [bumpFlow_apply]
  exact hcurve.eqOn_maximalIntegralCurve ((contMDiff_bumpField v hmn hρ).of_le
    (by exact_mod_cast hm)) hR0 (by simp) (abs_lt.1 htR)

omit [FiniteDimensional ℝ E] in
private theorem norm_list_sum_smul_le (l : List (ℝ × E)) :
    ‖(l.map fun p ↦ p.1 • p.2).sum‖ ≤ (l.map fun p ↦ |p.1| * (‖p.2‖ + 1)).sum := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.sum_cons]
    refine (norm_add_le _ _).trans (add_le_add ?_ ih)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)

/-- A composite of cut-off coordinate motions near `x` is translation in the chart by the sum of
their displacements, as long as the motions stay in the ball where `ρ = 1`. -/
private theorem list_prod_bumpFlow_extChartAt_symm (l : List (ℝ × E)) {c : E}
    (hc : ‖c - extChartAt I x x‖ + (l.map fun p ↦ |p.1| * (‖p.2‖ + 1)).sum < ρ.rIn) :
    (l.map fun p ↦ bumpFlow hm hmn hρ p.2 p.1).prod ((extChartAt I x).symm c) =
      (extChartAt I x).symm (c + (l.map fun p ↦ p.1 • p.2).sum) := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, Diffeomorph.mul_apply] at hc ⊢
    have hp : 0 ≤ |p.1| * (‖p.2‖ + 1) := by positivity
    rw [ih (by linarith), bumpFlow_extChartAt_symm, add_comm (p.1 • p.2), add_assoc]
    calc ‖c + (l.map fun p ↦ p.1 • p.2).sum - extChartAt I x x‖ + |p.1| * (‖p.2‖ + 1)
        ≤ ‖c - extChartAt I x x‖ + (l.map fun p ↦ |p.1| * (‖p.2‖ + 1)).sum +
            |p.1| * (‖p.2‖ + 1) := by
          rw [add_sub_right_comm]
          linarith [norm_add_le (c - extChartAt I x x) (l.map fun p ↦ p.1 • p.2).sum,
            norm_list_sum_smul_le l]
      _ < ρ.rIn := by linarith

/-! ### Composites of coordinate motions -/

/-- The composite of the cut-off coordinate motions along the vectors of the basis
`Module.finBasis ℝ E`, for the times given by the coordinates of `d`. -/
private noncomputable def coordMotion (hm : 1 ≤ m) (hmn : (m : ℕ∞ω) + 1 ≤ n)
    (hρ : Metric.closedBall (extChartAt I x x) ρ.rOut ⊆ (extChartAt I x).target) (d : E) :
    M ≃ₘ^m⟮I, I⟯ M :=
  ((List.ofFn fun i ↦ ((Module.finBasis ℝ E).repr d i, Module.finBasis ℝ E i)).map
    fun p ↦ bumpFlow hm hmn hρ p.2 p.1).prod

variable {hm : 1 ≤ m} {hmn : (m : ℕ∞ω) + 1 ≤ n}
  {hρ : Metric.closedBall (extChartAt I x x) ρ.rOut ⊆ (extChartAt I x).target}

private theorem coordMotion_zero : coordMotion hm hmn hρ (0 : E) = 1 := by
  simp only [coordMotion, map_zero, Finsupp.coe_zero, Pi.zero_apply, List.map_ofFn]
  refine List.prod_eq_one fun f hf ↦ ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hf
  refine Diffeomorph.ext fun z ↦ ?_
  simp only [Function.comp_apply, bumpFlow, globalFlowDiffeomorph_apply, Flow.map_zero_apply,
    Diffeomorph.one_apply]

private theorem contMDiff_coordMotion :
    ContMDiff (𝓘(ℝ, E).prod I) I m fun q : E × M ↦ coordMotion hm hmn hρ q.1 q.2 := by
  have h := contMDiff_list_prod_apply (I' := 𝓘(ℝ, E)) (List.ofFn fun (i : Fin _) (d : E) ↦
    bumpFlow hm hmn hρ (Module.finBasis ℝ E i) ((Module.finBasis ℝ E).repr d i)) fun f hf ↦ by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hf
      have hcoord : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) m fun d : E ↦ (Module.finBasis ℝ E).repr d i :=
        (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i)).contDiff.contMDiff
      exact (contMDiff_bumpFlow (Module.finBasis ℝ E i)).comp
        ((hcoord.comp contMDiff_fst).prodMk contMDiff_snd)
  simpa only [coordMotion, List.map_ofFn, Function.comp_def] using h

private theorem coordMotion_extChartAt_symm {d : E}
    (hd : ∑ i, |(Module.finBasis ℝ E).repr d i| * (‖Module.finBasis ℝ E i‖ + 1) < ρ.rIn) :
    coordMotion hm hmn hρ d ((extChartAt I x).symm (extChartAt I x x)) =
      (extChartAt I x).symm (extChartAt I x x + d) := by
  rw [coordMotion, list_prod_bumpFlow_extChartAt_symm]
  · simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply, Module.Basis.sum_repr]
  · simpa only [sub_self, norm_zero, zero_add, List.map_ofFn, List.sum_ofFn, Function.comp_apply]
      using hd

private theorem coordMotion_apply_of_notMem {z : M}
    (hz : z ∉ (extChartAt I x).symm '' Metric.closedBall (extChartAt I x x) ρ.rOut) (d : E) :
    coordMotion hm hmn hρ d z = z := by
  rw [coordMotion]
  induction (List.ofFn fun i ↦ ((Module.finBasis ℝ E).repr d i, Module.finBasis ℝ E i)) with
  | nil => rfl
  | cons p l ih =>
    rw [List.map_cons, List.prod_cons, Diffeomorph.mul_apply, ih, bumpFlow_apply_of_notMem _ hz]

end ChartMotion

/-! ### The local section -/

section LocalSection

variable [CompactSpace M] [IsManifold I m M]

/-- **Local sections of evaluation.** Let `M` be a compact boundaryless `C^n` manifold modelled on
a finite-dimensional space, and `1 ≤ m` with `m + 1 ≤ n`. For every point `x` of an open set `V`,
there are an open neighbourhood `U` of `x` and a map `s : M → Diff(M)`, continuous on `U` for the
weak Whitney topology, with `s z x = z` for every `z ∈ U` and `s x = 1`. Every `s z` fixes each
point outside a compact subset `K` of `V`. -/
theorem exists_continuousOn_diffeomorph_apply_eq (hm : 1 ≤ m) (hmn : (m : ℕ∞ω) + 1 ≤ n)
    {V : Set M} (hV : IsOpen V) {x : M} (hx : x ∈ V) :
    ∃ U ∈ 𝓝 x, IsOpen U ∧ ∃ (K : Set M) (s : M → M ≃ₘ^m⟮I, I⟯ M), IsCompact K ∧ K ⊆ V ∧
      ContinuousOn s U ∧ s x = 1 ∧ (∀ z ∈ U, s z x = z) ∧ ∀ z, EqOn (s z) id Kᶜ := by
  have : IsManifold I 1 M := .of_le (by exact_mod_cast hm : (1 : ℕ∞ω) ≤ m)
  -- A ball around `x` in the interior of the chart target whose preimage lies in `V`.
  have hW : IsOpen (interior (extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' V) :=
    ((continuousOn_extChartAt_symm x).mono interior_subset).isOpen_inter_preimage
      isOpen_interior hV
  have hxW :
      extChartAt I x x ∈ interior (extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' V :=
    ⟨(I.isInteriorPoint_iff).1 BoundarylessManifold.isInteriorPoint, by
      rwa [mem_preimage, extChartAt_to_inv]⟩
  obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.1 hW (extChartAt I x x) hxW
  let ρ : ContDiffBump (extChartAt I x x) := ⟨r / 2, 3 * r / 4, by positivity, by linarith⟩
  have hKr : Metric.closedBall (extChartAt I x x) ρ.rOut ⊆ Metric.ball (extChartAt I x x) r :=
    Metric.closedBall_subset_ball (by change 3 * r / 4 < r; linarith)
  have hρ : Metric.closedBall (extChartAt I x x) ρ.rOut ⊆ (extChartAt I x).target :=
    fun p hp ↦ interior_subset (hrW (hKr hp)).1
  -- The displacements `d` for which the coordinate motions stay in the ball where `ρ = 1`.
  set D : Set E := {d | ∑ i, |(Module.finBasis ℝ E).repr d i| *
    (‖Module.finBasis ℝ E i‖ + 1) < ρ.rIn} with hD
  have hDo : IsOpen D := isOpen_lt (continuous_finsetSum _ fun i _ ↦
    ((LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i)).continuous.abs.mul
      continuous_const)) continuous_const
  have hD0 : (0 : E) ∈ D := by simpa [hD] using ρ.rIn_pos
  set U := (extChartAt I x).source ∩ extChartAt I x ⁻¹' ((· + extChartAt I x x) '' D) with hU
  have hUo : IsOpen U :=
    isOpen_extChartAt_preimage' x ((isOpenMap_add_right (extChartAt I x x)) D hDo)
  have hxU : x ∈ U := ⟨mem_extChartAt_source x, ⟨0, hD0, zero_add _⟩⟩
  have hfam := contMDiff_coordMotion (hm := hm) (hmn := hmn) (hρ := hρ)
  refine ⟨U, hUo.mem_nhds hxU, hUo,
    (extChartAt I x).symm '' Metric.closedBall (extChartAt I x x) ρ.rOut,
    fun z ↦ coordMotion hm hmn hρ (extChartAt I x z - extChartAt I x x),
    isCompact_image_closedBall hρ, ?_, ?_, by simp [coordMotion_zero], fun z hz ↦ ?_,
    fun z y hy ↦ coordMotion_apply_of_notMem hy _⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact (hrW (hKr hp)).2
  · exact (hfam.continuous_diffeomorphWeakWhitney.comp_continuousOn
      (((continuousOn_extChartAt x).sub continuousOn_const).mono inter_subset_left))
  · obtain ⟨d, hd, hdz⟩ := hz.2
    have hd' : extChartAt I x z - extChartAt I x x ∈ D := by
      rwa [← hdz, add_sub_cancel_right]
    have h := coordMotion_extChartAt_symm (hm := hm) (hmn := hmn) (hρ := hρ) hd'
    rw [extChartAt_to_inv] at h
    rw [h, add_sub_cancel, (extChartAt I x).left_inv hz.1]

/-! ### Local triviality of evaluation -/

omit [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] [IsManifold I n M] in
/-- On a compact manifold, evaluation `g ↦ g • x₀ = g x₀` of `C^m` diffeomorphisms is continuous
for the weak Whitney topology. -/
private theorem continuous_smul_diffeomorph (x₀ : M) :
    Continuous fun g : M ≃ₘ^m⟮I, I⟯ M ↦ g • x₀ :=
  Diffeomorph.continuous_eval_const x₀

/-- A local section of evaluation at `x₀` over a neighbourhood of any point `y` of the orbit of
`x₀`. -/
private theorem exists_continuousOn_smul_eq (hm : 1 ≤ m) (hmn : (m : ℕ∞ω) + 1 ≤ n) {x₀ y : M}
    (hy : y ∈ orbit (M ≃ₘ^m⟮I, I⟯ M) x₀) :
    ∃ U, IsOpen U ∧ y ∈ U ∧ ∃ σ : M → M ≃ₘ^m⟮I, I⟯ M, ContinuousOn σ U ∧
      ∀ z ∈ U, σ z • x₀ = z := by
  obtain ⟨g, rfl⟩ := hy
  obtain ⟨U, hUx, hU, -, s, -, -, hs, -, hsU, -⟩ :=
    exists_continuousOn_diffeomorph_apply_eq (I := I) hm hmn isOpen_univ (mem_univ (g • x₀))
  exact ⟨U, hU, mem_of_mem_nhds hUx, fun z ↦ s z * g, hs.mul continuousOn_const,
    fun z hz ↦ hsU z hz⟩

/-- **Evaluation is a locally trivial principal bundle.** Let `M` be a compact boundaryless `C^n`
manifold modelled on a finite-dimensional space, `1 ≤ m` with `m + 1 ≤ n`, and `x₀ : M`. Over a
neighbourhood of every point `y` of the orbit of `x₀` under `Diff(M)`, evaluation
`g ↦ g x₀ : Diff(M) → M` has a trivialization with fibre the stabilizer `H` of `x₀`, equivariant
for right multiplication by `H`. -/
theorem exists_trivialization_diffeomorph_apply (hm : 1 ≤ m) (hmn : (m : ℕ∞ω) + 1 ≤ n)
    {x₀ y : M} (hy : y ∈ orbit (M ≃ₘ^m⟮I, I⟯ M) x₀) :
    ∃ e : Bundle.Trivialization (stabilizer (M ≃ₘ^m⟮I, I⟯ M) x₀)
        (fun g : M ≃ₘ^m⟮I, I⟯ M ↦ g x₀),
      y ∈ e.baseSet ∧ ∀ g ∈ e.source, ∀ h : stabilizer (M ≃ₘ^m⟮I, I⟯ M) x₀,
        e (g * h) = ((e g).1, (e g).2 * h) := by
  obtain ⟨U, hU, hyU, σ, hσ, hσU⟩ := exists_continuousOn_smul_eq hm hmn hy
  exact ⟨orbitMapTrivialization x₀ (continuous_smul_diffeomorph x₀) U hU σ hσ hσU,
    by simpa using hyU, fun g hg h ↦ orbitMapTrivialization_apply_mul
      (by simpa [Bundle.Trivialization.mem_source] using hg) h⟩

/-- The orbits of the diffeomorphism group of a compact manifold are open. -/
theorem isOpen_orbit_diffeomorph (hm : 1 ≤ m) (hmn : (m : ℕ∞ω) + 1 ≤ n) (x₀ : M) :
    IsOpen (orbit (M ≃ₘ^m⟮I, I⟯ M) x₀) := by
  refine isOpen_iff_mem_nhds.2 fun y hy ↦ ?_
  obtain ⟨U, hU, hyU, σ, -, hσU⟩ := exists_continuousOn_smul_eq hm hmn hy
  exact mem_of_superset (hU.mem_nhds hyU) fun z hz ↦ ⟨σ z, hσU z hz⟩

/-- The orbits of the diffeomorphism group of a compact manifold are open and closed. -/
theorem isClopen_orbit_diffeomorph (hm : 1 ≤ m) (hmn : (m : ℕ∞ω) + 1 ≤ n) (x₀ : M) :
    IsClopen (orbit (M ≃ₘ^m⟮I, I⟯ M) x₀) := by
  refine ⟨isOpen_compl_iff.1 (isOpen_iff_mem_nhds.2 fun z hz ↦ ?_),
    isOpen_orbit_diffeomorph hm hmn x₀⟩
  refine mem_of_superset ((isOpen_orbit_diffeomorph (I := I) hm hmn z).mem_nhds (mem_orbit_self z))
    fun w hw hw₀ ↦ hz ?_
  rw [← (orbit_eq_iff.2 hw).symm.trans (orbit_eq_iff.2 hw₀)]
  exact mem_orbit_self z

/-- **Transitivity.** The diffeomorphism group of a connected compact manifold acts transitively.
-/
theorem orbit_diffeomorph_eq_univ [PreconnectedSpace M] (hm : 1 ≤ m) (hmn : (m : ℕ∞ω) + 1 ≤ n)
    (x₀ : M) : orbit (M ≃ₘ^m⟮I, I⟯ M) x₀ = univ :=
  (isClopen_orbit_diffeomorph (I := I) hm hmn x₀).eq_univ ⟨x₀, mem_orbit_self x₀⟩

end LocalSection

end TauCeti
