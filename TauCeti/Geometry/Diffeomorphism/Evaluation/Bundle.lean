/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import TauCeti.Geometry.Diffeomorphism.Inversion
public import TauCeti.Topology.Algebra.GroupAction.LocalSection
import Mathlib.GroupTheory.GroupAction.Transitive
import TauCeti.Geometry.Manifold.Diffeomorph.Extend
import TauCeti.Geometry.Manifold.Diffeomorph.Perturbation

/-!
# The evaluation bundle of the diffeomorphism group

Let `M` be a Hausdorff boundaryless `C^n` manifold, `1 ≤ n ≤ ∞`, modelled on a
finite-dimensional real normed space. This file shows that the orbits of its group `Diff(M)` of
`C^n` self-diffeomorphisms are open and closed, so that `Diff(M)` acts transitively when `M` is
connected. When `M` is moreover compact, give `Diff(M)` the weak Whitney topology, for which it is
a topological group, and fix a point `x₀ : M`. Then evaluation `Diff(M) → M`, `g ↦ g x₀`, is
locally trivial over the orbit of `x₀`, with fibre the stabilizer `H = {g | g x₀ = x₀}`.

The local trivializations come from continuous local sections. Near a point `y`, read in the
chart at `y`, the maps `p ↦ p + ρ(p) • d`, with `ρ` a bump function equal to `1` near `y`, are
compactly supported diffeomorphisms of the model space carrying `y` to `y + d`; extended by the
identity outside the chart they form a family of diffeomorphisms of `M` depending jointly smoothly
on `d` and the point of `M` (`Diffeomorph.exists_contMDiff_family_apply_eq`). Hence the orbits are
open, and so closed as complements of the other orbits. For compact `M`, joint smoothness makes
the family continuous for the weak Whitney topology, giving a continuous family `s z` of
diffeomorphisms of `M`, indexed by the points `z` near `y`, with `s z y = z` and `s y = 1`
(`Diffeomorph.exists_continuousOn_apply_eq`). If `g x₀ = y`, then `σ z = s z * g` is a local
section of evaluation at `x₀` through `g`, and it gives the trivialization
`g' ↦ (g' x₀, σ(g' x₀)⁻¹ * g')`, with inverse `(z, h) ↦ σ z * h`, equivariant for right
multiplication by `H` (`Diffeomorph.exists_trivialization_smul`). For connected `M` the orbit is
`M`, and evaluation is a locally trivial principal `H`-bundle over `M`
(`Diffeomorph.exists_trivialization_mem_baseSet`).

## Main results

* `Diffeomorph.exists_contMDiff_family_apply_eq`: jointly smooth families of diffeomorphisms
  moving a point to every nearby point.
* `Diffeomorph.isOpen_orbit`, `Diffeomorph.isClosed_orbit`: the orbits of `Diff(M)` are open and
  closed.
* `Diffeomorph.isPretransitive`: `Diff(M)` acts transitively on a connected manifold.
* `Diffeomorph.exists_continuousOn_apply_eq`: for compact `M`, continuous local sections of
  evaluation at a point, equal to the identity at that point.
* `Diffeomorph.exists_trivialization_smul`: evaluation at `x₀` is trivialized, equivariantly
  for the stabilizer, over a neighbourhood of every point of the orbit of `x₀`.
* `Diffeomorph.exists_trivialization_mem_baseSet`: on a connected manifold, evaluation at `x₀` is a
  locally trivial bundle over `M` with fibre the stabilizer of `x₀`.

## References

* R. Palais, *Local triviality of the restriction map for embeddings*, Comment. Math. Helv. 34
  (1960), 305–312.
* J. Cerf, *Topologie de certains espaces de plongements*, Bull. Soc. Math. France 89 (1961),
  227–380.
* J. W. Milnor, *Topology from the Differentiable Viewpoint* (1965), §4, Homogeneity Lemma.
-/

public section

open Set Topology Metric
open scoped Manifold ContDiff TauCeti.DiffeomorphWeakWhitney

namespace Diffeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [BoundarylessManifold I M] {n : ℕ∞} [IsManifold I n M]

/-- **Smooth families of point motions.** For `1 ≤ n`, every point `y` of a Hausdorff
boundaryless `C^n` manifold `M` has an open neighbourhood `U` with a family `S d`, `d ∈ E`, of
`C^n` diffeomorphisms of `M`, depending jointly `C^n`-smoothly on `d` and the point of `M`, and a
map `f : M → E`, continuous on `U`, such that `S (f z)` carries `y` to `z` for every `z ∈ U` and
`S (f y)` is the identity. -/
theorem exists_contMDiff_family_apply_eq (hn : 1 ≤ n) (y : M) :
    ∃ U : Set M, IsOpen U ∧ y ∈ U ∧ ∃ (S : E → M ≃ₘ^n⟮I, I⟯ M) (f : M → E),
      ContMDiff (𝓘(ℝ, E).prod I) I n (fun q : E × M ↦ S q.1 q.2) ∧ ContinuousOn f U ∧
      (∀ z ∈ U, S (f z) y = z) ∧ S (f y) = 1 := by
  set e := extChartAt I y with he
  -- A closed ball `K` about `e y` in the interior of the chart target.
  obtain ⟨r, hr, hrt⟩ := Metric.isOpen_iff.1 isOpen_interior (e y)
    ((I.isInteriorPoint_iff).1 BoundarylessManifold.isInteriorPoint)
  set K := closedBall (e y) (r / 2) with hK
  have hKc : IsCompact K := isCompact_closedBall _ _
  have hKt : K ⊆ interior e.target := (closedBall_subset_ball (by linarith)).trans hrt
  -- The compactly supported translations `τ d` of the model space, moving `e y` to `e y + d`.
  obtain ⟨δ, hδ, τ, hτs, hτK, hτ0, hτc⟩ :=
    TauCeti.exists_diffeomorph_family_apply_eq_add (e y) (by positivity : 0 < r / 2) hn
  have hτK' (d : E) : ∀ p ∉ K, τ d p = p := fun p hp ↦ hτK d p fun h ↦ hp (ball_subset_closedBall h)
  -- Their extensions through the chart form a smooth family `S` of diffeomorphisms of `M`.
  let S : E → M ≃ₘ^n⟮I, I⟯ M := fun d ↦ (τ d).chartExtend y hKc hKt (hτK' d)
  have hS : ContMDiff (𝓘(ℝ, E).prod I) I n (fun q : E × M ↦ S q.1 q.2) := by
    have hτs' := contMDiff_iff_contDiff.2 hτs
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hτs'
    exact contMDiff_chartExtend hτs' hτK'
  have hS_apply (d : E) (hd : ‖d‖ < δ) : S d y = e.symm (e y + d) := by
    have h := chartExtend_extChartAt_symm (φ := τ d) (hK := hKc) (hKt := hKt) (hφ := hτK' d)
      (mem_extChartAt_target y)
    rwa [← he, e.left_inv (mem_extChartAt_source y), hτc d hd] at h
  -- The section at `z` is `S (e z - e y)`, on the chart points within `δ` of `e y`.
  refine ⟨e.source ∩ e ⁻¹' ball (e y) δ, isOpen_extChartAt_preimage' y isOpen_ball,
    ⟨mem_extChartAt_source y, mem_ball_self hδ⟩, S, fun z ↦ e z - e y, hS, ?_, fun z hz ↦ ?_, ?_⟩
  · exact ((continuousOn_extChartAt y).sub continuousOn_const).mono fun _ hz ↦ hz.1
  · rw [hS_apply _ (by rw [← dist_eq_norm]; exact hz.2), add_sub_cancel, e.left_inv hz.1]
  · ext z
    simp [S, hτ0, TauCeti.chartExtend_id]

/-- **The orbits of the diffeomorphism group are open.** -/
theorem isOpen_orbit (hn : 1 ≤ n) (x : M) : IsOpen (MulAction.orbit (M ≃ₘ^n⟮I, I⟯ M) x) := by
  refine isOpen_iff_forall_mem_open.2 ?_
  rintro _ ⟨g, rfl⟩
  obtain ⟨U, hU, hgU, S, f, -, -, hS, -⟩ := exists_contMDiff_family_apply_eq (I := I) hn (g • x)
  refine ⟨U, fun z hz ↦ ?_, hU, hgU⟩
  have hz' : (S (f z) * g) • x = z := by rw [mul_smul, smul_def (S (f z)), hS z hz]
  exact ⟨_, hz'⟩

/-- **The orbits of the diffeomorphism group are closed**, being complements of unions of
orbits. -/
theorem isClosed_orbit (hn : 1 ≤ n) (x : M) : IsClosed (MulAction.orbit (M ≃ₘ^n⟮I, I⟯ M) x) := by
  refine isOpen_compl_iff.1 (isOpen_iff_forall_mem_open.2 fun y hy ↦ ⟨_, fun z hz hzx ↦ hy ?_,
    isOpen_orbit (I := I) hn y, MulAction.mem_orbit_self y⟩)
  rw [← MulAction.orbit_eq_iff.2 hzx, MulAction.orbit_eq_iff.2 hz]
  exact MulAction.mem_orbit_self y

/-- **The diffeomorphism group of a connected manifold acts transitively**: for `1 ≤ n`, every
point of a connected Hausdorff boundaryless `C^n` manifold is carried to every other point
by a `C^n` diffeomorphism. -/
theorem isPretransitive [ConnectedSpace M] (hn : 1 ≤ n) :
    MulAction.IsPretransitive (M ≃ₘ^n⟮I, I⟯ M) M := by
  obtain ⟨x⟩ := ConnectedSpace.toNonempty (α := M)
  rw [MulAction.isPretransitive_iff_orbit_eq_univ x]
  exact IsClopen.eq_univ ⟨isClosed_orbit hn x, isOpen_orbit hn x⟩ ⟨x, MulAction.mem_orbit_self x⟩

variable [CompactSpace M]

/-- **Continuous local sections of evaluation.** For `1 ≤ n`, every point `y` of a compact
Hausdorff boundaryless `C^n` manifold `M` has an open neighbourhood `U` with a family `s z` of
`C^n` diffeomorphisms of `M`, continuous on `U` for the weak Whitney topology, such that `s z`
carries `y` to `z` for every `z ∈ U` and `s y` is the identity. -/
theorem exists_continuousOn_apply_eq (hn : 1 ≤ n) (y : M) :
    ∃ U : Set M, IsOpen U ∧ y ∈ U ∧ ∃ s : M → M ≃ₘ^n⟮I, I⟯ M,
      ContinuousOn s U ∧ (∀ z ∈ U, s z y = z) ∧ s y = 1 := by
  obtain ⟨U, hU, hyU, S, f, hS, hf, hSy, hS1⟩ := exists_contMDiff_family_apply_eq (I := I) hn y
  exact ⟨U, hU, hyU, fun z ↦ S (f z), hS.continuous_diffeomorphWeakWhitney.comp_continuousOn hf,
    hSy, hS1⟩

variable {x₀ : M}

/-- **Continuous local sections of evaluation through a diffeomorphism.** For `1 ≤ n` and every
diffeomorphism `g`, evaluation at `x₀` has a continuous local section `s` over an open
neighbourhood `U` of `g x₀`, with `s (g x₀) = g`. -/
theorem exists_continuousOn_smul_eq (hn : 1 ≤ n) (g : M ≃ₘ^n⟮I, I⟯ M) :
    ∃ U : Set M, IsOpen U ∧ g • x₀ ∈ U ∧ ∃ s : M → M ≃ₘ^n⟮I, I⟯ M,
      ContinuousOn s U ∧ (∀ z ∈ U, s z • x₀ = z) ∧ s (g • x₀) = g := by
  obtain ⟨U, hU, hyU, s, hs, hsy, hs1⟩ := exists_continuousOn_apply_eq (I := I) hn (g • x₀)
  refine ⟨U, hU, hyU, fun z ↦ s z * g, hs.mul continuousOn_const, fun z hz ↦ ?_, ?_⟩
  · rw [mul_smul, smul_def (s z), hsy z hz]
  · simp only [hs1, one_mul]

/-- **Evaluation at `x₀` is locally trivial over the orbit of `x₀`**, with fibre the stabilizer of
`x₀`: for `1 ≤ n`, every point `g • x₀` of the orbit lies in the base of a local trivialization of
`g ↦ g • x₀` which intertwines right multiplication by the stabilizer with right multiplication on
the fibre. -/
theorem exists_trivialization_smul (hn : 1 ≤ n) (g : M ≃ₘ^n⟮I, I⟯ M) :
    ∃ e : Bundle.Trivialization (MulAction.stabilizer (M ≃ₘ^n⟮I, I⟯ M) x₀)
        (fun g : M ≃ₘ^n⟮I, I⟯ M ↦ g • x₀),
      g • x₀ ∈ e.baseSet ∧ ∀ g' ∈ e.source, ∀ h : MulAction.stabilizer (M ≃ₘ^n⟮I, I⟯ M) x₀,
        e (g' * h) = (g' • x₀, (e g').2 * h) := by
  obtain ⟨U, hU, hgU, s, hs, hsec, -⟩ := exists_continuousOn_smul_eq hn g
  refine ⟨TauCeti.orbitMapTrivialization (continuous_eval_const x₀) U hU s hs hsec,
    by rwa [TauCeti.orbitMapTrivialization_baseSet],
    fun g' hg' h ↦ TauCeti.orbitMapTrivialization_apply_mul ?_ h⟩
  rwa [Bundle.Trivialization.mem_source, TauCeti.orbitMapTrivialization_baseSet] at hg'

/-- **The evaluation bundle of the diffeomorphism group.** For `1 ≤ n` and a connected compact
Hausdorff boundaryless `C^n` manifold `M`, evaluation `g ↦ g • x₀` at a point `x₀` is a locally
trivial bundle over `M` with fibre the stabilizer of `x₀`: every point of `M` lies in the base of
a local trivialization, which is equivariant for right multiplication by the stabilizer. -/
theorem exists_trivialization_mem_baseSet [ConnectedSpace M] (hn : 1 ≤ n) (y : M) :
    ∃ e : Bundle.Trivialization (MulAction.stabilizer (M ≃ₘ^n⟮I, I⟯ M) x₀)
        (fun g : M ≃ₘ^n⟮I, I⟯ M ↦ g • x₀),
      y ∈ e.baseSet ∧ ∀ g' ∈ e.source, ∀ h : MulAction.stabilizer (M ≃ₘ^n⟮I, I⟯ M) x₀,
        e (g' * h) = (g' • x₀, (e g').2 * h) := by
  have := isPretransitive (I := I) (M := M) hn
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (M ≃ₘ^n⟮I, I⟯ M) x₀ y
  exact exists_trivialization_smul hn g

end Diffeomorph
