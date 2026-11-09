/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import TauCeti.Geometry.Diffeomorphism.Inversion
public import TauCeti.Topology.Algebra.GroupAction.LocalSection
import TauCeti.Geometry.Diffeomorphism.Orbit
import TauCeti.Geometry.Manifold.Diffeomorph.PointMotion

/-!
# The evaluation bundle of the diffeomorphism group

Let `M` be a compact Hausdorff boundaryless `C^n` manifold, `1 ≤ n ≤ ∞`, modelled on a
finite-dimensional real normed space, and give its group `Diff(M)` of `C^n` self-diffeomorphisms
the weak Whitney topology, for which it is a topological group. Fix a point `x₀ : M`. This file
shows that evaluation `Diff(M) → M`, `g ↦ g x₀`, is locally trivial over the orbit of `x₀`, with
fibre the stabilizer `H = {g | g x₀ = x₀}`.

The local trivializations come from continuous local sections. Near a point `y` there is a family
of diffeomorphisms of `M`, indexed by `d ∈ E` and depending jointly smoothly on `d` and the point
of `M`, that carries `y` to every nearby point (`Diffeomorph.exists_contMDiff_family_apply_eq`).
Joint smoothness makes the family continuous for the weak Whitney topology, giving a continuous
family `s z` of diffeomorphisms of `M`, indexed by the points `z` near `y`, with `s z y = z` and
`s y = 1` (`Diffeomorph.exists_continuousOn_apply_eq`). If `g x₀ = y`, then `σ z = s z * g` is a
local section of evaluation at `x₀` through `g`, and it gives the trivialization
`g' ↦ (g' x₀, σ(g' x₀)⁻¹ * g')`, with inverse `(z, h) ↦ σ z * h`, equivariant for right
multiplication by `H` (`Diffeomorph.exists_trivialization_smul`). For connected `M` the orbit is
`M` (`Diffeomorph.isPretransitive`), and evaluation is a locally trivial principal `H`-bundle over
`M` (`Diffeomorph.exists_trivialization_mem_baseSet`).

## Main results

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
`x₀`: for `1 ≤ n`, every point `g • x₀` of the orbit lies in the base of a local trivialization `e`
of `g ↦ g • x₀`, given by a continuous local section `s` of evaluation over `e.baseSet` with
`s (g • x₀) = g`. The chart sends `g'` to `(g' • x₀, s(g' • x₀)⁻¹ * g')`, its inverse sends `(z, h)`
to `s z * h`, and it intertwines right multiplication by the stabilizer with right multiplication
on the fibre. -/
theorem exists_trivialization_smul (hn : 1 ≤ n) (g : M ≃ₘ^n⟮I, I⟯ M) :
    ∃ (e : Bundle.Trivialization (MulAction.stabilizer (M ≃ₘ^n⟮I, I⟯ M) x₀)
        (fun g : M ≃ₘ^n⟮I, I⟯ M ↦ g • x₀)) (s : M → M ≃ₘ^n⟮I, I⟯ M),
      g • x₀ ∈ e.baseSet ∧ ContinuousOn s e.baseSet ∧ (∀ z ∈ e.baseSet, s z • x₀ = z) ∧
      s (g • x₀) = g ∧ (∀ g' ∈ e.source, ((e g').2 : M ≃ₘ^n⟮I, I⟯ M) = (s (g' • x₀))⁻¹ * g') ∧
      (∀ z ∈ e.baseSet, ∀ h : MulAction.stabilizer (M ≃ₘ^n⟮I, I⟯ M) x₀,
        e.toOpenPartialHomeomorph.symm (z, h) = s z * h) ∧
      ∀ g' ∈ e.source, ∀ h : MulAction.stabilizer (M ≃ₘ^n⟮I, I⟯ M) x₀,
        e (g' * h) = (g' • x₀, (e g').2 * h) := by
  obtain ⟨U, hU, hgU, s, hs, hsec, hsg⟩ := exists_continuousOn_smul_eq hn g
  refine ⟨TauCeti.orbitMapTrivialization (continuous_eval_const x₀) U hU s hs hsec, s, ?_⟩
  simp only [Bundle.Trivialization.mem_source, TauCeti.orbitMapTrivialization_baseSet]
  exact ⟨hgU, hs, hsec, hsg, fun g' hg' ↦ TauCeti.orbitMapTrivialization_fiberCoordinate hg',
    fun z hz h ↦ TauCeti.orbitMapTrivialization_symm_apply hz h,
    fun g' hg' h ↦ TauCeti.orbitMapTrivialization_apply_mul hg' h⟩

/-- **The evaluation bundle of the diffeomorphism group.** For `1 ≤ n` and a connected compact
Hausdorff boundaryless `C^n` manifold `M`, evaluation `g ↦ g • x₀` at a point `x₀` is a locally
trivial bundle over `M` with fibre the stabilizer of `x₀`: every point of `M` lies in the base of
a local trivialization `e`, given by a continuous local section `s` of evaluation over
`e.baseSet`. The chart sends `g` to `(g • x₀, s(g • x₀)⁻¹ * g)`, its inverse sends `(z, h)` to
`s z * h`, and it is equivariant for right multiplication by the stabilizer. -/
theorem exists_trivialization_mem_baseSet [ConnectedSpace M] (hn : 1 ≤ n) (y : M) :
    ∃ (e : Bundle.Trivialization (MulAction.stabilizer (M ≃ₘ^n⟮I, I⟯ M) x₀)
        (fun g : M ≃ₘ^n⟮I, I⟯ M ↦ g • x₀)) (s : M → M ≃ₘ^n⟮I, I⟯ M),
      y ∈ e.baseSet ∧ ContinuousOn s e.baseSet ∧ (∀ z ∈ e.baseSet, s z • x₀ = z) ∧
      (∀ g ∈ e.source, ((e g).2 : M ≃ₘ^n⟮I, I⟯ M) = (s (g • x₀))⁻¹ * g) ∧
      (∀ z ∈ e.baseSet, ∀ h : MulAction.stabilizer (M ≃ₘ^n⟮I, I⟯ M) x₀,
        e.toOpenPartialHomeomorph.symm (z, h) = s z * h) ∧
      ∀ g ∈ e.source, ∀ h : MulAction.stabilizer (M ≃ₘ^n⟮I, I⟯ M) x₀,
        e (g * h) = (g • x₀, (e g).2 * h) := by
  have := isPretransitive (I := I) (M := M) hn
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (M ≃ₘ^n⟮I, I⟯ M) x₀ y
  obtain ⟨e, s, hg, hs, hsec, -, hfib, hsymm, hmul⟩ := exists_trivialization_smul hn g
  exact ⟨e, s, hg, hs, hsec, hfib, hsymm, hmul⟩

end Diffeomorph
