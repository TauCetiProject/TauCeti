/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import TauCeti.Geometry.Diffeomorphism.Action
public import TauCeti.Geometry.Diffeomorphism.Inversion
public import TauCeti.Topology.Algebra.GroupAction.OrbitTrivialization
import TauCeti.Geometry.Manifold.Diffeomorph.PointMotion

/-!
# Local sections of evaluation on the diffeomorphism group

Let `M` be a compact boundaryless `C^m` manifold modelled on a finite-dimensional space, `1 ≤ m`,
and give the group `Diff(M)` of `C^m` self-diffeomorphisms of `M` the weak Whitney topology.
Evaluation at a point `x`, `g ↦ g x`, has continuous local sections: there are an open
neighbourhood `U` of `x` and a map `s : M → Diff(M)`, continuous on `U`, with `s z x = z` for
`z ∈ U` and `s x = 1` (`TauCeti.exists_continuousOn_diffeomorph_apply_eq`). The diffeomorphisms
`s z` can moreover be chosen to fix every point outside a compact subset of any prescribed
neighbourhood of `x`.

The section is built from cut-off translations. Read in the chart at `x`, the maps
`p ↦ p + ρ(p) • d`, with `ρ` a bump function equal to `1` near `x`, are compactly supported
diffeomorphisms of the model space carrying `x` to the point with chart coordinate `e x + d`, where
`e` is the chart. Extended by the identity outside the chart, they form a family of
diffeomorphisms of `M` depending jointly `C^m`-smoothly on `d` and the point
(`TauCeti.exists_contMDiff_family_apply_eq`), hence a continuous map into `Diff(M)`. Flows of
vector fields would lose a derivative, since vector fields on a `C^m` manifold are only `C^(m-1)`;
cut-off translations do not, so `C^m` regularity of `M` suffices.

Consequently evaluation at `x₀` is a locally trivial principal bundle over the orbit of `x₀`,
with structure group the stabilizer `H` of `x₀`: over a neighbourhood of each point of the orbit
it has the trivialization `g ↦ (g x₀, σ (g x₀)⁻¹ * g)` with inverse `(z, h) ↦ σ z * h`, for a
local section `σ` (`TauCeti.exists_trivialization_diffeomorph_apply`, by
`TauCeti.orbitMapTrivialization`), and these trivializations are equivariant for right
multiplication by `H`. The orbits themselves are open and closed
(`TauCeti.isClopen_orbit_diffeomorph`).

## Main results

* `TauCeti.exists_continuousOn_diffeomorph_apply_eq`: evaluation `Diff(M) → M` at a point has a
  continuous local section through the identity, by diffeomorphisms supported in a prescribed
  neighbourhood.
* `TauCeti.exists_continuousOn_diffeomorph_apply_eq_of_mem_orbit`: evaluation at `x₀` has a
  continuous local section around every point of the orbit of `x₀`.
* `TauCeti.exists_trivialization_diffeomorph_apply`: evaluation at `x₀` is trivial, with fibre the
  stabilizer of `x₀` and equivariantly for its right action, over a neighbourhood of each point of
  the orbit of `x₀`, by the chart `g ↦ (g x₀, σ (g x₀)⁻¹ * g)` of a continuous local section `σ`.

## References

* R. Palais, *Local triviality of the restriction map for embeddings*, Comment. Math. Helv. 34
  (1960), 305–312.
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia
  (1965), §4, Homogeneity Lemma.
-/

public section

open Set Filter Metric Topology MulAction
open scoped Manifold ContDiff TauCeti.DiffeomorphWeakWhitney

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [BoundarylessManifold I M] {m : ℕ∞}

/-! ### The local section -/

section LocalSection

variable [CompactSpace M] [IsManifold I m M]

/-- **Local sections of evaluation.** Let `M` be a compact boundaryless `C^m` manifold modelled on
a finite-dimensional space, `1 ≤ m`. For every point `x` of an open set `V`, there are an open
neighbourhood `U` of `x` and a map `s : M → Diff(M)`, continuous on `U` for the weak Whitney
topology, with `s z x = z` for every `z ∈ U` and `s x = 1`. Every `s z` fixes each point outside a
compact subset `K` of `V`. -/
theorem exists_continuousOn_diffeomorph_apply_eq (hm : 1 ≤ m) {V : Set M} (hV : IsOpen V) {x : M}
    (hx : x ∈ V) :
    ∃ U ∈ 𝓝 x, IsOpen U ∧ ∃ (K : Set M) (s : M → M ≃ₘ^m⟮I, I⟯ M), IsCompact K ∧ K ⊆ V ∧
      ContinuousOn s U ∧ s x = 1 ∧ (∀ z ∈ U, s z x = z) ∧ ∀ z, EqOn (s z) id Kᶜ := by
  obtain ⟨U, hU, hxU, K, S, f, hK, hKV, hS, hf, hSx, hS1, hSK⟩ :=
    exists_contMDiff_family_apply_eq (I := I) hm hV hx
  exact ⟨U, hU.mem_nhds hxU, hU, K, fun z ↦ S (f z), hK, hKV,
    hS.continuous_diffeomorphWeakWhitney.comp_continuousOn hf, hS1, hSx, fun z ↦ hSK (f z)⟩

/-! ### Local triviality of evaluation -/

/-- Evaluation `g ↦ g x₀ : Diff(M) → M` has a section `σ`, `σ z x₀ = z`, continuous on an open
neighbourhood of any point `y` of the orbit of `x₀`. -/
theorem exists_continuousOn_diffeomorph_apply_eq_of_mem_orbit (hm : 1 ≤ m) {x₀ y : M}
    (hy : y ∈ orbit (M ≃ₘ^m⟮I, I⟯ M) x₀) :
    ∃ U, IsOpen U ∧ y ∈ U ∧ ∃ σ : M → M ≃ₘ^m⟮I, I⟯ M, ContinuousOn σ U ∧
      ∀ z ∈ U, σ z x₀ = z := by
  obtain ⟨g, rfl⟩ := mem_orbit_iff.1 hy
  rw [Diffeomorph.smul_def]
  obtain ⟨U, hUx, hU, -, s, -, -, hs, -, hsU, -⟩ :=
    exists_continuousOn_diffeomorph_apply_eq (I := I) hm isOpen_univ (mem_univ (g x₀))
  refine ⟨U, hU, mem_of_mem_nhds hUx, fun z ↦ s z * g, hs.mul continuousOn_const, fun z hz ↦ ?_⟩
  rw [Diffeomorph.mul_apply]
  exact hsU z hz

/-- **Evaluation is a locally trivial principal bundle.** Let `M` be a compact boundaryless `C^m`
manifold modelled on a finite-dimensional space, `1 ≤ m`, and `x₀ : M`. Over a neighbourhood of
every point `y` of the orbit of `x₀` under `Diff(M)`, evaluation
`g ↦ g x₀ : Diff(M) → M` has a trivialization `e` with fibre the stabilizer `H` of `x₀`, equivariant
for right multiplication by `H`. It is the chart of a section `σ` of evaluation, continuous on the
base of `e`: `e` sends `g` to `(g x₀, σ (g x₀)⁻¹ * g)`, and its inverse sends `(z, h)` to
`σ z * h`. -/
theorem exists_trivialization_diffeomorph_apply (hm : 1 ≤ m) {x₀ y : M}
    (hy : y ∈ orbit (M ≃ₘ^m⟮I, I⟯ M) x₀) :
    ∃ (σ : M → M ≃ₘ^m⟮I, I⟯ M) (e : Bundle.Trivialization (stabilizer (M ≃ₘ^m⟮I, I⟯ M) x₀)
        (fun g : M ≃ₘ^m⟮I, I⟯ M ↦ g x₀)),
      y ∈ e.baseSet ∧ ContinuousOn σ e.baseSet ∧ (∀ z ∈ e.baseSet, σ z x₀ = z) ∧
      (∀ g ∈ e.source, ((e g).2 : M ≃ₘ^m⟮I, I⟯ M) = (σ (g x₀))⁻¹ * g) ∧
      (∀ p, e.toOpenPartialHomeomorph.symm p = σ p.1 * p.2) ∧
      ∀ g ∈ e.source, ∀ h : stabilizer (M ≃ₘ^m⟮I, I⟯ M) x₀,
        e (g * h) = ((e g).1, (e g).2 * h) := by
  obtain ⟨U, hU, hyU, σ, hσ, hσU⟩ :=
    exists_continuousOn_diffeomorph_apply_eq_of_mem_orbit hm hy
  -- Evaluation `g ↦ g x₀` is the orbit map `g ↦ g • x₀` by definition (`Diffeomorph.smul_def`).
  let e := orbitMapTrivialization x₀ (Diffeomorph.continuous_eval_const x₀) U hU σ hσ hσU
  have he : e.baseSet = U := orbitMapTrivialization_baseSet
  have hsource (g : M ≃ₘ^m⟮I, I⟯ M) (hg : g ∈ e.source) : g x₀ ∈ U := he ▸ e.mem_source.1 hg
  refine ⟨σ, e, he ▸ hyU, he ▸ hσ, he ▸ hσU,
    fun g hg ↦ orbitMapTrivialization_fiberCoordinate (hsource g hg),
    orbitMapTrivialization_symm_apply,
    fun g hg h ↦ orbitMapTrivialization_apply_mul (hsource g hg) h⟩

end LocalSection

end TauCeti
