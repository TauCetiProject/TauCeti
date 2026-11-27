/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Persistence
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Evaluation
import TauCeti.Geometry.Manifold.Flow.Complete
import TauCeti.Geometry.Manifold.Flow.RestPoint

/-!
# Nondegenerate closed orbits are an open condition on `C^k` vector fields

Let `M` be a compact Hausdorff boundaryless smooth manifold modelled on a finite-dimensional real
space, and `k ≥ 1`. The `C^k` vector fields on `M` are the `C^k` sections
`Cₛ^k⟮I; E, TangentSpace I⟯` of the tangent bundle, with the frame topology
`ContMDiffSection.frameTopology` of any covering system of smooth frames. On a compact manifold
this topology does not depend on the frame system
(`ContMDiffSection.frameTopology_eq_of_extChartAt_interior_cover`), and it is the topology of the
Banach norm of any finite chart-frame atlas (`ContMDiffSection.finiteAtlasNormedAddCommGroup`,
`ContMDiffSection.completeSpace_finiteAtlas`). For such a norm, evaluation `(X, x) ↦ X x` is
jointly `C^k` (`ContMDiffSection.contMDiff_totalSpace_eval_finiteAtlas`), so the tautological
family `X ↦ X`, indexed by the space of all `C^k` vector fields, is a jointly `C¹` family of vector
fields indexed by a Banach space, to which the persistence results of
`TauCeti.Geometry.Manifold.Flow.Persistence` apply. Every `C¹` vector field on a compact manifold
is complete, so no flow-domain conditions remain.

A closed orbit of `X` through `x` with return time `t` is *nondegenerate* when, for some local
section `{g = g x}` transverse to `X` at `x`, `1` is not an eigenvalue of the linearized return map
`TauCeti.returnDerivative X g t x`; by `TauCeti.hasEigenvalue_returnDerivative_iff` this does not
depend on the section or on the point of the orbit. A zero of `X` solves `Φ_t(x) = x` for every `t`
and has no transverse section, so it is never nondegenerate.

* **Compact windows.** For every compact set `S` of pairs `(t, x)`, the `C^k` vector fields all of
  whose closed-orbit solutions `Φ_t(x) = x` in `S` are nondegenerate form an open set
  (`ContMDiffSection.isOpen_setOf_forall_not_hasEigenvalue_returnDerivative`). A window
  `S = [a, b] × K` contains the multiple covers of a closed orbit whose return times lie in
  `[a, b]`, so iterates are included.
* **Bounded periods.** For every compact set `K ⊆ M` and every `A`, the `C^k` vector fields all of
  whose closed orbits through `K` with return time in `(0, A]` are nondegenerate form an open set
  (`ContMDiffSection.isOpen_setOf_forall_not_hasEigenvalue_returnDerivative_period_le`). For
  `A > 0` such a field has no zero on `K`, so near it the positive return times through `K` are
  bounded below by some `ε > 0` (`TauCeti.exists_pos_eventually_period_le_of_isCompact_param`),
  which reduces this to the window `[ε, A] × K`.

These are the openness statements of the Kupka–Smale argument for closed orbits, stated on the
space of all `C^k` vector fields rather than for a finite-dimensional family of perturbations.

## Main results

* `ContMDiffSection.isOpen_setOf_forall_not_hasEigenvalue_returnDerivative`: the `C^k` vector
  fields whose closed orbits in a compact window are nondegenerate form an open set.
* `ContMDiffSection.isOpen_setOf_forall_not_hasEigenvalue_returnDerivative_period_le`: the `C^k`
  vector fields whose closed orbits through a compact set with return time at most `A` are
  nondegenerate form an open set.

## References

* M. M. Peixoto, *On an approximation theorem of Kupka and Smale*, J. Differential Equations 3
  (1967), 214–227, §2.
* J. Palis, W. de Melo, *Geometric Theory of Dynamical Systems*, Springer 1982, Chapter 3, §§3–4
  (persistence of closed orbits and the Kupka–Smale theorem).
-/

public section

noncomputable section

open Bundle Manifold Set Filter TopologicalSpace TauCeti
open scoped ContDiff Manifold Topology

namespace ContMDiffSection

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M] [CompactSpace M]

section FiniteAtlas

variable {k : ℕ} {ι : Type*} [Fintype ι]
  {e : ι → Trivialization E (π E (TangentSpace (M := M) I))}
  [∀ i, MemTrivializationAtlas (e i)]
  {U : ι → Opens M} {hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet}
  {c : ∀ i, U i} {K : ∀ i, Compacts (extChartAt I (c i)).target}
  (hK : ∀ y : M, ∃ i, ∃ hyU : y ∈ U i,
    ∃ hy : (⟨y, hyU⟩ : U i) ∈ (extChartAt I (c i)).source,
      (⟨extChartAt I (c i) ⟨y, hyU⟩, (extChartAt I (c i)).map_source hy⟩ :
        (extChartAt I (c i)).target) ∈ interior (K i : Set (extChartAt I (c i)).target))

include hK

/-- The closed-orbit solutions of `X₀` in a compact window `S` that are all nondegenerate stay
nondegenerate for every `C^k` vector field `X` near `X₀` (`k ≥ 1`) in a finite-atlas `C^k`
norm. -/
private theorem eventually_forall_not_hasEigenvalue_returnDerivative_finiteAtlas (hk : 1 ≤ k)
    {S : Set (ℝ × M)} (hS : IsCompact S) {X₀ : Cₛ^k⟮I; E, TangentSpace (M := M) I⟯}
    (hX₀ : ∀ x ∈ S, flowOf X₀ x.1 x.2 = x.2 → ∃ g : M → ℝ, ContMDiffAt I 𝓘(ℝ) 1 g x.2 ∧
      mvfderiv I g x.2 (X₀ x.2) ≠ 0 ∧ ¬(returnDerivative X₀ g x.1 x.2).HasEigenvalue 1) :
    letI := finiteAtlasNormedAddCommGroup (𝕜 := ℝ) k e U hU hK
    ∀ᶠ X : Cₛ^k⟮I; E, TangentSpace (M := M) I⟯ in 𝓝 X₀, ∀ x ∈ S, flowOf X x.1 x.2 = x.2 →
      ∃ g : M → ℝ, ContMDiffAt I 𝓘(ℝ) 1 g x.2 ∧ mvfderiv I g x.2 (X x.2) ≠ 0 ∧
        ¬(returnDerivative X g x.1 x.2).HasEigenvalue 1 := by
  let := finiteAtlasNormedAddCommGroup (𝕜 := ℝ) k e U hU hK
  let := finiteAtlasNormedSpace (𝕜 := ℝ) k e U hU hK
  have := completeSpace_finiteAtlas (𝕜 := ℝ) k e U hU hK
  filter_upwards [eventually_subset_flowDomain_and_forall_not_hasEigenvalue_returnDerivative
    (v := fun (X : Cₛ^k⟮I; E, TangentSpace (M := M) I⟯) x ↦ X x)
    ((contMDiff_totalSpace_eval_finiteAtlas k e U hU hK).of_le (by exact_mod_cast hk)) hS
    (fun z _ ↦ (isCompleteVectorField_of_compactSpace
      (X₀.contMDiff.of_le (by exact_mod_cast hk))).mem_flowDomain z.1 z.2) hX₀] with X hX
  exact hX.2

/-- If the `C^k` vector field `X₀` (`k ≥ 1`) has no zero on a compact set `K'`, there is `ε > 0`
such that, for every `C^k` vector field `X` near `X₀` in a finite-atlas `C^k` norm, no point of
`K'` returns to itself under the flow of `X` at a positive time less than `ε`. -/
private theorem exists_pos_eventually_period_le_finiteAtlas (hk : 1 ≤ k) {K' : Set M}
    (hK' : IsCompact K') {X₀ : Cₛ^k⟮I; E, TangentSpace (M := M) I⟯}
    (hmove : ∀ x ∈ K', X₀ x ≠ 0) :
    letI := finiteAtlasNormedAddCommGroup (𝕜 := ℝ) k e U hU hK
    ∃ ε > 0, ∀ᶠ X : Cₛ^k⟮I; E, TangentSpace (M := M) I⟯ in 𝓝 X₀, ∀ x ∈ K', ∀ T > 0,
      flowOf X T x = x → ε ≤ T := by
  let := finiteAtlasNormedAddCommGroup (𝕜 := ℝ) k e U hU hK
  let := finiteAtlasNormedSpace (𝕜 := ℝ) k e U hU hK
  have := completeSpace_finiteAtlas (𝕜 := ℝ) k e U hU hK
  obtain ⟨ε, hε, hbound⟩ := exists_pos_eventually_period_le_of_isCompact_param
    (v := fun (X : Cₛ^k⟮I; E, TangentSpace (M := M) I⟯) x ↦ X x)
    ((contMDiff_totalSpace_eval_finiteAtlas k e U hU hK).of_le (by exact_mod_cast hk)) hK' hmove
  refine ⟨ε, hε, ?_⟩
  filter_upwards [hbound] with X hX x hx T hT hfix
  exact (hX.self_of_nhdsSet x hx) T hT ((isCompleteVectorField_of_compactSpace
    (X.contMDiff.of_le (by exact_mod_cast hk))).mem_flowDomain T x) hfix

end FiniteAtlas

variable (k : ℕ) {κ : Type*} (e : κ → Trivialization E (π E (TangentSpace (M := M) I)))
  [∀ j, MemTrivializationAtlas (e j)]
  (U : κ → Opens M) (hU : ∀ j, (U j : Set M) ⊆ (e j).baseSet)

/-- **Nondegeneracy of the closed orbits in a compact window is open in the space of `C^k` vector
fields.** Let `M` be a compact Hausdorff boundaryless smooth manifold modelled on a
finite-dimensional real space, `k ≥ 1`, and give the `C^k` vector fields on `M` the frame topology
of any covering system of smooth frames, which is the topology of every finite-atlas `C^k` norm.
For every compact set `S` of pairs `(t, x)`, the `C^k` vector fields `X` such that every
closed-orbit solution `flowOf X t x = x` with `(t, x) ∈ S` is nondegenerate at return time `t` for
some transverse section form an open set. -/
theorem isOpen_setOf_forall_not_hasEigenvalue_returnDerivative (hk : 1 ≤ k)
    (hcover : ∀ y : M, ∃ j, y ∈ U j) {S : Set (ℝ × M)} (hS : IsCompact S) :
    letI := frameTopology (I := I) (n := k) e U hU
    IsOpen {X : Cₛ^k⟮I; E, TangentSpace (M := M) I⟯ | ∀ x ∈ S, flowOf X x.1 x.2 = x.2 →
      ∃ g : M → ℝ, ContMDiffAt I 𝓘(ℝ) 1 g x.2 ∧ mvfderiv I g x.2 (X x.2) ≠ 0 ∧
        ¬(returnDerivative X g x.1 x.2).HasEigenvalue 1} := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  -- The frame topology is that of the norm of a finite chart-frame atlas.
  obtain ⟨N, r, c, K, hK⟩ := exists_finite_compact_chart_cover_of_opens_cover (I := I) U hcover
  rw [← frameTopology_eq_of_extChartAt_interior_cover (n := k) (fun i ↦ e (r i))
    (fun i ↦ U (r i)) (fun i ↦ hU (r i)) hK e U hU hcover, @isOpen_iff_mem_nhds]
  exact fun _ hX₀ ↦ eventually_forall_not_hasEigenvalue_returnDerivative_finiteAtlas hK hk hS hX₀

/-- **Nondegeneracy of the closed orbits of bounded period is open in the space of `C^k` vector
fields.** Let `M` be a compact Hausdorff boundaryless smooth manifold modelled on a
finite-dimensional real space, `k ≥ 1`, and give the `C^k` vector fields on `M` the frame topology
of any covering system of smooth frames. For every compact set `K ⊆ M` and every `A`, the `C^k`
vector fields `X` such that every closed orbit through a point of `K` with return time in `(0, A]`,
multiple covers included, is nondegenerate form an open set. For `A > 0` such a field has no zero
on `K`. -/
theorem isOpen_setOf_forall_not_hasEigenvalue_returnDerivative_period_le (hk : 1 ≤ k)
    (hcover : ∀ y : M, ∃ j, y ∈ U j) {K : Set M} (hK : IsCompact K) (A : ℝ) :
    letI := frameTopology (I := I) (n := k) e U hU
    IsOpen {X : Cₛ^k⟮I; E, TangentSpace (M := M) I⟯ | ∀ x ∈ K, ∀ t ∈ Ioc 0 A,
      flowOf X t x = x → ∃ g : M → ℝ, ContMDiffAt I 𝓘(ℝ) 1 g x ∧ mvfderiv I g x (X x) ≠ 0 ∧
        ¬(returnDerivative X g t x).HasEigenvalue 1} := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  -- The frame topology is that of the norm of a finite chart-frame atlas.
  obtain ⟨N, r, c, L, hL⟩ := exists_finite_compact_chart_cover_of_opens_cover (I := I) U hcover
  rw [← frameTopology_eq_of_extChartAt_interior_cover (n := k) (fun i ↦ e (r i))
    (fun i ↦ U (r i)) (fun i ↦ hU (r i)) hL e U hU hcover, @isOpen_iff_mem_nhds]
  intro X₀ hX₀
  rcases le_or_gt A 0 with hA | hA
  · -- No return time lies in `(0, A]`.
    exact Filter.Eventually.of_forall fun X x _ t ht ↦ absurd (ht.1.trans_le ht.2) hA.not_gt
  -- A zero of `X₀` in `K` would be a closed orbit of return time `A` with no transverse section.
  have hmove : ∀ x ∈ K, X₀ x ≠ 0 := fun x hx h0 ↦ by
    obtain ⟨g, -, hgv, -⟩ := hX₀ x hx A ⟨hA, le_rfl⟩ (flowOf_eq_self_of_eq_zero
      (X₀.contMDiff.of_le (by exact_mod_cast hk)) h0 A)
    exact hgv (by rw [h0, map_zero])
  -- Near `X₀`, return times in `(0, ε)` do not occur, and the window `[ε, A] × K` persists.
  obtain ⟨ε, hε, hbound⟩ := exists_pos_eventually_period_le_finiteAtlas
    (e := fun i ↦ e (r i)) (hU := fun i ↦ hU (r i)) hL hk hK hmove
  filter_upwards [hbound, eventually_forall_not_hasEigenvalue_returnDerivative_finiteAtlas
    (e := fun i ↦ e (r i)) (hU := fun i ↦ hU (r i)) hL hk (isCompact_Icc.prod hK) (X₀ := X₀)
    fun z hz hfix ↦ hX₀ z.2 hz.2 z.1 ⟨hε.trans_le hz.1.1, hz.1.2⟩ hfix]
    with X hX hwin x hx t ht hfix
  exact hwin (t, x) ⟨⟨hX x hx t ht.1 hfix, ht.2⟩, hx⟩ hfix

end ContMDiffSection
