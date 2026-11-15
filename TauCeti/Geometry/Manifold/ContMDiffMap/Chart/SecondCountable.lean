/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Multilinear.SecondCountable
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.CountableSeminorms
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Second countability of the weak Whitney topology

Let `M` be a manifold, `c i` a family of points whose extended chart sources cover `M`, and
`A i` a compact exhaustion of the extended chart target at `c i`. The coordinate derivatives in
these charts, of every admissible order and restricted to every piece `A i j`, determine the weak
Whitney topology on vector-valued `C^n` maps
(`ContMDiffMap.isInducing_restrict_chartIteratedFDeriv`), even though only the charts at the
points `c i` are used.

When the family is countable, this embeds the space of `C^n` maps into a countable product of
spaces of continuous maps from compact metric spaces into spaces of multilinear maps. Over a
complete field, with a finite-dimensional model space and a second-countable target, each factor
is second countable, so the space of `C^n` maps is second countable
(`ContMDiffMap.secondCountableTopology_chartExhaustion`), hence separable. A σ-compact manifold
modelled on a locally compact space has such a countable chart family, so the weak Whitney
topology on its `C^n` maps is second countable
(`ContMDiffMap.secondCountableTopology_manifoldWeakWhitney_of_sigmaCompact`). In particular, the
Banach spaces of `C^k` functions on a compact manifold, whose topology is the weak Whitney
topology, are separable. This is the countability that the Sard–Smale theorem asks of a space of
parameters, such as `C^k(M, ℝ)` for the universal section `(f, x) ↦ df_x` over `C^k(M, ℝ) × M`.

Finite, smooth and analytic regularity and manifolds with boundary and corners are all allowed:
derivatives are taken within the extended chart targets.

## Main results

* `ContMDiffMap.isInducing_restrict_chartIteratedFDeriv`: the restricted coordinate derivatives
  in a covering chart family with compact exhaustions induce the weak Whitney topology.
* `ContMDiffMap.secondCountableTopology_chartExhaustion`: for a countable such family the weak
  Whitney topology is second countable.
* `ContMDiffMap.secondCountableTopology_manifoldWeakWhitney_of_sigmaCompact`: on a σ-compact
  manifold modelled on a locally compact space over a complete field, the weak Whitney topology on
  `C^n` maps into a second-countable normed space is second countable.

## References

* M. Hirsch, *Differential Topology*, GTM 33, Springer, 1976, Chapter 2, §1, for the weak
  topology on spaces of `C^r` maps.
-/

public section

open Set Topology TopologicalSpace
open scoped Manifold TauCeti.ManifoldWeakWhitney

namespace ContMDiffMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : WithTop ℕ∞} [IsManifold I n M]
  {ι : Type*} (c : ι → M)

/-- The coordinate derivatives of every admissible order in the charts at the points `c i`,
restricted to the pieces of compact exhaustions `A i` of the chart targets, induce the weak
Whitney topology on vector-valued `C^n` maps, provided the chart sources cover the manifold. -/
theorem isInducing_restrict_chartIteratedFDeriv
    (hcover : ∀ x : M, ∃ i, x ∈ (extChartAt I (c i)).source)
    (A : ∀ i, CompactExhaustion (extChartAt I (c i)).target) :
    IsInducing (fun (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) (j : ι × ℕ × {m : ℕ // m ≤ n}) ↦
      (chartIteratedFDeriv f (c j.1) j.2.2.1 j.2.2.2).restrict (A j.1 j.2.1)) := by
  let Φ : C^n⟮I, M; 𝓘(𝕜, F), F⟯ →ₗ[𝕜] ∀ j : ι × ℕ × {m : ℕ // m ≤ n},
      C((A j.1 j.2.1 : Set (extChartAt I (c j.1)).target), E [×j.2.2.1]→L[𝕜] F) :=
    { toFun f j := (chartIteratedFDeriv f (c j.1) j.2.2.1 j.2.2.2).restrict (A j.1 j.2.1)
      map_add' f g := by
        ext j z
        simp only [chartIteratedFDeriv_add, ContinuousMap.restrict_apply,
          ContinuousMap.add_apply, Pi.add_apply]
      map_smul' a f := by
        ext j z
        simp only [chartIteratedFDeriv_smul, ContinuousMap.restrict_apply,
          ContinuousMap.smul_apply, Pi.smul_apply, RingHom.id_apply] }
  have hΦ : Continuous Φ := continuous_pi fun j ↦
    (ContinuousMap.continuous_restrict _).comp (continuous_chartIteratedFDeriv _ _ _)
  refine ⟨le_antisymm hΦ.le_induced ?_⟩
  rw [← continuous_id_iff_le]
  -- Both topologies are given by seminorms: the weak Whitney one by the exhaustion seminorms,
  -- the induced one by the supremum norms of the components of `Φ`. Each exhaustion seminorm is
  -- the largest of finitely many of these norms, so the identity is continuous.
  have hq := withSeminorms_chartExhaustion (F := F) (n := n) c hcover A
  have (i : ι) (l : ℕ) : CompactSpace (A i l : Set (extChartAt I (c i)).target) :=
    isCompact_iff_compactSpace.mp ((A i).isCompact l)
  let _ : TopologicalSpace C^n⟮I, M; 𝓘(𝕜, F), F⟯ := .induced Φ inferInstance
  have hp := IsInducing.withSeminorms (withSeminorms_pi fun j ↦ norm_withSeminorms 𝕜
    C((A j.1 j.2.1 : Set (extChartAt I (c j.1)).target), E [×j.2.2.1]→L[𝕜] F)) (f := Φ) ⟨rfl⟩
  classical
  refine hp.continuous_of_isBounded hq LinearMap.id fun ⟨i, l, k, hk⟩ ↦ ?_
  refine ⟨Finset.univ.image fun m : Fin (k + 1) ↦ ⟨(i, l, ⟨m, (Nat.cast_le.mpr
    (Nat.le_of_lt_succ m.isLt)).trans hk⟩), ()⟩, 1, fun f ↦ ?_⟩
  rw [one_smul, Seminorm.comp_id, chartExhaustionSeminormFamily_apply]
  refine (chartCkSeminorm_le_iff _ _ k hk f (apply_nonneg _ _)).mpr fun m hm z hz ↦ ?_
  refine le_trans ?_ (Seminorm.le_finset_sup_apply (Finset.mem_image_of_mem _
    (Finset.mem_univ (⟨m, Nat.lt_succ_of_le hm⟩ : Fin (k + 1)))))
  exact ((chartIteratedFDeriv f (c i) m _).restrict (A i l)).norm_coe_le_norm ⟨z, hz⟩

/-- For a countable family of points whose chart sources cover a manifold modelled on a
finite-dimensional space over a complete field, and compact exhaustions of the chart targets, the
weak Whitney topology on `C^n` maps into a second-countable normed space is second countable. -/
theorem secondCountableTopology_chartExhaustion [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]
    [SecondCountableTopology F] [Countable ι]
    (hcover : ∀ x : M, ∃ i, x ∈ (extChartAt I (c i)).source)
    (A : ∀ i, CompactExhaustion (extChartAt I (c i)).target) :
    SecondCountableTopology C^n⟮I, M; 𝓘(𝕜, F), F⟯ := by
  have (i : ι) (l : ℕ) : CompactSpace (A i l : Set (extChartAt I (c i)).target) :=
    isCompact_iff_compactSpace.mp ((A i).isCompact l)
  exact (isInducing_restrict_chartIteratedFDeriv (F := F) (n := n) c hcover A)
    |>.secondCountableTopology

/-- **The weak Whitney topology is second countable.** On a σ-compact manifold modelled on a
locally compact space over a complete field, including manifolds with boundary and corners, the
weak Whitney topology on `C^n` maps into a second-countable normed space is second countable, and
hence separable. -/
theorem secondCountableTopology_manifoldWeakWhitney_of_sigmaCompact [CompleteSpace 𝕜]
    [LocallyCompactSpace E] [SecondCountableTopology F] [SigmaCompactSpace M] :
    SecondCountableTopology C^n⟮I, M; 𝓘(𝕜, F), F⟯ := by
  have : ProperSpace E := .of_locallyCompactSpace 𝕜
  have : FiniteDimensional 𝕜 E := .of_locallyCompactSpace 𝕜
  obtain ⟨s, hs, hc, ⟨A⟩⟩ := exists_countable_chartExhaustion (I := I) (M := M)
  have := hs.to_subtype
  exact secondCountableTopology_chartExhaustion (F := F) (n := n) (fun i : s ↦ (i : M)) hc A

end ContMDiffMap
