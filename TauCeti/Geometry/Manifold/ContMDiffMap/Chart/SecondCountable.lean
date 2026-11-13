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
# Second countability of spaces of `C^n` maps

Let `M` be a manifold modelled on a finite-dimensional, second-countable space `E` over a complete
field `𝕜`, and `F` a second-countable normed space. Choose countably many charts of `M` whose
sources cover `M`, and a compact exhaustion of each chart target. Restricting the coordinate
derivatives of order at most `n` to the compact pieces of these exhaustions gives a linear map
`ContMDiffMap.chartExhaustionJet` from the vector-valued `C^n` maps into a countable product of
supremum-norm spaces of continuous maps on compact sets. The supremum norms of its components are
the compact chart derivative seminorms, which are equivalent to the compact chart `C^k` seminorms
generating the weak Whitney topology (`ContMDiffMap.withSeminorms_chartExhaustion`), so this map
induces the weak Whitney topology (`ContMDiffMap.isInducing_chartExhaustionJet`). Each factor is
second countable: the compact pieces are compact metrizable, and the derivatives take values in a
second-countable space of continuous multilinear maps
(`ContinuousMultilinearMap.secondCountableTopology`). So the space of `C^n` maps is second
countable, and in particular separable.

This holds on every sigma-compact manifold with locally compact model over a complete field, for
every regularity `n`, including manifolds with boundary or corners: such a model is
finite-dimensional, and it is second countable because it is proper. The finite-atlas norm of
`ContMDiffMap.finiteAtlasNormedAddCommGroup` carries the weak Whitney topology by construction, so
on a compact manifold the Banach space of `C^k` maps is separable. These are the separability
hypotheses of the Sard–Smale theorem and of parametric transversality when the parameter space is
a space of functions: the product of the parameter space with a second-countable manifold, and
hence every subset of it, such as the zero set of a universal section, is again second
countable.

## Main results

* `ContMDiffMap.isInducing_chartExhaustionJet`: the family of restricted chart derivatives
  induces the weak Whitney topology.
* `ContMDiffMap.secondCountableTopology_chartExhaustion`: the weak Whitney topology is second
  countable, given countably many covering charts with compact exhaustions.
* `ContMDiffMap.secondCountableTopology_manifoldWeakWhitney_of_sigmaCompact`: the weak Whitney
  topology is second countable on a sigma-compact manifold with locally compact model; it is a
  scoped instance in `TauCeti.ManifoldWeakWhitney`.

## References

* M. Hirsch, *Differential Topology*, GTM 33, Chapter 2 (the weak topology on `C^r` maps and
  its countability properties).
-/

public section

open Set Topology
open scoped Manifold TauCeti.ManifoldWeakWhitney

namespace ContMDiffMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section Exhaustion

variable {n : WithTop ℕ∞} [IsManifold I n M] {ι : Type*} (c : ι → M)

/-- The coordinate derivatives of order at most `n` in the charts at the points `c i`, restricted
to the compact pieces of chosen exhaustions `A i` of the chart targets, each in its
supremum-norm space of continuous maps. The component at `(i, l, m)` is the `m`-th derivative in
the chart at `c i`, restricted to the `l`-th compact piece of `A i`. -/
noncomputable def chartExhaustionJet (A : ∀ i, CompactExhaustion (extChartAt I (c i)).target) :
    C^n⟮I, M; 𝓘(𝕜, F), F⟯ →ₗ[𝕜]
      ∀ j : ι × ℕ × {m : ℕ // m ≤ n},
        C((⟨A j.1 j.2.1, (A j.1).isCompact j.2.1⟩ :
          TopologicalSpace.Compacts (extChartAt I (c j.1)).target), E [×j.2.2.1]→L[𝕜] F) :=
  LinearMap.pi fun j ↦
    (ContinuousMap.compCLM 𝕜 (E [×j.2.2.1]→L[𝕜] F)
      (ContinuousMap.subtypeVal (A j.1 j.2.1))).toLinearMap ∘ₗ
        chartIteratedFDerivLinearMap (c j.1) j.2.2.1 j.2.2.2

/-- A component of `chartExhaustionJet` is the corresponding chart derivative, restricted to
the corresponding compact piece. -/
theorem chartExhaustionJet_apply (A : ∀ i, CompactExhaustion (extChartAt I (c i)).target)
    (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) (j : ι × ℕ × {m : ℕ // m ≤ n}) :
    chartExhaustionJet c A f j =
      (chartIteratedFDeriv f (c j.1) j.2.2.1 j.2.2.2).restrict (A j.1 j.2.1) := by
  refine ContinuousMap.ext fun z ↦ ?_
  simp only [chartExhaustionJet, LinearMap.pi_apply, LinearMap.comp_apply,
    ContinuousLinearMap.coe_coe, ContinuousMap.compCLM_apply, ContinuousMap.comp_apply]
  -- Both sides evaluate the chart derivative at the point `z` of the compact piece; the point is
  -- typed by the bundled compact set, so `subtypeVal_apply` and `restrict_apply` do not fire.
  exact DFunLike.congr_fun (chartIteratedFDerivLinearMap_apply (c j.1) j.2.2.1 j.2.2.2 f) _

/-- The supremum norm of a component of `chartExhaustionJet` is the compact chart derivative
seminorm on the corresponding compact piece. -/
theorem norm_chartExhaustionJet_apply (A : ∀ i, CompactExhaustion (extChartAt I (c i)).target)
    (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) (i : ι) (l m : ℕ) (hm : m ≤ n) :
    ‖chartExhaustionJet c A f (i, l, ⟨m, hm⟩)‖ =
      chartDerivativeSeminorm (c i) ⟨A i l, (A i).isCompact l⟩ m hm f := by
  rw [chartExhaustionJet_apply, chartDerivativeSeminorm_apply]
  -- The compact piece, bundled as a compact set, coerces back to the same set.
  rfl

variable (hcover : ∀ x : M, ∃ i, x ∈ (extChartAt I (c i)).source)
include hcover

/-- For charts whose sources cover the manifold, the coordinate derivatives restricted to the
compact pieces of exhaustions of the chart targets induce the weak Whitney topology. -/
theorem isInducing_chartExhaustionJet (A : ∀ i, CompactExhaustion (extChartAt I (c i)).target) :
    IsInducing (chartExhaustionJet (F := F) (n := n) c A) := by
  classical
  let Φ := chartExhaustionJet (F := F) (n := n) c A
  let P (j : ι × ℕ × {m : ℕ // m ≤ n}) := C((⟨A j.1 j.2.1, (A j.1).isCompact j.2.1⟩ :
    TopologicalSpace.Compacts (extChartAt I (c j.1)).target), E [×j.2.2.1]→L[𝕜] F)
  let q : SeminormFamily 𝕜 C^n⟮I, M; 𝓘(𝕜, F), F⟯ ((_ : ι × ℕ × {m : ℕ // m ≤ n}) × Unit) :=
    (SeminormFamily.sigma fun j ↦
      SeminormFamily.comp (fun _ : Unit ↦ normSeminorm 𝕜 (P j)) (LinearMap.proj j)).comp Φ
  -- The norms of the components generate the induced topology.
  have hind : WithSeminorms (topology := .induced Φ inferInstance) q :=
    Φ.withSeminorms_induced (withSeminorms_pi fun j ↦ norm_withSeminorms 𝕜 (P j))
  -- They are the compact chart derivative seminorms, which are equivalent to the compact chart
  -- `C^k` seminorms generating the weak Whitney topology.
  have hnorm (i : ι) (l m : ℕ) (hm : m ≤ n) (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) :
      q ⟨(i, l, ⟨m, hm⟩), ()⟩ f =
        chartDerivativeSeminorm (c i) ⟨A i l, (A i).isCompact l⟩ m hm f := by
    simp only [q, SeminormFamily.comp_apply, SeminormFamily.sigma, Seminorm.comp_apply,
      coe_normSeminorm, LinearMap.proj_apply]
    exact norm_chartExhaustionJet_apply c A f i l m hm
  have hWW : WithSeminorms q := (withSeminorms_chartExhaustion (F := F) (n := n) c hcover A).congr
    (Seminorm.IsBounded.of_real fun j ↦ ⟨{(j.1.1, j.1.2.1, j.1.2.2)}, 1, fun f ↦ ?_⟩)
    (Seminorm.IsBounded.of_real fun j ↦
      ⟨Finset.univ.image fun m : Fin (j.2.2.1 + 1) ↦
        (⟨(j.1, j.2.1, ⟨m, (Nat.cast_le.mpr (Nat.le_of_lt_succ m.isLt)).trans j.2.2.2⟩), ()⟩ :
          (_ : ι × ℕ × {m : ℕ // m ≤ n}) × Unit), 1, fun f ↦ ?_⟩)
  · exact ⟨hWW.1.trans
      (WithSeminorms.topology_eq_withSeminorms (topology := .induced Φ inferInstance) hind).symm⟩
  · -- A derivative seminorm is at most the `C^k` seminorm of the same order.
    obtain ⟨⟨i, l, m, hm⟩, -⟩ := j
    dsimp only
    rw [LinearMap.id_apply, hnorm, one_mul, Finset.sup_singleton,
      chartExhaustionSeminormFamily_apply]
    refine (chartDerivativeSeminorm_le_iff _ _ m hm f (apply_nonneg _ _)).mpr fun z hz ↦ ?_
    exact (chartCkSeminorm_le_iff _ _ m hm f (apply_nonneg _ _)).mp le_rfl m le_rfl z hz
  · -- A `C^k` seminorm is the maximum of the derivative seminorms of order at most `k`.
    obtain ⟨i, l, k, hk⟩ := j
    rw [LinearMap.id_apply, one_mul, chartExhaustionSeminormFamily_apply]
    refine (chartCkSeminorm_le_iff _ _ k hk f (apply_nonneg _ _)).mpr fun m hmk z hz ↦ ?_
    refine ((chartDerivativeSeminorm_le_iff _ _ m _ f (apply_nonneg _ _)).mp le_rfl z hz).trans ?_
    refine (hnorm i l m _ f).symm.le.trans (Seminorm.le_finset_sup_apply ?_)
    exact Finset.mem_image.mpr ⟨⟨m, Nat.lt_succ_of_le hmk⟩, Finset.mem_univ _, rfl⟩

/-- Countably many charts whose sources cover the manifold, with compact exhaustions of their
targets, make the weak Whitney topology on vector-valued `C^n` maps second countable when the
model space is finite-dimensional and second countable over a complete field and the target is
second countable. -/
theorem secondCountableTopology_chartExhaustion [Countable ι] [CompleteSpace 𝕜]
    [FiniteDimensional 𝕜 E] [SecondCountableTopology E] [SecondCountableTopology F]
    (A : ∀ i, CompactExhaustion (extChartAt I (c i)).target) :
    SecondCountableTopology C^n⟮I, M; 𝓘(𝕜, F), F⟯ :=
  (isInducing_chartExhaustionJet (F := F) (n := n) c hcover A).secondCountableTopology

end Exhaustion

/-- On a sigma-compact manifold with locally compact model over a complete field, the weak Whitney
topology on `C^n` maps into a second-countable normed space is second countable, hence separable.
This holds for every regularity `n` and also on manifolds with boundary or corners. -/
theorem secondCountableTopology_manifoldWeakWhitney_of_sigmaCompact {n : WithTop ℕ∞}
    [IsManifold I n M] [CompleteSpace 𝕜] [LocallyCompactSpace E] [SecondCountableTopology F]
    [SigmaCompactSpace M] :
    SecondCountableTopology C^n⟮I, M; 𝓘(𝕜, F), F⟯ := by
  have := ProperSpace.of_locallyCompactSpace 𝕜 (E := E)
  have := FiniteDimensional.of_locallyCompactSpace 𝕜 (E := E)
  obtain ⟨s, hs, hc, ⟨A⟩⟩ := exists_countable_chartExhaustion (I := I) (M := M)
  have := hs.to_subtype
  exact secondCountableTopology_chartExhaustion (F := F) (n := n) (fun i : s ↦ (i : M)) hc A

scoped[TauCeti.ManifoldWeakWhitney] attribute [instance]
  ContMDiffMap.secondCountableTopology_manifoldWeakWhitney_of_sigmaCompact

end ContMDiffMap
