/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Basic
public import TauCeti.Geometry.Manifold.PontryaginThom.Basic
public import TauCeti.Geometry.Manifold.TubularNeighborhood.Existence

/-!
# Framed tubes around framed submanifolds

Let `f : M → N` be a smooth embedding of finite-dimensional boundaryless manifolds, with `N`
Hausdorff and second countable. A **framing** of `f` is a global trivialization
`φ : ν ≅ M × P` of its intrinsic normal bundle `ν`, linear on fibres, with model fibre `P` of the
codimension. Composing the inverse of the framing with the tubular neighbourhood
`ν ≅ W ⊆ N` of `TauCeti.SmoothEmbedding.exists_diffeomorph_normalBundle_subset` gives a framed
tube `M × P → N` around `f` (`TauCeti.SmoothEmbedding.exists_isFramedTube`), inside any
prescribed open neighbourhood of the image of `f`.

So every framed embedding of a compact manifold `M` has a Pontryagin–Thom collapse
`N → OnePoint P` (`TauCeti.pontryaginThomCollapse`), continuous because `M` is compact and `N`
is Hausdorff, with `M` the preimage of the origin. For a closed ambient manifold `N` this is the
collapse of a framed submanifold onto the sphere `Sᵏ = OnePoint ℝᵏ`. Isotopic tubes and
homotopic framings give homotopic collapses
(`TauCeti.pontryaginThomCollapseMap_homotopic`,
`TauCeti.pontryaginThomCollapseMap_comp_prodUnitsHomeomorph_homotopic`).

## Main results

* `TauCeti.SmoothEmbedding.exists_isFramedTube`: a framed smooth embedding admits a framed tube
  inside any open neighbourhood of its image.
* `TauCeti.SmoothEmbedding.exists_pontryaginThomCollapse`: a framed smooth embedding of a compact
  manifold has a continuous collapse onto `OnePoint P` with the image as the preimage of the
  origin.

## References

* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia,
  1965, §7.
* M. Hirsch, *Differential Topology*, Chapter 4, Theorem 6.3 (tubular neighbourhoods).
-/

public section

open Bundle Set Topology
open scoped ContDiff Manifold

namespace TauCeti.SmoothEmbedding

variable {E V P H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [T2Space N] [SecondCountableTopology N]

/-- **Framed tubes exist.** A smooth embedding `f : M → N` whose intrinsic normal bundle is framed
by a global fibrewise linear trivialization `φ` with fibre `P` admits a framed tube
`τ : M × P → N` around `f` with image inside any prescribed open neighbourhood `O` of the image of
`f`. The tube is the inverse of the framing followed by a tubular neighbourhood of `f`. -/
theorem exists_isFramedTube (f : SmoothEmbedding I J ∞ M N) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E)
    (φ : Trivialization P (π P fun x ↦ f.NormalSpace x hn)) [φ.IsLinear ℝ]
    (hφ : φ.baseSet = univ) {O : Set N} (hO : IsOpen O) (hfO : range f ⊆ O) :
    ∃ τ : M × P → N, IsFramedTube f τ ∧ range τ ⊆ O := by
  let := f.normalSpaceFiberBundle hn hdim
  obtain ⟨W, hWO, Φ, hΦ⟩ := f.exists_diffeomorph_normalBundle_subset (P := P) hdim hO hfO
  have hbase (x : M) : x ∈ φ.baseSet := hφ ▸ mem_univ x
  -- With base set `univ`, the framing is a homeomorphism of the whole total space onto `M × P`.
  let ψ := φ.toOpenPartialHomeomorph.toHomeomorphOfSourceEqUnivTargetEqUniv
    (by rw [φ.source_eq, hφ, preimage_univ]) (by rw [φ.target_eq, hφ, univ_prod_univ])
  have hψ (x : M) : ψ.symm (x, 0) = zeroSection P (fun x ↦ f.NormalSpace x hn) x := by
    have h0 : φ.symm x 0 = 0 := by
      rw [← φ.symmₗ_apply (R := ℝ) (hbase x)]
      exact map_zero _
    rw [OpenPartialHomeomorph.toHomeomorphOfSourceEqUnivTargetEqUniv_symm_apply,
      ← φ.mk_symm (hbase x), h0, zeroSection]
  refine ⟨fun p ↦ (Φ (ψ.symm p) : N), ⟨?_, fun x ↦ ?_⟩, ?_⟩
  · exact W.isOpen.isOpenEmbedding_subtypeVal.comp
      (Φ.toHomeomorph.isOpenEmbedding.comp ψ.symm.isOpenEmbedding)
  · simp only [hψ]
    exact hΦ x
  · rintro _ ⟨p, rfl⟩
    exact hWO (Φ (ψ.symm p)).2

/-- **The Pontryagin–Thom collapse of a framed submanifold.** A framed smooth embedding `f` of a
compact manifold has a continuous map `c : N → OnePoint P` that sends exactly the image of `f` to
the origin and every point outside a prescribed open neighbourhood `O` of that image to `∞`. The
statement records only these two properties; the map constructed is the Pontryagin–Thom collapse
of the framed tube given by `TauCeti.SmoothEmbedding.exists_isFramedTube`, which is the way to
access the tube itself. -/
theorem exists_pontryaginThomCollapse [CompactSpace M] (f : SmoothEmbedding I J ∞ M N)
    (hn : (∞ : ℕ∞ω) ≠ 0) (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E)
    (φ : Trivialization P (π P fun x ↦ f.NormalSpace x hn)) [φ.IsLinear ℝ]
    (hφ : φ.baseSet = univ) {O : Set N} (hO : IsOpen O) (hfO : range f ⊆ O) :
    ∃ c : C(N, OnePoint P), (∀ y, c y = (0 : P) ↔ y ∈ range f) ∧ ∀ y ∉ O, c y = OnePoint.infty := by
  obtain ⟨τ, hτ, hτO⟩ := f.exists_isFramedTube hn hdim φ hφ hO hfO
  refine ⟨pontryaginThomCollapseMap hτ.isOpenEmbedding, fun y ↦ ?_, fun y hy ↦ ?_⟩
  · rw [coe_pontryaginThomCollapseMap]
    exact hτ.pontryaginThomCollapse_eq_zero_iff
  · rw [coe_pontryaginThomCollapseMap]
    exact pontryaginThomCollapse_of_notMem_range fun h ↦ hy (hτO h)

end TauCeti.SmoothEmbedding
