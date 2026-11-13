/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Equiv
public import TauCeti.Geometry.Manifold.TubularNeighborhood.Riemannian.Coordinates
import TauCeti.Topology.Homotopy.DeformationRetract
import TauCeti.Topology.VectorBundle.ZeroSection

/-!
# Tubular neighbourhoods without a prescribed metric

The intrinsic normal bundle of a smooth embedding between finite-dimensional, boundaryless
real manifolds is diffeomorphic to an open neighbourhood of its image. The neighbourhood
can be chosen inside any prescribed open neighbourhood, and the zero section is sent to
the original embedding. The ambient manifold is Hausdorff and second countable; neither
compactness nor closedness of the image is required.

An auxiliary smooth Riemannian metric is chosen on the ambient tangent bundle using
`TauCeti.nonempty_contMDiffRiemannianMetric`. The Riemannian tubular theorem
`SmoothEmbedding.exists_diffeomorph_normalBundle_riemannian_subset` then supplies the
coordinates. The conclusion uses the intrinsic quotient normal bundle and its existing
complementary-coordinate atlas, both independent of that metric.

Projecting the tubular neighbourhood to the base gives a smooth retraction of an open
neighbourhood of the image onto the embedded manifold
(`TauCeti.SmoothEmbedding.exists_contMDiffOn_retraction`). Transporting the fibrewise
straight-line homotopy `(t, v) ↦ t • v` of the normal bundle (`TauCeti.zeroSectionDeformation`)
along the tubular neighbourhood shows that this neighbourhood strong deformation retracts onto the
image (`TauCeti.SmoothEmbedding.exists_deformation_range`), so the embedding, read as a map into
it, is a homotopy equivalence (`TauCeti.SmoothEmbedding.exists_homotopyEquiv`).

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 6.24.
* M. Hirsch, *Differential Topology*, Chapter 4, Theorem 6.3.
-/

public noncomputable section

open Bundle Manifold Set
open scoped ContDiff Manifold ContinuousMap

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

/-- **Smooth tubular neighbourhood theorem.** The entire intrinsic normal bundle of a
smooth embedding is diffeomorphic to an arbitrarily small open neighbourhood of its image,
with the zero section sent to the embedding. No Riemannian metric is part of the input or
output, and the image need not be closed or compact. -/
theorem exists_diffeomorph_normalBundle_subset
    (f : SmoothEmbedding I J ∞ M N)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E)
    {O : Set N} (hO : IsOpen O) (hfO : range f ⊆ O) :
    let hn : (∞ : ℕ∞ω) ≠ 0 := by simp
    letI := f.normalSpaceFiberBundle hn hdim
    ∃ W : TopologicalSpace.Opens N, (W : Set N) ⊆ O ∧
      ∃ Φ : TotalSpace P (fun x ↦ f.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W,
        ∀ x, (Φ (zeroSection P (fun x ↦ f.NormalSpace x hn) x) : N) = f x := by
  have : LocallyCompactSpace G := J.locallyCompactSpace
  have : LocallyCompactSpace N := ChartedSpace.locallyCompactSpace G N
  obtain ⟨g⟩ := nonempty_contMDiffRiemannianMetric (IB := J) (n := ⊤) (F := V)
    (E := fun y : N ↦ TangentSpace J y)
  let : RiemannianBundle (fun y : N ↦ TangentSpace J y) := ⟨g.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle J ∞ V (fun y : N ↦ TangentSpace J y) :=
    Bundle.instIsContMDiffRiemannianBundle g
  exact f.exists_diffeomorph_normalBundle_riemannian_subset hdim hO hfO

/-- **Smooth retractions onto embedded submanifolds.** A smooth embedding `f : M → N` of a
nonempty boundaryless manifold into a second countable Hausdorff boundaryless manifold has a
smooth retraction `r : N → M` on an open neighbourhood `W` of its image, inside any prescribed
open neighbourhood `O` of the image: `r` is smooth on `W` and `r ∘ f = id`. Outside `W` the
values of `r` are arbitrary. -/
theorem exists_contMDiffOn_retraction [Nonempty M] (f : SmoothEmbedding I J ∞ M N) {O : Set N}
    (hO : IsOpen O) (hfO : range f ⊆ O) :
    ∃ W : Set N, IsOpen W ∧ range f ⊆ W ∧ W ⊆ O ∧
      ∃ r : N → M, ContMDiffOn J I ∞ r W ∧ ∀ x, r (f x) = x := by
  classical
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  let P := EuclideanSpace ℝ (Fin (Module.finrank ℝ V - Module.finrank ℝ E))
  have hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E :=
    finrank_euclideanSpace_fin
  let := f.normalSpaceFiberBundle hn hdim
  -- A tubular neighbourhood `Φ` of `f`; the retraction is its base projection.
  obtain ⟨W, hWO, Φ, hΦ⟩ := f.exists_diffeomorph_normalBundle_subset (P := P) hdim hO hfO
  let r : N → M := fun y ↦ if h : y ∈ W then (Φ.symm ⟨y, h⟩).proj else Classical.arbitrary M
  have hrW (w : W) : r w = (Φ.symm w).proj := by simp [r, w.2]
  have hfW (x : M) : f x ∈ W := by
    rw [← hΦ x]
    exact (Φ _).2
  refine ⟨W, W.isOpen, range_subset_iff.2 hfW, hWO, r, fun y hy ↦ ?_, fun x ↦ ?_⟩
  · have hsmooth : ContMDiff J I ∞ fun w : W ↦ r w := by
      simp only [hrW]
      exact (contMDiff_proj (fun x ↦ f.NormalSpace x hn)).comp Φ.symm.contMDiff
    exact (contMDiffAt_subtype_iff (x := ⟨y, hy⟩).1 (hsmooth _)).contMDiffWithinAt
  · have h : Φ.symm ⟨f x, hfW x⟩ = zeroSection P (fun x ↦ f.NormalSpace x hn) x :=
      Φ.symm_apply_eq.2 (Subtype.ext (hΦ x).symm)
    rw [hrW ⟨f x, hfW x⟩, h, zeroSection_proj]

/-- **Tubular neighbourhoods deformation retract onto the submanifold.** For a smooth embedding
`f : M → N` of a boundaryless manifold into a second countable Hausdorff boundaryless manifold,
every open neighbourhood `O` of the image contains an open neighbourhood `W` of the image which
strong deformation retracts onto it: there is a retraction `r : W → range f` and a homotopy from
`r`, followed by the inclusion, to the identity of `W` that fixes the image of `f` throughout. -/
theorem exists_deformation_range (f : SmoothEmbedding I J ∞ M N) {O : Set N} (hO : IsOpen O)
    (hfO : range f ⊆ O) :
    ∃ W : Set N, IsOpen W ∧ W ⊆ O ∧ ∃ hfW : range f ⊆ W,
      ∃ r : C(W, range f), (∀ y, r (ContinuousMap.inclusion hfW y) = y) ∧
        Nonempty (((ContinuousMap.inclusion hfW).comp r).HomotopyRel (.id W)
          {y | (y : N) ∈ range f}) := by
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  let P := EuclideanSpace ℝ (Fin (Module.finrank ℝ V - Module.finrank ℝ E))
  have hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E :=
    finrank_euclideanSpace_fin
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  obtain ⟨W, hWO, Φ, hΦ⟩ := f.exists_diffeomorph_normalBundle_subset (P := P) hdim hO hfO
  -- The tubular neighbourhood as a homeomorphism `ψ` from the normal bundle onto `W`, and the
  -- straight-line deformation `D` of the normal bundle onto its zero section.
  let ψ := Φ.toHomeomorph
  let D := zeroSectionDeformation ℝ P fun x ↦ f.NormalSpace x hn
  have hfW (x : M) : f x ∈ W := by
    rw [← hΦ x]
    exact (Φ _).2
  have hψ (x : M) (hx : f x ∈ W) :
      ψ.symm ⟨f x, hx⟩ = zeroSection P (fun x ↦ f.NormalSpace x hn) x :=
    ψ.symm_apply_eq.2 (Subtype.ext (hΦ x).symm)
  let r : C(W, range f) := ⟨fun w ↦ ⟨f (ψ.symm w).proj, mem_range_self _⟩,
    (f.isEmbedding.continuous.comp
      ((FiberBundle.continuous_proj P _).comp ψ.symm.continuous)).subtype_mk _⟩
  refine ⟨W, W.isOpen, hWO, range_subset_iff.2 hfW, r, ?_, ⟨?_⟩⟩
  · rintro ⟨_, x, rfl⟩
    exact Subtype.ext (by simp [r, ContinuousMap.inclusion, hψ])
  -- Conjugating `D` by `ψ` gives the deformation of `W`.
  exact
    { toFun := fun p ↦ ψ (D (p.1, ψ.symm p.2))
      continuous_toFun := by fun_prop
      map_zero_left := fun w ↦ Subtype.ext <| by
        simp only [ContinuousMap.coe_mk, ContinuousMap.comp_apply, D, r,
          ContinuousMap.HomotopyWith.apply_zero, ContinuousMap.inclusion]
        exact hΦ (ψ.symm w).proj
      map_one_left := fun w ↦ by simp [D]
      prop' := by
        rintro t ⟨_, hw⟩ ⟨x, rfl⟩
        -- The point lies on the zero section, which `D` fixes.
        refine Subtype.ext ?_
        simp only [ContinuousMap.coe_mk, ContinuousMap.comp_apply, r, ContinuousMap.inclusion,
          hψ x hw, D.eq_fst t (mem_range_self x)]
        exact hΦ x }

/-- **An embedded submanifold is homotopy equivalent to a tubular neighbourhood.** For a smooth
embedding `f : M → N` of a boundaryless manifold into a second countable Hausdorff boundaryless
manifold, every open neighbourhood `O` of the image contains an open neighbourhood `W` of the
image such that `f`, read as a map into `W`, is a homotopy equivalence. -/
theorem exists_homotopyEquiv (f : SmoothEmbedding I J ∞ M N) {O : Set N} (hO : IsOpen O)
    (hfO : range f ⊆ O) :
    ∃ W : Set N, IsOpen W ∧ W ⊆ O ∧ ∃ e : M ≃ₕ W, ∀ x, (e x : N) = f x := by
  obtain ⟨W, hW, hWO, hfW, r, hr, ⟨G⟩⟩ := f.exists_deformation_range hO hfO
  refine ⟨W, hW, hWO,
    f.isEmbedding.toHomeomorph.toHomotopyEquiv.trans
      (ContinuousMap.HomotopyEquiv.ofRetraction hfW r hr G.toHomotopy), fun x ↦ ?_⟩
  simp [ContinuousMap.HomotopyEquiv.trans]

end TauCeti.SmoothEmbedding
