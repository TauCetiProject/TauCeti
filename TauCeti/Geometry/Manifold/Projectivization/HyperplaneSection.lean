/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue.Polynomial
public import TauCeti.LinearAlgebra.Projectivization.ZeroLocus
public import TauCeti.Topology.Algebra.Projectivization

import TauCeti.Geometry.Manifold.ChartedSpace
import TauCeti.Geometry.Manifold.Complex.Compact
import TauCeti.Topology.Algebra.Projectivization.ZeroLocus

/-!
# Hyperplane sections meet every connected component

Let `X ⊆ ℂℙⁿ` be closed and let `H = {x_i = 0}` be a coordinate hyperplane. Its complement is the
standard affine chart `U_i = Projectivization.affineOpen i ≅ ℂⁿ`. Suppose that the image `Z ⊆ ℂⁿ`
of `X \ H` in this chart is a complex manifold of positive dimension whose inclusion into `ℂⁿ` is
holomorphic; nothing is assumed about `X` near `H`, where it may be singular. Then `X ∩ H` meets
every connected component of `X` (`TauCeti.exists_mem_connectedComponentIn_notMem_affineOpen`).
Indeed a component of `X` missing `H` would be compact, and open in the manifold `X \ H ≅ Z`, so
a nonempty compact open subset of a positive-dimensional complex submanifold of `ℂⁿ`, which does
not exist by the maximum modulus principle
(`MDifferentiableOn.eq_empty_of_injOn_of_isCompact_of_isOpen`). Equivalently, the inclusion
`X ∩ H → X` is surjective on connected components: this is the connected-component case of the
Lefschetz hyperplane theorem.

For the zero locus `X = complexProjectiveZeroLocus p` of a finite family `p` of homogeneous
polynomials, the affine part `X \ H = X ∩ U_i` is cut out by the dehomogenized equations
`dehomogenize i (p k)`, and the affine chart restricts to a homeomorphism from `X ∩ U_i` onto the
closed affine algebraic set `affineZeroLocus (dehomogenize i ∘ p) ⊆ ℂⁿ`
(`TauCeti.complexProjectiveZeroLocusAffineOpenHomeomorph`). If the dehomogenized equations have
surjective Jacobian at each of their common zeros, this is a smooth affine complete intersection
of dimension `n - |ι|`, and the theorem applies when there are fewer than `n` equations
(`TauCeti.exists_mem_connectedComponentIn_complexProjectiveZeroLocus_notMem_affineOpen`).
The dimension hypothesis is necessary: the point `[1 : 0 : ⋯ : 0]`, cut out by the `n` linear
equations `x_j = 0` for `j ≠ 0`, does not meet `{x_0 = 0}`.

Every hyperplane becomes a coordinate hyperplane after a linear change of coordinates, under which
zero loci transform by `TauCeti.preimage_map_complexProjectiveZeroLocus`.

## Main declarations

* `TauCeti.exists_mem_connectedComponentIn_notMem_affineOpen`: if `X ⊆ ℂℙⁿ` is closed and
  `X \ H` is a complex submanifold of positive dimension of the affine chart, every connected
  component of `X` meets `H`.
* `TauCeti.exists_mem_connectedComponentIn_complexProjectiveZeroLocus_notMem_affineOpen`: the same
  conclusion for a projective zero locus whose affine part is a smooth complete intersection of
  positive dimension.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Section 7.
-/

public section

open MvPolynomial Set
open scoped LinearAlgebra.Projectivization Manifold

namespace TauCeti

variable {n : ℕ}

/-- **A hyperplane section meets every connected component.** Let `X` be a closed subset of `ℂℙⁿ`
and `H = {x_i = 0}` a coordinate hyperplane. Suppose that the image `Z ⊆ ℂⁿ` of `X \ H` in the
standard affine chart is a complex manifold without isolated points, for instance one of positive
dimension (`ChartedSpace.perfectSpace`), whose inclusion into `ℂⁿ` is holomorphic. Then every
connected component of `X` contains a point of `H`. Nothing is assumed about `X` near `H`. -/
theorem exists_mem_connectedComponentIn_notMem_affineOpen {E G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace G] {I : ModelWithCorners ℂ E G} [I.Boundaryless]
    {X : Set (ℙ ℂ (Fin (n + 1) → ℂ))} (hX : IsClosed X) (i : Fin (n + 1)) {Z : Set (Fin n → ℂ)}
    (hZ : Projectivization.affineChart i '' (X ∩ Projectivization.affineOpen i) = Z)
    [ChartedSpace G Z] [IsManifold I 1 Z] [PerfectSpace Z]
    (hZval : MDifferentiable I 𝓘(ℂ, Fin n → ℂ) (Subtype.val : Z → Fin n → ℂ))
    {L : ℙ ℂ (Fin (n + 1) → ℂ)} (hL : L ∈ X) :
    ∃ L' ∈ connectedComponentIn X L, L' ∉ Projectivization.affineOpen i := by
  set Y := X ∩ Projectivization.affineOpen i
  by_contra! hsub
  have hLY : L ∈ Y := ⟨hL, hsub L (mem_connectedComponentIn hL)⟩
  -- The component of `L` in `X` lies in `Y`, so it is also the component of `L` in `Y`.
  have hC : connectedComponentIn Y L = connectedComponentIn X L :=
    (connectedComponentIn_mono L inter_subset_left).antisymm
      (isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn hL) fun x hx ↦ ⟨connectedComponentIn_subset X L hx, hsub x hx⟩)
  -- It is compact, being a connected component of the compact space `X`.
  have : CompactSpace X := isCompact_iff_compactSpace.1 hX.isCompact
  have hCc : IsCompact (connectedComponentIn X L) := by
    rw [connectedComponentIn_eq_image hL]
    exact isClosed_connectedComponent.isCompact.image continuous_subtype_val
  -- Transport the component of `⟨L, hLY⟩` in `Y` to `Z` through the affine chart.
  let e : Y ≃ₜ Z := (Projectivization.affineOpenPartialHomeomorph i).homeomorphOfImageSubsetSource
    (by simp [Y]) (by simpa using hZ)
  have : LocallyConnectedSpace G := I.toHomeomorph.locallyConnectedSpace
  have : LocallyConnectedSpace Z := ChartedSpace.locallyConnectedSpace G Z
  have : LocallyConnectedSpace Y := e.locallyConnectedSpace
  have hKc : IsCompact (connectedComponent (⟨L, hLY⟩ : Y)) := by
    rw [Subtype.isCompact_iff, ← connectedComponentIn_eq_image hLY, hC]
    exact hCc
  -- Its image is a nonempty compact open subset of `Z`, which cannot exist.
  have hempty := hZval.mdifferentiableOn.eq_empty_of_injOn_of_isCompact_of_isOpen
    Subtype.val_injective.injOn (hKc.image e.continuous) (e.isOpenMap _ isOpen_connectedComponent)
  exact (image_nonempty.2 ⟨_, mem_connectedComponent⟩).ne_empty hempty

section ZeroLocus

variable {ι : Type*} {p : ι → MvPolynomial (Fin (n + 1)) ℂ} {d : ι → ℕ}

/-- **A hyperplane section of a projective zero locus meets every connected component.** Let `X`
be the zero locus in `ℂℙⁿ` of a finite family of homogeneous polynomials, and suppose that the part
of `X` outside the hyperplane `H = {x_i = 0}` is a smooth affine complete intersection of positive
dimension `n - |ι|`: the dehomogenized equations have surjective Jacobian at each of their common
zeros, and there are fewer than `n` of them. Then every connected component of `X` contains a point
of `H`. No smoothness is assumed at the points of `X ∩ H`. -/
theorem exists_mem_connectedComponentIn_complexProjectiveZeroLocus_notMem_affineOpen
    [Fintype ι] (hp : ∀ k, (p k).IsHomogeneous (d k)) (i : Fin (n + 1))
    (hrank : ∀ z ∈ affineZeroLocus fun k ↦ dehomogenize i (p k),
      Function.Surjective (jacobiMatrixAt (fun k ↦ dehomogenize i (p k)) z).mulVec)
    (hcard : Fintype.card ι < n) {L : ℙ ℂ (Fin (n + 1) → ℂ)}
    (hL : L ∈ complexProjectiveZeroLocus p) :
    ∃ L' ∈ connectedComponentIn (complexProjectiveZeroLocus p) L,
      L' ∉ Projectivization.affineOpen i := by
  let _ := affineZeroLocusChartedSpace hrank
  have := isManifold_affineZeroLocus hrank 1
  -- The model `Fin (n - |ι|) → ℂ` of the smooth affine part is nontrivial.
  have : Nonempty (Fin (Fintype.card (Fin n) - Fintype.card ι)) :=
    ⟨⟨0, by rw [Fintype.card_fin]; omega⟩⟩
  have := ChartedSpace.perfectSpace (H := Fin (Fintype.card (Fin n) - Fintype.card ι) → ℂ)
    (X := affineZeroLocus fun k ↦ dehomogenize i (p k))
  exact exists_mem_connectedComponentIn_notMem_affineOpen (isClosed_complexProjectiveZeroLocus p)
    i (image_affineChart_complexProjectiveZeroLocus_inter_affineOpen hp i)
    ((contMDiff_coe_affineZeroLocus hrank 1).mdifferentiable one_ne_zero) hL

end ZeroLocus

end TauCeti
