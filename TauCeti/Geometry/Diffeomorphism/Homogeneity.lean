/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import TauCeti.Geometry.Diffeomorphism.Action
public import TauCeti.Topology.ConnectedComponents
import TauCeti.Geometry.Manifold.Diffeomorph.ClopenSwap
import TauCeti.Geometry.Manifold.Diffeomorph.PointMotion
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset

/-!
# Orbits of the diffeomorphism group

The orbits of the group of `C^m` self-diffeomorphisms of a finite-dimensional boundaryless `C^m`
manifold `M` are open and closed for any `1 ≤ m`. Near each point, cut-off translations in a chart
move it to every nearby point (`TauCeti.exists_contMDiff_family_apply_eq`), and unlike flows of
vector fields they lose no derivative, so no further smoothness of `M` is needed. In particular the
diffeomorphism group of a connected manifold acts transitively.

On a disconnected manifold the orbit of a point `x₀` is the union of the connected components
diffeomorphic to the component of `x₀`. A diffeomorphism of `M` restricts to a diffeomorphism
between the components of a point and of its image (`Diffeomorph.subtype`). Conversely, a
diffeomorphism between two distinct components extends to `M` by acting as its inverse on the
target component and as the identity elsewhere (`Diffeomorph.clopenSwap`), and within one component
the orbit is everything because orbits are open and closed. Components are open because manifolds
are locally connected (`ModelWithCorners.locallyPathConnectedSpace_of_chartedSpace`).

## Main results

* `TauCeti.isOpen_orbit_diffeomorph`: the orbits of the diffeomorphism group are open.
* `TauCeti.isClopen_orbit_diffeomorph`: the orbits of the diffeomorphism group are open and
  closed.
* `TauCeti.orbit_diffeomorph_eq_univ`: on a connected manifold, the diffeomorphism group acts
  transitively.
* `TauCeti.mem_orbit_diffeomorph_iff`: a point `y` lies in the orbit of `x₀` exactly when the
  connected component of `y` is diffeomorphic to the connected component of `x₀`.
* `TauCeti.orbit_diffeomorph_eq_iUnion`: the orbit of `x₀` is the union of the connected
  components diffeomorphic to the component of `x₀`.

## References

* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia
  (1965), §4, Homogeneity Lemma.
-/

public section

noncomputable section

open Set MulAction
open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] {m : ℕ∞} [IsManifold I m M]

/-- The orbits of the diffeomorphism group of a finite-dimensional boundaryless manifold are
open. -/
theorem isOpen_orbit_diffeomorph (hm : 1 ≤ m) (x₀ : M) : IsOpen (orbit (M ≃ₘ^m⟮I, I⟯ M) x₀) := by
  refine isOpen_iff_forall_mem_open.2 ?_
  rintro _ ⟨g, rfl⟩
  obtain ⟨U, hU, hgU, -, S, f, -, -, -, -, hS, -, -⟩ :=
    exists_contMDiff_family_apply_eq (I := I) hm isOpen_univ (mem_univ (g • x₀))
  refine ⟨U, fun z hz ↦ ⟨S (f z) * g, ?_⟩, hU, hgU⟩
  dsimp only
  rw [mul_smul, Diffeomorph.smul_def (S (f z)), hS z hz]

/-- The orbits of the diffeomorphism group of a finite-dimensional boundaryless manifold are open
and closed. -/
theorem isClopen_orbit_diffeomorph (hm : 1 ≤ m) (x₀ : M) :
    IsClopen (orbit (M ≃ₘ^m⟮I, I⟯ M) x₀) :=
  ⟨isClosed_orbit_of_forall_isOpen_orbit (isOpen_orbit_diffeomorph hm) x₀,
    isOpen_orbit_diffeomorph hm x₀⟩

/-- **Transitivity.** The diffeomorphism group of a connected finite-dimensional boundaryless
manifold acts transitively. -/
theorem orbit_diffeomorph_eq_univ [PreconnectedSpace M] (hm : 1 ≤ m) (x₀ : M) :
    orbit (M ≃ₘ^m⟮I, I⟯ M) x₀ = univ :=
  (isClopen_orbit_diffeomorph (I := I) hm x₀).eq_univ ⟨x₀, mem_orbit_self x₀⟩

section Components

variable [LocallyConnectedSpace M]

/-- **Orbits on a disconnected manifold.** A point `y` lies in the orbit of `x₀` under the group of
`C^m` self-diffeomorphisms exactly when the connected component of `y` is `C^m` diffeomorphic to the
connected component of `x₀`, both carrying the charts restricted from `M`. The local connectedness
of `M`, needed for its components to be open submanifolds, holds for every manifold
(`ModelWithCorners.locallyPathConnectedSpace_of_chartedSpace`). -/
theorem mem_orbit_diffeomorph_iff (hm : 1 ≤ m) {x₀ y : M} :
    y ∈ orbit (M ≃ₘ^m⟮I, I⟯ M) x₀ ↔
      Nonempty ((ConnectedComponents.mk y).opens ≃ₘ^m⟮I, I⟯ (ConnectedComponents.mk x₀).opens) := by
  refine ⟨?_, fun ⟨φ⟩ ↦ ?_⟩
  · -- A diffeomorphism `g` maps the component of `x₀` onto the component of `g x₀`.
    rintro ⟨g, rfl⟩
    have h_iff (z : M) : z ∈ (ConnectedComponents.mk x₀).opens ↔
        g z ∈ (ConnectedComponents.mk (g x₀)).opens := by
      simp only [ConnectedComponents.mem_opens]
      refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
      · simpa using congrArg g.continuous.connectedComponentsMap h
      · simpa using congrArg g.symm.continuous.connectedComponentsMap h
    exact ⟨(g.subtype h_iff).symm⟩
  -- The open and closed orbit of `x₀` contains the whole component of `x₀`.
  have hsub : connectedComponent x₀ ⊆ orbit (M ≃ₘ^m⟮I, I⟯ M) x₀ :=
    (isClopen_orbit_diffeomorph (I := I) hm x₀).connectedComponent_subset (mem_orbit_self x₀)
  by_cases hyx : ConnectedComponents.mk y = ConnectedComponents.mk x₀
  · exact hsub (ConnectedComponents.coe_eq_coe'.1 hyx)
  · -- Otherwise swap the two components along `φ`, which moves `y` into the component of `x₀`.
    have hUV : Disjoint (ConnectedComponents.mk y).opens (ConnectedComponents.mk x₀).opens :=
      ConnectedComponents.pairwise_disjoint_opens hyx
    let g := Diffeomorph.clopenSwap φ (ConnectedComponents.isClopen_opens _).1
      (ConnectedComponents.isClopen_opens _).1 hUV
    let y' : (ConnectedComponents.mk y).opens := ⟨y, ConnectedComponents.mem_opens.2 rfl⟩
    have hgy : g y = φ y' := Diffeomorph.clopenSwap_apply_coe_left φ _ _ hUV y'
    obtain ⟨h, hh : h • x₀ = φ y'⟩ :=
      hsub (ConnectedComponents.coe_eq_coe'.1 (ConnectedComponents.mem_opens.1 (φ y').2))
    refine ⟨g⁻¹ * h, ?_⟩
    dsimp only
    rw [mul_smul, hh, ← hgy]
    exact inv_smul_smul g y

/-- **The orbit of a point of a disconnected manifold** is the union of the connected components
`C^m` diffeomorphic to the component of the point. -/
theorem orbit_diffeomorph_eq_iUnion (hm : 1 ≤ m) (x₀ : M) :
    orbit (M ≃ₘ^m⟮I, I⟯ M) x₀ = ⋃ (C : ConnectedComponents M)
      (_ : Nonempty (C.opens ≃ₘ^m⟮I, I⟯ (ConnectedComponents.mk x₀).opens)), (C.opens : Set M) := by
  ext y
  simp only [mem_iUnion, SetLike.mem_coe, ConnectedComponents.mem_opens, exists_prop,
    exists_eq_right', mem_orbit_diffeomorph_iff hm]

end Components

end TauCeti
