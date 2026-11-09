/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Sphere.HomotopyGroup
public import TauCeti.Topology.Homotopy.HomotopyGroup.LoopSpace
public import TauCeti.Topology.MappingSpace.Sphere.Basic
public import TauCeti.Topology.PathComponent

/-!
# Path components of based mapping spaces out of spheres

For `k ≥ 1`, the set of path components of the based mapping space `Map_*(S^k, X)`, with the
compact-open topology, is the homotopy group `π_k(X, x)`: two based maps are joined by a path in
`Map_*(S^k, X)` exactly when they are based homotopic. This reads the homeomorphism
`TauCeti.basedMapSphereHomeomorph : Map_*(S^k, X) ≃ₜ Ω^ (Fin k) X x` on path components and
composes it with the identification `HomotopyGroup.zerothHomotopyEquiv` of `π_k(X, x)` with the
path components of the space of generalized loops. It is natural in `X`.

For `X = Sⁿ` with `n ≥ 2`, the computation `πₙ(Sⁿ) ≅ ℤ` then gives `π₀ Map_*(Sⁿ, Sⁿ) ≅ ℤ`, in
particular `π₀ Map_*(S², S²) ≅ ℤ`.

## Main declarations

* `TauCeti.zerothHomotopyBasedMapSphereEquiv`: `π₀ Map_*(S^k, X) ≃ π_k(X, x)` for `k ≥ 1`,
  natural in `X` by `TauCeti.zerothHomotopyBasedMapSphereEquiv_map`.
* `TauCeti.zerothHomotopyBasedMapSphereSelfEquivInt`: `π₀ Map_*(Sⁿ, Sⁿ) ≃ ℤ` for `n ≥ 2`, given an
  orthonormal basis of `ℝⁿ⁺¹`, which fixes the sign.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter I.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.
-/

public section

noncomputable section

open Metric Topology.Homotopy

namespace TauCeti

section Maps

variable (k : ℕ) [NeZero k] {X : Type*} [TopologicalSpace X] (x : X)
  (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1)

/-- **The path components of `Map_*(S^k, X)` are the homotopy group `π_k(X, x)`.** For `k ≥ 1`,
the path component of a based map `f : S^k → X` corresponds to the homotopy class of the
generalized loop `z ↦ f (sphereCollapse z)`. -/
def zerothHomotopyBasedMapSphereEquiv :
    ZerothHomotopy (BasedMap (sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) X s₀ x) ≃
      HomotopyGroup (Fin k) X x :=
  (basedMapSphereHomeomorph k x s₀).zerothHomotopyCongr.trans HomotopyGroup.zerothHomotopyEquiv

/-- The path component of a based map `f` corresponds to the class of its generalized loop
`basedMapSphereHomeomorph k x s₀ f`. -/
@[simp]
theorem zerothHomotopyBasedMapSphereEquiv_mk
    (f : BasedMap (sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) X s₀ x) :
    zerothHomotopyBasedMapSphereEquiv k x s₀ (.mk f) = ⟦basedMapSphereHomeomorph k x s₀ f⟧ := by
  rw [zerothHomotopyBasedMapSphereEquiv, Equiv.trans_apply, Homeomorph.zerothHomotopyCongr_mk]
  exact HomotopyGroup.zerothHomotopyEquiv_mk _

/-- The class of a generalized loop `p` corresponds to the path component of the based map
`(basedMapSphereHomeomorph k x s₀).symm p`. -/
@[simp]
theorem zerothHomotopyBasedMapSphereEquiv_symm_mk (p : Ω^ (Fin k) X x) :
    (zerothHomotopyBasedMapSphereEquiv k x s₀).symm (⟦p⟧ : HomotopyGroup (Fin k) X x) =
      .mk ((basedMapSphereHomeomorph k x s₀).symm p) :=
  (Equiv.symm_apply_eq _).2 <| by
    rw [zerothHomotopyBasedMapSphereEquiv_mk, Homeomorph.apply_symm_apply]

/-- **Two based maps `S^k → X` are joined by a path in `Map_*(S^k, X)` exactly when they are
homotopic relative to the basepoint**, in the cubical form: their generalized loops are homotopic
relative to the boundary of the cube. -/
theorem joined_iff_homotopic_basedMapSphereHomeomorph
    {f g : BasedMap (sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) X s₀ x} :
    Joined f g ↔ GenLoop.Homotopic (basedMapSphereHomeomorph k x s₀ f)
      (basedMapSphereHomeomorph k x s₀ g) := by
  rw [GenLoop.homotopic_iff_joined, Homeomorph.joined_iff]

/-- The identification `π₀ Map_*(S^k, X) ≃ π_k(X, x)` is natural in `X`: postcomposition by a
based map `g : X → Y` corresponds to the map `g` induces on homotopy groups. -/
theorem zerothHomotopyBasedMapSphereEquiv_map {Y : Type*} [TopologicalSpace Y] {y : Y}
    (g : C(X, Y)) (hg : g x = y)
    (f : BasedMap (sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) X s₀ x) :
    zerothHomotopyBasedMapSphereEquiv k y s₀ (.mk (BasedMap.map g hg f)) =
      HomotopyGroup.map g hg (zerothHomotopyBasedMapSphereEquiv k x s₀ (.mk f)) := by
  rw [zerothHomotopyBasedMapSphereEquiv_mk, zerothHomotopyBasedMapSphereEquiv_mk,
    basedMapSphereHomeomorph_map, HomotopyGroup.map_mk]

end Maps

section Sphere

variable (n : ℕ) (b : OrthonormalBasis (Fin (n + 3)) ℝ (EuclideanSpace ℝ (Fin (n + 3))))
  (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1)

/-- **`π₀ Map_*(Sᵐ, Sᵐ) ≅ ℤ` for `m ≥ 2`.** The path components of the space of based self-maps
of the sphere `S^(n+2) ⊆ ℝ^(n+3)` are in bijection with `ℤ`, through `π_(n+2)(S^(n+2)) ≅ ℤ`
(`TauCeti.homotopyGroupSphereAddEquiv`); the orthonormal basis `b` fixes the sign. For `n = 0`
this is `π₀ Map_*(S², S²) ≅ ℤ`. -/
def zerothHomotopyBasedMapSphereSelfEquivInt :
    ZerothHomotopy (BasedMap (sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1)
      (sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1) s₀ s₀) ≃ ℤ :=
  (zerothHomotopyBasedMapSphereEquiv (n + 2) s₀ s₀).trans
    (Additive.ofMul.trans (homotopyGroupSphereAddEquiv b s₀).toEquiv)

/-- The integer of a path component of based self-maps of the sphere is the image of the
corresponding element of `π_(n+2)(S^(n+2))` under `TauCeti.homotopyGroupSphereAddEquiv`; by
`TauCeti.zerothHomotopyBasedMapSphereEquiv_mk`, for the component of `f` this element is the class
of the generalized loop of `f`. -/
@[simp]
theorem zerothHomotopyBasedMapSphereSelfEquivInt_apply
    (c : ZerothHomotopy (BasedMap (sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1)
      (sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1) s₀ s₀)) :
    zerothHomotopyBasedMapSphereSelfEquivInt n b s₀ c =
      homotopyGroupSphereAddEquiv b s₀
        (Additive.ofMul (zerothHomotopyBasedMapSphereEquiv (n + 2) s₀ s₀ c)) := by
  rw [zerothHomotopyBasedMapSphereSelfEquivInt, Equiv.trans_apply, Equiv.trans_apply,
    AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe]

end Sphere

end TauCeti
