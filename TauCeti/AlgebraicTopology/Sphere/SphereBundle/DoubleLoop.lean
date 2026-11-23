/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Homotopy.ConnectedMap
public import TauCeti.AlgebraicTopology.Sphere.DoubleTangentCircle
public import TauCeti.Topology.MappingSpace.Sphere.ConnectedMap
public import TauCeti.Topology.VectorBundle.SphereBundle.Fiber

/-!
# Double loops of a sphere bundle over a highly connected base

Let `Q = S(E)` be the unit sphere bundle of a real vector bundle `E → B` whose fibre norm is
continuous, and let `S(E_b) ⊆ Q` be the sphere of the fibre over a point `b` of the base. If
`π_j(B, b)` is trivial for every `j ≤ n + k`, the inclusion `S(E_b) → Q` is `(n + k)`-connected
(`TauCeti.isNConnected_sphereBundleFiberIncl`), so the induced map of based mapping spaces
`Map_*(Sᵏ, S(E_b)) → Map_*(Sᵏ, Q)` is `n`-connected and induces isomorphisms on singular homology
with any coefficients in every degree `m < n`
(`TauCeti.isIso_singularHomologyMap_basedMapMap_sphereBundleFiberIncl`), and surjections for
`m ≤ n` (`TauCeti.epi_singularHomologyMap_basedMapMap_sphereBundleFiberIncl`). For `k = 2` these
are the double loop spaces `Ω²S(E_b) → Ω²Q`.

This is how Barraud–Damian–Humilière–Oancea (proof of Proposition 6.23) carry a nonvanishing class
of the double loop space of a sphere into the double loop space of a sphere bundle. With fibres
`Sᴺ`:

* for `N` even over a `2N`-connected base, the comparison holds in degrees `m ≤ 2N − 3`, which
  contains the degree of the class of Proposition 6.17;
* for a base that is `(N + 1)`-connected, it holds in degrees `m ≤ N − 2`. Over a point `x` of the
  fibre sphere `S(E_b)` carrying two orthonormal tangent fields `u`, `v`, the based two-spheres of
  Example 6.20 form a map `Σₓ → Map_*(S², S(E_b))` from a sphere of dimension `N − 2` which
  induces an isomorphism on `H_{N-2}(-; ℤ)` (Proposition 6.21,
  `TauCeti.isIso_singularHomologyFunctor_map_twoFieldSphereFamilyFiber`). Included into `Q`, these
  two-spheres still induce an isomorphism `H_{N-2}(Σₓ; ℤ) ≅ H_{N-2}(Map_*(S², Q); ℤ)`
  (`TauCeti.isIso_singularHomologyMap_basedMapMap_comp_twoFieldSphereFamilyFiber`): the class of
  the fibre `Σₓ` is a generator of `H_{N-2}(Ω²Q; ℤ) ≅ ℤ`.

## Main results

* `TauCeti.isIso_singularHomologyMap_basedMapMap_sphereBundleFiberIncl`,
  `TauCeti.epi_singularHomologyMap_basedMapMap_sphereBundleFiberIncl`: over a highly connected
  base, the based sphere maps into a fibre sphere and into the sphere bundle have the same
  homology in a range.
* `TauCeti.isIso_singularHomologyMap_basedMapMap_comp_twoFieldSphereFamilyFiber`: the based
  two-spheres over a point of a fibre sphere with two orthonormal tangent fields, included into a
  sphere bundle over an `(N + 1)`-connected base, generate `H_{N-2}(Map_*(S², Q); ℤ)`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.2, Example 6.20 and
  Propositions 6.21 and 6.23.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1.
-/

public section

open AlgebraicTopology Bundle CategoryTheory Metric Module
open scoped Topology Topology.Homotopy

namespace TauCeti

universe w

section BasedMap

variable {B : Type w} [TopologicalSpace B] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  (E : B → Type w) [TopologicalSpace (TotalSpace F E)] [∀ b, NormedAddCommGroup (E b)]
  [∀ b, NormedSpace ℝ (E b)] [FiberBundle F E] [VectorBundle ℝ F E] {b : B} {n k : ℕ} [NeZero k]
  (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) (x : sphere (0 : E b) 1) (R : Type w)
  [Ring R]

/-- **Based sphere maps into a sphere bundle over a highly connected base.** If `π_j(B, b)` is
trivial for every `j ≤ n + k`, the inclusion of the sphere of the fibre over `b` induces
isomorphisms `H_m(Map_*(Sᵏ, S(E_b)); R) ≅ H_m(Map_*(Sᵏ, S(E)); R)` in every degree `m < n`, at
every base point of the fibre sphere and with any coefficients. For `k = 2` these are the double
loop spaces. -/
theorem isIso_singularHomologyMap_basedMapMap_sphereBundleFiberIncl
    (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.snd‖)
    (hB : ∀ j ≤ n + k, Subsingleton (π_ j B b))
    {m : ℕ} (hm : m < n) :
    IsIso (((singularHomologyFunctor (ModuleCat.{w} R) m).obj (ModuleCat.of R R)).map
      (TopCat.ofHom (BasedMap.mapContinuousMap (B := sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1)
        (b₀ := s₀) (x := x) (sphereBundleFiberIncl F E b) rfl))) :=
  ((isNConnected_sphereBundleFiberIncl hnorm hB).basedMapMap rfl s₀).isIso_singularHomologyMap
    R hm

/-- If `π_j(B, b)` is trivial for every `j ≤ n + k`, the inclusion of the sphere of the fibre over
`b` induces surjections `H_m(Map_*(Sᵏ, S(E_b)); R) → H_m(Map_*(Sᵏ, S(E)); R)` in every degree
`m ≤ n`. -/
theorem epi_singularHomologyMap_basedMapMap_sphereBundleFiberIncl
    (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.snd‖)
    (hB : ∀ j ≤ n + k, Subsingleton (π_ j B b))
    {m : ℕ} (hm : m ≤ n) :
    Epi (((singularHomologyFunctor (ModuleCat.{w} R) m).obj (ModuleCat.of R R)).map
      (TopCat.ofHom (BasedMap.mapContinuousMap (B := sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1)
        (b₀ := s₀) (x := x) (sphereBundleFiberIncl F E b) rfl))) :=
  ((isNConnected_sphereBundleFiberIncl hnorm hB).basedMapMap rfl s₀).epi_singularHomologyMap
    R hm

end BasedMap

section TwoFieldFamily

variable {B : Type} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type} [TopologicalSpace (TotalSpace F E)] [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] [FiberBundle F E] [VectorBundle ℝ F E] {b : B}
  {u v : sphere (0 : E b) 1 → E b}
  (h : ∀ x : sphere (0 : E b) 1, Orthonormal ℝ ![(x : E b), u x, v x]) (hu : Continuous u)
  (hv : Continuous v)

/-- **The two-spheres over a point of a fibre generate the homology of the double loops of a sphere
bundle** (Barraud–Damian–Humilière–Oancea, Proposition 6.21 carried into a sphere bundle as in the
proof of Proposition 6.23). Let `E → B` be a real vector bundle with continuous fibre norm whose
fibre `E_b` has dimension `N + 1 ≥ 5`, and suppose `π_j(B, b)` is trivial for every `j ≤ N + 1`.
Let `u`, `v` be continuous tangent fields on the fibre sphere `S(E_b) = Sᴺ`, orthonormal at every
point. Over every point `x` of `S(E_b)`, the based two-spheres `Σₓ → Map_*(S², S(E_b))` of
Example 6.20, included into the sphere bundle, give a map `Σₓ → Map_*(S², S(E))` which induces an
isomorphism `H_{N-2}(Σₓ; ℤ) ≅ H_{N-2}(Map_*(S², S(E)); ℤ)`. As `Σₓ` is a sphere of dimension
`N − 2`, its fundamental class goes to a generator of `H_{N-2}(Ω²S(E); ℤ) ≅ ℤ`. -/
theorem isIso_singularHomologyMap_basedMapMap_comp_twoFieldSphereFamilyFiber
    (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.snd‖) {m : ℕ} (hE : finrank ℝ (E b) = m + 5)
    (hB : ∀ j ≤ m + 5, Subsingleton (π_ j B b)) (x : sphere (0 : E b) 1) :
    IsIso (((singularHomologyFunctor (ModuleCat.{0} ℤ) (m + 2)).obj (ModuleCat.of ℤ ℤ)).map
      (TopCat.ofHom ((BasedMap.mapContinuousMap (sphereBundleFiberIncl F E b) rfl).comp
        (twoFieldSphereFamilyFiber h hu hv x)))) := by
  have := isIso_singularHomologyFunctor_map_twoFieldSphereFamilyFiber h hu hv hE x
  have := isIso_singularHomologyMap_basedMapMap_sphereBundleFiberIncl F E (n := m + 3) (k := 2)
    Sphere2.north x ℤ hnorm hB (m := m + 2) (by omega)
  rw [TopCat.ofHom_comp, Functor.map_comp]
  infer_instance

end TwoFieldFamily

end TauCeti
