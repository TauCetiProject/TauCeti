/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.Defs
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import TauCeti.LinearAlgebra.AffineSpace.MarkingStabilizer
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.DiscreteSubset
import TauCeti.Analysis.Calculus.FDeriv.RestrictScalars

/-!
# Stabilizing sphere components by a transverse target cut

A component of a genus-zero curve with fewer than three special points is not a stable pointed
curve: the Möbius transformations fixing its special points form a positive-dimensional group. In
the virtual constructions of moduli spaces of pseudoholomorphic curves (Pardon) such a component is
stabilized by a *target cut*: a real codimension-two submanifold `D` of the target which the map
`u` of the component meets transversally. The *full* preimage `u⁻¹(D)` is then a finite set, and
it is added to the domain as an *unordered* set of further marked points. The group theory of this
stabilization, for a sphere `K ∪ {∞}` with a special point at `∞`, is in
`TauCeti.LinearAlgebra.AffineSpace.MarkingStabilizer`: the stabilized domain has finitely many
automorphisms (`TauCeti.card_markingStabilizer_dvd_factorial`), and forgetting the cut points does
not change the isotropy of `u` (`TauCeti.markedIsotropy_le_markingStabilizer`), which is therefore
finite of order dividing `|u⁻¹(D)|!` (`TauCeti.card_markedIsotropy_dvd_factorial`) as soon as
`u⁻¹(D)` is finite. This file proves that finiteness for `K = ℂ`.

* **Finiteness of transverse preimages.** The predicate `TauCeti.IsTransverseCutAt u D z` asks
  that near `u z` the set `D` be the zero set of a function `g : X → ℂ` such that `g ∘ u` has an
  invertible real derivative at `z`; no regularity of `g` is required
  (`TauCeti.isTransverseCutAt_iff`). It holds when a smooth map `u` to a manifold is
  transverse at `z` to a codimension-two submanifold `D` with local defining function `g`, that is,
  when `dg ∘ du` is injective (`TauCeti.isTransverseCutAt_of_hasMFDerivAt`); in general it is
  weaker than transversality, and it is exactly what the isolation argument needs. Intersection
  points at which it holds are isolated
  (`TauCeti.IsTransverseCutAt.eventually_notMem`). Hence if `u` is continuous, `D` is closed, `u`
  has a limit `y ∉ D` at `∞` and the predicate holds at every point of `u⁻¹(D)`, the preimage
  `u⁻¹(D)` is finite (`TauCeti.finite_preimage_of_isTransverseCutAt`). The predicate is invariant
  under reparametrization by maps with invertible derivative (`TauCeti.IsTransverseCutAt.comp`),
  in particular under the automorphisms of the sphere fixing `∞`, which have invertible real
  derivatives (`AffineEquiv.hasFDerivAt_restrictScalars`,
  `TauCeti.isTransverseCutAt_comp_affineEquiv_iff`), so it is a property of the unparametrized
  map.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), Section 9.2, on stabilization by the full
  preimage of a codimension-two submanifold transverse to the map.
* K. Cieliebak and K. Mohnke, *Symplectic hypersurfaces and transversality in Gromov–Witten
  theory*, J. Symplectic Geom. 5 (2007), 281–356, on stabilizing domains by the intersection
  points with a hypersurface.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 5.1,
  on stable maps and their automorphisms.
-/

public section

noncomputable section

open Filter Set Topology
open scoped Manifold

namespace TauCeti

/-! ### Transverse target cuts -/

section Transverse

variable {X : Type*} [TopologicalSpace X] {u : ℂ → X} {D : Set X} {z : ℂ}

/-- The transversality condition on the target cut `D` used to stabilize `u` at `z`: near `u z`
the set `D` is the zero set of a function `g : X → ℂ` such that `g ∘ u` has an invertible real
derivative at `z`. The predicate is used at the points `z` of `u⁻¹(D)`. No regularity of `g` is
required, so in general it is weaker than transversality; it holds when a smooth map `u` to a
manifold is transverse at `z` to a codimension-two submanifold `D` with local defining function
`g` (`TauCeti.isTransverseCutAt_of_hasMFDerivAt`), and it is what makes the points of `u⁻¹(D)`
isolated (`TauCeti.IsTransverseCutAt.eventually_notMem`). -/
def IsTransverseCutAt (u : ℂ → X) (D : Set X) (z : ℂ) : Prop :=
  ∃ (g : X → ℂ) (L : ℂ ≃L[ℝ] ℂ), (∀ᶠ x in 𝓝 (u z), x ∈ D ↔ g x = 0) ∧
    HasFDerivAt (g ∘ u) (L : ℂ →L[ℝ] ℂ) z

/-- Unfold `IsTransverseCutAt u D z` into a local defining function `g` of `D` near `u z` and the
invertible real derivative of `g ∘ u` at `z`. -/
theorem isTransverseCutAt_iff :
    IsTransverseCutAt u D z ↔ ∃ (g : X → ℂ) (L : ℂ ≃L[ℝ] ℂ),
      (∀ᶠ x in 𝓝 (u z), x ∈ D ↔ g x = 0) ∧ HasFDerivAt (g ∘ u) (L : ℂ →L[ℝ] ℂ) z :=
  Iff.rfl

/-- Build `IsTransverseCutAt u D z` from a local defining function `g` of `D` near `u z` such that
`g ∘ u` has an invertible real derivative at `z`. -/
theorem IsTransverseCutAt.intro {g : X → ℂ} {L : ℂ ≃L[ℝ] ℂ}
    (hD : ∀ᶠ x in 𝓝 (u z), x ∈ D ↔ g x = 0) (hg : HasFDerivAt (g ∘ u) (L : ℂ →L[ℝ] ℂ) z) :
    IsTransverseCutAt u D z :=
  ⟨g, L, hD, hg⟩

/-- A transverse intersection point of `u` with `D` is isolated: nearby points are not mapped
into `D`. -/
theorem IsTransverseCutAt.eventually_notMem (h : IsTransverseCutAt u D z)
    (hu : ContinuousAt u z) : ∀ᶠ w in 𝓝[≠] z, u w ∉ D := by
  obtain ⟨g, L, hD, hg⟩ := h
  filter_upwards [hg.eventually_ne (c := 0) ⟨_, L.antilipschitzWith⟩,
    nhdsWithin_le_nhds (hu.eventually hD)] with w hw hwD
  exact fun hmem ↦ hw (hwD.1 hmem)

/-- **Finiteness of the full preimage of a transverse cut.** If the sphere component `u`, with a
limit `y ∉ D` at `∞`, meets the closed set `D` transversally at every point of `u⁻¹(D)`, then
`u⁻¹(D)` is finite. -/
theorem finite_preimage_of_isTransverseCutAt {y : X} (hu : Continuous u) (hD : IsClosed D)
    (hy : Tendsto u (cocompact ℂ) (𝓝 y)) (hyD : y ∉ D)
    (h : ∀ z ∈ u ⁻¹' D, IsTransverseCutAt u D z) : (u ⁻¹' D).Finite := by
  obtain ⟨K, hK, hKD⟩ := mem_cocompact.1 (hy (hD.isOpen_compl.mem_nhds hyD))
  refine (hK.of_isClosed_subset (hD.preimage hu) fun z hz ↦ ?_).finite
    (isDiscrete_iff_nhdsNE.2 fun z hz ↦
      inf_principal_eq_bot.2 ((h z hz).eventually_notMem hu.continuousAt))
  by_contra hzK
  exact hKD hzK hz

/-- The predicate is invariant under reparametrization by a map with invertible derivative. -/
theorem IsTransverseCutAt.comp {ρ : ℂ → ℂ} (h : IsTransverseCutAt u D (ρ z)) {E : ℂ ≃L[ℝ] ℂ}
    (hρ : HasFDerivAt ρ (E : ℂ →L[ℝ] ℂ) z) : IsTransverseCutAt (u ∘ ρ) D z := by
  obtain ⟨g, L, hD, hg⟩ := h
  refine ⟨g, E.trans L, hD, ?_⟩
  rw [← ContinuousLinearEquiv.comp_coe]
  exact hg.comp z hρ

/-- `IsTransverseCutAt` is invariant under the automorphisms of the sphere fixing `∞`, so it is a
property of the unparametrized map. -/
theorem isTransverseCutAt_comp_affineEquiv_iff (f : ℂ ≃ᵃ[ℂ] ℂ) :
    IsTransverseCutAt (u ∘ f) D z ↔ IsTransverseCutAt u D (f z) := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.comp (f.hasFDerivAt_restrictScalars ℝ z)⟩
  have h' : IsTransverseCutAt (u ∘ f) D (f.symm (f z)) := by simpa using h
  have hu : (u ∘ f) ∘ f.symm = u := by
    funext w
    simp
  simpa [hu] using h'.comp (f.symm.hasFDerivAt_restrictScalars ℝ (f z))

/-- Transversality of a smooth map `u` from `ℂ` to a manifold to a set `D` with a local defining
function `g` at `u z`: if `d(g ∘ u) = dg ∘ du` is injective at `z`, then `u` meets the target cut
`D` transversally at `z`. -/
theorem isTransverseCutAt_of_hasMFDerivAt {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] {u : ℂ → M} {D : Set M} {g : M → ℂ}
    {dg : TangentSpace I (u z) →L[ℝ] ℂ} {du : ℂ →L[ℝ] TangentSpace I (u z)}
    (hD : ∀ᶠ x in 𝓝 (u z), x ∈ D ↔ g x = 0) (hg : HasMFDerivAt I 𝓘(ℝ, ℂ) g (u z) dg)
    (hu : HasMFDerivAt 𝓘(ℝ, ℂ) I u z du) (hinj : Function.Injective (dg.comp du)) :
    IsTransverseCutAt u D z := by
  refine ⟨g, (LinearEquiv.ofInjectiveEndo (dg.comp du : ℂ →ₗ[ℝ] ℂ) hinj).toContinuousLinearEquiv,
    hD, ?_⟩
  have he : ((LinearEquiv.ofInjectiveEndo (dg.comp du : ℂ →ₗ[ℝ] ℂ) hinj).toContinuousLinearEquiv :
      ℂ →L[ℝ] ℂ) = dg.comp du := by
    ext w
    simp
  rw [he]
  exact hasMFDerivAt_iff_hasFDerivAt.1 (hg.comp z hu)

end Transverse

end TauCeti
