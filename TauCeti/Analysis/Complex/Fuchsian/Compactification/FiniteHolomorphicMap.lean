/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Elliptic.LocalMultiplicity
public import TauCeti.Analysis.Complex.RiemannSurface.Degree
import TauCeti.Analysis.Complex.Fuchsian.Compactification.Fiber

/-!
# Bundled finite holomorphic maps of compactified Fuchsian quotients

A finite-index inclusion of discrete projective subgroups induces a finite holomorphic map of
compactified quotients. This file bundles the canonical quotient map for the generic degree,
divisor, and ramification APIs. Its forward function and composition law agree with the existing
unbundled maps. No compactness hypothesis is needed for the bundle; composition uses the compact
source hypothesis of the generic finite holomorphic map API.

The local elliptic model used to prove nonconstancy follows Farkas--Kra, *Riemann Surfaces*,
Chapter I, §§4--5.
-/

public noncomputable section

open Filter Function Set Topology UpperHalfPlane
open Subgroup Subgroup.CompactifiedQuotient TauCeti.RiemannSurface
open scoped Manifold MatrixGroups

namespace TauCeti.Fuchsian

variable {Δ Γ : Subgroup PSL(2, ℝ)} [DiscreteTopology Γ]

/-- The finite holomorphic map of compactified quotients induced by a finite-index inclusion.
Its forward function is the ordinary map on interior orbits and cusp orbits. No compactness
hypothesis is needed to construct it. -/
def compactifiedQuotientFiniteHolomorphicMap (h : Δ ≤ Γ) [Δ.IsFiniteRelIndex Γ] :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    FiniteHolomorphicMap Δ.CompactifiedQuotient Γ.CompactifiedQuotient := by
  let : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  refine
    { toFun := compactifiedQuotientMap h
      holomorphic := mdifferentiable_compactifiedQuotientMap h
      finite_fiber := fun y ↦ by
        have hs : {x | compactifiedQuotientMap h x = y}.Finite :=
          Set.finite_coe_iff.mp (finite_fiber_compactifiedQuotientMap h y)
        simpa only [preimage, mem_singleton_iff] using hs
      nonconstant := ?_ }
  classical
  have : Nonempty Γ.CompactifiedQuotient := ⟨ofQuotient (Quotient.mk'' UpperHalfPlane.I)⟩
  let x : Δ.CompactifiedQuotient := ofQuotient (Quotient.mk'' UpperHalfPlane.I)
  have hpos : 0 < localMultiplicity (compactifiedQuotientMap h) x := by
    rw [localMultiplicity_compactifiedQuotientMap_ofQuotient_eq_ellipticRamificationIndex]
    exact ellipticRamificationIndex_pos h _
  have hne := (localMultiplicity_pos_iff
    (.of_forall (mdifferentiable_compactifiedQuotientMap h))).mp hpos
  by_contra hn
  push Not at hn
  exact hne (eventuallyConst_iff_exists_eventuallyEq.mpr
    ⟨compactifiedQuotientMap h x, .of_forall fun y ↦ hn y x⟩)

/-- The bundled map has exactly the canonical compactified quotient map as its forward function. -/
@[simp]
theorem coe_compactifiedQuotientFiniteHolomorphicMap (h : Δ ≤ Γ) [Δ.IsFiniteRelIndex Γ] :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    ⇑(compactifiedQuotientFiniteHolomorphicMap h) = compactifiedQuotientMap h :=
  (rfl)

variable (h : Δ ≤ Γ) [Δ.IsFiniteRelIndex Γ]
variable [hcompact : letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  CompactSpace Δ.CompactifiedQuotient]

/-- Bundled finite holomorphic maps compose along subgroup towers, so generic divisor
functoriality and ramification chain rules apply to the canonical quotient maps. -/
@[simp]
theorem compactifiedQuotientFiniteHolomorphicMap_comp {Θ : Subgroup PSL(2, ℝ)} [DiscreteTopology Θ]
    (k : Γ ≤ Θ) [Γ.IsFiniteRelIndex Θ] :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    letI : Δ.IsFiniteRelIndex Θ := (inferInstance : Δ.IsFiniteRelIndex Γ).trans inferInstance
    (compactifiedQuotientFiniteHolomorphicMap k).comp
        (compactifiedQuotientFiniteHolomorphicMap h) =
      compactifiedQuotientFiniteHolomorphicMap (h.trans k) := by
  let : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  let : Δ.IsFiniteRelIndex Θ := (inferInstance : Δ.IsFiniteRelIndex Γ).trans inferInstance
  apply FiniteHolomorphicMap.ext
  intro x
  simp

end TauCeti.Fuchsian
