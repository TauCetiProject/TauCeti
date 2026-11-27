/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Unitization
public import TauCeti.Analysis.CStarAlgebra.Projection.Perturbation
public import TauCeti.LinearAlgebra.Matrix.ProjectionMonoid.Unitization.Basic

/-!
# Homotopy invariance of `K₀` of C⋆-algebras

Let `B` be a C⋆-algebra, possibly without unit, and let `φ_t : A → B` be a family of star
homomorphisms out of a star algebra `A`, indexed by a preconnected space `X` (for instance the unit
interval), that is **pointwise continuous**: `t ↦ φ_t(a)` is continuous for every `a`. For a matrix
projection `p` over `A`, the entrywise images `φ_t(p)` form a continuous family of projections over
`B`, so any two of them are Murray–von Neumann equivalent
(`Continuous.isMurrayVonNeumannEquivalent`). Hence all the `φ_t` induce the same homomorphism on
the projection monoid `V(A)` (`TauCeti.ProjectionMonoid.map_eq_of_continuous`) and on its
Grothendieck group (`TauCeti.ProjectionKZero.map_eq_of_continuous`).

The unitizations `φ_t⁺ : A⁺ → B⁺` are again pointwise continuous in `t`, so the same holds for the
`K₀`-group `K₀(A) = ker (K₀(A⁺) → K₀(ℂ))`: **homotopic star homomorphisms induce the same
homomorphism** `K₀(A) → K₀(B)` (`TauCeti.UnitizationKZero.map_eq_of_continuous`).

## Main statements

* `TauCeti.ProjectionMonoid.map_eq_of_continuous`, `TauCeti.ProjectionKZero.map_eq_of_continuous`:
  homotopy invariance on `V(A)` and its Grothendieck group.
* `TauCeti.UnitizationKZero.map_eq_of_continuous`: homotopy invariance of `K₀`.
-/

public section

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
  {B : Type*} [NonUnitalCStarAlgebra B]

section

variable {A : Type*} [NonUnitalSemiring A] [StarRing A]

namespace ProjectionMonoid

/-- **Homotopy invariance on `V(A)`.** A pointwise continuous family `φ` of star homomorphisms
into a C⋆-algebra, indexed by a preconnected space, induces the same homomorphism of projection
monoids at any two parameters. -/
theorem map_eq_of_continuous {φ : X → A →⋆ₙ+* B} (hφ : ∀ a, Continuous fun t ↦ φ t a)
    (x y : X) : map (φ x) = map (φ y) := by
  ext v
  induction v using ProjectionMonoid.ind with
  | mk k p hp =>
    rw [map_mk, map_mk]
    refine mk_eq_mk (Continuous.isMurrayVonNeumannEquivalent (f := fun t ↦ p.map (φ t))
      (continuous_pi fun i ↦ continuous_pi fun j ↦ hφ (p i j))
      (fun t ↦ hp.matrix_map (φ t)) x y)

end ProjectionMonoid

namespace ProjectionKZero

/-- **Homotopy invariance on the Grothendieck group of `V(A)`.** A pointwise continuous family `φ`
of star homomorphisms into a C⋆-algebra, indexed by a preconnected space, induces the same
homomorphism `ProjectionKZero A →+ ProjectionKZero B` at any two parameters. -/
theorem map_eq_of_continuous {φ : X → A →⋆ₙ+* B} (hφ : ∀ a, Continuous fun t ↦ φ t a)
    (x y : X) : map (φ x) = map (φ y) :=
  Algebra.GrothendieckAddGroup.addHom_ext fun v ↦ by
    rw [map_of, map_of, ProjectionMonoid.map_eq_of_continuous hφ x y]

end ProjectionKZero

end

namespace UnitizationKZero

variable {A : Type*} [NonUnitalSemiring A] [StarRing A] [Module ℂ A] [IsScalarTower ℂ A A]
  [SMulCommClass ℂ A A] [StarModule ℂ A]

/-- **Homotopy invariance of `K₀`.** A pointwise continuous family `φ` of star homomorphisms
into a C⋆-algebra, possibly without unit, indexed by a preconnected space, induces the same
homomorphism `K₀(A) →+ K₀(B)` at any two parameters. -/
theorem map_eq_of_continuous {φ : X → A →⋆ₙₐ[ℂ] B} (hφ : ∀ a, Continuous fun t ↦ φ t a)
    (x y : X) : map (φ x) = map (φ y) := by
  -- The unitizations `(r, a) ↦ (r, φ t a)` are pointwise continuous in `t`.
  have h : ∀ u : Unitization ℂ A,
      Continuous fun t ↦ NonUnitalStarRingHom.ofClass (Unitization.starMap (φ t)) u := by
    intro u
    refine Unitization.continuous_iff.2 ⟨?_, ?_⟩
    · simpa [Unitization.fst_starMap] using continuous_const
    · simpa [Unitization.snd_starMap] using hφ u.snd
  ext v
  rw [coe_map, coe_map, ProjectionKZero.map_eq_of_continuous h x y]

end UnitizationKZero

end TauCeti
