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
# Homotopy invariance and zero maps for `K₀` of C⋆-algebras

Let `A` and `B` be C⋆-algebras, possibly without unit, and let `φ_t : A → B` be a family of star
homomorphisms indexed by a preconnected space `X` (for instance the unit interval) that is
**pointwise continuous**: `t ↦ φ_t(a)` is continuous for every `a`. For a matrix projection `p`
over `A`, the entrywise images `φ_t(p)` form a continuous family of projections, so any two of them
are Murray–von Neumann equivalent (`Continuous.isMurrayVonNeumannEquivalent`). Hence all the
`φ_t` induce the same homomorphism on the projection monoid `V(A)`
(`TauCeti.ProjectionMonoid.map_eq_of_continuous`) and on its Grothendieck group
(`TauCeti.ProjectionKZero.map_eq_of_continuous`).

The unitizations `φ_t⁺ : A⁺ → B⁺` are again pointwise continuous in `t`, so the same holds for the
operator `K₀`-group `K₀(A) = ker (K₀(A⁺) → K₀(ℂ))`: **homotopic star homomorphisms induce the same
homomorphism** `K₀(A) → K₀(B)` (`TauCeti.UnitizationKZero.map_eq_of_continuous`).

The **zero homomorphism** `A → B` induces the zero map on `K₀`
(`TauCeti.UnitizationKZero.map_zero`), for star algebras over any commutative star ring: its
unitization factors through the augmentation `A⁺ → R`, which kills `K₀(A)`.

## Main statements

* `TauCeti.ProjectionMonoid.map_eq_of_continuous`, `TauCeti.ProjectionKZero.map_eq_of_continuous`:
  homotopy invariance on `V(A)` and its Grothendieck group.
* `TauCeti.UnitizationKZero.map_eq_of_continuous`: homotopy invariance of `K₀`.
* `TauCeti.UnitizationKZero.map_zero`: the zero homomorphism induces zero on `K₀`.
-/

public section

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
  {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

namespace ProjectionMonoid

/-- **Homotopy invariance on `V(A)`.** A pointwise continuous family `φ` of star homomorphisms
between C⋆-algebras, indexed by a preconnected space, induces the same homomorphism of projection
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
of star homomorphisms between C⋆-algebras, indexed by a preconnected space, induces the same
homomorphism `ProjectionKZero A →+ ProjectionKZero B` at any two parameters. -/
theorem map_eq_of_continuous {φ : X → A →⋆ₙ+* B} (hφ : ∀ a, Continuous fun t ↦ φ t a)
    (x y : X) : map (φ x) = map (φ y) :=
  Algebra.GrothendieckAddGroup.addHom_ext fun v ↦ by
    rw [map_of, map_of, ProjectionMonoid.map_eq_of_continuous hφ x y]

end ProjectionKZero

namespace UnitizationKZero

/-- **Homotopy invariance of `K₀`.** A pointwise continuous family `φ` of star homomorphisms
between C⋆-algebras, possibly without unit, indexed by a preconnected space, induces the same
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

namespace UnitizationKZero

variable {R A B : Type*} [CommSemiring R] [StarRing R] [NonUnitalSemiring A] [StarRing A]
  [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]
  [NonUnitalSemiring B] [StarRing B] [Module R B] [IsScalarTower R B B] [SMulCommClass R B B]
  [StarModule R B]

/-- **Zero maps.** The zero homomorphism `A → B` induces the zero homomorphism on `K₀`: its
unitization is the augmentation `A⁺ → R` followed by the scalar inclusion `R → B⁺`. -/
@[simp]
theorem map_zero : map (0 : A →⋆ₙₐ[R] B) = 0 := by
  have h : NonUnitalStarRingHom.ofClass (Unitization.starMap (0 : A →⋆ₙₐ[R] B)) =
      (NonUnitalStarRingHom.ofClass (StarAlgHom.ofId R (Unitization R B))).comp
        (NonUnitalStarRingHom.ofClass (Unitization.fstStarAlgHom R A)) :=
    NonUnitalStarRingHom.ext fun u ↦ by ext <;> simp
  ext v
  rw [coe_map, h, ProjectionKZero.map_comp, AddMonoidHom.comp_apply, ← augmentation_def,
    ← inl_def, (mem_iff _).1 v.property, _root_.map_zero, AddMonoidHom.zero_apply,
    ZeroMemClass.coe_zero]

end UnitizationKZero

end TauCeti
