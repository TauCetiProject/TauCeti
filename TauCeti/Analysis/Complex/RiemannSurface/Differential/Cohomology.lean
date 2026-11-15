/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Twist
public import TauCeti.Topology.Sheaves.Cech.Colimit
import TauCeti.Analysis.Complex.RiemannSurface.Differential.FiniteDimensional

/-!
# Čech cohomology of differential sheaves

Let `ω` be a `1`-form on a compact Riemann surface `X` which is meromorphic and of finite order
everywhere, and let `K = div ω`. Division by `ω` identifies the sheaf `Ω_D` of meromorphic
`1`-forms with divisor at least `-D` with the divisor sheaf `𝒪_(D + K)`
(`TauCeti.RiemannSurface.differentialSheafIsoDivisorSheafAdd`). Čech cohomology is a functor of
the coefficient presheaf, so this isomorphism of sheaves induces isomorphisms
`Hⁿ(X, Ω_D) ≅ Hⁿ(X, 𝒪_(D + K))` in every degree `n`
(`TauCeti.RiemannSurface.differentialSheafCechCohomologyIso`). These are the identifications
through which Serre duality `H¹(X, 𝒪_D)^* ≅ H⁰(X, Ω_(-D))` and `h⁰(K) = dim H¹(X, 𝒪)` pass between
differentials and divisor sheaves.

In degree `0` the isomorphism is the map of global sections `η ↦ η / ω`, read through the
identification of degree `0` Čech cohomology of a sheaf with its global sections; this is
`TauCeti.Topology.cechCohomologyZeroIso_hom_naturality` after rewriting with
`TauCeti.RiemannSurface.differentialSheafCechCohomologyIso_hom`. In particular `H⁰(X, Ω_D)` is
finite-dimensional on a compact connected surface, with no nonzero meromorphic `1`-form assumed
to exist
(`TauCeti.RiemannSurface.finiteDimensional_cechCohomology_zero_differentialSheaf`). That a
nonzero meromorphic `1`-form exists is not proved here, so `ω` is a hypothesis throughout.

## Main definitions

* `TauCeti.RiemannSurface.differentialSheafCechCohomologyIso`: `Hⁿ(X, Ω_D) ≅ Hⁿ(X, 𝒪_(D + K))`.

## Main results

* `TauCeti.RiemannSurface.finiteDimensional_cechCohomology_zero_differentialSheaf`: `H⁰(X, Ω_D)`
  is finite-dimensional on a compact connected surface.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §17 (the sheaves `Ω_D`, `Ω_D ≅ 𝒪_(D + K)` and their cohomology).
-/

public noncomputable section

open CategoryTheory
open scoped Manifold

namespace TauCeti.RiemannSurface

open _root_.TauCeti.AlgebraicGeometry (WeilDivisor)

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [CompactSpace X]

/-- **`Hⁿ(X, Ω_D) ≅ Hⁿ(X, 𝒪_(D + div ω))`.** On a compact Riemann surface, a `1`-form `ω` which
is meromorphic and of finite order everywhere identifies the degree `n` Čech cohomology of the
sheaf `Ω_D` with that of the divisor sheaf of `D + div ω`. It is the map induced on Čech
cohomology by division by `ω` (`TauCeti.RiemannSurface.differentialSheafIsoDivisorSheafAdd`). -/
def differentialSheafCechCohomologyIso (ω : OneForm X) (hω : ∀ x, ω.MeromorphicAt x)
    (hω₀ : ∀ x, ω.order x ≠ ⊤) (D : WeilDivisor X) (n : ℕ) :
    (Topology.cechCohomology (TopCat.of X) (ModuleCat.{u} ℂ) n).obj (differentialSheaf D).obj ≅
      (Topology.cechCohomology (TopCat.of X) (ModuleCat.{u} ℂ) n).obj
        (divisorSheaf (D + ω.divisor)).obj :=
  (Topology.cechCohomology (TopCat.of X) (ModuleCat.{u} ℂ) n).mapIso
    ((sheafToPresheaf _ _).mapIso (differentialSheafIsoDivisorSheafAdd ω hω hω₀ D))

variable {ω : OneForm X} (hω : ∀ x, ω.MeromorphicAt x) (hω₀ : ∀ x, ω.order x ≠ ⊤)
  (D : WeilDivisor X)

/-- The isomorphism `Hⁿ(X, Ω_D) ≅ Hⁿ(X, 𝒪_(D + div ω))` is the map induced on Čech cohomology by
the isomorphism of sheaves `Ω_D ≅ 𝒪_(D + div ω)`. -/
@[simp]
theorem differentialSheafCechCohomologyIso_hom (n : ℕ) :
    (differentialSheafCechCohomologyIso ω hω hω₀ D n).hom =
      (Topology.cechCohomology (TopCat.of X) (ModuleCat.{u} ℂ) n).map
        (differentialSheafIsoDivisorSheafAdd ω hω hω₀ D).hom.hom :=
  (rfl)

/-- The inverse of `Hⁿ(X, Ω_D) ≅ Hⁿ(X, 𝒪_(D + div ω))` is the map induced on Čech cohomology by
multiplication by `ω`, the inverse of `Ω_D ≅ 𝒪_(D + div ω)`. -/
@[simp]
theorem differentialSheafCechCohomologyIso_inv (n : ℕ) :
    (differentialSheafCechCohomologyIso ω hω hω₀ D n).inv =
      (Topology.cechCohomology (TopCat.of X) (ModuleCat.{u} ℂ) n).map
        (differentialSheafIsoDivisorSheafAdd ω hω hω₀ D).inv.hom :=
  (rfl)

/-- **`H⁰(X, Ω_D)` is finite-dimensional.** On a compact connected Riemann surface the degree `0`
Čech cohomology of `Ω_D` is finite-dimensional for every divisor `D`, since it is the space of
global sections of `Ω_D`. No nonzero meromorphic `1`-form is assumed to exist. -/
instance finiteDimensional_cechCohomology_zero_differentialSheaf [ConnectedSpace X] :
    FiniteDimensional ℂ
      ((Topology.cechCohomology (TopCat.of X) (ModuleCat.{u} ℂ) 0).obj
        (differentialSheaf D).obj) :=
  Module.Finite.equiv (Topology.cechCohomologyZeroIso (differentialSheaf D)).toLinearEquiv

end TauCeti.RiemannSurface
