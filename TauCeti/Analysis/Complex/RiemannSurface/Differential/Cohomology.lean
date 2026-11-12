/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Canonical.Basic
public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Twist
public import TauCeti.Topology.Sheaves.Cech.Colimit
import TauCeti.Analysis.Complex.RiemannSurface.Differential.FiniteDimensional
import TauCeti.Analysis.Complex.RiemannSurface.Differential.Sphere
import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Cohomology

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

The remaining statements only need some meromorphic `1`-form to exist, so they are stated for a
surface with a canonical divisor (`TauCeti.RiemannSurface.IsCanonicalDivisor`). For every
canonical divisor `K` the cohomology of `Ω_D` is that of `𝒪_(D + K)`
(`nonempty_iso_cechCohomology_differentialSheaf_divisorSheaf_add_of_isCanonicalDivisor`);
on the Riemann sphere, `div dz = -2[∞]`, so `Ω_D` has the cohomology of `𝒪_(D - 2[∞])`
(`nonempty_iso_cechCohomology_differentialSheaf_divisorSheaf_add_neg_two_infty`).
A finite holomorphic map to the Riemann sphere supplies a canonical divisor, by pulling back
`dz` (see `TauCeti.Analysis.Complex.RiemannSurface.Differential.RiemannHurwitz`).

Transporting the divisor point-twist results along `Ω_D ≅ 𝒪_(D + K)` gives the point-twist steps of
Riemann–Roch for the sheaves `Ω_D`, whose point-twist sequence `0 → Ω_D → Ω_(D + x) → ℂ_x → 0` is
`TauCeti.RiemannSurface.differentialPointTwistSequence`. On a compact Hausdorff surface with a
canonical divisor, finiteness of `H¹(X, Ω_D)` does not change when a point is added to `D`; if the
surface is moreover connected, adding a point raises `h⁰(Ω_D) - h¹(Ω_D)` by one once `H¹(X, Ω_D)`
is finite-dimensional.

## Main definitions

* `TauCeti.RiemannSurface.differentialSheafCechCohomologyIso`: `Hⁿ(X, Ω_D) ≅ Hⁿ(X, 𝒪_(D + K))`.

## Main results

* `TauCeti.RiemannSurface.finiteDimensional_cechCohomology_zero_differentialSheaf`: `H⁰(X, Ω_D)`
  is finite-dimensional on a compact connected surface.
* `TauCeti.RiemannSurface.finiteDimensional_cechCohomology_one_differentialSheaf_add_point_iff`:
  `H¹(X, Ω_(D + x))` is finite-dimensional if and only if `H¹(X, Ω_D)` is.
* `TauCeti.RiemannSurface.finrank_differentialSheaf_pointTwist_euler_characteristic`:
  `χ(Ω_(D + x)) = χ(Ω_D) + 1` on a compact connected Hausdorff surface.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §§16–17 (the point-twist sequence, the sheaves `Ω_D`, `Ω_D ≅ 𝒪_(D + K)` and their
  cohomology).
-/

public noncomputable section

open CategoryTheory Opposite
open scoped Manifold

namespace TauCeti.RiemannSurface

open _root_.TauCeti.AlgebraicGeometry (WeilDivisor)

universe u

section Iso

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

end Iso

section Canonical

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [CompactSpace X]

/-- **`Hⁿ(X, Ω_D) ≅ Hⁿ(X, 𝒪_(D + K))` for every canonical divisor `K`.** On a compact Riemann
surface, if `K` is the divisor of some `1`-form meromorphic and of finite order everywhere, the
degree `n` Čech cohomology of `Ω_D` is isomorphic to that of the divisor sheaf of `D + K`. -/
theorem nonempty_iso_cechCohomology_differentialSheaf_divisorSheaf_add_of_isCanonicalDivisor
    {K : WeilDivisor X} (hK : IsCanonicalDivisor K) (D : WeilDivisor X) (n : ℕ) :
    Nonempty ((Topology.cechCohomology (TopCat.of X) (ModuleCat.{u} ℂ) n).obj
        (differentialSheaf D).obj ≅
      (Topology.cechCohomology (TopCat.of X) (ModuleCat.{u} ℂ) n).obj
        (divisorSheaf (D + K)).obj) := by
  obtain ⟨ω, hω, hω₀, rfl⟩ := hK.exists_divisor_eq
  exact ⟨differentialSheafCechCohomologyIso ω hω hω₀ D n⟩

end Canonical

section PointTwist

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [CompactSpace X] [T2Space X]

/-- **Finiteness of `H¹(X, Ω_D)` is unchanged by adding a point.** On a compact Hausdorff Riemann
surface with a canonical divisor, `H¹(X, Ω_(D + x))` is finite-dimensional if and only if
`H¹(X, Ω_D)` is. Finiteness is not asserted for any divisor. -/
theorem finiteDimensional_cechCohomology_one_differentialSheaf_add_point_iff
    (hK : ∃ K : WeilDivisor X, IsCanonicalDivisor K) (D : WeilDivisor X) (x : X) :
    FiniteDimensional ℂ ((Topology.cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) 1).obj
        (differentialSheaf (D + WeilDivisor.ofPoint x)).obj) ↔
      FiniteDimensional ℂ ((Topology.cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) 1).obj
        (differentialSheaf D).obj) := by
  classical
  obtain ⟨_, hK⟩ := hK
  obtain ⟨ω, hω, hω₀, -⟩ := hK.exists_divisor_eq
  have h := finiteDimensional_divisorCechCohomology_one_add_point_iff (D + ω.divisor) x
  rw [← add_right_comm D (WeilDivisor.ofPoint x) ω.divisor] at h
  exact (Module.Finite.equiv_iff (differentialSheafCechCohomologyIso ω hω hω₀
      (D + WeilDivisor.ofPoint x) 1).toLinearEquiv).trans
    (h.trans (Module.Finite.equiv_iff
      (differentialSheafCechCohomologyIso ω hω hω₀ D 1).toLinearEquiv).symm)

/-- **The point-twist step of Riemann–Roch for `Ω_D`.** On a compact connected Hausdorff Riemann
surface with a canonical divisor, once `H¹(X, Ω_D)` is finite-dimensional, adding a point raises
`h⁰(Ω_D) - h¹(Ω_D)` by one, where `h⁰` is the dimension of the global sections of `Ω_D` and `h¹`
that of its first Čech cohomology. -/
theorem finrank_differentialSheaf_pointTwist_euler_characteristic [ConnectedSpace X]
    (hK : ∃ K : WeilDivisor X, IsCanonicalDivisor K) (D : WeilDivisor X) (x : X)
    [FiniteDimensional ℂ ((Topology.cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) 1).obj
      (differentialSheaf D).obj)] :
    (Module.finrank ℂ ((differentialSheaf (D + WeilDivisor.ofPoint x)).obj.obj (op ⊤)) : ℤ) -
        Module.finrank ℂ ((Topology.cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) 1).obj
          (differentialSheaf (D + WeilDivisor.ofPoint x)).obj) =
      (Module.finrank ℂ ((differentialSheaf D).obj.obj (op ⊤)) : ℤ) -
        Module.finrank ℂ ((Topology.cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) 1).obj
          (differentialSheaf D).obj) + 1 := by
  classical
  obtain ⟨_, hK⟩ := hK
  obtain ⟨ω, hω, hω₀, -⟩ := hK.exists_divisor_eq
  have : FiniteDimensional ℂ (divisorCechCohomology (D + ω.divisor) 1) :=
    Module.Finite.equiv (differentialSheafCechCohomologyIso ω hω hω₀ D 1).toLinearEquiv
  have h₀ (E : WeilDivisor X) : Module.finrank ℂ ((differentialSheaf E).obj.obj (op ⊤)) =
      Module.finrank ℂ ((divisorSheaf (E + ω.divisor)).obj.obj (op ⊤)) :=
    (((sheafToPresheaf _ _).mapIso
      (differentialSheafIsoDivisorSheafAdd ω hω hω₀ E)).app (op ⊤)).toLinearEquiv.finrank_eq
  rw [h₀, h₀, (differentialSheafCechCohomologyIso ω hω hω₀ D 1).toLinearEquiv.finrank_eq,
    (differentialSheafCechCohomologyIso ω hω hω₀ (D + WeilDivisor.ofPoint x)
      1).toLinearEquiv.finrank_eq,
    add_right_comm D (WeilDivisor.ofPoint x) ω.divisor]
  exact finrank_pointTwist_euler_characteristic (D + ω.divisor) x

end PointTwist

open OnePoint in
/-- **Check on the Riemann sphere.** Since `div dz = -2[∞]`, the sheaf `Ω_D` on `OnePoint ℂ` has
the Čech cohomology of the divisor sheaf of `D - 2[∞]` in every degree. -/
theorem nonempty_iso_cechCohomology_differentialSheaf_divisorSheaf_add_neg_two_infty
    (D : WeilDivisor (OnePoint ℂ)) (n : ℕ) :
    Nonempty ((Topology.cechCohomology (TopCat.of (OnePoint ℂ)) (ModuleCat.{0} ℂ) n).obj
        (differentialSheaf D).obj ≅
      (Topology.cechCohomology (TopCat.of (OnePoint ℂ)) (ModuleCat.{0} ℂ) n).obj
        (divisorSheaf (D + (-2 : ℤ) • WeilDivisor.ofPoint (∞ : OnePoint ℂ))).obj) :=
  nonempty_iso_cechCohomology_differentialSheaf_divisorSheaf_add_of_isCanonicalDivisor
    isCanonicalDivisor_neg_two_infty D n

end TauCeti.RiemannSurface
