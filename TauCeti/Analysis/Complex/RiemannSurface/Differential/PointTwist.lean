/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Twist
public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.PointTwist

/-!
# The point-twist sequence of differential sheaves

Let `ω` be a `1`-form on a compact Riemann surface `X` which is meromorphic and of finite order
everywhere. Division by `ω` identifies the sheaf `Ω_D` of meromorphic `1`-forms with divisor at
least `-D` with the divisor sheaf `𝒪_(D + div ω)`
(`TauCeti.RiemannSurface.differentialSheafIsoDivisorSheafAdd`), naturally in `D`
(`TauCeti.RiemannSurface.differentialSheafMapOfLE_comp_differentialSheafIsoDivisorSheafAdd_hom`).

Transporting the point-twist sequence `0 → 𝒪_(D + K) → 𝒪_(D + K + x) → ℂ_x → 0` of divisor
sheaves along these isomorphisms, for `K = div ω`, gives the short exact sequence
`0 → Ω_D → Ω_(D + x) → ℂ_x → 0`
(`TauCeti.RiemannSurface.differentialPointTwistSequence_shortExact`). Its consequences for the
Čech cohomology of `Ω_D`, the point-twist steps of Riemann–Roch for the sheaves `Ω_D`, are in
`TauCeti.Analysis.Complex.RiemannSurface.Differential.Cohomology`.

## Main definitions

* `TauCeti.RiemannSurface.differentialSheafIsoDivisorSheafAddOfPoint`: the isomorphism
  `Ω_(D + x) ≅ 𝒪_(D + div ω + x)`.
* `TauCeti.RiemannSurface.differentialPointTwistSequence`: the sequence
  `Ω_D → Ω_(D + x) → ℂ_x`.
* `TauCeti.RiemannSurface.differentialPointTwistSequenceIso`: its isomorphism, by division by `ω`,
  with the point-twist sequence of `𝒪_(D + div ω)`.

## Main results

* `TauCeti.RiemannSurface.differentialPointTwistSequence_shortExact`: it is short exact.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §§16–17 (the point-twist sequence, the sheaves `Ω_D` and `Ω_D ≅ 𝒪_(D + K)`).
-/

public noncomputable section

open CategoryTheory Filter Opposite TopologicalSpace Topology
open scoped Manifold

namespace TauCeti.RiemannSurface

open _root_.TauCeti.AlgebraicGeometry (WeilDivisor)

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [CompactSpace X] (ω : OneForm X) (hω : ∀ x, ω.MeromorphicAt x) (hω₀ : ∀ x, ω.order x ≠ ⊤)
  (D : WeilDivisor X) (x : X)

/-- **`Ω_(D + x) ≅ 𝒪_(D + div ω + x)`.** On a compact surface, division by a `1`-form `ω`
meromorphic and of finite order everywhere identifies `Ω_(D + x)` with the divisor sheaf of
`D + div ω + x`, the point twist of the divisor sheaf `𝒪_(D + div ω) ≅ Ω_D`. It is
`TauCeti.RiemannSurface.differentialSheafIsoDivisorSheafAdd` at `D + x`, followed by the equality
`D + x + div ω = D + div ω + x`. -/
def differentialSheafIsoDivisorSheafAddOfPoint :
    differentialSheaf (D + WeilDivisor.ofPoint x) ≅
      divisorSheaf (D + ω.divisor + WeilDivisor.ofPoint x) :=
  differentialSheafIsoDivisorSheafAdd ω hω hω₀ (D + WeilDivisor.ofPoint x) ≪≫
    eqToIso (congrArg divisorSheaf (add_right_comm D (WeilDivisor.ofPoint x) ω.divisor))

/-- `Ω_(D + x) ≅ 𝒪_(D + div ω + x)` is `Ω_(D + x) ≅ 𝒪_(D + x + div ω)` followed by the equality
`D + x + div ω = D + div ω + x`. -/
theorem differentialSheafIsoDivisorSheafAddOfPoint_def :
    differentialSheafIsoDivisorSheafAddOfPoint ω hω hω₀ D x =
      differentialSheafIsoDivisorSheafAdd ω hω hω₀ (D + WeilDivisor.ofPoint x) ≪≫
        eqToIso (congrArg divisorSheaf (add_right_comm D (WeilDivisor.ofPoint x) ω.divisor)) :=
  (rfl)

/-- Off a closed discrete set, a section `η` of `Ω_(D + x)` and its image `η / ω` in
`𝒪_(D + div ω + x)` satisfy `(η / ω) ω = η`. -/
theorem differentialSheafIsoDivisorSheafAddOfPoint_hom_app_smul (U : Opens X)
    (s : (differentialSheaf (D + WeilDivisor.ofPoint x)).obj.obj (op U)) :
    ∀ᶠ y in codiscrete U,
      (divisorSheafSectionsEquiv (D + ω.divisor + WeilDivisor.ofPoint x) U
        ((differentialSheafIsoDivisorSheafAddOfPoint ω hω hω₀ D x).hom.hom.app (op U) s)).1 y •
          ω y = (differentialSheafSectionsEquiv (D + WeilDivisor.ofPoint x) U s).1 y := by
  rw [differentialSheafIsoDivisorSheafAddOfPoint_def]
  generalize add_right_comm D (WeilDivisor.ofPoint x) ω.divisor = h
  generalize D + ω.divisor + WeilDivisor.ofPoint x = E at h ⊢
  subst h
  simpa using differentialSheafIsoDivisorSheafAdd_hom_app_smul hω hω₀ U s

/-- Off a closed discrete set, the inverse of `differentialSheafIsoDivisorSheafAddOfPoint` sends a
section `f` of `𝒪_(D + div ω + x)` to `f ω`. -/
theorem differentialSheafIsoDivisorSheafAddOfPoint_inv_app (U : Opens X)
    (f : (divisorSheaf (D + ω.divisor + WeilDivisor.ofPoint x)).obj.obj (op U)) :
    ∀ᶠ y in codiscrete U,
      (differentialSheafSectionsEquiv (D + WeilDivisor.ofPoint x) U
        ((differentialSheafIsoDivisorSheafAddOfPoint ω hω hω₀ D x).inv.hom.app (op U) f)).1 y =
        (divisorSheafSectionsEquiv (D + ω.divisor + WeilDivisor.ofPoint x) U f).1 y • ω y := by
  rw [differentialSheafIsoDivisorSheafAddOfPoint_def]
  generalize add_right_comm D (WeilDivisor.ofPoint x) ω.divisor = h at f ⊢
  generalize D + ω.divisor + WeilDivisor.ofPoint x = E at h f ⊢
  subst h
  simpa using differentialSheafIsoDivisorSheafAdd_inv_app hω hω₀ U f

/-- Division by `ω` carries the inclusion `Ω_D ⟶ Ω_(D + x)` to the inclusion
`𝒪_(D + div ω) ⟶ 𝒪_(D + div ω + x)`. -/
@[reassoc]
theorem differentialSheafMapOfLE_comp_differentialSheafIsoDivisorSheafAddOfPoint_hom :
    differentialSheafMapOfLE (WeilDivisor.le_add_ofPoint D x) ≫
        (differentialSheafIsoDivisorSheafAddOfPoint ω hω hω₀ D x).hom =
      (differentialSheafIsoDivisorSheafAdd ω hω hω₀ D).hom ≫
        divisorSheafMapOfLE (WeilDivisor.le_add_ofPoint (D + ω.divisor) x) := by
  rw [differentialSheafIsoDivisorSheafAddOfPoint_def, Iso.trans_hom, eqToIso.hom,
    differentialSheafMapOfLE_comp_differentialSheafIsoDivisorSheafAdd_hom_assoc]
  congr 1
  have key : ∀ (E : WeilDivisor X) (h : D + WeilDivisor.ofPoint x + ω.divisor = E)
      (h₁ : D + ω.divisor ≤ D + WeilDivisor.ofPoint x + ω.divisor) (h₂ : D + ω.divisor ≤ E),
      divisorSheafMapOfLE h₁ ≫ eqToHom (congrArg divisorSheaf h) = divisorSheafMapOfLE h₂ := by
    rintro _ rfl _ _
    rw [eqToHom_refl, Category.comp_id]
  exact key _ (add_right_comm D (WeilDivisor.ofPoint x) ω.divisor) _ _

variable [∀ U : Opens X, Decidable (x ∈ U)]

/-- **The point-twist sequence `Ω_D → Ω_(D + x) → ℂ_x` of differential sheaves.** The first map
is the inclusion; the second divides by `ω` and extracts the newly allowed coefficient at `x` of
the resulting section of `𝒪_(D + div ω + x)` (`TauCeti.RiemannSurface.pointTwistMap`). The body
is exposed so that downstream statements can name its objects and maps. -/
@[expose] def differentialPointTwistSequence :
    ShortComplex (TopCat.Sheaf (ModuleCat.{u} ℂ) (TopCat.of X)) :=
  ShortComplex.mk (differentialSheafMapOfLE (WeilDivisor.le_add_ofPoint D x))
    ((differentialSheafIsoDivisorSheafAddOfPoint ω hω hω₀ D x).hom ≫
      pointTwistMap (D + ω.divisor) x) (by
        rw [differentialSheafMapOfLE_comp_differentialSheafIsoDivisorSheafAddOfPoint_hom_assoc,
          divisorSheafMapOfLE_comp_pointTwistMap, Limits.comp_zero])

/-- The first object of the differential point-twist sequence is `Ω_D`. -/
@[simp]
theorem differentialPointTwistSequence_X₁ :
    (differentialPointTwistSequence ω hω hω₀ D x).X₁ = differentialSheaf D :=
  (rfl)

/-- The middle object of the differential point-twist sequence is `Ω_(D + x)`. -/
@[simp]
theorem differentialPointTwistSequence_X₂ :
    (differentialPointTwistSequence ω hω hω₀ D x).X₂ =
      differentialSheaf (D + WeilDivisor.ofPoint x) :=
  (rfl)

/-- The final object of the differential point-twist sequence is the skyscraper sheaf `ℂ_x`. -/
@[simp]
theorem differentialPointTwistSequence_X₃ :
    (differentialPointTwistSequence ω hω hω₀ D x).X₃ =
      skyscraperSheaf (X := TopCat.of X) x (ModuleCat.of ℂ (ULift.{u} ℂ)) :=
  (rfl)

/-- The first map of the differential point-twist sequence is the inclusion `Ω_D ⟶ Ω_(D + x)`. -/
@[simp]
theorem differentialPointTwistSequence_f :
    (differentialPointTwistSequence ω hω hω₀ D x).f =
      differentialSheafMapOfLE (WeilDivisor.le_add_ofPoint D x) :=
  (rfl)

/-- The second map of the differential point-twist sequence is division by `ω` followed by
extraction of the new coefficient at `x`. -/
@[simp]
theorem differentialPointTwistSequence_g :
    (differentialPointTwistSequence ω hω hω₀ D x).g =
      (differentialSheafIsoDivisorSheafAddOfPoint ω hω hω₀ D x).hom ≫
        pointTwistMap (D + ω.divisor) x :=
  (rfl)

/-- The differential point-twist sequence is isomorphic, by division by `ω`, to the point-twist
sequence `𝒪_(D + div ω) → 𝒪_(D + div ω + x) → ℂ_x` of divisor sheaves. -/
def differentialPointTwistSequenceIso :
    differentialPointTwistSequence ω hω hω₀ D x ≅ ShortComplex.mk
      (divisorSheafMapOfLE (WeilDivisor.le_add_ofPoint (D + ω.divisor) x))
      (pointTwistMap (D + ω.divisor) x) (divisorSheafMapOfLE_comp_pointTwistMap _ x) :=
  ShortComplex.isoMk (differentialSheafIsoDivisorSheafAdd ω hω hω₀ D)
    (differentialSheafIsoDivisorSheafAddOfPoint ω hω hω₀ D x) (Iso.refl _)
    (differentialSheafMapOfLE_comp_differentialSheafIsoDivisorSheafAddOfPoint_hom
      ω hω hω₀ D x).symm
    (Category.comp_id _).symm

/-- On `Ω_D`, the isomorphism of point-twist sequences is `Ω_D ≅ 𝒪_(D + div ω)`. -/
@[simp]
theorem differentialPointTwistSequenceIso_hom_τ₁ :
    (differentialPointTwistSequenceIso ω hω hω₀ D x).hom.τ₁ =
      (differentialSheafIsoDivisorSheafAdd ω hω hω₀ D).hom :=
  (rfl)

/-- On `Ω_(D + x)`, the isomorphism of point-twist sequences is `Ω_(D + x) ≅ 𝒪_(D + div ω + x)`. -/
@[simp]
theorem differentialPointTwistSequenceIso_hom_τ₂ :
    (differentialPointTwistSequenceIso ω hω hω₀ D x).hom.τ₂ =
      (differentialSheafIsoDivisorSheafAddOfPoint ω hω hω₀ D x).hom :=
  (rfl)

/-- On `ℂ_x`, the isomorphism of point-twist sequences is the identity. -/
@[simp]
theorem differentialPointTwistSequenceIso_hom_τ₃ :
    (differentialPointTwistSequenceIso ω hω hω₀ D x).hom.τ₃ = 𝟙 _ :=
  (rfl)

/-- On `𝒪_(D + div ω)`, the inverse isomorphism of point-twist sequences is multiplication by `ω`,
the inverse of `Ω_D ≅ 𝒪_(D + div ω)`. -/
@[simp]
theorem differentialPointTwistSequenceIso_inv_τ₁ :
    (differentialPointTwistSequenceIso ω hω hω₀ D x).inv.τ₁ =
      (differentialSheafIsoDivisorSheafAdd ω hω hω₀ D).inv :=
  (rfl)

/-- On `𝒪_(D + div ω + x)`, the inverse isomorphism of point-twist sequences is multiplication by
`ω`, the inverse of `Ω_(D + x) ≅ 𝒪_(D + div ω + x)`. -/
@[simp]
theorem differentialPointTwistSequenceIso_inv_τ₂ :
    (differentialPointTwistSequenceIso ω hω hω₀ D x).inv.τ₂ =
      (differentialSheafIsoDivisorSheafAddOfPoint ω hω hω₀ D x).inv :=
  (rfl)

/-- On `ℂ_x`, the inverse isomorphism of point-twist sequences is the identity. -/
@[simp]
theorem differentialPointTwistSequenceIso_inv_τ₃ :
    (differentialPointTwistSequenceIso ω hω hω₀ D x).inv.τ₃ = 𝟙 _ :=
  (rfl)

/-- **The point-twist sequence `0 → Ω_D → Ω_(D + x) → ℂ_x → 0` is short exact** on a compact
Riemann surface carrying a `1`-form `ω` meromorphic and of finite order everywhere. -/
theorem differentialPointTwistSequence_shortExact :
    (differentialPointTwistSequence ω hω hω₀ D x).ShortExact :=
  ShortComplex.shortExact_of_iso (differentialPointTwistSequenceIso ω hω hω₀ D x).symm
    (ShortComplex.shortExact_of_iso (pointTwistSequenceIso (D + ω.divisor) x)
      (pointTwistSequence_shortExact (D + ω.divisor) x))

end TauCeti.RiemannSurface
