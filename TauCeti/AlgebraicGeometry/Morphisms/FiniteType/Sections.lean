/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.GlobalSections
public import TauCeti.AlgebraicGeometry.Morphisms.FiniteType.Basic

import TauCeti.AlgebraicGeometry.AffineScheme.Basic

/-!
# Coordinate rings on affine opens of locally finite-type schemes

For a scheme `X` locally of finite type over `Spec R`, the sections `Γ(X, U)` over every affine
open `U` form a finitely generated `R`-algebra with respect to `X.baseRingToStructurePresheaf R`.
In a cartesian square over `Spec S ⟶ Spec R`, this combines with the base-change pushout on
section rings to give both the algebra pushout and the finite-type structure over `R`.

## Main results

* `TauCeti.AlgebraicGeometry.finiteType_sections_of_locallyOfFiniteType`: `Γ(X, U)` is a finitely
  generated `R`-algebra for every affine open `U` of `X` locally of finite type over `Spec R`.
* `TauCeti.AlgebraicGeometry.with_finiteType_algebraIsPushout_of_isPullback`: continuation-passing
  helper installing the section-ring algebra structures, scalar towers, pushout, finite type,
  and affine-chart identities on an affine open in a pullback square over `Spec S ⟶ Spec R`.
-/

public section

universe u

namespace TauCeti.AlgebraicGeometry

open CategoryTheory _root_.AlgebraicGeometry Opposite

/-- If `X` is locally of finite type over `Spec R`, then the ring of functions `Γ(X, U)` on every
affine open `U` is a finitely generated `R`-algebra. -/
theorem finiteType_sections_of_locallyOfFiniteType (R : Type u) [CommRing R] (X : Scheme.{u})
    [X.Over (Spec (.of R))] [LocallyOfFiniteType (X ↘ Spec (.of R))] (U : X.affineOpens) :
    letI : Algebra R Γ(X, U) :=
      ((X.baseRingToStructurePresheaf R).app (op U.val)).hom.toAlgebra
    Algebra.FiniteType R Γ(X, U) := by
  let : Algebra R Γ(X, U) :=
    ((X.baseRingToStructurePresheaf R).app (op U.val)).hom.toAlgebra
  refine RingHom.finiteType_algebraMap.mp ?_
  rw [RingHom.algebraMap_toAlgebra, Scheme.baseRingToStructurePresheaf_app_eq_appLE]
  exact (X ↘ Spec (.of R)).finiteType_ΓSpecIso_inv_comp_appLE U.property

/-- Continuation-passing helper for an affine open `U` of a scheme `X` locally of finite type over
`Spec R`, in a cartesian square with `Y` over `Spec S`: installs the canonical section-ring algebra
structures and scalar towers, and supplies the pushout
`Algebra.IsPushout R Γ(X, U) S Γ(Y, g ⁻¹ᵁ U)`, finite type of `Γ(X, U)` over `R`, the affine-chart
identity over `Spec R`, the `S`-algebra map of `Γ(Y, g ⁻¹ᵁ U)`, and the equality identifying the
`Γ(X, U)`-algebra structure with `g.app U`. -/
theorem with_finiteType_algebraIsPushout_of_isPullback
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {X Y : Scheme.{u}} {toR : X ⟶ Spec (.of R)} [LocallyOfFiniteType toR]
    {toS : Y ⟶ Spec (.of S)} {g : Y ⟶ X}
    (H : IsPullback g toS toR (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    {U : X.Opens} (hU : IsAffineOpen U) {P : Prop}
    (hP : ∀ [Algebra R Γ(X, U)] [Algebra S Γ(Y, g ⁻¹ᵁ U)]
      [instXY : Algebra Γ(X, U) Γ(Y, g ⁻¹ᵁ U)] [Algebra R Γ(Y, g ⁻¹ᵁ U)]
      [IsScalarTower R Γ(X, U) Γ(Y, g ⁻¹ᵁ U)] [IsScalarTower R S Γ(Y, g ⁻¹ᵁ U)]
      [Algebra.IsPushout R Γ(X, U) S Γ(Y, g ⁻¹ᵁ U)] [Algebra.FiniteType R Γ(X, U)],
      hU.fromSpec ≫ toR = Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U))) →
      algebraMap S Γ(Y, g ⁻¹ᵁ U) =
        ((Scheme.ΓSpecIso (.of S)).inv ≫ toS.appLE ⊤ (g ⁻¹ᵁ U) le_top).hom →
      instXY = (g.app U).hom.toAlgebra → P) : P := by
  let : X.Over (Spec (.of R)) := ⟨toR⟩
  let : Y.Over (Spec (.of S)) := ⟨toS⟩
  have : LocallyOfFiniteType (X ↘ Spec (.of R)) := ‹_›
  let : Algebra R Γ(X, U) := ((X.baseRingToStructurePresheaf R).app (op U)).hom.toAlgebra
  let : Algebra S Γ(Y, g ⁻¹ᵁ U) :=
    ((Y.baseRingToStructurePresheaf S).app (op (g ⁻¹ᵁ U))).hom.toAlgebra
  let : Algebra Γ(X, U) Γ(Y, g ⁻¹ᵁ U) := (g.app U).hom.toAlgebra
  let : Algebra R Γ(Y, g ⁻¹ᵁ U) := ((g.app U).hom.comp (algebraMap R Γ(X, U))).toAlgebra
  have : IsScalarTower R Γ(X, U) Γ(Y, g ⁻¹ᵁ U) := .of_algebraMap_eq' rfl
  have : IsScalarTower R S Γ(Y, g ⁻¹ᵁ U) :=
    Scheme.Modules.isScalarTower_baseRingToStructurePresheaf_app g U H.toCommSq
  have : Algebra.IsPushout R Γ(X, U) S Γ(Y, g ⁻¹ᵁ U) :=
    (Scheme.algebraIsPushout_baseRingToStructurePresheaf_of_isAffineOpen H hU).symm
  have : Algebra.FiniteType R Γ(X, U) := finiteType_sections_of_locallyOfFiniteType R X ⟨U, hU⟩
  have hcomp : hU.fromSpec ≫ toR = Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U))) := by
    -- `X ↘ Spec (.of R)` is definitionally `toR` via the local `Over` instance above.
    change hU.fromSpec ≫ (X ↘ Spec (.of R)) = _
    rw [hU.fromSpec_comp_eq_SpecMap (X ↘ Spec (.of R)), RingHom.algebraMap_toAlgebra,
      Scheme.baseRingToStructurePresheaf_app_eq_appLE, CommRingCat.ofHom_hom]
  have hS : algebraMap S Γ(Y, g ⁻¹ᵁ U) =
      ((Scheme.ΓSpecIso (.of S)).inv ≫ toS.appLE ⊤ (g ⁻¹ᵁ U) le_top).hom := by
    -- `Y ↘ Spec (.of S)` is definitionally `toS` via the local `Over` instance above.
    change _ = ((Scheme.ΓSpecIso (.of S)).inv ≫ (Y ↘ Spec (.of S)).appLE ⊤ (g ⁻¹ᵁ U) le_top).hom
    rw [RingHom.algebraMap_toAlgebra, Scheme.baseRingToStructurePresheaf_app_eq_appLE]
  exact hP hcomp hS rfl

end TauCeti.AlgebraicGeometry
