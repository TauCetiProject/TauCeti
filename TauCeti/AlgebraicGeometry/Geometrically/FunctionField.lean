/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.RingTheory.TensorProduct.Nontrivial
public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra
public import TauCeti.FieldTheory.AlgebraicClosure
public import TauCeti.FieldTheory.FunctionField.ConstantField
public import TauCeti.RingTheory.TensorProduct.IsDomain

/-!
# The function field of a geometrically integral scheme

Let `X` be an integral scheme over a field `k` that is geometrically integral over `k`. Then for
every field extension `L / k` the ring `k(X) ⊗[k] L` is a domain, and consequently `k` is
algebraically closed in the function field `k(X)`, that is, `k` is the full field of constants of
`k(X)`.

For the first statement, choose a nonempty affine open `U` of `X`. The base change
`Spec (Γ(X, U) ⊗[k] L)` of `U` to `L` is a nonempty open subscheme of the integral scheme
`X ×_k Spec L`, so `Γ(X, U) ⊗[k] L` is a domain, and `k(X) ⊗[k] L` is a localization of it because
`k(X)` is the fraction field of `Γ(X, U)`. The second statement follows by taking for `L` an
algebraic closure of `k` (`TauCeti.algebraicClosure_eq_bot_of_isDomain_tensorProduct`).

The constant-field hypothesis `IsIntegrallyClosedIn k X.functionField` is how the function-field
theory of curves (Weil differentials, the genus of the function field, Serre duality for divisor
sheaves) is applied to a curve. This file derives it from geometric integrality, which in turn
holds for smooth geometrically connected schemes over `k`
(`TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral`).

The proof is built on Andrew Yang's formalization of geometrically integral morphisms in Mathlib
(`AlgebraicGeometry.GeometricallyIntegral`, in `Mathlib/AlgebraicGeometry/Geometrically/Integral`),
which supplies the integrality of the base change `X ×_k Spec L`.

## Main results

* `TauCeti.AlgebraicGeometry.isDomain_functionField_tensorProduct_of_geometricallyIntegral`:
  `k(X) ⊗[k] L` is a domain for every field extension `L / k`;
* `TauCeti.AlgebraicGeometry.isIntegrallyClosedIn_functionField_of_geometricallyIntegral`:
  `k` is algebraically closed in `k(X)`.
-/

public section

open CategoryTheory Limits _root_.AlgebraicGeometry
open scoped TensorProduct

namespace TauCeti

namespace AlgebraicGeometry

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]
  [GeometricallyIntegral (X ↘ Spec (.of k))]

/-- The function field of a geometrically integral scheme over `k` stays a domain after extending
scalars to any field extension `L` of `k`. -/
instance isDomain_functionField_tensorProduct_of_geometricallyIntegral (L : Type u) [Field L]
    [Algebra k L] : IsDomain (X.functionField ⊗[k] L) := by
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  replace hU : IsAffineOpen U := hU
  -- `Γ(X, U)` is a `k`-algebra through the structure morphism, compatibly with `k(X)`.
  let _ : Algebra k Γ(X, U) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appLE ⊤ U le_top).hom.toAlgebra
  have : IsScalarTower k Γ(X, U) X.functionField :=
    .of_algebraMap_eq' (Scheme.baseRingToFunctionField_eq_comp_appLE k X U)
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  have hw : hU.fromSpec ≫ (X ↘ Spec (.of k)) =
      Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U))) := by
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec _ (isAffineOpen_top _) hU le_top,
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp,
      RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom]
  -- `Spec (Γ(X, U) ⊗[k] L)` is the base change of `U` to `L`, an open subscheme of the integral
  -- scheme `X ×_k Spec L`.
  let s := Spec.map (CommRingCat.ofHom (algebraMap k L))
  have : IsIntegral (pullback (X ↘ Spec (.of k)) s) :=
    pullback_of_geometrically GeometricallyIntegral.geometrically_isIntegral L s
  have : Nontrivial (Γ(X, U) ⊗[k] L) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k _ _
      (algebraMap k Γ(X, U)).injective (algebraMap k L).injective
  let e : Spec (.of (Γ(X, U) ⊗[k] L)) ≅
      pullback hU.fromSpec (pullback.fst (X ↘ Spec (.of k)) s) :=
    (pullbackSpecIso k Γ(X, U) L).symm ≪≫ pullback.congrHom hw.symm rfl ≪≫
      (pullbackRightPullbackFstIso _ _ _).symm
  have : IsIntegral (Spec (.of (Γ(X, U) ⊗[k] L))) :=
    isIntegral_of_isOpenImmersion (e.hom ≫ pullback.snd _ _)
  have : IsDomain (Γ(X, U) ⊗[k] L) := (affine_isIntegral_iff _).mp this
  exact isDomain_tensorProduct_of_isLocalization (nonZeroDivisors Γ(X, U)) le_rfl
    X.functionField L

/-- **The constant field of a geometrically integral scheme.** If `X` is integral and
geometrically integral over `k`, then `k` is algebraically closed in the function field `k(X)`. -/
theorem isIntegrallyClosedIn_functionField_of_geometricallyIntegral :
    IsIntegrallyClosedIn k X.functionField :=
  algebraicClosure_eq_bot_iff_isIntegrallyClosedIn.mp
    (algebraicClosure_eq_bot_of_isDomain_tensorProduct (AlgebraicClosure k))

end AlgebraicGeometry

end TauCeti
