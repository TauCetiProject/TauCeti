/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.RingTheory.TensorProduct.Nontrivial
public import TauCeti.AlgebraicGeometry.PullbackSpecMap
public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra
public import TauCeti.FieldTheory.AlgebraicClosure
public import TauCeti.FieldTheory.FunctionField.ConstantField
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.TensorProduct
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

The same chart describes the function field of the base change `Y = X ×_k Spec K` to an algebraic
extension `K / k`. The function field of `Y` is the fraction field of `Γ(X, U) ⊗[k] K`, and so is
the constant field extension `k(X) · K`, because `k(X) ⊗[k] K` is a field
(`TauCeti.isFractionRing_tensorProduct_of_constantCompositum_eq_top`). Hence `K(Y) ≃ k(X) · K`
as `K`-algebras, also when `K / k` is inseparable. This is how invariants of the function field of
a geometrically integral curve, such as its genus, are compared with those of its base change.

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
  `k` is algebraically closed in `k(X)`;
* `TauCeti.AlgebraicGeometry.nonempty_functionField_algEquiv_of_isPullback`: the function field of
  the base change of `X` to an algebraic extension `K / k` is the compositum `k(X) · K`.

The chart arguments use `TauCeti.AlgebraicGeometry.exists_affineOpen_isFractionRing` and
`AlgebraicGeometry.Scheme.Hom.nonempty_functionField_algEquiv_of_isOpenImmersion` (the function
field of an integral scheme is the fraction field of any affine chart), from
`TauCeti/AlgebraicGeometry/Scheme/BaseAlgebra.lean`, and
`TauCeti.AlgebraicGeometry.exists_isOpenImmersion_tensorProduct_of_isPullback` (the base change of
an affine chart is an affine chart of the base change), from
`TauCeti/AlgebraicGeometry/PullbackSpecMap.lean`.
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
  obtain ⟨U, hU, _, _, _, _, hw⟩ := exists_affineOpen_isFractionRing (k := k) (X := X)
  -- `Spec (Γ(X, U) ⊗[k] L)` is the base change of `U` to `L`, an open subscheme of the integral
  -- scheme `X ×_k Spec L`.
  let s := Spec.map (CommRingCat.ofHom (algebraMap k L))
  have : IsIntegral (pullback (X ↘ Spec (.of k)) s) :=
    pullback_of_geometrically GeometricallyIntegral.geometrically_isIntegral L s
  have : Nontrivial (Γ(X, U) ⊗[k] L) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k _ _
      (algebraMap k Γ(X, U)).injective (algebraMap k L).injective
  obtain ⟨ι, _, -⟩ := exists_isOpenImmersion_tensorProduct_of_isPullback hw
    (IsPullback.of_hasPullback (X ↘ Spec (.of k)) s)
  have : IsIntegral (Spec (.of (Γ(X, U) ⊗[k] L))) := isIntegral_of_isOpenImmersion ι
  have : IsDomain (Γ(X, U) ⊗[k] L) := (affine_isIntegral_iff _).mp this
  exact isDomain_tensorProduct_of_isLocalization (nonZeroDivisors Γ(X, U)) le_rfl
    X.functionField L

/-- **The constant field of a geometrically integral scheme.** If `X` is integral and
geometrically integral over `k`, then `k` is algebraically closed in the function field `k(X)`. -/
theorem isIntegrallyClosedIn_functionField_of_geometricallyIntegral :
    IsIntegrallyClosedIn k X.functionField :=
  algebraicClosure_eq_bot_iff_isIntegrallyClosedIn.mp
    (algebraicClosure_eq_bot_of_isDomain_tensorProduct (AlgebraicClosure k))

/-- **The function field of the base change is the constant field extension.** Let `X` be a
geometrically integral scheme over `k` and `Y = X ×_k Spec K` its base change to an algebraic
extension `K / k`. Then the function field of `Y` is, as a `K`-algebra, the compositum
`F' = k(X) · K`, for inseparable `K / k` as well. -/
theorem nonempty_functionField_algEquiv_of_isPullback {K : Type u} [Field K] [Algebra k K]
    [Algebra.IsAlgebraic k K] {Y : Scheme.{u}} [Y.Over (Spec (.of K))] {g : Y ⟶ X}
    (H : IsPullback g (Y ↘ Spec (.of K)) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    {F' : Type*} [Field F'] [Algebra K F'] [Algebra X.functionField F'] [Algebra k F']
    [IsScalarTower k K F'] [IsScalarTower k X.functionField F']
    (h : constantCompositum X.functionField K F' = ⊤) :
    haveI := GeometricallyIntegral.geometrically_isIntegral _ _ _ H
    Nonempty (Y.functionField ≃ₐ[K] F') := by
  have := GeometricallyIntegral.geometrically_isIntegral _ _ _ H
  obtain ⟨U, _, _, _, _, _, hw⟩ := exists_affineOpen_isFractionRing (k := k) (X := X)
  -- the base change `Spec (Γ(X, U) ⊗[k] K)` of `U` is an open subscheme of `Y` over `Spec K`
  obtain ⟨ι, _, hι⟩ := exists_isOpenImmersion_tensorProduct_of_isPullback hw H
  let _ : Algebra K (Γ(X, U) ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
  -- and `F' = k(X) · K` is a fraction field of `Γ(X, U) ⊗[k] K`
  let _ : Algebra (Γ(X, U) ⊗[k] K) F' := (((Algebra.TensorProduct.productMap
    (IsScalarTower.toAlgHom k X.functionField F') (IsScalarTower.toAlgHom k K F')).comp
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k Γ(X, U) X.functionField)
      (AlgHom.id k K))) : Γ(X, U) ⊗[k] K →+* F').toAlgebra
  have : IsFractionRing (Γ(X, U) ⊗[k] K) F' :=
    isFractionRing_tensorProduct_of_constantCompositum_eq_top h
  have : IsScalarTower K (Γ(X, U) ⊗[k] K) F' := .of_algebraMap_eq fun c ↦ by
    simp [RingHom.algebraMap_toAlgebra]
  exact ι.nonempty_functionField_algEquiv_of_isOpenImmersion hι F'

end AlgebraicGeometry

end TauCeti
