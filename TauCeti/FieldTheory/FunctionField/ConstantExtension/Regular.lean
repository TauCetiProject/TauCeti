/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.TensorProduct
import TauCeti.FieldTheory.AlgebraicClosure
import TauCeti.FieldTheory.PurelyInseparable.TensorProduct
import TauCeti.RingTheory.TensorProduct.IsDomain
import TauCeti.RingTheory.TensorProduct.Reduced

/-!
# Separably generated fields with exact constants are regular

Let `F / k` be a field extension with a **separating element**: some `x ∈ F` is transcendental
over `k` and `F` is separable algebraic over `k(x)`. Then `F ⊗[k] K` is reduced for every field
extension `K / k`. If moreover `k` is algebraically closed in `F` (exact constants), then
`F ⊗[k] K` is a domain for every field extension `K / k`, and more generally `F ⊗[k] A` is a domain
for every `k`-algebra `A` that is a domain: in the language of Weil and Lang, `F` is a *regular*
extension of `k`. For a function field `F`, this says that the curve with function
field `F` stays integral after every extension of the constants, so that `F ⊗[k] K` is a field
when `K / k` is algebraic, namely the constant field extension `F · K`.

Both hypotheses are needed. Over `k = ℝ`, the field `ℂ(x)` has the separating element `x`, but
`ℂ(x) ⊗[ℝ] ℂ` is not a domain since the constants `ℂ` are not exact. Over an imperfect field, exact
constants alone do not suffice: for `k = 𝔽_p(a, b)` and `F = k(x, y)` with `y ^ p = a + b x ^ p`,
the element `y - a ^ (1/p) - b ^ (1/p) x` of `F ⊗[k] k(a ^ (1/p), b ^ (1/p))` is nilpotent and
nonzero. Over every field, exact constants do give a domain after a separable algebraic extension
of the constants (`TauCeti.isDomain_tensorProduct_of_isIntegrallyClosedIn`), and a domain after
extension to an algebraic closure forces exact constants
(`TauCeti.algebraicClosure_eq_bot_of_isDomain_tensorProduct`).

Reducedness comes from writing `F ⊗[k] K = F ⊗[k(x)] (k(x) ⊗[k] K)`. Here `k(x) ⊗[k] K` is a
localization of the polynomial ring `K[X]`, hence a domain, and extending the scalars of a reduced
algebra by the separable algebraic extension `F / k(x)` preserves reducedness
(`TauCeti.isReduced_tensorProduct_of_isReduced_of_isSeparable`).

For the domain property, first let `K / k` be algebraic and let `L` be the separable closure of `k`
in `K`. Exact constants make `L ⊗[k] F` a domain, and `K ⊗[k] F` is reduced. Since `K / L` is purely
inseparable, every element of `K ⊗[k] F` has a positive power in `L ⊗[k] F`, so `K ⊗[k] F` is a
domain (`TauCeti.IsPurelyInseparable.isDomain_tensorProduct`). For an arbitrary `K`, embed an
algebraic closure `k̄` of `k` in an algebraic closure `K̄` of `K`. Then `F ⊗[k] K` embeds in
`K̄ ⊗[k] F = K̄ ⊗[k̄] (k̄ ⊗[k] F)`, the tensor product of two domains over an algebraically closed
field, which is a domain (`TauCeti.isDomain_tensorProduct_of_isAlgClosed`). A domain `A` is handled
through its fraction field in the same way.

## Main results

* `TauCeti.isReduced_tensorProduct_of_separating`: a separating element makes `F ⊗[k] K` reduced
  for every field extension `K / k`.
* `TauCeti.isGeometricallyReduced_of_separating`: hence `F` is geometrically reduced over `k`.
* `TauCeti.isDomain_tensorProduct_of_separating`: with exact constants, `F ⊗[k] A` is a domain for
  every `k`-algebra `A` that is a domain, in particular for every field extension of `k`.
* `TauCeti.productMap_bijective_of_separating`: hence multiplication `F ⊗[k] k' → F · k'` is an
  isomorphism for every algebraic extension `k' / k`.

## References

* S. Lang, *Introduction to Algebraic Geometry*, Interscience, 1958, Chapter III, Section 1.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.6.
-/

public section

open scoped TensorProduct IntermediateField

namespace TauCeti

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- **A separating element makes the field geometrically reduced.** If `x ∈ F` is transcendental
over `k` and `F` is separable algebraic over `k(x)`, then `F ⊗[k] K` is reduced for every field
extension `K / k`. -/
theorem isReduced_tensorProduct_of_separating {x : F} (hx : Transcendental k x)
    [Algebra.IsSeparable k⟮x⟯ F] (K : Type*) [Field K] [Algebra k K] :
    IsReduced (F ⊗[k] K) :=
  -- `k(x) ⊗[k] K` is reduced, as `k(x)` is a rational function field over `k`
  isReduced_tensorProduct_of_isReduced_of_isSeparable k (E := k⟮x⟯) K (hE :=
    let e := Algebra.TensorProduct.congr (RatFunc.algEquivOfTranscendental x hx).symm
      (AlgEquiv.refl : K ≃ₐ[k] K)
    isReduced_of_injective e e.injective)

/-- A field with a separating element is geometrically reduced over its base field. -/
theorem isGeometricallyReduced_of_separating {x : F} (hx : Transcendental k x)
    [Algebra.IsSeparable k⟮x⟯ F] : Algebra.IsGeometricallyReduced k F := by
  rw [Algebra.isGeometricallyReduced_field_iff]
  have := isReduced_tensorProduct_of_separating hx (AlgebraicClosure k)
  exact isReduced_of_injective (Algebra.TensorProduct.comm k (AlgebraicClosure k) F)
    (Algebra.TensorProduct.comm k (AlgebraicClosure k) F).injective

/-- The algebraic case of `isDomain_tensorProduct_of_separating`. -/
private theorem isDomain_tensorProduct_of_separating_of_isAlgebraic (hex : IsIntegrallyClosedIn k F)
    {x : F} (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] (K : Type*) [Field K]
    [Algebra k K] [Algebra.IsAlgebraic k K] : IsDomain (K ⊗[k] F) :=
  -- Over the separable closure `L` of `k` in `K`, exact constants make `L ⊗[k] F` a domain, and
  -- `K` is purely inseparable over `L`
  have := isDomain_tensorProduct_of_isIntegrallyClosedIn hex (separableClosure k K)
  have := isReduced_tensorProduct_of_separating hx K
  IsPurelyInseparable.isDomain_tensorProduct (separableClosure k K) K F
    (hK := (Algebra.TensorProduct.comm k _ F).toMulEquiv.isDomain)
    (hL := isReduced_of_injective (Algebra.TensorProduct.comm k K F)
      (Algebra.TensorProduct.comm k K F).injective)

/-- **Separably generated fields with exact constants are regular.** If `x ∈ F` is transcendental
over `k`, `F` is separable algebraic over `k(x)` and `k` is algebraically closed in `F`, then
`F ⊗[k] A` is a domain for every `k`-algebra `A` that is a domain, in particular for every field
extension of `k`. -/
theorem isDomain_tensorProduct_of_separating (hex : IsIntegrallyClosedIn k F) {x : F}
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] (A : Type*) [CommRing A] [IsDomain A]
    [Algebra k A] : IsDomain (F ⊗[k] A) := by
  -- Embed an algebraic closure `k̄` of `k` in an algebraic closure `Ω` of the fraction field of `A`
  let Ω := AlgebraicClosure (FractionRing A)
  let j : AlgebraicClosure k →ₐ[k] Ω := IsAlgClosed.lift
  algebraize [j.toRingHom]
  have : IsScalarTower k (AlgebraicClosure k) Ω :=
    IsScalarTower.of_algebraMap_eq fun c ↦ (j.commutes c).symm
  have := isDomain_tensorProduct_of_separating_of_isAlgebraic hex hx (AlgebraicClosure k)
  -- `Ω ⊗[k] F = Ω ⊗[k̄] (k̄ ⊗[k] F)` is a domain, as `k̄` is algebraically closed
  have : IsDomain (Ω ⊗[k] F) :=
    (Algebra.TensorProduct.cancelBaseChange k (AlgebraicClosure k) Ω Ω F).symm.toMulEquiv.isDomain
  -- `F ⊗[k] A` embeds in `Ω ⊗[k] F`, since `F` is flat over the field `k`
  have hA : Function.Injective (algebraMap A Ω) := by
    rw [IsScalarTower.algebraMap_eq A (FractionRing A) Ω]
    exact (algebraMap (FractionRing A) Ω).injective.comp (IsFractionRing.injective A _)
  let φ : A ⊗[k] F →ₐ[k] Ω ⊗[k] F :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom k A Ω) (AlgHom.id k F)
  have hφ : Function.Injective φ :=
    Module.Flat.rTensor_preserves_injective_linearMap (IsScalarTower.toAlgHom k A Ω).toLinearMap hA
  exact (hφ.comp (Algebra.TensorProduct.comm k F A).injective).isDomain
    (φ.comp (Algebra.TensorProduct.comm k F A).toAlgHom)

/-- **A constant field extension of a separably generated field is a tensor product.** If `F` has
a separating element and exact constants, then multiplication `F ⊗[k] k' → F · k'` is bijective for
every algebraic extension `k' / k`, separable or not. -/
theorem productMap_bijective_of_separating {k' F' : Type*} [Field k'] [Field F'] [Algebra k k']
    [Algebra k F'] [Algebra k' F'] [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F']
    [Algebra.IsAlgebraic k k'] (hex : IsIntegrallyClosedIn k F) {x : F} (hx : Transcendental k x)
    [Algebra.IsSeparable k⟮x⟯ F] (h : constantCompositum F k' F' = ⊤) :
    Function.Bijective (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
      (IsScalarTower.toAlgHom k k' F')) :=
  have := isDomain_tensorProduct_of_separating hex hx k'
  productMap_bijective_of_constantCompositum_eq_top h

end TauCeti
