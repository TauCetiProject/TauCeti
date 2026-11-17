/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import TauCeti.FieldTheory.AlgebraicClosure
public import TauCeti.RingTheory.IntegralClosure.IntegrallyClosed
public import TauCeti.RingTheory.TensorProduct.IsDomain
import TauCeti.FieldTheory.PurelyInseparable.TensorProduct
public import TauCeti.RingTheory.TensorProduct.Reduced

/-!
# Regular field extensions: characterizations and stability under base change

Let `F / k` be a field extension with a **separating element**: some `x ∈ F` is transcendental
over `k` and `F` is separable algebraic over `k(x)`. Then `F ⊗[k] K` is reduced for every
reduced `k`-algebra `K`, so `F` is geometrically reduced over `k`. If `F` is
geometrically reduced and `k` is algebraically closed in `F` (exact constants), then `F ⊗[k] K` is
a domain for every field extension `K / k`, and more generally `F ⊗[k] A` is a domain for every
`k`-algebra `A` that is a domain: in the language of Weil and Lang, `F` is a *regular* extension
of `k`. Conversely, if `F ⊗[k] L` is a domain for even one algebraically closed field `L` over `k`,
then `F` is geometrically reduced over `k` and `k` is algebraically closed in `F`, so `F ⊗[k] A` is
a domain for every domain `k`-algebra `A` (and indeed `B ⊗[k] L` being a domain implies `B ⊗[k] A`
is a domain for any commutative `k`-algebra `B`). Over a perfect field (in particular in
characteristic zero), geometric reducedness is automatic
(`TauCeti.instIsGeometricallyReducedOfPerfectField`), so regularity is equivalent to exact
constants alone.

Both hypotheses are needed in general. Over `k = ℝ`, the field `ℂ(x)` has the separating element
`x`, but `ℂ ⊗[ℝ] ℂ(x)` is not a domain (`TauCeti.not_isDomain_complex_tensorProduct`) since the
constants `ℝ` are not exact. Over an imperfect field, exact constants alone do not suffice: for
`k = 𝔽_p(a, b)` and `F = k(x, y)` with `y ^ p = a + b x ^ p`, the element
`y - a ^ (1/p) - b ^ (1/p) x` of `F ⊗[k] k(a ^ (1/p), b ^ (1/p))` is nilpotent and nonzero
(`TauCeti.not_isReduced_tensorProduct_of_pow_eq_add_mul_X_pow`). Over every field, exact constants
do give a domain after a separable algebraic extension of the constants
(`TauCeti.isDomain_tensorProduct_of_isIntegrallyClosedIn`), and a domain after extension to an
algebraic closure forces exact constants
(`TauCeti.algebraicClosure_eq_bot_of_isDomain_tensorProduct`).

Regular extensions are stable under arbitrary field extensions of scalars: if `F / k` is
geometrically reduced with exact constants and `K / k` is any field extension (possibly
transcendental or inseparable), then for any fraction ring `Q` of `K ⊗[k] F` (or of `F ⊗[k] K`),
`Q` is geometrically reduced over `K` (`TauCeti.isGeometricallyReduced_of_isLocalization` and
`TauCeti.isGeometricallyReduced_of_isFractionRing_tensorProduct`), `K` is algebraically closed in
`Q`, and `Q ⊗[K] A` is a domain for every domain `K`-algebra `A`. Indeed,
`(K ⊗[k] F) ⊗[K] A ≃ A ⊗[k] F` and `Q ⊗[K] A` is a localization of it at nonzero divisors of
`K ⊗[k] F` (`TauCeti.isDomain_tensorProduct_of_isLocalization`). In particular, over an
algebraically closed base field `k`, for any field extension `F / k` and commutative domain
`k`-algebra `B`, the field `F` is relatively algebraically closed in `Frac(F ⊗[k] B)` (and
similarly `K` is relatively algebraically closed in `Frac(A ⊗[k] K)`).

Reducedness comes from writing `F ⊗[k] K = F ⊗[k(x)] (k(x) ⊗[k] K)`. Here `k(x) ⊗[k] K` is a
localization of the polynomial ring `K[X]`, hence reduced
(`TauCeti.isReduced_ratFunc_tensorProduct`), and extending the scalars of a reduced
algebra by the separable algebraic extension `F / k(x)` preserves reducedness
(`TauCeti.isReduced_tensorProduct_of_isReduced_of_isSeparable`).

For the domain property, first let `K / k` be algebraic and let `L` be the separable closure of `k`
in `K`. Exact constants make `L ⊗[k] F` a domain, and `K ⊗[k] F` is reduced by geometric
reducedness. Since `K / L` is purely inseparable, every element of `K ⊗[k] F` has a positive power
in `L ⊗[k] F`, so `K ⊗[k] F` is a domain
(`TauCeti.IsPurelyInseparable.isDomain_tensorProduct_of_isDomain_tensorProduct`).
For an arbitrary `K`, embed an algebraic closure `C` of `k` in an algebraic closure `Ω` of `K`.
Then `F ⊗[k] K` embeds in `Ω ⊗[k] F = Ω ⊗[C] (C ⊗[k] F)`, the tensor product of two domains over
an algebraically closed field, which is a domain (`TauCeti.isDomain_tensorProduct_of_isAlgClosed`).
A domain `A` is handled through its fraction field in the same way.

## Main results

* `TauCeti.isReduced_tensorProduct_of_separating`: a separating element makes `F ⊗[k] K` reduced
  for every reduced `k`-algebra `K`.
* `TauCeti.isGeometricallyReduced_of_separating`: hence `F` is geometrically reduced over `k`.
* `TauCeti.isDomain_tensorProduct_of_isGeometricallyReduced` and
  `TauCeti.isDomain_tensorProduct_of_isGeometricallyReduced'`: if `F` is geometrically reduced with
  exact constants (automatically geometrically reduced over a perfect field), then `F ⊗[k] A` and
  `A ⊗[k] F` are domains for every domain `k`-algebra `A`.
* `TauCeti.isDomain_tensorProduct_of_isDomain_tensorProduct_isAlgClosed`: if `B ⊗[k] L` is a domain
  for one algebraically closed field `L / k`, then `B ⊗[k] A` is a domain for every domain
  `k`-algebra `A`.
* `TauCeti.isGeometricallyReduced_and_isIntegrallyClosedIn_iff_isDomain_tensorProduct` and
  `TauCeti.isGeometricallyReduced_and_isIntegrallyClosedIn_iff_forall_isDomain_tensorProduct`:
  regularity is equivalent to `F ⊗[k] L` being a domain for one algebraically closed field `L / k`,
  and to `F ⊗[k] K` being a domain for all field extensions `K / k`.
* `TauCeti.isIntegrallyClosedIn_of_isFractionRing_left_tensorProduct`,
  `TauCeti.isIntegrallyClosedIn_of_isFractionRing_tensorProduct`, and
  `TauCeti.isIntegrallyClosedIn_fractionRing_tensorProduct`: scalar extension through
  `Frac(K ⊗[k] F)` or `Frac(F ⊗[k] K)` preserves exactness of the constants for regular `F / k`.
* `TauCeti.isDomain_tensorProduct_of_isFractionRing_left_tensorProduct_of_isAlgClosed`,
  `TauCeti.isIntegrallyClosedIn_of_isFractionRing_left_tensorProduct_of_isAlgClosed`,
  `TauCeti.isIntegrallyClosedIn_fractionRing_left_tensorProduct_of_isAlgClosed`, and
  `TauCeti.isIntegrallyClosedIn_fractionRing_tensorProduct_of_isAlgClosed`: over an algebraically
  closed field `k`, `Frac(F ⊗[k] B)` is regular over `F` and `F` is relatively algebraically closed
  in `Frac(F ⊗[k] B)` for any field extension `F / k` and commutative domain `k`-algebra `B` (and
  symmetrically for `K` in `Frac(A ⊗[k] K)`).

## References

* S. Lang, *Introduction to Algebraic Geometry*, Interscience, 1958, Chapter III, Section 1.
* N. Bourbaki, *Algebra II*, Chapters 4–7, Chapter V, Section 17.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.6.
-/

public section

open scoped TensorProduct IntermediateField

namespace TauCeti

universe u v

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]

/-- **A separating element makes the field geometrically reduced.** If `x ∈ F` is transcendental
over `k` and `F` is separable algebraic over `k(x)`, then `F ⊗[k] K` is reduced for every
reduced `k`-algebra `K`, in particular for every field extension `K / k`. -/
theorem isReduced_tensorProduct_of_separating {x : F} (hx : Transcendental k x)
    [Algebra.IsSeparable k⟮x⟯ F] (K : Type*) [CommRing K] [IsReduced K] [Algebra k K] :
    IsReduced (F ⊗[k] K) :=
  -- `k(x) ⊗[k] K` is reduced, as `k(x)` is a rational function field over `k`
  isReduced_tensorProduct_of_isReduced_of_isSeparable k (E := k⟮x⟯) K (hE :=
    let e := Algebra.TensorProduct.congr (RatFunc.algEquivOfTranscendental x hx).symm
      (AlgEquiv.refl : K ≃ₐ[k] K)
    isReduced_of_injective e e.injective)

/-- A field with a separating element is geometrically reduced over its base field. -/
theorem isGeometricallyReduced_of_separating {x : F} (hx : Transcendental k x)
    [Algebra.IsSeparable k⟮x⟯ F] : Algebra.IsGeometricallyReduced k F :=
  have := isReduced_tensorProduct_of_separating hx (AlgebraicClosure k)
  Algebra.IsGeometricallyReduced.of_isReduced_tensorProduct' (AlgebraicClosure k)

/-- The algebraic case of `isDomain_tensorProduct_of_isGeometricallyReduced`. -/
private theorem isDomain_tensorProduct_of_isGeometricallyReduced_of_isAlgebraic
    (hex : IsIntegrallyClosedIn k F) [Algebra.IsGeometricallyReduced k F] (K : Type*) [Field K]
    [Algebra k K] [Algebra.IsAlgebraic k K] : IsDomain (K ⊗[k] F) :=
  -- Over the separable closure `L` of `k` in `K`, exact constants make `L ⊗[k] F` a domain, and
  -- `K` is purely inseparable over `L`
  have := isDomain_tensorProduct_of_isIntegrallyClosedIn hex (separableClosure k K)
  IsPurelyInseparable.isDomain_tensorProduct_of_isDomain_tensorProduct (separableClosure k K) K F
    (hK := (Algebra.TensorProduct.comm k _ F).toMulEquiv.isDomain)

/-- **Geometrically reduced fields with exact constants are regular.** If `F` is geometrically
reduced over `k` and `k` is algebraically closed in `F`, then `F ⊗[k] A` is a domain for every
`k`-algebra `A` that is a domain, in particular for every field extension of `k`. -/
theorem isDomain_tensorProduct_of_isGeometricallyReduced (hex : IsIntegrallyClosedIn k F)
    [Algebra.IsGeometricallyReduced k F] (A : Type*) [CommRing A] [IsDomain A] [Algebra k A] :
    IsDomain (F ⊗[k] A) := by
  -- Embed an algebraic closure `C` of `k` in an algebraic closure `Ω` of the fraction field of `A`
  let Ω := AlgebraicClosure (FractionRing A)
  let j : AlgebraicClosure k →ₐ[k] Ω := IsAlgClosed.lift
  algebraize [j.toRingHom]
  have : IsScalarTower k (AlgebraicClosure k) Ω :=
    IsScalarTower.of_algebraMap_eq fun c ↦ (j.commutes c).symm
  have := isDomain_tensorProduct_of_isGeometricallyReduced_of_isAlgebraic hex (AlgebraicClosure k)
  -- `Ω ⊗[k] F = Ω ⊗[C] (C ⊗[k] F)` is a domain, as `C` is algebraically closed
  have : IsDomain (Ω ⊗[k] F) :=
    (Algebra.TensorProduct.cancelBaseChange k (AlgebraicClosure k) Ω Ω F).symm.toMulEquiv.isDomain
  -- `F ⊗[k] A` embeds in `Ω ⊗[k] F`, since `F` is flat over the field `k`
  have hA : Function.Injective (algebraMap A Ω) := by
    rw [IsScalarTower.algebraMap_eq A (FractionRing A) Ω]
    exact (algebraMap (FractionRing A) Ω).injective.comp (IsFractionRing.injective A _)
  let φ : A ⊗[k] F →ₐ[k] Ω ⊗[k] F :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom k A Ω) (AlgHom.id k F)
  have hφ : Function.Injective φ := by
    -- Rewrite `φ` as an `rTensor` and apply flatness of `F` over `k`.
    rw [← AlgHom.coe_toLinearMap, Algebra.TensorProduct.toLinearMap_map,
      TensorProduct.AlgebraTensorModule.map_eq]
    exact Module.Flat.rTensor_preserves_injective_linearMap
      (IsScalarTower.toAlgHom k A Ω).toLinearMap hA
  exact (hφ.comp (Algebra.TensorProduct.comm k F A).injective).isDomain
    (φ.comp (Algebra.TensorProduct.comm k F A).toAlgHom)

/-- Symmetric form of `TauCeti.isDomain_tensorProduct_of_isGeometricallyReduced`, with the domain
algebra on the left. -/
theorem isDomain_tensorProduct_of_isGeometricallyReduced' (hex : IsIntegrallyClosedIn k F)
    [Algebra.IsGeometricallyReduced k F] (A : Type*) [CommRing A] [IsDomain A] [Algebra k A] :
    IsDomain (A ⊗[k] F) :=
  have := isDomain_tensorProduct_of_isGeometricallyReduced hex A
  (Algebra.TensorProduct.comm k A F).toMulEquiv.isDomain

/-- **Separably generated fields with exact constants are regular.** If `F` is separable algebraic
over `k(x)` for some `x ∈ F`, and `k` is algebraically closed in `F`, then `F ⊗[k] A` is a domain
for every `k`-algebra `A` that is a domain, in particular for every field extension of `k`. When
`x` is algebraic over `k`, so is `F`, hence `F = k` and the statement is trivial. -/
theorem isDomain_tensorProduct_of_separating (hex : IsIntegrallyClosedIn k F) {x : F}
    [Algebra.IsSeparable k⟮x⟯ F] (A : Type*) [CommRing A] [IsDomain A]
    [Algebra k A] : IsDomain (F ⊗[k] A) := by
  by_cases hx : Transcendental k x
  · have := isGeometricallyReduced_of_separating hx
    exact isDomain_tensorProduct_of_isGeometricallyReduced hex A
  -- Otherwise `F` is algebraic over `k`, so the exact constants force `k = F`.
  have h1 : Algebra.IsAlgebraic k k⟮x⟯ :=
    IntermediateField.isAlgebraic_adjoin_simple (not_not.1 hx).isIntegral
  have h2 : Algebra.IsAlgebraic k⟮x⟯ F := Algebra.IsSeparable.isAlgebraic _ _
  have h3 : Algebra.IsAlgebraic k F := Algebra.IsAlgebraic.trans k k⟮x⟯ F
  have hbij : Function.Bijective (algebraMap k F) :=
    ⟨(algebraMap k F).injective, fun y ↦ (IsIntegralClosure.isIntegral_iff (R := k) (A := k)).1
      (Algebra.IsAlgebraic.isAlgebraic y).isIntegral⟩
  let e : F ⊗[k] A ≃ₐ[k] A :=
    (Algebra.TensorProduct.congr (AlgEquiv.ofBijective (Algebra.ofId k F) hbij).symm
      AlgEquiv.refl).trans (Algebra.TensorProduct.lid k A)
  exact e.toMulEquiv.isDomain

/-! ### Converse and equivalence characterizations -/

/-- **Testing regularity against one algebraically closed field.** If `B ⊗[k] L` is a domain for
one algebraically closed field `L` over `k`, then `B ⊗[k] A` is a domain for every domain
`k`-algebra `A`. -/
theorem isDomain_tensorProduct_of_isDomain_tensorProduct_isAlgClosed {B : Type*} [CommRing B]
    [Algebra k B] (L : Type*) [Field L] [Algebra k L] [IsAlgClosed L] [IsDomain (B ⊗[k] L)]
    (A : Type*) [CommRing A] [IsDomain A] [Algebra k A] : IsDomain (B ⊗[k] A) := by
  have : IsDomain B :=
    (Algebra.TensorProduct.includeLeft_injective (S := k) (algebraMap k L).injective).isDomain
      (Algebra.TensorProduct.includeLeft : B →ₐ[k] B ⊗[k] L)
  have : IsDomain (FractionRing B ⊗[k] L) :=
    isDomain_tensorProduct_of_isLocalization (nonZeroDivisors B) le_rfl (FractionRing B) L
  have : Algebra.IsGeometricallyReduced k (FractionRing B) :=
    Algebra.IsGeometricallyReduced.of_isReduced_tensorProduct' L
  have : IsDomain (FractionRing B ⊗[k] A) :=
    isDomain_tensorProduct_of_isGeometricallyReduced
      (isIntegrallyClosedIn_of_isDomain_tensorProduct L) A
  let φ : B ⊗[k] A →ₐ[k] FractionRing B ⊗[k] A :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom k B (FractionRing B)) (AlgHom.id k A)
  have hφ : Function.Injective φ := by
    rw [← AlgHom.coe_toLinearMap, Algebra.TensorProduct.toLinearMap_map,
      TensorProduct.AlgebraTensorModule.map_eq]
    exact Module.Flat.rTensor_preserves_injective_linearMap
      (IsScalarTower.toAlgHom k B (FractionRing B)).toLinearMap
      (IsFractionRing.injective B (FractionRing B))
  exact hφ.isDomain φ

/-- **Characterization of regular field extensions via an algebraically closed extension.** For any
algebraically closed field `L` over `k`, `F` is geometrically reduced over `k` with exact constants
if and only if `F ⊗[k] L` is a domain. -/
theorem isGeometricallyReduced_and_isIntegrallyClosedIn_iff_isDomain_tensorProduct
    (L : Type*) [Field L] [Algebra k L] [IsAlgClosed L] :
    Algebra.IsGeometricallyReduced k F ∧ IsIntegrallyClosedIn k F ↔ IsDomain (F ⊗[k] L) :=
  ⟨fun ⟨_, hex⟩ ↦ isDomain_tensorProduct_of_isGeometricallyReduced hex L,
    fun _ ↦ ⟨Algebra.IsGeometricallyReduced.of_isReduced_tensorProduct' L,
      isIntegrallyClosedIn_of_isDomain_tensorProduct L⟩⟩

/-- **Characterization of regular field extensions via all scalar extensions.** A field extension
`F / k` is geometrically reduced with exact constants if and only if `F ⊗[k] K` is a domain for
every field extension `K / k`. -/
theorem isGeometricallyReduced_and_isIntegrallyClosedIn_iff_forall_isDomain_tensorProduct :
    Algebra.IsGeometricallyReduced k F ∧ IsIntegrallyClosedIn k F ↔
      ∀ (K : Type u) [Field K] [Algebra k K], IsDomain (F ⊗[k] K) :=
  ⟨fun ⟨_, hex⟩ K _ _ ↦ isDomain_tensorProduct_of_isGeometricallyReduced hex K,
    fun h ↦ have := h (AlgebraicClosure k)
      ⟨Algebra.IsGeometricallyReduced.of_isReduced_tensorProduct' (AlgebraicClosure k),
        isIntegrallyClosedIn_of_isDomain_tensorProduct (AlgebraicClosure k)⟩⟩

/-- Over a perfect field, `k` is algebraically closed in `F` if and only if `F ⊗[k] L` is a domain
for a given algebraically closed field `L` over `k`. -/
theorem isIntegrallyClosedIn_iff_isDomain_tensorProduct_of_perfectField [PerfectField k]
    (L : Type*) [Field L] [Algebra k L] [IsAlgClosed L] :
    IsIntegrallyClosedIn k F ↔ IsDomain (F ⊗[k] L) :=
  ⟨fun hex ↦ isDomain_tensorProduct_of_isGeometricallyReduced hex L,
    fun _ ↦ isIntegrallyClosedIn_of_isDomain_tensorProduct L⟩

/-- Over a perfect field, `k` is algebraically closed in `F` if and only if `F ⊗[k] K` is a domain
for every field extension `K / k`. -/
theorem isIntegrallyClosedIn_iff_forall_isDomain_tensorProduct_of_perfectField [PerfectField k] :
    IsIntegrallyClosedIn k F ↔ ∀ (K : Type u) [Field K] [Algebra k K], IsDomain (F ⊗[k] K) :=
  ⟨fun hex K _ _ ↦ isDomain_tensorProduct_of_isGeometricallyReduced hex K,
    fun h ↦ have := h (AlgebraicClosure k)
      isIntegrallyClosedIn_of_isDomain_tensorProduct (AlgebraicClosure k)⟩

/-! ### Stability of regular extensions under scalar extension -/

section BaseChange

/-- **Regularity is stable under arbitrary field base change (left-scalar tensor order).** Let
`F / k` be geometrically reduced with exact constants and let `K / k` be any field extension. For
any fraction ring `Q` of `K ⊗[k] F` and any domain `K`-algebra `A`, the tensor product `Q ⊗[K] A`
is a domain. -/
theorem isDomain_tensorProduct_of_isFractionRing_left_tensorProduct
    (hex : IsIntegrallyClosedIn k F) [Algebra.IsGeometricallyReduced k F]
    {K Q : Type*} [Field K] [Algebra k K] [CommRing Q] [Algebra (K ⊗[k] F) Q] [Algebra K Q]
    [IsScalarTower K (K ⊗[k] F) Q] [IsFractionRing (K ⊗[k] F) Q]
    (A : Type*) [CommRing A] [IsDomain A] [Algebra K A] :
    IsDomain (Q ⊗[K] A) := by
  let _ : Algebra k A := ((algebraMap K A).comp (algebraMap k K)).toAlgebra
  have : IsScalarTower k K A := .of_algebraMap_eq fun _ ↦ rfl
  have : IsDomain (A ⊗[k] F) := isDomain_tensorProduct_of_isGeometricallyReduced' hex A
  exact isDomain_tensorProduct_of_isLocalization_tensorProduct
    (nonZeroDivisors (K ⊗[k] F)) le_rfl Q A

/-- **Exact constants persist after arbitrary field base change of a regular extension.** If
`F / k` is geometrically reduced with exact constants and `K / k` is any field extension, then `K`
is algebraically closed in any fraction ring `Q` of `K ⊗[k] F`. -/
theorem isIntegrallyClosedIn_of_isFractionRing_left_tensorProduct
    (hex : IsIntegrallyClosedIn k F) [Algebra.IsGeometricallyReduced k F]
    {K Q : Type*} [Field K] [Algebra k K] [CommRing Q] [Algebra (K ⊗[k] F) Q] [Algebra K Q]
    [IsScalarTower K (K ⊗[k] F) Q] [IsFractionRing (K ⊗[k] F) Q] :
    IsIntegrallyClosedIn K Q := by
  have := isDomain_tensorProduct_of_isFractionRing_left_tensorProduct hex (K := K) (Q := Q)
    (AlgebraicClosure K)
  exact isIntegrallyClosedIn_of_isDomain_tensorProduct (k := K) (A := Q) (AlgebraicClosure K)

/-- **Over an algebraically closed base field, `Frac(F ⊗[k] B)` is regular over `F`.** For any
field extension `F / k`, any commutative domain `k`-algebra `B` over an algebraically closed field
`k`, any fraction ring `Q` of `F ⊗[k] B`, and any domain `F`-algebra `A`, the tensor product
`Q ⊗[F] A` is a domain. -/
theorem isDomain_tensorProduct_of_isFractionRing_left_tensorProduct_of_isAlgClosed [IsAlgClosed k]
    {B Q : Type*} [CommRing B] [IsDomain B] [Algebra k B] [CommRing Q] [Algebra (F ⊗[k] B) Q]
    [Algebra F Q] [IsScalarTower F (F ⊗[k] B) Q] [IsFractionRing (F ⊗[k] B) Q]
    (A : Type*) [CommRing A] [IsDomain A] [Algebra F A] :
    IsDomain (Q ⊗[F] A) := by
  let _ : Algebra k A := ((algebraMap F A).comp (algebraMap k F)).toAlgebra
  have : IsScalarTower k F A := .of_algebraMap_eq fun _ ↦ rfl
  exact isDomain_tensorProduct_of_isLocalization_tensorProduct
    (nonZeroDivisors (F ⊗[k] B)) le_rfl Q A

/-- **Relative algebraic closure in `Frac(F ⊗[k] B)` over an algebraically closed field.** If `k`
is algebraically closed, then for any field extension `F / k` and commutative domain `k`-algebra
`B`, the field `F` is integrally closed (relatively algebraically closed) in any fraction ring `Q`
of `F ⊗[k] B`. -/
theorem isIntegrallyClosedIn_of_isFractionRing_left_tensorProduct_of_isAlgClosed [IsAlgClosed k]
    {B Q : Type*} [CommRing B] [IsDomain B] [Algebra k B] [CommRing Q] [Algebra (F ⊗[k] B) Q]
    [Algebra F Q] [IsScalarTower F (F ⊗[k] B) Q] [IsFractionRing (F ⊗[k] B) Q] :
    IsIntegrallyClosedIn F Q := by
  have := isDomain_tensorProduct_of_isFractionRing_left_tensorProduct_of_isAlgClosed
    (k := k) (F := F) (B := B) (Q := Q) (AlgebraicClosure F)
  exact isIntegrallyClosedIn_of_isDomain_tensorProduct (k := F) (A := Q) (AlgebraicClosure F)

variable (k F) in
/-- Over an algebraically closed base field `k`, `F` is unconditionally relatively algebraically
closed in `FractionRing (F ⊗[k] B)` for any field extension `F / k` and commutative domain
`k`-algebra `B`. -/
theorem isIntegrallyClosedIn_fractionRing_left_tensorProduct_of_isAlgClosed [IsAlgClosed k]
    (B : Type*) [CommRing B] [IsDomain B] [Algebra k B] :
    IsIntegrallyClosedIn F (FractionRing (F ⊗[k] B)) :=
  isIntegrallyClosedIn_of_isFractionRing_left_tensorProduct_of_isAlgClosed (k := k) (B := B)

section RightAlgebra

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  Algebra.TensorProduct.right_isScalarTower

/-- The `K ⊗[R] A`-algebra structure on an `A ⊗[R] K`-algebra induced by swapping tensor factors. -/
@[instance_reducible]
private noncomputable def commLeftAlgebra {R A K Q : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [CommRing K] [Algebra R K] [CommRing Q] [Algebra (A ⊗[R] K) Q] : Algebra (K ⊗[R] A) Q :=
  ((algebraMap (A ⊗[R] K) Q).comp
    (Algebra.TensorProduct.comm R A K).toRingEquiv.symm.toRingHom).toAlgebra

/-- Swapping `A ⊗[R] K` with `K ⊗[R] A` preserves the `K`-scalar tower and `IsFractionRing`. -/
private theorem commLeft_isScalarTower_and_isFractionRing {R A K Q : Type*} [CommRing R]
    [CommRing A] [Algebra R A] [CommRing K] [Algebra R K] [CommRing Q] [Algebra (A ⊗[R] K) Q]
    [Algebra K Q] [IsScalarTower K (A ⊗[R] K) Q] [IsFractionRing (A ⊗[R] K) Q] :
    letI := commLeftAlgebra (R := R) (A := A) (K := K) (Q := Q)
    IsScalarTower K (K ⊗[R] A) Q ∧ IsFractionRing (K ⊗[R] A) Q :=
  letI := commLeftAlgebra (R := R) (A := A) (K := K) (Q := Q)
  ⟨.of_algebraMap_eq fun c ↦ by
      simp [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_apply K (A ⊗[R] K) Q,
        Algebra.TensorProduct.comm_symm_tmul],
    (IsFractionRing.isFractionRing_iff_of_base_ringEquiv Q
      (Algebra.TensorProduct.comm R A K).toRingEquiv).mp inferInstance⟩

/-- Right-scalar companion to `TauCeti.isDomain_tensorProduct_of_isFractionRing_left_tensorProduct`,
viewing a fraction ring `Q` of `F ⊗[k] K` as a `K`-algebra via the right tensor factor. -/
theorem isDomain_tensorProduct_of_isFractionRing_tensorProduct
    (hex : IsIntegrallyClosedIn k F) [Algebra.IsGeometricallyReduced k F]
    {K Q : Type*} [Field K] [Algebra k K] [CommRing Q] [Algebra (F ⊗[k] K) Q] [Algebra K Q]
    [IsScalarTower K (F ⊗[k] K) Q] [IsFractionRing (F ⊗[k] K) Q]
    (A : Type*) [CommRing A] [IsDomain A] [Algebra K A] :
    IsDomain (Q ⊗[K] A) := by
  let _ := commLeftAlgebra (R := k) (A := F) (K := K) (Q := Q)
  obtain ⟨_, _⟩ := commLeft_isScalarTower_and_isFractionRing (R := k) (A := F) (K := K) (Q := Q)
  exact isDomain_tensorProduct_of_isFractionRing_left_tensorProduct hex (Q := Q) A

/-- Right-scalar companion to
`TauCeti.isIntegrallyClosedIn_of_isFractionRing_left_tensorProduct`: if `F / k` is geometrically
reduced with exact constants and `K / k` is any field extension, then `K` is algebraically closed
in any fraction ring `Q` of `F ⊗[k] K`. -/
theorem isIntegrallyClosedIn_of_isFractionRing_tensorProduct
    (hex : IsIntegrallyClosedIn k F) [Algebra.IsGeometricallyReduced k F]
    {K Q : Type*} [Field K] [Algebra k K] [CommRing Q] [Algebra (F ⊗[k] K) Q] [Algebra K Q]
    [IsScalarTower K (F ⊗[k] K) Q] [IsFractionRing (F ⊗[k] K) Q] :
    IsIntegrallyClosedIn K Q := by
  let _ := commLeftAlgebra (R := k) (A := F) (K := K) (Q := Q)
  obtain ⟨_, _⟩ := commLeft_isScalarTower_and_isFractionRing (R := k) (A := F) (K := K) (Q := Q)
  exact isIntegrallyClosedIn_of_isFractionRing_left_tensorProduct hex (Q := Q)

/-- If `F / k` is geometrically reduced with exact constants, then `K` is algebraically closed in
`FractionRing (F ⊗[k] K)` for every field extension `K / k`. -/
theorem isIntegrallyClosedIn_fractionRing_tensorProduct (hex : IsIntegrallyClosedIn k F)
    [Algebra.IsGeometricallyReduced k F] (K : Type*) [Field K] [Algebra k K] :
    IsIntegrallyClosedIn K (FractionRing (F ⊗[k] K)) :=
  isIntegrallyClosedIn_of_isFractionRing_tensorProduct hex

variable (k) in
/-- Over an algebraically closed base field `k`, `K` is unconditionally algebraically closed in
`FractionRing (A ⊗[k] K)` for any commutative domain `k`-algebra `A` and field extension `K / k`. -/
theorem isIntegrallyClosedIn_fractionRing_tensorProduct_of_isAlgClosed [IsAlgClosed k]
    (A : Type*) [CommRing A] [IsDomain A] [Algebra k A] (K : Type*) [Field K] [Algebra k K] :
    IsIntegrallyClosedIn K (FractionRing (A ⊗[k] K)) := by
  let _ := commLeftAlgebra (R := k) (A := A) (K := K) (Q := FractionRing (A ⊗[k] K))
  obtain ⟨_, _⟩ := commLeft_isScalarTower_and_isFractionRing
    (R := k) (A := A) (K := K) (Q := FractionRing (A ⊗[k] K))
  exact isIntegrallyClosedIn_of_isFractionRing_left_tensorProduct_of_isAlgClosed
    (k := k) (F := K) (B := A) (Q := FractionRing (A ⊗[k] K))

end RightAlgebra

end BaseChange

end TauCeti
