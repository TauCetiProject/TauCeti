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
import TauCeti.RingTheory.TensorProduct.Reduced

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
a domain for every domain `k`-algebra `A`. Over a perfect field (in particular in characteristic
zero), geometric reducedness is automatic, so regularity is equivalent to exact constants alone.

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
transcendental or inseparable), then any fraction field `Q` of `K ⊗[k] F` (or of `F ⊗[k] K`) is
again geometrically reduced over `K` with exact constants `K`. Indeed, for any domain `K`-algebra
`A`, `(K ⊗[k] F) ⊗[K] A ≃ A ⊗[k] F` is a domain and `Q ⊗[K] A` is a localization of it at nonzero
divisors (`TauCeti.isDomain_tensorProduct_of_isLocalization`). In particular, over an algebraically
closed base field `k`, every field extension `L / k` is regular, so for any two field extensions
`F / k` and `L / k`, the field `F` is relatively algebraically closed in `Frac(F ⊗[k] L)`.

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
  exact constants, then `F ⊗[k] A` and `A ⊗[k] F` are domains for every domain `k`-algebra `A`.
* `TauCeti.isDomain_tensorProduct_of_perfectField`: over a perfect field, exact constants alone
  make `F ⊗[k] A` a domain for every domain `k`-algebra `A`.
* `TauCeti.isGeometricallyReduced_and_isIntegrallyClosedIn_iff_isDomain_tensorProduct` and
  `TauCeti.isGeometricallyReduced_and_isIntegrallyClosedIn_iff_forall_isDomain_tensorProduct`:
  regularity is equivalent to `F ⊗[k] L` being a domain for one algebraically closed field `L / k`,
  and to `F ⊗[k] K` being a domain for all field extensions `K / k`.
* `TauCeti.isIntegrallyClosedIn_of_isFractionRing_left_tensorProduct`,
  `TauCeti.isIntegrallyClosedIn_of_isFractionRing_tensorProduct`,
  `TauCeti.isIntegrallyClosedIn_fractionRing_tensorProduct`, and
  `TauCeti.isGeometricallyReduced_fractionRing_tensorProduct`: scalar extension of a regular
  field through `Frac(K ⊗[k] F)` or `Frac(F ⊗[k] K)` preserves geometric reducedness and exactness
  of the constants, with specializations to `[PerfectField k]` and `[IsAlgClosed k]`.
* `TauCeti.isIntegrallyClosedIn_left_of_isFractionRing_tensorProduct_of_isAlgClosed` and
  `TauCeti.isIntegrallyClosedIn_left_fractionRing_tensorProduct_of_isAlgClosed`: over an
  algebraically closed field `k`, `F` is relatively algebraically closed in `Frac(F ⊗[k] L)` for
  any field extensions `F / k` and `L / k`.

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
    [Algebra.IsSeparable k⟮x⟯ F] : Algebra.IsGeometricallyReduced k F := by
  rw [Algebra.isGeometricallyReduced_field_iff]
  have := isReduced_tensorProduct_of_separating hx (AlgebraicClosure k)
  exact isReduced_of_injective (Algebra.TensorProduct.comm k (AlgebraicClosure k) F)
    (Algebra.TensorProduct.comm k (AlgebraicClosure k) F).injective

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

/-- **Over a perfect field, exact constants make a field extension regular.** If `k` is perfect
(for instance in characteristic zero) and algebraically closed in `F`, then `F ⊗[k] A` is a domain
for every domain `k`-algebra `A`, with no finite-generation hypothesis on `F` or `A`. -/
theorem isDomain_tensorProduct_of_perfectField [PerfectField k] (hex : IsIntegrallyClosedIn k F)
    (A : Type*) [CommRing A] [IsDomain A] [Algebra k A] :
    IsDomain (F ⊗[k] A) :=
  isDomain_tensorProduct_of_isGeometricallyReduced hex A

/-- Symmetric form of `TauCeti.isDomain_tensorProduct_of_perfectField`, with the domain algebra on
the left. -/
theorem isDomain_tensorProduct_of_perfectField' [PerfectField k] (hex : IsIntegrallyClosedIn k F)
    (A : Type*) [CommRing A] [IsDomain A] [Algebra k A] :
    IsDomain (A ⊗[k] F) :=
  isDomain_tensorProduct_of_isGeometricallyReduced' hex A

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

/-- If `F ⊗[k] L` is a domain for some algebraically closed field `L` over `k`, then `F` is
geometrically reduced over `k`. -/
theorem isGeometricallyReduced_of_isDomain_tensorProduct (L : Type*) [Field L] [Algebra k L]
    [IsAlgClosed L] [IsDomain (F ⊗[k] L)] : Algebra.IsGeometricallyReduced k F := by
  have : IsDomain (L ⊗[k] F) := (Algebra.TensorProduct.comm k L F).toMulEquiv.isDomain
  exact Algebra.IsGeometricallyReduced.of_isReduced_tensorProduct L

/-- **Testing regularity against one algebraically closed field.** If `F ⊗[k] L` is a domain for
one algebraically closed field `L` over `k`, then `F ⊗[k] A` is a domain for every domain
`k`-algebra `A`. -/
theorem isDomain_tensorProduct_of_isDomain_tensorProduct_isAlgClosed (L : Type*) [Field L]
    [Algebra k L] [IsAlgClosed L] [IsDomain (F ⊗[k] L)] (A : Type*) [CommRing A] [IsDomain A]
    [Algebra k A] : IsDomain (F ⊗[k] A) :=
  have := isGeometricallyReduced_of_isDomain_tensorProduct (k := k) (F := F) L
  isDomain_tensorProduct_of_isGeometricallyReduced
    (isIntegrallyClosedIn_of_isDomain_tensorProduct L) A

/-- **Characterization of regular field extensions via an algebraically closed extension.** For any
algebraically closed field `L` over `k`, `F` is geometrically reduced over `k` with exact constants
if and only if `F ⊗[k] L` is a domain. -/
theorem isGeometricallyReduced_and_isIntegrallyClosedIn_iff_isDomain_tensorProduct
    (L : Type*) [Field L] [Algebra k L] [IsAlgClosed L] :
    Algebra.IsGeometricallyReduced k F ∧ IsIntegrallyClosedIn k F ↔ IsDomain (F ⊗[k] L) :=
  ⟨fun ⟨_, hex⟩ ↦ isDomain_tensorProduct_of_isGeometricallyReduced hex L,
    fun _ ↦ ⟨isGeometricallyReduced_of_isDomain_tensorProduct L,
      isIntegrallyClosedIn_of_isDomain_tensorProduct L⟩⟩

/-- **Characterization of regular field extensions via all scalar extensions.** A field extension
`F / k` is geometrically reduced with exact constants if and only if `F ⊗[k] K` is a domain for
every field extension `K / k`. -/
theorem isGeometricallyReduced_and_isIntegrallyClosedIn_iff_forall_isDomain_tensorProduct :
    Algebra.IsGeometricallyReduced k F ∧ IsIntegrallyClosedIn k F ↔
      ∀ (K : Type u) [Field K] [Algebra k K], IsDomain (F ⊗[k] K) :=
  ⟨fun ⟨_, hex⟩ K _ _ ↦ isDomain_tensorProduct_of_isGeometricallyReduced hex K,
    fun h ↦ have := h (AlgebraicClosure k)
      ⟨isGeometricallyReduced_of_isDomain_tensorProduct (AlgebraicClosure k),
        isIntegrallyClosedIn_of_isDomain_tensorProduct (AlgebraicClosure k)⟩⟩

/-- Over a perfect field, `k` is algebraically closed in `F` if and only if `F ⊗[k] L` is a domain
for a given algebraically closed field `L` over `k`. -/
theorem isIntegrallyClosedIn_iff_isDomain_tensorProduct_of_perfectField [PerfectField k]
    (L : Type*) [Field L] [Algebra k L] [IsAlgClosed L] :
    IsIntegrallyClosedIn k F ↔ IsDomain (F ⊗[k] L) :=
  ⟨fun hex ↦ isDomain_tensorProduct_of_perfectField hex L,
    fun _ ↦ isIntegrallyClosedIn_of_isDomain_tensorProduct L⟩

/-- Over a perfect field, `k` is algebraically closed in `F` if and only if `F ⊗[k] K` is a domain
for every field extension `K / k`. -/
theorem isIntegrallyClosedIn_iff_forall_isDomain_tensorProduct_of_perfectField [PerfectField k] :
    IsIntegrallyClosedIn k F ↔ ∀ (K : Type u) [Field K] [Algebra k K], IsDomain (F ⊗[k] K) :=
  ⟨fun hex K _ _ ↦ isDomain_tensorProduct_of_perfectField hex K,
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
  -- `(K ⊗[k] F) ⊗[K] A ≃ A ⊗[k] F` is a domain, and `Q` localizes `K ⊗[k] F` at nonzero divisors.
  let e : (K ⊗[k] F) ⊗[K] A ≃ₐ[K] A ⊗[k] F :=
    (Algebra.TensorProduct.comm K (K ⊗[k] F) A).trans
      (Algebra.TensorProduct.cancelBaseChange k K K A F)
  have : IsDomain ((K ⊗[k] F) ⊗[K] A) := e.toMulEquiv.isDomain
  exact isDomain_tensorProduct_of_isLocalization (nonZeroDivisors (K ⊗[k] F)) le_rfl Q A

/-- **Exact constants persist after arbitrary field base change of a regular extension.** If
`F / k` is geometrically reduced with exact constants and `K / k` is any field extension, then `K`
is algebraically closed in any fraction ring `Q` of `K ⊗[k] F`. -/
theorem isIntegrallyClosedIn_of_isFractionRing_left_tensorProduct
    (hex : IsIntegrallyClosedIn k F) [Algebra.IsGeometricallyReduced k F]
    {K Q : Type*} [Field K] [Algebra k K] [CommRing Q] [Algebra (K ⊗[k] F) Q] [Algebra K Q]
    [IsScalarTower K (K ⊗[k] F) Q] [IsFractionRing (K ⊗[k] F) Q] :
    IsIntegrallyClosedIn K Q := by
  have := isDomain_tensorProduct_of_isGeometricallyReduced' hex K
  let _ : Field Q := IsFractionRing.toField (K ⊗[k] F)
  have := isDomain_tensorProduct_of_isFractionRing_left_tensorProduct hex (K := K) (Q := Q)
    (AlgebraicClosure K)
  exact isIntegrallyClosedIn_of_isDomain_tensorProduct (k := K) (K := Q) (AlgebraicClosure K)

/-- **Geometric reducedness persists after arbitrary field base change of a regular extension.** If
`F / k` is geometrically reduced with exact constants and `K / k` is any field extension, then any
fraction ring `Q` of `K ⊗[k] F` is geometrically reduced over `K`. -/
theorem isGeometricallyReduced_of_isFractionRing_left_tensorProduct
    (hex : IsIntegrallyClosedIn k F) [Algebra.IsGeometricallyReduced k F]
    {K Q : Type*} [Field K] [Algebra k K] [CommRing Q] [Algebra (K ⊗[k] F) Q] [Algebra K Q]
    [IsScalarTower K (K ⊗[k] F) Q] [IsFractionRing (K ⊗[k] F) Q] :
    Algebra.IsGeometricallyReduced K Q := by
  have := isDomain_tensorProduct_of_isGeometricallyReduced' hex K
  let _ : Field Q := IsFractionRing.toField (K ⊗[k] F)
  have := isDomain_tensorProduct_of_isFractionRing_left_tensorProduct hex (K := K) (Q := Q)
    (AlgebraicClosure K)
  exact isGeometricallyReduced_of_isDomain_tensorProduct (k := K) (F := Q) (AlgebraicClosure K)

/-- **Over an algebraically closed base field, `Frac(F ⊗[k] L)` is regular over `F`.** For any two
field extensions `F / k` and `L / k` over an algebraically closed field `k`, any fraction ring `Q`
of `F ⊗[k] L`, and any domain `F`-algebra `A`, the tensor product `Q ⊗[F] A` is a domain. -/
theorem isDomain_tensorProduct_of_isFractionRing_tensorProduct_of_isAlgClosed [IsAlgClosed k]
    {L Q : Type*} [Field L] [Algebra k L] [CommRing Q] [Algebra (F ⊗[k] L) Q] [Algebra F Q]
    [IsScalarTower F (F ⊗[k] L) Q] [IsFractionRing (F ⊗[k] L) Q]
    (A : Type*) [CommRing A] [IsDomain A] [Algebra F A] :
    IsDomain (Q ⊗[F] A) :=
  isDomain_tensorProduct_of_isFractionRing_left_tensorProduct
    (F := L) (K := F) (isIntegrallyClosedIn_of_isAlgClosed (k := k) (A := L)) A

/-- **Relative algebraic closure in `Frac(F ⊗[k] L)` over an algebraically closed field.** If `k`
is algebraically closed, then for any two field extensions `F / k` and `L / k`, the field `F` is
integrally closed (relatively algebraically closed) in any fraction ring `Q` of `F ⊗[k] L`. -/
theorem isIntegrallyClosedIn_left_of_isFractionRing_tensorProduct_of_isAlgClosed [IsAlgClosed k]
    {L Q : Type*} [Field L] [Algebra k L] [CommRing Q] [Algebra (F ⊗[k] L) Q] [Algebra F Q]
    [IsScalarTower F (F ⊗[k] L) Q] [IsFractionRing (F ⊗[k] L) Q] :
    IsIntegrallyClosedIn F Q :=
  isIntegrallyClosedIn_of_isFractionRing_left_tensorProduct
    (F := L) (K := F) (isIntegrallyClosedIn_of_isAlgClosed (k := k) (A := L))

/-- Over an algebraically closed field `k`, for any two field extensions `F / k` and `L / k`, any
fraction ring `Q` of `F ⊗[k] L` is geometrically reduced over `F`. -/
theorem isGeometricallyReduced_left_of_isFractionRing_tensorProduct_of_isAlgClosed [IsAlgClosed k]
    {L Q : Type*} [Field L] [Algebra k L] [CommRing Q] [Algebra (F ⊗[k] L) Q] [Algebra F Q]
    [IsScalarTower F (F ⊗[k] L) Q] [IsFractionRing (F ⊗[k] L) Q] :
    Algebra.IsGeometricallyReduced F Q :=
  isGeometricallyReduced_of_isFractionRing_left_tensorProduct
    (F := L) (K := F) (isIntegrallyClosedIn_of_isAlgClosed (k := k) (A := L))

variable (k F) in
/-- Over an algebraically closed base field `k`, `F` is unconditionally relatively algebraically
closed in `FractionRing (F ⊗[k] K)` for any field extensions `F / k` and `K / k`. -/
theorem isIntegrallyClosedIn_left_fractionRing_tensorProduct_of_isAlgClosed [IsAlgClosed k]
    (K : Type*) [Field K] [Algebra k K] :
    IsIntegrallyClosedIn F (FractionRing (F ⊗[k] K)) :=
  isIntegrallyClosedIn_left_of_isFractionRing_tensorProduct_of_isAlgClosed (k := k) (L := K)

section RightAlgebra

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  Algebra.TensorProduct.right_isScalarTower

/-- Right-scalar companion to `TauCeti.isDomain_tensorProduct_of_isFractionRing_left_tensorProduct`,
viewing a fraction ring `Q` of `F ⊗[k] K` as a `K`-algebra via the right tensor factor. -/
theorem isDomain_tensorProduct_of_isFractionRing_tensorProduct
    (hex : IsIntegrallyClosedIn k F) [Algebra.IsGeometricallyReduced k F]
    {K Q : Type*} [Field K] [Algebra k K] [CommRing Q] [Algebra (F ⊗[k] K) Q] [Algebra K Q]
    [IsScalarTower K (F ⊗[k] K) Q] [IsFractionRing (F ⊗[k] K) Q]
    (A : Type*) [CommRing A] [IsDomain A] [Algebra K A] :
    IsDomain (Q ⊗[K] A) := by
  let σ : F ⊗[k] K ≃+* K ⊗[k] F := (Algebra.TensorProduct.comm k F K).toRingEquiv
  let _ : Algebra (K ⊗[k] F) Q := ((algebraMap (F ⊗[k] K) Q).comp σ.symm.toRingHom).toAlgebra
  have : IsScalarTower K (K ⊗[k] F) Q := .of_algebraMap_eq fun c ↦ by
    simp [σ, RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_apply K (F ⊗[k] K) Q]
  have : IsFractionRing (K ⊗[k] F) Q :=
    (IsFractionRing.isFractionRing_iff_of_base_ringEquiv Q σ).mp inferInstance
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
  have := isDomain_tensorProduct_of_isGeometricallyReduced hex K
  let _ : Field Q := IsFractionRing.toField (F ⊗[k] K)
  have := isDomain_tensorProduct_of_isFractionRing_tensorProduct hex (K := K) (Q := Q)
    (AlgebraicClosure K)
  exact isIntegrallyClosedIn_of_isDomain_tensorProduct (k := K) (K := Q) (AlgebraicClosure K)

/-- Right-scalar companion to
`TauCeti.isGeometricallyReduced_of_isFractionRing_left_tensorProduct`: if `F / k` is geometrically
reduced with exact constants and `K / k` is any field extension, then any fraction ring `Q` of
`F ⊗[k] K` is geometrically reduced over `K`. -/
theorem isGeometricallyReduced_of_isFractionRing_tensorProduct
    (hex : IsIntegrallyClosedIn k F) [Algebra.IsGeometricallyReduced k F]
    {K Q : Type*} [Field K] [Algebra k K] [CommRing Q] [Algebra (F ⊗[k] K) Q] [Algebra K Q]
    [IsScalarTower K (F ⊗[k] K) Q] [IsFractionRing (F ⊗[k] K) Q] :
    Algebra.IsGeometricallyReduced K Q := by
  have := isDomain_tensorProduct_of_isGeometricallyReduced hex K
  let _ : Field Q := IsFractionRing.toField (F ⊗[k] K)
  have := isDomain_tensorProduct_of_isFractionRing_tensorProduct hex (K := K) (Q := Q)
    (AlgebraicClosure K)
  exact isGeometricallyReduced_of_isDomain_tensorProduct (k := K) (F := Q) (AlgebraicClosure K)

/-- If `F / k` is geometrically reduced with exact constants, then `K` is algebraically closed in
`FractionRing (F ⊗[k] K)` for every field extension `K / k`. -/
theorem isIntegrallyClosedIn_fractionRing_tensorProduct (hex : IsIntegrallyClosedIn k F)
    [Algebra.IsGeometricallyReduced k F] (K : Type*) [Field K] [Algebra k K] :
    IsIntegrallyClosedIn K (FractionRing (F ⊗[k] K)) :=
  isIntegrallyClosedIn_of_isFractionRing_tensorProduct hex

/-- If `F / k` is geometrically reduced with exact constants, then `FractionRing (F ⊗[k] K)` is
geometrically reduced over `K` for every field extension `K / k`. -/
theorem isGeometricallyReduced_fractionRing_tensorProduct (hex : IsIntegrallyClosedIn k F)
    [Algebra.IsGeometricallyReduced k F] (K : Type*) [Field K] [Algebra k K] :
    Algebra.IsGeometricallyReduced K (FractionRing (F ⊗[k] K)) :=
  isGeometricallyReduced_of_isFractionRing_tensorProduct hex

/-- Over a perfect base field `k`, exactness of `k` in `F` implies that `K` is algebraically
closed in `FractionRing (F ⊗[k] K)` for every field extension `K / k`. -/
theorem isIntegrallyClosedIn_fractionRing_tensorProduct_of_perfectField [PerfectField k]
    (hex : IsIntegrallyClosedIn k F) (K : Type*) [Field K] [Algebra k K] :
    IsIntegrallyClosedIn K (FractionRing (F ⊗[k] K)) :=
  isIntegrallyClosedIn_fractionRing_tensorProduct hex K

/-- Over a perfect base field `k`, exactness of `k` in `F` implies that `FractionRing (F ⊗[k] K)`
is geometrically reduced over `K` for every field extension `K / k`. -/
theorem isGeometricallyReduced_fractionRing_tensorProduct_of_perfectField [PerfectField k]
    (hex : IsIntegrallyClosedIn k F) (K : Type*) [Field K] [Algebra k K] :
    Algebra.IsGeometricallyReduced K (FractionRing (F ⊗[k] K)) :=
  isGeometricallyReduced_fractionRing_tensorProduct hex K

variable (k F) in
/-- Over an algebraically closed base field `k`, `K` is unconditionally algebraically closed in
`FractionRing (F ⊗[k] K)` for any field extensions `F / k` and `K / k`. -/
theorem isIntegrallyClosedIn_fractionRing_tensorProduct_of_isAlgClosed [IsAlgClosed k]
    (K : Type*) [Field K] [Algebra k K] :
    IsIntegrallyClosedIn K (FractionRing (F ⊗[k] K)) :=
  isIntegrallyClosedIn_fractionRing_tensorProduct_of_perfectField
    (isIntegrallyClosedIn_of_isAlgClosed (k := k) (A := F)) K

variable (k F) in
/-- Over an algebraically closed base field `k`, `FractionRing (F ⊗[k] K)` is unconditionally
geometrically reduced over `K` for any field extensions `F / k` and `K / k`. -/
theorem isGeometricallyReduced_fractionRing_tensorProduct_of_isAlgClosed [IsAlgClosed k]
    (K : Type*) [Field K] [Algebra k K] :
    Algebra.IsGeometricallyReduced K (FractionRing (F ⊗[k] K)) :=
  isGeometricallyReduced_fractionRing_tensorProduct_of_perfectField
    (isIntegrallyClosedIn_of_isAlgClosed (k := k) (A := F)) K

end RightAlgebra

end BaseChange

end TauCeti
