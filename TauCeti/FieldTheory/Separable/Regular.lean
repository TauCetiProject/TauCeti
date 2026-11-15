/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import TauCeti.FieldTheory.Separable.GeometricallyReduced
public import TauCeti.RingTheory.TensorProduct.IsDomain
import TauCeti.FieldTheory.AlgebraicClosure
import TauCeti.FieldTheory.PurelyInseparable.TensorProduct
import TauCeti.RingTheory.IntegralClosure.IntegrallyClosed
import TauCeti.RingTheory.TensorProduct.Reduced

/-!
# Regular field extensions: characterizations, towers, and scalar stability

Let `F / k` be a field extension with a **separating element**: some `x ∈ F` is transcendental
over `k` and `F` is separable algebraic over `k(x)`. Then `F ⊗[k] K` is reduced for every
reduced `k`-algebra `K`, so `F` is geometrically reduced over `k`. If `F` is
geometrically reduced and `k` is algebraically closed in `F` (exact constants), then `F ⊗[k] K` is
a domain for every field extension `K / k`, and more generally `F ⊗[k] A` is a domain for every
`k`-algebra `A` that is a domain: in the language of Weil and Lang, `F` is a *regular* extension
of `k`. For a function field `F`, this says that the curve with function field `F` stays integral
after every extension of the constants.

Conversely, if `F ⊗[k] L` is a domain for a single algebraically closed field `L` over `k`, then
`k` is algebraically closed in `F` (`TauCeti.algebraicClosure_eq_bot_of_isDomain_tensorProduct`)
and `F / k` is geometrically reduced (`Algebra.IsGeometricallyReduced.of_isReduced_tensorProduct`).
Together with `TauCeti.isGeometricallyReduced_iff_isTranscendentalSeparable` (and
`TauCeti.isGeometricallyReduced_iff_isSeparablyGenerated` for finitely generated extensions), this
proves the equivalence of the standard definitions of a regular extension:

1. `k` is integrally closed in `F` and `F / k` is geometrically reduced (equivalently
   transcendentally separable, or separably generated when `F / k` is finitely generated);
2. `F ⊗[k] L` is a domain for one (equivalently every) algebraically closed field `L` over `k`;
3. `F ⊗[k] K` is a domain for every field extension `K / k`;
4. `F ⊗[k] A` is a domain for every `k`-algebra `A` that is a domain.

Over a perfect field `k`, geometric reducedness holds automatically, so regularity reduces to
`IsIntegrallyClosedIn k F`; over an algebraically closed field `k`, every field extension is
regular.

Regularity is stable under towers of field extensions (`IsIntegralClosure` transitivity together
with `Algebra.IsGeometricallyReduced.trans`) and under scalar extension through any specified
fraction field `Q` of `F ⊗[k] K`: if `F / k` is regular, then `Q / K` is regular; symmetrically, if
`K / k` is regular, then `Q / F` is regular. In particular, when `k` is algebraically closed, both
`F` and `K` are algebraically closed in `Q` (`IsIntegrallyClosedIn F Q` and
`IsIntegrallyClosedIn K Q`).

Both hypotheses are needed in general. Over `k = ℝ`, the field `ℂ(x)` has the separating element
`x`, but `ℂ(x) ⊗[ℝ] ℂ` is not a domain since the constants `ℂ` are not exact. Over an imperfect
field, exact constants alone do not suffice: for `k = 𝔽_p(a, b)` and `F = k(x, y)` with
`y ^ p = a + b x ^ p`, the element `y - a ^ (1/p) - b ^ (1/p) x` of
`F ⊗[k] k(a ^ (1/p), b ^ (1/p))` is nilpotent and nonzero.

## Main results

* `TauCeti.isReduced_tensorProduct_of_separating`, `TauCeti.isGeometricallyReduced_of_separating`:
  a separating element makes `F ⊗[k] K` reduced for every reduced `k`-algebra `K`, hence makes `F`
  geometrically reduced over `k`.
* `TauCeti.isDomain_tensorProduct_of_isGeometricallyReduced`,
  `TauCeti.isDomain_tensorProduct_of_isGeometricallyReduced_right`: if `F / k` is geometrically
  reduced with exact constants, then `F ⊗[k] A` and `A ⊗[k] F` are domains for every domain
  `k`-algebra `A`.
* `TauCeti.isDomain_tensorProduct_isAlgClosed_iff`,
  `TauCeti.forall_isDomain_tensorProduct_field_iff`,
  `TauCeti.forall_isDomain_tensorProduct_iff`: equivalent characterizations of regular extensions,
  with separable-generation and perfect-field specializations.
* `TauCeti.isDomain_tensorProduct_of_isGeometricallyReduced_tower`: tower stability of regular
  field extensions.
* `TauCeti.isIntegrallyClosedIn_right_of_isFractionRing_tensorProduct`,
  `TauCeti.isGeometricallyReduced_right_of_isFractionRing_tensorProduct`,
  `TauCeti.isIntegrallyClosedIn_left_of_isFractionRing_tensorProduct`,
  `TauCeti.isGeometricallyReduced_left_of_isFractionRing_tensorProduct`: scalar stability of
  regularity in any specified fraction field `Q` of `F ⊗[k] K`, together with `[PerfectField k]`
  and `[IsAlgClosed k]` specializations.

## References

* S. Lang, *Introduction to Algebraic Geometry*, Interscience, 1958, Chapter III, Section 1.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.6.
-/

public section

open scoped TensorProduct IntermediateField

namespace TauCeti

section Basic

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

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

/-- Right-factor form of `TauCeti.isDomain_tensorProduct_of_isGeometricallyReduced`: if `F / k` is
geometrically reduced with exact constants, then `A ⊗[k] F` is a domain for every domain
`k`-algebra `A`. -/
theorem isDomain_tensorProduct_of_isGeometricallyReduced_right (hex : IsIntegrallyClosedIn k F)
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

end Basic

section Equivalences

universe u v

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]

/-- If `F ⊗[k] L` is a domain for some algebraically closed field `L` over `k`, then `k` is
integrally closed in `F`. -/
theorem isIntegrallyClosedIn_of_isDomain_tensorProduct (L : Type*) [Field L] [Algebra k L]
    [IsAlgClosed L] [IsDomain (F ⊗[k] L)] : IsIntegrallyClosedIn k F := by
  rw [← IsIntegrallyClosedIn.integralClosure_eq_bot_iff F (algebraMap k F).injective,
    ← algebraicClosure_toSubalgebra, ← IntermediateField.bot_toSubalgebra,
    IntermediateField.toSubalgebra_inj]
  exact algebraicClosure_eq_bot_of_isDomain_tensorProduct L

/-- If `F ⊗[k] L` is a domain for some algebraically closed field `L` over `k`, then `F` is
geometrically reduced over `k`. -/
theorem isGeometricallyReduced_of_isDomain_tensorProduct (L : Type*) [Field L] [Algebra k L]
    [IsAlgClosed L] [IsDomain (F ⊗[k] L)] : Algebra.IsGeometricallyReduced k F := by
  have : IsDomain (L ⊗[k] F) := (Algebra.TensorProduct.comm k L F).toMulEquiv.isDomain
  exact Algebra.IsGeometricallyReduced.of_isReduced_tensorProduct L

/-- **Algebraically closed tensor criterion for regularity**: for any algebraically closed field
`L` over `k`, `F ⊗[k] L` is a domain if and only if `k` is integrally closed in `F` and `F / k` is
geometrically reduced. -/
theorem isDomain_tensorProduct_isAlgClosed_iff (L : Type*) [Field L] [Algebra k L]
    [IsAlgClosed L] :
    IsDomain (F ⊗[k] L) ↔ IsIntegrallyClosedIn k F ∧ Algebra.IsGeometricallyReduced k F :=
  ⟨fun _ ↦ ⟨isIntegrallyClosedIn_of_isDomain_tensorProduct L,
    isGeometricallyReduced_of_isDomain_tensorProduct L⟩,
    fun ⟨hex, _⟩ ↦ isDomain_tensorProduct_of_isGeometricallyReduced hex L⟩

/-- Regularity over `k` tested against an algebraically closed field `L`, expressed via
`Algebra.IsTranscendentalSeparable`. -/
theorem isDomain_tensorProduct_isAlgClosed_iff_isTranscendentalSeparable (L : Type*) [Field L]
    [Algebra k L] [IsAlgClosed L] :
    IsDomain (F ⊗[k] L) ↔ IsIntegrallyClosedIn k F ∧ Algebra.IsTranscendentalSeparable k F := by
  rw [isDomain_tensorProduct_isAlgClosed_iff, isGeometricallyReduced_iff_isTranscendentalSeparable]

/-- For a finitely generated field extension `F / k`, `F ⊗[k] L` is a domain (for an algebraically
closed `L / k`) if and only if `k` is integrally closed in `F` and `F / k` is separably
generated. -/
theorem isDomain_tensorProduct_isAlgClosed_iff_isSeparablyGenerated [Algebra.EssFiniteType k F]
    (L : Type*) [Field L] [Algebra k L] [IsAlgClosed L] :
    IsDomain (F ⊗[k] L) ↔ IsIntegrallyClosedIn k F ∧ Algebra.IsSeparablyGenerated k F := by
  rw [isDomain_tensorProduct_isAlgClosed_iff, isGeometricallyReduced_iff_isSeparablyGenerated]

/-- **Universal field-extension criterion for regularity**: `F ⊗[k] K` is a domain for every field
extension `K / k` (in `Type u`, the universe of `k`) if and only if `k` is integrally closed in `F`
and `F / k` is geometrically reduced. -/
theorem forall_isDomain_tensorProduct_field_iff :
    (∀ (K : Type u) [Field K] [Algebra k K], IsDomain (F ⊗[k] K)) ↔
      IsIntegrallyClosedIn k F ∧ Algebra.IsGeometricallyReduced k F :=
  ⟨fun h ↦
    letI := h (AlgebraicClosure k)
    (isDomain_tensorProduct_isAlgClosed_iff (AlgebraicClosure k)).mp inferInstance,
    fun ⟨hex, _⟩ K _ _ ↦ isDomain_tensorProduct_of_isGeometricallyReduced hex K⟩

/-- **Universal domain criterion for regularity**: `F ⊗[k] A` is a domain for every domain
`k`-algebra `A` (in `Type u`) if and only if `k` is integrally closed in `F` and `F / k` is
geometrically reduced. -/
theorem forall_isDomain_tensorProduct_iff :
    (∀ (A : Type u) [CommRing A] [IsDomain A] [Algebra k A], IsDomain (F ⊗[k] A)) ↔
      IsIntegrallyClosedIn k F ∧ Algebra.IsGeometricallyReduced k F :=
  ⟨fun h ↦
    letI := h (AlgebraicClosure k)
    (isDomain_tensorProduct_isAlgClosed_iff (AlgebraicClosure k)).mp inferInstance,
    fun ⟨hex, _⟩ A _ _ _ ↦ isDomain_tensorProduct_of_isGeometricallyReduced hex A⟩

/-- Over a perfect field `k`, exact constants alone make `F / k` regular: `F ⊗[k] A` is a domain
for every domain `k`-algebra `A`. -/
theorem isDomain_tensorProduct_of_perfectField [PerfectField k] (hex : IsIntegrallyClosedIn k F)
    (A : Type*) [CommRing A] [IsDomain A] [Algebra k A] : IsDomain (F ⊗[k] A) :=
  isDomain_tensorProduct_of_isGeometricallyReduced hex A

/-- Over a perfect field `k`, `F ⊗[k] L` is a domain (for an algebraically closed `L / k`) if and
only if `k` is integrally closed in `F`. -/
theorem isDomain_tensorProduct_isAlgClosed_iff_of_perfectField [PerfectField k] (L : Type*)
    [Field L] [Algebra k L] [IsAlgClosed L] :
    IsDomain (F ⊗[k] L) ↔ IsIntegrallyClosedIn k F := by
  rw [isDomain_tensorProduct_isAlgClosed_iff]
  exact and_iff_left inferInstance

/-- Over a perfect field `k`, `F ⊗[k] K` is a domain for all field extensions `K / k` (in `Type u`)
if and only if `k` is integrally closed in `F`. -/
theorem forall_isDomain_tensorProduct_field_iff_of_perfectField [PerfectField k] :
    (∀ (K : Type u) [Field K] [Algebra k K], IsDomain (F ⊗[k] K)) ↔ IsIntegrallyClosedIn k F := by
  rw [forall_isDomain_tensorProduct_field_iff]
  exact and_iff_left inferInstance

end Equivalences

section Tower

/-- **Regularity is transitive in towers of field extensions**: if `E / k` and `F / E` are
geometrically reduced with exact constants, then `F ⊗[k] A` is a domain for every domain
`k`-algebra `A`. -/
theorem isDomain_tensorProduct_of_isGeometricallyReduced_tower {k E F : Type*} [Field k] [Field E]
    [Field F] [Algebra k E] [Algebra E F] [Algebra k F] [IsScalarTower k E F]
    [IsIntegrallyClosedIn k E] [IsIntegrallyClosedIn E F]
    [Algebra.IsGeometricallyReduced k E] [Algebra.IsGeometricallyReduced E F]
    (A : Type*) [CommRing A] [IsDomain A] [Algebra k A] : IsDomain (F ⊗[k] A) :=
  have hex : IsIntegrallyClosedIn k F :=
    IsIntegralClosure.of_isIntegralClosure_of_isIntegrallyClosedIn k k E F
  have : Algebra.IsGeometricallyReduced k F := Algebra.IsGeometricallyReduced.trans k E F
  isDomain_tensorProduct_of_isGeometricallyReduced hex A

end Tower

section FractionRing

section LeftRegular

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  Algebra.TensorProduct.right_isScalarTower

variable {k F K Q : Type*} [Field k] [Field F] [Field K] [Field Q]
  [Algebra k F] [Algebra k K] [Algebra (F ⊗[k] K) Q] [Algebra K Q]
  [IsScalarTower K (F ⊗[k] K) Q] [IsFractionRing (F ⊗[k] K) Q]

/-- **Scalar stability of regularity (domain form, left-regular factor)**: if `F / k` is regular
and `Q` is a specified fraction field of `F ⊗[k] K`, then `Q ⊗[K] D` is a domain for every domain
`K`-algebra `D`. -/
theorem isDomain_tensorProduct_of_isFractionRing_tensorProduct_left
    (hex : IsIntegrallyClosedIn k F) [Algebra.IsGeometricallyReduced k F]
    (D : Type*) [CommRing D] [IsDomain D] [Algebra K D] : IsDomain (Q ⊗[K] D) := by
  let _ : Algebra k D := Algebra.compHom D (algebraMap k K)
  have : IsScalarTower k K D := .of_algebraMap_eq' rfl
  have : IsDomain (F ⊗[k] D) := isDomain_tensorProduct_of_isGeometricallyReduced hex D
  exact isDomain_tensorProduct_of_isLocalization_tensorProduct_right
    (nonZeroDivisors (F ⊗[k] K)) le_rfl Q D

/-- **Scalar stability of exact constants**: if `F / k` is regular and `Q` is a specified fraction
field of `F ⊗[k] K`, then `K` is integrally closed in `Q` (no new constants appear over `K`). -/
theorem isIntegrallyClosedIn_right_of_isFractionRing_tensorProduct
    (hex : IsIntegrallyClosedIn k F) [Algebra.IsGeometricallyReduced k F] :
    IsIntegrallyClosedIn K Q := by
  have : IsDomain (Q ⊗[K] AlgebraicClosure K) :=
    isDomain_tensorProduct_of_isFractionRing_tensorProduct_left hex (AlgebraicClosure K)
  exact isIntegrallyClosedIn_of_isDomain_tensorProduct (F := Q) (AlgebraicClosure K)

/-- Relative-algebraic-closure form of
`TauCeti.isIntegrallyClosedIn_right_of_isFractionRing_tensorProduct`. -/
theorem algebraicClosure_right_eq_bot_of_isFractionRing_tensorProduct
    (hex : IsIntegrallyClosedIn k F) [Algebra.IsGeometricallyReduced k F] :
    algebraicClosure K Q = ⊥ := by
  have : IsDomain (Q ⊗[K] AlgebraicClosure K) :=
    isDomain_tensorProduct_of_isFractionRing_tensorProduct_left hex (AlgebraicClosure K)
  exact algebraicClosure_eq_bot_of_isDomain_tensorProduct (K := Q) (AlgebraicClosure K)

/-- **Scalar stability of geometric reducedness**: if `F / k` is regular and `Q` is a specified
fraction field of `F ⊗[k] K`, then `Q` is geometrically reduced over `K`. -/
theorem isGeometricallyReduced_right_of_isFractionRing_tensorProduct
    (hex : IsIntegrallyClosedIn k F) [Algebra.IsGeometricallyReduced k F] :
    Algebra.IsGeometricallyReduced K Q := by
  have : IsDomain (Q ⊗[K] AlgebraicClosure K) :=
    isDomain_tensorProduct_of_isFractionRing_tensorProduct_left hex (AlgebraicClosure K)
  exact isGeometricallyReduced_of_isDomain_tensorProduct (F := Q) (AlgebraicClosure K)

/-- Over a perfect base field `k`, exactness of `k` in `F` implies that `K` is integrally closed in
any specified fraction field `Q` of `F ⊗[k] K`. -/
theorem isIntegrallyClosedIn_right_of_isFractionRing_tensorProduct_of_perfectField [PerfectField k]
    (hex : IsIntegrallyClosedIn k F) : IsIntegrallyClosedIn K Q :=
  isIntegrallyClosedIn_right_of_isFractionRing_tensorProduct hex

end LeftRegular

section RightRegular

variable {k F K Q : Type*} [Field k] [Field F] [Field K] [Field Q]
  [Algebra k F] [Algebra k K] [Algebra (F ⊗[k] K) Q] [Algebra F Q]
  [IsScalarTower F (F ⊗[k] K) Q] [IsFractionRing (F ⊗[k] K) Q]

/-- **Scalar stability of regularity (domain form, right-regular factor)**: if `K / k` is regular
and `Q` is a specified fraction field of `F ⊗[k] K`, then `Q ⊗[F] D` is a domain for every domain
`F`-algebra `D`. -/
theorem isDomain_tensorProduct_of_isFractionRing_tensorProduct_right
    (hex : IsIntegrallyClosedIn k K) [Algebra.IsGeometricallyReduced k K]
    (D : Type*) [CommRing D] [IsDomain D] [Algebra F D] : IsDomain (Q ⊗[F] D) := by
  let _ : Algebra k D := Algebra.compHom D (algebraMap k F)
  have : IsScalarTower k F D := .of_algebraMap_eq' rfl
  have : IsDomain (D ⊗[k] K) := isDomain_tensorProduct_of_isGeometricallyReduced_right hex D
  exact isDomain_tensorProduct_of_isLocalization_tensorProduct_left
    (nonZeroDivisors (F ⊗[k] K)) le_rfl Q D

/-- **Symmetric scalar stability of exact constants**: if `K / k` is regular and `Q` is a specified
fraction field of `F ⊗[k] K`, then `F` is integrally closed in `Q`. -/
theorem isIntegrallyClosedIn_left_of_isFractionRing_tensorProduct
    (hex : IsIntegrallyClosedIn k K) [Algebra.IsGeometricallyReduced k K] :
    IsIntegrallyClosedIn F Q := by
  have : IsDomain (Q ⊗[F] AlgebraicClosure F) :=
    isDomain_tensorProduct_of_isFractionRing_tensorProduct_right hex (AlgebraicClosure F)
  exact isIntegrallyClosedIn_of_isDomain_tensorProduct (F := Q) (AlgebraicClosure F)

/-- Relative-algebraic-closure form of
`TauCeti.isIntegrallyClosedIn_left_of_isFractionRing_tensorProduct`. -/
theorem algebraicClosure_left_eq_bot_of_isFractionRing_tensorProduct
    (hex : IsIntegrallyClosedIn k K) [Algebra.IsGeometricallyReduced k K] :
    algebraicClosure F Q = ⊥ := by
  have : IsDomain (Q ⊗[F] AlgebraicClosure F) :=
    isDomain_tensorProduct_of_isFractionRing_tensorProduct_right hex (AlgebraicClosure F)
  exact algebraicClosure_eq_bot_of_isDomain_tensorProduct (K := Q) (AlgebraicClosure F)

/-- **Symmetric scalar stability of geometric reducedness**: if `K / k` is regular and `Q` is a
specified fraction field of `F ⊗[k] K`, then `Q` is geometrically reduced over `F`. -/
theorem isGeometricallyReduced_left_of_isFractionRing_tensorProduct
    (hex : IsIntegrallyClosedIn k K) [Algebra.IsGeometricallyReduced k K] :
    Algebra.IsGeometricallyReduced F Q := by
  have : IsDomain (Q ⊗[F] AlgebraicClosure F) :=
    isDomain_tensorProduct_of_isFractionRing_tensorProduct_right hex (AlgebraicClosure F)
  exact isGeometricallyReduced_of_isDomain_tensorProduct (F := Q) (AlgebraicClosure F)

/-- Over a perfect base field `k`, exactness of `k` in `K` implies that `F` is integrally closed in
any specified fraction field `Q` of `F ⊗[k] K`. -/
theorem isIntegrallyClosedIn_left_of_isFractionRing_tensorProduct_of_perfectField [PerfectField k]
    (hex : IsIntegrallyClosedIn k K) : IsIntegrallyClosedIn F Q :=
  isIntegrallyClosedIn_left_of_isFractionRing_tensorProduct hex

end RightRegular

section IsAlgClosed

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  Algebra.TensorProduct.right_isScalarTower in
/-- Over an algebraically closed field `k`, `K` is integrally closed in any specified fraction
field `Q` of `F ⊗[k] K`. -/
theorem isIntegrallyClosedIn_right_of_isFractionRing_tensorProduct_of_isAlgClosed
    (k F : Type*) {K Q : Type*} [Field k] [IsAlgClosed k] [Field F] [Field K] [Field Q]
    [Algebra k F] [Algebra k K] [Algebra (F ⊗[k] K) Q] [Algebra K Q]
    [IsScalarTower K (F ⊗[k] K) Q] [IsFractionRing (F ⊗[k] K) Q] :
    IsIntegrallyClosedIn K Q :=
  isIntegrallyClosedIn_right_of_isFractionRing_tensorProduct
    (isIntegrallyClosedIn_of_isAlgClosed (k := k) (A := F))

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  Algebra.TensorProduct.right_isScalarTower in
/-- Over an algebraically closed field `k`, any specified fraction field `Q` of `F ⊗[k] K` is
geometrically reduced over `K`. -/
theorem isGeometricallyReduced_right_of_isFractionRing_tensorProduct_of_isAlgClosed
    (k F : Type*) {K Q : Type*} [Field k] [IsAlgClosed k] [Field F] [Field K] [Field Q]
    [Algebra k F] [Algebra k K] [Algebra (F ⊗[k] K) Q] [Algebra K Q]
    [IsScalarTower K (F ⊗[k] K) Q] [IsFractionRing (F ⊗[k] K) Q] :
    Algebra.IsGeometricallyReduced K Q :=
  isGeometricallyReduced_right_of_isFractionRing_tensorProduct
    (isIntegrallyClosedIn_of_isAlgClosed (k := k) (A := F))

/-- **Fixed-base algebraically closed constant extension has no algebraic elements over `F`**: over
an algebraically closed field `k`, `F` is integrally closed in any specified fraction field `Q` of
`F ⊗[k] K`. -/
theorem isIntegrallyClosedIn_left_of_isFractionRing_tensorProduct_of_isAlgClosed
    (k K : Type*) {F Q : Type*} [Field k] [IsAlgClosed k] [Field F] [Field K] [Field Q]
    [Algebra k F] [Algebra k K] [Algebra (F ⊗[k] K) Q] [Algebra F Q]
    [IsScalarTower F (F ⊗[k] K) Q] [IsFractionRing (F ⊗[k] K) Q] :
    IsIntegrallyClosedIn F Q :=
  isIntegrallyClosedIn_left_of_isFractionRing_tensorProduct
    (isIntegrallyClosedIn_of_isAlgClosed (k := k) (A := K))

/-- Over an algebraically closed field `k`, any specified fraction field `Q` of `F ⊗[k] K` is
geometrically reduced over `F`. -/
theorem isGeometricallyReduced_left_of_isFractionRing_tensorProduct_of_isAlgClosed
    (k K : Type*) {F Q : Type*} [Field k] [IsAlgClosed k] [Field F] [Field K] [Field Q]
    [Algebra k F] [Algebra k K] [Algebra (F ⊗[k] K) Q] [Algebra F Q]
    [IsScalarTower F (F ⊗[k] K) Q] [IsFractionRing (F ⊗[k] K) Q] :
    Algebra.IsGeometricallyReduced F Q :=
  isGeometricallyReduced_left_of_isFractionRing_tensorProduct
    (isIntegrallyClosedIn_of_isAlgClosed (k := k) (A := K))

end IsAlgClosed

end FractionRing

end TauCeti
