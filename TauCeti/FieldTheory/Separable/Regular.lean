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
# Regular field extensions: characterizations and scalar stability

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

More generally, if `B ⊗[k] L` is a domain for one algebraically closed field `L` over `k`, then
`B ⊗[k] A` is a domain for every domain `k`-algebra `A`, for any commutative `k`-algebra `B`
(`TauCeti.isDomain_tensorProduct_of_isDomain_tensorProduct_isAlgClosed`).

Over a perfect field `k`, geometric reducedness holds automatically, so regularity reduces to
`IsIntegrallyClosedIn k F`; over an algebraically closed field `k`, every field extension is
regular.

Regularity is stable under scalar extension through any specified total ring of fractions `Q` of
`F ⊗[k] K`, for an arbitrary (possibly transcendental) field extension `K / k`: if `F / k` is
regular, then `Q / K` is regular; symmetrically, if `K / k` is regular, then `Q / F` is regular.
Indeed `Q ⊗[K] D` is a localization of `F ⊗[k] D`. In particular, when `k` is algebraically closed,
`F` is algebraically closed in any total ring of fractions `Q` of `F ⊗[k] B` for every domain
`k`-algebra `B`, and symmetrically.

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
* `TauCeti.isDomain_tensorProduct_iff_of_isAlgClosed`,
  `TauCeti.forall_isDomain_tensorProduct_field_iff`,
  `TauCeti.forall_isDomain_tensorProduct_iff`: equivalent characterizations of regular extensions.
* `TauCeti.isDomain_tensorProduct_of_isDomain_tensorProduct_isAlgClosed`: if `B ⊗[k] L` is a domain
  for one algebraically closed field `L / k`, then `B ⊗[k] A` is a domain for every domain
  `k`-algebra `A`.
* `TauCeti.isIntegrallyClosedIn_iff_isDomain_tensorProduct_of_perfectField`,
  `TauCeti.isIntegrallyClosedIn_iff_forall_isDomain_tensorProduct_of_perfectField`: over a perfect
  field, regularity is equivalent to exact constants.
* `TauCeti.isDomain_tensorProduct_right_of_isFractionRing_tensorProduct`,
  `TauCeti.isIntegrallyClosedIn_right_of_isFractionRing_tensorProduct`,
  `TauCeti.isGeometricallyReduced_right_of_isFractionRing_tensorProduct`,
  `TauCeti.isDomain_tensorProduct_left_of_isFractionRing_tensorProduct`,
  `TauCeti.isIntegrallyClosedIn_left_of_isFractionRing_tensorProduct`,
  `TauCeti.isGeometricallyReduced_left_of_isFractionRing_tensorProduct`: scalar stability of
  regularity in any specified total ring of fractions `Q` of `F ⊗[k] K`, together with
  `[IsAlgClosed k]` specializations in which the other factor need only be a domain.

## References

* S. Lang, *Introduction to Algebraic Geometry*, Interscience, 1958, Chapter III, Section 1.
* N. Bourbaki, *Algebra II*, Chapters 4–7, Chapter V, Section 17.
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

/-- If `A ⊗[k] L` is a domain for some algebraically closed field `L` over `k`, then the
commutative `k`-algebra `A` is geometrically reduced over `k`. Together with
`TauCeti.isIntegrallyClosedIn_of_isDomain_tensorProduct`, this is the converse half of the
regularity criterion. -/
theorem isGeometricallyReduced_of_isDomain_tensorProduct {A : Type*} [CommRing A] [Algebra k A]
    (L : Type*) [Field L] [Algebra k L] [IsAlgClosed L] [IsDomain (A ⊗[k] L)] :
    Algebra.IsGeometricallyReduced k A :=
  Algebra.IsGeometricallyReduced.of_isReduced_tensorProduct' L

/-- **Algebraically closed tensor criterion for regularity**: for any algebraically closed field
`L` over `k`, `F ⊗[k] L` is a domain if and only if `k` is integrally closed in `F` and `F / k` is
geometrically reduced. -/
theorem isDomain_tensorProduct_iff_of_isAlgClosed (L : Type*) [Field L] [Algebra k L]
    [IsAlgClosed L] :
    IsDomain (F ⊗[k] L) ↔ IsIntegrallyClosedIn k F ∧ Algebra.IsGeometricallyReduced k F :=
  ⟨fun _ ↦ ⟨isIntegrallyClosedIn_of_isDomain_tensorProduct L,
    isGeometricallyReduced_of_isDomain_tensorProduct L⟩,
    fun ⟨hex, _⟩ ↦ isDomain_tensorProduct_of_isGeometricallyReduced hex L⟩

/-- **Universal field-extension criterion for regularity**: `F ⊗[k] K` is a domain for every field
extension `K / k` (in `Type u`, the universe of `k`) if and only if `k` is integrally closed in `F`
and `F / k` is geometrically reduced. -/
theorem forall_isDomain_tensorProduct_field_iff :
    (∀ (K : Type u) [Field K] [Algebra k K], IsDomain (F ⊗[k] K)) ↔
      IsIntegrallyClosedIn k F ∧ Algebra.IsGeometricallyReduced k F :=
  ⟨fun h ↦
    letI := h (AlgebraicClosure k)
    (isDomain_tensorProduct_iff_of_isAlgClosed (AlgebraicClosure k)).mp inferInstance,
    fun ⟨hex, _⟩ K _ _ ↦ isDomain_tensorProduct_of_isGeometricallyReduced hex K⟩

/-- **Universal domain criterion for regularity**: `F ⊗[k] A` is a domain for every domain
`k`-algebra `A` (in `Type u`) if and only if `k` is integrally closed in `F` and `F / k` is
geometrically reduced. -/
theorem forall_isDomain_tensorProduct_iff :
    (∀ (A : Type u) [CommRing A] [IsDomain A] [Algebra k A], IsDomain (F ⊗[k] A)) ↔
      IsIntegrallyClosedIn k F ∧ Algebra.IsGeometricallyReduced k F :=
  ⟨fun h ↦
    letI := h (AlgebraicClosure k)
    (isDomain_tensorProduct_iff_of_isAlgClosed (AlgebraicClosure k)).mp inferInstance,
    fun ⟨hex, _⟩ A _ _ _ ↦ isDomain_tensorProduct_of_isGeometricallyReduced hex A⟩

/-- **Testing regularity against one algebraically closed field.** If `B ⊗[k] L` is a domain for
one algebraically closed field `L` over `k`, then `B ⊗[k] A` is a domain for every domain
`k`-algebra `A`. Here `B` is an arbitrary commutative `k`-algebra, not necessarily a field. -/
theorem isDomain_tensorProduct_of_isDomain_tensorProduct_isAlgClosed {B : Type*} [CommRing B]
    [Algebra k B] (L : Type*) [Field L] [Algebra k L] [IsAlgClosed L] [IsDomain (B ⊗[k] L)]
    (A : Type*) [CommRing A] [IsDomain A] [Algebra k A] : IsDomain (B ⊗[k] A) := by
  have : IsDomain B :=
    (Algebra.TensorProduct.includeLeft_injective (S := k) (algebraMap k L).injective).isDomain
      (Algebra.TensorProduct.includeLeft : B →ₐ[k] B ⊗[k] L)
  have : IsDomain (FractionRing B ⊗[k] L) :=
    isDomain_tensorProduct_of_isLocalization (nonZeroDivisors B) le_rfl (FractionRing B) L
  have : Algebra.IsGeometricallyReduced k (FractionRing B) :=
    isGeometricallyReduced_of_isDomain_tensorProduct L
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

end Equivalences

section FractionRing

section LeftRegular

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  Algebra.TensorProduct.right_isScalarTower

variable {k F K Q : Type*} [Field k] [Field F] [Field K] [CommRing Q]
  [Algebra k F] [Algebra k K] [Algebra (F ⊗[k] K) Q] [Algebra K Q]
  [IsScalarTower K (F ⊗[k] K) Q] [IsFractionRing (F ⊗[k] K) Q]

/-- **Scalar stability of regularity (domain form, over the right factor)**: if `F / k` is regular
and `Q` is a specified total ring of fractions of `F ⊗[k] K`, then `Q ⊗[K] D` is a domain for every
domain `K`-algebra `D`. Here `K / k` is an arbitrary, possibly transcendental, field extension. -/
theorem isDomain_tensorProduct_right_of_isFractionRing_tensorProduct
    (hex : IsIntegrallyClosedIn k F) [Algebra.IsGeometricallyReduced k F]
    (D : Type*) [CommRing D] [IsDomain D] [Algebra K D] : IsDomain (Q ⊗[K] D) := by
  let _ : Algebra k D := Algebra.compHom D (algebraMap k K)
  have : IsScalarTower k K D := .of_algebraMap_eq' rfl
  have : IsDomain (F ⊗[k] D) := isDomain_tensorProduct_of_isGeometricallyReduced hex D
  exact isDomain_tensorProduct_of_isLocalization_tensorProduct_right
    (nonZeroDivisors (F ⊗[k] K)) le_rfl Q D

/-- **Scalar stability of exact constants**: if `F / k` is regular and `Q` is a specified total ring
of fractions of `F ⊗[k] K`, then `K` is integrally closed in `Q` (no new constants appear over
`K`). -/
theorem isIntegrallyClosedIn_right_of_isFractionRing_tensorProduct
    (hex : IsIntegrallyClosedIn k F) [Algebra.IsGeometricallyReduced k F] :
    IsIntegrallyClosedIn K Q := by
  have : IsDomain (Q ⊗[K] AlgebraicClosure K) :=
    isDomain_tensorProduct_right_of_isFractionRing_tensorProduct hex (AlgebraicClosure K)
  exact isIntegrallyClosedIn_of_isDomain_tensorProduct (A := Q) (AlgebraicClosure K)

/-- **Scalar stability of geometric reducedness**: if `F / k` is regular and `Q` is a specified
total ring of fractions of `F ⊗[k] K`, then `Q` is geometrically reduced over `K`. -/
theorem isGeometricallyReduced_right_of_isFractionRing_tensorProduct
    (hex : IsIntegrallyClosedIn k F) [Algebra.IsGeometricallyReduced k F] :
    Algebra.IsGeometricallyReduced K Q := by
  have : IsDomain (Q ⊗[K] AlgebraicClosure K) :=
    isDomain_tensorProduct_right_of_isFractionRing_tensorProduct hex (AlgebraicClosure K)
  exact isGeometricallyReduced_of_isDomain_tensorProduct (A := Q) (AlgebraicClosure K)

end LeftRegular

section RightRegular

variable {k F K Q : Type*} [Field k] [Field F] [Field K] [CommRing Q]
  [Algebra k F] [Algebra k K] [Algebra (F ⊗[k] K) Q] [Algebra F Q]
  [IsScalarTower F (F ⊗[k] K) Q] [IsFractionRing (F ⊗[k] K) Q]

/-- **Scalar stability of regularity (domain form, over the left factor)**: if `K / k` is regular
and `Q` is a specified total ring of fractions of `F ⊗[k] K`, then `Q ⊗[F] D` is a domain for every
domain `F`-algebra `D`. -/
theorem isDomain_tensorProduct_left_of_isFractionRing_tensorProduct
    (hex : IsIntegrallyClosedIn k K) [Algebra.IsGeometricallyReduced k K]
    (D : Type*) [CommRing D] [IsDomain D] [Algebra F D] : IsDomain (Q ⊗[F] D) := by
  let _ : Algebra k D := Algebra.compHom D (algebraMap k F)
  have : IsScalarTower k F D := .of_algebraMap_eq' rfl
  have : IsDomain (D ⊗[k] K) := isDomain_tensorProduct_of_isGeometricallyReduced_right hex D
  exact isDomain_tensorProduct_of_isLocalization_tensorProduct_left
    (nonZeroDivisors (F ⊗[k] K)) le_rfl Q D

/-- **Symmetric scalar stability of exact constants**: if `K / k` is regular and `Q` is a specified
total ring of fractions of `F ⊗[k] K`, then `F` is integrally closed in `Q`. -/
theorem isIntegrallyClosedIn_left_of_isFractionRing_tensorProduct
    (hex : IsIntegrallyClosedIn k K) [Algebra.IsGeometricallyReduced k K] :
    IsIntegrallyClosedIn F Q := by
  have : IsDomain (Q ⊗[F] AlgebraicClosure F) :=
    isDomain_tensorProduct_left_of_isFractionRing_tensorProduct hex (AlgebraicClosure F)
  exact isIntegrallyClosedIn_of_isDomain_tensorProduct (A := Q) (AlgebraicClosure F)

/-- **Symmetric scalar stability of geometric reducedness**: if `K / k` is regular and `Q` is a
specified total ring of fractions of `F ⊗[k] K`, then `Q` is geometrically reduced over `F`. -/
theorem isGeometricallyReduced_left_of_isFractionRing_tensorProduct
    (hex : IsIntegrallyClosedIn k K) [Algebra.IsGeometricallyReduced k K] :
    Algebra.IsGeometricallyReduced F Q := by
  have : IsDomain (Q ⊗[F] AlgebraicClosure F) :=
    isDomain_tensorProduct_left_of_isFractionRing_tensorProduct hex (AlgebraicClosure F)
  exact isGeometricallyReduced_of_isDomain_tensorProduct (A := Q) (AlgebraicClosure F)

end RightRegular

section IsAlgClosed

/-! Over an algebraically closed field `k`, the tensor product of two domains is a domain
(`TauCeti.isDomain_tensorProduct_of_isAlgClosed`), so the other factor only needs to be a domain
rather than a field. -/

section Right

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  Algebra.TensorProduct.right_isScalarTower

variable (k A : Type*) {K Q : Type*} [Field k] [IsAlgClosed k] [CommRing A] [IsDomain A] [Field K]
  [CommRing Q] [Algebra k A] [Algebra k K] [Algebra (A ⊗[k] K) Q] [Algebra K Q]
  [IsScalarTower K (A ⊗[k] K) Q] [IsFractionRing (A ⊗[k] K) Q]

include k A

/-- Over an algebraically closed field `k`, for any domain `k`-algebra `A` and any field
extension `K / k`, the tensor product `Q ⊗[K] D` is a domain for every specified total ring of
fractions `Q` of `A ⊗[k] K` and every domain `K`-algebra `D`. -/
theorem isDomain_tensorProduct_right_of_isFractionRing_tensorProduct_of_isAlgClosed
    (D : Type*) [CommRing D] [IsDomain D] [Algebra K D] : IsDomain (Q ⊗[K] D) := by
  let _ : Algebra k D := Algebra.compHom D (algebraMap k K)
  have : IsScalarTower k K D := .of_algebraMap_eq' rfl
  exact isDomain_tensorProduct_of_isLocalization_tensorProduct_right
    (nonZeroDivisors (A ⊗[k] K)) le_rfl Q D

/-- Over an algebraically closed field `k`, `K` is integrally closed (relatively algebraically
closed) in any specified total ring of fractions `Q` of `A ⊗[k] K`, for any domain `k`-algebra
`A`. -/
theorem isIntegrallyClosedIn_right_of_isFractionRing_tensorProduct_of_isAlgClosed :
    IsIntegrallyClosedIn K Q := by
  have := isDomain_tensorProduct_right_of_isFractionRing_tensorProduct_of_isAlgClosed k A
    (K := K) (Q := Q) (AlgebraicClosure K)
  exact isIntegrallyClosedIn_of_isDomain_tensorProduct (A := Q) (AlgebraicClosure K)

/-- Over an algebraically closed field `k`, any specified total ring of fractions `Q` of
`A ⊗[k] K` is geometrically reduced over `K`, for any domain `k`-algebra `A`. -/
theorem isGeometricallyReduced_right_of_isFractionRing_tensorProduct_of_isAlgClosed :
    Algebra.IsGeometricallyReduced K Q := by
  have := isDomain_tensorProduct_right_of_isFractionRing_tensorProduct_of_isAlgClosed k A
    (K := K) (Q := Q) (AlgebraicClosure K)
  exact isGeometricallyReduced_of_isDomain_tensorProduct (A := Q) (AlgebraicClosure K)

end Right

section Left

variable (k B : Type*) {F Q : Type*} [Field k] [IsAlgClosed k] [CommRing B] [IsDomain B] [Field F]
  [CommRing Q] [Algebra k B] [Algebra k F] [Algebra (F ⊗[k] B) Q] [Algebra F Q]
  [IsScalarTower F (F ⊗[k] B) Q] [IsFractionRing (F ⊗[k] B) Q]

include k B

/-- Over an algebraically closed field `k`, for any field extension `F / k` and any domain
`k`-algebra `B`, the tensor product `Q ⊗[F] D` is a domain for every specified total ring of
fractions `Q` of `F ⊗[k] B` and every domain `F`-algebra `D`. -/
theorem isDomain_tensorProduct_left_of_isFractionRing_tensorProduct_of_isAlgClosed
    (D : Type*) [CommRing D] [IsDomain D] [Algebra F D] : IsDomain (Q ⊗[F] D) := by
  let _ : Algebra k D := Algebra.compHom D (algebraMap k F)
  have : IsScalarTower k F D := .of_algebraMap_eq' rfl
  exact isDomain_tensorProduct_of_isLocalization_tensorProduct_left
    (nonZeroDivisors (F ⊗[k] B)) le_rfl Q D

/-- **Fixed-base algebraically closed constant extension has no algebraic elements over `F`**: over
an algebraically closed field `k`, `F` is integrally closed (relatively algebraically closed) in any
specified total ring of fractions `Q` of `F ⊗[k] B`, for any domain `k`-algebra `B`. -/
theorem isIntegrallyClosedIn_left_of_isFractionRing_tensorProduct_of_isAlgClosed :
    IsIntegrallyClosedIn F Q := by
  have := isDomain_tensorProduct_left_of_isFractionRing_tensorProduct_of_isAlgClosed k B
    (F := F) (Q := Q) (AlgebraicClosure F)
  exact isIntegrallyClosedIn_of_isDomain_tensorProduct (A := Q) (AlgebraicClosure F)

/-- Over an algebraically closed field `k`, any specified total ring of fractions `Q` of
`F ⊗[k] B` is geometrically reduced over `F`, for any domain `k`-algebra `B`. -/
theorem isGeometricallyReduced_left_of_isFractionRing_tensorProduct_of_isAlgClosed :
    Algebra.IsGeometricallyReduced F Q := by
  have := isDomain_tensorProduct_left_of_isFractionRing_tensorProduct_of_isAlgClosed k B
    (F := F) (Q := Q) (AlgebraicClosure F)
  exact isGeometricallyReduced_of_isDomain_tensorProduct (A := Q) (AlgebraicClosure F)

end Left

end IsAlgClosed

end FractionRing

end TauCeti
