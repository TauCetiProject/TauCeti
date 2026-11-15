/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.FieldTheory.SeparablyGenerated
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import TauCeti.FieldTheory.AlgebraicClosure
import TauCeti.FieldTheory.PurelyInseparable.TensorProduct
import TauCeti.FieldTheory.Separable.GeometricallyReduced
import TauCeti.RingTheory.IntegralClosure.IntegrallyClosed
import TauCeti.RingTheory.TensorProduct.IsDomain
import TauCeti.RingTheory.TensorProduct.Reduced

/-!
# Regular field extensions, exact constants, and extension of scalars

Let `F / k` be a field extension. If `F` is separable algebraic over a purely transcendental
subextension `k(x_ι)` (`x : ι → F` algebraically independent over `k`), then `F ⊗[k] A` is
reduced for every reduced `k`-algebra `A`, so `F` is geometrically reduced over `k`. For
finitely generated extensions `F / k`, combining this with
`TauCeti.exists_isTranscendenceBasis_and_isSeparable_of_isGeometricallyReduced` equates
geometric reducedness with the existence of a finite separating transcendence basis.

If `F` is geometrically reduced and `k` is algebraically closed in `F` (exact constants), then
`F ⊗[k] A` is a domain for every `k`-algebra `A` that is a domain: in the language of Weil and
Lang, `F` is a *regular* extension of `k`. Conversely, if `F ⊗[k] Ω` is a domain for one
algebraically closed field `Ω` over `k` (or if `F ⊗[k] K` is a domain for every field
extension `K / k`), then `F / k` is geometrically reduced and `k` is integrally closed in `F`.
Over a perfect base field `k`, geometric reducedness is automatic, so regularity reduces to
`IsIntegrallyClosedIn k F`.

Both hypotheses are needed in general. Over `k = ℝ`, the field `ℂ(x)` has the separating
element `x`, but `ℂ(x) ⊗[ℝ] ℂ` is not a domain since the constants `ℂ` are not exact. Over
an imperfect field, exact constants alone do not suffice: for `k = 𝔽_p(a, b)` and
`F = k(x, y)` with `y ^ p = a + b x ^ p`, the element `y - a ^ (1/p) - b ^ (1/p) x` of
`F ⊗[k] k(a ^ (1/p), b ^ (1/p))` is nilpotent and nonzero. Over every field, exact constants
do give a domain after a separable algebraic extension of the constants
(`TauCeti.isDomain_tensorProduct_of_isIntegrallyClosedIn`), and a domain after extension to an
algebraic closure forces exact constants
(`TauCeti.algebraicClosure_eq_bot_of_isDomain_tensorProduct`).

Regularity is stable under base change to the fraction field `Q` of `F ⊗[k] K` for any field
extension `K / k`: writing `(F ⊗[k] K) ⊗[K] A ≃ F ⊗[k] A` and localizing the first factor
shows that `Q ⊗[K] A` is a domain for every domain `K`-algebra `A`. In particular, `Q` is
regular over `K` and the enlarged constant field `K` is integrally closed in `Q`.
Symmetrically, when `K / k` is regular and `F / k` is arbitrary, `Q` is regular over `F` and
`F` is integrally closed in `Q`; this applies without extra hypotheses whenever `k` is
algebraically closed.

## Main results

* `TauCeti.isReduced_tensorProduct_of_separating`,
  `TauCeti.isReduced_tensorProduct_of_algebraicIndependent`: a separating element or separating
  algebraically independent family makes `F ⊗[k] A` reduced for every reduced `k`-algebra `A`.
* `TauCeti.isGeometricallyReduced_iff_exists_isTranscendenceBasis_and_isSeparable`: a finitely
  generated field extension is geometrically reduced iff it admits a finite separating
  transcendence basis.
* `TauCeti.isDomain_tensorProduct_of_isGeometricallyReduced`: if `F` is geometrically reduced
  with exact constants, then `F ⊗[k] A` is a domain for every `k`-algebra `A` that is a domain.
* `TauCeti.isDomain_tensorProduct_iff_isGeometricallyReduced_and_isIntegrallyClosedIn`,
  `TauCeti.forall_isDomain_tensorProduct_field_iff`: the regular-field equivalences over an
  algebraically closed test field and across all field extensions, together with perfect-base
  specializations.
* `TauCeti.isDomain_tensorProduct_right_of_isFractionRing_tensorProduct`,
  `TauCeti.isIntegrallyClosedIn_right_of_isFractionRing_tensorProduct`: if `F / k` is regular,
  any fraction field `Q` of `F ⊗[k] K` is regular over `K` and has exact constants `K`.
* `TauCeti.isDomain_tensorProduct_left_of_isFractionRing_tensorProduct`,
  `TauCeti.isIntegrallyClosedIn_left_of_isFractionRing_tensorProduct`: if `K / k` is regular
  and `F / k` is arbitrary, any fraction field `Q` of `F ⊗[k] K` is regular over `F` and `F` is
  relatively algebraically closed in `Q` (in particular whenever `k` is algebraically closed).

## References

* S. Lang, *Introduction to Algebraic Geometry*, Interscience, 1958, Chapter III, Section 1.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.6.
* [The Stacks project, Tag 037R](https://stacks.math.columbia.edu/tag/037R)
-/

public section

open scoped TensorProduct IntermediateField

namespace TauCeti

section Separating

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

/-- If `x : ι → F` is algebraically independent over `k` and `F` is separable algebraic over
`k(x)`, then `F ⊗[k] A` is reduced for every reduced `k`-algebra `A`. -/
theorem isReduced_tensorProduct_of_algebraicIndependent {ι : Type*} {x : ι → F}
    (hx : AlgebraicIndependent k x)
    [Algebra.IsSeparable (IntermediateField.adjoin k (Set.range x)) F]
    (A : Type*) [CommRing A] [IsReduced A] [Algebra k A] :
    IsReduced (F ⊗[k] A) := by
  have : IsReduced (MvPolynomial ι k ⊗[k] A) :=
    let e := (Algebra.TensorProduct.comm k (MvPolynomial ι k) A).trans
      ((MvPolynomial.algebraTensorAlgEquiv k A).restrictScalars k)
    isReduced_of_injective e e.injective
  have : IsReduced (FractionRing (MvPolynomial ι k) ⊗[k] A) :=
    isReduced_tensorProduct_of_isLocalization (nonZeroDivisors (MvPolynomial ι k)) _ A
  let e := Algebra.TensorProduct.congr hx.aevalEquivField.symm (AlgEquiv.refl : A ≃ₐ[k] A)
  exact isReduced_tensorProduct_of_isReduced_of_isSeparable k
    (E := IntermediateField.adjoin k (Set.range x)) A (hE := isReduced_of_injective e e.injective)

/-- A field extension that is separable algebraic over a purely transcendental subextension is
geometrically reduced. -/
theorem isGeometricallyReduced_of_algebraicIndependent {ι : Type*} {x : ι → F}
    (hx : AlgebraicIndependent k x)
    [Algebra.IsSeparable (IntermediateField.adjoin k (Set.range x)) F] :
    Algebra.IsGeometricallyReduced k F := by
  rw [Algebra.isGeometricallyReduced_field_iff]
  have := isReduced_tensorProduct_of_algebraicIndependent hx (AlgebraicClosure k)
  exact isReduced_of_injective (Algebra.TensorProduct.comm k (AlgebraicClosure k) F)
    (Algebra.TensorProduct.comm k (AlgebraicClosure k) F).injective

/-- A finitely generated field extension is geometrically reduced if and only if it has a finite
separating transcendence basis. -/
theorem isGeometricallyReduced_iff_exists_isTranscendenceBasis_and_isSeparable
    [Algebra.EssFiniteType k F] :
    Algebra.IsGeometricallyReduced k F ↔
      ∃ s : Finset F, IsTranscendenceBasis k ((↑) : s → F) ∧
        Algebra.IsSeparable (IntermediateField.adjoin k (s : Set F)) F := by
  refine ⟨fun _ ↦
    exists_isTranscendenceBasis_and_isSeparable_of_isGeometricallyReduced k F, ?_⟩
  rintro ⟨s, hs, hsep⟩
  have hrange : Set.range ((↑) : s → F) = (s : Set F) := by simp
  rw [← hrange] at hsep
  exact isGeometricallyReduced_of_algebraicIndependent hs.1

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

/-- **Separably generated fields with exact constants are regular.** If `F` is separable
algebraic over `k(x)` for some `x ∈ F`, and `k` is algebraically closed in `F`, then `F ⊗[k] A`
is a domain for every `k`-algebra `A` that is a domain, in particular for every field extension
of `k`. When `x` is algebraic over `k`, so is `F`, hence `F = k` and the statement is
trivial. -/
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

/-- If `F` is separable algebraic over a purely transcendental subextension `k(x)` and `k` is
algebraically closed in `F`, then `F ⊗[k] A` is a domain for every domain `k`-algebra `A`. -/
theorem isDomain_tensorProduct_of_algebraicIndependent (hex : IsIntegrallyClosedIn k F)
    {ι : Type*} {x : ι → F} (hx : AlgebraicIndependent k x)
    [Algebra.IsSeparable (IntermediateField.adjoin k (Set.range x)) F]
    (A : Type*) [CommRing A] [IsDomain A] [Algebra k A] :
    IsDomain (F ⊗[k] A) := by
  have := isGeometricallyReduced_of_algebraicIndependent hx
  exact isDomain_tensorProduct_of_isGeometricallyReduced hex A

/-- If `F ⊗[k] Ω` is a domain for some algebraically closed field `Ω` over `k`, then `k` is
integrally closed in `F`. -/
theorem isIntegrallyClosedIn_of_isDomain_tensorProduct (Ω : Type*) [Field Ω] [Algebra k Ω]
    [IsAlgClosed Ω] [IsDomain (F ⊗[k] Ω)] : IsIntegrallyClosedIn k F := by
  rw [← IsIntegrallyClosedIn.integralClosure_eq_bot_iff F (algebraMap k F).injective,
    ← algebraicClosure_toSubalgebra, ← IntermediateField.bot_toSubalgebra,
    IntermediateField.toSubalgebra_inj]
  exact algebraicClosure_eq_bot_of_isDomain_tensorProduct Ω

/-- **Regular-field equivalence over an algebraically closed test field.** For any
algebraically closed field `Ω` over `k`, `F ⊗[k] Ω` is a domain if and only if `F / k` is
geometrically reduced and `k` is integrally closed in `F`. -/
theorem isDomain_tensorProduct_iff_isGeometricallyReduced_and_isIntegrallyClosedIn
    (Ω : Type*) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] :
    IsDomain (F ⊗[k] Ω) ↔ Algebra.IsGeometricallyReduced k F ∧ IsIntegrallyClosedIn k F := by
  refine ⟨fun _ ↦ ⟨?_, isIntegrallyClosedIn_of_isDomain_tensorProduct Ω⟩,
    fun ⟨_, hex⟩ ↦ isDomain_tensorProduct_of_isGeometricallyReduced hex Ω⟩
  have : IsReduced (Ω ⊗[k] F) :=
    isReduced_of_injective (Algebra.TensorProduct.comm k Ω F)
      (Algebra.TensorProduct.comm k Ω F).injective
  exact Algebra.IsGeometricallyReduced.of_isReduced_tensorProduct Ω

/-- For a finitely generated field extension `F / k` and an algebraically closed field `Ω` over
`k`, `F ⊗[k] Ω` is a domain if and only if `F / k` has a finite separating transcendence basis
and `k` is integrally closed in `F`. -/
theorem isDomain_tensorProduct_iff_exists_isTranscendenceBasis_and_isIntegrallyClosedIn
    [Algebra.EssFiniteType k F] (Ω : Type*) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] :
    IsDomain (F ⊗[k] Ω) ↔
      (∃ s : Finset F, IsTranscendenceBasis k ((↑) : s → F) ∧
        Algebra.IsSeparable (IntermediateField.adjoin k (s : Set F)) F) ∧
        IsIntegrallyClosedIn k F := by
  rw [isDomain_tensorProduct_iff_isGeometricallyReduced_and_isIntegrallyClosedIn Ω,
    isGeometricallyReduced_iff_exists_isTranscendenceBasis_and_isSeparable]

/-- Over a perfect base field `k`, `F ⊗[k] Ω` is a domain for an algebraically closed field `Ω`
over `k` if and only if `k` is integrally closed in `F`. -/
theorem isDomain_tensorProduct_iff_isIntegrallyClosedIn [PerfectField k]
    (Ω : Type*) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] :
    IsDomain (F ⊗[k] Ω) ↔ IsIntegrallyClosedIn k F := by
  rw [isDomain_tensorProduct_iff_isGeometricallyReduced_and_isIntegrallyClosedIn Ω]
  exact and_iff_right inferInstance

end Separating

section UniversalRegular

universe u v

/-- **Regular-field equivalence across all field extensions.** A field extension `F / k` stays a
domain after tensoring with every field extension `K / k` if and only if `F / k` is
geometrically reduced and `k` is integrally closed in `F`. -/
theorem forall_isDomain_tensorProduct_field_iff {k : Type u} {F : Type v}
    [Field k] [Field F] [Algebra k F] :
    (∀ (K : Type u) [Field K] [Algebra k K], IsDomain (F ⊗[k] K)) ↔
      Algebra.IsGeometricallyReduced k F ∧ IsIntegrallyClosedIn k F := by
  rw [← isDomain_tensorProduct_iff_isGeometricallyReduced_and_isIntegrallyClosedIn
    (AlgebraicClosure k)]
  exact ⟨fun h ↦ h (AlgebraicClosure k), fun h K _ _ ↦ by
    rw [isDomain_tensorProduct_iff_isGeometricallyReduced_and_isIntegrallyClosedIn] at h
    have := h.1
    exact isDomain_tensorProduct_of_isGeometricallyReduced h.2 K⟩

/-- Over a perfect base field `k`, `F ⊗[k] K` is a domain for every field extension `K / k` if
and only if `k` is integrally closed in `F`. -/
theorem forall_isDomain_tensorProduct_field_iff_isIntegrallyClosedIn {k : Type u} {F : Type v}
    [Field k] [PerfectField k] [Field F] [Algebra k F] :
    (∀ (K : Type u) [Field K] [Algebra k K], IsDomain (F ⊗[k] K)) ↔
      IsIntegrallyClosedIn k F := by
  rw [forall_isDomain_tensorProduct_field_iff]
  exact and_iff_right inferInstance

end UniversalRegular

section BaseChangeLeft

section Regular

variable {k F K Q : Type*} [Field k] [Field F] [Field K] [Field Q]
  [Algebra k F] [Algebra k K] [Algebra (F ⊗[k] K) Q] [Algebra F Q]
  [IsScalarTower F (F ⊗[k] K) Q] [IsFractionRing (F ⊗[k] K) Q]

/-- **Base change of a regular extension along the left factor.** If `K / k` is regular and
`F / k` is any field extension, then any fraction field `Q` of `F ⊗[k] K` is regular over `F`:
`Q ⊗[F] A` is a domain for every domain `F`-algebra `A`. -/
theorem isDomain_tensorProduct_left_of_isFractionRing_tensorProduct
    (hex : IsIntegrallyClosedIn k K) [Algebra.IsGeometricallyReduced k K]
    (A : Type*) [CommRing A] [IsDomain A] [Algebra F A] :
    IsDomain (Q ⊗[F] A) := by
  let : Algebra k A := RingHom.toAlgebra ((algebraMap F A).comp (algebraMap k F))
  have : IsScalarTower k F A := .of_algebraMap_eq' rfl
  have : IsDomain (K ⊗[k] A) := isDomain_tensorProduct_of_isGeometricallyReduced hex A
  have : IsDomain (A ⊗[k] K) := (Algebra.TensorProduct.comm k A K).toMulEquiv.isDomain
  have : IsDomain (A ⊗[F] (F ⊗[k] K)) :=
    (Algebra.TensorProduct.cancelBaseChange k F F A K).toMulEquiv.isDomain
  have : IsDomain ((F ⊗[k] K) ⊗[F] A) :=
    (Algebra.TensorProduct.comm F (F ⊗[k] K) A).toMulEquiv.isDomain
  exact isDomain_tensorProduct_of_isLocalization (nonZeroDivisors (F ⊗[k] K)) le_rfl Q A

/-- If `K / k` is regular and `F / k` is any field extension, then any fraction field `Q` of
`F ⊗[k] K` is geometrically reduced over `F`. -/
theorem isGeometricallyReduced_left_of_isFractionRing_tensorProduct
    (hex : IsIntegrallyClosedIn k K) [Algebra.IsGeometricallyReduced k K] :
    Algebra.IsGeometricallyReduced F Q := by
  have h : IsDomain (Q ⊗[F] AlgebraicClosure F) :=
    isDomain_tensorProduct_left_of_isFractionRing_tensorProduct hex (AlgebraicClosure F)
  exact ((isDomain_tensorProduct_iff_isGeometricallyReduced_and_isIntegrallyClosedIn
    (AlgebraicClosure F)).mp h).1

/-- **Relative algebraic closure of `F` in `Frac(F ⊗[k] K)`.** If `K / k` is regular and `F / k`
is any field extension, then `F` is integrally closed in any fraction field `Q` of `F ⊗[k] K`. -/
theorem isIntegrallyClosedIn_left_of_isFractionRing_tensorProduct
    (hex : IsIntegrallyClosedIn k K) [Algebra.IsGeometricallyReduced k K] :
    IsIntegrallyClosedIn F Q := by
  have h : IsDomain (Q ⊗[F] AlgebraicClosure F) :=
    isDomain_tensorProduct_left_of_isFractionRing_tensorProduct hex (AlgebraicClosure F)
  exact ((isDomain_tensorProduct_iff_isGeometricallyReduced_and_isIntegrallyClosedIn
    (AlgebraicClosure F)).mp h).2

end Regular

variable {F Q : Type*} [Field F] [Field Q] [Algebra F Q]

/-- Over an algebraically closed field `k`, for any field extensions `F / k` and `K / k`, any
fraction field `Q` of `F ⊗[k] K` is geometrically reduced over `F`. -/
theorem isGeometricallyReduced_left_of_isFractionRing_tensorProduct_of_isAlgClosed
    (k K : Type*) [Field k] [IsAlgClosed k] [Field K] [Algebra k F] [Algebra k K]
    [Algebra (F ⊗[k] K) Q] [IsScalarTower F (F ⊗[k] K) Q] [IsFractionRing (F ⊗[k] K) Q] :
    Algebra.IsGeometricallyReduced F Q :=
  isGeometricallyReduced_left_of_isFractionRing_tensorProduct
    (isIntegrallyClosedIn_of_isAlgClosed (k := k) (A := K))

/-- Over an algebraically closed field `k`, for any field extensions `F / k` and `K / k`, `F` is
integrally closed in any fraction field `Q` of `F ⊗[k] K`. -/
theorem isIntegrallyClosedIn_left_of_isFractionRing_tensorProduct_of_isAlgClosed
    (k K : Type*) [Field k] [IsAlgClosed k] [Field K] [Algebra k F] [Algebra k K]
    [Algebra (F ⊗[k] K) Q] [IsScalarTower F (F ⊗[k] K) Q] [IsFractionRing (F ⊗[k] K) Q] :
    IsIntegrallyClosedIn F Q :=
  isIntegrallyClosedIn_left_of_isFractionRing_tensorProduct
    (isIntegrallyClosedIn_of_isAlgClosed (k := k) (A := K))

end BaseChangeLeft

section BaseChangeRight

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  Algebra.TensorProduct.right_isScalarTower

section Regular

variable {k F K Q : Type*} [Field k] [Field F] [Field K] [Field Q]
  [Algebra k F] [Algebra k K] [Algebra (F ⊗[k] K) Q] [Algebra K Q]
  [IsScalarTower K (F ⊗[k] K) Q] [IsFractionRing (F ⊗[k] K) Q]

/-- **Scalar stability of regular extensions.** If `F / k` is regular and `K / k` is any field
extension, then any fraction field `Q` of `F ⊗[k] K` is regular over `K`: `Q ⊗[K] A` is a
domain for every domain `K`-algebra `A`. -/
theorem isDomain_tensorProduct_right_of_isFractionRing_tensorProduct
    (hex : IsIntegrallyClosedIn k F) [Algebra.IsGeometricallyReduced k F]
    (A : Type*) [CommRing A] [IsDomain A] [Algebra K A] :
    IsDomain (Q ⊗[K] A) := by
  let : Algebra k A := RingHom.toAlgebra ((algebraMap K A).comp (algebraMap k K))
  have : IsScalarTower k K A := .of_algebraMap_eq' rfl
  have : IsDomain (F ⊗[k] A) := isDomain_tensorProduct_of_isGeometricallyReduced hex A
  have : IsDomain (A ⊗[k] F) := (Algebra.TensorProduct.comm k A F).toMulEquiv.isDomain
  have : IsDomain (A ⊗[K] (K ⊗[k] F)) :=
    (Algebra.TensorProduct.cancelBaseChange k K K A F).toMulEquiv.isDomain
  have : IsDomain ((F ⊗[k] K) ⊗[K] A) :=
    ((Algebra.TensorProduct.congr (Algebra.TensorProduct.commRight k K F).symm
      (AlgEquiv.refl : A ≃ₐ[K] A)).trans
      (Algebra.TensorProduct.comm K (K ⊗[k] F) A)).toMulEquiv.isDomain
  exact isDomain_tensorProduct_of_isLocalization (nonZeroDivisors (F ⊗[k] K)) le_rfl Q A

/-- If `F / k` is regular and `K / k` is any field extension, then any fraction field `Q` of
`F ⊗[k] K` is geometrically reduced over `K`. -/
theorem isGeometricallyReduced_right_of_isFractionRing_tensorProduct
    (hex : IsIntegrallyClosedIn k F) [Algebra.IsGeometricallyReduced k F] :
    Algebra.IsGeometricallyReduced K Q := by
  have h : IsDomain (Q ⊗[K] AlgebraicClosure K) :=
    isDomain_tensorProduct_right_of_isFractionRing_tensorProduct hex (AlgebraicClosure K)
  exact ((isDomain_tensorProduct_iff_isGeometricallyReduced_and_isIntegrallyClosedIn
    (AlgebraicClosure K)).mp h).1

/-- **Exactness of enlarged constants in `Frac(F ⊗[k] K)`.** If `F / k` is regular and `K / k` is
any field extension, then `K` is integrally closed in any fraction field `Q` of `F ⊗[k] K`. -/
theorem isIntegrallyClosedIn_right_of_isFractionRing_tensorProduct
    (hex : IsIntegrallyClosedIn k F) [Algebra.IsGeometricallyReduced k F] :
    IsIntegrallyClosedIn K Q := by
  have h : IsDomain (Q ⊗[K] AlgebraicClosure K) :=
    isDomain_tensorProduct_right_of_isFractionRing_tensorProduct hex (AlgebraicClosure K)
  exact ((isDomain_tensorProduct_iff_isGeometricallyReduced_and_isIntegrallyClosedIn
    (AlgebraicClosure K)).mp h).2

end Regular

variable {K Q : Type*} [Field K] [Field Q] [Algebra K Q]

/-- Over an algebraically closed field `k`, for any field extensions `F / k` and `K / k`, any
fraction field `Q` of `F ⊗[k] K` is geometrically reduced over `K`. -/
theorem isGeometricallyReduced_right_of_isFractionRing_tensorProduct_of_isAlgClosed
    (k F : Type*) [Field k] [IsAlgClosed k] [Field F] [Algebra k F] [Algebra k K]
    [Algebra (F ⊗[k] K) Q] [IsScalarTower K (F ⊗[k] K) Q] [IsFractionRing (F ⊗[k] K) Q] :
    Algebra.IsGeometricallyReduced K Q :=
  isGeometricallyReduced_right_of_isFractionRing_tensorProduct
    (isIntegrallyClosedIn_of_isAlgClosed (k := k) (A := F))

/-- Over an algebraically closed field `k`, for any field extensions `F / k` and `K / k`, `K` is
integrally closed in any fraction field `Q` of `F ⊗[k] K`. -/
theorem isIntegrallyClosedIn_right_of_isFractionRing_tensorProduct_of_isAlgClosed
    (k F : Type*) [Field k] [IsAlgClosed k] [Field F] [Algebra k F] [Algebra k K]
    [Algebra (F ⊗[k] K) Q] [IsScalarTower K (F ⊗[k] K) Q] [IsFractionRing (F ⊗[k] K) Q] :
    IsIntegrallyClosedIn K Q :=
  isIntegrallyClosedIn_right_of_isFractionRing_tensorProduct
    (isIntegrallyClosedIn_of_isAlgClosed (k := k) (A := F))

end BaseChangeRight

end TauCeti
