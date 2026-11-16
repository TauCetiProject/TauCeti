/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.RationalFunctions
public import TauCeti.AlgebraicGeometry.Scheme.Normal
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Order
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import TauCeti.AlgebraicGeometry.Scheme.StalkSpecializes
import TauCeti.RingTheory.Ideal.Quotient.Colon
import TauCeti.RingTheory.SerreCondition.Normal

/-!
# Rational functions without poles are regular

On a locally Noetherian integral scheme a regular function has nonnegative order at every point
where it is defined (`TauCeti.AlgebraicGeometry.Scheme.ord_germToFunctionField_nonneg`). This file
proves the converse (*algebraic Hartogs' principle*) in two settings:

1. On a nonempty open subset `U` of dimension at most one whose codimension-one local rings are
   discrete valuation rings, a rational function with no poles on `U` is the germ of a regular
   function on `U`.
2. On any locally Noetherian normal integral scheme `X`, each local ring `𝒪_{X,x}` satisfies
   Serre's condition `(S_2)` (`TauCeti.satisfiesSerreS_two_of_forall_isIntegrallyClosed`): for any
   nonzerodivisor `b ∈ 𝒪_{X,x}`, every associated prime of `𝒪_{X,x} ⧸ (b)` has height one and
   comes from a codimension-one generization `η ⤳ x` whose local ring `𝒪_{X,η}` is a discrete
   valuation ring (`IsNormalScheme.isDiscreteValuationRing_stalk`). Consequently, a rational
   function with nonnegative order at every codimension-one point of `U` is regular on `U`.

## Main declarations

In the namespace `TauCeti.AlgebraicGeometry.Scheme`:

* `exists_algebraMap_stalk_eq_of_ord_nonneg`: at a codimension-one point whose local ring is a
  discrete valuation ring, a rational function of nonnegative order lies in that local ring;
* `exists_algebraMap_stalk_eq_of_coheight_eq_zero`: at a point with no proper generization the
  local ring is already the whole function field;
* `exists_germToFunctionField_eq_of_ord_nonneg`: a rational function with nonnegative order at
  every codimension-one point of a one-dimensional open `U` is the germ at the generic point of a
  section of `𝒪_X` over `U`;
* `exists_unit_germToFunctionField_eq_of_ord_eq_zero`: a nonzero rational function with *zero*
  order at every codimension-one point of `U` is the germ of a unit of `Γ(X, U)`;
* `exists_algebraMap_stalk_eq_of_forall_specializes_ord_nonneg`,
  `exists_germToFunctionField_eq_of_ord_nonneg_of_isNormalScheme`, and
  `exists_unit_germToFunctionField_eq_of_ord_eq_zero_of_isNormalScheme`: algebraic Hartogs'
  principle on locally Noetherian normal integral schemes of arbitrary dimension.

The dimension-one case identifies the sheaf `𝒪_X(0)` of the zero divisor with the structure sheaf
and glues the local equations of a locally principal Weil divisor into a Cartier divisor; the
normal case proves injectivity of the Cartier-to-Weil homomorphism in arbitrary dimension.

## References

* [Stacks Project, Lemma 10.157.6 (031T)](https://stacks.math.columbia.edu/tag/031T) (algebraic
  Hartogs' principle on normal Noetherian domains).
* R. Hartshorne, *Algebraic Geometry*, Chapter II, Proposition 6.3A and Proposition 6.11.
* The associated-prime localization step in
  `TauCeti.AlgebraicGeometry.Scheme.exists_algebraMap_stalk_eq_of_forall_specializes_ord_nonneg`
  adapts `TauCeti.isIntegrallyClosed_of_satisfiesSerreR_one_of_satisfiesSerreS_two`, which itself
  adapts `Pcf.Stacks.isIntegrallyClosed_of_isRegularRing` from T. Dupuy, T. Tucker, and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `a39c3781b9850b9f3d5cbc9920322a3b8e365ef2` (Apache-2.0),
  `lean/Pcf/Stacks/Common/RegularNormal.lean`.
-/

public section

open AlgebraicGeometry CategoryTheory Opposite Order TopologicalSpace
open scoped WithZero nonZeroDivisors

namespace TauCeti

namespace AlgebraicGeometry

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

noncomputable section

namespace Scheme

/-- At a codimension-one point whose local ring is a discrete valuation ring, a rational function
of nonnegative order is a section of that local ring. This is the local half of the statement that
a rational function without poles is regular. -/
theorem exists_algebraMap_stalk_eq_of_ord_nonneg {x : X}
    [IsDiscreteValuationRing (X.presheaf.stalk x)]
    {f : X.functionField} (hf : 0 ≤ X.ord f x) :
    ∃ g : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField g = f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact ⟨0, map_zero _⟩
  have hx : coheight x = 1 := by
    have := ringKrullDim_stalk_eq_coheight x
    rw [IsDiscreteValuationRing.ringKrullDim_eq_one] at this
    exact_mod_cast this.symm
  refine IsDiscreteValuationRing.exists_lift_of_le_one ?_
  have h1 : (1 : ℤᵐ⁰) ≤ X.ordHom x hx f := by
    simpa using (X.le_ord_iff hx hf0 (n := 0)).mp (by simpa using hf)
  simp only [_root_.AlgebraicGeometry.Scheme.ordHom, Ring.ordFrac_eq_valuation_inv] at h1
  exact (one_le_inv_iff₀.mp h1).2

omit [IsLocallyNoetherian X] in
/-- At a point with no proper generization the local ring is the whole function field: it is a
zero-dimensional local domain, hence a field, and it has the function field as its field of
fractions. -/
theorem exists_algebraMap_stalk_eq_of_coheight_eq_zero {x : X} (hx : coheight x = 0)
    (f : X.functionField) :
    ∃ g : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField g = f := by
  have hdim : Ring.KrullDimLE 0 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have hfield : IsField (X.presheaf.stalk x) :=
    Ring.isField_iff_maximal_bot.mpr (Ring.krullDimLE_zero_iff.mp hdim ⊥ Ideal.isPrime_bot)
  exact IsFractionRing.surjective_iff_isField.mpr hfield f

/-- **A rational function without poles is regular.** On a locally Noetherian integral scheme, let
`U` be a nonempty open subset of dimension at most one whose codimension-one local rings are
discrete valuation rings. A rational function whose order is nonnegative at every codimension-one
point of `U` is the image of a section of `𝒪_X` over `U`.

This is the one-dimensional case of algebraic Hartogs' principle. The hypothesis on the dimension
enters only through the points of `U`: at a codimension-one point the discrete valuation gives the
bound, and at a point with no proper generization the local ring is already the function field. -/
theorem exists_germToFunctionField_eq_of_ord_nonneg
    {U : X.Opens} [Nonempty U]
    (hDVR : ∀ y : CodimensionOnePoint X, (y : X) ∈ U →
      IsDiscreteValuationRing (X.presheaf.stalk (y : X)))
    (hU : ∀ y ∈ U, coheight y ≤ 1) {f : X.functionField}
    (hf : ∀ (y : CodimensionOnePoint X), (y : X) ∈ U → 0 ≤ X.ord f y) :
    ∃ a : Γ(X, U), X.germToFunctionField U a = f := by
  refine exists_germToFunctionField_eq_of_forall_mem_range fun y hy ↦ ?_
  rcases eq_or_lt_of_le (hU y hy) with hy' | hy'
  · have : IsDiscreteValuationRing (X.presheaf.stalk y) := hDVR ⟨y, hy'⟩ hy
    exact exists_algebraMap_stalk_eq_of_ord_nonneg (hf ⟨y, hy'⟩ hy)
  · exact exists_algebraMap_stalk_eq_of_coheight_eq_zero (Order.lt_one_iff.mp hy') f

/-- **A rational function without zeros or poles is a regular unit.** On a locally Noetherian
integral scheme, let `U` be a nonempty open subset of dimension at most one whose codimension-one
local rings are discrete valuation rings. A nonzero rational function whose order vanishes at
every codimension-one point of `U` is the germ of a unit of `Γ(X, U)`.

Simultaneous regularity of the function and its inverse makes the resulting section a unit. -/
theorem exists_unit_germToFunctionField_eq_of_ord_eq_zero
    {U : X.Opens} [Nonempty U]
    (hDVR : ∀ y : CodimensionOnePoint X, (y : X) ∈ U →
      IsDiscreteValuationRing (X.presheaf.stalk (y : X)))
    (hU : ∀ y ∈ U, coheight y ≤ 1) {f : X.functionFieldˣ}
    (hf : ∀ (y : CodimensionOnePoint X), (y : X) ∈ U → X.ord (f : X.functionField) y = 0) :
    ∃ a : Γ(X, U)ˣ, X.germToFunctionField U (a : Γ(X, U)) = (f : X.functionField) := by
  obtain ⟨a, ha⟩ := exists_germToFunctionField_eq_of_ord_nonneg hDVR hU
    (f := (f : X.functionField)) fun y hy ↦ (hf y hy).ge
  obtain ⟨b, hb⟩ := exists_germToFunctionField_eq_of_ord_nonneg hDVR hU
    (f := ((f⁻¹ : X.functionFieldˣ) : X.functionField)) fun y hy ↦ by
      rw [Units.val_inv_eq_inv_val, AlgebraicGeometry.Scheme.ord_inv, hf y hy, neg_zero]
  have hab : a * b = 1 := by
    refine X.germToFunctionField_injective U ?_
    rw [map_mul, ha, hb, map_one, Units.mul_inv]
  exact ⟨⟨a, b, hab, (mul_comm b a).trans hab⟩, ha⟩

section Hartogs

variable [IsNormalScheme X]

/-- **Local algebraic Hartogs' principle.** On a locally Noetherian normal integral scheme, a
rational function whose order is nonnegative at every codimension-one generization of `x` belongs
to the local ring `𝒪_{X,x}`. Stacks, Lemma 10.157.6 (031T); Hartshorne, Proposition II.6.3A. -/
@[stacks 031T]
theorem exists_algebraMap_stalk_eq_of_forall_specializes_ord_nonneg {x : X} {f : X.functionField}
    (hf : ∀ η : CodimensionOnePoint X, (η : X) ⤳ x → 0 ≤ X.ord f η) :
    ∃ g : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField g = f := by
  set R := X.presheaf.stalk x
  have hS : Module.SatisfiesSerreS 2 R R :=
    TauCeti.satisfiesSerreS_two_of_forall_isIntegrallyClosed fun p _ ↦
      ⟨IsLocalization.isDomain_localization p.primeCompl_le_nonZeroDivisors,
        isIntegrallyClosed_of_isLocalization _ p.primeCompl p.primeCompl_le_nonZeroDivisors⟩
  obtain ⟨⟨a, ⟨b, hb⟩⟩, hf'⟩ := IsLocalization.mk'_surjective R⁰ f
  dsimp only at hf'
  subst hf'
  by_cases hab : a ∈ Ideal.span {b}
  · obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hab
    exact ⟨g, IsLocalization.eq_mk'_iff_mul_eq.mpr (by rw [← map_mul, mul_comm])⟩
  exfalso
  -- An associated prime `P` of `R ⧸ (b)` containing `((b) : a)` has height one by `(S_2)`.
  obtain ⟨P, hPass, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R
    (Ideal.Quotient.mk (Ideal.span {b}) a) (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  have := hPass.isPrime
  have hP1 := hS.height_eq_one_of_isAssociatedPrime_quotient_span_singleton hb hPass
  obtain ⟨η, hη, hηx, hcomap⟩ := exists_comap_stalkSpecializes_maximalIdeal_eq P
  rw [hP1] at hη
  have : IsDiscreteValuationRing (X.presheaf.stalk η) :=
    IsNormalScheme.isDiscreteValuationRing_stalk η hη
  obtain ⟨y, hy⟩ := exists_algebraMap_stalk_eq_of_ord_nonneg (hf ⟨η, hη⟩ hηx)
  -- Then `a ∈ (b) 𝒪_{X,η}` inside the localization `𝒪_{X,η} = R_P`, contradicting `s ∉ P`.
  let := (X.presheaf.stalkSpecializes hηx).hom.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk η) P :=
    hcomap ▸ isLocalization_stalkSpecializes hηx
  have hmul : y * (X.presheaf.stalkSpecializes hηx).hom b =
      (X.presheaf.stalkSpecializes hηx).hom a :=
    IsFractionRing.injective (X.presheaf.stalk η) X.functionField <| by
      rw [map_mul, hy, algebraMap_stalkSpecializes hηx, algebraMap_stalkSpecializes hηx,
        IsLocalization.mk'_spec]
  have hmem : algebraMap R (X.presheaf.stalk η) a ∈
      (Ideal.span {b}).map (algebraMap R (X.presheaf.stalk η)) := by
    rw [Ideal.map_span, Set.image_singleton]
    exact Ideal.mem_span_singleton'.mpr ⟨y, hmul⟩
  obtain ⟨s, hs, hsa⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff P.primeCompl (X.presheaf.stalk η) _ _).mp hmem
  exact hs (hle (TauCeti.Ideal.Quotient.mem_colon_singleton_mk.mpr hsa))

/-- **Algebraic Hartogs' principle.** On a locally Noetherian normal integral scheme, a rational
function whose order of vanishing is nonnegative at every codimension-one point of a nonempty open
subset `U` is regular on `U`. -/
theorem exists_germToFunctionField_eq_of_ord_nonneg_of_isNormalScheme {U : X.Opens} [Nonempty U]
    {f : X.functionField} (hf : ∀ y : CodimensionOnePoint X, (y : X) ∈ U → 0 ≤ X.ord f y) :
    ∃ a : Γ(X, U), X.germToFunctionField U a = f :=
  exists_germToFunctionField_eq_of_forall_mem_range fun _ hx ↦
    exists_algebraMap_stalk_eq_of_forall_specializes_ord_nonneg fun η hηx ↦
      hf η (hηx.mem_open U.isOpen hx)

/-- On a locally Noetherian normal integral scheme, a nonzero rational function whose order of
vanishing is zero at every codimension-one point of a nonempty open subset `U` is a regular unit
on `U`. -/
theorem exists_unit_germToFunctionField_eq_of_ord_eq_zero_of_isNormalScheme {U : X.Opens}
    [Nonempty U] {f : X.functionFieldˣ}
    (hf : ∀ y : CodimensionOnePoint X, (y : X) ∈ U → X.ord (f : X.functionField) y = 0) :
    ∃ a : Γ(X, U)ˣ, X.germToFunctionField U (a : Γ(X, U)) = (f : X.functionField) := by
  obtain ⟨a, ha⟩ := exists_germToFunctionField_eq_of_ord_nonneg_of_isNormalScheme
    (f := (f : X.functionField)) fun y hy ↦ (hf y hy).ge
  obtain ⟨b, hb⟩ := exists_germToFunctionField_eq_of_ord_nonneg_of_isNormalScheme
    (f := ((f⁻¹ : X.functionFieldˣ) : X.functionField)) fun y hy ↦ by
      rw [Units.val_inv_eq_inv_val, _root_.AlgebraicGeometry.Scheme.ord_inv, hf y hy, neg_zero]
  have hab : a * b = 1 := X.germToFunctionField_injective U <| by
    rw [map_mul, ha, hb, map_one, Units.mul_inv]
  exact ⟨⟨a, b, hab, (mul_comm b a).trans hab⟩, ha⟩

end Hartogs

end Scheme

end

end AlgebraicGeometry

end TauCeti
