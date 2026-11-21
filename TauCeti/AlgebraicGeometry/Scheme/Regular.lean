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

* `TauCeti.AlgebraicGeometry.Scheme.exists_algebraMap_stalk_eq_of_ord_nonneg`: at a
  codimension-one point whose local ring is a discrete valuation ring, a rational function of
  nonnegative order lies in that local ring;
* `TauCeti.AlgebraicGeometry.Scheme.exists_algebraMap_stalk_eq_of_coheight_eq_zero`: at a point
  with no proper generization the local ring is already the whole function field;
* `TauCeti.AlgebraicGeometry.Scheme.exists_germToFunctionField_eq_of_ord_nonneg`: a rational
  function with nonnegative order at every codimension-one point of `U` is the germ at the generic
  point of a section of `𝒪_X` over `U`;
* `TauCeti.AlgebraicGeometry.Scheme.exists_unit_germToFunctionField_eq_of_ord_eq_zero`: a nonzero
  rational function with *zero* order at every codimension-one point of `U` is the germ of a unit
  of `Γ(X, U)`;
* `TauCeti.AlgebraicGeometry.Scheme.exists_algebraMap_stalk_eq_of_ord_nonneg_of_isNormalScheme`,
  `TauCeti.AlgebraicGeometry.Scheme.exists_germToFunctionField_eq_of_ord_nonneg_of_isNormalScheme`,
  and `Scheme.exists_unit_germToFunctionField_eq_of_ord_eq_zero_of_isNormalScheme`:
  algebraic Hartogs' principle on locally Noetherian normal integral schemes in arbitrary
  dimension, proved via Serre's condition `(S_2)`.

The third statement is the one-dimensional case of algebraic Hartogs' principle, and it is the
input that identifies the sheaf `𝒪_X(0)` of the zero divisor with the structure sheaf. The last
one applies it to a function and to its inverse; it is the local comparison used to glue the
local equations of a locally principal Weil divisor into a Cartier divisor.

The argument follows Hartshorne, *Algebraic Geometry*, II.6.3A and Proposition II.6.11, in the
dimension-one case where the intersection of the local rings can be taken over the points of `U`
themselves. The local step is Mathlib's `IsDiscreteValuationRing.exists_lift_of_le_one` together
with `Ring.ordFrac_eq_valuation_inv`, and the global step, that a rational function lying in every
local ring of `U` is regular on `U`, is
`TauCeti.AlgebraicGeometry.Scheme.exists_germToFunctionField_eq_of_forall_mem_range`.
-/

public section

open AlgebraicGeometry CategoryTheory IsLocalRing Opposite Order TopologicalSpace
open scoped WithZero

namespace TauCeti

namespace AlgebraicGeometry

universe u

/-- On a scheme of dimension at most one whose local rings are domains and whose codimension-one
local rings are discrete valuation rings, every local ring is a unique factorization domain: a
field in codimension zero and a discrete valuation ring in codimension one. -/
theorem uniqueFactorizationMonoid_stalk_of_forall_coheight_le_one {X : Scheme.{u}}
    [∀ x : X, IsDomain (X.presheaf.stalk x)]
    [hDVR : ∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))]
    (hX : ∀ x : X, coheight x ≤ 1) (x : X) :
    UniqueFactorizationMonoid (X.presheaf.stalk x) := by
  rcases eq_or_lt_of_le (hX x) with hx | hx
  · have := hDVR ⟨x, hx⟩
    infer_instance
  · have hdim : Ring.KrullDimLE 0 (X.presheaf.stalk x) :=
      krullDimLE_of_coheight_le (Order.lt_one_iff.mp hx).le
    let : Field (X.presheaf.stalk x) :=
      (Ring.isField_iff_maximal_bot.mpr
        (Ring.krullDimLE_zero_iff.mp hdim ⊥ Ideal.isPrime_bot)).toField
    infer_instance

/-- A scheme of dimension at most one whose local rings are domains and whose codimension-one local
rings are discrete valuation rings is normal. -/
theorem IsNormalScheme.of_forall_coheight_le_one {X : Scheme.{u}}
    [∀ x : X, IsDomain (X.presheaf.stalk x)]
    [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))]
    (hX : ∀ x : X, coheight x ≤ 1) :
    IsNormalScheme X := by
  have := uniqueFactorizationMonoid_stalk_of_forall_coheight_le_one hX
  exact IsNormalScheme.of_uniqueFactorizationMonoid_stalk

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

/-- If every rational function with nonnegative order at all codimension-one points of `U` lifts to
a regular section over `U`, then any rational unit with zero order on `U` lifts to a unit of
`Γ(X, U)`. -/
private theorem exists_unit_germToFunctionField_eq_of_forall_ord_nonneg
    {U : X.Opens} [Nonempty U]
    (hreg : ∀ g : X.functionField,
      (∀ y : CodimensionOnePoint X, (y : X) ∈ U → 0 ≤ X.ord g y) →
        ∃ a : Γ(X, U), X.germToFunctionField U a = g)
    {f : X.functionFieldˣ}
    (hf : ∀ y : CodimensionOnePoint X, (y : X) ∈ U → X.ord (f : X.functionField) y = 0) :
    ∃ a : Γ(X, U)ˣ, X.germToFunctionField U (a : Γ(X, U)) = (f : X.functionField) := by
  obtain ⟨a, ha⟩ := hreg (f : X.functionField) fun y hy ↦ (hf y hy).ge
  obtain ⟨b, hb⟩ := hreg ((f⁻¹ : X.functionFieldˣ) : X.functionField) fun y hy ↦ by
    rw [Units.val_inv_eq_inv_val, _root_.AlgebraicGeometry.Scheme.ord_inv, hf y hy, neg_zero]
  have hab : a * b = 1 := X.germToFunctionField_injective U <| by
    rw [map_mul, ha, hb, map_one, Units.mul_inv]
  exact ⟨⟨a, b, hab, (mul_comm b a).trans hab⟩, ha⟩

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
    ∃ a : Γ(X, U)ˣ, X.germToFunctionField U (a : Γ(X, U)) = (f : X.functionField) :=
  exists_unit_germToFunctionField_eq_of_forall_ord_nonneg
    (fun _ ↦ exists_germToFunctionField_eq_of_ord_nonneg hDVR hU) hf

section Normal

variable [IsNormalScheme X]

/-- **Local algebraic Hartogs' principle.** At a point `x` of a locally Noetherian normal integral
scheme, a rational function `f` with nonnegative order at every codimension-one generization of `x`
lies in `𝒪_{X,x}`. Stacks, Lemma 10.157.6 (031T); Hartshorne, Proposition II.6.3A. -/
@[stacks 031T]
theorem exists_algebraMap_stalk_eq_of_ord_nonneg_of_isNormalScheme {x : X} {f : X.functionField}
    (hf : ∀ η : CodimensionOnePoint X, (η : X) ⤳ x → 0 ≤ X.ord f η) :
    ∃ g : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField g = f := by
  set A := X.presheaf.stalk x
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) f
  have hb0 : algebraMap A X.functionField b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  by_cases hab : a ∈ Ideal.span {b}
  · obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hab
    exact ⟨g, by rw [map_mul, mul_div_cancel_right₀ _ hb0]⟩
  exfalso
  have hS : Module.SatisfiesSerreS 2 A A :=
    TauCeti.satisfiesSerreS_two_of_forall_isIntegrallyClosed fun p _ ↦
      ⟨inferInstance, isIntegrallyClosed_of_isLocalization _ p.primeCompl
        p.primeCompl_le_nonZeroDivisors⟩
  obtain ⟨P, hPass, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing A
    (Ideal.Quotient.mk (Ideal.span {b}) a) (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  have := hPass.isPrime
  obtain ⟨η, hηcoh, hηx, hcomap⟩ := exists_specializes_and_comap_stalkSpecializes_maximalIdeal_eq P
  rw [hS.height_eq_one_of_isAssociatedPrime_quotient_span_singleton hb hPass] at hηcoh
  have : IsDiscreteValuationRing (X.presheaf.stalk η) :=
    IsNormalScheme.isDiscreteValuationRing_stalk η hηcoh
  obtain ⟨c, hc⟩ := exists_algebraMap_stalk_eq_of_ord_nonneg (hf ⟨η, hηcoh⟩ hηx)
  let := (X.presheaf.stalkSpecializes hηx).hom.toAlgebra
  set Q := (maximalIdeal (X.presheaf.stalk η)).comap (X.presheaf.stalkSpecializes hηx).hom
  have := isLocalization_stalkSpecializes hηx
  obtain ⟨⟨d, s⟩, hds⟩ := IsLocalization.surj Q.primeCompl c
  have hba : algebraMap A X.functionField (s * a) = algebraMap A X.functionField (b * d) := by
    have hcd := congrArg (algebraMap (X.presheaf.stalk η) X.functionField) hds
    rw [map_mul, RingHom.algebraMap_toAlgebra (X.presheaf.stalkSpecializes hηx).hom,
      algebraMap_stalkSpecializes, algebraMap_stalkSpecializes, hc,
      mul_comm _ (algebraMap A _ (s : A))] at hcd
    have hcd' := congrArg (· * algebraMap A X.functionField b) hcd
    rw [mul_div_assoc', div_mul_cancel₀ _ hb0, mul_comm _ (algebraMap A X.functionField b)] at hcd'
    rwa [map_mul, map_mul]
  have hsa : (s : A) * a ∈ Ideal.span {b} := Ideal.mem_span_singleton'.mpr
    ⟨d, mul_comm d b ▸ IsFractionRing.injective A X.functionField hba.symm⟩
  exact (hcomap ▸ s.property : (s : A) ∉ P) (hle (TauCeti.Ideal.Quotient.mem_colon_singleton_mk.mpr
      hsa))

/-- **Algebraic Hartogs' principle on normal Noetherian schemes.** A rational function with
nonnegative order at every codimension-one point of a nonempty open `U` is regular on `U`. -/
theorem exists_germToFunctionField_eq_of_ord_nonneg_of_isNormalScheme {U : X.Opens} [Nonempty U]
    {f : X.functionField} (hf : ∀ y : CodimensionOnePoint X, (y : X) ∈ U → 0 ≤ X.ord f y) :
    ∃ a : Γ(X, U), X.germToFunctionField U a = f :=
  exists_germToFunctionField_eq_of_forall_mem_range fun _ hx ↦
    exists_algebraMap_stalk_eq_of_ord_nonneg_of_isNormalScheme fun y hyx ↦
      hf y (hyx.mem_open U.isOpen hx)

/-- **A rational function without zeros or poles on a normal scheme is a regular unit.** A nonzero
rational function with zero order at every codimension-one point of `U` comes from `Γ(X, U)ˣ`. -/
theorem exists_unit_germToFunctionField_eq_of_ord_eq_zero_of_isNormalScheme {U : X.Opens}
    [Nonempty U] {f : X.functionFieldˣ}
    (hf : ∀ y : CodimensionOnePoint X, (y : X) ∈ U → X.ord (f : X.functionField) y = 0) :
    ∃ u : Γ(X, U)ˣ, X.germToFunctionField U (u : Γ(X, U)) = (f : X.functionField) := by
  obtain ⟨a, ha⟩ := exists_germToFunctionField_eq_of_ord_nonneg_of_isNormalScheme (U := U)
    (f := (f : X.functionField)) fun y hy ↦ (hf y hy).ge
  obtain ⟨b, hb⟩ := exists_germToFunctionField_eq_of_ord_nonneg_of_isNormalScheme (U := U)
    (f := ((f⁻¹ : X.functionFieldˣ) : X.functionField)) fun y hy ↦ by
      rw [Units.val_inv_eq_inv_val, AlgebraicGeometry.Scheme.ord_inv, hf y hy, neg_zero]
  have hab : a * b = 1 := X.germToFunctionField_injective U <| by
    rw [map_mul, ha, hb, map_one, Units.mul_inv]
  exact ⟨⟨a, b, hab, (mul_comm b a).trans hab⟩, ha⟩

end Normal

end Scheme

end

end AlgebraicGeometry

end TauCeti
