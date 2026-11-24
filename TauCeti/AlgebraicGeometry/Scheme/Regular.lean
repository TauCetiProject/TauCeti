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
import TauCeti.RingTheory.DiscreteValuationRing.IntegrallyClosed
import TauCeti.RingTheory.SerreCondition.Normal

/-!
# Rational functions without poles are regular

On a locally Noetherian integral scheme a regular function has nonnegative order at every point
where it is defined (`TauCeti.AlgebraicGeometry.Scheme.ord_germToFunctionField_nonneg`). This file
proves the converse, algebraic Hartogs' principle, on an open subset `U` at whose points the local
rings are integrally closed, for instance an open subset of a normal scheme: a rational function
with no poles at the codimension-one points of `U` is the germ of a regular function on `U`.

The local step is that a Noetherian integrally closed domain is the intersection of its
localizations at the primes of height one (`TauCeti.mem_range_algebraMap_of_forall_height_eq_one`),
and the localizations of `𝒪_{X,x}` at its primes of height one are the local rings at the
codimension-one generizations of `x`
(`TauCeti.AlgebraicGeometry.Scheme.exists_specializes_and_comap_stalkSpecializes_maximalIdeal_eq`).
In dimension at most one with discrete valuation rings in codimension one, every local ring is a
discrete valuation ring or the function field, so the principle applies there with no normality
hypothesis to check.

## Main declarations

* `TauCeti.AlgebraicGeometry.Scheme.exists_algebraMap_stalk_eq_of_ord_nonneg`: at a
  codimension-one point whose local ring is a discrete valuation ring, a rational function of
  nonnegative order lies in that local ring;
* `TauCeti.AlgebraicGeometry.Scheme.exists_algebraMap_stalk_eq_of_coheight_eq_zero`: at a point
  with no proper generization the local ring is already the whole function field;
* `TauCeti.AlgebraicGeometry.Scheme.exists_algebraMap_stalk_eq_of_forall_ord_nonneg`: at a point
  with integrally closed local ring, a rational function of nonnegative order at every
  codimension-one generization lies in that local ring;
* `Scheme.exists_germToFunctionField_eq_of_ord_nonneg_of_isIntegrallyClosed` and
  `Scheme.exists_germToFunctionField_eq_of_ord_nonneg`: a rational
  function with nonnegative order at every codimension-one point of `U` is the germ at the generic
  point of a section of `𝒪_X` over `U`, when the local rings of `U` are integrally closed, and when
  `U` has dimension at most one with discrete valuation rings in codimension one;
* `Scheme.isIntegrallyClosed_stalk_of_coheight_le_one`: on an open subset of dimension at most
  one whose codimension-one local rings are discrete valuation rings, every local ring is
  integrally closed;
* `Scheme.exists_unit_germToFunctionField_eq_of_ord_eq_zero_of_isIntegrallyClosed`: when the
  local rings of `U` are integrally closed, a nonzero rational function with *zero* order at every
  codimension-one point of `U` is the germ of a unit of `Γ(X, U)`.

The regularity statements identify the sheaf `𝒪_X(0)` of the zero divisor with the structure
sheaf. The unit statement applies them to a function and to its inverse; it is the local
comparison used to glue the local equations of a locally principal Weil divisor into a Cartier
divisor, and to show that a Cartier divisor on a normal scheme is determined by its Weil divisor.

The argument follows Hartshorne, *Algebraic Geometry*, II.6.3A and Proposition II.6.11, and the
Stacks Project, Lemma 10.157.6 (031T). The global step, that a rational function lying in every
local ring of `U` is regular on `U`, is
`TauCeti.AlgebraicGeometry.Scheme.exists_germToFunctionField_eq_of_forall_mem_range`.
-/

public section

open AlgebraicGeometry CategoryTheory Opposite Order TopologicalSpace
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

/-- **Algebraic Hartogs' principle at a point.** On a locally Noetherian integral scheme, let `x`
be a point whose local ring `𝒪_{X,x}` is integrally closed. A rational function whose order is
nonnegative at every codimension-one generization of `x` lies in `𝒪_{X,x}`. The local rings at
these generizations are the localizations of `𝒪_{X,x}` at its primes of height one, so this is
`𝒪_{X,x} = ⋂_{ht P = 1} (𝒪_{X,x})_P`, Stacks, Lemma 10.157.6 (031T). -/
theorem exists_algebraMap_stalk_eq_of_forall_ord_nonneg {x : X}
    [IsIntegrallyClosed (X.presheaf.stalk x)] {f : X.functionField}
    (hf : ∀ y : CodimensionOnePoint X, (y : X) ⤳ x → 0 ≤ X.ord f y) :
    ∃ g : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField g = f := by
  refine TauCeti.mem_range_algebraMap_of_forall_height_eq_one fun Q _ hQ ↦ ?_
  -- `Q` is the prime of a generization `y` of `x`, of codimension one
  obtain ⟨y, hcoh, h, rfl⟩ := exists_specializes_and_comap_stalkSpecializes_maximalIdeal_eq Q
  rw [hQ] at hcoh
  let := (X.presheaf.stalkSpecializes h).hom.toAlgebra
  have := isLocalization_stalkSpecializes h
  -- `𝒪_{X,y}` is the localization of `𝒪_{X,x}` at `Q`, an integrally closed local domain of
  -- dimension one, hence a discrete valuation ring
  have : IsIntegrallyClosed (X.presheaf.stalk y) :=
    isIntegrallyClosed_of_isLocalization _ _ (Ideal.primeCompl_le_nonZeroDivisors
      ((IsLocalRing.maximalIdeal _).comap (X.presheaf.stalkSpecializes h).hom))
  have : IsDiscreteValuationRing (X.presheaf.stalk y) :=
    IsDiscreteValuationRing.of_ringKrullDim_eq_one <| by
      rw [ringKrullDim_stalk_eq_coheight, hcoh, WithBot.coe_one]
  -- so `f = c` for some `c ∈ 𝒪_{X,y}`, and `c = r / s` with `s ∉ Q`
  obtain ⟨c, hc⟩ := exists_algebraMap_stalk_eq_of_ord_nonneg (hf ⟨y, hcoh⟩ h)
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj
    ((IsLocalRing.maximalIdeal _).comap (X.presheaf.stalkSpecializes h).hom).primeCompl c
  refine ⟨s, s.property, r, ?_⟩
  have := congrArg (algebraMap (X.presheaf.stalk y) X.functionField) hrs
  rw [map_mul, hc] at this
  rw [← algebraMap_stalkSpecializes h, ← algebraMap_stalkSpecializes h, mul_comm]
  -- the algebra structure on `𝒪_{X,y}` is the specialization map, so `this` is the goal
  exact this.symm

/-- **Algebraic Hartogs' principle.** On a locally Noetherian integral scheme, let `U` be a
nonempty open subset at whose points the local rings are integrally closed, for instance an open
subset of a normal scheme. A rational function whose order is nonnegative at every
codimension-one point of `U` is the image of a section of `𝒪_X` over `U`. -/
theorem exists_germToFunctionField_eq_of_ord_nonneg_of_isIntegrallyClosed
    {U : X.Opens} [Nonempty U] (hU : ∀ y ∈ U, IsIntegrallyClosed (X.presheaf.stalk y))
    {f : X.functionField} (hf : ∀ y : CodimensionOnePoint X, (y : X) ∈ U → 0 ≤ X.ord f y) :
    ∃ a : Γ(X, U), X.germToFunctionField U a = f :=
  exists_germToFunctionField_eq_of_forall_mem_range fun y hy ↦
    have := hU y hy
    exists_algebraMap_stalk_eq_of_forall_ord_nonneg fun z hz ↦ hf z (hz.mem_open U.isOpen hy)

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
integral scheme, let `U` be a nonempty open subset at whose points the local rings are integrally
closed. A nonzero rational function whose order vanishes at every codimension-one point of `U` is
the germ of a unit of `Γ(X, U)`.

Simultaneous regularity of the function and its inverse makes the resulting section a unit. -/
theorem exists_unit_germToFunctionField_eq_of_ord_eq_zero_of_isIntegrallyClosed
    {U : X.Opens} [Nonempty U] (hU : ∀ y ∈ U, IsIntegrallyClosed (X.presheaf.stalk y))
    {f : X.functionFieldˣ}
    (hf : ∀ (y : CodimensionOnePoint X), (y : X) ∈ U → X.ord (f : X.functionField) y = 0) :
    ∃ a : Γ(X, U)ˣ, X.germToFunctionField U (a : Γ(X, U)) = (f : X.functionField) :=
  exists_unit_germToFunctionField_eq_of_forall_ord_nonneg
    (fun _ ↦ exists_germToFunctionField_eq_of_ord_nonneg_of_isIntegrallyClosed hU) hf

omit [IsLocallyNoetherian X] in
/-- On an open subset of dimension at most one whose codimension-one local rings are discrete
valuation rings, every local ring is integrally closed: it is a discrete valuation ring or the
function field. -/
theorem isIntegrallyClosed_stalk_of_coheight_le_one {U : X.Opens}
    (hDVR : ∀ y : CodimensionOnePoint X, (y : X) ∈ U →
      IsDiscreteValuationRing (X.presheaf.stalk (y : X)))
    (hU : ∀ y ∈ U, coheight y ≤ 1) (y : X) (hy : y ∈ U) :
    IsIntegrallyClosed (X.presheaf.stalk y) := by
  rcases eq_or_lt_of_le (hU y hy) with hy' | hy'
  · have := hDVR ⟨y, hy'⟩ hy
    infer_instance
  · exact (isIntegrallyClosed_iff X.functionField).2 fun {f} _ ↦
      exists_algebraMap_stalk_eq_of_coheight_eq_zero (Order.lt_one_iff.mp hy') f

/-- **A rational function without poles is regular.** On a locally Noetherian integral scheme, let
`U` be a nonempty open subset of dimension at most one whose codimension-one local rings are
discrete valuation rings. A rational function whose order is nonnegative at every codimension-one
point of `U` is the image of a section of `𝒪_X` over `U`.

This is the one-dimensional case of algebraic Hartogs' principle: the local rings at the points of
`U` are discrete valuation rings or the function field, hence integrally closed. -/
theorem exists_germToFunctionField_eq_of_ord_nonneg
    {U : X.Opens} [Nonempty U]
    (hDVR : ∀ y : CodimensionOnePoint X, (y : X) ∈ U →
      IsDiscreteValuationRing (X.presheaf.stalk (y : X)))
    (hU : ∀ y ∈ U, coheight y ≤ 1) {f : X.functionField}
    (hf : ∀ (y : CodimensionOnePoint X), (y : X) ∈ U → 0 ≤ X.ord f y) :
    ∃ a : Γ(X, U), X.germToFunctionField U a = f :=
  exists_germToFunctionField_eq_of_ord_nonneg_of_isIntegrallyClosed
    (isIntegrallyClosed_stalk_of_coheight_le_one hDVR hU) hf

end Scheme

end

end AlgebraicGeometry

end TauCeti
