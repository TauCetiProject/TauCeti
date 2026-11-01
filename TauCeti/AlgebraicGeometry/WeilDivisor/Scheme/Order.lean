/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Basic
public import Mathlib.AlgebraicGeometry.OrderOfVanishing
import Mathlib.RingTheory.SimpleModule.Basic
import TauCeti.AlgebraicGeometry.Scheme.StalkSpecializes
import TauCeti.RingTheory.OrderOfVanishing

/-!
# Orders of rational functions at codimension-one points

For a locally Noetherian integral scheme `X`, Mathlib defines the order of vanishing
`Scheme.ord f x : ℤ` of a rational function at a point. This file packages its restriction to
nonzero rational functions at a codimension-one point as an additive homomorphism

`SchemeWeilDivisor.orderAt x : Additive X.functionFieldˣ →+ ℤ`.

This is the local algebraic input for the scheme-theoretic principal-divisor map. Constructing
that map also requires the separate global theorem that a nonzero rational function has nonzero
order at only finitely many codimension-one points; no finiteness assumption is hidden here.

Elementary facts about `Scheme.ord` itself are recorded first: the order of one vanishes
(`Scheme.ord_one`), the order of an inverse is the negative of the order (`Scheme.ord_inv`), and a
function regular on `U` has nonnegative order at every point of `U`
(`Scheme.ord_germToFunctionField_nonneg`), that is, it has no poles where it is defined. On an
element of the local ring at a codimension-one point, the order is the length `Ring.ord` of its
quotient (`Scheme.ord_algebraMap_stalk`). More generally, at a codimension-one generization `η`
of a point `x`, the order of a nonzero germ at `x` is the `Ring.ord` of its image in `𝒪_{X,η}`
(`Scheme.ord_algebraMap_stalk_of_specializes`), and in particular it is nonnegative
(`Scheme.ord_algebraMap_stalk_nonneg`). It vanishes exactly when the germ lies outside the prime
of `𝒪_{X,x}` under the maximal ideal of `𝒪_{X,η}` (`Scheme.ord_algebraMap_stalk_eq_zero_iff`),
and a generator of that prime has order one (`Scheme.ord_algebraMap_stalk_eq_one`).

Where the local ring at a codimension-one point is a discrete valuation ring, `orderAt` is
surjective onto `ℤ` (`SchemeWeilDivisor.exists_orderAt_eq`): the powers of a uniformizer supply
a rational function of each prescribed order.

The construction reuses Mathlib's `AlgebraicGeometry.Scheme.ord`, `ordHom`, and
`ord_eq_unzero_ordHom`; no external formalization is vendored.
-/

public section

open AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

noncomputable section

namespace Scheme

/-- The constant function one has order zero at every point: it is a global regular unit. -/
@[simp]
lemma ord_one {x : X} : X.ord (1 : X.functionField) x = 0 := by
  let _ : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
  -- Naming this proof fixes the open set before elaborating `ord_of_isUnit`.
  have hx_top : x ∈ (⊤ : X.Opens) := by simp
  simpa using X.ord_of_isUnit (U := ⊤) isUnit_one hx_top

/-- The order of an inverse is the negative of the order. Both sides vanish at the zero function,
whose inverse is again zero. -/
@[simp]
lemma ord_inv (f : X.functionField) {x : X} : X.ord f⁻¹ x = -X.ord f x := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · have h := X.ord_mul (x := x) hf (inv_ne_zero hf)
    rw [mul_inv_cancel₀ hf, ord_one] at h
    omega

/-- A regular function on `U` has nonnegative order at every point of `U`: it has no poles where
it is defined. -/
lemma ord_germToFunctionField_nonneg {U : X.Opens} [Nonempty U] (a : Γ(X, U)) {x : X}
    (hx : x ∈ U) : 0 ≤ X.ord (X.germToFunctionField U a) x := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · have h := Scheme.ord_le_smul hx ha (1 : X.functionField)
    rwa [Algebra.smul_def, mul_one, RingHom.algebraMap_toAlgebra, ord_one] at h

/-- At a codimension-one point `x`, the order of the image in the function field of a nonzero
element `c` of the local ring `𝒪_{X,x}` is its order of vanishing `Ring.ord`, the length of
`𝒪_{X,x} ⧸ (c)`. -/
theorem ord_algebraMap_stalk {x : X} (hx : Order.coheight x = 1) {c : X.presheaf.stalk x}
    (hc : c ≠ 0) :
    X.ord (algebraMap (X.presheaf.stalk x) X.functionField c) x =
      (Ring.ord (X.presheaf.stalk x) c).toNat := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have hnz : c ∈ nonZeroDivisors (X.presheaf.stalk x) := mem_nonZeroDivisors_of_ne_zero hc
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (Ring.ord_ne_top hnz)
  have hne : algebraMap (X.presheaf.stalk x) X.functionField c ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hc
  rw [X.ord_eq_iff hx hne, ← hn, ENat.toNat_natCast]
  simp only [_root_.AlgebraicGeometry.Scheme.ordHom]
  rw [Ring.ordFrac_eq_ord _ hc, Ring.ordMonoidWithZeroHom_eq_coe _ hnz hn.symm]

/-- At a codimension-one generization `η` of `x`, the order of a nonzero germ at `x` is the
order of vanishing `Ring.ord` of its image in the one-dimensional local ring `𝒪_{X,η}`. -/
theorem ord_algebraMap_stalk_of_specializes {x η : X} (hη : Order.coheight η = 1) (h : η ⤳ x)
    {b : X.presheaf.stalk x} (hb : b ≠ 0) :
    X.ord (algebraMap (X.presheaf.stalk x) X.functionField b) η =
      (Ring.ord (X.presheaf.stalk η) ((X.presheaf.stalkSpecializes h).hom b)).toNat := by
  rw [← algebraMap_stalkSpecializes h,
    ord_algebraMap_stalk hη ((map_ne_zero_iff _ (stalkSpecializes_injective h)).mpr hb)]

/-- A nonzero germ at `x` has nonnegative order at every codimension-one generization of `x`. -/
theorem ord_algebraMap_stalk_nonneg {x η : X} (hη : Order.coheight η = 1) (h : η ⤳ x)
    {b : X.presheaf.stalk x} (hb : b ≠ 0) :
    0 ≤ X.ord (algebraMap (X.presheaf.stalk x) X.functionField b) η := by
  rw [ord_algebraMap_stalk_of_specializes hη h hb]
  exact Int.natCast_nonneg _

/-- At a codimension-one generization `η` of `x`, a nonzero germ at `x` has order zero exactly
when it lies outside the prime of `𝒪_{X,x}` lying under the maximal ideal of `𝒪_{X,η}`. -/
theorem ord_algebraMap_stalk_eq_zero_iff {x η : X} (hη : Order.coheight η = 1) (h : η ⤳ x)
    {b : X.presheaf.stalk x} (hb : b ≠ 0) :
    X.ord (algebraMap (X.presheaf.stalk x) X.functionField b) η = 0 ↔
      b ∉ (IsLocalRing.maximalIdeal (X.presheaf.stalk η)).comap
        (X.presheaf.stalkSpecializes h).hom := by
  have hc := (map_ne_zero_iff _ (stalkSpecializes_injective h)).mpr hb
  have : Ring.KrullDimLE 1 (X.presheaf.stalk η) := krullDimLE_of_coheight_le hη.le
  have hnt := Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hc)
  rw [ord_algebraMap_stalk_of_specializes hη h hb, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, not_not, ← TauCeti.Ring.ord_eq_zero_iff, Int.natCast_eq_zero,
    ENat.toNat_eq_zero]
  exact or_iff_left hnt

/-- At a codimension-one generization `η` of `x`, a nonzero generator of the prime of `𝒪_{X,x}`
lying under the maximal ideal of `𝒪_{X,η}` has order one at `η`: its image generates the maximal
ideal of `𝒪_{X,η}`. -/
theorem ord_algebraMap_stalk_eq_one {x η : X} (hη : Order.coheight η = 1) (h : η ⤳ x)
    {p : X.presheaf.stalk x}
    (hp : (IsLocalRing.maximalIdeal (X.presheaf.stalk η)).comap
      (X.presheaf.stalkSpecializes h).hom = Ideal.span {p}) (hp0 : p ≠ 0) :
    X.ord (algebraMap (X.presheaf.stalk x) X.functionField p) η = 1 := by
  rw [ord_algebraMap_stalk_of_specializes hη h hp0]
  suffices Ring.ord (X.presheaf.stalk η) ((X.presheaf.stalkSpecializes h).hom p) = 1 by
    rw [this, ENat.toNat_one, Nat.cast_one]
  let := (X.presheaf.stalkSpecializes h).hom.toAlgebra
  have := isLocalization_stalkSpecializes h
  have hmax : IsLocalRing.maximalIdeal (X.presheaf.stalk η) =
      Ideal.span {(X.presheaf.stalkSpecializes h).hom p} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal
      ((IsLocalRing.maximalIdeal (X.presheaf.stalk η)).comap (X.presheaf.stalkSpecializes h).hom),
      hp, Ideal.map_span, Set.image_singleton, RingHom.algebraMap_toAlgebra]
  rw [Ring.ord, ← hmax, Module.length_eq_one_iff, isSimpleModule_iff_isCoatom]
  exact (IsLocalRing.maximalIdeal.isMaximal _).out

end Scheme

namespace SchemeWeilDivisor

/-- The order of a nonzero rational function at a codimension-one point, as an additive
homomorphism from the additive form of the unit group of the function field. -/
noncomputable def orderAt (x : CodimensionOnePoint X) :
    Additive (X.functionFieldˣ) →+ ℤ :=
  MonoidHom.toAdditiveLeft
    (WithZero.unitsWithZeroEquiv.toMonoidHom.comp
      (Units.map (X.ordHom x x.property).toMonoidHom))

/-- Evaluating `orderAt` gives Mathlib's integer-valued order of vanishing. -/
@[simp]
lemma orderAt_apply (x : CodimensionOnePoint X) (f : Additive X.functionFieldˣ) :
    orderAt x f = X.ord ((Additive.toMul f : X.functionFieldˣ) : X.functionField) x := by
  rw [X.ord_eq_unzero_ordHom x.property
    (Units.ne_zero (Additive.toMul f : X.functionFieldˣ))]
  simp only [orderAt, MonoidHom.toAdditiveLeft_apply_apply, MonoidHom.coe_comp,
    MulEquiv.coe_toMonoidHom, Function.comp_apply, WithZero.unitsWithZeroEquiv_apply]
  congr 1

/-- **Every integer is an order of vanishing.** At a codimension-one point whose local ring is a
discrete valuation ring, a uniformizer has order one, so its integer powers realize every integer
as the order of a nonzero rational function. -/
theorem exists_orderAt_eq (x : CodimensionOnePoint X)
    [IsDiscreteValuationRing (X.presheaf.stalk (x : X))] (n : ℤ) :
    ∃ g : Additive X.functionFieldˣ, orderAt x g = n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk (x : X))
  have hinj := IsFractionRing.injective (X.presheaf.stalk (x : X)) X.functionField
  have hne : algebraMap (X.presheaf.stalk (x : X)) X.functionField ϖ ≠ 0 := fun h ↦
    hϖ.ne_zero (hinj (h.trans (map_zero _).symm))
  have hord : X.ord (algebraMap (X.presheaf.stalk (x : X)) X.functionField ϖ) (x : X) = 1 := by
    rw [X.ord_eq_iff x.property hne]
    simp only [_root_.AlgebraicGeometry.Scheme.ordHom]
    rw [Ring.ordFrac_irreducible hϖ, WithZero.exp_eq_coe_ofAdd]
  refine ⟨n • Additive.ofMul (Units.mk0 _ hne), ?_⟩
  rw [map_zsmul, orderAt_apply]
  simp [hord]

end SchemeWeilDivisor

end

end AlgebraicGeometry

end TauCeti
