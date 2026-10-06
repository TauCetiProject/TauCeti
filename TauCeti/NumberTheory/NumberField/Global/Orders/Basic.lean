/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.FractionalIdeal.Basic

/-!
# Orders in number fields

An order in a number field `K` is a subalgebra over `ℤ` that is finite as a `ℤ`-module and spans
`K` over `ℚ`.  The spanning condition ensures that `K` is the fraction field of the order; this
file installs that instance, so fractional ideals and Picard groups can be formed directly over an
order.

Every order consists of algebraic integers, because module-finiteness implies integrality.  Thus it
embeds canonically in the maximal order `𝓞 K`; in particular it is never the whole field.  The
maximal order itself is packaged as `maximalNumberFieldOrder K`.

## Main definitions

* `TauCeti.GlobalNumberFields.NumberFieldOrder`: an order in a number field.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.toRingOfIntegers`: an order as a subalgebra of the
  maximal order.
* `TauCeti.GlobalNumberFields.maximalNumberFieldOrder`: the ring of integers as an order.

## Main results

* `TauCeti.GlobalNumberFields.NumberFieldOrder.isFractionRing`: the ambient number field is the
  fraction field of any order.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.le_ringOfIntegers`: every order is contained in the
  ring of integers.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.toSubalgebra_ne_top`: an order is a proper subring
  of its number field.
* `Ideal.restrictScalars_coeIdeal_map_toRingOfIntegersEquiv_mul_one`:
  over `ℤ`, an ideal of an order times `𝓞 K` is its extension to `𝓞 K`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §2.
* G. S. Kopp and J. C. Lagarias, *Class Field Theory for Orders of Number Fields*, §2.
-/

public section
noncomputable section

open NumberField
open scoped nonZeroDivisors

namespace TauCeti.GlobalNumberFields

universe u

/-- An order in a number field `K`: a subring containing `ℤ`, finite as a `ℤ`-module, whose
`ℚ`-span is all of `K`. -/
structure NumberFieldOrder (K : Type u) [Field K] [NumberField K] where
  /-- The order as a `ℤ`-subalgebra of its ambient number field. -/
  toSubalgebra : Subalgebra ℤ K
  /-- An order is finitely generated as a `ℤ`-module. -/
  finite : Module.Finite ℤ toSubalgebra
  /-- An order has full rank in its ambient number field. -/
  spans : Submodule.span ℚ (toSubalgebra : Set K) = ⊤

namespace NumberFieldOrder

variable {K : Type u} [Field K] [NumberField K]

attribute [instance] finite

/-- Two orders in the same number field are equal when their underlying subalgebras are equal. -/
@[ext]
theorem ext {O O' : NumberFieldOrder K} (h : O.toSubalgebra = O'.toSubalgebra) : O = O' := by
  cases O
  cases O'
  cases h
  rfl

/-- Every element of an order is integral over `ℤ`. -/
theorem isIntegral (O : NumberFieldOrder K) (x : O.toSubalgebra) :
    IsIntegral ℤ (x : K) :=
  (IsIntegral.of_finite ℤ x).map O.toSubalgebra.val

/-- Every order in a number field is contained in its ring of integers. -/
theorem le_ringOfIntegers (O : NumberFieldOrder K) :
    O.toSubalgebra ≤ integralClosure ℤ K := fun x hx => by
  exact (O.isIntegral ⟨x, hx⟩)

/-- An order `O`, viewed as a `ℤ`-subalgebra of the maximal order `𝓞 K`. -/
def toRingOfIntegers (O : NumberFieldOrder K) : Subalgebra ℤ (𝓞 K) :=
  O.toSubalgebra.comap (IsScalarTower.toAlgHom ℤ (𝓞 K) K)

/-- An algebraic integer lies in the copy of `O` inside `𝓞 K` exactly when it lies in `O`. -/
@[simp]
theorem mem_toRingOfIntegers (O : NumberFieldOrder K) {x : 𝓞 K} :
    x ∈ O.toRingOfIntegers ↔ (x : K) ∈ O.toSubalgebra :=
  Iff.rfl

/-- The copy `O.toRingOfIntegers` of an order inside `𝓞 K` is isomorphic to the order itself.
This moves ideals of the order between the two models: comparisons with ideals of `𝓞 K` use the
former, fractional ideals and Picard groups the latter. -/
def toRingOfIntegersEquiv (O : NumberFieldOrder K) : O.toRingOfIntegers ≃+* O.toSubalgebra where
  toFun x := ⟨((x : 𝓞 K) : K), x.2⟩
  invFun y := ⟨⟨y, O.le_ringOfIntegers y.2⟩, O.mem_toRingOfIntegers.mpr y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- The isomorphism `toRingOfIntegersEquiv` does not change the underlying element of `K`. -/
@[simp]
theorem coe_toRingOfIntegersEquiv (O : NumberFieldOrder K) (x : O.toRingOfIntegers) :
    (O.toRingOfIntegersEquiv x : K) = ((x : 𝓞 K) : K) :=
  (rfl)

/-- The inverse of `toRingOfIntegersEquiv` does not change the underlying element of `K`. -/
@[simp]
theorem coe_toRingOfIntegersEquiv_symm (O : NumberFieldOrder K) (y : O.toSubalgebra) :
    (((O.toRingOfIntegersEquiv.symm y : O.toRingOfIntegers) : 𝓞 K) : K) = y :=
  (rfl)

/-- An order is a proper subring of its number field. -/
theorem toSubalgebra_ne_top (O : NumberFieldOrder K) : O.toSubalgebra ≠ ⊤ := by
  intro h
  have : Algebra.IsIntegral ℤ K := ⟨fun x => O.isIntegral ⟨x, by rw [h]; exact Algebra.mem_top⟩⟩
  exact Int.not_isField
    ((Algebra.IsIntegral.isField_iff_isField (algebraMap ℤ K).injective_int).mpr
      (Field.toIsField K))

private theorem exists_order_div (O : NumberFieldOrder K) (z : K) :
    ∃ a b : O.toSubalgebra, (b : K) ≠ 0 ∧ z = (a : K) / (b : K) := by
  have hz : z ∈ Submodule.span ℚ (O.toSubalgebra : Set K) := by
    rw [O.spans]
    exact Submodule.mem_top
  induction hz using Submodule.span_induction with
  | mem x hx =>
      exact ⟨⟨x, hx⟩, 1, one_ne_zero, by simp⟩
  | zero =>
      exact ⟨0, 1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
      obtain ⟨a, b, hb, hxab⟩ := hx
      obtain ⟨c, d, hd, hycd⟩ := hy
      refine ⟨a * d + c * b, b * d, mul_ne_zero hb hd, ?_⟩
      push_cast
      rw [hxab, hycd]
      field_simp
  | smul q x _ hx =>
      obtain ⟨a, b, hb, hxab⟩ := hx
      obtain ⟨m, n, hn, hq⟩ := IsFractionRing.div_surjective ℤ q
      have hnK : algebraMap ℤ K n ≠ 0 := by
        simpa using (Int.cast_ne_zero.mpr (mem_nonZeroDivisors_iff_ne_zero.mp hn) : (n : K) ≠ 0)
      refine ⟨algebraMap ℤ O.toSubalgebra m * a,
        algebraMap ℤ O.toSubalgebra n * b, mul_ne_zero hnK hb, ?_⟩
      push_cast
      rw [Algebra.smul_def, hxab, ← hq]
      rw [map_div₀ (algebraMap ℚ K), ← IsScalarTower.algebraMap_apply ℤ ℚ K m,
        ← IsScalarTower.algebraMap_apply ℤ ℚ K n]
      field_simp

/-- The ambient number field is the fraction field of each of its orders. -/
instance isFractionRing (O : NumberFieldOrder K) : IsFractionRing O.toSubalgebra K :=
  IsFractionRing.of_field O.toSubalgebra K fun z => by
    obtain ⟨a, b, _, hz⟩ := O.exists_order_div z
    exact ⟨a, b, hz⟩

/-! ### Ideals of an order and of the maximal order -/

section

variable {O : NumberFieldOrder K}

/-- An element of `K` lies in the fractional ideal of `O` attached to an ideal `I` of
`O.toRingOfIntegers` exactly when it is an element of `I`. -/
theorem mem_coeIdeal_map_toRingOfIntegersEquiv {I : Ideal O.toRingOfIntegers} {y : K} :
    y ∈ ((I.map O.toRingOfIntegersEquiv : Ideal O.toSubalgebra) :
        FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) ↔
      ∃ x ∈ I, ((x : 𝓞 K) : K) = y := by
  rw [FractionalIdeal.mem_coeIdeal]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_of_equiv _ a).mp ha
    exact ⟨x, hx, by simp⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, Ideal.mem_map_of_mem _ hx, by simp⟩

/-- Over `ℤ`, the product of an ideal `I` of the order with `𝓞 K` is the extension of `I` to
`𝓞 K`. -/
theorem _root_.Ideal.restrictScalars_coeIdeal_map_toRingOfIntegersEquiv_mul_one
    (I : Ideal O.toRingOfIntegers) :
    (((I.map O.toRingOfIntegersEquiv : Ideal O.toSubalgebra) :
        FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) :
          Submodule O.toSubalgebra K).restrictScalars ℤ *
        (1 : Submodule (𝓞 K) K).restrictScalars ℤ =
      (((I.map (O.toRingOfIntegers.val : O.toRingOfIntegers →+* 𝓞 K) : Ideal (𝓞 K)) :
        FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).restrictScalars ℤ := by
  set i := (((I.map O.toRingOfIntegersEquiv : Ideal O.toSubalgebra) :
    FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) :
      Submodule O.toSubalgebra K).restrictScalars ℤ
  -- The extension of `I` is the `𝓞 K`-span of the elements of `I`.
  have hspan : (((I.map (O.toRingOfIntegers.val : O.toRingOfIntegers →+* 𝓞 K) : Ideal (𝓞 K)) :
      FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) = Submodule.span (𝓞 K) (i : Set K) := by
    rw [FractionalIdeal.coe_coeIdeal, Ideal.map, IsLocalization.coeSubmodule_span,
      Set.image_image]
    congr 1
    ext y
    exact mem_coeIdeal_map_toRingOfIntegersEquiv.symm
  -- Over `ℤ`, that span is spanned by the products `r • x` with `r ∈ 𝓞 K` and `x ∈ i`.
  rw [hspan, ← Submodule.span_smul_of_span_eq_top (R := ℤ) Submodule.span_univ]
  conv_lhs => rw [← Submodule.span_eq i,
    ← Submodule.span_eq ((1 : Submodule (𝓞 K) K).restrictScalars ℤ), Submodule.span_mul_span]
  congr 1
  ext y
  simp only [Set.mem_mul, Set.mem_smul, Set.mem_univ, true_and, SetLike.mem_coe,
    Submodule.restrictScalars_mem, Submodule.mem_one]
  constructor
  · rintro ⟨x, hx, _, ⟨r, rfl⟩, rfl⟩
    exact ⟨r, x, hx, by rw [Algebra.smul_def, mul_comm]⟩
  · rintro ⟨r, x, hx, rfl⟩
    exact ⟨x, hx, _, ⟨r, rfl⟩, by rw [Algebra.smul_def, mul_comm]⟩

end

end NumberFieldOrder

/-- The maximal order of a number field, namely its ring of integers. -/
def maximalNumberFieldOrder (K : Type u) [Field K] [NumberField K] : NumberFieldOrder K where
  toSubalgebra := integralClosure ℤ K
  finite := inferInstanceAs (Module.Finite ℤ (𝓞 K))
  spans := by
    apply top_unique
    rw [← (integralBasis K).span_eq]
    exact Submodule.span_mono fun x hx => by
      obtain ⟨i, rfl⟩ := hx
      rw [integralBasis_apply]
      exact (RingOfIntegers.basis K i).property

@[simp]
theorem maximalNumberFieldOrder_toSubalgebra
    (K : Type u) [Field K] [NumberField K] :
    (maximalNumberFieldOrder K).toSubalgebra = integralClosure ℤ K := (rfl)

end TauCeti.GlobalNumberFields
