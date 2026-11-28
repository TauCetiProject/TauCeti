/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import TauCeti.NumberTheory.NumberField.CMField.AdeleStar
public import TauCeti.NumberTheory.NumberField.Global.Adeles.AddChar
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.BorelSpace
public import TauCeti.Topology.Algebra.Star.SelfAdjoint
import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
import TauCeti.NumberTheory.NumberField.Countable

/-!
# The self-adjoint finite adeles of a CM field and their dual lattice

Let `E` be a CM field with finite adeles `𝔸_f`, integral finite adeles `Ô`, complex conjugation
`z ↦ star z` (the star structure `NumberField.IsCMField.instStarRingFiniteAdeleRing`) and standard
finite character `ψ_f` (`TauCeti.GlobalNumberFields.finiteAdeleAddChar`). The *self-adjoint finite
adeles* `𝔸_f⁺ = {z ∈ 𝔸_f : star z = z}` are Mathlib's `selfAdjoint 𝔸ᶠ[E]`; they play the part of the
finite adeles of the maximal totally real subfield `E⁺`. They form a closed subgroup of `𝔸_f`
(Mathlib's `isClosed_setOfPred_isSelfAdjoint`), hence a locally compact, second countable abelian
group.

The *dual lattice* `𝔡 = {z ∈ 𝔸_f⁺ : ψ_f(zÔ) = 1}` (`TauCeti.selfAdjointFiniteAdeleDual`) is the
trace on `𝔸_f⁺` of the annihilator of `Ô` under `ψ_f`, which is the finite adelic ideal `𝔇⁻¹Ô` of
the inverse different (`TauCeti.GlobalNumberFields.forall_finiteAdeleAddChar_mul_eq_one_iff`). So
`𝔡` is a compact open subgroup of `𝔸_f⁺`, and it normalises a Haar measure on `𝔸_f⁺`: the measure
`TauCeti.selfAdjointFiniteAdeleHaar` with `vol(𝔡) = 1`. It is regular, so, as `𝔸_f⁺` is abelian,
Mathlib's `MeasureTheory.Measure.IsAddHaarMeasure.isNegInvariant_of_regular` makes it invariant
under negation.

This is the measure of the variable `z` of the Fourier integrals over `𝔸_f⁺` that define the
density of a function at a norm of the standard hermitian form (`TauCeti.normDensity`).

## Main declarations

* `TauCeti.selfAdjointFiniteAdeleDual`: the dual lattice `𝔡`, with
  `TauCeti.mem_selfAdjointFiniteAdeleDual_iff_mem_finiteAdelicIdeal`,
  `TauCeti.isOpen_selfAdjointFiniteAdeleDual` and `TauCeti.isCompact_selfAdjointFiniteAdeleDual`.
* `TauCeti.selfAdjointFiniteAdeleHaar`: the Haar measure of `𝔸_f⁺` with `vol(𝔡) = 1`
  (`TauCeti.selfAdjointFiniteAdeleHaar_selfAdjointFiniteAdeleDual`), characterised among the
  Haar measures by this normalisation
  (`Measure.eq_selfAdjointFiniteAdeleHaar_of_apply_selfAdjointFiniteAdeleDual_eq_one`).

## References

* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, thesis (1950), §4.1.
-/

public section
noncomputable section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing NumberField NumberField.IsCMField
  MeasureTheory MeasureTheory.Measure TauCeti.GlobalNumberFields Topology TopologicalSpace
open scoped NumberField.AdeleRing nonZeroDivisors

namespace TauCeti

variable (E : Type*) [Field E] [NumberField E] [IsCMField E]

/-- The **dual lattice** `𝔡 = {z ∈ 𝔸_f⁺ : ψ_f(zÔ) = 1}` of the self-adjoint finite adeles of a CM
field: the self-adjoint finite adeles `z` with `ψ_f (z u) = 1` for every integral finite adele
`u`. -/
def selfAdjointFiniteAdeleDual : AddSubgroup (selfAdjoint 𝔸ᶠ[E]) where
  carrier := {z | ∀ u ∈ integralAdeles (𝓞 E) E, finiteAdeleAddChar E ((z : 𝔸ᶠ[E]) * u) = 1}
  zero_mem' := by simp
  add_mem' {a b} ha hb u hu := by
    rw [AddMemClass.coe_add, add_mul, AddChar.map_add_eq_mul, ha u hu, hb u hu, one_mul]
  neg_mem' {a} ha u hu := by
    rw [NegMemClass.coe_neg, neg_mul, AddChar.map_neg_eq_inv, ha u hu, inv_one]

variable {E}

/-- A self-adjoint finite adele `z` lies in the dual lattice `𝔡` exactly when `ψ_f (z u) = 1` for
every integral finite adele `u`. -/
theorem mem_selfAdjointFiniteAdeleDual_iff {z : selfAdjoint 𝔸ᶠ[E]} :
    z ∈ selfAdjointFiniteAdeleDual E ↔
      ∀ u ∈ integralAdeles (𝓞 E) E, finiteAdeleAddChar E ((z : 𝔸ᶠ[E]) * u) = 1 :=
  Iff.rfl

/-- A self-adjoint finite adele lies in the dual lattice `𝔡` exactly when it lies in the finite
adelic ideal `𝔇⁻¹Ô` of the inverse different `𝔇⁻¹ = FractionalIdeal.dual ℤ ℚ 1`. -/
theorem mem_selfAdjointFiniteAdeleDual_iff_mem_finiteAdelicIdeal {z : selfAdjoint 𝔸ᶠ[E]} :
    z ∈ selfAdjointFiniteAdeleDual E ↔
      (z : 𝔸ᶠ[E]) ∈ finiteAdelicIdeal (Units.mk0 (FractionalIdeal.dual ℤ ℚ 1)
        (FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero)) :=
  forall_finiteAdeleAddChar_mul_eq_one_iff (z : 𝔸ᶠ[E])

/-- The dual lattice `𝔡` is the preimage in `𝔸_f⁺` of the finite adelic ideal of the inverse
different. -/
theorem coe_selfAdjointFiniteAdeleDual :
    (selfAdjointFiniteAdeleDual E : Set (selfAdjoint 𝔸ᶠ[E])) =
      Subtype.val ⁻¹' (finiteAdelicIdeal (R := 𝓞 E) (K := E)
        (Units.mk0 (FractionalIdeal.dual ℤ ℚ 1) (FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero)) :
          Set 𝔸ᶠ[E]) :=
  Set.ext fun _ ↦ mem_selfAdjointFiniteAdeleDual_iff_mem_finiteAdelicIdeal

variable (E)

/-- The dual lattice `𝔡` is open in the self-adjoint finite adeles. -/
theorem isOpen_selfAdjointFiniteAdeleDual :
    IsOpen (selfAdjointFiniteAdeleDual E : Set (selfAdjoint 𝔸ᶠ[E])) := by
  -- `𝔡` is cut out by `t⁻¹ z ∈ Ô` for a finite idele `t` representing the inverse different
  obtain ⟨t, ht⟩ := toFractionalIdeal_surjective (R := 𝓞 E) (K := E)
    (Units.mk0 (FractionalIdeal.dual ℤ ℚ 1) (FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero))
  have h𝔡 : (selfAdjointFiniteAdeleDual E : Set (selfAdjoint 𝔸ᶠ[E])) =
      (fun z : selfAdjoint 𝔸ᶠ[E] ↦ (↑t⁻¹ : 𝔸ᶠ[E]) * z) ⁻¹' (integralAdeles (𝓞 E) E : Set 𝔸ᶠ[E]) :=
    Set.ext fun _ ↦ mem_selfAdjointFiniteAdeleDual_iff_mem_finiteAdelicIdeal.trans
      (mem_finiteAdelicIdeal_iff t ht)
  rw [h𝔡]
  exact (isOpen_integralAdeles _ _).preimage (continuous_const.mul continuous_subtypeVal)

/-- The dual lattice `𝔡` is compact. -/
theorem isCompact_selfAdjointFiniteAdeleDual :
    IsCompact (selfAdjointFiniteAdeleDual E : Set (selfAdjoint 𝔸ᶠ[E])) := by
  rw [coe_selfAdjointFiniteAdeleDual]
  exact (isClosed_setOfPred_isSelfAdjoint (α := 𝔸ᶠ[E])).isClosedEmbedding_subtypeVal
    |>.isCompact_preimage (isCompact_finiteAdelicIdeal _)

/-- The dual lattice `𝔡`, as a compact subset of `𝔸_f⁺` with nonempty interior. -/
def selfAdjointFiniteAdeleDualPositiveCompacts : PositiveCompacts (selfAdjoint 𝔸ᶠ[E]) where
  carrier := selfAdjointFiniteAdeleDual E
  isCompact' := isCompact_selfAdjointFiniteAdeleDual E
  interior_nonempty' := by
    rw [(isOpen_selfAdjointFiniteAdeleDual E).interior_eq]
    exact ⟨0, zero_mem _⟩

/-- The underlying set of `selfAdjointFiniteAdeleDualPositiveCompacts` is the dual lattice. -/
@[simp]
theorem coe_selfAdjointFiniteAdeleDualPositiveCompacts :
    (selfAdjointFiniteAdeleDualPositiveCompacts E : Set (selfAdjoint 𝔸ᶠ[E])) =
      selfAdjointFiniteAdeleDual E :=
  (rfl)

/-- The **Haar measure of the self-adjoint finite adeles** `𝔸_f⁺` of a CM field normalised by
`vol(𝔡) = 1` for the dual lattice `𝔡 = {z ∈ 𝔸_f⁺ : ψ_f(zÔ) = 1}`. -/
def selfAdjointFiniteAdeleHaar : Measure (selfAdjoint 𝔸ᶠ[E]) :=
  addHaarMeasure (selfAdjointFiniteAdeleDualPositiveCompacts E)

/-- The Haar measure of `𝔸_f⁺` is Mathlib's Haar measure normalised by the compact set `𝔡`. -/
theorem selfAdjointFiniteAdeleHaar_def :
    selfAdjointFiniteAdeleHaar E = addHaarMeasure (selfAdjointFiniteAdeleDualPositiveCompacts E) :=
  (rfl)

instance : (selfAdjointFiniteAdeleHaar E).IsAddHaarMeasure := by
  rw [selfAdjointFiniteAdeleHaar_def]
  exact isAddHaarMeasure_addHaarMeasure _

instance : (selfAdjointFiniteAdeleHaar E).Regular := by
  rw [selfAdjointFiniteAdeleHaar_def]
  exact regular_addHaarMeasure

/-- The dual lattice `𝔡` has measure one. -/
@[simp]
theorem selfAdjointFiniteAdeleHaar_selfAdjointFiniteAdeleDual :
    selfAdjointFiniteAdeleHaar E (selfAdjointFiniteAdeleDual E) = 1 := by
  rw [selfAdjointFiniteAdeleHaar_def, ← coe_selfAdjointFiniteAdeleDualPositiveCompacts]
  exact addHaarMeasure_self

end TauCeti

open TauCeti

namespace MeasureTheory.Measure

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

/-- A Haar measure on `𝔸_f⁺` giving the dual lattice `𝔡` measure one is the Haar measure
`selfAdjointFiniteAdeleHaar`. -/
theorem eq_selfAdjointFiniteAdeleHaar_of_apply_selfAdjointFiniteAdeleDual_eq_one
    (μ : Measure (selfAdjoint 𝔸ᶠ[E])) [μ.IsAddHaarMeasure]
    (hμ : μ (selfAdjointFiniteAdeleDual E) = 1) : μ = selfAdjointFiniteAdeleHaar E := by
  rw [addHaarMeasure_unique μ (selfAdjointFiniteAdeleDualPositiveCompacts E),
    coe_selfAdjointFiniteAdeleDualPositiveCompacts, hμ, one_smul, selfAdjointFiniteAdeleHaar_def]

end MeasureTheory.Measure
