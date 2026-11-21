/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

import Mathlib.NumberTheory.NumberField.FractionalIdeal
import Mathlib.RingTheory.LocalProperties.Invertible
import TauCeti.RingTheory.FractionalIdeal.Projective

/-!
# Hilbert modular polarization lattices

For a number field `F` and an invertible fractional ideal `c` of its ring of integers `O`, the
polarization lattice in the space of row vectors `F × F` is `O ⊕ c⁻¹𝔡⁻¹`, with `𝔡` the absolute
different. It is finite projective of constant rank two over `O` and free of rank `2 [F : ℚ]`
over `ℤ`. No generator of `c` is chosen. Replacing `c` by `a c` for `a ∈ Fˣ` acts on the
second coordinate by `a⁻¹`.

The lattice is that of Birkbeck, Heuer and Williams, *Overconvergent Hilbert modular forms via
perfectoid modular varieties*, Notation 5.1(3). We use Mathlib's `FractionalIdeal.dual` for
trace duality.
-/

public section

open scoped NumberField nonZeroDivisors
open FractionalIdeal

namespace TauCeti.HilbertModular

variable {F : Type*} [Field F] [NumberField F]

/-- The polarization lattice `O ⊕ c⁻¹𝔡⁻¹` in the row representation, expressed using the trace
dual of `c` for its second summand. -/
noncomputable def polarizationLattice (c : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    Submodule (𝓞 F) (F × F) :=
  (1 : FractionalIdeal (𝓞 F)⁰ F).coeToSubmodule.prod
    (dual ℤ ℚ (c : FractionalIdeal (𝓞 F)⁰ F)).coeToSubmodule

/-- The polarization lattice written as a product with the inverse different. -/
theorem polarizationLattice_def (c : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    polarizationLattice c = (1 : Submodule (𝓞 F) F).prod
      ((c : FractionalIdeal (𝓞 F)⁰ F)⁻¹ * dual ℤ ℚ 1).coeToSubmodule := by
  rw [polarizationLattice, coeToSubmodule_one, dual_eq_mul_inv, mul_comm (dual ℤ ℚ 1)]

/-- A row belongs to the polarization lattice exactly when its first coordinate is integral
and its second lies in the trace dual of `c`. -/
@[simp] theorem mem_polarizationLattice {c : (FractionalIdeal (𝓞 F)⁰ F)ˣ} {x : F × F} :
    x ∈ polarizationLattice c ↔ x.1 ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) ∧
      x.2 ∈ dual ℤ ℚ (c : FractionalIdeal (𝓞 F)⁰ F) := (Iff.rfl)

/-- The coordinate equivalence of the polarization lattice with the product of the unit
fractional ideal and the trace dual of `c`. -/
noncomputable def polarizationLatticeEquiv (c : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    polarizationLattice c ≃ₗ[𝓞 F]
      ((1 : FractionalIdeal (𝓞 F)⁰ F) × dual ℤ ℚ (c : FractionalIdeal (𝓞 F)⁰ F)) :=
  Submodule.prodEquiv _ _

/-- The coordinate equivalence preserves the two entries of the row. -/
@[simp] theorem polarizationLatticeEquiv_apply (c : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (x : polarizationLattice c) :
    (((polarizationLatticeEquiv c x).1 : F), ((polarizationLatticeEquiv c x).2 : F)) = x :=
  (rfl)

/-- The inverse coordinate equivalence assembles the two entries into a row. -/
@[simp] theorem polarizationLatticeEquiv_symm_apply (c : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (x : (1 : FractionalIdeal (𝓞 F)⁰ F) × dual ℤ ℚ (c : FractionalIdeal (𝓞 F)⁰ F)) :
    ((polarizationLatticeEquiv c).symm x : F × F) = ((x.1 : F), (x.2 : F)) :=
  (rfl)

private noncomputable def dualUnit (c : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    (FractionalIdeal (𝓞 F)⁰ F)ˣ :=
  Units.mk0 (dual ℤ ℚ (c : FractionalIdeal (𝓞 F)⁰ F)) (dual_ne_zero ℤ ℚ c.ne_zero)

instance (c : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : Module.Finite (𝓞 F) (polarizationLattice c) := by
  let : Module.Finite (𝓞 F) (1 : FractionalIdeal (𝓞 F)⁰ F) := finite_units 1
  let : Module.Finite (𝓞 F) (dual ℤ ℚ (c : FractionalIdeal (𝓞 F)⁰ F)) := finite_units (dualUnit c)
  exact Module.Finite.of_surjective (polarizationLatticeEquiv c).symm.toLinearMap
    (polarizationLatticeEquiv c).symm.surjective

instance (c : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : Module.Projective (𝓞 F) (polarizationLattice c) := by
  let : Module.Projective (𝓞 F) (1 : FractionalIdeal (𝓞 F)⁰ F) := projective_units 1
  let : Module.Projective (𝓞 F) (dual ℤ ℚ (c : FractionalIdeal (𝓞 F)⁰ F)) :=
    projective_units (dualUnit c)
  exact Module.Projective.of_equiv' (polarizationLatticeEquiv c).symm

/-- At every prime of the ring of integers the polarization lattice has rank two. -/
theorem rankAtStalk_polarizationLattice (c : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (p : PrimeSpectrum (𝓞 F)) : Module.rankAtStalk (polarizationLattice c) p = 2 := by
  let : Module.Invertible (𝓞 F) (1 : FractionalIdeal (𝓞 F)⁰ F) := invertible_units 1
  let : Module.Invertible (𝓞 F) (dual ℤ ℚ (c : FractionalIdeal (𝓞 F)⁰ F)) :=
    invertible_units (dualUnit c)
  rw [Module.rankAtStalk_eq_of_equiv (polarizationLatticeEquiv c), Module.rankAtStalk_prod]
  simp [Module.rankAtStalk, Module.Invertible.finrank_eq_one]

instance (c : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : Module.Free ℤ (polarizationLattice c) :=
  Module.Free.of_equiv ((polarizationLatticeEquiv c).symm.restrictScalars ℤ)

instance (c : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : Module.Finite ℤ (polarizationLattice c) :=
  Module.Finite.trans (𝓞 F) (polarizationLattice c)

/-- The integral rank of the polarization lattice is twice the degree of the field. -/
theorem finrank_int_polarizationLattice (c : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    Module.finrank ℤ (polarizationLattice c) = 2 * Module.finrank ℚ F := by
  rw [((polarizationLatticeEquiv c).restrictScalars ℤ).finrank_eq, Module.finrank_prod]
  have h₁ : Module.finrank ℤ (1 : FractionalIdeal (𝓞 F)⁰ F) =
      Module.finrank ℤ (𝓞 F) := NumberField.fractionalIdeal_rank F 1
  have h₂ : Module.finrank ℤ (dual ℤ ℚ (c : FractionalIdeal (𝓞 F)⁰ F)) =
      Module.finrank ℤ (𝓞 F) := NumberField.fractionalIdeal_rank F (dualUnit c)
  rw [h₁, h₂, NumberField.RingOfIntegers.rank, two_mul]

/-- Multiplying the polarization ideal by `(a)` sends the lattice to its image under the
right row action of `diag(1, a⁻¹)`. -/
theorem map_polarizationLattice (c : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (a : Fˣ) :
    (polarizationLattice c).map (LinearMap.id.prodMap (LinearMap.mulLeft (𝓞 F) (a : F)⁻¹)) =
      polarizationLattice (toPrincipalIdeal (𝓞 F) F a * c) := by
  rw [polarizationLattice, polarizationLattice, LinearMap.prodMap_map_prod, Submodule.map_id]
  congr 1
  have h : dual ℤ ℚ (↑(toPrincipalIdeal (𝓞 F) F a * c) : FractionalIdeal (𝓞 F)⁰ F) =
      spanSingleton _ (a : F)⁻¹ * dual ℤ ℚ (c : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [dual_eq_mul_inv, dual_eq_mul_inv ℤ ℚ (c : FractionalIdeal (𝓞 F)⁰ F)]
    simp only [Units.val_mul, mul_inv, coe_toPrincipalIdeal, spanSingleton_inv]
    ac_rfl
  rw [h, coeToSubmodule_mul, coeToSubmodule_spanSingleton]
  ext x
  simp only [Submodule.mem_map, LinearMap.mulLeft_apply, Submodule.mem_span_singleton_mul]

private theorem mem_polarizationLattice_rat_one {x : ℚ × ℚ} :
    x ∈ polarizationLattice (F := ℚ) 1 ↔
      x.1 ∈ (algebraMap ℤ ℚ).range ∧ x.2 ∈ (algebraMap ℤ ℚ).range := by
  have h {y : ℚ} : y ∈ (1 : FractionalIdeal (𝓞 ℚ)⁰ ℚ) ↔
      y ∈ (algebraMap ℤ ℚ).range := by
    rw [mem_one_iff, ← IsIntegralClosure.isIntegral_iff (A := 𝓞 ℚ) (R := ℤ)]
    exact IsIntegrallyClosed.isIntegral_iff
  rw [mem_polarizationLattice, h, Units.val_one, mem_dual one_ne_zero]
  refine and_congr_right fun _ ↦ ⟨fun hy ↦ ?_, fun hy z hz ↦ ?_⟩
  · simpa [Algebra.traceForm_apply] using hy 1 (h.mpr (algebraMap ℤ ℚ).range.one_mem)
  · simpa [Algebra.traceForm_apply] using (algebraMap ℤ ℚ).range.mul_mem hy (h.mp hz)

-- A principal change of ideal can genuinely enlarge the embedded lattice.
example :
    (0, 1 / 2) ∈ polarizationLattice (toPrincipalIdeal (𝓞 ℚ) ℚ (Units.mk0 2 (by norm_num))) ∧
      (0, 1 / 2) ∉ polarizationLattice (F := ℚ) 1 := by
  have h (a : ℚˣ) := map_polarizationLattice (F := ℚ) 1 a
  refine ⟨?_, ?_⟩
  · rw [← mul_one (toPrincipalIdeal _ _ _), ← h, Submodule.mem_map]
    refine ⟨(0, 1), mem_polarizationLattice_rat_one.mpr ⟨?_, ?_⟩, ?_⟩
    · exact (algebraMap ℤ ℚ).range.zero_mem
    · exact (algebraMap ℤ ℚ).range.one_mem
    · simp [one_div]
  · rw [mem_polarizationLattice_rat_one]
    rintro ⟨_, n, hn⟩
    have hn' : (n : ℚ) * 2 = 1 := by
      simpa [algebraMap_int_eq] using (eq_div_iff (by norm_num)).mp hn
    exact (by omega : ¬ n * 2 = 1) (by exact_mod_cast hn')

end TauCeti.HilbertModular
