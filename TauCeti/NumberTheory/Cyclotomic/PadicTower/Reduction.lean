/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Cyclotomic.PadicTower.Basic
public import Mathlib.NumberTheory.Padics.RingHoms
import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.RingTheory.Polynomial.Cyclotomic.PrimePow
import TauCeti.RingTheory.RootsOfUnity.CyclotomicUnits

/-!
# Reduction and polynomial unit lifts in the local cyclotomic tower

Reduction from the integral closure of `ℤ_p` in the chosen cyclotomic level to `ZMod p` sends
the chosen root to one. The root minus one generates both the kernel of reduction and the
canonical maximal ideal, so it is a uniformizer of the discrete valuation ring.
The explicit reduction identifies the residue field and detects units in polynomial coordinates.
Every unit has a polynomial representative of degree below the cyclotomic degree with unit
constant coefficient. These results hold for every prime, including `p = 2`.

These algebraic inputs to finite-level interpolation follow J. Rodrigues Jacinto and C. Williams,
*An introduction to p-adic L-functions*, Essential Number Theory 4 (2025), §9 and Lemma 10.1.
-/

public section

open Polynomial IsLocalRing

namespace TauCeti.padicCyclotomicField

variable (p : ℕ) [Fact p.Prime] (Ω : Type*) [Field Ω] [Algebra ℚ_[p] Ω]
  [IsAlgClosed Ω] [Algebra ℤ_[p] Ω] [IsScalarTower ℤ_[p] ℚ_[p] Ω]

/-- The coefficient algebra on `ZMod p` for the reduction construction is induced by
`PadicInt.toZMod`. -/
noncomputable local instance : Algebra ℤ_[p] (ZMod p) := PadicInt.toZMod.toAlgebra

/-- Reduction of the integral cyclotomic level modulo the chosen root minus one. -/
noncomputable def reduction (n : ℕ) :
    integralClosure ℤ_[p] (padicCyclotomicField p Ω n) →+* ZMod p :=
  ((integralPowerBasis p Ω n).lift 0 (by
    rw [← coeff_zero_eq_aeval_zero']
    simp [integralPowerBasis_gen, minpoly_integralRoot_sub_one])).toRingHom

/-- On included `p`-adic integers, cyclotomic reduction is the native reduction modulo `p`. -/
@[simp]
theorem reduction_algebraMap (n : ℕ) (a : ℤ_[p]) :
    reduction p Ω n (algebraMap ℤ_[p] _ a) = PadicInt.toZMod a := by
  rw [← RingHom.algebraMap_toAlgebra (PadicInt.toZMod (p := p))]
  exact ((integralPowerBasis p Ω n).lift 0 _).commutes a

/-- The chosen cyclotomic difference reduces to zero. -/
theorem reduction_integralRoot_sub_one (n : ℕ) :
    reduction p Ω n (integralRoot p Ω n - 1) = 0 := by
  rw [reduction, ← integralPowerBasis_gen]
  exact PowerBasis.lift_gen _ _ _

/-- The chosen integral root reduces to one. -/
@[simp]
theorem reduction_integralRoot (n : ℕ) :
    reduction p Ω n (integralRoot p Ω n) = 1 := by
  simpa only [map_sub, map_one, sub_eq_zero] using reduction_integralRoot_sub_one p Ω n

/-- Reduction in polynomial coordinates reads the constant coefficient modulo `p`. -/
@[simp]
theorem reduction_aeval (n : ℕ) (f : ℤ_[p][X]) :
    reduction p Ω n (aeval (integralRoot p Ω n - 1) f) = PadicInt.toZMod (f.coeff 0) := by
  rw [← integralPowerBasis_gen]
  simp [reduction, -integralPowerBasis_gen, ← coeff_zero_eq_aeval_zero',
    RingHom.algebraMap_toAlgebra (PadicInt.toZMod (p := p))]

/-- Scalar compatibility and the chosen root characterize cyclotomic reduction. -/
theorem reduction_unique (n : ℕ)
    (f : integralClosure ℤ_[p] (padicCyclotomicField p Ω n) →+* ZMod p)
    (hscalar : ∀ a : ℤ_[p], f (algebraMap ℤ_[p] _ a) = PadicInt.toZMod a)
    (hroot : f (integralRoot p Ω n) = 1) : f = reduction p Ω n := by
  let g : integralClosure ℤ_[p] (padicCyclotomicField p Ω n) →ₐ[ℤ_[p]] ZMod p :=
    { f with
      commutes' := fun a ↦ by
        rw [RingHom.algebraMap_toAlgebra (PadicInt.toZMod (p := p))]
        exact hscalar a }
  let g' : integralClosure ℤ_[p] (padicCyclotomicField p Ω n) →ₐ[ℤ_[p]] ZMod p :=
    { reduction p Ω n with
      commutes' := fun a ↦ by
        rw [RingHom.algebraMap_toAlgebra (PadicInt.toZMod (p := p))]
        exact reduction_algebraMap p Ω n a }
  have h := (integralPowerBasis p Ω n).algHom_ext (f := g) (g := g') (by
    simp [integralPowerBasis_gen, g, g', hroot])
  exact congrArg AlgHom.toRingHom h

/-- The kernel of reduction is the principal cyclotomic difference ideal. -/
theorem ker_reduction (n : ℕ) :
    RingHom.ker (reduction p Ω n) = Ideal.span {integralRoot p Ω n - 1} := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a, ha⟩ := (integralPowerBasis p Ω n).exists_gen_dvd_sub x
    rw [integralPowerBasis_gen] at ha
    have hzero : PadicInt.toZMod a = 0 := by
      have := map_dvd (reduction p Ω n) ha
      simpa [RingHom.mem_ker.mp hx] using this
    have hap := (PadicInt.toZMod_eq_zero_iff_dvd a).mp hzero
    have hscalar : integralRoot p Ω n - 1 ∣ algebraMap ℤ_[p] _ a :=
      (isPrimitiveRoot_integralRoot p Ω n).sub_one_dvd_natCast_of_prime_pow.trans
        (by simpa only [map_natCast] using _root_.map_dvd (algebraMap ℤ_[p] _) hap)
    exact Ideal.mem_span_singleton.mpr ((dvd_sub_left hscalar).mp ha)
  · exact Ideal.span_le.mpr (by simp)

/-- The quotient by the chosen root minus one is canonically isomorphic to `ZMod p`. -/
noncomputable def quotientSpanEquivZMod (n : ℕ) :
    (integralClosure ℤ_[p] (padicCyclotomicField p Ω n) ⧸
      Ideal.span {integralRoot p Ω n - 1}) ≃+* ZMod p :=
  (Ideal.quotEquivOfEq (ker_reduction p Ω n).symm).trans
    (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective (reduction p Ω n)))

/-- The quotient equivalence computes by cyclotomic reduction on representatives. -/
@[simp]
theorem quotientSpanEquivZMod_mk (n : ℕ)
    (x : integralClosure ℤ_[p] (padicCyclotomicField p Ω n)) :
    quotientSpanEquivZMod p Ω n (Ideal.Quotient.mk _ x) = reduction p Ω n x := by
  simp [quotientSpanEquivZMod]

/-- The inverse quotient equivalence recovers the class of a cyclotomic integer from its
reduction. -/
@[simp]
theorem quotientSpanEquivZMod_symm_reduction (n : ℕ)
    (x : integralClosure ℤ_[p] (padicCyclotomicField p Ω n)) :
    (quotientSpanEquivZMod p Ω n).symm (reduction p Ω n x) = Ideal.Quotient.mk _ x := by
  rw [← quotientSpanEquivZMod_mk p Ω n x, RingEquiv.symm_apply_apply]

/-- The canonical maximal ideal is generated by the chosen root minus one. -/
theorem maximalIdeal_eq_span_integralRoot_sub_one (n : ℕ) :
    maximalIdeal (integralClosure ℤ_[p] (padicCyclotomicField p Ω n)) =
      Ideal.span {integralRoot p Ω n - 1} :=
  (IsLocalRing.ker_eq_maximalIdeal (reduction p Ω n)
    (ZMod.ringHom_surjective _)).symm.trans (ker_reduction p Ω n)

/-- The cyclotomic difference is irreducible, hence a uniformizer of the algebraic DVR. -/
theorem irreducible_integralRoot_sub_one (n : ℕ) :
    Irreducible (integralRoot p Ω n - 1) :=
  IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _
    ((isPrimitiveRoot_integralRoot p Ω n).sub_one_ne_zero
      (one_lt_pow₀ (Fact.out : p.Prime).one_lt (by omega)))
    (maximalIdeal_eq_span_integralRoot_sub_one p Ω n)

/-- The canonical residue field is the specified copy of `ZMod p`. -/
noncomputable def residueFieldEquiv (n : ℕ) :
    ResidueField (integralClosure ℤ_[p] (padicCyclotomicField p Ω n)) ≃+* ZMod p :=
  (Ideal.quotEquivOfEq (maximalIdeal_eq_span_integralRoot_sub_one p Ω n)).trans
    (quotientSpanEquivZMod p Ω n)

/-- On canonical residues the residue-field equivalence is cyclotomic reduction. -/
@[simp]
theorem residueFieldEquiv_residue (n : ℕ)
    (x : integralClosure ℤ_[p] (padicCyclotomicField p Ω n)) :
    residueFieldEquiv p Ω n (residue _ x) = reduction p Ω n x := by
  rw [residue]
  exact (congrArg (quotientSpanEquivZMod p Ω n)
    (Ideal.quotEquivOfEq_mk (maximalIdeal_eq_span_integralRoot_sub_one p Ω n) x)).trans
      (quotientSpanEquivZMod_mk p Ω n x)

/-- The inverse equivalence recovers the canonical residue class from cyclotomic reduction. -/
@[simp]
theorem residueFieldEquiv_symm_reduction (n : ℕ)
    (x : integralClosure ℤ_[p] (padicCyclotomicField p Ω n)) :
    (residueFieldEquiv p Ω n).symm (reduction p Ω n x) = residue _ x := by
  rw [← residueFieldEquiv_residue p Ω n x, RingEquiv.symm_apply_apply]

/-- Compatibility with reduction uniquely determines the residue-field map. -/
theorem residueFieldEquiv_unique (n : ℕ)
    (f : ResidueField (integralClosure ℤ_[p] (padicCyclotomicField p Ω n)) →+* ZMod p)
    (h : f.comp (residue _) = reduction p Ω n) :
    f = (residueFieldEquiv p Ω n).toRingHom := by
  refine (RingHom.cancel_right residue_surjective).mp (h.trans ?_)
  ext x
  simp

/-- A cyclotomic integer is a unit exactly when its reduction is nonzero. -/
theorem isUnit_iff_reduction_ne_zero (n : ℕ)
    (x : integralClosure ℤ_[p] (padicCyclotomicField p Ω n)) :
    IsUnit x ↔ reduction p Ω n x ≠ 0 := by
  rw [← isUnit_iff_ne_zero, isUnit_map_iff]

/-- A polynomial in the cyclotomic difference is a unit exactly when its constant coefficient
is a unit in `ℤ_p`. This holds for polynomials of arbitrary degree. -/
theorem isUnit_aeval_integralRoot_sub_one_iff (n : ℕ) (f : ℤ_[p][X]) :
    IsUnit (aeval (integralRoot p Ω n - 1) f) ↔ IsUnit (f.coeff 0) := by
  rw [isUnit_iff_reduction_ne_zero, reduction_aeval, ← isUnit_iff_ne_zero, isUnit_map_iff]

/-- Every integral cyclotomic unit has a bounded polynomial representative with unit constant
coefficient. -/
theorem exists_polynomial_lift_unit (n : ℕ)
    (u : (integralClosure ℤ_[p] (padicCyclotomicField p Ω n))ˣ) :
    ∃ f : ℤ_[p][X], f.natDegree < p ^ n * (p - 1) ∧
      aeval (integralRoot p Ω n - 1) f = u ∧ IsUnit (f.coeff 0) := by
  obtain ⟨f, hdeg, hf⟩ := (integralPowerBasis p Ω n).exists_eq_aeval (u : _)
  rw [integralPowerBasis_gen] at hf
  refine ⟨f, by simpa using hdeg, hf.symm, ?_⟩
  exact (isUnit_aeval_integralRoot_sub_one_iff p Ω n f).mp (hf ▸ u.isUnit)

end TauCeti.padicCyclotomicField
