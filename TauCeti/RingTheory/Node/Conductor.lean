/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Node.BranchSequence
public import TauCeti.RingTheory.Node.Jacobian.Locus
public import Mathlib.RingTheory.Conductor
import Mathlib.RingTheory.Ideal.Prod

/-!
# The conductor of a split node

For the branch inclusion `R[x,y]/(xy) → R[t] × R[t]`, the conductor in the branch algebra
is `(t) × (t)`. Its contraction to the node algebra is the Jacobian ideal `(x,y)`, and its
extension back to the branch algebra recovers the conductor. The branch algebra modulo the
conductor is `R × R`: the two copies record the two branch origins.

These identities supply the local conductor calculation for the normalization of nodal curves.
They hold over every commutative ring, including nonreduced rings. No assertion that the
branch algebra is a normalization over an arbitrary base is needed.

The conductor uses Mathlib's `conductor A 0` with the algebra structure induced by the
branch inclusion: adjoining zero to `A` gives precisely the image of `A`.

## References

* The Stacks Project, Section 53.19, *Nodal curves*, Tag 0C46.
-/

public section

noncomputable section

namespace TauCeti.NodeAlgebra

open Polynomial

variable (R : Type*) [CommRing R]

/-- The conductor of the branch inclusion, as an ideal of the branch algebra. -/
def branchConductor : Ideal (R[X] × R[X]) :=
  letI := (branchMap R).toRingHom.toAlgebra
  conductor (NodeAlgebra R 0) (0 : R[X] × R[X])

/-- A branch function belongs to the conductor precisely when every multiple descends to
the node. -/
theorem mem_branchConductor_iff (p : R[X] × R[X]) :
    p ∈ branchConductor R ↔ ∀ q : R[X] × R[X], p * q ∈ (branchMap R).range := by
  simp only [branchConductor, mem_conductor_iff, Algebra.adjoin_singleton_zero,
    Algebra.mem_bot, RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, AlgHom.mem_range, Set.mem_range]

/-- Conductor functions vanish at the origins of both branches. -/
@[simp]
theorem mem_branchConductor_iff_coeff_zero (p : R[X] × R[X]) :
    p ∈ branchConductor R ↔ p.1.coeff 0 = 0 ∧ p.2.coeff 0 = 0 := by
  rw [mem_branchConductor_iff]
  constructor
  · intro h
    have h₁ := (mem_range_branchMap_iff R _).mp (h (1, 0))
    have h₂ := (mem_range_branchMap_iff R _).mp (h (0, 1))
    simpa using And.intro h₁ h₂.symm
  · rintro ⟨h₁, h₂⟩ q
    exact (mem_range_branchMap_iff R _).mpr (by simp [mul_coeff_zero, h₁, h₂])

/-- The conductor in the branch algebra is the product of the ideals of the two origins. -/
theorem branchConductor_eq_prod :
    branchConductor R = (Ideal.span {(X : R[X])}).prod (Ideal.span {(X : R[X])}) := by
  ext p
  simp [Ideal.mem_prod, Ideal.mem_span_singleton, X_dvd_iff]

/-- Evaluation at the two branch origins. -/
def branchValues : (R[X] × R[X]) →ₐ[R] R × R :=
  (aeval (0 : R)).prodMap (aeval (0 : R))

/-- The branch values are the constant coefficients, equivalently the values at the two
branch origins. -/
@[simp]
theorem branchValues_apply (p : R[X] × R[X]) :
    branchValues R p = (p.1.coeff 0, p.2.coeff 0) := by
  simp [branchValues, AlgHom.prodMap, RingHom.prodMap, ← coeff_zero_eq_eval_zero]

/-- The two branch values may be chosen independently. -/
theorem branchValues_surjective : Function.Surjective (branchValues R) :=
  fun r ↦ ⟨(C r.1, C r.2), by simp⟩

/-- The conductor cuts out the two branch origins scheme-theoretically. -/
theorem branchConductor_eq_ker_branchValues :
    branchConductor R = RingHom.ker (branchValues R) := by
  ext p
  simp [RingHom.mem_ker, Prod.ext_iff]

/-- The branch algebra modulo the conductor is two copies of the base ring. -/
def branchConductorQuotientEquiv :
    ((R[X] × R[X]) ⧸ branchConductor R) ≃ₐ[R] R × R :=
  (Ideal.quotientEquivAlgOfEq R (branchConductor_eq_ker_branchValues R)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (branchValues_surjective R))

/-- The quotient comparison records the values at the two origins. -/
@[simp]
theorem branchConductorQuotientEquiv_mk (p : R[X] × R[X]) :
    branchConductorQuotientEquiv R (Ideal.Quotient.mk _ p) =
      (p.1.coeff 0, p.2.coeff 0) := by
  simp [branchConductorQuotientEquiv]

/-- The inverse comparison represents the two values by constant branch functions. -/
@[simp]
theorem branchConductorQuotientEquiv_symm_apply (r : R × R) :
    (branchConductorQuotientEquiv R).symm r = Ideal.Quotient.mk _ (C r.1, C r.2) := by
  apply (branchConductorQuotientEquiv R).injective
  simp

/-- Extending the Jacobian ideal to the branch algebra gives the conductor. -/
theorem map_jacobianIdeal_eq_branchConductor :
    (jacobianIdeal (0 : R)).map (branchMap R).toRingHom = branchConductor R := by
  rw [jacobianIdeal_def, Ideal.map_span]
  simp only [Set.image_insert_eq, Set.image_singleton, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, branchMap_coord_zero, branchMap_coord_one]
  ext p
  rw [Ideal.mem_span_pair, mem_branchConductor_iff_coeff_zero]
  constructor
  · rintro ⟨a, b, rfl⟩
    simp [mul_coeff_zero]
  · rintro ⟨h₁, h₂⟩
    obtain ⟨a, ha⟩ := X_dvd_iff.mpr h₁
    obtain ⟨b, hb⟩ := X_dvd_iff.mpr h₂
    exact ⟨(a, 0), (0, b), by ext <;> simp [ha, hb, mul_comm]⟩

/-- Contracting the conductor to the node algebra gives its Jacobian ideal. -/
theorem comap_branchConductor_eq_jacobianIdeal :
    (branchConductor R).comap (branchMap R).toRingHom = jacobianIdeal (0 : R) := by
  apply le_antisymm ?_
    (map_jacobianIdeal_eq_branchConductor R ▸ Ideal.le_comap_map)
  intro z hz
  have hzero : ((branchMap R z).1).coeff 0 = 0 :=
    ((mem_branchConductor_iff_coeff_zero R _).mp hz).1
  -- Compare with the existing Jacobian quotient, rather than reconstructing its kernel.
  have hhom :
      (jacobianQuotientEquiv (0 : R)).toAlgHom.comp
          (Ideal.Quotient.mkₐ R (jacobianIdeal (0 : R))) =
        (Ideal.Quotient.mkₐ R (Ideal.span {(0 : R)})).comp
          ((aeval (0 : R)).comp ((AlgHom.fst R R[X] R[X]).comp (branchMap R))) := by
    ext <;> simp
  have hval : jacobianQuotientEquiv (0 : R)
      (Ideal.Quotient.mk (jacobianIdeal (0 : R)) z) = 0 := by
    simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, Ideal.Quotient.mkₐ_eq_mk,
      AlgHom.fst_apply, ← coeff_zero_eq_aeval_zero', hzero, map_zero]
      using AlgHom.congr_fun hhom z
  exact Ideal.Quotient.eq_zero_iff_mem.mp
    ((jacobianQuotientEquiv (0 : R)).injective (hval.trans (map_zero _).symm))

end TauCeti.NodeAlgebra
