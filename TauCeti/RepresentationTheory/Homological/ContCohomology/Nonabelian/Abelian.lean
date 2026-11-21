/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Nonabelian.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.LowDegree
public import TauCeti.Topology.Algebra.GroupAction.TypeTags

/-!
# Abelian coefficients in continuous nonabelian cohomology

For an additive commutative topological group `M`, reading a continuous nonabelian cocycle
with coefficients in `Multiplicative M` additively identifies it with the existing continuous
cocycle group `ContCohomology.Z1 G M`. Gauge equivalence becomes equality modulo additive
coboundaries, giving `NonabelianH1.additiveEquiv` with target `ContCohomology.H1 G M`.
The neutral class corresponds to zero. In degree zero, the same change of notation identifies
the fixed subgroups.

The convention in `Cocycle.twist` is `a⁻¹ * c(g) * g • a`. Its additive form is
`c(g) + (g • a - a)`, so this twist adds the differential `ContCohomology.d0`.
These comparisons allow abelian cohomology to be used in nonabelian lifting problems.

## References

* J.-P. Serre, *Galois Cohomology*, Springer, 1997, I.5.1–I.5.2.
-/

public section

namespace TauCeti.NonabelianH1

open Multiplicative

section Cocycles

variable (G M : Type*) [Group G] [TopologicalSpace G] [AddCommGroup M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [DistribMulAction G M]

/-- Read a continuous multiplicative cocycle with abelian coefficients additively. -/
def Cocycle.additiveEquiv : Cocycle G (Multiplicative M) ≃ ContCohomology.Z1 G M where
  toFun c := ⟨fun g ↦ (c g).toAdd, ContCohomology.mem_Z1_iff.mpr
    ⟨continuous_toAdd.comp c.continuous, fun g h ↦ by
      simpa only [toAdd_mul, toAdd_smul, add_comm] using congrArg toAdd (c.apply_mul g h)⟩⟩
  invFun c :=
    { toFun := fun g ↦ ofAdd (c.val g)
      continuous_toFun := continuous_ofAdd.comp (ContCohomology.mem_Z1_iff.mp c.property).1
      map_mul' g h := by
        apply toAdd.injective
        simpa only [toAdd_ofAdd, toAdd_mul, toAdd_smul, add_comm] using
          (ContCohomology.mem_Z1_iff.mp c.property).2 g h }
  left_inv c := Cocycle.ext fun _ ↦ ofAdd_toAdd _
  right_inv c := Subtype.ext (funext fun _ ↦ toAdd_ofAdd _)

variable {G M}

@[simp]
theorem Cocycle.additiveEquiv_apply (c : Cocycle G (Multiplicative M)) (g : G) :
    (additiveEquiv G M c : G → M) g = (c g).toAdd :=
  (rfl)

@[simp]
theorem Cocycle.additiveEquiv_symm_apply (c : ContCohomology.Z1 G M) (g : G) :
    (additiveEquiv G M).symm c g = ofAdd (c.val g) :=
  (rfl)

@[simp]
theorem Cocycle.additiveEquiv_one :
    additiveEquiv G M (1 : Cocycle G (Multiplicative M)) = 0 :=
  Subtype.ext (funext fun _ ↦ toAdd_one)

/-- Gauge translation in multiplicative notation adds an additive coboundary. -/
theorem Cocycle.additiveEquiv_twist [ContinuousSMul G M]
    (c : Cocycle G (Multiplicative M)) (a : Multiplicative M) :
    (additiveEquiv G M (c.twist a) : G → M) =
      (additiveEquiv G M c : G → M) + ContCohomology.d0 G M a.toAdd := by
  ext g
  simp [ContCohomology.d0_apply, add_comm, add_left_comm, sub_eq_add_neg]

/-- The gauge relation is precisely equality of the additive cohomology classes. -/
theorem Cocycle.equiv_iff_H1pi_additiveEquiv_eq [ContinuousSMul G M]
    (c d : Cocycle G (Multiplicative M)) :
    c ≈ d ↔
      ContCohomology.H1pi G M (additiveEquiv G M c) =
        ContCohomology.H1pi G M (additiveEquiv G M d) := by
  simp only [ContCohomology.H1pi, QuotientAddGroup.mk'_apply]
  rw [equiv_iff_exists_twist_eq, ContCohomology.H1pi_eq_iff]
  constructor
  · rintro ⟨a, rfl⟩
    rw [additiveEquiv_twist, sub_add_cancel_left, ← map_neg]
    exact ContCohomology.d0_mem_B1 _
  · intro h
    obtain ⟨m, hm⟩ := ContCohomology.mem_B1_iff.mp h
    replace hm : ContCohomology.d0 G M m = _ :=
      funext fun g ↦ (ContCohomology.d0_apply m g).trans (hm g)
    refine ⟨ofAdd (-m), (additiveEquiv G M).injective (Subtype.ext ?_)⟩
    rw [additiveEquiv_twist, toAdd_ofAdd, map_neg, hm, neg_sub, add_sub_cancel]

variable (G M)

/-- Continuous nonabelian `H¹` with abelian coefficients is the existing additive continuous
`H¹`, as a pointed set with neutral element corresponding to zero. -/
def additiveEquiv [ContinuousSMul G M] :
    NonabelianH1 G (Multiplicative M) ≃ ContCohomology.H1 G M where
  toFun := lift (fun c ↦ ContCohomology.H1pi G M (Cocycle.additiveEquiv G M c))
    (fun c d h ↦ (c.equiv_iff_H1pi_additiveEquiv_eq d).mp h)
  invFun := Quotient.lift (fun c ↦ mk ((Cocycle.additiveEquiv G M).symm c)) fun c d h ↦ by
    apply mk_eq_mk_iff.mpr
    apply (Cocycle.equiv_iff_H1pi_additiveEquiv_eq _ _).mpr
    simp only [Equiv.apply_symm_apply]
    exact Quotient.sound h
  left_inv c := by
    induction c using induction_on with | mk c =>
    simp only [lift_mk, ContCohomology.H1pi, QuotientAddGroup.mk'_apply,
      Quotient.lift_mk, Equiv.symm_apply_apply]
  right_inv c := by
    induction c using QuotientAddGroup.induction_on with | H c =>
    simp only [ContCohomology.H1pi, QuotientAddGroup.mk'_apply,
      Quotient.lift_mk, lift_mk, Equiv.apply_symm_apply]

variable {G M}

@[simp]
theorem additiveEquiv_mk [ContinuousSMul G M] (c : Cocycle G (Multiplicative M)) :
    additiveEquiv G M (mk c) = ContCohomology.H1pi G M (Cocycle.additiveEquiv G M c) :=
  lift_mk _ _ c

@[simp]
theorem additiveEquiv_symm_coe [ContinuousSMul G M] (c : ContCohomology.Z1 G M) :
    (additiveEquiv G M).symm (c : ContCohomology.H1 G M) =
      mk ((Cocycle.additiveEquiv G M).symm c) :=
  (rfl)

@[simp]
theorem additiveEquiv_one [ContinuousSMul G M] :
    additiveEquiv G M (1 : NonabelianH1 G (Multiplicative M)) = 0 := by
  rw [one_def, additiveEquiv_mk, Cocycle.additiveEquiv_one, map_zero]

@[simp]
theorem additiveEquiv_symm_zero [ContinuousSMul G M] :
    (additiveEquiv G M).symm 0 = 1 :=
  (additiveEquiv G M).symm_apply_eq.mpr additiveEquiv_one.symm

end Cocycles

variable (G M : Type*) [Monoid G] [AddCommGroup M] [DistribMulAction G M]

/-- The multiplicative and additive invariant subgroups agree under the change of notation. -/
def fixedPointsAdditiveEquiv :
    FixedPoints.subgroup G (Multiplicative M) ≃* Multiplicative (ContCohomology.H0 G M) where
  toFun a := ofAdd ⟨a.val.toAdd, fun g ↦ congrArg toAdd (a.property g)⟩
  invFun a := ⟨ofAdd a.toAdd.val, fun g ↦ congrArg ofAdd (a.toAdd.property g)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp]
theorem fixedPointsAdditiveEquiv_apply (a : FixedPoints.subgroup G (Multiplicative M)) :
    (fixedPointsAdditiveEquiv G M a).toAdd.val = a.val.toAdd :=
  (rfl)

@[simp]
theorem fixedPointsAdditiveEquiv_symm_apply (a : Multiplicative (ContCohomology.H0 G M)) :
    ((fixedPointsAdditiveEquiv G M).symm a).val = ofAdd a.toAdd.val :=
  (rfl)

end TauCeti.NonabelianH1
