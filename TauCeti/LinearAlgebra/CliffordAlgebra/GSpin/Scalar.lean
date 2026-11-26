/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.GSpin.CliffordGroup
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Central scalars in the general spin group

Let `Q` be a quadratic form over a commutative ring `R`, in every characteristic. This file shows
that a unit `c` of `R`, viewed as a central scalar, lies in the general spin group `GSpin(Q)`
(`CliffordAlgebra.specialCliffordGroup`) with general spin norm `ν(c) = reverse(c) c = c²`. So the
scalars with `c² = 1` lie in `Spin(Q) = ker ν` (`CliffordAlgebra.normOneSpinGroup`), and when the
scalars embed in the Clifford algebra the scalars in `Spin(Q)` are exactly those with `c² = 1`. In
particular `Spin(Q)` contains `μ₂(R)` in every rank, unlike Mathlib's `spinGroup`, which is
trivial in rank `0`.

When the scalars embed in the Clifford algebra and every element of `GSpin(Q)` is a scalar (as in
ranks zero and one), `Spin(Q)` is exactly the group `μ₂(R)` of square roots of unity.

## Main declarations

* `CliffordAlgebra.scalarSpecialCliffordGroup`: the central scalars `Rˣ →* GSpin(Q)`.
* `CliffordAlgebra.specialCliffordGroupNorm_scalarSpecialCliffordGroup`: `ν(c) = c²`.
* `CliffordAlgebra.scalarSpecialCliffordGroup_injective`: the central scalars embed in `GSpin(Q)`
  when they embed in the Clifford algebra.
* `CliffordAlgebra.unitsMap_algebraMap_mem_normOneSpinGroup_iff`: a scalar lies in `Spin(Q)`
  exactly when its square is `1`, when the scalars embed.
* `CliffordAlgebra.normOneSpinGroup_eq_map_rootsOfUnity`: `Spin(Q) = μ₂` when the central scalars
  map bijectively onto `GSpin(Q)`.

## References

* B. Conrad, *Reductive group schemes*, Appendix C, §C.4, for the Clifford and spin groups of a
  quadratic space over a ring.
-/

public section

namespace CliffordAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {Q : QuadraticForm R M}

variable (Q) in
/-- A unit of the base ring, as a central scalar, lies in the general spin group. -/
theorem unitsMap_algebraMap_mem_specialCliffordGroup (c : Rˣ) :
    Units.map (algebraMap R (CliffordAlgebra Q) : R →* CliffordAlgebra Q) c ∈
      specialCliffordGroup Q := by
  have hconj (d : Rˣ) (m : M) :
      ((Units.map (algebraMap R (CliffordAlgebra Q) : R →* CliffordAlgebra Q) d :
          (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * ι Q m *
        ((Units.map (algebraMap R (CliffordAlgebra Q) : R →* CliffordAlgebra Q) d)⁻¹ :
          (CliffordAlgebra Q)ˣ) = ι Q m := by
    have hU : ((Units.map (algebraMap R (CliffordAlgebra Q) : R →* CliffordAlgebra Q) d :
        (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = algebraMap R _ d := by
      rw [Units.coe_map, MonoidHom.coe_ofClass]
    rw [hU, (Algebra.commute_algebraMap_left (d : R) (ι Q m)).eq, mul_assoc, ← hU,
      Units.mul_inv, mul_one]
  refine mem_specialCliffordGroup_iff_conj.mpr ⟨?_, fun m => ⟨m, (hconj c m).symm⟩,
    fun m => ⟨m, ?_⟩⟩
  · exact Subalgebra.algebraMap_mem _ _
  · have h := hconj c⁻¹ m
    rw [map_inv (Units.map (algebraMap R (CliffordAlgebra Q) : R →* CliffordAlgebra Q)) c,
      inv_inv] at h
    exact h.symm

variable (Q) in
/-- **The central scalars of the general spin group**, `Rˣ →* GSpin(Q)`. -/
noncomputable def scalarSpecialCliffordGroup : Rˣ →* specialCliffordGroup Q :=
  (Units.map (algebraMap R (CliffordAlgebra Q) : R →* CliffordAlgebra Q)).codRestrict _
    (unitsMap_algebraMap_mem_specialCliffordGroup Q)

/-- The central scalar `c` of the general spin group is `algebraMap R _ c`. -/
@[simp]
theorem coe_scalarSpecialCliffordGroup (c : Rˣ) :
    (((scalarSpecialCliffordGroup Q c : (CliffordAlgebra Q)ˣ)) : CliffordAlgebra Q) =
      algebraMap R _ c :=
  (rfl)

/-- The central scalars embed in the general spin group when they embed in the Clifford algebra
(for instance for free `M`, by `CliffordAlgebra.algebraMap_injective_of_free`). -/
theorem scalarSpecialCliffordGroup_injective
    (hinj : Function.Injective (algebraMap R (CliffordAlgebra Q))) :
    Function.Injective (scalarSpecialCliffordGroup Q) := fun a b h =>
  Units.ext <| hinj <| by
    rw [← coe_scalarSpecialCliffordGroup, ← coe_scalarSpecialCliffordGroup, h]

/-- **The general spin norm of a central scalar is its square**: `ν(c) = c²`. -/
theorem specialCliffordGroupNorm_scalarSpecialCliffordGroup (c : Rˣ) :
    (((specialCliffordGroupNorm Q (scalarSpecialCliffordGroup Q c) : (CliffordAlgebra Q)ˣ)) :
        CliffordAlgebra Q) = algebraMap R _ ((c : R) ^ 2) := by
  rw [coe_specialCliffordGroupNorm, coe_scalarSpecialCliffordGroup, reverse.commutes, ← map_mul,
    ← pow_two]

/-- A central scalar whose square is `1` lies in `Spin(Q)`. -/
theorem unitsMap_algebraMap_mem_normOneSpinGroup {c : Rˣ} (hc : (c : R) ^ 2 = 1) :
    Units.map (algebraMap R (CliffordAlgebra Q) : R →* CliffordAlgebra Q) c ∈
      normOneSpinGroup Q := by
  refine mem_normOneSpinGroup_iff.mpr ⟨unitsMap_algebraMap_mem_specialCliffordGroup Q c, ?_⟩
  have h := specialCliffordGroupNorm_scalarSpecialCliffordGroup (Q := Q) c
  rw [coe_specialCliffordGroupNorm, hc, map_one] at h
  exact h

/-- **The scalars in `Spin(Q)` are the square roots of unity**, when the scalars embed in the
Clifford algebra (for instance for free `M`, by `CliffordAlgebra.algebraMap_injective_of_free`).
In particular `Spin(Q)` contains `{±1}` in every rank. -/
theorem unitsMap_algebraMap_mem_normOneSpinGroup_iff
    (hinj : Function.Injective (algebraMap R (CliffordAlgebra Q))) (c : Rˣ) :
    Units.map (algebraMap R (CliffordAlgebra Q) : R →* CliffordAlgebra Q) c ∈
      normOneSpinGroup Q ↔ (c : R) ^ 2 = 1 := by
  refine ⟨fun h => hinj ?_, unitsMap_algebraMap_mem_normOneSpinGroup⟩
  have h2 := specialCliffordGroupNorm_scalarSpecialCliffordGroup (Q := Q) c
  rw [coe_specialCliffordGroupNorm] at h2
  rw [← h2, map_one]
  exact (mem_normOneSpinGroup_iff.mp h).2

/-- **`Spin(Q) = μ₂`** when the scalars embed in the Clifford algebra and every element of the
general spin group is a central scalar: `Spin(Q)` is the image of the square roots of unity. -/
theorem normOneSpinGroup_eq_map_rootsOfUnity
    (hinj : Function.Injective (algebraMap R (CliffordAlgebra Q)))
    (hsurj : Function.Surjective (scalarSpecialCliffordGroup Q)) :
    normOneSpinGroup Q =
      (rootsOfUnity 2 R).map (Units.map (algebraMap R (CliffordAlgebra Q) : R →* _)) := by
  ext x
  simp only [Subgroup.mem_map, mem_rootsOfUnity]
  constructor
  · intro hx
    obtain ⟨c, hc⟩ := hsurj ⟨x, (mem_normOneSpinGroup_iff.mp hx).1⟩
    have hcx : Units.map (algebraMap R (CliffordAlgebra Q) : R →* _) c = x := Units.ext <| by
      rw [Units.coe_map, MonoidHom.coe_ofClass, ← coe_scalarSpecialCliffordGroup, hc]
    refine ⟨c, Units.ext ?_, hcx⟩
    rw [← hcx] at hx
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact (unitsMap_algebraMap_mem_normOneSpinGroup_iff hinj c).mp hx
  · rintro ⟨c, hc, rfl⟩
    exact unitsMap_algebraMap_mem_normOneSpinGroup
      (by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one])

end CliffordAlgebra
