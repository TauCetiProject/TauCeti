/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.LocallyConvex.LatticeGauge.Discrete
public import TauCeti.RingTheory.Huber.TateGauge.Basic

/-!
# Scalar normalisation of the Tate gauge

When the pseudo-uniformiser of an algebra is the image of a scalar `π`, the Tate gauge at
base `‖π‖⁻¹` is the normalised discrete lattice gauge. Consequently it is bounded between
the scalar lattice gauge and `‖π‖⁻¹` times that gauge. No discrete-valuation or completeness
assumption is required. These estimates supply bounded equivalence of the two gauges,
which is stronger than equality of their induced topologies.
-/

public section

open Set Pointwise

namespace TauCeti.Huber

section NormedField

variable {K A : Type*} [NormedField K] [CommRing A] [Algebra K A]
  {A₀ : Subring A} {π : Kˣ} {x : A}

/-- At the reciprocal scalar-norm base, the Tate gauge is the normalised discrete gauge. -/
theorem tateGauge_eq_discreteLatticeGauge :
    tateGauge A₀ (Units.map (algebraMap K A).toMonoidHom π) ‖(π : K)‖⁻¹ x =
      discreteLatticeGauge (A₀ : Set A) (π : K) x := by
  rw [tateGauge_def, discreteLatticeGauge_def]
  simp only [inv_zpow', zpow_neg, inv_inv]
  congr 2
  ext n
  simp only [mem_ofPred_eq, mem_smul_set_iff_inv_smul_mem₀ (zpow_ne_zero n π.ne_zero)]
  simp only [← map_zpow, ← map_inv, Units.coe_map, Units.val_inv_eq_inv_val,
    Units.val_zpow_eq_zpow_val, Algebra.smul_def]
  rfl

end NormedField

variable {K A : Type*} [NontriviallyNormedField K] [CommRing A] [Algebra K A]
  {A₀ : Subring A} {π : Kˣ}

/-- The scalar lattice gauge is bounded above by the normalised Tate gauge. -/
theorem latticeGauge_le_tateGauge (hb : Balanced K (A₀ : Set A))
    (hs : Absorbent K (A₀ : Set A)) (hπ : ‖(π : K)‖ < 1) (x : A) :
    latticeGauge K (A₀ : Set A) x ≤
      tateGauge A₀ (Units.map (algebraMap K A).toMonoidHom π) ‖(π : K)‖⁻¹ x := by
  rw [tateGauge_eq_discreteLatticeGauge]
  exact latticeGauge_le_discreteLatticeGauge hb hs (norm_pos_iff.2 π.ne_zero) hπ x

/-- The normalised Tate gauge loses at most one inverse scalar-norm factor. -/
theorem tateGauge_le_inv_mul_latticeGauge (hb : Balanced K (A₀ : Set A))
    (hs : Absorbent K (A₀ : Set A)) (hπ : ‖(π : K)‖ < 1) (x : A) :
    tateGauge A₀ (Units.map (algebraMap K A).toMonoidHom π) ‖(π : K)‖⁻¹ x ≤
      ‖(π : K)‖⁻¹ * latticeGauge K (A₀ : Set A) x := by
  rw [tateGauge_eq_discreteLatticeGauge]
  exact discreteLatticeGauge_le_inv_mul_latticeGauge hb hs (norm_pos_iff.2 π.ne_zero) hπ x

end TauCeti.Huber
