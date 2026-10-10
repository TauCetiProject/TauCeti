/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.OrthogonalGroup.Integral.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.BaseChange
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Projection
import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Proper
import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# Integral Spin subgroups

For a basis of a quadratic space over `ℚ_[p]`, the integral Spin subgroup consists of Spin
points whose orthogonal actions are integral in that basis, in both directions. It is the
preimage of `TauCeti.QuadraticMap.integralOrthogonalSubgroup`, not a condition on coordinates
of the Clifford element itself.

This subgroup is open in the canonical Clifford topology. For a nondegenerate form it is also
compact. Scalar extension sends every rational Spin point into this subgroup at almost every
prime. Thus these
subgroups supply a compact-open Spin reference family compatible with the integral orthogonal
family, without an additional integrality hypothesis on the rational Spin points.

Membership and transport statements do not require nondegeneracy. The construction includes
the zero-dimensional case, where Mathlib's Spin group is trivial.

The integral family lives in `TauCeti.CliffordAlgebra`; its ambient group and projection are
`spinGroup` and `CliffordAlgebra.spinToOrthogonal`.

## Main results

* `TauCeti.CliffordAlgebra.isOpen_integralSpinSubgroup` and
  `TauCeti.CliffordAlgebra.isCompact_integralSpinSubgroup` give the local topological properties.
* `TauCeti.CliffordAlgebra.mem_integralSpinSubgroup_spinGroupEquiv` transports the subgroup
  when the basis is transported along an isometry.
* `TauCeti.CliffordAlgebra.eventually_mem_integralSpinSubgroup` gives rational integrality.

The construction uses the existing integral orthogonal family. Compactness of its full preimage
follows from properness of the local Spin projection, via
`CliffordAlgebra.isCompact_preimage_spinToOrthogonal`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms* (1963), §101.
-/

public section

namespace TauCeti.CliffordAlgebra

open _root_.CliffordAlgebra TauCeti.QuadraticMap
open Module Filter
open scoped TensorProduct Topology

noncomputable section

variable {p : ℕ} [Fact p.Prime] {V ι : Type*}
  [AddCommGroup V] [Module ℚ_[p] V] [Fintype ι] [DecidableEq ι]
  (Q : QuadraticForm ℚ_[p] V) (b : Basis ι ℚ_[p] V)

/-- Spin points whose orthogonal actions and inverse actions are integral in the basis `b`.
This is the full preimage of the integral orthogonal subgroup under the Spin projection. -/
def integralSpinSubgroup : Subgroup (spinGroup Q) :=
  (integralOrthogonalSubgroup Q b).comap (spinToOrthogonal Q)

/-- Membership is integrality of the induced orthogonal action, in both directions. -/
@[simp]
theorem mem_integralSpinSubgroup_iff (s : spinGroup Q) :
    s ∈ integralSpinSubgroup Q b ↔ spinToOrthogonal Q s ∈ integralOrthogonalSubgroup Q b :=
  Iff.rfl

/-- Project an integral Spin point to its integral orthogonal action. -/
def integralSpinToOrthogonal : integralSpinSubgroup Q b →* integralOrthogonalSubgroup Q b :=
  (spinToOrthogonal Q).subgroupComap (integralOrthogonalSubgroup Q b)

/-- The integral projection agrees with the ambient Spin projection. -/
@[simp]
theorem coe_integralSpinToOrthogonal_apply (s : integralSpinSubgroup Q b) :
    (integralSpinToOrthogonal Q b s : orthogonalGroup Q) = spinToOrthogonal Q s :=
  (rfl)

/-- Transporting the quadratic space and the basis transports integral Spin membership. -/
@[simp↓]
theorem mem_integralSpinSubgroup_spinGroupEquiv
    {W : Type*} [AddCommGroup W] [Module ℚ_[p] W] {Q' : QuadraticForm ℚ_[p] W}
    (e : Q.IsometryEquiv Q') (s : spinGroup Q) :
    e.spinGroupEquiv s ∈ integralSpinSubgroup Q' (b.map e.toLinearEquiv) ↔
      s ∈ integralSpinSubgroup Q b := by
  rw [mem_integralSpinSubgroup_iff, spinToOrthogonal_spinGroupEquiv,
    mem_integralOrthogonalSubgroup_orthogonalGroupCongr, mem_integralSpinSubgroup_iff]

/-- The integral Spin subgroup is open for the canonical topology on the Spin group. -/
theorem isOpen_integralSpinSubgroup :
    IsOpen (integralSpinSubgroup Q b : Set (spinGroup Q)) := by
  let : FiniteDimensional ℚ_[p] V := Module.Finite.of_basis b
  exact (isOpen_integralOrthogonalSubgroup Q b).preimage (continuous_spinToOrthogonal Q)

/-- The integral Spin subgroup of a nondegenerate quadratic space is compact. -/
theorem isCompact_integralSpinSubgroup (hQ : Q.Nondegenerate) :
    IsCompact (integralSpinSubgroup Q b : Set (spinGroup Q)) := by
  let : FiniteDimensional ℚ_[p] V := Module.Finite.of_basis b
  exact isCompact_preimage_spinToOrthogonal Q hQ (isCompact_integralOrthogonalSubgroup Q b)

/-- In dimension zero the integral Spin subgroup is the whole, trivial Spin group. -/
@[simp]
theorem integralSpinSubgroup_eq_top [Subsingleton V] : integralSpinSubgroup Q b = ⊤ := by
  exact eq_top_iff.mpr fun s _ ↦ by
    rw [Subsingleton.elim s 1]
    exact (integralSpinSubgroup Q b).one_mem

section Rational

private noncomputable instance invertibleTwoRat : Invertible (2 : ℚ) :=
  invertibleOfNonzero two_ne_zero

variable {W : Type*} [AddCommGroup W] [Module ℚ W]
  (Q₀ : QuadraticForm ℚ W) (b₀ : Basis ι ℚ W)

/-- Every rational Spin point belongs to the integral Spin subgroups in a fixed rational basis
at almost every prime. -/
theorem eventually_mem_integralSpinSubgroup (s : spinGroup Q₀) :
    ∀ᶠ p : Nat.Primes in cofinite,
      let _ : Fact (p : ℕ).Prime := ⟨p.property⟩
      spinGroupBaseChange (A := ℚ_[p]) Q₀ s ∈
        integralSpinSubgroup (Q₀.baseChange ℚ_[p]) (b₀.baseChange ℚ_[p]) := by
  filter_upwards [eventually_mem_integralOrthogonalSubgroup Q₀ b₀ (spinToOrthogonal Q₀ s)]
    with p hp
  let : Fact (p : ℕ).Prime := ⟨p.property⟩
  have h := spinToOrthogonal_baseChange (A := ℚ_[p]) Q₀ s
  -- Identify the scalar-extended inverse of two with the local p-adic instance.
  rw [Subsingleton.elim
    ((Invertible.map (algebraMap ℚ ℚ_[p]) 2).copy 2 (map_ofNat _ _).symm)
    (inferInstance : Invertible (2 : ℚ_[p]))] at h
  simpa only [mem_integralSpinSubgroup_iff, h] using hp

end Rational
end

end TauCeti.CliffordAlgebra
