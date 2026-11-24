/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.IntegralLattice.Localization.Stabilizer
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Subgroup
import TauCeti.NumberTheory.QuadraticForm.OrthogonalGroup.Integral.Reflection

/-!
# The index of the proper local stabilizer

The proper local stabilizer is the determinant-one part of `K_p(L)`. Its index in
`K_p(L)` divides two, and is two exactly when `K_p(L)` contains an isometry of determinant
minus one. The statements use `Subgroup.relIndex`: the relative index of `SO(V_p)` in
`K_p(L)` is, by definition, the index of their intersection in `K_p(L)`.

Nondegeneracy is needed to ensure that every orthogonal determinant is `±1`. No parity,
positive rank or odd-prime hypothesis is imposed, so the criterion also applies at two
and on the zero space. It distinguishes full from proper stabilizers without assuming
that an improper isometry exists.

Such an isometry does exist as soon as the form of `L` is nonzero, at every prime, `p = 2`
included: in a basis of `L`, the local stabilizer is an integral orthogonal subgroup, which
contains the reflection in a vector of `L_p` whose norm has the largest absolute value among the
norms of `e i` and `e i + e j` for a basis `e` of `L`
(`TauCeti.QuadraticMap.exists_mem_integralOrthogonalSubgroup_orthogonalDet_eq_neg_one`). So for
a nondegenerate lattice the index is two in positive rank. In rank zero it is one, since the
only isometry of the zero space is the identity.

## Main results

* `TauCeti.IntegralLattice.relIndex_localStabilizer_eq_two_iff`: the index is two exactly when
  `K_p(L)` contains an isometry of determinant `-1`.
* `TauCeti.IntegralLattice.exists_mem_localStabilizer_orthogonalDet_eq_neg_one`: if the form of
  `L` is nonzero, `K_p(L)` contains an isometry of determinant `-1`.
* `TauCeti.IntegralLattice.relIndex_localStabilizer_eq_two`: in positive rank the index is two.
* `TauCeti.IntegralLattice.relIndex_localStabilizer_eq_one`: in rank zero the index is one.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §82E for the norm ideal and §102A.
-/

public section

open TauCeti.QuadraticMap QuadraticMap
open scoped TensorProduct

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
  (L : IntegralLattice V) (p : ℕ) [Fact p.Prime]

/-- **An improper element of the local stabilizer.** If the form of `L` is nonzero, then at every
prime `p`, `p = 2` included, `K_p(L)` contains an isometry of determinant `-1`, namely the
reflection in a suitable vector of `L_p`. -/
theorem exists_mem_localStabilizer_orthogonalDet_eq_neg_one (h : L.form ≠ 0) :
    ∃ g ∈ L.localStabilizer p, orthogonalDet (L.norm.baseChange ℚ_[p]) g = -1 := by
  classical
  obtain ⟨x, hx⟩ := LinearMap.BilinForm.exists_bilinForm_self_ne_zero h
    (LinearMap.BilinForm.isSymm_iff.mp L.isSymm)
  have hQ : L.norm.baseChange ℚ_[p] ≠ 0 := fun h0 ↦ hx <| by
    simpa [norm_apply] using congrArg (fun Q ↦ Q ((1 : ℚ_[p]) ⊗ₜ x)) h0
  rw [L.localStabilizer_eq_integralOrthogonalSubgroup p (Module.Free.chooseBasis ℤ L)]
  exact exists_mem_integralOrthogonalSubgroup_orthogonalDet_eq_neg_one hQ

/-- **In rank zero the proper local stabilizer is everything**: its index in `K_p(L)` is one, as
the only isometry of the zero space is the identity. -/
theorem relIndex_localStabilizer_eq_one (hn : Module.finrank ℤ L = 0) :
    (specialOrthogonalWithin (L.norm.baseChange ℚ_[p])).relIndex (L.localStabilizer p) = 1 := by
  have := L.finiteDimensional
  have hV : Module.finrank ℚ_[p] (ℚ_[p] ⊗[ℚ] V) = 0 := by
    rw [Module.finrank_baseChange, ← L.finrank_carrier, hn]
  refine Subgroup.relIndex_eq_one.mpr fun g _ ↦ ?_
  rw [mem_specialOrthogonalWithin_iff]
  exact Units.ext ((LinearEquiv.coe_det _).trans (LinearMap.det_eq_one_of_finrank_eq_zero hV _))

variable [L.IsNondegenerate]

/-- The proper local stabilizer has index dividing two in the full local stabilizer. -/
theorem relIndex_localStabilizer_dvd_two :
    (specialOrthogonalWithin (L.norm.baseChange ℚ_[p])).relIndex (L.localStabilizer p) ∣ 2 := by
  have := L.finiteDimensional
  have hQ := QuadraticForm.Nondegenerate.baseChange (A := ℚ_[p]) L.nondegenerate_norm
  exact (L.localStabilizer p).relIndex_specialOrthogonalWithin_dvd_two
    (nondegenerate_polar_iff.mpr hQ).1

/-- The proper local stabilizer has index two exactly when the full local stabilizer
contains an isometry of determinant minus one. -/
theorem relIndex_localStabilizer_eq_two_iff :
    (specialOrthogonalWithin (L.norm.baseChange ℚ_[p])).relIndex (L.localStabilizer p) = 2 ↔
      ∃ g ∈ L.localStabilizer p, orthogonalDet (L.norm.baseChange ℚ_[p]) g = -1 := by
  have := L.finiteDimensional
  have hQ := QuadraticForm.Nondegenerate.baseChange (A := ℚ_[p]) L.nondegenerate_norm
  exact (L.localStabilizer p).relIndex_specialOrthogonalWithin_eq_two_iff
    (nondegenerate_polar_iff.mpr hQ).1

/-- **The proper local stabilizer has index two in positive rank**, at every prime `p`,
`p = 2` included. -/
theorem relIndex_localStabilizer_eq_two (hn : 0 < Module.finrank ℤ L) :
    (specialOrthogonalWithin (L.norm.baseChange ℚ_[p])).relIndex (L.localStabilizer p) = 2 := by
  have := L.finiteDimensional
  have : Nontrivial V := Module.finrank_pos_iff.mp (L.finrank_carrier ▸ hn)
  exact (L.relIndex_localStabilizer_eq_two_iff p).mpr
    (L.exists_mem_localStabilizer_orthogonalDet_eq_neg_one p L.form_nondegenerate.ne_zero)

end TauCeti.IntegralLattice
