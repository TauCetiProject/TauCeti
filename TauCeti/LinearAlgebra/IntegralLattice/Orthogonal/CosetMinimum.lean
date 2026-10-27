/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Operations
public import Mathlib.Order.Bounds.Image

/-!
# Discriminant coset minima of orthogonal sums

Under the canonical identification `A_(L ⊥ M) ≃ A_L × A_M`, the norms in a discriminant
coset are exactly the sums of norms in its two component cosets. Consequently, attained
component minima add, and a vector attains their sum exactly when both components attain
their minima. Iterating this result combines shortest-coset calculations for root lattices
without losing attainment in the orthogonal sum.

No positivity, evenness, or nondegeneracy assumption is required: the statements apply
whenever the two specified component cosets have least norms.

The construction uses `discriminantGroupOrthogonalSumEquiv` and
`orthogonalSumDualCarrierEquiv` to keep the classes tied to the actual dual carriers.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*,
  Chapter 4, §6 and Chapter 16, §1.
-/

public section

namespace TauCeti.IntegralLattice

universe u v

variable {V : Type u} {W : Type v}
variable [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
variable (L : IntegralLattice V) (M : IntegralLattice W)

/-- The norms in a discriminant coset of an orthogonal sum are exactly the pairwise sums
of norms in its component cosets. -/
theorem setOf_form_self_orthogonalSum (a : L.DiscriminantGroup) (b : M.DiscriminantGroup) :
    {q : ℚ | ∃ x : (L.orthogonalSum M).dualCarrier,
      Submodule.Quotient.mk x = (L.discriminantGroupOrthogonalSumEquiv M).symm (a, b) ∧
        (L.orthogonalSum M).form x x = q} =
      Set.image2 (· + ·)
        {q : ℚ | ∃ x : L.dualCarrier, Submodule.Quotient.mk x = a ∧ L.form x x = q}
        {q : ℚ | ∃ y : M.dualCarrier, Submodule.Quotient.mk y = b ∧ M.form y y = q} := by
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hclass := congrArg (L.discriminantGroupOrthogonalSumEquiv M) hx
    rw [discriminantGroupOrthogonalSumEquiv_mk, LinearEquiv.apply_symm_apply] at hclass
    refine ⟨_, ⟨(L.orthogonalSumDualCarrierEquiv M x).1, congrArg Prod.fst hclass, rfl⟩,
      _, ⟨(L.orthogonalSumDualCarrierEquiv M x).2, congrArg Prod.snd hclass, rfl⟩, ?_⟩
    simp only [orthogonalSum_form, orthogonalSumForm_apply,
      orthogonalSumDualCarrierEquiv_apply]
  · rintro ⟨r, ⟨x, hx, rfl⟩, s, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨(L.orthogonalSumDualCarrierEquiv M).symm (x, y), ?_, ?_⟩
    · apply (L.discriminantGroupOrthogonalSumEquiv M).injective
      rw [discriminantGroupOrthogonalSumEquiv_mk, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply, hx, hy]
    · simp only [orthogonalSum_form, orthogonalSumForm_apply,
        coe_orthogonalSumDualCarrierEquiv_symm_apply]

/-- Attained least norms in two discriminant cosets add to the attained least norm of the
corresponding coset of the orthogonal sum. -/
theorem isLeast_form_self_orthogonalSum
    {a : L.DiscriminantGroup} {b : M.DiscriminantGroup} {r s : ℚ}
    (hL : IsLeast {q : ℚ | ∃ x : L.dualCarrier,
      Submodule.Quotient.mk x = a ∧ L.form x x = q} r)
    (hM : IsLeast {q : ℚ | ∃ y : M.dualCarrier,
      Submodule.Quotient.mk y = b ∧ M.form y y = q} s) :
    IsLeast {q : ℚ | ∃ x : (L.orthogonalSum M).dualCarrier,
      Submodule.Quotient.mk x = (L.discriminantGroupOrthogonalSumEquiv M).symm (a, b) ∧
        (L.orthogonalSum M).form x x = q} (r + s) := by
  rw [setOf_form_self_orthogonalSum]
  exact hL.image2 (fun _ ↦ monotone_id.add_const _) (fun _ ↦ monotone_const.add monotone_id) hM

/-- A vector in a fixed discriminant coset attains the sum of component lower bounds
exactly when both components attain their respective bounds. -/
theorem form_self_orthogonalSum_eq_add_iff
    {a : L.DiscriminantGroup} {b : M.DiscriminantGroup} {r s : ℚ}
    (hL : r ∈ lowerBounds {q : ℚ | ∃ x : L.dualCarrier,
      Submodule.Quotient.mk x = a ∧ L.form x x = q})
    (hM : s ∈ lowerBounds {q : ℚ | ∃ y : M.dualCarrier,
      Submodule.Quotient.mk y = b ∧ M.form y y = q})
    (x : (L.orthogonalSum M).dualCarrier)
    (hx : Submodule.Quotient.mk x = (L.discriminantGroupOrthogonalSumEquiv M).symm (a, b)) :
    (L.orthogonalSum M).form x x = r + s ↔
      L.form (L.orthogonalSumDualCarrierEquiv M x).1
          (L.orthogonalSumDualCarrierEquiv M x).1 = r ∧
        M.form (L.orthogonalSumDualCarrierEquiv M x).2
          (L.orthogonalSumDualCarrierEquiv M x).2 = s := by
  have hclass := congrArg (L.discriminantGroupOrthogonalSumEquiv M) hx
  rw [discriminantGroupOrthogonalSumEquiv_mk, LinearEquiv.apply_symm_apply] at hclass
  have h₁ := hL ⟨(L.orthogonalSumDualCarrierEquiv M x).1,
    congrArg Prod.fst hclass, rfl⟩
  have h₂ := hM ⟨(L.orthogonalSumDualCarrierEquiv M x).2,
    congrArg Prod.snd hclass, rfl⟩
  simp only [orthogonalSum_form, orthogonalSumForm_apply,
    orthogonalSumDualCarrierEquiv_apply] at *
  constructor
  · intro h
    constructor <;> linarith
  · rintro ⟨h₁, h₂⟩
    rw [h₁, h₂]

end TauCeti.IntegralLattice
