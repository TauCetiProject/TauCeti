/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Operations
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Pi
public import Mathlib.Order.Bounds.Image

/-!
# Discriminant coset minima of orthogonal sums

Under the canonical identification `A_(L ⊥ M) ≃ A_L × A_M`, the norms in a discriminant
coset are exactly the sums of norms in its two component cosets. Consequently, attained
component minima add, and a vector attains their sum exactly when both components attain
their minima. Iterating this result combines shortest-coset calculations for root lattices
without losing attainment in the orthogonal sum.

The same holds for the orthogonal sum `⊥ i, L i` of a finite family: under
`A_(⊥ i, L i) ≃ Π i, A_(L i)`, attained least norms `r i` of the component cosets sum to the
attained least norm `∑ i, r i` of the coset of the orthogonal sum, and a vector of that coset
attains `∑ i, r i` exactly when each of its coordinates attains `r i`.  This is the form in which
the shortest norm of a glue word is the sum of the shortest norms of its labels.

No positivity, evenness, or nondegeneracy assumption is required: the statements apply
whenever the specified component cosets have least norms.

The construction uses `discriminantGroupOrthogonalSumEquiv` and
`orthogonalSumDualCarrierEquiv`, respectively `discriminantGroupPiEquiv` and `piDualCarrierEquiv`,
to keep the classes tied to the actual dual carriers.

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

/-! ## Finite families -/

section Pi

variable {ι : Type v} [Fintype ι] {U : ι → Type u} [∀ i, AddCommGroup (U i)]
  [∀ i, Module ℚ (U i)] (N : ∀ i, IntegralLattice (U i))

/-- Attained least norms `r i` in the discriminant cosets `a i` of a finite family of lattices
sum to the attained least norm of the corresponding coset of the orthogonal sum `⊥ i, N i`. -/
theorem isLeast_form_self_pi {a : ∀ i, (N i).DiscriminantGroup} {r : ι → ℚ}
    (h : ∀ i, IsLeast {q : ℚ | ∃ x : (N i).dualCarrier,
      Submodule.Quotient.mk x = a i ∧ (N i).form x x = q} (r i)) :
    IsLeast {q : ℚ | ∃ x : (pi N).dualCarrier,
      Submodule.Quotient.mk x = (discriminantGroupPiEquiv N).symm a ∧
        (pi N).form x x = q} (∑ i, r i) := by
  constructor
  · choose x hx hxr using fun i ↦ (h i).1
    refine ⟨(piDualCarrierEquiv N).symm x, ?_, ?_⟩
    · rw [← discriminantGroupPiEquiv_symm_mk, funext hx]
    · simp only [pi_form, piForm_apply, coe_piDualCarrierEquiv_symm_apply, hxr]
  · rintro q ⟨x, hx, rfl⟩
    have hclass := congrArg (discriminantGroupPiEquiv N) hx
    rw [discriminantGroupPiEquiv_mk, LinearEquiv.apply_symm_apply] at hclass
    rw [pi_form, piForm_apply]
    exact Finset.sum_le_sum fun i _ ↦ (h i).2
      ⟨piDualCarrierEquiv N x i, congrFun hclass i, by rw [coe_piDualCarrierEquiv_apply]⟩

/-- A vector in a fixed discriminant coset of the orthogonal sum `⊥ i, N i` attains the sum of
component lower bounds exactly when each of its coordinates attains its bound. -/
theorem form_self_pi_eq_sum_iff {a : ∀ i, (N i).DiscriminantGroup} {r : ι → ℚ}
    (h : ∀ i, r i ∈ lowerBounds {q : ℚ | ∃ x : (N i).dualCarrier,
      Submodule.Quotient.mk x = a i ∧ (N i).form x x = q})
    (x : (pi N).dualCarrier)
    (hx : Submodule.Quotient.mk x = (discriminantGroupPiEquiv N).symm a) :
    (pi N).form x x = ∑ i, r i ↔
      ∀ i, (N i).form (piDualCarrierEquiv N x i) (piDualCarrierEquiv N x i) = r i := by
  have hclass := congrArg (discriminantGroupPiEquiv N) hx
  rw [discriminantGroupPiEquiv_mk, LinearEquiv.apply_symm_apply] at hclass
  have hle : ∀ i ∈ Finset.univ,
      r i ≤ (N i).form (piDualCarrierEquiv N x i) (piDualCarrierEquiv N x i) :=
    fun i _ ↦ h i ⟨_, congrFun hclass i, rfl⟩
  have hcoord : ∀ i ∈ Finset.univ, (N i).form ((x : ∀ i, U i) i) ((x : ∀ i, U i) i) =
      (N i).form (piDualCarrierEquiv N x i) (piDualCarrierEquiv N x i) := fun i _ ↦ by
    rw [coe_piDualCarrierEquiv_apply]
  rw [pi_form, piForm_apply, Finset.sum_congr rfl hcoord, eq_comm,
    Finset.sum_eq_sum_iff_of_le hle]
  simp only [Finset.mem_univ, true_imp_iff, eq_comm]

end Pi

end TauCeti.IntegralLattice
