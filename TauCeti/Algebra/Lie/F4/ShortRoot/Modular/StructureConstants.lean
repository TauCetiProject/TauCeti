/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Modular.Bracket

/-!
# Coordinates of the short-root F₄ bracket in characteristic two

The bracket tensor of the twenty-six-dimensional short-root ideal is defined through the
abstract Chevalley lattice. This file computes its entries from the integral root and coroot
tables. For two nonopposite short roots, a short-root sum has coefficient one; all other
coordinates vanish. Opposite roots give the two short-simple-coroot coordinates. The remaining
entries are the Cartan integers and zero brackets between Cartan vectors.

These formulas retain integral weight labels even though their coefficients lie in `𝔽₂`.
They make the bracket equations available for explicit calculations of derivations and root
spaces, without unfolding the rational Lie algebra or choosing Chevalley signs.

## Main declarations

* `f4ShortRootBracketCoeff`: computable coefficients in the root--Cartan labels.
* `f4ShortRootBracketMatrix_eq_coeff`: their agreement with the actual Lie bracket tensor.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §12.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VIII.

The calculation uses the bracket and weight-support results in
`TauCeti.Algebra.Lie.F4.ShortRoot.Modular.Bracket`.
-/

public section

namespace TauCeti.DynkinType

/-- The computable bracket coefficients on the twenty-four short-root labels and two
Cartan labels. The middle argument is the output coordinate in the weight table.
The body is exposed so that finite coefficient calculations can be checked by reduction. -/
@[expose] def f4ShortRootBracketCoeff :
    (F4ShortRootIndex ⊕ Fin 2) → Fin 26 → (F4ShortRootIndex ⊕ Fin 2) → ZMod 2
  | .inl α, i, .inl β =>
      if f4ShortRootWeight i = 0 then
        if f4Root β = -f4Root α then
          if i = 12 then (f4Coroot α 2 : ZMod 2)
          else if i = 13 then (f4Coroot α 3 : ZMod 2) else 0
        else 0
      else if f4ShortRootWeight i = f4Root β + f4Root α then 1 else 0
  | .inr k, i, .inl β =>
      if f4ShortRootWeight i = f4Root β then (f4Root β ⟨k + 2, by omega⟩ : ZMod 2) else 0
  | .inl α, i, .inr k =>
      if f4ShortRootWeight i = f4Root α then (f4Root α ⟨k + 2, by omega⟩ : ZMod 2) else 0
  | .inr _, _, .inr _ => 0

/-- Root--root coefficients are determined by the sum weight, with opposite roots
contributing the two short-simple-coroot coordinates. -/
@[simp]
theorem f4ShortRootBracketCoeff_root_root (α β : F4ShortRootIndex) (i : Fin 26) :
    f4ShortRootBracketCoeff (Sum.inl α) i (Sum.inl β) =
      if f4ShortRootWeight i = 0 then
        if f4Root β = -f4Root α then
          if i = 12 then (f4Coroot α 2 : ZMod 2)
          else if i = 13 then (f4Coroot α 3 : ZMod 2) else 0
        else 0
      else if f4ShortRootWeight i = f4Root β + f4Root α then 1 else 0 := (rfl)

/-- Cartan--root coefficients are the Cartan integer at the root's weight and zero
at all other weights. -/
@[simp]
theorem f4ShortRootBracketCoeff_cartan_root (k : Fin 2) (β : F4ShortRootIndex)
    (i : Fin 26) :
    f4ShortRootBracketCoeff (Sum.inr k) i (Sum.inl β) =
      if f4ShortRootWeight i = f4Root β then (f4Root β ⟨k + 2, by omega⟩ : ZMod 2)
      else 0 := (rfl)

/-- Root--Cartan coefficients have the same Cartan-integer formula in characteristic two. -/
@[simp]
theorem f4ShortRootBracketCoeff_root_cartan (α : F4ShortRootIndex) (k : Fin 2)
    (i : Fin 26) :
    f4ShortRootBracketCoeff (Sum.inl α) i (Sum.inr k) =
      if f4ShortRootWeight i = f4Root α then (f4Root α ⟨k + 2, by omega⟩ : ZMod 2)
      else 0 := (rfl)

/-- All Cartan--Cartan coefficients vanish. -/
@[simp]
theorem f4ShortRootBracketCoeff_cartan_cartan (k l : Fin 2) (i : Fin 26) :
    f4ShortRootBracketCoeff (Sum.inr k) i (Sum.inr l) = 0 := (rfl)

noncomputable section

private theorem coroot_coordinate (α : Fin 48) (i : Fin 26) :
    f4ModularChevalleyBasis.repr (f4ModularCoroot α) (f4ShortRootBasisCoordinate i) =
      if i = 12 then (f4Coroot α 2 : ZMod 2)
      else if i = 13 then (f4Coroot α 3 : ZMod 2) else 0 := by
  classical
  obtain ⟨b, rfl⟩ := f4ShortRootWeightIndexEquiv.symm.surjective i
  rcases b with β | k
  · rw [f4ShortRootBasisCoordinate_symm_inl,
      f4ModularChevalleyBasis_repr_coroot_inl]
    have h12 : f4ShortRootWeightIndexEquiv.symm (Sum.inl β) ≠ 12 := by
      intro h
      have := congrArg f4ShortRootWeightIndexEquiv h
      simp at this
    have h13 : f4ShortRootWeightIndexEquiv.symm (Sum.inl β) ≠ 13 := by
      intro h
      have := congrArg f4ShortRootWeightIndexEquiv h
      simp at this
    simp [h12, h13]
  · have hcoord (j : Fin F4.rank) :
        f4ModularChevalleyBasis.repr (f4ModularCoroot α)
          (Sum.inr ((F4.lieBasis valid_F4).baseSupportEquiv j)) =
            (f4Coroot α (Fin.cast rank_F4 j) : ZMod 2) := by
      have hsum := congrArg (fun x : f4ModularChevalleyLieAlgebra =>
        f4ModularChevalleyBasis.repr x
          (Sum.inr ((F4.lieBasis valid_F4).baseSupportEquiv j)))
        (f4ModularCoroot_eq_sum_simple α)
      simpa only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
        Finsupp.smul_apply, f4ModularSimpleCoroot_eq_basis, Module.Basis.repr_self,
        Finsupp.single_apply, Sum.inr.injEq, Equiv.apply_eq_iff_eq, smul_eq_mul,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using hsum
    simp only [f4ShortRootBasisCoordinate_symm_inr, hcoord]
    fin_cases k <;> simp

/-- The root--root entries of the bracket tensor. A nonzero output weight occurs exactly
when it is the sum of the two input roots. Opposite inputs instead give the coroot, whose
only possible coordinates in the short-root ideal are `12` and `13`. -/
private theorem f4ShortRootBracketMatrix_root_root (α β : F4ShortRootIndex) (i : Fin 26) :
    f4ShortRootBracketMatrix (f4ShortRootWeightIndexEquiv.symm (Sum.inl α)) i
        (f4ShortRootWeightIndexEquiv.symm (Sum.inl β)) =
      if f4ShortRootWeight i = 0 then
        if f4Root β = -f4Root α then
          if i = 12 then (f4Coroot α 2 : ZMod 2)
          else if i = 13 then (f4Coroot α 3 : ZMod 2) else 0
        else 0
      else if f4ShortRootWeight i = f4Root β + f4Root α then 1 else 0 := by
  classical
  -- The zero-weight output is the coroot case; away from it, weight support
  -- forces a root sum and the equal-length bracket formula gives coefficient one.
  by_cases hz : f4ShortRootWeight i = 0
  · rw [ite_eq_left hz]
    by_cases hopp : f4Root β = -f4Root α
    · rw [ite_eq_left hopp]
      have hβ : β.val = f4OppositeRootIndex α := by
        rw [f4OppositeRootIndex_eq_reflectionPerm]
        apply (f4SimplyConnectedRootDatum.root_eq_neg_iff (i := β.val) (j := α.val)).mp
        simpa only [f4SimplyConnectedRootDatum_root] using hopp
      rw [f4ShortRootBracketMatrix_apply,
        coe_f4ShortRootLieIdealBasis_symm_inl,
        coe_f4ShortRootLieIdealBasis_symm_inl, hβ,
        f4Modular_lie_rootVector_opposite, coroot_coordinate]
    · rw [ite_eq_right hopp]
      by_contra hne
      have h := f4ShortRootBracketMatrix_weight_support _ _ _ hne
      rw [f4ShortRootWeight_f4ShortRootWeightIndexEquiv_symm_inl,
        f4ShortRootWeight_f4ShortRootWeightIndexEquiv_symm_inl, hz] at h
      exact hopp (eq_neg_of_add_eq_zero_left h.symm)
  · rw [ite_eq_right hz]
    by_cases hadd : f4ShortRootWeight i = f4Root β + f4Root α
    · rw [ite_eq_left hadd]
      obtain ⟨γ, hγ, hi⟩ := (f4ShortRootWeight_ne_zero_iff_exists_shortRoot i).mp hz
      have hs : i = f4ShortRootWeightIndexEquiv.symm (Sum.inl ⟨γ, hγ⟩) := by
        exact f4ShortRootWeightIndexEquiv.eq_symm_apply.mpr
          ((f4ShortRootWeightIndexEquiv_apply_eq_inl_iff i ⟨γ, hγ⟩).mpr hi.symm)
      have hsum : f4SimplyConnectedRootDatum.root γ =
          f4SimplyConnectedRootDatum.root β + f4SimplyConnectedRootDatum.root α := by
        simpa only [f4SimplyConnectedRootDatum_root] using hi.trans hadd
      have hbr := f4Modular_lie_rootVector_of_add_of_length_eq α.val β.val γ
        (β.property.trans hγ.symm) hsum
      simp only [f4ShortRootBracketMatrix_apply,
        coe_f4ShortRootLieIdealBasis_symm_inl]
      rw [hbr]
      rw [hs, f4ShortRootBasisCoordinate_symm_inl]
      exact f4ModularChevalleyBasis_repr_rootVector_self γ
    · rw [ite_eq_right hadd]
      by_contra hne
      have h := f4ShortRootBracketMatrix_weight_support _ _ _ hne
      simp only [f4ShortRootWeight_f4ShortRootWeightIndexEquiv_symm_inl] at h
      exact hadd h

/-- Bracketing a short simple coroot with a short root multiplies that root coordinate
by its integral Cartan integer, reduced modulo two. -/
private theorem f4ShortRootBracketMatrix_cartan_root (k : Fin 2) (β : F4ShortRootIndex)
    (i : Fin 26) :
    f4ShortRootBracketMatrix (f4ShortRootWeightIndexEquiv.symm (Sum.inr k)) i
        (f4ShortRootWeightIndexEquiv.symm (Sum.inl β)) =
      if i = f4ShortRootWeightIndexEquiv.symm (Sum.inl β) then
        (f4Root β ⟨k + 2, by omega⟩ : ZMod 2) else 0 := by
  classical
  rw [f4ShortRootBracketMatrix_apply, coe_f4ShortRootLieIdealBasis_symm_inr,
    coe_f4ShortRootLieIdealBasis_symm_inl, f4Modular_lie_simpleCoroot_rootVector]
  simp only [map_smul, Finsupp.smul_apply]
  have hv := congrArg (fun x : f4ModularChevalleyLieAlgebra =>
    f4ModularChevalleyBasis.repr x (f4ShortRootBasisCoordinate i))
      (coe_f4ShortRootLieIdealBasis_symm_inl β)
  rw [← hv, ← f4ShortRootLieIdealBasis_repr_apply, Module.Basis.repr_self]
  rw [f4SimplyConnectedRootDatum_pairing, f4Coroot_castAdd, dotProduct_single_one]
  fin_cases k <;> simp [Finsupp.single_apply, eq_comm]

/-- In characteristic two the root--Cartan entries equal the Cartan--root entries. -/
private theorem f4ShortRootBracketMatrix_root_cartan (α : F4ShortRootIndex) (k : Fin 2)
    (i : Fin 26) :
    f4ShortRootBracketMatrix (f4ShortRootWeightIndexEquiv.symm (Sum.inl α)) i
        (f4ShortRootWeightIndexEquiv.symm (Sum.inr k)) =
      if i = f4ShortRootWeightIndexEquiv.symm (Sum.inl α) then
        (f4Root α ⟨k + 2, by omega⟩ : ZMod 2) else 0 := by
  have hsymm (a b : Fin 26) :
      f4ShortRootBracketMatrix a i b = f4ShortRootBracketMatrix b i a := by
    simp only [f4ShortRootBracketMatrix_apply]
    have h := lie_skew (f4ShortRootLieIdealBasis a : f4ModularChevalleyLieAlgebra)
      (f4ShortRootLieIdealBasis b : f4ModularChevalleyLieAlgebra)
    simpa only [map_neg, Finsupp.neg_apply, CharTwo.neg_eq] using
      congrArg (fun x : f4ModularChevalleyLieAlgebra =>
        f4ModularChevalleyBasis.repr x (f4ShortRootBasisCoordinate i)) h.symm
  exact (hsymm _ _).trans (f4ShortRootBracketMatrix_cartan_root k α i)

/-- The two zero-weight basis vectors commute. -/
private theorem f4ShortRootBracketMatrix_cartan_cartan (k l : Fin 2) (i : Fin 26) :
    f4ShortRootBracketMatrix (f4ShortRootWeightIndexEquiv.symm (Sum.inr k)) i
        (f4ShortRootWeightIndexEquiv.symm (Sum.inr l)) = 0 := by
  rw [f4ShortRootBracketMatrix_apply, coe_f4ShortRootLieIdealBasis_symm_inr,
    coe_f4ShortRootLieIdealBasis_symm_inr,
    f4Modular_lie_simpleCoroot_simpleCoroot_eq_zero, map_zero, Finsupp.zero_apply]

/-- The abstract bracket tensor is exactly the computable coefficient function after
reindexing its two inputs by the short-root and Cartan labels. -/
@[simp↓]
theorem f4ShortRootBracketMatrix_eq_coeff (a b : F4ShortRootIndex ⊕ Fin 2) (i : Fin 26) :
    f4ShortRootBracketMatrix (f4ShortRootWeightIndexEquiv.symm a) i
        (f4ShortRootWeightIndexEquiv.symm b) = f4ShortRootBracketCoeff a i b := by
  have heq (β : F4ShortRootIndex) :
      i = f4ShortRootWeightIndexEquiv.symm (Sum.inl β) ↔
        f4ShortRootWeight i = f4Root β :=
    f4ShortRootWeightIndexEquiv.eq_symm_apply.trans
      (f4ShortRootWeightIndexEquiv_apply_eq_inl_iff i β)
  rcases a with α | k <;> rcases b with β | l
  · exact f4ShortRootBracketMatrix_root_root α β i
  · simpa only [f4ShortRootBracketCoeff, heq] using
      f4ShortRootBracketMatrix_root_cartan α l i
  · simpa only [f4ShortRootBracketCoeff, heq] using
      f4ShortRootBracketMatrix_cartan_root k β i
  · exact f4ShortRootBracketMatrix_cartan_cartan k l i

end

end TauCeti.DynkinType
