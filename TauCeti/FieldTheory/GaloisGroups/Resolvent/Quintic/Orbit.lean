/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisGroups.Resolvent.Quintic.Basic

/-!
# The six conjugates of the quintic Frobenius invariant

The orbit of Dummit's quintic invariant has six elements. Here they are represented by the
permutations of the last three variables that fix the first two. This explicit orbit makes the
universal resolvent a product of six named factors, useful for calculating its coefficients and
checking specializations.

## Main results

* `TauCeti.renameOrbit_quinticF20Invariant`: the six representatives give the entire orbit.
* `TauCeti.universalResolvent_quinticF20Invariant`: the resulting six-factor product.

## References

* D. S. Dummit, *Solving solvable quintics*, Mathematics of Computation **57** (1991), §2.
-/

public section

open Equiv Equiv.Perm Polynomial

namespace TauCeti

/-- Representatives of the six cosets of the stabilizer of Dummit's quintic invariant.
They permute the last three indices and fix the first two. -/
def quinticF20OrbitRepresentatives : Finset (Perm (Fin 5)) :=
  {1, swap 2 3, swap 3 4, swap 2 4, swap 2 3 * swap 3 4,
    swap 3 4 * swap 2 3}

noncomputable section

private def orbitTestPoint : Fin 5 → ℤ := ![1, 2, 4, 8, 16]

private theorem orbitTestValues :
    quinticF20OrbitRepresentatives.image
      (fun (σ : Perm (Fin 5)) => MvPolynomial.eval orbitTestPoint
        (MvPolynomial.rename (⇑σ) quinticF20Invariant)) =
      ({9424, 9088, 11488, 10312, 11944, 8752} : Finset ℤ) := by
  simp only [orbitTestPoint, rename_quinticF20Invariant, Fin.isValue, Fin.sum_univ_five,
    zero_add, zero_sub, Fin.reduceAdd, sub_self, Fin.reduceSub, map_add, map_mul, map_pow,
    MvPolynomial.eval_X, quinticF20OrbitRepresentatives, Finset.image_insert, coe_one, id_eq,
    Matrix.cons_val_zero, one_pow, Matrix.cons_val_one, Matrix.cons_val, Int.reduceMul,
    Int.reduceAdd, one_mul, Int.reducePow, mul_one, Equiv.swap_apply_def, Fin.reduceEq,
    ↓reduceIte, coe_mul, Function.comp_apply,
    Finset.image_singleton, ite_eq_left_iff]
  decide

/-- The six permutations of the last three indices give all conjugates of Dummit's quintic
invariant. In particular, none of their renamings coincide as integral polynomials. -/
theorem renameOrbit_quinticF20Invariant :
    MvPolynomial.renameOrbit quinticF20Invariant =
      quinticF20OrbitRepresentatives.image
        (fun (σ : Perm (Fin 5)) => MvPolynomial.rename (⇑σ) quinticF20Invariant) := by
  let S := quinticF20OrbitRepresentatives.image
    (fun (σ : Perm (Fin 5)) => MvPolynomial.rename (⇑σ) quinticF20Invariant)
  have hsub : S ⊆ MvPolynomial.renameOrbit quinticF20Invariant := by
    intro Ψ hΨ
    obtain ⟨σ, -, rfl⟩ := Finset.mem_image.mp hΨ
    exact (MvPolynomial.mem_renameOrbit _ _).mpr ⟨σ, rfl⟩
  have hcard : 6 ≤ S.card := by
    have hvalues : S.image (MvPolynomial.eval orbitTestPoint) =
        ({9424, 9088, 11488, 10312, 11944, 8752} : Finset ℤ) := by
      simpa only [S, Finset.image_image, Function.comp_def] using orbitTestValues
    calc
      6 = ({9424, 9088, 11488, 10312, 11944, 8752} : Finset ℤ).card := by decide
      _ = (S.image (MvPolynomial.eval orbitTestPoint)).card := congrArg Finset.card hvalues.symm
      _ ≤ S.card := Finset.card_image_le
  exact (Finset.eq_of_subset_of_card_le hsub
    (by rw [card_renameOrbit_quinticF20Invariant]; exact hcard)).symm

/-- The universal quintic Frobenius resolvent is the product of the six linear factors
indexed by the explicit orbit representatives. -/
theorem universalResolvent_quinticF20Invariant :
    MvPolynomial.universalResolvent quinticF20Invariant =
      ∏ σ ∈ quinticF20OrbitRepresentatives,
        (X - C (MvPolynomial.rename (⇑σ) quinticF20Invariant)) := by
  rw [MvPolynomial.universalResolvent_def, renameOrbit_quinticF20Invariant]
  exact Finset.prod_image (by
    intro σ hσ τ hτ h
    have hinj : quinticF20OrbitRepresentatives.card = 6 := by
      decide
    have himg : (quinticF20OrbitRepresentatives.image
        (fun (σ : Perm (Fin 5)) => MvPolynomial.rename (⇑σ) quinticF20Invariant)).card = 6 := by
      rw [← renameOrbit_quinticF20Invariant, card_renameOrbit_quinticF20Invariant]
    exact (Finset.card_image_iff.mp (by rw [himg, hinj])) hσ hτ h)

end

end TauCeti
