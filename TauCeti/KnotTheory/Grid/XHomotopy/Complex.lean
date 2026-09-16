/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import TauCeti.KnotTheory.Grid.Chain.Complex
public import TauCeti.KnotTheory.Grid.Diagram.Components
public import TauCeti.KnotTheory.Grid.XHomotopy.Annulus

/-!
# Multiplication by the grid variables is homotopic along a link component

Let `X_k` be the `X`-marking of column `k` of a grid diagram, and let `O_j` be the `O`-marking in
the row of `X_k`. In characteristic two, the `X`-marking homotopy `H_k` satisfies

`∂⁻ ∘ H_k + H_k ∘ ∂⁻ = V_k + V_j`

on the unblocked grid complex `GC⁻` (`unblockedDifferential_comp_XHomotopy_add_XHomotopy_comp`):
the off-diagonal matrix entries cancel in pairs and each diagonal entry is the sum of the weights
of the two thin annuli through `X_k`. Hence multiplication by `V_k` and multiplication by `V_j` are
chain homotopic (`unblockedComplexXHomotopy`), and so induce the same map on homology.

Walking from `O_j` along its row to `X_k` and then along column `k` to `O_k` is one step of the
component permutation, so `k = componentPerm j`. Consequently the multiplications by any two
variables belonging to the same link component are chain homotopic. For a knot grid there is a
single component, so all the variables `V_c` act identically on the homology of `GC⁻`
(`IsKnot.homologyMap_X_smul_eq`), which is what makes that homology a module over a
one-variable polynomial ring.

## Main definitions

* `TauCeti.GridDiagram.unblockedComplexXHomotopy`: the chain homotopy `H_k` from
  multiplication by `V_k` to multiplication by `V_j`.
* `TauCeti.GridDiagram.unblockedComplexComponentHomotopy`: the chain homotopy from
  multiplication by `V_{componentPerm c}` to multiplication by `V_c`.

## Main results

* `TauCeti.GridDiagram.sum_unblockedCoefficient_mul_XHomotopyCoefficient_add`: the matrix entries
  of `∂⁻ ∘ H_k + H_k ∘ ∂⁻`.
* `TauCeti.GridDiagram.unblockedDifferential_comp_XHomotopy_add_XHomotopy_comp`: the homotopy
  identity `∂⁻ ∘ H_k + H_k ∘ ∂⁻ = V_k + V_j`.
* `TauCeti.GridDiagram.IsKnot.nonempty_homotopy_X_smul` and
  `TauCeti.GridDiagram.IsKnot.homologyMap_X_smul_eq`: on a knot grid, the multiplications by any
  two variables are chain homotopic and agree on homology.

## References

This is Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Lemma 4.6.9 and its
consequence that the variables of one component act identically on unblocked grid homology.
-/

public section

open CategoryTheory

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

section Matrix

variable (R : Type*) [CommSemiring R] [CharP R 2]

/-- In characteristic two the matrix entries of `∂⁻ ∘ H_k + H_k ∘ ∂⁻` vanish off the diagonal
and equal `V_k + V_j` on it, where `O_j` is the `O`-marking in the row of `X_k`. -/
theorem sum_unblockedCoefficient_mul_XHomotopyCoefficient_add (k : Fin n) (x z : GridState n) :
    ∑ y : GridState n, (G.unblockedCoefficient R x y * G.XHomotopyCoefficient R k y z +
        G.XHomotopyCoefficient R k x y * G.unblockedCoefficient R y z) =
      if x = z then (MvPolynomial.X k + MvPolynomial.X (G.O.columnOfRow (G.X k)) :
        MvPolynomial (Fin n) R) else 0 := by
  rw [← sum_XHomotopyDecompositions]
  split_ifs with h
  · subst h
    rcases lt_or_ge 1 n with hn | hn
    · exact G.sum_XHomotopyDecompositions_self R hn k x
    · -- On a grid with at most one column there are no rectangles, and `V_k + V_k = 0`.
      have : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.mpr hn
      rw [Subsingleton.elim (G.O.columnOfRow (G.X k)) k, CharTwo.add_self_eq_zero]
      exact Finset.sum_eq_zero fun D _ => absurd (Subsingleton.elim _ _) D.first.left_ne_right
  · exact G.sum_XHomotopyDecompositions_eq_zero R k (Ne.symm h)

/-- The homotopy identity `∂⁻ ∘ H_k + H_k ∘ ∂⁻ = V_k + V_j` on the unblocked grid complex in
characteristic two, where `O_j` is the `O`-marking in the row of `X_k`. -/
theorem unblockedDifferential_comp_XHomotopy_add_XHomotopy_comp (k : Fin n) :
    G.unblockedDifferential R ∘ₗ G.XHomotopy R k + G.XHomotopy R k ∘ₗ G.unblockedDifferential R =
      (MvPolynomial.X k + MvPolynomial.X (G.O.columnOfRow (G.X k)) : MvPolynomial (Fin n) R) •
        LinearMap.id := by
  refine Finsupp.lhom_ext' fun x => LinearMap.ext_ring (Finsupp.ext fun z => ?_)
  have h₁ : G.unblockedDifferential R (G.XHomotopy R k (Finsupp.single x 1)) z =
      ∑ y : GridState n, G.XHomotopyCoefficient R k x y * G.unblockedCoefficient R y z := by
    rw [unblockedDifferential_apply_apply, Finsupp.sum_fintype _ _ fun _ => zero_mul _]
    simp
  have h₂ : G.XHomotopy R k (G.unblockedDifferential R (Finsupp.single x 1)) z =
      ∑ y : GridState n, G.unblockedCoefficient R x y * G.XHomotopyCoefficient R k y z := by
    rw [XHomotopy_apply_apply, Finsupp.sum_fintype _ _ fun _ => zero_mul _]
    simp
  simp only [LinearMap.add_apply, LinearMap.comp_apply, Finsupp.lsingle_apply,
    LinearMap.smul_apply, LinearMap.id_apply, Finsupp.add_apply, Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, h₁, h₂,
    ← G.sum_unblockedCoefficient_mul_XHomotopyCoefficient_add R k x z,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun y _ => add_comm _ _

end Matrix

/-! ### Chain homotopies -/

variable (R : Type*) [CommRing R] [CharP R 2]

/-- The `X`-marking homotopy `H_k` as a chain homotopy on the unblocked grid complex, from
multiplication by `V_k` to multiplication by `V_j`, where `O_j` is the `O`-marking in the row of
`X_k`. -/
noncomputable def unblockedComplexXHomotopy (k : Fin n) :
    Homotopy ((MvPolynomial.X k : MvPolynomial (Fin n) R) • 𝟙 (G.unblockedComplex R))
      ((MvPolynomial.X (G.O.columnOfRow (G.X k)) : MvPolynomial (Fin n) R) •
        𝟙 (G.unblockedComplex R)) where
  hom _ _ := eqToHom (G.unblockedComplex_X R ()) ≫ ModuleCat.ofHom (G.XHomotopy R k) ≫
    eqToHom (G.unblockedComplex_X R ()).symm
  zero i j h := absurd (Subsingleton.elim j i) h
  comm _ := by
    -- Transport the identity across the object equation `X () = GC⁻` of the one-object complex.
    have transport : ∀ {A B : ModuleCat (MvPolynomial (Fin n) R)} (e : A = B) (d h : B ⟶ B)
        (a b : MvPolynomial (Fin n) R), a • 𝟙 B = d ≫ h + h ≫ d + b • 𝟙 B →
        a • 𝟙 A = (eqToHom e ≫ d ≫ eqToHom e.symm) ≫ (eqToHom e ≫ h ≫ eqToHom e.symm) +
          (eqToHom e ≫ h ≫ eqToHom e.symm) ≫ (eqToHom e ≫ d ≫ eqToHom e.symm) + b • 𝟙 A := by
      intro A B e d h a b hB
      subst e
      simpa using hB
    rw [dNext_eq _ (rfl : (ComplexShape.refl Unit).Rel () ()),
      prevD_eq _ (rfl : (ComplexShape.refl Unit).Rel () ()), HomologicalComplex.smul_f_apply,
      HomologicalComplex.smul_f_apply, HomologicalComplex.id_f, unblockedComplex_d]
    refine transport _ _ _ _ _ (ModuleCat.hom_ext ?_)
    have hid := G.unblockedDifferential_comp_XHomotopy_add_XHomotopy_comp R k
    simp only [ModuleCat.hom_add, ModuleCat.hom_smul, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
      ModuleCat.hom_id]
    rw [add_comm (G.XHomotopy R k ∘ₗ _), hid, ← add_smul, add_assoc, CharTwo.add_self_eq_zero,
      add_zero]

/-- The chain homotopy from multiplication by `V_{componentPerm c}` to multiplication by `V_c`:
the two `O`-markings are consecutive on a link component. -/
noncomputable def unblockedComplexComponentHomotopy (c : Fin n) :
    Homotopy ((MvPolynomial.X (G.componentPerm c) : MvPolynomial (Fin n) R) •
        𝟙 (G.unblockedComplex R))
      ((MvPolynomial.X c : MvPolynomial (Fin n) R) • 𝟙 (G.unblockedComplex R)) :=
  (G.unblockedComplexXHomotopy R (G.componentPerm c)).trans
    (Homotopy.ofEq (by rw [columnOfRow_X_componentPerm]))

/-- On a knot grid, multiplication by any two variables is chain homotopic on the unblocked grid
complex. -/
theorem IsKnot.nonempty_homotopy_X_smul {G : GridDiagram n} (hG : G.IsKnot) (c c' : Fin n) :
    Nonempty (Homotopy ((MvPolynomial.X c : MvPolynomial (Fin n) R) • 𝟙 (G.unblockedComplex R))
      ((MvPolynomial.X c' : MvPolynomial (Fin n) R) • 𝟙 (G.unblockedComplex R))) := by
  have hcycle := (G.isKnot_iff_componentPerm_isCycle).mp hG
  obtain ⟨i, hi⟩ := hcycle.exists_pow_eq (G.componentPerm_apply_ne_self c)
    (G.componentPerm_apply_ne_self c')
  subst hi
  induction i with
  | zero => exact ⟨Homotopy.refl _⟩
  | succ i ih =>
    obtain ⟨h⟩ := ih
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact ⟨h.trans (G.unblockedComplexComponentHomotopy R _).symm⟩

/-- On a knot grid, all the variables `V_c` act identically on the homology of the unblocked grid
complex. -/
theorem IsKnot.homologyMap_X_smul_eq {G : GridDiagram n} (hG : G.IsKnot) (c c' : Fin n) :
    HomologicalComplex.homologyMap
        ((MvPolynomial.X c : MvPolynomial (Fin n) R) • 𝟙 (G.unblockedComplex R)) () =
      HomologicalComplex.homologyMap
        ((MvPolynomial.X c' : MvPolynomial (Fin n) R) • 𝟙 (G.unblockedComplex R)) () :=
  (hG.nonempty_homotopy_X_smul R c c').some.homologyMap_eq ()

end GridDiagram

end TauCeti
