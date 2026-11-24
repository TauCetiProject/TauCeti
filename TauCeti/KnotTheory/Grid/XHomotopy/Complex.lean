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
variables belonging to the same link component are chain homotopic
(`nonempty_homotopy_X_smul_of_pow_componentPerm_apply`) and act identically on the homology of
`GC⁻` (`homologyMap_X_smul_eq_of_pow_componentPerm_apply`). For a knot grid there is a single
component, so the action of `V_c` on the homology of `GC⁻` is independent of the choice of `c`
(`IsKnot.homologyMap_X_smul_eq`).

## Main definitions

* `TauCeti.GridDiagram.componentPathXHomotopy`: the `m`-step sum of `X`-marking homotopies
  walking along `componentPerm` from a column `c`.
* `TauCeti.GridDiagram.unblockedComplexXHomotopy`: the chain homotopy `H_k` from
  multiplication by `V_k` to multiplication by `V_j`.
* `TauCeti.GridDiagram.unblockedComplexComponentHomotopy`: the chain homotopy from
  multiplication by `V_{componentPerm c}` to multiplication by `V_c`.
* `TauCeti.GridDiagram.IsKnot.XSmulHomotopy`: on a knot grid, the sum
  `componentPathXHomotopy c (traversalIndex c c')` of `X`-marking homotopies along the knot from
  `c` to `c'`, which in characteristic two satisfies `∂⁻ H + H ∂⁻ = V_c + V_c'`.

## Main results

* `TauCeti.GridDiagram.sum_unblockedCoefficient_mul_XHomotopyCoefficient_add`: the matrix entries
  of `∂⁻ ∘ H_k + H_k ∘ ∂⁻`.
* `TauCeti.GridDiagram.unblockedDifferential_comp_XHomotopy_add_XHomotopy_comp` and
  `unblockedDifferential_comp_componentPathXHomotopy_add_componentPathXHomotopy_comp`:
  the homotopy identities for a single `X`-marking homotopy and an `m`-step path sum.
* `TauCeti.GridDiagram.IsKnot.unblockedDifferential_comp_XSmulHomotopy_add_XSmulHomotopy_comp`:
  on a knot grid, `∂⁻ H + H ∂⁻ = V_c + V_c'` for `H = hG.XSmulHomotopy R c c'`.
* `TauCeti.GridDiagram.IsKnot.unblockedDifferential_add_XSmulHomotopy_left` and
  `TauCeti.GridDiagram.IsKnot.unblockedDifferential_add_XSmulHomotopy_right`: if `∂⁻ x = V_c a`,
  then `∂⁻(x + H a) = V_c' a`, and symmetrically.
* `TauCeti.GridDiagram.nonempty_homotopy_X_smul_of_pow_componentPerm_apply` and
  `TauCeti.GridDiagram.homologyMap_X_smul_eq_of_pow_componentPerm_apply`: the multiplications by
  two variables on the same link component are chain homotopic and agree on homology.
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

section PathHomotopy

variable (R : Type*) [CommSemiring R]

/-- The `m`-step sum of `X`-marking homotopies walking along `componentPerm` from column `c`. In
characteristic two it provides a chain homotopy between multiplication by `V_c` and multiplication
by `V_{(componentPerm ^ m) c}`. -/
noncomputable def componentPathXHomotopy (c : Fin n) (m : ℕ) :
    GridChainMinus R n →ₗ[MvPolynomial (Fin n) R] GridChainMinus R n :=
  ∑ t ∈ Finset.range m, G.XHomotopy R ((G.componentPerm ^ (t + 1)) c)

/-- Walking zero steps along `componentPerm` gives the zero homotopy. -/
@[simp]
theorem componentPathXHomotopy_zero (c : Fin n) :
    G.componentPathXHomotopy R c 0 = 0 := by
  simp [componentPathXHomotopy]

/-- Walking `m + 1` steps adds the `X`-marking homotopy at `(componentPerm ^ (m + 1)) c`. -/
@[simp]
theorem componentPathXHomotopy_succ (c : Fin n) (m : ℕ) :
    G.componentPathXHomotopy R c (m + 1) =
      G.componentPathXHomotopy R c m + G.XHomotopy R ((G.componentPerm ^ (m + 1)) c) := by
  simp [componentPathXHomotopy, Finset.sum_range_succ]

/-- Evaluating `componentPathXHomotopy` on a chain sums the constituent `X`-marking homotopies. -/
theorem componentPathXHomotopy_apply (c : Fin n) (m : ℕ) (x : GridChainMinus R n) :
    G.componentPathXHomotopy R c m x =
      ∑ t ∈ Finset.range m, G.XHomotopy R ((G.componentPerm ^ (t + 1)) c) x := by
  simp [componentPathXHomotopy]

/-- On a knot grid, the sum `componentPathXHomotopy c (traversalIndex c c')` of `X`-marking
homotopies along the knot from `c` to `c'` (`IsKnot.XSmulHomotopy_eq_componentPathXHomotopy`). In
characteristic two it is a map `H` on `GC⁻` with `∂⁻ H + H ∂⁻ = V_c + V_c'`, a null-homotopy of
multiplication by `V_c + V_c'`
(`IsKnot.unblockedDifferential_comp_XSmulHomotopy_add_XSmulHomotopy_comp`). -/
noncomputable def IsKnot.XSmulHomotopy {G : GridDiagram n} (hG : G.IsKnot) (c c' : Fin n) :
    GridChainMinus R n →ₗ[MvPolynomial (Fin n) R] GridChainMinus R n :=
  G.componentPathXHomotopy R c (hG.traversalIndex c c')

/-- The null-homotopy `hG.XSmulHomotopy R c c'` is the sum of the `X`-marking homotopies along the
`traversalIndex c c'` steps of the knot from `c` to `c'`. -/
theorem IsKnot.XSmulHomotopy_eq_componentPathXHomotopy {G : GridDiagram n} (hG : G.IsKnot)
    (c c' : Fin n) :
    hG.XSmulHomotopy R c c' = G.componentPathXHomotopy R c (hG.traversalIndex c c') :=
  (rfl)

end PathHomotopy

section Matrix

variable (R : Type*) [CommSemiring R] [CharP R 2]

/-- In characteristic two the matrix entries of `∂⁻ ∘ H_k + H_k ∘ ∂⁻` vanish off the diagonal
and equal `V_k + V_j` on it, where `O_j` is the `O`-marking in the row of `X_k`. -/
theorem sum_unblockedCoefficient_mul_XHomotopyCoefficient_add (k : Fin n) (x z : GridState n) :
    ∑ y : GridState n, (G.unblockedCoefficient R x y * G.XHomotopyCoefficient R k y z +
        G.XHomotopyCoefficient R k x y * G.unblockedCoefficient R y z) =
      if x = z then (MvPolynomial.X k + MvPolynomial.X (G.O.transpose (G.X k)) :
        MvPolynomial (Fin n) R) else 0 := by
  rw [← sum_XHomotopyDecompositions]
  split_ifs with h
  · subst h
    rcases lt_or_ge 1 n with hn | hn
    · exact G.sum_XHomotopyDecompositions_self R hn k x
    · -- On a grid with at most one column there are no rectangles, and `V_k + V_k = 0`.
      have : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.mpr hn
      rw [Subsingleton.elim (G.O.transpose (G.X k)) k, CharTwo.add_self_eq_zero]
      exact Finset.sum_eq_zero fun D _ => absurd (Subsingleton.elim _ _) D.first.left_ne_right
  · exact G.sum_XHomotopyDecompositions_eq_zero R k (Ne.symm h)

/-- The homotopy identity `∂⁻ ∘ H_k + H_k ∘ ∂⁻ = V_k + V_j` on the unblocked grid complex in
characteristic two, where `O_j` is the `O`-marking in the row of `X_k`. -/
theorem unblockedDifferential_comp_XHomotopy_add_XHomotopy_comp (k : Fin n) :
    G.unblockedDifferential R ∘ₗ G.XHomotopy R k + G.XHomotopy R k ∘ₗ G.unblockedDifferential R =
      (MvPolynomial.X k + MvPolynomial.X (G.O.transpose (G.X k)) : MvPolynomial (Fin n) R) •
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

/-- In characteristic two, the `m`-step component-path `X`-homotopy satisfies
`∂⁻ ∘ H + H ∘ ∂⁻ = (V_c + V_{(componentPerm ^ m) c}) • id`. -/
theorem unblockedDifferential_comp_componentPathXHomotopy_add_componentPathXHomotopy_comp
    (c : Fin n) (m : ℕ) :
    G.unblockedDifferential R ∘ₗ G.componentPathXHomotopy R c m +
        G.componentPathXHomotopy R c m ∘ₗ G.unblockedDifferential R =
      (MvPolynomial.X c + MvPolynomial.X ((G.componentPerm ^ m) c) : MvPolynomial (Fin n) R) •
        LinearMap.id := by
  induction m with
  | zero => simp [CharTwo.add_self_eq_zero]
  | succ m ih =>
    have hk := G.unblockedDifferential_comp_XHomotopy_add_XHomotopy_comp R
      (G.componentPerm ((G.componentPerm ^ m) c))
    rw [O_transpose_X_componentPerm] at hk
    rw [componentPathXHomotopy_succ, pow_succ', Equiv.Perm.mul_apply, LinearMap.comp_add,
      LinearMap.add_comp, add_add_add_comm, ih, hk, ← add_smul]
    congr 1
    calc _ = (MvPolynomial.X ((G.componentPerm ^ m) c) + MvPolynomial.X ((G.componentPerm ^ m) c)) +
          (MvPolynomial.X c + MvPolynomial.X (G.componentPerm ((G.componentPerm ^ m) c))) := by
          abel
      _ = _ := by rw [CharTwo.add_self_eq_zero, zero_add]

/-- The homotopy identity `∂⁻ H + H ∂⁻ = V_c + V_c'` for `H = hG.XSmulHomotopy R c c'`. -/
theorem IsKnot.unblockedDifferential_comp_XSmulHomotopy_add_XSmulHomotopy_comp {G : GridDiagram n}
    (hG : G.IsKnot) (c c' : Fin n) :
    G.unblockedDifferential R ∘ₗ hG.XSmulHomotopy R c c' +
        hG.XSmulHomotopy R c c' ∘ₗ G.unblockedDifferential R =
      (MvPolynomial.X c + MvPolynomial.X c' : MvPolynomial (Fin n) R) • LinearMap.id := by
  rw [hG.XSmulHomotopy_eq_componentPathXHomotopy R]
  simpa only [hG.pow_traversalIndex_apply] using
    G.unblockedDifferential_comp_componentPathXHomotopy_add_componentPathXHomotopy_comp R c
      (hG.traversalIndex c c')

/-- On a cycle `a`, the `X`-marking homotopy `H = hG.XSmulHomotopy R c c'` has boundary
`∂⁻(H a) = (V_c + V_c') a`. -/
theorem IsKnot.unblockedDifferential_XSmulHomotopy_of_eq_zero {G : GridDiagram n}
    (hG : G.IsKnot) (c c' : Fin n) {a : GridChainMinus R n}
    (ha : G.unblockedDifferential R a = 0) :
    G.unblockedDifferential R (hG.XSmulHomotopy R c c' a) =
      (MvPolynomial.X c + MvPolynomial.X c' : MvPolynomial (Fin n) R) • a := by
  have h := congr($(hG.unblockedDifferential_comp_XSmulHomotopy_add_XSmulHomotopy_comp R c c') a)
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, ha, map_zero, add_zero,
    LinearMap.smul_apply, LinearMap.id_apply] using h

/-- If `∂⁻ x = V_c a`, then `∂⁻(x + H a) = V_c' a` for the `X`-marking homotopy
`H = hG.XSmulHomotopy R c c'` between the actions of `V_c` and `V_c'`. -/
theorem IsKnot.unblockedDifferential_add_XSmulHomotopy_left {G : GridDiagram n} (hG : G.IsKnot)
    (c c' : Fin n) (x a : GridChainMinus R n)
    (hx : G.unblockedDifferential R x = (MvPolynomial.X c : MvPolynomial (Fin n) R) • a) :
    G.unblockedDifferential R (x + hG.XSmulHomotopy R c c' a) =
      (MvPolynomial.X c' : MvPolynomial (Fin n) R) • a := by
  rw [map_add, hx, hG.unblockedDifferential_XSmulHomotopy_of_eq_zero R c c'
    (G.unblockedDifferential_eq_zero_of_eq_X_smul R hx), add_smul, ← add_assoc, ← add_smul,
    CharTwo.add_self_eq_zero, zero_smul, zero_add]

/-- If `∂⁻ x = V_c' a`, then `∂⁻(x + H a) = V_c a` for the `X`-marking homotopy
`H = hG.XSmulHomotopy R c c'` between the actions of `V_c` and `V_c'`. -/
theorem IsKnot.unblockedDifferential_add_XSmulHomotopy_right {G : GridDiagram n} (hG : G.IsKnot)
    (c c' : Fin n) (x a : GridChainMinus R n)
    (hx : G.unblockedDifferential R x = (MvPolynomial.X c' : MvPolynomial (Fin n) R) • a) :
    G.unblockedDifferential R (x + hG.XSmulHomotopy R c c' a) =
      (MvPolynomial.X c : MvPolynomial (Fin n) R) • a := by
  rw [map_add, hx, hG.unblockedDifferential_XSmulHomotopy_of_eq_zero R c c'
    (G.unblockedDifferential_eq_zero_of_eq_X_smul R hx), add_smul, add_comm, add_assoc, ← add_smul,
    CharTwo.add_self_eq_zero, zero_smul, add_zero]

end Matrix

/-! ### Chain homotopies -/

variable (R : Type*) [CommRing R] [CharP R 2]

/-- The `X`-marking homotopy `H_k` as a chain homotopy on the unblocked grid complex, from
multiplication by `V_k` to multiplication by `V_j`, where `O_j` is the `O`-marking in the row of
`X_k`. -/
noncomputable def unblockedComplexXHomotopy (k : Fin n) :
    Homotopy ((MvPolynomial.X k : MvPolynomial (Fin n) R) • 𝟙 (G.unblockedComplex R))
      ((MvPolynomial.X (G.O.transpose (G.X k)) : MvPolynomial (Fin n) R) •
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
    (Homotopy.ofEq (by rw [O_transpose_X_componentPerm]))

/-- Multiplication by the variables of two columns on the same link component is chain homotopic
on the unblocked grid complex. -/
theorem nonempty_homotopy_X_smul_of_pow_componentPerm_apply {c c' : Fin n} (i : ℕ)
    (h : (G.componentPerm ^ i) c = c') :
    Nonempty (Homotopy ((MvPolynomial.X c : MvPolynomial (Fin n) R) • 𝟙 (G.unblockedComplex R))
      ((MvPolynomial.X c' : MvPolynomial (Fin n) R) • 𝟙 (G.unblockedComplex R))) := by
  subst h
  induction i with
  | zero => exact ⟨Homotopy.refl _⟩
  | succ i ih =>
    obtain ⟨h⟩ := ih
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact ⟨h.trans (G.unblockedComplexComponentHomotopy R _).symm⟩

/-- The variables of two columns on the same link component act identically on the homology of
the unblocked grid complex. -/
theorem homologyMap_X_smul_eq_of_pow_componentPerm_apply {c c' : Fin n} (i : ℕ)
    (h : (G.componentPerm ^ i) c = c') :
    HomologicalComplex.homologyMap
        ((MvPolynomial.X c : MvPolynomial (Fin n) R) • 𝟙 (G.unblockedComplex R)) () =
      HomologicalComplex.homologyMap
        ((MvPolynomial.X c' : MvPolynomial (Fin n) R) • 𝟙 (G.unblockedComplex R)) () :=
  (G.nonempty_homotopy_X_smul_of_pow_componentPerm_apply R i h).some.homologyMap_eq ()

/-- On a knot grid, multiplication by any two variables is chain homotopic on the unblocked grid
complex. -/
theorem IsKnot.nonempty_homotopy_X_smul {G : GridDiagram n} (hG : G.IsKnot) (c c' : Fin n) :
    Nonempty (Homotopy ((MvPolynomial.X c : MvPolynomial (Fin n) R) • 𝟙 (G.unblockedComplex R))
      ((MvPolynomial.X c' : MvPolynomial (Fin n) R) • 𝟙 (G.unblockedComplex R))) := by
  obtain ⟨i, hi⟩ := ((G.isKnot_iff_componentPerm_isCycle).mp hG).exists_pow_eq
    (G.componentPerm_apply_ne_self c) (G.componentPerm_apply_ne_self c')
  exact G.nonempty_homotopy_X_smul_of_pow_componentPerm_apply R i hi

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
