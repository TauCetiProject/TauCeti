/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import TauCeti.Algebra.Homology.Linear
public import TauCeti.KnotTheory.Grid.XHomotopy.Complex

/-!
# Unblocked grid homology as a module over `R[U]`

The unblocked grid homology `GH⁻(G)` of a grid diagram `G` of size `n` is the homology of the
unblocked complex `GC⁻(G)`, a module over `R[V₀, …, V_{n-1}]` (`unblockedHomology`). The
`X`-marking homotopies show that two variables `V_c`, `V_{c'}` whose columns lie on the same link
component act identically on it (`X_smul_unblockedHomology_eq_of_sameCycle`). Consequently every
polynomial acts on `GH⁻(G)` as does its image under any renaming of the variables that keeps each
column on its component (`smul_unblockedHomology_eq_rename_smul`).

For a knot grid all variables lie on one component, so the action of `R[V₀, …, V_{n-1}]` factors
through the evaluation `π : R[V₀, …, V_{n-1}] → R[U]` sending every `V_c` to `U`: `GH⁻(G)` is
annihilated by the kernel of `π` (`IsKnot.isTorsionBySet_unblockedHomology`). Since `π` is
surjective, this makes `GH⁻(G)` a module over `R[U]` (`IsKnot.unblockedHomologyModule`), with
`π p` acting as `p` (`IsKnot.aeval_smul_unblockedHomology`) and in particular `U` acting as any
one of the variables `V_c` (`IsKnot.X_smul_unblockedHomology`). The construction involves no
choice of a distinguished column. This is the `𝔽[U]`-module structure on the grid homology of a
knot through which the concordance invariant `τ` is defined.

## Main definitions

* `TauCeti.GridDiagram.unblockedHomology`: the unblocked grid homology `GH⁻`.
* `TauCeti.GridDiagram.IsKnot.unblockedHomologyModule`: the `R[U]`-module structure on the
  unblocked grid homology of a knot grid.

## Main results

* `TauCeti.GridDiagram.X_smul_unblockedHomology_eq_of_sameCycle`: variables on the same
  component act identically on `GH⁻`.
* `TauCeti.GridDiagram.smul_unblockedHomology_eq_rename_smul`: renaming the variables within
  components does not change the action of a polynomial on `GH⁻`.
* `TauCeti.GridDiagram.IsKnot.isTorsionBySet_unblockedHomology`: for a knot grid, `GH⁻` is
  annihilated by the kernel of `R[V₀, …, V_{n-1}] → R[U]`.
* `TauCeti.GridDiagram.IsKnot.aeval_smul_unblockedHomology` and
  `TauCeti.GridDiagram.IsKnot.X_smul_unblockedHomology`: the action of `R[U]` on `GH⁻` of a knot
  grid.

## References

This is Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 4.6: by
Lemma 4.6.9 the variables of a knot grid act identically on `GH⁻`, which is thereby regarded as a
module over `𝔽[U]`.
-/

public section

open CategoryTheory

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommRing R] [CharP R 2]

/-- The unblocked grid homology `GH⁻(G)`: the homology of the unblocked grid complex, a module over
the polynomial ring `R[V₀, …, V_{n-1}]`. -/
noncomputable abbrev unblockedHomology : ModuleCat (MvPolynomial (Fin n) R) :=
  (G.unblockedComplex R).homology ()

variable {G R}

/-- Two variables whose columns lie on the same link component act identically on the unblocked
grid homology. -/
theorem X_smul_unblockedHomology_eq_of_sameCycle {c c' : Fin n}
    (h : G.componentPerm.SameCycle c c') (x : G.unblockedHomology R) :
    (MvPolynomial.X c : MvPolynomial (Fin n) R) • x =
      (MvPolynomial.X c' : MvPolynomial (Fin n) R) • x := by
  obtain ⟨i, hi⟩ := h.exists_nat_pow_eq
  have hmap := congrArg (fun f => f.hom x)
    (G.homologyMap_X_smul_eq_of_pow_componentPerm_apply R i hi)
  simpa using hmap

/-- Every polynomial acts on the unblocked grid homology as its image under a renaming of the
variables that keeps each column on its link component. -/
theorem smul_unblockedHomology_eq_rename_smul (f : Fin n → Fin n)
    (hf : ∀ c, G.componentPerm.SameCycle c (f c)) (p : MvPolynomial (Fin n) R)
    (x : G.unblockedHomology R) :
    p • x = MvPolynomial.rename f p • x := by
  induction p using MvPolynomial.induction_on generalizing x with
  | C r => rw [MvPolynomial.rename_C]
  | add p q hp hq => rw [add_smul, hp, hq, map_add, add_smul]
  | mul_X p c hp =>
    rw [mul_smul, hp, X_smul_unblockedHomology_eq_of_sameCycle (hf c), map_mul,
      MvPolynomial.rename_X, mul_smul]

namespace IsKnot

variable (R) in
/-- The evaluation `R[V₀, …, V_{n-1}] → R[U]` sending every variable to `U`. -/
private noncomputable abbrev evalU (n : ℕ) : MvPolynomial (Fin n) R →ₐ[R] Polynomial R :=
  MvPolynomial.aeval fun _ => Polynomial.X

omit [CharP R 2] in
/-- Renaming every variable to `V_c` is the evaluation `V_i ↦ U` followed by `U ↦ V_c`. -/
private theorem rename_const_eq_aeval_evalU (c : Fin n) (p : MvPolynomial (Fin n) R) :
    MvPolynomial.rename (fun _ => c) p = Polynomial.aeval (MvPolynomial.X c) (evalU R n p) := by
  rw [← AlgHom.comp_apply]
  congr 1
  exact MvPolynomial.algHom_ext fun i => by simp

omit [CharP R 2] in
/-- On a nonempty set of columns the evaluation `V_i ↦ U` is surjective. -/
private theorem evalU_surjective (c : Fin n) : Function.Surjective (evalU R n) := fun q =>
  ⟨Polynomial.aeval (MvPolynomial.X c) q, by
    rw [← Polynomial.aeval_algHom_apply, MvPolynomial.aeval_X, Polynomial.aeval_X_left_apply]⟩

/-- On a knot grid every polynomial acts on the unblocked grid homology as its renaming with every
variable replaced by one fixed variable `V_c`. -/
private theorem smul_eq_rename_const_smul (hG : G.IsKnot) (c : Fin n)
    (p : MvPolynomial (Fin n) R) (x : G.unblockedHomology R) :
    p • x = MvPolynomial.rename (fun _ => c) p • x :=
  smul_unblockedHomology_eq_rename_smul _ (fun c' =>
    ((G.isKnot_iff_componentPerm_isCycle).mp hG).sameCycle (G.componentPerm_apply_ne_self c')
      (G.componentPerm_apply_ne_self c)) p x

/-- On a knot grid the unblocked grid homology is annihilated by the kernel of the evaluation
`R[V₀, …, V_{n-1}] → R[U]` sending every variable to `U`. -/
theorem isTorsionBySet_unblockedHomology (hG : G.IsKnot) :
    Module.IsTorsionBySet (MvPolynomial (Fin n) R) (G.unblockedHomology R)
      (RingHom.ker (MvPolynomial.aeval (R := R) fun _ : Fin n => (Polynomial.X : Polynomial R)) :
        Set (MvPolynomial (Fin n) R)) := by
  intro x ⟨p, hp⟩
  have : NeZero n := ⟨hG.ne_zero⟩
  rw [smul_eq_rename_const_smul hG 0, rename_const_eq_aeval_evalU, (RingHom.mem_ker).mp hp,
    map_zero, zero_smul]

variable (R) in
/-- The `R[U]`-module structure on the unblocked grid homology of a knot grid: a polynomial `q`
acts as any `p ∈ R[V₀, …, V_{n-1}]` with `p(U, …, U) = q`, so `U` acts as each variable `V_c`. -/
@[instance_reducible]
noncomputable def unblockedHomologyModule (hG : G.IsKnot) :
    Module (Polynomial R) (G.unblockedHomology R) :=
  letI := (isTorsionBySet_unblockedHomology (R := R) hG).module
  Module.compHom _ (Ideal.quotientKerAlgEquivOfSurjective
    (evalU_surjective (R := R) (n := n) ⟨0, Nat.pos_of_ne_zero hG.ne_zero⟩)).symm.toRingHom

/-- On a knot grid, the evaluation `p(U, …, U)` of a polynomial acts on the unblocked grid
homology as `p` does. -/
theorem aeval_smul_unblockedHomology (hG : G.IsKnot) (p : MvPolynomial (Fin n) R)
    (x : G.unblockedHomology R) :
    letI := unblockedHomologyModule R hG
    MvPolynomial.aeval (fun _ => (Polynomial.X : Polynomial R)) p • x = p • x := by
  let _ := (isTorsionBySet_unblockedHomology (R := R) hG).module
  -- `Module.compHom` acts through the ring map by definition: `q` acts as the class `e.symm q`.
  change (Ideal.quotientKerAlgEquivOfSurjective
    (evalU_surjective (R := R) (n := n) ⟨0, Nat.pos_of_ne_zero hG.ne_zero⟩)).symm
      (evalU R n p) • x = p • x
  rw [Ideal.quotientKerAlgEquivOfSurjective_symm_apply, Module.IsTorsionBySet.mk_smul]

/-- On a knot grid, `U` acts on the unblocked grid homology as each variable `V_c`. -/
theorem X_smul_unblockedHomology (hG : G.IsKnot) (c : Fin n) (x : G.unblockedHomology R) :
    letI := unblockedHomologyModule R hG
    (Polynomial.X : Polynomial R) • x = (MvPolynomial.X c : MvPolynomial (Fin n) R) • x := by
  simpa using aeval_smul_unblockedHomology hG (MvPolynomial.X c) x

end IsKnot

end GridDiagram

end TauCeti
