/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import TauCeti.Algebra.Homology.Linear
public import TauCeti.Algebra.Homology.SquareZero
public import TauCeti.Algebra.MvPolynomial.AevalConstX
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

Concretely, `GH⁻(G)` is the quotient `ker ∂⁻ ⧸ im ∂⁻` of the cycles of `GC⁻(G)` by the boundaries
(`unblockedHomologyIso`), so every class is the class of a cycle (`unblockedHomologyClass`), and a
cycle has zero class exactly when it is a boundary. Structure on `GC⁻(G)` that the differential
respects, such as the Alexander grading, descends to this quotient.

## Main definitions

* `TauCeti.GridDiagram.unblockedHomology`: the unblocked grid homology `GH⁻`.
* `TauCeti.GridDiagram.unblockedHomologyIso`: `GH⁻` is `ker ∂⁻ ⧸ im ∂⁻`.
* `TauCeti.GridDiagram.unblockedHomologyClass`: the class in `GH⁻` of a cycle.
* `TauCeti.GridDiagram.IsKnot.unblockedHomologyModule`: the `R[U]`-module structure on the
  unblocked grid homology of a knot grid.

## Main results

* `TauCeti.GridDiagram.X_smul_unblockedHomology_eq_of_sameCycle`: variables on the same
  component act identically on `GH⁻`.
* `TauCeti.GridDiagram.smul_unblockedHomology_eq_rename_smul`: renaming the variables within
  components does not change the action of a polynomial on `GH⁻`.
* `TauCeti.GridDiagram.unblockedHomologyClass_surjective` and
  `TauCeti.GridDiagram.unblockedHomologyClass_eq_zero_iff`: every class is the class of a cycle,
  and a cycle has zero class exactly when it is a boundary.
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

/-! ### Cycles and boundaries -/

section Quotient

variable (G R)

/-- The unblocked complex with its unique object and differential spelled out, so that its
homology is the homology of the unblocked grid differential in the sense of
`LinearMap.homology`. -/
private noncomputable abbrev unblockedComplex' :
    HomologicalComplex (ModuleCat (MvPolynomial (Fin n) R)) (ComplexShape.refl Unit) where
  X _ := ModuleCat.of (MvPolynomial (Fin n) R) (GridChainMinus R n)
  d _ _ := ModuleCat.ofHom (G.unblockedDifferential R)
  d_comp_d' _ _ _ _ _ :=
    ((G.unblockedDifferential R).shortComplex (G.unblockedDifferential_comp_self_eq_zero R)).zero

/-- The unblocked complex is isomorphic to its spelled-out form `unblockedComplex'`. -/
private noncomputable def unblockedComplexIso : G.unblockedComplex R ≅ G.unblockedComplex' R :=
  HomologicalComplex.Hom.isoOfComponents (fun i ↦ eqToIso (G.unblockedComplex_X R i)) (by
    rintro ⟨⟩ ⟨⟩ -
    simp)

/-- The unblocked grid homology `GH⁻` is the homology `ker ∂⁻ ⧸ im ∂⁻` of the unblocked grid
differential: the cycles of `GC⁻` modulo the boundaries. -/
noncomputable def unblockedHomologyIso :
    G.unblockedHomology R ≅
      ModuleCat.of (MvPolynomial (Fin n) R)
        ((G.unblockedDifferential R).homology (G.unblockedDifferential_comp_self_eq_zero R)) :=
  HomologicalComplex.homologyMapIso (G.unblockedComplexIso R) () ≪≫
    (G.unblockedComplex' R).homologyIsoSc' () () () rfl rfl ≪≫
      (G.unblockedDifferential R).homologyIso (G.unblockedDifferential_comp_self_eq_zero R)

/-- The linear map sending a cycle of `GC⁻` to its class in `GH⁻`. -/
noncomputable def unblockedHomologyClass :
    LinearMap.ker (G.unblockedDifferential R) →ₗ[MvPolynomial (Fin n) R] G.unblockedHomology R :=
  (G.unblockedHomologyIso R).inv.hom ∘ₗ
    (G.unblockedDifferential R).homologyπ (G.unblockedDifferential_comp_self_eq_zero R)

/-- Under `unblockedHomologyIso`, the class of a cycle is its class modulo the boundaries. -/
@[simp]
theorem unblockedHomologyIso_hom_unblockedHomologyClass
    (z : LinearMap.ker (G.unblockedDifferential R)) :
    (G.unblockedHomologyIso R).hom (G.unblockedHomologyClass R z) =
      (G.unblockedDifferential R).homologyπ (G.unblockedDifferential_comp_self_eq_zero R) z := by
  simp [unblockedHomologyClass]

/-- Every class in `GH⁻` is represented by a cycle. -/
theorem unblockedHomologyClass_surjective : Function.Surjective (G.unblockedHomologyClass R) := by
  rw [unblockedHomologyClass, LinearMap.coe_comp]
  exact ((ModuleCat.epi_iff_surjective (G.unblockedHomologyIso R).inv).mp inferInstance).comp
    ((G.unblockedDifferential R).homologyπ_surjective
      (G.unblockedDifferential_comp_self_eq_zero R))

/-- A cycle represents zero in `GH⁻` exactly when it is a boundary. -/
@[simp]
theorem unblockedHomologyClass_eq_zero_iff (z : LinearMap.ker (G.unblockedDifferential R)) :
    G.unblockedHomologyClass R z = 0 ↔ (z : GridChainMinus R n) ∈
      LinearMap.range (G.unblockedDifferential R) := by
  rw [← LinearMap.homologyπ_eq_zero_iff (G.unblockedDifferential R)
    (G.unblockedDifferential_comp_self_eq_zero R),
    ← unblockedHomologyIso_hom_unblockedHomologyClass,
    ← map_zero (G.unblockedHomologyIso R).hom.hom]
  exact ((ModuleCat.mono_iff_injective _).mp inferInstance).eq_iff.symm

end Quotient

namespace IsKnot

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
  rw [smul_eq_rename_const_smul hG 0, MvPolynomial.rename_const_eq_aeval_aeval_X,
    (RingHom.mem_ker).mp hp, map_zero, zero_smul]

variable (R) in
/-- The `R[U]`-module structure on the unblocked grid homology of a knot grid: a polynomial `q`
acts as any `p ∈ R[V₀, …, V_{n-1}]` with `p(U, …, U) = q`, so `U` acts as each variable `V_c`. -/
@[instance_reducible]
noncomputable def unblockedHomologyModule (hG : G.IsKnot) :
    Module (Polynomial R) (G.unblockedHomology R) :=
  letI := (isTorsionBySet_unblockedHomology (R := R) hG).module
  haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hG.ne_zero⟩⟩
  Module.compHom _ (Ideal.quotientKerAlgEquivOfSurjective
    (MvPolynomial.aeval_const_X_surjective (Fin n) R)).symm.toRingHom

/-- The `R[U]`-action on the unblocked grid homology of a knot grid is the action of the
quotient `R[V₀, …, V_{n-1}] ⧸ ker π` transported along `R[V₀, …, V_{n-1}] ⧸ ker π ≃ R[U]`. -/
private theorem smul_unblockedHomology_def (hG : G.IsKnot)
    (hπ : Function.Surjective
      (MvPolynomial.aeval (R := R) fun _ : Fin n => (Polynomial.X : Polynomial R)))
    (q : Polynomial R) (x : G.unblockedHomology R) :
    letI := (isTorsionBySet_unblockedHomology (R := R) hG).module
    letI := unblockedHomologyModule R hG
    q • x = (Ideal.quotientKerAlgEquivOfSurjective hπ).symm q • x :=
  rfl

/-- On a knot grid, the evaluation `p(U, …, U)` of a polynomial acts on the unblocked grid
homology as `p` does. -/
@[simp]
theorem aeval_smul_unblockedHomology (hG : G.IsKnot) (p : MvPolynomial (Fin n) R)
    (x : G.unblockedHomology R) :
    letI := unblockedHomologyModule R hG
    MvPolynomial.aeval (fun _ => (Polynomial.X : Polynomial R)) p • x = p • x := by
  let _ := (isTorsionBySet_unblockedHomology (R := R) hG).module
  have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hG.ne_zero⟩⟩
  rw [smul_unblockedHomology_def hG (MvPolynomial.aeval_const_X_surjective (Fin n) R),
    Ideal.quotientKerAlgEquivOfSurjective_symm_apply, Module.IsTorsionBySet.mk_smul]

/-- On a knot grid, `U` acts on the unblocked grid homology as each variable `V_c`. -/
theorem X_smul_unblockedHomology (hG : G.IsKnot) (c : Fin n) (x : G.unblockedHomology R) :
    letI := unblockedHomologyModule R hG
    (Polynomial.X : Polynomial R) • x = (MvPolynomial.X c : MvPolynomial (Fin n) R) • x := by
  simpa using aeval_smul_unblockedHomology hG (MvPolynomial.X c) x

end IsKnot

end GridDiagram

end TauCeti
