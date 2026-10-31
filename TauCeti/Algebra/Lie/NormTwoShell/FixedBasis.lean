/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.NormTwoShell.Reindex
public import TauCeti.GroupTheory.Perm.Cycle.Enumeration
public import TauCeti.LinearAlgebra.WeightedCycle.Family.Signed

/-!
# The integral fixed basis of a pinned diagram action

Let `B : Matrix I I ℤ` be an integer Gram matrix on a linearly ordered finite set `I` whose
norm-two shell `Φ` is finite, for instance a positive definite one, and let `σ` be a permutation of
`I` with `B.reindex σ σ = B`, for instance an automorphism of a simply laced Dynkin diagram. Its
pinned action `Matrix.ShellLieAlgebra.reindex σ hσ` on the
signed shell Lie algebra `Matrix.ShellLieAlgebra B` permutes the integral basis up to sign:

`H_(αᵢ) ↦ H_(α_(σ i))`,  `x_a ↦ s(a) x_(γ a)`,

where `γ a = a ∘ σ.symm` is the induced permutation of `Φ` and
`s = Matrix.inversionSign B σ`. Along the cycle `a, γ a, …, γ^(l-1) a` of a root `a`, the cycle
coefficients are `c_r = s(a) s(γ a) ⋯ s(γ^(r-1) a)`
(`Matrix.ShellLieAlgebra.cycleCoeff`) and the monodromy of the cycle is `μ = c_l`
(`Matrix.ShellLieAlgebra.monodromy`), the product of `s` over the cycle.

A fixed vector has equal coefficients on the Cartan vectors of a `σ`-orbit of vertices, and its
coefficients along a root cycle are `c_r t` for its initial coefficient `t`, which must satisfy
`μ t = t`. Over `ℤ` a cycle of monodromy `-1` therefore carries no fixed vector, and the fixed
submodule of the pinned action is free with basis (`Matrix.ShellLieAlgebra.fixedBasis`)

* the orbit sums `∑_{i ∈ O} H_(αᵢ)` of the `σ`-orbits `O` of vertices, and
* the signed orbit sums `∑_{r < l} c_r x_(γ^r a)` (`Matrix.ShellLieAlgebra.orbitRoot`) of the root
  cycles of monodromy `1`.

The coordinates of a fixed vector in this basis are its coefficients on the chosen representatives
(`Matrix.ShellLieAlgebra.fixedBasis_repr_inl`, `Matrix.ShellLieAlgebra.fixedBasis_repr_inr`).

Root cycles of monodromy `-1` do occur: for the reversal of `A₂`, the root `α₁ + α₂` is fixed and
has inversion sign `-1`. Over a coefficient ring with nonzero `2`-torsion such a cycle carries
fixed vectors, so the fixed module of a scalar extension can be larger than the scalar extension of
the integral fixed module; `Module.Basis.fixedEquivSignedFamilyBaseChange` is the general
signed-cycle statement.

## Main definitions

* `Matrix.ShellLieAlgebra.cycleCoeff`: the cycle coefficients `c_r` of a root.
* `Matrix.ShellLieAlgebra.monodromy`: the monodromy of a root cycle.
* `Matrix.ShellLieAlgebra.orbitRoot`: the signed orbit sum of a root cycle.
* `Matrix.ShellLieAlgebra.fixedBasis`: the integral basis of the fixed submodule of the pinned
  action.

## Main results

* `Matrix.ShellLieAlgebra.monodromy_eq_prod`: the monodromy is the product of the inversion signs
  over the cycle, so it does not depend on the representative.
* `Matrix.ShellLieAlgebra.fixedBasis_inl`, `Matrix.ShellLieAlgebra.fixedBasis_inr`: the basis
  vectors are the Cartan orbit sums and the signed orbit sums of the root cycles of monodromy `1`.

## References

* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, Cambridge University Press (1990),
  §§7.8–7.9.
-/

public section

open Function

namespace Matrix.ShellLieAlgebra

variable {I : Type*} [Fintype I] [LinearOrder I] {B : Matrix I I ℤ} (σ : Equiv.Perm I)
  (hσ : B.reindex σ σ = B)

/-! ### Cycle coefficients and monodromy -/

/-- The cycle coefficient `c_r = s(a) s(γ a) ⋯ s(γ^(r-1) a)` of a root `a`, the product of the
inversion signs `s = Matrix.inversionSign B σ` over the first `r` points of the cycle of `a` under
the permutation `γ = Matrix.normTwoShellCongr hσ` of the norm-two shell. The `r`-th iterate of the
pinned action sends `x_a` to `c_r x_(γ^r a)`. -/
noncomputable def cycleCoeff (a : B.normTwoShell) (r : ℕ) : ℤˣ :=
  ∏ k ∈ Finset.range r, inversionSign B σ ((normTwoShellCongr hσ ^ k) a)

@[simp]
theorem cycleCoeff_zero (a : B.normTwoShell) : cycleCoeff σ hσ a 0 = 1 := by
  simp [cycleCoeff]

theorem cycleCoeff_succ (a : B.normTwoShell) (r : ℕ) :
    cycleCoeff σ hσ a (r + 1) =
      cycleCoeff σ hσ a r * inversionSign B σ ((normTwoShellCongr hσ ^ r) a) := by
  simp [cycleCoeff, Finset.prod_range_succ]

/-- The monodromy `μ = c_l` of a cycle of length `l` of the permutation
`γ = Matrix.normTwoShellCongr hσ` of the norm-two shell: the product of the inversion signs over the
cycle (`Matrix.ShellLieAlgebra.monodromy_eq_prod`). -/
noncomputable def monodromy (C : Quotient (Equiv.Perm.SameCycle.setoid (normTwoShellCongr hσ))) :
    ℤˣ :=
  cycleCoeff σ hσ C.out (minimalPeriod (normTwoShellCongr hσ) C.out)

/-- The monodromy of a cycle is the product of the inversion signs over the roots of the cycle; in
particular it does not depend on the chosen representative. -/
theorem monodromy_eq_prod [Fintype B.normTwoShell]
    [DecidableRel (Equiv.Perm.SameCycle (normTwoShellCongr hσ))]
    (C : Quotient (Equiv.Perm.SameCycle.setoid (normTwoShellCongr hσ))) :
    monodromy σ hσ C =
      ∏ a with Equiv.Perm.SameCycle (normTwoShellCongr hσ) a C.out, inversionSign B σ a :=
  Equiv.Perm.prod_range_minimalPeriod_out (normTwoShellCongr hσ)
    (fun a : B.normTwoShell ↦ inversionSign B σ a) C

/-- The signed orbit sum `∑_{r < l} c_r x_(γ^r a)` of a cycle of length `l` of the permutation
`γ = Matrix.normTwoShellCongr hσ` of the norm-two shell, starting at the chosen representative `a`
and weighted by the cycle coefficients `c_r = Matrix.ShellLieAlgebra.cycleCoeff σ hσ a r`. For a
cycle of monodromy `1` it is a vector of the integral fixed basis
(`Matrix.ShellLieAlgebra.fixedBasis_inr`). -/
noncomputable def orbitRoot (C : Quotient (Equiv.Perm.SameCycle.setoid (normTwoShellCongr hσ))) :
    ShellLieAlgebra B :=
  ∑ r ∈ Finset.range (minimalPeriod (normTwoShellCongr hσ) C.out),
    (cycleCoeff σ hσ C.out r : ℤ) • root B ((normTwoShellCongr hσ ^ r) C.out)

/-! ### The cycles of the pinned action on the integral basis -/

variable [Finite B.normTwoShell]

/-- The length minus one of the cycles of the pinned action on the integral basis. It is reducible,
so the fibre `Fin (cycleLength σ hσ (.inl O) + 1)` is definitionally the fibre of
`Equiv.Perm.sigmaCycleEquiv σ` at `O`, and likewise for root cycles; the proofs below close goals
stated with either fibre by `exact` with the cycle-enumeration lemmas. -/
private noncomputable abbrev cycleLength :
    Quotient (Equiv.Perm.SameCycle.setoid σ) ⊕
      Quotient (Equiv.Perm.SameCycle.setoid (normTwoShellCongr hσ)) → ℕ :=
  Sum.elim (fun O ↦ minimalPeriod σ O.out - 1)
    (fun C ↦ minimalPeriod (normTwoShellCongr hσ) C.out - 1)

/-- The enumeration of the integral basis `I ⊕ Φ` along the cycles of the pinned action: the
vertex orbits enumerate `I` and the root cycles enumerate `Φ`. -/
private noncomputable def cycleEnum :
    (Σ j, Fin (cycleLength σ hσ j + 1)) ≃ I ⊕ B.normTwoShell :=
  (Equiv.sumSigmaDistrib _).trans
    (σ.sigmaCycleEquiv.sumCongr (Equiv.Perm.sigmaCycleEquiv (normTwoShellCongr hσ)))

omit [LinearOrder I] in
private theorem cycleEnum_inl
    (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) (i : Fin (cycleLength σ hσ (.inl O) + 1)) :
    cycleEnum σ hσ ⟨.inl O, i⟩ = .inl (σ.sigmaCycleEquiv ⟨O, i⟩) :=
  rfl

omit [LinearOrder I] in
private theorem cycleEnum_inr
    (C : Quotient (Equiv.Perm.SameCycle.setoid (normTwoShellCongr hσ)))
    (i : Fin (cycleLength σ hσ (.inr C) + 1)) :
    cycleEnum σ hσ ⟨.inr C, i⟩ =
      .inr (Equiv.Perm.sigmaCycleEquiv (normTwoShellCongr hσ) ⟨C, i⟩) :=
  rfl

/-- The sign by which the pinned action scales an enumerated basis vector: `1` on Cartan vectors and
the inversion sign on root vectors. -/
private noncomputable def cycleSign (j)
    (i : Fin (cycleLength σ hσ j + 1)) : ℤ :=
  Sum.elim (fun _ ↦ 1) (fun a : B.normTwoShell ↦ (inversionSign B σ a : ℤ))
    (cycleEnum σ hσ ⟨j, i⟩)

private theorem cycleSign_inl
    (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) : cycleSign σ hσ (.inl O) = fun _ ↦ 1 :=
  funext fun i ↦ by rw [cycleSign, cycleEnum_inl, Sum.elim_inl]

private theorem cycleSign_inr
    (C : Quotient (Equiv.Perm.SameCycle.setoid (normTwoShellCongr hσ))) :
    cycleSign σ hσ (.inr C) = fun i ↦
      (inversionSign B σ (Equiv.Perm.sigmaCycleEquiv (normTwoShellCongr hσ) ⟨C, i⟩) : ℤ) :=
  funext fun i ↦ by rw [cycleSign, cycleEnum_inr, Sum.elim_inr]

private theorem cycleSign_eq_one_or (j)
    (i : Fin (cycleLength σ hσ j + 1)) : cycleSign σ hσ j i = 1 ∨ cycleSign σ hσ j i = -1 := by
  cases j with
  | inl O => exact .inl (congrFun (cycleSign_inl σ hσ O) i)
  | inr C => rw [cycleSign_inr]; exact Int.isUnit_iff.mp (Units.isUnit _)

private theorem reindex_cycleEnum (j)
    (i : Fin (cycleLength σ hσ j + 1)) :
    (reindex σ hσ).toLinearMap (basis B (cycleEnum σ hσ ⟨j, i⟩)) =
      cycleSign σ hσ j i • basis B (cycleEnum σ hσ ⟨j, finRotate _ i⟩) := by
  classical
  cases j with
  | inl O =>
    rw [cycleEnum_inl, cycleEnum_inl, cycleSign_inl, one_smul, LinearEquiv.coe_coe, basis_inl,
      basis_inl, reindex_cartan, Pi.single_comp_equiv, Equiv.symm_symm]
    exact congrArg (fun x ↦ cartan B (Pi.single x 1)) (σ.sigmaCycleEquiv_finRotate O i).symm
  | inr C =>
    rw [cycleEnum_inr, cycleEnum_inr, cycleSign_inr, LinearEquiv.coe_coe, basis_inr, basis_inr,
      reindex_root, Units.smul_def]
    exact congrArg (fun a ↦ _ • root B a)
      (Equiv.Perm.sigmaCycleEquiv_finRotate (normTwoShellCongr hσ) C i).symm

private theorem prod_cycleSign_inl
    (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) : ∏ i, cycleSign σ hσ (.inl O) i = 1 := by
  simp [cycleSign_inl]

private theorem partialProd_cycleSign_inr
    (C : Quotient (Equiv.Perm.SameCycle.setoid (normTwoShellCongr hσ)))
    (i : Fin (cycleLength σ hσ (.inr C) + 1)) :
    Fin.partialProd (Fin.init (cycleSign σ hσ (.inr C))) i = (cycleCoeff σ hσ C.out i : ℤ) := by
  rw [cycleSign_inr, cycleCoeff, Units.coe_prod]
  exact Equiv.Perm.partialProd_init_sigmaCycleEquiv (normTwoShellCongr hσ)
    (fun a : B.normTwoShell ↦ (inversionSign B σ a : ℤ)) C i

private theorem prod_cycleSign_inr
    (C : Quotient (Equiv.Perm.SameCycle.setoid (normTwoShellCongr hσ))) :
    ∏ i, cycleSign σ hσ (.inr C) i = (monodromy σ hσ C : ℤ) := by
  rw [cycleSign_inr, monodromy, cycleCoeff, Units.coe_prod]
  exact Equiv.Perm.prod_sigmaCycleEquiv_eq_prod_range (normTwoShellCongr hσ)
    (fun a : B.normTwoShell ↦ (inversionSign B σ a : ℤ)) C

/-- The positive cycles of the pinned action are the vertex orbits and the root cycles of
monodromy `1`. -/
private noncomputable def positiveCycleEquiv :
    {j // ∏ i, cycleSign σ hσ j i = 1} ≃
      Quotient (Equiv.Perm.SameCycle.setoid σ) ⊕
        {C : Quotient (Equiv.Perm.SameCycle.setoid (normTwoShellCongr hσ)) //
          monodromy σ hσ C = 1} :=
  Equiv.subtypeSum.trans <| Equiv.sumCongr (Equiv.subtypeUnivEquiv (prod_cycleSign_inl σ hσ))
    (Equiv.subtypeEquivRight fun C ↦ by rw [prod_cycleSign_inr, Units.val_eq_one])

private theorem positiveCycleEquiv_symm_inl
    (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    ((positiveCycleEquiv σ hσ).symm (.inl O)).val = .inl O :=
  rfl

private theorem positiveCycleEquiv_symm_inr
    (C : {C : Quotient (Equiv.Perm.SameCycle.setoid (normTwoShellCongr hσ)) //
      monodromy σ hσ C = 1}) :
    ((positiveCycleEquiv σ hσ).symm (.inr C)).val = .inr C.val :=
  rfl

/-- The integral basis of the fixed submodule indexed by the positive cycles of the pinned
action. -/
private noncomputable def cycleBasis :
    Module.Basis {j // ∏ i, cycleSign σ hσ j i = 1} ℤ (reindex σ hσ).toLinearMap.fixedSubmodule :=
  (basis B).fixedBasisSignedFamily (cycleEnum σ hσ) (cycleSign σ hσ) (cycleSign_eq_one_or σ hσ)
    (reindex σ hσ).toLinearMap (reindex_cycleEnum σ hσ)

private theorem cycleBasis_of_eq_inl (j)
    (hjp : ∏ i, cycleSign σ hσ j i = 1) (O : Quotient (Equiv.Perm.SameCycle.setoid σ))
    (hj : j = .inl O) :
    (cycleBasis σ hσ ⟨j, hjp⟩ : ShellLieAlgebra B) =
      ∑ i with σ.SameCycle i O.out, cartan B (Pi.single i 1) := by
  classical
  subst hj
  have h1 (i : Fin (cycleLength σ hσ (.inl O) + 1)) :
      Fin.partialProd (Fin.init (cycleSign σ hσ (.inl O))) i = 1 := by
    rw [cycleSign_inl]
    induction i using Fin.induction with
    | zero => exact Fin.partialProd_zero _
    | succ j ih => rw [Fin.partialProd_succ, ih]; simp [Fin.init]
  rw [cycleBasis, Module.Basis.fixedBasisSignedFamily_apply]
  refine (Finset.sum_congr rfl fun i _ ↦ ?_).trans
    (σ.sum_sigmaCycleEquiv (fun i ↦ cartan B (Pi.single i 1)) O)
  rw [h1, one_smul, cycleEnum_inl, basis_inl]

private theorem cycleBasis_of_eq_inr (j)
    (hjp : ∏ i, cycleSign σ hσ j i = 1)
    (C : Quotient (Equiv.Perm.SameCycle.setoid (normTwoShellCongr hσ))) (hj : j = .inr C) :
    (cycleBasis σ hσ ⟨j, hjp⟩ : ShellLieAlgebra B) = orbitRoot σ hσ C := by
  subst hj
  rw [cycleBasis, Module.Basis.fixedBasisSignedFamily_apply, orbitRoot,
    ← Equiv.Perm.minimalPeriod_sub_one_add_one (normTwoShellCongr hσ) C.out,
    ← Fin.sum_univ_eq_sum_range (fun r ↦ (cycleCoeff σ hσ C.out r : ℤ) •
      root B ((normTwoShellCongr hσ ^ r) C.out))]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [partialProd_cycleSign_inr, cycleEnum_inr, basis_inr]
  exact congrArg (fun a ↦ _ • root B a)
    (Equiv.Perm.sigmaCycleEquiv_apply (normTwoShellCongr hσ) C i)

private theorem cycleBasis_repr_of_eq_inl
    (v : (reindex σ hσ).toLinearMap.fixedSubmodule) (j) (hjp : ∏ i, cycleSign σ hσ j i = 1)
    (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) (hj : j = .inl O) :
    (cycleBasis σ hσ).repr v ⟨j, hjp⟩ = (basis B).repr v (.inl O.out) := by
  subst hj
  rw [cycleBasis, Module.Basis.fixedBasisSignedFamily_repr, cycleEnum_inl]
  exact congrArg (fun x ↦ (basis B).repr v (.inl x)) ((σ.sigmaCycleEquiv_apply O 0).trans (by simp))

private theorem cycleBasis_repr_of_eq_inr
    (v : (reindex σ hσ).toLinearMap.fixedSubmodule) (j) (hjp : ∏ i, cycleSign σ hσ j i = 1)
    (C : Quotient (Equiv.Perm.SameCycle.setoid (normTwoShellCongr hσ))) (hj : j = .inr C) :
    (cycleBasis σ hσ).repr v ⟨j, hjp⟩ = (basis B).repr v (.inr C.out) := by
  subst hj
  rw [cycleBasis, Module.Basis.fixedBasisSignedFamily_repr, cycleEnum_inr]
  exact congrArg (fun x ↦ (basis B).repr v (.inr x))
    ((Equiv.Perm.sigmaCycleEquiv_apply (normTwoShellCongr hσ) C 0).trans (by simp))

/-! ### The integral fixed basis -/

/-- **The integral fixed basis of a pinned diagram action.** For `B` with finite norm-two shell
(for instance positive definite, `Matrix.PosDef.finite_normTwoShell`) and a permutation `σ` of the
vertices with `B.reindex σ σ = B`, the fixed submodule of the pinned action
`Matrix.ShellLieAlgebra.reindex σ hσ` is free over `ℤ` with a basis indexed by the `σ`-orbits `O` of
vertices and the cycles `C` of monodromy `1` of the induced permutation of the norm-two shell. The
basis vectors are the orbit sums `∑_{i ∈ O} H_(αᵢ)` (`Matrix.ShellLieAlgebra.fixedBasis_inl`) and
the signed orbit sums `Matrix.ShellLieAlgebra.orbitRoot σ hσ C`
(`Matrix.ShellLieAlgebra.fixedBasis_inr`). -/
noncomputable def fixedBasis :
    Module.Basis (Quotient (Equiv.Perm.SameCycle.setoid σ) ⊕
        {C : Quotient (Equiv.Perm.SameCycle.setoid (normTwoShellCongr hσ)) //
          monodromy σ hσ C = 1}) ℤ
      (reindex σ hσ).toLinearMap.fixedSubmodule :=
  (cycleBasis σ hσ).reindex (positiveCycleEquiv σ hσ)

/-- The basis vector of a `σ`-orbit `O` of vertices is the orbit sum `∑_{i ∈ O} H_(αᵢ)`. -/
@[simp]
theorem fixedBasis_inl (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    (fixedBasis σ hσ (.inl O) : ShellLieAlgebra B) =
      ∑ i with σ.SameCycle i O.out, cartan B (Pi.single i 1) := by
  rw [fixedBasis, Module.Basis.reindex_apply]
  exact cycleBasis_of_eq_inl σ hσ _ _ O (positiveCycleEquiv_symm_inl σ hσ O)

/-- The basis vector of a root cycle `C` of monodromy `1` is its signed orbit sum. -/
@[simp]
theorem fixedBasis_inr
    (C : {C : Quotient (Equiv.Perm.SameCycle.setoid (normTwoShellCongr hσ)) //
      monodromy σ hσ C = 1}) :
    (fixedBasis σ hσ (.inr C) : ShellLieAlgebra B) = orbitRoot σ hσ C := by
  rw [fixedBasis, Module.Basis.reindex_apply]
  exact cycleBasis_of_eq_inr σ hσ _ _ C (positiveCycleEquiv_symm_inr σ hσ C)

/-- The coordinate of a fixed vector at a `σ`-orbit `O` of vertices is its coefficient on the
Cartan vector `H_(αᵢ)` of the chosen representative `i` of `O`. -/
@[simp]
theorem fixedBasis_repr_inl (v : (reindex σ hσ).toLinearMap.fixedSubmodule)
    (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    (fixedBasis σ hσ).repr v (.inl O) = (basis B).repr v (.inl O.out) := by
  rw [fixedBasis, Module.Basis.repr_reindex_apply]
  exact cycleBasis_repr_of_eq_inl σ hσ v _ _ O (positiveCycleEquiv_symm_inl σ hσ O)

/-- The coordinate of a fixed vector at a root cycle `C` of monodromy `1` is its coefficient on the
root vector `x_a` of the chosen representative `a` of `C`. -/
@[simp]
theorem fixedBasis_repr_inr (v : (reindex σ hσ).toLinearMap.fixedSubmodule)
    (C : {C : Quotient (Equiv.Perm.SameCycle.setoid (normTwoShellCongr hσ)) //
      monodromy σ hσ C = 1}) :
    (fixedBasis σ hσ).repr v (.inr C) = (basis B).repr v (.inr C.val.out) := by
  rw [fixedBasis, Module.Basis.repr_reindex_apply]
  exact cycleBasis_repr_of_eq_inr σ hσ v _ _ C (positiveCycleEquiv_symm_inr σ hσ C)

end Matrix.ShellLieAlgebra
