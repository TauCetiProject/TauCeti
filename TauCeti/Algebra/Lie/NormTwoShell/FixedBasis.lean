/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.NormTwoShell.Reindex
public import TauCeti.LinearAlgebra.WeightedCycle.Family.SignedPerm

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

The basis is `Module.Basis.fixedBasisSignedPerm`, the integral fixed basis of a signed permutation
of a basis, applied to the permutation `Equiv.Perm.sumCongr σ γ` of the index `I ⊕ Φ` of the
integral basis, with the representatives `Quotient.out` of the vertex orbits and of the root
cycles.

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
* `Matrix.ShellLieAlgebra.reindex_pow_root`: the `r`-th iterate of the pinned action sends `x_a` to
  `c_r x_(γ^r a)`.
* `Matrix.ShellLieAlgebra.reindex_basis`, `Matrix.ShellLieAlgebra.existsUnique_sameCycle_basis`: the
  pinned action is the signed permutation `Equiv.Perm.sumCongr σ γ` of the integral basis, whose
  cycles are represented by the vertex orbits and the root cycles.
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
the permutation `γ = Matrix.normTwoShellCongr hσ` of the norm-two shell: the cycle coefficient
`Equiv.Perm.cycleCoeff` of `γ` with the weights `s`. The `r`-th iterate of the pinned action sends
`x_a` to `c_r x_(γ^r a)` (`Matrix.ShellLieAlgebra.reindex_pow_root`). -/
noncomputable def cycleCoeff (a : B.normTwoShell) (r : ℕ) : ℤˣ :=
  Equiv.Perm.cycleCoeff (normTwoShellCongr hσ) (fun a : B.normTwoShell ↦ inversionSign B σ a) a r

theorem cycleCoeff_def (a : B.normTwoShell) (r : ℕ) :
    cycleCoeff σ hσ a r = ∏ k ∈ Finset.range r, inversionSign B σ ((normTwoShellCongr hσ ^ k) a) :=
  Equiv.Perm.cycleCoeff_def _ _ a r

@[simp]
theorem cycleCoeff_zero (a : B.normTwoShell) : cycleCoeff σ hσ a 0 = 1 :=
  Equiv.Perm.cycleCoeff_zero _ _ a

theorem cycleCoeff_succ (a : B.normTwoShell) (r : ℕ) :
    cycleCoeff σ hσ a (r + 1) =
      cycleCoeff σ hσ a r * inversionSign B σ ((normTwoShellCongr hσ ^ r) a) :=
  Equiv.Perm.cycleCoeff_succ _ _ a r

/-- The `r`-th iterate of the pinned action sends the root vector `x_a` to `c_r x_(γ^r a)`, for the
cycle coefficient `c_r = Matrix.ShellLieAlgebra.cycleCoeff σ hσ a r`. -/
theorem reindex_pow_root (a : B.normTwoShell) (r : ℕ) :
    ((reindex σ hσ).toLinearMap ^ r) (root B a) =
      cycleCoeff σ hσ a r • root B ((normTwoShellCongr hσ ^ r) a) := by
  rw [Units.smul_def, cycleCoeff, ← Units.coeHom_apply, Equiv.Perm.map_cycleCoeff]
  exact Module.End.pow_apply_of_apply_eq_smul _ _ _ (root B)
    (fun b ↦ (reindex_root σ hσ b).trans (Units.smul_def _ _)) a r

/-- The monodromy `μ = c_l` of a cycle of length `l` of the permutation
`γ = Matrix.normTwoShellCongr hσ` of the norm-two shell: the monodromy `Equiv.Perm.monodromy` of its
chosen representative, which is the product of the inversion signs over the cycle
(`Matrix.ShellLieAlgebra.monodromy_eq_prod`). -/
noncomputable def monodromy (C : Quotient (Equiv.Perm.SameCycle.setoid (normTwoShellCongr hσ))) :
    ℤˣ :=
  Equiv.Perm.monodromy (normTwoShellCongr hσ) (fun a : B.normTwoShell ↦ inversionSign B σ a) C.out

theorem monodromy_def (C : Quotient (Equiv.Perm.SameCycle.setoid (normTwoShellCongr hσ))) :
    monodromy σ hσ C = cycleCoeff σ hσ C.out (minimalPeriod (normTwoShellCongr hσ) C.out) :=
  Equiv.Perm.monodromy_def _ _ C.out

/-- The monodromy of a cycle is the product of the inversion signs over the roots of the cycle; in
particular it does not depend on the chosen representative. -/
theorem monodromy_eq_prod [Fintype B.normTwoShell]
    [DecidableRel (Equiv.Perm.SameCycle (normTwoShellCongr hσ))]
    (C : Quotient (Equiv.Perm.SameCycle.setoid (normTwoShellCongr hσ))) :
    monodromy σ hσ C =
      ∏ a with Equiv.Perm.SameCycle (normTwoShellCongr hσ) a C.out, inversionSign B σ a :=
  (Equiv.Perm.monodromy_eq_prod _ _ C.out).trans
    (Finset.prod_congr (Finset.filter_congr fun _ _ ↦ Equiv.Perm.sameCycle_comm) fun _ _ ↦ rfl)

/-- The signed orbit sum `∑_{r < l} c_r x_(γ^r a)` of a cycle of length `l` of the permutation
`γ = Matrix.normTwoShellCongr hσ` of the norm-two shell, starting at the chosen representative `a`
and weighted by the cycle coefficients `c_r = Matrix.ShellLieAlgebra.cycleCoeff σ hσ a r`. For a
cycle of monodromy `1` it is a vector of the integral fixed basis
(`Matrix.ShellLieAlgebra.fixedBasis_inr`). -/
noncomputable def orbitRoot (C : Quotient (Equiv.Perm.SameCycle.setoid (normTwoShellCongr hσ))) :
    ShellLieAlgebra B :=
  ∑ r ∈ Finset.range (minimalPeriod (normTwoShellCongr hσ) C.out),
    (cycleCoeff σ hσ C.out r : ℤ) • root B ((normTwoShellCongr hσ ^ r) C.out)

theorem orbitRoot_def (C : Quotient (Equiv.Perm.SameCycle.setoid (normTwoShellCongr hσ))) :
    orbitRoot σ hσ C = ∑ r ∈ Finset.range (minimalPeriod (normTwoShellCongr hσ) C.out),
      (cycleCoeff σ hσ C.out r : ℤ) • root B ((normTwoShellCongr hσ ^ r) C.out) :=
  (rfl)

/-! ### The pinned action as a signed permutation of the integral basis -/

/-- The pinned action permutes the integral basis `I ⊕ Φ` by `Equiv.Perm.sumCongr σ γ`, with sign
`1` on Cartan vectors and the inversion sign on root vectors. -/
theorem reindex_basis (i : I ⊕ B.normTwoShell) :
    (reindex σ hσ).toLinearMap (basis B i) =
      Sum.elim (1 : I → ℤˣ) (fun a : B.normTwoShell ↦ inversionSign B σ a) i •
        basis B (Equiv.Perm.sumCongr σ (normTwoShellCongr hσ) i) := by
  rcases i with i | a
  · simp [basis_inl, reindex_cartan, Pi.single_comp_equiv]
  · simp [basis_inr, reindex_root]

omit [LinearOrder I] in
/-- The representatives of the vertex orbits and of the root cycles represent the cycles of the
pinned action on the integral basis. -/
theorem existsUnique_sameCycle_basis (x : I ⊕ B.normTwoShell) :
    ∃! j : Quotient (Equiv.Perm.SameCycle.setoid σ) ⊕
        Quotient (Equiv.Perm.SameCycle.setoid (normTwoShellCongr hσ)),
      (Equiv.Perm.sumCongr σ (normTwoShellCongr hσ)).SameCycle
        (Sum.map Quotient.out Quotient.out j) x :=
  Equiv.Perm.existsUnique_sameCycle_sumCongr σ.existsUnique_sameCycle_out
    (Equiv.Perm.existsUnique_sameCycle_out (normTwoShellCongr hσ)) x

/-- The monodromy of the pinned action at the representative of a root cycle is the monodromy of
that cycle. -/
private theorem monodromy_basis_inr
    (C : Quotient (Equiv.Perm.SameCycle.setoid (normTwoShellCongr hσ))) :
    (Equiv.Perm.sumCongr σ (normTwoShellCongr hσ)).monodromy
      (Sum.elim (1 : I → ℤˣ) (fun a : B.normTwoShell ↦ inversionSign B σ a))
      (Sum.map Quotient.out Quotient.out
        (.inr C : Quotient (Equiv.Perm.SameCycle.setoid σ) ⊕ _)) = monodromy σ hσ C :=
  Equiv.Perm.monodromy_sumCongr_inr _ _ _ _ C.out

/-- The positive cycles of the pinned action on the integral basis are the vertex orbits and the
root cycles of monodromy `1`. -/
private noncomputable def positiveCycleEquiv :
    Quotient (Equiv.Perm.SameCycle.setoid σ) ⊕
        {C : Quotient (Equiv.Perm.SameCycle.setoid (normTwoShellCongr hσ)) //
          monodromy σ hσ C = 1} ≃
      {j : Quotient (Equiv.Perm.SameCycle.setoid σ) ⊕
          Quotient (Equiv.Perm.SameCycle.setoid (normTwoShellCongr hσ)) //
        (Equiv.Perm.sumCongr σ (normTwoShellCongr hσ)).monodromy
          (Sum.elim (1 : I → ℤˣ) (fun a : B.normTwoShell ↦ inversionSign B σ a))
          (Sum.map Quotient.out Quotient.out j) = 1}
    where
  toFun := Sum.elim (fun O ↦ ⟨.inl O, by simp⟩)
    (fun C ↦ ⟨.inr C.val, (monodromy_basis_inr σ hσ C.val).trans C.property⟩)
  invFun
    | ⟨.inl O, _⟩ => .inl O
    | ⟨.inr C, hC⟩ => .inr ⟨C, (monodromy_basis_inr σ hσ C).symm.trans hC⟩
  left_inv := by rintro (O | C) <;> rfl
  right_inv := by rintro ⟨O | C, h⟩ <;> rfl

private theorem positiveCycleEquiv_inl (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    (positiveCycleEquiv σ hσ (.inl O)).val = .inl O := by
  rw [positiveCycleEquiv, Equiv.coe_fn_mk, Sum.elim_inl]

private theorem positiveCycleEquiv_inr
    (C : {C : Quotient (Equiv.Perm.SameCycle.setoid (normTwoShellCongr hσ)) //
      monodromy σ hσ C = 1}) :
    (positiveCycleEquiv σ hσ (.inr C)).val = .inr C.val := by
  rw [positiveCycleEquiv, Equiv.coe_fn_mk, Sum.elim_inr]

/-! ### The integral fixed basis -/

variable [Finite B.normTwoShell]

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
  ((basis B).fixedBasisSignedPerm _ _ _ (reindex_basis σ hσ) _
    (existsUnique_sameCycle_basis σ hσ)).reindex (positiveCycleEquiv σ hσ).symm

/-- The basis vector of a `σ`-orbit `O` of vertices is the orbit sum `∑_{i ∈ O} H_(αᵢ)`. -/
@[simp]
theorem fixedBasis_inl (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    (fixedBasis σ hσ (.inl O) : ShellLieAlgebra B) =
      ∑ i with σ.SameCycle i O.out, cartan B (Pi.single i 1) := by
  rw [fixedBasis, Module.Basis.reindex_apply, Equiv.symm_symm,
    Module.Basis.fixedBasisSignedPerm_apply, positiveCycleEquiv_inl]
  simp only [Sum.map_inl, Equiv.Perm.minimalPeriod_sumCongr_inl,
    Equiv.Perm.cycleCoeff_sumCongr_inl, Equiv.Perm.cycleCoeff_one, one_smul,
    Equiv.Perm.sumCongr_pow, Equiv.Perm.sumCongr_apply, basis_inl]
  rw [σ.sum_range_minimalPeriod (fun i ↦ cartan B (Pi.single i 1)) O.out]
  exact Finset.sum_congr (Finset.filter_congr fun _ _ ↦ Equiv.Perm.sameCycle_comm) fun _ _ ↦ rfl

/-- The basis vector of a root cycle `C` of monodromy `1` is its signed orbit sum. -/
@[simp]
theorem fixedBasis_inr
    (C : {C : Quotient (Equiv.Perm.SameCycle.setoid (normTwoShellCongr hσ)) //
      monodromy σ hσ C = 1}) :
    (fixedBasis σ hσ (.inr C) : ShellLieAlgebra B) = orbitRoot σ hσ C := by
  rw [fixedBasis, Module.Basis.reindex_apply, Equiv.symm_symm,
    Module.Basis.fixedBasisSignedPerm_apply, positiveCycleEquiv_inr, orbitRoot_def]
  simp only [Sum.map_inr, Equiv.Perm.minimalPeriod_sumCongr_inr,
    Equiv.Perm.cycleCoeff_sumCongr_inr, Equiv.Perm.sumCongr_pow, Equiv.Perm.sumCongr_apply,
    basis_inr, Units.smul_def, cycleCoeff]

/-- The coordinate of a fixed vector at a `σ`-orbit `O` of vertices is its coefficient on the
Cartan vector `H_(αᵢ)` of the chosen representative `i` of `O`. -/
@[simp]
theorem fixedBasis_repr_inl (v : (reindex σ hσ).toLinearMap.fixedSubmodule)
    (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    (fixedBasis σ hσ).repr v (.inl O) = (basis B).repr v (.inl O.out) := by
  rw [fixedBasis, Module.Basis.repr_reindex_apply, Equiv.symm_symm,
    Module.Basis.fixedBasisSignedPerm_repr, positiveCycleEquiv_inl, Sum.map_inl]

/-- The coordinate of a fixed vector at a root cycle `C` of monodromy `1` is its coefficient on the
root vector `x_a` of the chosen representative `a` of `C`. -/
@[simp]
theorem fixedBasis_repr_inr (v : (reindex σ hσ).toLinearMap.fixedSubmodule)
    (C : {C : Quotient (Equiv.Perm.SameCycle.setoid (normTwoShellCongr hσ)) //
      monodromy σ hσ C = 1}) :
    (fixedBasis σ hσ).repr v (.inr C) = (basis B).repr v (.inr C.val.out) := by
  rw [fixedBasis, Module.Basis.repr_reindex_apply, Equiv.symm_symm,
    Module.Basis.fixedBasisSignedPerm_repr, positiveCycleEquiv_inr, Sum.map_inr]

end Matrix.ShellLieAlgebra
