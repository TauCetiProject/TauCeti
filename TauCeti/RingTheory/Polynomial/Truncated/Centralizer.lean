/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FGModuleCat.Cyclic
public import TauCeti.Combinatorics.Enumerative.Partition.ColumnSquares
public import TauCeti.LinearAlgebra.End.Centralizer
public import TauCeti.LinearAlgebra.Pi

/-!
# Centralizer dimensions of sums of nilpotent blocks

Let `A = K[X]/(X^n)`, with `x` the class of `X`. On the cyclic module `A/(x^i)`,
for `i ≤ n`, multiplication by `x` is a nilpotent Jordan block of size `i`.
The endomorphisms commuting with `x` on a finite sum of these modules have dimension
`∑ i, ∑ j, min (len i) (len j)`, equivalently the sum of squared column lengths.
This is the blockwise centralizer calculation used in the dimension formula for nilpotent
orbits. Zero-length blocks and empty sums are allowed.

The cyclic modules are the existing right-module quotients, with the action written using
`Aᵐᵒᵖ`. No choice of a Jordan-chain basis for an arbitrary endomorphism is needed here.

## References

* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*,
  §6.1: centralizer dimensions from homomorphisms between Jordan blocks.
-/

public section

namespace TauCeti

open Polynomial MulOpposite CategoryTheory

variable {K : Type*} [Field K] {n : ℕ}

/-- The space of `Aᵐᵒᵖ`-linear endomorphisms of a sum of nilpotent cyclic blocks,
where `A = K[X]/(X^n)`, has dimension the sum of the pairwise minima of their lengths.
These are precisely the endomorphisms commuting with the action of `x`. -/
theorem finrank_end_pi_cyclic_root_pow {ι : Type*} [Fintype ι] (len : ι → ℕ)
    (hlen : ∀ i, len i ≤ n) :
    Module.finrank K (Module.End (AdjoinRoot (X ^ n : K[X]))ᵐᵒᵖ
      ((i : ι) → ((AdjoinRoot (X ^ n : K[X]))ᵐᵒᵖ ⧸
        Ideal.span {op (AdjoinRoot.root (X ^ n : K[X]) ^ len i)}))) =
      ∑ i, ∑ j, min (len i) (len j) := by
  have := (monic_X_pow n).finite_adjoinRoot (R := K)
  let M (i : ι) := (AdjoinRoot (X ^ n : K[X]))ᵐᵒᵖ ⧸
    Ideal.span {op (AdjoinRoot.root (X ^ n : K[X]) ^ len i)}
  let e (i j : ι) := FGModuleCat.cyclicModuleHomLinearEquiv K
    (M := M j) (AdjoinRoot.root (X ^ n : K[X]) ^ len i)
  let _ (i j : ι) : Module.Finite K (M i →ₗ[(AdjoinRoot (X ^ n : K[X]))ᵐᵒᵖ] M j) :=
    LinearEquiv.finiteDimensional ((e i j).symm.trans
      (FGModuleCat.cyclicModuleHomEquiv K (AdjoinRoot.root (X ^ n : K[X]) ^ len i))).symm
  let _ (i j : ι) : Module.Free K (M i →ₗ[(AdjoinRoot (X ^ n : K[X]))ᵐᵒᵖ] M j) :=
    Module.Free.of_divisionRing K _
  rw [finrank_linearMap_pi_eq_sum (R := K)]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    (e i j).finrank_eq.symm.trans (FGModuleCat.finrank_cyclicModule_hom_root_pow (hlen j))

/-- The centralizer of the nilpotent action on a sum of cyclic blocks has dimension
the sum of the pairwise minima of their lengths. -/
theorem finrank_centralizer_pi_cyclic_root_pow {ι : Type*} [Fintype ι] (len : ι → ℕ)
    (hlen : ∀ i, len i ≤ n) :
    Module.finrank K (Subalgebra.centralizer K
      {Algebra.lsmul K K
        ((i : ι) → ((AdjoinRoot (X ^ n : K[X]))ᵐᵒᵖ ⧸
          Ideal.span {op (AdjoinRoot.root (X ^ n : K[X]) ^ len i)}))
        (op (AdjoinRoot.root (X ^ n : K[X])))}) =
      ∑ i, ∑ j, min (len i) (len j) := by
  have hgen : Algebra.adjoin K {op (AdjoinRoot.root (X ^ n : K[X]))} = ⊤ := by
    have h := congrArg (Subalgebra.map (AlgEquiv.toOpposite K
      (AdjoinRoot (X ^ n : K[X]))).toAlgHom) (AdjoinRoot.adjoinRoot_eq_top (f := X ^ n))
    simp only [AlgHom.map_adjoin_singleton, Algebra.map_top] at h
    exact h.trans ((AlgHom.range_eq_top _).mpr (AlgEquiv.toOpposite K _).surjective)
  let M := (i : ι) → ((AdjoinRoot (X ^ n : K[X]))ᵐᵒᵖ ⧸
    Ideal.span {op (AdjoinRoot.root (X ^ n : K[X]) ^ len i)})
  have e := Module.End.centralizerScalarEquiv (M := M) _ hgen
  rw [Set.image_singleton] at e
  rw [e.toLinearEquiv.finrank_eq]
  exact finrank_end_pi_cyclic_root_pow len hlen

/-- The dimension of the centralizer of a sum of nilpotent cyclic blocks is the sum
of the squared column lengths of its block partition. Here column `k` consists of the
blocks whose length exceeds `k`; no ordering of the blocks is required. -/
theorem finrank_centralizer_pi_cyclic_root_pow_eq_sum_sq {ι : Type*} [Fintype ι]
    (len : ι → ℕ) (hlen : ∀ i, len i ≤ n) :
    Module.finrank K (Subalgebra.centralizer K
      {Algebra.lsmul K K
        ((i : ι) → ((AdjoinRoot (X ^ n : K[X]))ᵐᵒᵖ ⧸
          Ideal.span {op (AdjoinRoot.root (X ^ n : K[X]) ^ len i)}))
        (op (AdjoinRoot.root (X ^ n : K[X])))}) =
      ∑ k ∈ Finset.range n, (Finset.univ.filter fun i => k < len i).card ^ 2 := by
  classical
  rw [finrank_centralizer_pi_cyclic_root_pow len hlen]
  exact Finset.sum_sum_min_eq_sum_sq_card_filter Finset.univ len n fun i _ => hlen i

end TauCeti
