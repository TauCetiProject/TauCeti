/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Regular
public import TauCeti.RepresentationTheory.SymmetricAlgebra.Weyl.Invariants

/-!
# Invariant degrees and the eigenvalues of the bipartite Coxeter element

Let `b` be a base of a finite irreducible reduced crystallographic root system on a
finite-dimensional space over a field `K` which contains `ℝ` and is algebraically closed, such as
`ℂ`. Let `c` be a bipartite Coxeter element, of order `h`, and let `d₁, …, dₙ` be the degrees of a
homogeneous basic invariant system of the polynomial functions. Then there is a primitive `h`-th
root of unity `ζ` such that the characteristic polynomial of `c` is `∏ᵢ (X - ζ ^ (dᵢ - 1))`: the
eigenvalues of `c`, with multiplicity, are the powers of `ζ` by the exponents `dᵢ - 1`.

This combines Steinberg's regular eigenvector of `c`, whose eigenvalue is a primitive `h`-th root
of unity
(`RootPairing.exists_isRegularWeight_bipartiteCoxeterElement_smul_eq_smul_isPrimitiveRoot`), with
Springer's computation of the characteristic polynomial at a regular eigenvector
(`RootPairing.charpoly_weylGroupRootRep_of_isRegularWeight_of_smul_eq`). The statement does not
say which primitive root `ζ` is; over `ℂ` it is some `exp (2πi k / h)` with `k` coprime to `h`.

## Main results

* `RootPairing.exists_isPrimitiveRoot_charpoly_bipartiteCoxeterElement_eq_prod`: the characteristic
  polynomial of the bipartite Coxeter element is `∏ᵢ (X - ζ ^ (dᵢ - 1))` for a primitive root of
  unity `ζ` of order the order of the element.

## References

* R. Steinberg, *Finite reflection groups*, Trans. Amer. Math. Soc. **91** (1959), 493–504.
* T. A. Springer, *Regular elements of finite reflection groups*, Invent. Math. **25** (1974),
  159–198, §4.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  §§3.17–3.19.
-/

public section

open Polynomial SymmetricAlgebra TauCeti TauCeti.SymmetricAlgebra

namespace RootPairing

variable {ι K M N κ : Type*} [Field K] [CharZero K] [Algebra ℝ K] [IsAlgClosed K]
  [AddCommGroup M] [Module K M] [FiniteDimensional K M] [AddCommGroup N] [Module K N]
  (P : RootPairing ι K M N) [Finite ι] [Nonempty ι] [P.IsCrystallographic] [P.IsReduced]
  [P.IsIrreducible]

/-- **The eigenvalues of the bipartite Coxeter element are powers of a primitive root of unity by
the exponents.** For a base `b` of a finite irreducible reduced crystallographic root system on a
finite-dimensional space over an algebraically closed field `K` containing `ℝ`, and any colouring
of its Dynkin diagram, let `c` be the bipartite Coxeter element. For the degrees `d k` of any
finite homogeneous basic invariant system of `Sym(M*)^W`, there is a primitive root of unity `ζ`
of order the order of `c` with `charpoly c = ∏ k, (X - ζ ^ (d k - 1))`. -/
theorem exists_isPrimitiveRoot_charpoly_bipartiteCoxeterElement_eq_prod [Fintype κ]
    (b : P.Base) (c : (coxeterMatrixOfBase P b).graph.Coloring Bool)
    {f : κ → P.weylGroupRootRep.dual.symmetricAlgebraInvariants} {d : κ → ℕ}
    (hf : ∀ k, (f k : SymmetricAlgebra K (Module.Dual K M)) ∈
      homogeneousSubmodule K (Module.Dual K M) (d k))
    (hbij : Function.Bijective (MvPolynomial.aeval (R := K) f)) :
    ∃ ζ : K, IsPrimitiveRoot ζ (orderOf ((weylCoxeterSystem P b).bipartiteCoxeterElement c)) ∧
      (P.weylGroupRootRep ((weylCoxeterSystem P b).bipartiteCoxeterElement c)).charpoly =
        ∏ k, (X - C (ζ ^ (d k - 1))) := by
  have := P.finite_weylGroup_of_base b
  obtain ⟨x, μ, hx, hgx, hμ⟩ :=
    P.exists_isRegularWeight_bipartiteCoxeterElement_smul_eq_smul_isPrimitiveRoot b c
  have hμ0 : μ ≠ 0 := hμ.ne_zero (orderOf_pos _).ne'
  refine ⟨μ⁻¹, hμ.inv, ?_⟩
  have h := P.charpoly_weylGroupRootRep_of_isRegularWeight_of_smul_eq b hf hbij
    (c := Units.mk0 μ hμ0) hx hgx
  simpa only [Units.val_inv_eq_inv_val, Units.val_mk0] using h

end RootPairing
