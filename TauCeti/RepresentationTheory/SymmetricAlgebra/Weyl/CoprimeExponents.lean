/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.Complex
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.ActsBy
public import TauCeti.RepresentationTheory.SymmetricAlgebra.Weyl.Invariants
public import TauCeti.RingTheory.Polynomial.Cyclotomic.Exponents
import Mathlib.LinearAlgebra.Eigenspace.Charpoly

/-!
# Regular Weyl eigenvalues and coprime exponents

Let `P` be a finite reduced crystallographic root system over a field `K` of characteristic zero,
with a base `b`, and let `d k` be the degrees of a homogeneous basic invariant system of the Weyl
group `W` acting on the polynomial functions `Sym(M*)`. Suppose that `w ∈ W` has a regular
eigenvector `x` (one lying on no root hyperplane) whose eigenvalue `ζ` is a primitive `h`-th root
of unity. Springer's calculation
(`RootPairing.charpoly_weylGroupRootRep_of_isRegularWeight_of_smul_eq`) gives the characteristic
polynomial of `w` acting on `M` as `∏ k, (X - ζ⁻¹ ^ (d k - 1))`.

The point of this file is that `w` acts on the simple roots by an integer matrix
(`RootPairing.Base.exists_charpoly_weylGroupRootRep_eq_map`), so this characteristic polynomial
is rational, and its roots are closed under Galois conjugation. Hence the primitive root `ζ⁻¹` in
Springer's formula may be replaced by any primitive `h`-th root of unity `ξ`:

`charpoly w = ∏ k, (X - ξ ^ (d k - 1))`.

Over `ℂ`, taking `ξ = exp(2πi / h)` says that the eigenvalues of `w` are the numbers
`exp(2πi (d k - 1) / h)`, with multiplicity. Since `ζ` itself is an eigenvalue, the cyclotomic
argument `IsPrimitiveRoot.exists_eq_of_isRoot_of_map_eq_prod` also gives the **coprime exponent
theorem**: if the exponents `d k - 1` are less than `h`, then every residue less than `h` and
coprime to `h` is one of them.

These statements do not construct the regular eigenvector. For a Coxeter element of an
irreducible root system, with `h` its order, that construction is the remaining input to the
classical theorem that the eigenvalues of a Coxeter element are `exp(2πi eᵢ / h)` for the
exponents `eᵢ = dᵢ - 1`, and that every integer coprime to `h` between `1` and `h - 1` is an
exponent. Crystallographicity is essential: the noncrystallographic group `H₃` has Coxeter number
`10` and exponents `1, 5, 9`, so the coprime residues `3` and `7` do not occur.

## Main results

* `RootPairing.charpoly_weylGroupRootRep_of_isRegularWeight_of_isPrimitiveRoot`: at a regular
  eigenvector with primitive `h`-th root eigenvalue, the characteristic polynomial of `w` is
  `∏ k, (X - ξ ^ (d k - 1))` for every primitive `h`-th root of unity `ξ`.
* `RootPairing.charpoly_weylGroupRootRep_eq_prod_exp`: over `ℂ`, the eigenvalues of `w` are
  `exp(2πi (d k - 1) / h)`.
* `RootPairing.exists_degree_sub_one_eq_of_isRegularWeight_of_isPrimitiveRoot`: the coprime
  exponent theorem, for exponents less than `h`.

## References

* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge (1990), §§3.17–3.20.
* T. A. Springer, *Regular elements of finite reflection groups*, Invent. Math. **25** (1974),
  159–198, §4.
-/

public section

open Polynomial SymmetricAlgebra TauCeti TauCeti.SymmetricAlgebra

namespace RootPairing

section Field

variable {ι K M N κ : Type*} [Field K] [CharZero K] [AddCommGroup M] [Module K M]
  [FiniteDimensional K M] [AddCommGroup N] [Module K N] (P : RootPairing ι K M N)
  [Finite ι] [P.IsCrystallographic] [P.IsReduced] [P.IsRootSystem] [Fintype κ]

omit [CharZero K] [FiniteDimensional K M] [Finite ι] [P.IsCrystallographic] [P.IsReduced]
  [P.IsRootSystem] in
/-- If there is a root, a regular weight with `w • x = ζ • x` is an eigenvector of `w` for the
eigenvalue `ζ`. -/
private lemma hasEigenvector_of_isRegularWeight [Nonempty ι] {w : P.weylGroup} {x : M} {ζ : K}
    (hx : P.IsRegularWeight x) (hw : w • x = ζ • x) :
    Module.End.HasEigenvector (P.weylGroupRootRep w) ζ x :=
  Module.End.hasEigenvector_iff.mpr
    ⟨Module.End.mem_eigenspace_iff.mpr ((P.weylGroupRootRep_apply w x).trans hw), hx.ne_zero⟩

omit [FiniteDimensional K M] in
/-- If a regular weight is an eigenvector of a Weyl-group element for a primitive `h`-th root of
unity, then `h` is positive, unless there are no roots at all. -/
private lemma pos_or_finrank_eq_zero (b : P.Base) {w : P.weylGroup} {x : M} {ζ : K} {h : ℕ}
    (hx : P.IsRegularWeight x) (hw : w • x = ζ • x) (hζ : IsPrimitiveRoot ζ h) :
    0 < h ∨ Module.finrank K M = 0 := by
  rcases isEmpty_or_nonempty ι with hι | _
  · -- With no roots, the roots span the zero subspace, which is the whole weight space.
    refine Or.inr ?_
    rw [← finrank_top, ← IsRootSystem.span_root_eq_top (P := P), Set.range_eq_empty,
      Submodule.span_empty, finrank_bot]
  refine Or.inl (Nat.pos_of_ne_zero fun h0 ↦ ?_)
  have : Finite P.weylGroup := P.finite_weylGroup_of_base b
  -- The eigenvalue is a root of unity of order dividing the order of `w`.
  have hv := P.hasEigenvector_of_isRegularWeight hx hw
  have hpow := hv.pow_apply (orderOf w)
  rw [← map_pow, pow_orderOf_eq_one, map_one, one_apply_eq_self] at hpow
  have hζn : ζ ^ orderOf w = 1 := smul_left_injective K hv.2 (by simpa using hpow.symm)
  subst h0
  exact (orderOf_pos w).ne' (Nat.eq_zero_of_zero_dvd (hζ.dvd_of_pow_eq_one _ hζn))

omit [P.IsRootSystem] in
/-- On a zero-dimensional weight space, a basic invariant system is empty and the characteristic
polynomial of every Weyl-group element is `1`, so it equals every product over the invariants. -/
private lemma charpoly_eq_prod_of_finrank_eq_zero (b : P.Base)
    {f : κ → P.weylGroupRootRep.dual.symmetricAlgebraInvariants}
    (hbij : Function.Bijective (MvPolynomial.aeval (R := K) f))
    (hM : Module.finrank K M = 0) (w : P.weylGroup) (g : κ → K[X]) :
    (P.weylGroupRootRep w).charpoly = ∏ k, g k := by
  have : Finite P.weylGroup := P.finite_weylGroup_of_base b
  have hκ := P.natCard_eq_finrank_of_bijective_aeval_weylGroupRootRep_dual hbij
  rw [hM, Nat.card_eq_fintype_card, Fintype.card_eq_zero_iff] at hκ
  rw [Finset.univ_eq_empty, Finset.prod_empty]
  exact eq_one_of_monic_natDegree_zero (P.weylGroupRootRep w).charpoly_monic
    (by rw [LinearMap.charpoly_natDegree, hM])

/-- **Galois conjugates of a regular Weyl eigenvalue.** For a base `b` of a finite reduced
crystallographic root system over a field of characteristic zero, let `d k` be the degrees of a
finite homogeneous basic invariant system of `Sym(M*)^W`. If `x ∈ M` is a regular weight with
`w • x = ζ • x` for a primitive `h`-th root of unity `ζ`, then the characteristic polynomial of `w`
acting on `M` is `∏ k, (X - ξ ^ (d k - 1))` for every primitive `h`-th root of unity `ξ`. -/
theorem charpoly_weylGroupRootRep_of_isRegularWeight_of_isPrimitiveRoot (b : P.Base)
    {f : κ → P.weylGroupRootRep.dual.symmetricAlgebraInvariants} {d : κ → ℕ}
    (hf : ∀ k, (f k : SymmetricAlgebra K (Module.Dual K M)) ∈
      homogeneousSubmodule K (Module.Dual K M) (d k))
    (hbij : Function.Bijective (MvPolynomial.aeval (R := K) f))
    {w : P.weylGroup} {x : M} {ζ ξ : K} {h : ℕ} (hx : P.IsRegularWeight x)
    (hw : w • x = ζ • x) (hζ : IsPrimitiveRoot ζ h) (hξ : IsPrimitiveRoot ξ h) :
    (P.weylGroupRootRep w).charpoly = ∏ k, (X - C (ξ ^ (d k - 1))) := by
  rcases P.pos_or_finrank_eq_zero b hx hw hζ with hh | hM
  swap
  · exact P.charpoly_eq_prod_of_finrank_eq_zero b hbij hM w _
  -- Springer's formula, with the primitive root `ζ⁻¹`.
  have hc := P.charpoly_weylGroupRootRep_of_isRegularWeight_of_smul_eq b hf hbij
    (c := Units.mk0 ζ (hζ.ne_zero hh.ne')) hx hw
  rw [Units.val_inv_eq_inv_val, Units.val_mk0] at hc
  -- The characteristic polynomial is rational, so the primitive root can be changed.
  obtain ⟨q, hq⟩ := b.exists_charpoly_weylGroupRootRep_eq_map_rat w
  rw [← hq] at hc ⊢
  exact hζ.inv.map_eq_prod_of_map_eq_prod hh hξ hc

omit [Fintype κ] in
/-- **The coprime exponent theorem at a regular Weyl eigenvector.** For a base `b` of a finite
reduced crystallographic root system with at least one root, over a field of characteristic zero,
let `d k` be the degrees of a finite homogeneous basic invariant system of `Sym(M*)^W`. If `x ∈ M`
is a regular weight with `w • x = ζ • x` for a primitive `h`-th root of unity `ζ`, and every
exponent `d k - 1` is less than `h`, then every `a < h` coprime to `h` is one of the exponents. -/
theorem exists_degree_sub_one_eq_of_isRegularWeight_of_isPrimitiveRoot [Nonempty ι] [Finite κ]
    (b : P.Base)
    {f : κ → P.weylGroupRootRep.dual.symmetricAlgebraInvariants} {d : κ → ℕ}
    (hf : ∀ k, (f k : SymmetricAlgebra K (Module.Dual K M)) ∈
      homogeneousSubmodule K (Module.Dual K M) (d k))
    (hbij : Function.Bijective (MvPolynomial.aeval (R := K) f))
    {w : P.weylGroup} {x : M} {ζ : K} {h : ℕ} (hx : P.IsRegularWeight x)
    (hw : w • x = ζ • x) (hζ : IsPrimitiveRoot ζ h) (hd : ∀ k, d k - 1 < h)
    {a : ℕ} (ha : a < h) (hcop : a.Coprime h) : ∃ k, d k - 1 = a := by
  have : Fintype κ := Fintype.ofFinite κ
  obtain ⟨q, hq⟩ := b.exists_charpoly_weylGroupRootRep_eq_map_rat w
  -- The eigenvalue `ζ` is a root of the rational characteristic polynomial.
  have hroot : (q.map (algebraMap ℚ K)).IsRoot ζ := by
    rw [hq, ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
    exact Module.End.hasEigenvalue_of_hasEigenvector (P.hasEigenvector_of_isRegularWeight hx hw)
  exact hζ.exists_eq_of_isRoot_of_map_eq_prod hζ hroot hd
    (hq.trans (P.charpoly_weylGroupRootRep_of_isRegularWeight_of_isPrimitiveRoot b hf hbij hx hw
      hζ hζ)) ha hcop

end Field

section Complex

open Complex in
/-- **The eigenvalues at a regular Weyl eigenvector are `exp(2πi (d k - 1) / h)`.** For a base `b`
of a finite reduced crystallographic root system over `ℂ`, let `d k` be the degrees of a finite
homogeneous basic invariant system of `Sym(M*)^W`. If `x ∈ M` is a regular weight with
`w • x = ζ • x` for a primitive `h`-th root of unity `ζ`, then the characteristic polynomial of `w`
acting on `M` is `∏ k, (X - exp(2πi (d k - 1) / h))`. -/
theorem charpoly_weylGroupRootRep_eq_prod_exp {ι M N κ : Type*} [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] [AddCommGroup N] [Module ℂ N] (P : RootPairing ι ℂ M N)
    [Finite ι] [P.IsCrystallographic] [P.IsReduced] [P.IsRootSystem] [Fintype κ] (b : P.Base)
    {f : κ → P.weylGroupRootRep.dual.symmetricAlgebraInvariants} {d : κ → ℕ}
    (hf : ∀ k, (f k : SymmetricAlgebra ℂ (Module.Dual ℂ M)) ∈
      homogeneousSubmodule ℂ (Module.Dual ℂ M) (d k))
    (hbij : Function.Bijective (MvPolynomial.aeval (R := ℂ) f))
    {w : P.weylGroup} {x : M} {ζ : ℂ} {h : ℕ} (hx : P.IsRegularWeight x)
    (hw : w • x = ζ • x) (hζ : IsPrimitiveRoot ζ h) :
    (P.weylGroupRootRep w).charpoly =
      ∏ k, (X - C (exp (2 * Real.pi * I * ((d k - 1 : ℕ) : ℂ) / h))) := by
  rcases P.pos_or_finrank_eq_zero b hx hw hζ with hh | hM
  swap
  · exact P.charpoly_eq_prod_of_finrank_eq_zero b hbij hM w _
  rw [P.charpoly_weylGroupRootRep_of_isRegularWeight_of_isPrimitiveRoot b hf hbij hx hw hζ
    (isPrimitiveRoot_exp h hh.ne')]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [← exp_natCast_mul]
  congr 3
  ring

end Complex

end RootPairing
