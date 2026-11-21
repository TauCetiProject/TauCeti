/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Conj
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Orbit
public import TauCeti.RepresentationTheory.SymmetricAlgebra.Weyl.Coxeter.Element
public import TauCeti.RingTheory.Polynomial.Cyclotomic.Exponents
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import TauCeti.LinearAlgebra.RootSystem.Basic

/-!
# The Coxeter number and the exponents of a Weyl group

Let `b` be a base of a finite irreducible reduced crystallographic root system of rank `r`, on a
finite-dimensional space over an algebraically closed field `K` containing `ℝ`, such as `ℂ`. Let
`c` be a Coxeter element, a product of the `r` simple reflections in some order, and let `h` be
its order, the **Coxeter number**. This file proves:

* the number of roots is `|Φ| = r h`, equivalently `|Φ⁺| = r h / 2`;
* every exponent `dᵢ - 1`, for the degrees `dᵢ` of a homogeneous basic invariant system, is less
  than `h`.

With the computation of the eigenvalues of the bipartite Coxeter element at a regular
eigenvector (`RootPairing.exists_isPrimitiveRoot_charpoly_bipartiteCoxeterElement_eq_prod`), the
second statement says that its eigenvalues are `ζ ^ eᵢ` for a primitive `h`-th root of unity `ζ`,
with exponents `1 ≤ eᵢ < h` (the lower bound is
`RootPairing.two_le_of_injective_aeval_weylGroupRootRep_dual`).

## The argument

For the bipartite Coxeter element `c = c₀ c₁`, where `c₀` and `c₁` are the products of the simple
reflections of the two colours of the Dynkin diagram, `c⁻¹ = c₁ c c₁`. A regular eigenvector `x`
of `c` for a primitive `h`-th root of unity `μ` therefore gives the regular eigenvector `c₁ x`
for `μ⁻¹`, and the eigenvalue computation at both shows that the exponents `eᵢ` modulo `h` are
stable under `e ↦ -e`, with multiplicity. None of them is `0` modulo `h`, as `1` is not an
eigenvalue of `c`, so they pair off and `2 ∑ᵢ (eᵢ % h) = r h`. On the other hand
`∑ᵢ eᵢ = |Φ⁺|`
(`RootPairing.sum_sub_one_eq_ncard_posRoots_of_bijective_aeval_weylGroupRootRep_dual`) and every
`⟨c⟩`-orbit of roots meets the inversion set of `c`, which has `r` elements, within `h` steps,
so `2 |Φ⁺| = |Φ| ≤ r h` (`TauCeti.natCard_le_orderOf_wordProd_mul_length`). As `eᵢ % h ≤ eᵢ`,
all these inequalities are equalities: `|Φ| = r h` and `eᵢ % h = eᵢ`. Since all Coxeter elements
are conjugate, the results hold for every Coxeter element.

## Main results

* `RootPairing.natCard_eq_finrank_mul_orderOf_wordProd`: the number of roots is the rank times the
  order of any Coxeter element.
* `RootPairing.degree_sub_one_lt_orderOf_wordProd`: every exponent `dᵢ - 1` of a homogeneous basic
  invariant system is less than the order of any Coxeter element.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, no. 2.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  §§3.18–3.20.
* T. A. Springer, *Regular elements of finite reflection groups*, Invent. Math. **25** (1974),
  159–198, §4.
-/

public section

open Polynomial SymmetricAlgebra TauCeti TauCeti.SymmetricAlgebra

namespace RootPairing

variable {ι K M N κ : Type*} [Field K] [CharZero K] [Algebra ℝ K] [IsAlgClosed K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  (P : RootPairing ι K M N) [Finite ι] [Nonempty ι] [P.IsCrystallographic] [P.IsReduced]
  [P.IsIrreducible]

/-- The eigenvalues `ζ ^ eᵢ` of the bipartite Coxeter element `c` are stable under inversion,
since `c` and `c⁻¹` are conjugate: there is a primitive `h`-th root of unity `ζ` with
`charpoly c = ∏ᵢ (X - ζ ^ eᵢ) = ∏ᵢ (X - ζ⁻¹ ^ eᵢ)`. -/
private theorem exists_isPrimitiveRoot_charpoly_eq_prod_and_prod_eq_prod_inv
    [FiniteDimensional K M] [Fintype κ]
    (b : P.Base) (c : (coxeterMatrixOfBase P b).graph.Coloring Bool)
    {f : κ → P.weylGroupRootRep.dual.symmetricAlgebraInvariants} {d : κ → ℕ}
    (hf : ∀ k, (f k : SymmetricAlgebra K (Module.Dual K M)) ∈
      homogeneousSubmodule K (Module.Dual K M) (d k))
    (hbij : Function.Bijective (MvPolynomial.aeval (R := K) f)) :
    ∃ ζ : K, IsPrimitiveRoot ζ (orderOf ((weylCoxeterSystem P b).bipartiteCoxeterElement c)) ∧
      (P.weylGroupRootRep ((weylCoxeterSystem P b).bipartiteCoxeterElement c)).charpoly =
        ∏ k, (X - C (ζ ^ (d k - 1))) ∧
      ∏ k, (X - C (ζ ^ (d k - 1))) = ∏ k, (X - C (ζ⁻¹ ^ (d k - 1))) := by
  set cs := weylCoxeterSystem P b
  have := P.finite_weylGroup_of_base b
  obtain ⟨x, μ, hx, hgx, hμ⟩ :=
    P.exists_isRegularWeight_bipartiteCoxeterElement_smul_eq_smul_isPrimitiveRoot b c
  have hμ0 : μ ≠ 0 := hμ.ne_zero (orderOf_pos _).ne'
  -- With `c = A B` for the involutions `A` and `B`, `B x` is an eigenvector of `c` for `μ⁻¹`.
  set A := cs.colorClassProd c true
  set B := cs.colorClassProd c false
  have hAB : cs.bipartiteCoxeterElement c = A * B := cs.bipartiteCoxeterElement_def c
  have hBx : B • x = μ • A • x :=
    calc B • x = A • (A * B) • x := by
          rw [← mul_smul, ← mul_assoc, cs.colorClassProd_mul_self, one_mul]
      _ = A • μ • x := by rw [← hAB, hgx]
      _ = μ • A • x := smul_comm _ _ _
  have hμμ : μ⁻¹ * μ = 1 := inv_mul_cancel₀ hμ0
  have hy : cs.bipartiteCoxeterElement c • B • x = (↑(Units.mk0 μ hμ0)⁻¹ : K) • B • x :=
    calc cs.bipartiteCoxeterElement c • B • x = A • x := by
          rw [hAB, ← mul_smul, mul_assoc, cs.colorClassProd_mul_self, mul_one]
      _ = μ⁻¹ • B • x := by rw [hBx, smul_smul, hμμ, one_smul]
      _ = (↑(Units.mk0 μ hμ0)⁻¹ : K) • B • x := by
          simp only [Units.val_inv_eq_inv_val, Units.val_mk0]
  have h₁ := P.charpoly_weylGroupRootRep_of_isRegularWeight_of_smul_eq b hf hbij
    (c := Units.mk0 μ hμ0) hx hgx
  have h₂ := P.charpoly_weylGroupRootRep_of_isRegularWeight_of_smul_eq b hf hbij
    ((P.isRegularWeight_smul B x).mpr hx) hy
  simp only [inv_inv, Units.val_inv_eq_inv_val, Units.val_mk0] at h₁ h₂
  exact ⟨μ, hμ, h₂, h₂.symm.trans h₁⟩

/-- The two results of this file for the bipartite Coxeter element: `|Φ| = r h` and `eᵢ < h`. -/
private theorem natCard_eq_and_degree_sub_one_lt_orderOf_bipartiteCoxeterElement
    [FiniteDimensional K M] [Finite κ]
    (b : P.Base) (c : (coxeterMatrixOfBase P b).graph.Coloring Bool)
    {f : κ → P.weylGroupRootRep.dual.symmetricAlgebraInvariants} {d : κ → ℕ}
    (hf : ∀ k, (f k : SymmetricAlgebra K (Module.Dual K M)) ∈
      homogeneousSubmodule K (Module.Dual K M) (d k))
    (hbij : Function.Bijective (MvPolynomial.aeval (R := K) f)) :
    Nat.card ι =
        Module.finrank K M * orderOf ((weylCoxeterSystem P b).bipartiteCoxeterElement c) ∧
      ∀ k, d k - 1 < orderOf ((weylCoxeterSystem P b).bipartiteCoxeterElement c) := by
  classical
  have := Fintype.ofFinite κ
  set g := (weylCoxeterSystem P b).bipartiteCoxeterElement c
  have := P.finite_weylGroup_of_base b
  have : NeZero (orderOf g) := ⟨(orderOf_pos g).ne'⟩
  obtain ⟨ζ, hζ, hchar, hsym⟩ :=
    P.exists_isPrimitiveRoot_charpoly_eq_prod_and_prod_eq_prod_inv b c hf hbij
  obtain ⟨l₁, l₂, -, -, hnd, hall, hw⟩ :=
    (weylCoxeterSystem P b).exists_wordProd_eq_bipartiteCoxeterElement c
  rw [weylCoxeterSystem_wordProd] at hw
  -- No exponent is divisible by `h`, since `1` is not an eigenvalue of `c`.
  have hdvd (k : κ) : ¬ orderOf g ∣ d k - 1 := fun hk ↦ by
    refine not_hasEigenvalue_one_wordProd b hnd hall ?_
    rw [hw, Module.End.hasEigenvalue_iff_isRoot_charpoly, hchar, IsRoot.def, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [(hζ.pow_eq_one_iff_dvd _).2 hk])
  have hpair := hζ.two_mul_sum_mod_eq_mul_card hdvd hsym
  have hcard : Fintype.card κ = Module.finrank K M := by
    rw [← Nat.card_eq_fintype_card,
      P.natCard_eq_finrank_of_bijective_aeval_weylGroupRootRep_dual hbij]
  have hlen : (l₁ ++ l₂).length = Module.finrank K M := by
    rw [Module.finrank_eq_card_basis b.toWeightBasis, ← List.toFinset_card_of_nodup hnd,
      Finset.eq_univ_iff_forall.mpr fun i ↦ List.mem_toFinset.mpr (hall i), Finset.card_univ]
  have hle := natCard_le_orderOf_wordProd_mul_length b hnd hall
  rw [hw, hlen] at hle
  have hsum := P.sum_sub_one_eq_ncard_posRoots_of_bijective_aeval_weylGroupRootRep_dual b hf hbij
  have htwo := two_mul_ncard_posRoots P b
  have hmod : ∑ k, (d k - 1) % orderOf g ≤ ∑ k, (d k - 1) :=
    Finset.sum_le_sum fun k _ ↦ Nat.mod_le _ _
  rw [hcard] at hpair
  -- `2 ∑ (eᵢ % h) = r h ≥ |Φ| = 2 ∑ eᵢ ≥ 2 ∑ (eᵢ % h)`, so all are equal.
  have heq : ∑ k, (d k - 1) % orderOf g = ∑ k, (d k - 1) := by
    rw [mul_comm] at hle
    linarith
  refine ⟨by rw [mul_comm]; linarith, fun k ↦ ?_⟩
  have := (Finset.sum_eq_sum_iff_of_le fun k _ ↦ Nat.mod_le (d k - 1) (orderOf g)).mp heq k
    (Finset.mem_univ k)
  rw [← this]
  exact Nat.mod_lt _ (orderOf_pos g)

/-- **The Coxeter number is the number of roots divided by the rank.** For a base of a finite
irreducible reduced crystallographic root system over an algebraically closed field containing
`ℝ`, the number of roots is the rank `r` times the order `h`
of any Coxeter element, a product of all the simple reflections, each exactly once. Equivalently
(`TauCeti.two_mul_ncard_posRoots`), there are `r h / 2` positive roots. -/
theorem natCard_eq_finrank_mul_orderOf_wordProd (b : P.Base) {l : List b.support}
    (hl : l.Nodup) (hl' : ∀ i, i ∈ l) :
    Nat.card ι = Module.finrank K M * orderOf (wordProd P b l) := by
  have := P.finite_weight_of_isRootSystem
  obtain ⟨f, hfd, hbij⟩ := P.exists_bijective_aeval_weylGroupRootRep_dual_of_base b
  choose d _ hd using hfd
  obtain ⟨c⟩ := nonempty_coloring_graph_coxeterMatrixOfBase P b
  rw [← P.orderOf_bipartiteCoxeterElement_eq_orderOf_wordProd b c hl hl']
  exact (P.natCard_eq_and_degree_sub_one_lt_orderOf_bipartiteCoxeterElement b c hd hbij).1

/-- **The exponents are less than the Coxeter number.** For a base of a finite irreducible reduced
crystallographic root system over an algebraically closed field containing `ℝ`, every exponent
`d k - 1` of a finite homogeneous basic invariant system of `Sym(M*)^W` is less than the order of
any Coxeter element. -/
theorem degree_sub_one_lt_orderOf_wordProd [Finite κ] (b : P.Base) {l : List b.support}
    (hl : l.Nodup) (hl' : ∀ i, i ∈ l)
    {f : κ → P.weylGroupRootRep.dual.symmetricAlgebraInvariants} {d : κ → ℕ}
    (hf : ∀ k, (f k : SymmetricAlgebra K (Module.Dual K M)) ∈
      homogeneousSubmodule K (Module.Dual K M) (d k))
    (hbij : Function.Bijective (MvPolynomial.aeval (R := K) f)) (k : κ) :
    d k - 1 < orderOf (wordProd P b l) := by
  have := P.finite_weight_of_isRootSystem
  obtain ⟨c⟩ := nonempty_coloring_graph_coxeterMatrixOfBase P b
  rw [← P.orderOf_bipartiteCoxeterElement_eq_orderOf_wordProd b c hl hl']
  exact (P.natCard_eq_and_degree_sub_one_lt_orderOf_bipartiteCoxeterElement b c hf hbij).2 k

end RootPairing
