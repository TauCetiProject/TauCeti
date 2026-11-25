/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.ProdPow
public import TauCeti.LinearAlgebra.Charpoly.Pi
public import TauCeti.LinearAlgebra.Charpoly.Trace
public import TauCeti.RingTheory.Semisimple.Trace.Basic

import TauCeti.LinearAlgebra.Pi

/-!
# Brauer–Nesbitt: semisimple modules are determined by characteristic polynomials

Let `A` be an algebra over an algebraically closed field `k`, of any characteristic. This file
proves that two finite-dimensional semisimple `A`-modules on which the elements of a spanning set
of `A` act with the same characteristic polynomials are isomorphic
(`IsSemisimpleModule.nonempty_linearEquiv_of_charpoly_eq`). For the monoid algebra `k[G]` and the
spanning set `G`, this is the Brauer–Nesbitt theorem: the characteristic polynomials at the
elements of `G` determine a semisimple representation. In characteristic zero the traces already
suffice (`IsSemisimpleModule.nonempty_linearEquiv_of_trace_eq`); in characteristic `p` they only
determine the multiplicities modulo `p`
(`IsSemisimpleModule.natCast_jordanHolderMultiplicity_eq_of_trace_eq`).

The proof is the classical one. Fix a finite family of pairwise non-isomorphic simple modules
`T_i` covering the simple submodules of both modules (`IsSemisimpleModule.exists_simple_family`).
The characteristic polynomial of `a` on a semisimple module is then
`∏ i, charpoly(a | T_i) ^ [M : T_i]` (`IsSemisimpleModule.charpoly_lsmul_eq_prod`), and its next
coefficient gives the trace. By Burnside's theorem the traces on a spanning set determine the
multiplicities `[M : T_i]` cast into `k` (`IsSemisimpleModule.natCast_eq_of_sum_trace_eq`, in
`TauCeti.RingTheory.Semisimple.Trace.Basic`). Exponent vectors giving the same products of the
monic polynomials `charpoly(a | T_i)` and agreeing in `k` agree
(`Polynomial.eq_of_forall_prod_pow_eq`): in characteristic `p` the products are `p`-th powers
once the common part is cancelled, and Frobenius is injective on `k[X]`.

## Main results

* `IsSemisimpleModule.charpoly_lsmul_eq_prod`: the characteristic polynomial of `a` on a
  semisimple module, computed from the multiplicities of its simple constituents.
* `IsSemisimpleModule.nonempty_linearEquiv_of_charpoly_eq`: **Brauer–Nesbitt.** Semisimple
  modules with the same characteristic polynomials on a spanning set of `A` are isomorphic.

## References

* C. W. Curtis and I. Reiner, *Representation theory of finite groups and associative algebras*,
  Theorem 30.16.
* H. Darmon, F. Diamond and R. Taylor, *Fermat's Last Theorem*, proof of Proposition 2.6.
* G. Chenevier, *The p-adic analytic space of pseudocharacters of a profinite group and
  pseudorepresentations over arbitrary rings*, arXiv:0809.0415v2, end of the proof of
  Theorem 2.12.
-/

public section

open Module Polynomial TauCeti

namespace IsSemisimpleModule

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]

section Decomposition

variable {ι : Type*} [Fintype ι] {T : ι → Type*} [∀ i, AddCommGroup (T i)] [∀ i, Module k (T i)]
  [∀ i, Module A (T i)] [∀ i, IsScalarTower k A (T i)] [∀ i, FiniteDimensional k (T i)]
variable {M : Type*} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  [FiniteDimensional k M] [IsSemisimpleModule A M] [Module.Finite A M]

/-- **The characteristic polynomial on a semisimple module.** If every simple submodule of `M` is
isomorphic to one of the pairwise non-isomorphic modules `T i`, then the characteristic polynomial
of `a` on `M` is `∏ i, charpoly(a | T i) ^ [M : T i]`. -/
theorem charpoly_lsmul_eq_prod (hT : Pairwise fun i j => IsEmpty (T i ≃ₗ[A] T j))
    (hM : ∀ P : Submodule A M, IsSimpleModule A P → ∃ i, Nonempty (P ≃ₗ[A] T i)) (a : A) :
    (Algebra.lsmul k k M a).charpoly =
      ∏ i, (Algebra.lsmul k k (T i) a).charpoly ^ jordanHolderMultiplicity A M (T i) := by
  classical
  obtain ⟨n, σ, ⟨e⟩, hσ⟩ := exists_linearEquiv_pi_natCard_eq hT hM
  rw [← (e.restrictScalars k).charpoly_conj, e.conj_lsmul_eq_piMap, LinearMap.charpoly_piMap,
    ← Finset.prod_fiberwise Finset.univ σ]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.prod_congr rfl fun x hx => by rw [(Finset.mem_filter.1 hx).2], Finset.prod_const,
    ← hσ i, Nat.card_eq_fintype_card, Fintype.card_subtype]

end Decomposition

variable [IsAlgClosed k] {M N : Type*} [AddCommGroup M] [Module k M] [Module A M]
  [IsScalarTower k A M] [FiniteDimensional k M] [IsSemisimpleModule A M] [AddCommGroup N]
  [Module k N] [Module A N] [IsScalarTower k A N] [FiniteDimensional k N] [IsSemisimpleModule A N]

/-- **Brauer–Nesbitt.** Over an algebraically closed field `k` of any characteristic, two
finite-dimensional semisimple modules over a `k`-algebra `A` are isomorphic if the elements of a
spanning set `Set.range g` of `A` act on them with the same characteristic polynomials.

Traces alone do not suffice in characteristic `p`: over an algebraic closure of `𝔽₃`, three copies
of the trivial representation of `ℤ/2` and three copies of the sign representation have equal
traces. -/
theorem nonempty_linearEquiv_of_charpoly_eq {Γ : Type*} {g : Γ → A}
    (hg : Submodule.span k (Set.range g) = ⊤)
    (h : ∀ γ, (Algebra.lsmul k k M (g γ)).charpoly = (Algebra.lsmul k k N (g γ)).charpoly) :
    Nonempty (M ≃ₗ[A] N) := by
  have : Module.Finite A M := Module.Finite.of_restrictScalars_finite k A M
  have : Module.Finite A N := Module.Finite.of_restrictScalars_finite k A N
  obtain ⟨ι, _, T, hTs, hT, hM, hN⟩ := exists_simple_family (R := A) M N
  have (i : ι) : FiniteDimensional k (T i) :=
    .of_injective ((T i).subtype.restrictScalars k) Subtype.val_injective
  have (i : ι) : IsSimpleModule A (T i) := hTs i
  have hmult := eq_of_forall_prod_pow_eq (fun i γ => (Algebra.lsmul k k (T i) (g γ)).charpoly)
    (fun _ _ => (LinearMap.charpoly_monic _).ne_zero)
    (fun c d hcd => natCast_eq_of_sum_trace_eq hT hg c d fun γ => by
      rw [LinearMap.sum_nsmul_trace_eq_neg_nextCoeff_prod,
        LinearMap.sum_nsmul_trace_eq_neg_nextCoeff_prod, hcd γ])
    (fun i => jordanHolderMultiplicity A M (T i)) (fun i => jordanHolderMultiplicity A N (T i))
    fun γ => by rw [← charpoly_lsmul_eq_prod hT hM, ← charpoly_lsmul_eq_prod hT hN, h γ]
  exact nonempty_linearEquiv_of_jordanHolderMultiplicity_eq M N fun S _ _ _ =>
    apply_jordanHolderMultiplicity_eq_of_forall_eq id hM hN (congrFun hmult) S

end IsSemisimpleModule
