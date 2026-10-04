/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Induction
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.PowerOrder
public import TauCeti.GroupTheory.SpecificGroups.Cyclic.CoprimePart
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Permutation classes of quotients of prime-power exponent

Let `k` have characteristic `p`. If `D` is a normal subgroup of a finite group `C` and every
element of `C` has a `p`-power power in `D`, the permutation module `k[C/D]`, regarded as a
`C`-module, has exact Grothendieck class `[C : D] • [k]`. This equality uses short exact
sequences and includes permutation modules which are not direct sums of trivial lines.

For a finite cyclic subgroup `C`, its subgroup of order prime to `p` satisfies these hypotheses.

Inducing to a finite group `G` containing `C`, and using that `Ind_C^G k[C/D] = k[G/D]`
(`TauCeti.indK0_of_ofMulAction_quotient`), turns this into an equality of induced classes:
`[Ind_D^G k] = [C : D] • [Ind_C^G k]` (`TauCeti.indK0_of_trivial_eq_relIndex_nsmul`). For a cyclic
`C` this says that the `p`-part of `|C|` times the class of `Ind_C^G k` is the class induced from
the trivial line of the subgroup of `C` of order prime to `p`
(`TauCeti.exists_coprimePart_indK0_of_trivial_eq_nsmul`); this is the input that removes the
`p`-part of a cyclic subgroup in modular Artin induction.

The class computation uses
`TauCeti.exactK0_asModule_eq_finrank_nsmul_of_forall_pow_eq_one`; the cyclic subgroup is supplied
by `TauCeti.exists_coprimePart_of_isCyclic`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., §VII.3,
  (7.3.4).
* J.-P. Serre, *Linear Representations of Finite Groups*, Part III, §14.
-/

public section

open scoped MonoidAlgebra ModuleCat

namespace TauCeti

universe u

variable {k G : Type u} [Field k] [Group G]
  (p : ℕ) [Fact p.Prime] [CharP k p]

/-- A normal quotient of `p`-power exponent has permutation class equal to its cardinality
times the trivial class, in the exact Grothendieck group of the original group. -/
theorem exactK0_ofMulAction_quotient_eq_index_nsmul [Finite G]
    (D : Subgroup G) [D.Normal]
    (hpow : ∀ g : G, ∃ n : ℕ, g ^ p ^ n ∈ D) :
    letI : Module.Finite k[G] (Representation.ofMulAction k G (G ⧸ D)).asModule :=
      Module.Finite.of_restrictScalars_finite k k[G] _
    (ExactK0.of (FGModuleCat.of k[G] (Representation.ofMulAction k G (G ⧸ D)).asModule) :
      ExactK0 (finiteModulesExactStructure k[G])) =
        D.index • ExactK0.of (FGModuleCat.of k[G] (Representation.trivial k G k).asModule) := by
  classical
  let := Fintype.ofFinite (G ⧸ D)
  have hρ : ∀ g : G, ∃ n : ℕ,
      Representation.ofMulAction k G (G ⧸ D) g ^ p ^ n = 1 := by
    intro g
    obtain ⟨n, hn⟩ := hpow g
    refine ⟨n, ?_⟩
    rw [← map_pow]
    apply (MonoidAlgebra.basis (G ⧸ D) k).ext
    intro q
    simp only [MonoidAlgebra.basis_apply, Representation.ofMulAction_single,
      Module.End.one_apply]
    congr 1
    induction q using Quotient.inductionOn with
    | h x =>
      rw [MulAction.Quotient.smul_mk]
      apply QuotientGroup.eq.mpr
      simpa [mul_inv_rev, mul_assoc] using
        (inferInstance : D.Normal).conj_mem (g ^ p ^ n)⁻¹ (D.inv_mem hn) x⁻¹
  have h := exactK0_asModule_eq_finrank_nsmul_of_forall_pow_eq_one p
    (Representation.ofMulAction k G (G ⧸ D)) hρ
  rwa [Module.finrank_eq_card_basis (MonoidAlgebra.basis (G ⧸ D) k),
    Fintype.card_eq_nat_card, ← D.index_eq_card] at h

/-- A finite cyclic subgroup has a subgroup of order prime to `p` whose coset permutation
module, as a module for the cyclic subgroup, has class equal to the `p`-part of its order
times the trivial class. -/
theorem exists_coprimePart_exactK0_ofMulAction_eq_nsmul
    (C : Subgroup G) [Finite C] [IsCyclic C] :
    ∃ D : Subgroup G, D ≤ C ∧ (D.subgroupOf C).Normal ∧ ¬ p ∣ Nat.card D ∧
      D.relIndex C = p ^ (Nat.card C).factorization p ∧
      (letI : Module.Finite k[C]
          (Representation.ofMulAction k C (C ⧸ D.subgroupOf C)).asModule :=
        Module.Finite.of_restrictScalars_finite k k[C] _
      (ExactK0.of (FGModuleCat.of k[C]
          (Representation.ofMulAction k C (C ⧸ D.subgroupOf C)).asModule) :
        ExactK0 (finiteModulesExactStructure k[C])) =
          (p ^ (Nat.card C).factorization p) •
            ExactK0.of (FGModuleCat.of k[C] (Representation.trivial k C k).asModule)) := by
  obtain ⟨D, hDC, hDn, hDp, hpow, hindex⟩ :=
    exists_coprimePart_of_isCyclic (Fact.out : p.Prime) (C := C)
  let := hDn
  refine ⟨D, hDC, hDn, hDp, hindex, ?_⟩
  have hpow' : ∀ c : C, ∃ n : ℕ, c ^ p ^ n ∈ D.subgroupOf C := by
    intro c
    obtain ⟨n, hn⟩ := hpow c c.property
    exact ⟨n, hn⟩
  have h := exactK0_ofMulAction_quotient_eq_index_nsmul (k := k) p (D.subgroupOf C) hpow'
  rwa [← Subgroup.relIndex, hindex] at h

/-- **Inducing across a quotient of `p`-power exponent.** Let `D ≤ C` be subgroups of a finite
group `G`, with `D` normal in `C` and every element of `C` having a `p`-power power in `D`. Then
inducing the trivial line from `D` gives `[C : D]` times the class induced from `C`:
`[Ind_D^G k] = [C : D] • [Ind_C^G k]` in the exact Grothendieck group of `G`. -/
theorem indK0_of_trivial_eq_relIndex_nsmul [Finite G] {C D : Subgroup G} (h : D ≤ C)
    [(D.subgroupOf C).Normal] (hpow : ∀ c ∈ C, ∃ n : ℕ, c ^ p ^ n ∈ D) :
    letI : Module.Finite k[D] (Representation.trivial k D k).asModule :=
      Module.Finite.of_restrictScalars_finite k k[D] _
    letI : Module.Finite k[C] (Representation.trivial k C k).asModule :=
      Module.Finite.of_restrictScalars_finite k k[C] _
    indK0 k D (ExactK0.of (FGModuleCat.of k[D] (Representation.trivial k D k).asModule)) =
      D.relIndex C •
        indK0 k C (ExactK0.of (FGModuleCat.of k[C] (Representation.trivial k C k).asModule)) := by
  have hpow' : ∀ c : C, ∃ n : ℕ, c ^ p ^ n ∈ D.subgroupOf C := fun c ↦ hpow c c.property
  rw [← map_nsmul, Subgroup.relIndex,
    ← exactK0_ofMulAction_quotient_eq_index_nsmul p (D.subgroupOf C) hpow',
    indK0_of_ofMulAction_quotient k C h, indK0_of_trivial, permK0_def]

/-- A finite cyclic subgroup `C` has a subgroup `D` of order prime to `p` such that inducing the
trivial line from `D` gives the `p`-part of `|C|` times the class induced from `C`. -/
theorem exists_coprimePart_indK0_of_trivial_eq_nsmul [Finite G] (C : Subgroup G) [IsCyclic C] :
    ∃ D : Subgroup G, D ≤ C ∧ ¬ p ∣ Nat.card D ∧
      D.relIndex C = p ^ (Nat.card C).factorization p ∧
      (letI : Module.Finite k[D] (Representation.trivial k D k).asModule :=
        Module.Finite.of_restrictScalars_finite k k[D] _
      letI : Module.Finite k[C] (Representation.trivial k C k).asModule :=
        Module.Finite.of_restrictScalars_finite k k[C] _
      indK0 k D (ExactK0.of (FGModuleCat.of k[D] (Representation.trivial k D k).asModule)) =
        (p ^ (Nat.card C).factorization p) • indK0 k C
          (ExactK0.of (FGModuleCat.of k[C] (Representation.trivial k C k).asModule))) := by
  obtain ⟨D, hDC, hDn, hDp, hpow, hindex⟩ :=
    exists_coprimePart_of_isCyclic (Fact.out : p.Prime) (C := C)
  let := hDn
  refine ⟨D, hDC, hDp, hindex, ?_⟩
  rw [← hindex]
  exact indK0_of_trivial_eq_relIndex_nsmul (k := k) p hDC hpow

end TauCeti
