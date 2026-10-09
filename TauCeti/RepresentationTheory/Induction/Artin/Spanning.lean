/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Artin
public import TauCeti.RepresentationTheory.Induction.Artin.Modular

/-!
# Modular Artin induction with uniform coefficients

For a finite group `G` and a field of prime characteristic `p`, multiplication by `|G|` on
`G₀(k[G])` is a finite integral linear combination of induction after restriction from cyclic
subgroups of order prime to `p`. One coefficient family works for every virtual class.

This combines Artin's identity over every field with the removal of the prime part of cyclic
subgroups. In particular, it applies when `p` divides `|G|`, without semisimplicity or a
splitting-field hypothesis, and expresses every group-order multiple in the subgroup generated
by such induced classes.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  §VII.3, (7.3.4).
* J.-P. Serre, *Linear Representations of Finite Groups*, Part II, §9.2.
-/

public section

open scoped MonoidAlgebra

namespace TauCeti

universe u

/-- **Modular Artin induction.** A single finitely supported integral coefficient family over
cyclic subgroups of order prime to `p` expresses `|G|` times every virtual class as a sum of its
induced restrictions. -/
theorem exists_linearCombination_indK0_resK0_eq_natCard_nsmul
    {k G : Type u} [Field k] [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] [CharP k p] :
    ∃ a : {D : Subgroup G // IsCyclic D ∧ ¬ p ∣ Nat.card D} →₀ ℤ,
      ∀ x : ExactK0 (finiteModulesExactStructure k[G]),
        Finsupp.linearCombination ℤ
            (fun D : {D : Subgroup G // IsCyclic D ∧ ¬ p ∣ Nat.card D} ↦
              indK0 k D.val (resK0 k D.val.subtype x)) a = Nat.card G • x := by
  obtain ⟨a, ha⟩ := exists_linearCombination_indK0_resK0_eq_sum_artinCoeff (k := k) (G := G) p
  exact ⟨a, fun x ↦ (ha x).trans (natCard_nsmul_eq_sum_artinCoeff_indK0_resK0 k G x).symm⟩

end TauCeti
