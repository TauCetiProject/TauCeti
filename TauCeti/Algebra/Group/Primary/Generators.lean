/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li, The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Generators
public import TauCeti.Algebra.Group.Primary.Decomposition
public import TauCeti.GroupTheory.Rank

/-!
# The generator number of a finite abelian group

The least number of generators of a finite abelian group is the maximum of the least
numbers for its prime-primary components
(`TauCeti.AddCommGroup.spanFinrank_eq_sup_primaryComponents`).
The maximum is taken over the prime divisors of the group order; for the trivial group
this set is empty and the maximum is zero.

For any `n : ℕ` (not necessarily prime), the `n`-primary component `A[n^∞]` is a retract of `A`
because its order is coprime to its index, so its `AddGroup.rank` is at most that of `A`.

## Main results

* `TauCeti.AddCommGroup.spanFinrank_eq_sup_primaryComponents`: the generator number of `A` is the
  supremum over its prime-primary components.
* `TauCeti.AddCommGroup.rank_primaryComponent_le`: the `n`-primary component has `AddGroup.rank`
  at most `AddGroup.rank A`.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.1.
-/

public section

namespace TauCeti.AddCommGroup

/-- The least number of generators of a finite abelian group is the maximum of the
least numbers for its prime-primary components. -/
theorem spanFinrank_eq_sup_primaryComponents (A : Type*) [AddCommGroup A] [Finite A] :
    (⊤ : Submodule ℤ A).spanFinrank =
      Finset.univ.sup (fun p : (Nat.card A).primeFactors ↦
        (⊤ : Submodule ℤ (_root_.AddCommGroup.primaryComponent A p.val)).spanFinrank) := by
  classical
  let M : (Nat.card A).primeFactors → Type _ :=
    fun p ↦ _root_.AddCommGroup.primaryComponent A p.val
  have hcop : Pairwise fun p q ↦ (Nat.card (M p)).Coprime (Nat.card (M q)) := by
    intro p q hpq
    dsimp only [M]
    have hp := Nat.prime_of_mem_primeFactors p.property
    have hq := Nat.prime_of_mem_primeFactors q.property
    rw [natCard_primaryComponent A hp, natCard_primaryComponent A hq]
    exact ((Nat.coprime_primes hp hq).mpr (by simpa using hpq)).pow _ _
  let e : (∀ p, M p) ≃ₗ[ℤ] A := (primaryDecomposition A).toIntLinearEquiv
  have he := Submodule.spanFinrank_map_eq_of_injective e.toLinearMap e.injective
    (p := ⊤)
  rw [Submodule.map_top, LinearEquiv.range] at he
  exact he.trans (spanFinrank_pi_eq_sup_of_coprime_card M hcop)

/-- For any natural number `n`, the `n`-primary component of a finite abelian group `A` has
`AddGroup.rank` at most `AddGroup.rank A`. -/
theorem rank_primaryComponent_le (A : Type*) [AddCommGroup A] [Finite A] (n : ℕ) :
    AddGroup.rank (_root_.AddCommGroup.primaryComponent A n) ≤ AddGroup.rank A := by
  rw [AddGroup.rank_eq_spanFinrank_top, AddGroup.rank_eq_spanFinrank_top]
  set P := _root_.AddCommGroup.primaryComponent A n
  have hcop : (Nat.card P).Coprime P.index :=
    Nat.coprime_of_dvd fun p hp hpP hpI ↦ hp.not_dvd_one <|
      (coprime_index_primaryComponent (A := A) n).gcd_eq_one ▸
        Nat.dvd_gcd hpI (dvd_of_prime_dvd_natCard_primaryComponent hp hpP)
  let π : A →ₗ[ℤ] P :=
    { toFun := fun x ↦ ⟨P.index • x, P.nsmul_index_mem x⟩
      map_add' := fun x y ↦ Subtype.ext (nsmul_add x y P.index)
      map_smul' := fun r x ↦ Subtype.ext (smul_comm P.index r x) }
  have hsurj : Function.Surjective π := fun y ↦ by
    obtain ⟨z, rfl⟩ := hcop.nsmul_right_bijective.surjective y
    exact ⟨z, rfl⟩
  have h := Submodule.spanFinrank_map_le_of_fg π (Module.Finite.fg_top (R := ℤ) (M := A))
  rwa [Submodule.map_top, LinearMap.range_eq_top.mpr hsurj] at h

end TauCeti.AddCommGroup
