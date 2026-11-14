/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li, The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import TauCeti.Algebra.Group.Generators
public import TauCeti.Algebra.Group.Primary.Decomposition
public import TauCeti.GroupTheory.Rank
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The generator number of a finite abelian group

The least number of generators of a finite abelian group is the maximum of the least
numbers for its prime-primary components. We record both the `ℤ`-submodule formulation
`(⊤ : Submodule ℤ A).spanFinrank` and the group-theoretic formulation `AddGroup.rank A`
(bridged by `AddGroup.rank_eq_spanFinrank_top`), without introducing another invariant.
The maximum is taken over the prime divisors of the group order; for the trivial group
this set is empty and the maximum is zero.

For any `n : ℕ` (not necessarily prime), the `n`-primary component `A[n^∞]` is a retract of `A`
because its order is coprime to its index, so its generator number is at most that of `A`. On a
finite product `∏ᵢ ℤ/pᵏⁱ`, the generator number is `#{i | kᵢ ≠ 0}`.

## Main results

* `TauCeti.AddCommGroup.spanFinrank_eq_sup_primaryComponents`,
  `TauCeti.AddCommGroup.rank_eq_sup_primaryComponents`: the generator number of `A` is the
  supremum over its prime-primary components.
* `TauCeti.AddCommGroup.spanFinrank_primaryComponent_le`,
  `TauCeti.AddCommGroup.rank_primaryComponent_le`: the `n`-primary component needs no more
  generators than `A`.
* `TauCeti.AddCommGroup.spanFinrank_pi_zmod_pow`,
  `TauCeti.AddCommGroup.rank_pi_zmod_pow`: the generator number of `∏ᵢ ℤ/pᵏⁱ` is `#{i | kᵢ ≠ 0}`.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.1.
-/

public section

open Finset

namespace TauCeti.AddCommGroup

/-- The least number of generators of a finite abelian group is the maximum of the
least numbers for its prime-primary components. -/
theorem spanFinrank_eq_sup_primaryComponents (A : Type*) [AddCommGroup A] [Finite A] :
    (⊤ : Submodule ℤ A).spanFinrank =
      Finset.univ.sup (fun p : (Nat.card A).primeFactors ↦
        (⊤ : Submodule ℤ (_root_.AddCommGroup.primaryComponent A p.1)).spanFinrank) := by
  classical
  let M : (Nat.card A).primeFactors → Type _ :=
    fun p ↦ _root_.AddCommGroup.primaryComponent A p.1
  have hcop : Pairwise fun p q ↦ (Nat.card (M p)).Coprime (Nat.card (M q)) := by
    intro p q hpq
    dsimp only [M]
    have hp := Nat.prime_of_mem_primeFactors p.2
    have hq := Nat.prime_of_mem_primeFactors q.2
    rw [natCard_primaryComponent A hp, natCard_primaryComponent A hq]
    exact ((Nat.coprime_primes hp hq).mpr (by simpa using hpq)).pow _ _
  exact (Submodule.spanFinrank_eq_of_equiv (primaryDecomposition A).toIntLinearEquiv).symm.trans
    (spanFinrank_pi_eq_sup_of_coprime_card M hcop)

/-- Group-rank form of `spanFinrank_eq_sup_primaryComponents`: `AddGroup.rank A` is the maximum of
`AddGroup.rank` over the prime-primary components of `A`. -/
theorem rank_eq_sup_primaryComponents (A : Type*) [AddCommGroup A] [Finite A] :
    AddGroup.rank A =
      Finset.univ.sup (fun p : (Nat.card A).primeFactors ↦
        AddGroup.rank (_root_.AddCommGroup.primaryComponent A p.1)) := by
  simp_rw [AddGroup.rank_eq_spanFinrank_top]
  exact spanFinrank_eq_sup_primaryComponents A

/-- For any natural number `n`, the `n`-primary component of a finite abelian group `A` needs at
most as many generators over `ℤ` as `A`: scalar multiplication by `[A : A[n^∞]]` maps `A` into
`A[n^∞]` and acts bijectively on `A[n^∞]` because `#A[n^∞]` is coprime to `[A : A[n^∞]]`. -/
theorem spanFinrank_primaryComponent_le (A : Type*) [AddCommGroup A] [Finite A] (n : ℕ) :
    (⊤ : Submodule ℤ (_root_.AddCommGroup.primaryComponent A n)).spanFinrank ≤
      (⊤ : Submodule ℤ A).spanFinrank := by
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

/-- Group-rank form of `spanFinrank_primaryComponent_le`: for any `n : ℕ`, the `n`-primary
component of a finite abelian group `A` has `AddGroup.rank` at most `AddGroup.rank A`. -/
theorem rank_primaryComponent_le (A : Type*) [AddCommGroup A] [Finite A] (n : ℕ) :
    AddGroup.rank (_root_.AddCommGroup.primaryComponent A n) ≤ AddGroup.rank A := by
  rw [AddGroup.rank_eq_spanFinrank_top, AddGroup.rank_eq_spanFinrank_top]
  exact spanFinrank_primaryComponent_le A n

/-- The least number of `ℤ`-module generators of a finite product `∏ᵢ ℤ/pᵏⁱ` is the number of
nonzero exponents `kᵢ ≠ 0`. -/
theorem spanFinrank_pi_zmod_pow {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] (k : ι → ℕ) :
    (⊤ : Submodule ℤ (∀ i, ZMod (p ^ k i))).spanFinrank = #{i | k i ≠ 0} := by
  classical
  have hp : p.Prime := Fact.out
  have : ∀ i, NeZero (p ^ k i) := fun i ↦ ⟨pow_ne_zero _ hp.ne_zero⟩
  apply le_antisymm
  · -- Single-coordinate generators on `{i // k i ≠ 0}` span the product, as `ZMod 1` is trivial.
    let g : {i // k i ≠ 0} → ∀ i, ZMod (p ^ k i) := fun j ↦ Pi.single j.1 1
    have hspan : Submodule.span ℤ (Set.range g) = ⊤ := by
      refine top_unique fun x _ ↦ ?_
      rw [← Finset.univ_sum_single x]
      refine Submodule.sum_mem _ fun i _ ↦ ?_
      by_cases hi : k i = 0
      · have : Subsingleton (ZMod (p ^ k i)) := by rw [hi, pow_zero]; infer_instance
        rw [Subsingleton.elim (x i) 0, Pi.single_zero]
        exact Submodule.zero_mem _
      · have hx : Pi.single i (x i) = ((x i).val : ℤ) • g ⟨i, hi⟩ := by
          ext j
          by_cases hji : j = i
          · subst hji
            simp [g]
          · simp [g, hji]
        rw [hx]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)
    rw [← hspan]
    refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range g)).trans ?_
    calc (Set.range g).ncard ≤ Fintype.card {i // k i ≠ 0} := by
          simpa [Nat.card_eq_fintype_card] using Set.ncard_image_le (f := g) (s := Set.univ)
      _ = #{i | k i ≠ 0} := Fintype.card_subtype _
  · -- Reducing the nontrivial coordinates modulo `p` maps onto the `𝔽_p`-vector space `𝔽_p^S`.
    let π : (∀ i, ZMod (p ^ k i)) →ₗ[ℤ] ({i // k i ≠ 0} → ZMod p) :=
      LinearMap.pi fun j ↦
        ((ZMod.castHom (dvd_pow_self p j.2) (ZMod p)).toAddMonoidHom.toIntLinearMap).comp
          (LinearMap.proj j.1)
    have hsurj : Function.Surjective π := fun y ↦ by
      refine ⟨fun i ↦ if hi : k i ≠ 0 then ((y ⟨i, hi⟩).val : ZMod (p ^ k i)) else 0, ?_⟩
      ext ⟨i, hi⟩
      simp [π, hi]
    have hle := Submodule.spanFinrank_map_le_of_fg π (Module.Finite.fg_top (R := ℤ))
    rw [Submodule.map_top, LinearMap.range_eq_top.mpr hsurj] at hle
    calc #{i | k i ≠ 0} = Fintype.card {i // k i ≠ 0} := (Fintype.card_subtype _).symm
      _ = Module.finrank (ZMod p) ({i // k i ≠ 0} → ZMod p) := (Module.finrank_pi (ZMod p)).symm
      _ = (⊤ : Submodule (ZMod p) ({i // k i ≠ 0} → ZMod p)).spanFinrank :=
          Module.finrank_eq_spanFinrank_of_free
      _ = (⊤ : Submodule ℤ ({i // k i ≠ 0} → ZMod p)).spanFinrank :=
          (Submodule.spanFinrank_restrictScalars_eq
            (ZMod.ringHom_surjective (algebraMap ℤ (ZMod p))) ⊤).symm
      _ ≤ (⊤ : Submodule ℤ (∀ i, ZMod (p ^ k i))).spanFinrank := hle

/-- Group-rank form of `spanFinrank_pi_zmod_pow`: the minimal number of generators of `∏ᵢ ℤ/pᵏⁱ`
is `#{i | kᵢ ≠ 0}`. -/
theorem rank_pi_zmod_pow {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] (k : ι → ℕ) :
    AddGroup.rank (∀ i, ZMod (p ^ k i)) = #{i | k i ≠ 0} := by
  classical
  have : ∀ i, NeZero (p ^ k i) := fun i ↦ ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  rw [AddGroup.rank_eq_spanFinrank_top, spanFinrank_pi_zmod_pow]

end TauCeti.AddCommGroup
