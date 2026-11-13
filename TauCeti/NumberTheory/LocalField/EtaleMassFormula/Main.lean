/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.EtaleAlgebra
import TauCeti.NumberTheory.LocalField.EtaleMassFormula.SplittingSymbol.Mass

/-!
# Bhargava's mass formula for étale algebras over a local field

Let `K` be a nonarchimedean local field whose residue field has `q` elements. Bhargava's mass
formula ([Bhargava 2007, Theorem 1.1, Proposition 2.3, and §8]) evaluates the étale mass of degree
`n` as
`M_n(K) = ∑_{k = 0}^n q(k, n - k) · q ^ (-k)`,
where `q(k, m)` is the number of partitions of `k` into at most `m` parts. For `n ≥ 1`, the `k = n`
term has `q(n, 0) = 0`, matching Bhargava's sum over `0 ≤ k < n`, while at `n = 0` both sides are
`1`.

Every labelled Galois set `ρ : TauCeti.GaloisSet K n` has a splitting symbol whose ramification
partition is a partition of some `k ≤ n` into at most `n - k` parts. Grouping the sum in
`TauCeti.etaleMass` by `k` and this partition and applying
`TauCeti.etaleMass_ramificationPartition` gives `TauCeti.etaleMass_eq`. Combining with
`TauCeti.tsum_etaleDiscriminantExponent` yields Bhargava's Theorem 1.1 directly as a sum over
isomorphism classes of étale `K`-algebras of degree `n`
(`TauCeti.tsum_etaleDiscriminantExponent_eq`).

In particular, `M_2(K) = 1 + q⁻¹` and `M_3(K) = 1 + q⁻¹ + q⁻²` (`TauCeti.etaleMass_two`,
`TauCeti.etaleMass_three`), even in equal characteristic when there are infinitely many isomorphism
classes of extensions.

## Main results

* `TauCeti.etaleMass_eq`: Bhargava's mass formula `M_n(K) = ∑_{k = 0}^n q(k, n - k) q ^ (-k)`.
* `TauCeti.tsum_etaleDiscriminantExponent_eq`: Bhargava's Theorem 1.1 for isomorphism classes of
  étale `K`-algebras of degree `n`.
* `TauCeti.etaleMass_two` and `TauCeti.etaleMass_three`: explicit formulas in degrees `2` and `3`.

## References

* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density of
  number field discriminants*, IMRN **2007**, rnm052, Theorem 1.1, Proposition 2.3, and §8.
* K. S. Kedlaya, *Mass formulas for local Galois representations*, IMRN **2007**, rnm021.
* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036.
-/

public section

noncomputable section

open ValuativeRel
open scoped ENNReal Nat

namespace TauCeti

universe u

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-! ### Bhargava's mass formula -/

variable (K) in
/-- **Bhargava's mass formula** ([Bhargava 2007, Theorem 1.1, Proposition 2.3, and §8]): for a
nonarchimedean local field `K` with `q` residue classes, the étale mass of degree `n` is
`M_n(K) = ∑_{k = 0}^n q(k, n - k) · q ^ (-k)`, where `q(k, m)` is the number of partitions of `k`
into at most `m` parts. -/
theorem etaleMass_eq (n : ℕ) :
    etaleMass K n =
      ∑ k ∈ Finset.range (n + 1),
        (((Finset.univ : Finset k.Partition).filter fun π ↦ π.parts.card ≤ n - k).card :
            ℝ≥0∞) / (Nat.card 𝓀[K] : ℝ≥0∞) ^ k := by
  classical
  rw [etaleMass_def]
  set q : ℝ≥0∞ := (Nat.card 𝓀[K] : ℝ≥0∞)
  -- For every `ρ : GaloisSet K n`, `ramificationPartition ρ.splittingSymbol` has sum `k ≤ n`
  -- and at most `n - k` parts.
  have hbound : ∀ ρ : GaloisSet K n,
      (ramificationPartition ρ.splittingSymbol).sum < n + 1 ∧
        (ramificationPartition ρ.splittingSymbol).card ≤
          n - (ramificationPartition ρ.splittingSymbol).sum := by
    intro ρ
    have hdeg := sum_map_mul_eq_sum_ramificationPartition_add ρ.splittingSymbol
      fun x hx ↦ (ρ.pos_of_mem_splittingSymbol hx).2
    rw [ρ.sum_map_mul_splittingSymbol] at hdeg
    omega
  -- First group by `k = (ramificationPartition ρ.splittingSymbol).sum ∈ Finset.range (n + 1)`.
  let Ξ₁ : GaloisSet K n → Finset.range (n + 1) :=
    fun ρ ↦ ⟨(ramificationPartition ρ.splittingSymbol).sum, Finset.mem_range.2 (hbound ρ).1⟩
  rw [← tsum_fiberwise _ Ξ₁, tsum_fintype, Finset.mul_sum,
    ← Finset.sum_coe_sort (Finset.range (n + 1))]
  refine Finset.sum_congr rfl fun ⟨k, hk⟩ _ ↦ ?_
  dsimp only
  -- Next group the `k`-fibre by the ramification partition `π` with `π.parts.card ≤ n - k`.
  let S : Finset k.Partition :=
    (Finset.univ : Finset k.Partition).filter fun π ↦ π.parts.card ≤ n - k
  let e₁ : {ρ : GaloisSet K n // (ramificationPartition ρ.splittingSymbol).sum = k} ≃
      Ξ₁ ⁻¹' {⟨k, hk⟩} :=
    { toFun := fun ρ ↦ ⟨ρ.1, Subtype.ext ρ.2⟩
      invFun := fun r ↦ ⟨r.1, congrArg Subtype.val r.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let Ξ₂ : {ρ : GaloisSet K n // (ramificationPartition ρ.splittingSymbol).sum = k} → S :=
    fun ⟨ρ, hρ⟩ ↦ ⟨{ parts := ramificationPartition ρ.splittingSymbol
                     parts_pos := fun {t} ht ↦ Nat.pos_of_ne_zero (mem_ramificationPartition.1 ht).1
                     parts_sum := hρ },
      Finset.mem_filter.2 ⟨Finset.mem_univ _, by
        dsimp only
        rw [← hρ]
        exact (hbound ρ).2⟩⟩
  rw [← e₁.tsum_eq fun r ↦ 1 / q ^ r.1.discriminantExponent,
    ← tsum_fiberwise _ Ξ₂, tsum_fintype, Finset.mul_sum]
  have hπ_term : ∀ π : S,
      (n ! : ℝ≥0∞)⁻¹ * ∑' r : Ξ₂ ⁻¹' {π}, 1 / q ^ (e₁ r.1).1.discriminantExponent =
        1 / q ^ k := by
    rintro ⟨π, hπ_mem⟩
    have hπ : π.parts.card ≤ n - k := (Finset.mem_filter.1 hπ_mem).2
    let efib : {ρ : GaloisSet K n // ramificationPartition ρ.splittingSymbol = π.parts} ≃
        Ξ₂ ⁻¹' {⟨π, hπ_mem⟩} :=
      { toFun := fun ρ ↦
          ⟨⟨ρ.1, by rw [ρ.2, π.parts_sum]⟩, Subtype.ext (Nat.Partition.ext ρ.2)⟩
        invFun := fun r ↦
          ⟨r.1.1, congrArg (fun p : S ↦ p.1.parts) r.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    rw [← efib.tsum_eq fun r ↦ 1 / q ^ (e₁ r.1).1.discriminantExponent]
    exact etaleMass_ramificationPartition n k π hπ
  rw [Finset.sum_congr rfl fun π _ ↦ hπ_term π,
    Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, mul_one_div]

variable (K) in
/-- **Bhargava's Theorem 1.1**: for a family `A` of étale `K`-algebras of degree `n` containing
exactly one member of each `K`-isomorphism class,
`∑ 1 / (#Aut_K(A i) · q ^ d(A i)) = ∑_{k = 0}^n q(k, n - k) · q ^ (-k)`. -/
theorem tsum_etaleDiscriminantExponent_eq (n : ℕ) {ι : Type*} (A : ι → Type u)
    [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)] [∀ i, Algebra.Etale K (A i)]
    (hdeg : ∀ i, Module.finrank K (A i) = n)
    (hinj : ∀ i j, Nonempty (A i ≃ₐ[K] A j) → i = j)
    (hsurj : ∀ (B : Type u) [CommRing B] [Algebra K B] [Algebra.Etale K B],
      Module.finrank K B = n → ∃ i, Nonempty (B ≃ₐ[K] A i)) :
    ∑' i, 1 / ((Nat.card (A i ≃ₐ[K] A i) : ℝ≥0∞) *
        (Nat.card 𝓀[K] : ℝ≥0∞) ^ etaleDiscriminantExponent K (A i)) =
      ∑ k ∈ Finset.range (n + 1),
        (((Finset.univ : Finset k.Partition).filter fun π ↦ π.parts.card ≤ n - k).card :
            ℝ≥0∞) / (Nat.card 𝓀[K] : ℝ≥0∞) ^ k :=
  (tsum_etaleDiscriminantExponent K n A hdeg hinj hsurj).trans (etaleMass_eq K n)

/-! ### Small-degree evaluations -/

variable (K) in
/-- In degree `2`, `M_2(K) = 1 + q⁻¹`. -/
theorem etaleMass_two :
    etaleMass K 2 = 1 + 1 / (Nat.card 𝓀[K] : ℝ≥0∞) := by
  classical
  have h2 : ((Finset.univ : Finset (2 : ℕ).Partition).filter fun π ↦ π.parts = 0) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro π _ h0
    have hsum := π.parts_sum
    rw [h0, Multiset.sum_zero] at hsum
    omega
  rw [etaleMass_eq, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  simp [Finset.univ_unique, h2]

variable (K) in
/-- In degree `3`, `M_3(K) = 1 + q⁻¹ + q⁻²`. -/
theorem etaleMass_three :
    etaleMass K 3 =
      1 + 1 / (Nat.card 𝓀[K] : ℝ≥0∞) + 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ 2 := by
  classical
  have h2 : ((Finset.univ : Finset (2 : ℕ).Partition).filter fun π ↦ π.parts.card ≤ 1) =
      {Nat.Partition.indiscrete 2} := by
    ext π
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    refine ⟨fun hle ↦ ?_, fun h ↦ by simp [h]⟩
    have hne : π.parts ≠ 0 := fun h0 ↦ by
      have hsum := π.parts_sum
      rw [h0, Multiset.sum_zero] at hsum
      omega
    obtain ⟨a, ha⟩ := Multiset.card_eq_one.1 (le_antisymm hle (Multiset.card_pos.2 hne))
    have hak : a = 2 := by
      have hsum := π.parts_sum
      rwa [ha, Multiset.sum_singleton] at hsum
    exact Nat.Partition.ext (by simp [ha, hak])
  have h3 : ((Finset.univ : Finset (3 : ℕ).Partition).filter fun π ↦ π.parts = 0) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro π _ h0
    have hsum := π.parts_sum
    rw [h0, Multiset.sum_zero] at hsum
    omega
  rw [etaleMass_eq, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one]
  simp [Finset.univ_unique, h2, h3]

end TauCeti
