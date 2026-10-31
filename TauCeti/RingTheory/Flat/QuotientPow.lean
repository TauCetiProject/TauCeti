/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.Flat.Tensor

/-!
# Flatness from the infinitesimal neighbourhoods of maximal ideals

Let `A → B` be a homomorphism of Noetherian rings. Suppose that for every maximal ideal `𝔫` of
`B`, with contraction `𝔪 = 𝔫 ∩ A`, all the maps `A ⧸ 𝔪 ^ k → B ⧸ 𝔪 ^ k B` are bijective. Then `B`
is flat over `A` (`Module.Flat.of_bijective_quotientMap_pow`).

This applies when `B` is a completion-like enlargement of `A` with the same infinitesimal
neighbourhoods at every closed point of `B`, for instance the inclusion of the
Monsky–Washnitzer algebra into the Tate algebra. In that situation the `𝔫`-adic completion of
`B` is the `𝔪`-adic completion of `A`, and the statement is the usual flatness of completions;
the proof below avoids completions and localizations.

## Implementation notes

By Mathlib's ideal criterion it suffices that `B ⊗[A] J → B ⊗[A] A` is injective for every ideal
`J` of `A`. Let `t` be in the kernel and fix a maximal ideal `𝔫` of `B`, with `𝔪 = 𝔫 ∩ A`.

1. Since `B = A + 𝔪 ^ k B`, the element `t` is `1 ⊗ j` modulo `𝔪 ^ k (B ⊗[A] J)` for some `j ∈ J`.
   Its image in `B` then shows that `j` lies in `𝔪 ^ k B ∩ A = 𝔪 ^ k`.
2. By the Artin–Rees lemma `𝔪 ^ k ∩ J ⊆ 𝔪 ^ (k - c) J`, so `t ∈ 𝔪 ^ (k - c) (B ⊗[A] J)` for every
   `k`.
3. Krull's intersection theorem for the finite `B`-module `B ⊗[A] J` gives `r ∈ 𝔫` with
   `(1 - r) t = 0`. As this holds for every maximal ideal `𝔫`, `t = 0`.

## References

* H. Matsumura, *Commutative Ring Theory*, Theorems 8.8 and 8.10 (Artin–Rees and Krull's
  intersection theorem) and Theorem 22.3 (the local flatness criterion, of which this is a
  special case).
-/

public section

open TensorProduct LinearMap

namespace Module.Flat

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- The first step of the proof: modulo `𝔪 ^ k (B ⊗[A] J)`, every element of `B ⊗[A] J` is of the
form `1 ⊗ j`, as soon as every class of `B ⧸ 𝔪 ^ k B` comes from `A`. -/
private theorem exists_tmul_sub_mem_smul_top {I : Ideal A}
    (hI : ∀ b : B, ∃ a : A, b - algebraMap A B a ∈ I.map (algebraMap A B)) (J : Ideal A)
    (t : B ⊗[A] J) : ∃ j : J, t - (1 : B) ⊗ₜ j ∈ (I • ⊤ : Submodule A (B ⊗[A] J)) := by
  induction t using TensorProduct.inductionOn with
  | add x y hx hy =>
    obtain ⟨j, hj⟩ := hx
    obtain ⟨j', hj'⟩ := hy
    exact ⟨j + j', by simpa [tmul_add, add_sub_add_comm] using add_mem hj hj'⟩
  | tmul b j =>
    obtain ⟨a, ha⟩ := hI b
    refine ⟨a • j, ?_⟩
    -- `b ⊗ j - 1 ⊗ a j = (b - a) ⊗ j`, the image of `b - a ∈ I • B` under `· ⊗ j`.
    have hmem : b - algebraMap A B a ∈ (I • ⊤ : Submodule A B) := by
      rwa [Ideal.smul_top_eq_map]
    have key := Submodule.mem_map_of_mem (f := (TensorProduct.mk A B J).flip j) hmem
    rw [Submodule.map_smul''] at key
    have heq : ((TensorProduct.mk A B J).flip j) (b - algebraMap A B a) =
        b ⊗ₜ j - (1 : B) ⊗ₜ (a • j) := by
      simp [Algebra.algebraMap_eq_smul_one]
    rw [heq] at key
    exact Submodule.smul_mono le_rfl le_top key

/-- **Flatness from the infinitesimal neighbourhoods of maximal ideals.** Let `A → B` be a
homomorphism of Noetherian rings. If for every maximal ideal `𝔫` of `B` and every `k` the map
`A ⧸ 𝔪 ^ k → B ⧸ 𝔪 ^ k B` is bijective, where `𝔪 = 𝔫 ∩ A`, then `B` is flat over `A`. -/
theorem of_bijective_quotientMap_pow [IsNoetherianRing A] [IsNoetherianRing B]
    (h : ∀ (𝔫 : Ideal B) [𝔫.IsMaximal] (k : ℕ), Function.Bijective
      (Ideal.quotientMap ((𝔫.comap (algebraMap A B) ^ k).map (algebraMap A B)) (algebraMap A B)
        Ideal.le_comap_map)) :
    Flat A B := by
  refine iff_lTensor_injective'.mpr fun J ↦ (injective_iff_map_eq_zero _).mpr fun t ht ↦ ?_
  -- `t` lies in `𝔫 ^ n (B ⊗[A] J)` for every maximal ideal `𝔫` and every `n`.
  have hmem (𝔫 : Ideal B) [𝔫.IsMaximal] (n : ℕ) :
      t ∈ (𝔫 ^ n • ⊤ : Submodule B (B ⊗[A] J)) := by
    set 𝔪 := 𝔫.comap (algebraMap A B)
    obtain ⟨c, hc⟩ := 𝔪.exists_pow_inf_eq_pow_smul (M := A) J
    set k := n + c
    -- The map `A ⧸ 𝔪 ^ k → B ⧸ 𝔪 ^ k B` is surjective and injective.
    have hsurj (b : B) : ∃ a : A, b - algebraMap A B a ∈ (𝔪 ^ k).map (algebraMap A B) := by
      obtain ⟨x, hx⟩ := (h 𝔫 k).2 (Ideal.Quotient.mk _ b)
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact ⟨a, Ideal.Quotient.eq.mp (by simpa using hx.symm)⟩
    have hinj (a : A) (ha : algebraMap A B a ∈ (𝔪 ^ k).map (algebraMap A B)) : a ∈ 𝔪 ^ k := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      refine (injective_iff_map_eq_zero _).mp (h 𝔫 k).1 _ ?_
      rwa [Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem]
    obtain ⟨j, hj⟩ := exists_tmul_sub_mem_smul_top hsurj J t
    -- The image of `1 ⊗ j` in `B` is that of `j`, which therefore lies in `𝔪 ^ k B`.
    have hjk : (j : A) ∈ 𝔪 ^ k := by
      refine hinj _ ?_
      have himg := Submodule.mem_map_of_mem
        (f := (TensorProduct.rid A B).toLinearMap ∘ₗ J.subtype.lTensor B) hj
      rw [Submodule.map_smul'', map_sub, LinearMap.comp_apply, ht, map_zero, zero_sub,
        neg_mem_iff] at himg
      have := Submodule.smul_mono (le_refl (𝔪 ^ k)) le_top himg
      rw [Ideal.smul_top_eq_map] at this
      simpa [Algebra.algebraMap_eq_smul_one] using this
    -- By Artin–Rees, `j ∈ 𝔪 ^ n J`, so `1 ⊗ j ∈ 𝔪 ^ n (B ⊗[A] J)`.
    have hjn : (j : A) ∈ 𝔪 ^ n • J := by
      have hj' : (j : A) ∈ 𝔪 ^ k • (⊤ : Submodule A A) ⊓ J :=
        ⟨by simpa [smul_eq_mul, Ideal.mul_top] using hjk, j.2⟩
      rw [hc k (Nat.le_add_left c n), Nat.add_sub_cancel] at hj'
      exact Submodule.smul_mono le_rfl inf_le_right hj'
    have h1 : (1 : B) ⊗ₜ[A] j ∈ (𝔪 ^ n • ⊤ : Submodule A (B ⊗[A] J)) := by
      have hj'' : j ∈ (𝔪 ^ n • ⊤ : Submodule A J) := (Submodule.mem_smul_top_iff _ _ _).mpr hjn
      have := Submodule.mem_map_of_mem (f := (TensorProduct.mk A B J) 1) hj''
      rw [Submodule.map_smul''] at this
      exact Submodule.smul_mono le_rfl le_top this
    have ht' : t ∈ (𝔪 ^ n • ⊤ : Submodule A (B ⊗[A] J)) := by
      have := add_mem h1 (Submodule.smul_mono_left (Ideal.pow_le_pow_right
        (Nat.le_add_right n c)) hj)
      simpa using this
    -- Pass from `𝔪 ^ n` over `A` to `𝔫 ^ n` over `B`.
    have hle : (𝔪 ^ n • ⊤ : Submodule A (B ⊗[A] J)) ≤
        (𝔫 ^ n • (⊤ : Submodule B (B ⊗[A] J))).restrictScalars A := by
      rw [← Submodule.restrictScalars_top A B, ← Ideal.smul_restrictScalars, Ideal.map_pow]
      exact Submodule.restrictScalars_mono A
        (Submodule.smul_mono_left (Ideal.pow_right_mono Ideal.map_comap_le n))
    exact hle ht'
  -- Krull's intersection theorem: the annihilator of `t` lies in no maximal ideal.
  by_contra hne
  have hann : (Submodule.span B {t}).annihilator ≠ ⊤ := by
    rw [Ne, Ideal.eq_top_iff_one, Submodule.mem_annihilator_span_singleton, one_smul]
    exact hne
  obtain ⟨𝔫, h𝔫, hle⟩ := Ideal.exists_le_maximal _ hann
  obtain ⟨r, hr⟩ := (𝔫.mem_iInf_smul_pow_eq_bot_iff t).mp
    (Submodule.mem_iInf _ |>.mpr fun n ↦ hmem 𝔫 n)
  have h1r : 1 - (r : B) ∈ (Submodule.span B {t}).annihilator := by
    rw [Submodule.mem_annihilator_span_singleton, sub_smul, one_smul, hr, sub_self]
  exact h𝔫.ne_top ((Ideal.eq_top_iff_one _).mpr
    (by simpa using 𝔫.add_mem (hle h1r) r.2))

end Module.Flat
