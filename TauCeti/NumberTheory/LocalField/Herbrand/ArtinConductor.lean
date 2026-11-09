/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Herbrand.HasseArf.Abelian

/-!
# The Artin conductor exponent

Let `L/K` be a finite Galois extension of nonarchimedean local fields with group `G` and upper
ramification groups `G^v`. The **Artin conductor exponent** `f(χ)` of a homomorphism
`χ : G → M` is the least natural number `n` with `G^n ⊆ ker χ`. It is `0` exactly when `χ` is
unramified, that is trivial on the inertia group `G^0 = G_0`.

For `L/K` abelian the Hasse–Arf theorem makes every upper break an integer. This turns the
definition into Serre's formula for the conductor of a one-dimensional character in terms of the
lower ramification groups `G_i`,

`f(χ) · #G_0 = ∑_{i ≥ 0, χ(G_i) ≠ 1} #G_i`,

since the last lower index `t` with `χ(G_t) ≠ 1` sits at the upper index
`φ(t) = (#G_1 + ⋯ + #G_t) / #G_0`, an integer by Hasse–Arf, and `f(χ) = φ(t) + 1`.

## Main definitions

* `TauCeti.LocalFieldsRamification.artinConductorExponent K L χ`: the least `n : ℕ` such that `χ`
  is trivial on the upper ramification group `G^n`.

## Main results

* `TauCeti.LocalFieldsRamification.artinConductorExponent_le_iff`: `f(χ) ≤ n` exactly when
  `G^n ⊆ ker χ`.
* `TauCeti.LocalFieldsRamification.artinConductorExponent_eq_zero_iff`: `f(χ) = 0` exactly when
  `χ` is trivial on `G_0`.
* `TauCeti.LocalFieldsRamification.artinConductorExponent_mul_card_eq_sum_range`: Serre's formula
  for an abelian extension, as a sum over `i < n` for any `n` with `χ(G_n) = 1`.
* `TauCeti.LocalFieldsRamification.artinConductorExponent_mul_card_lowerRamificationGroup_zero`:
  Serre's formula `f(χ) · #G_0 = ∑_{i ≥ 0, χ(G_i) ≠ 1} #G_i` for an abelian extension.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §3, Chapter V, §7 and Chapter VI, §2.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §11.
-/

public section
noncomputable section

namespace TauCeti.LocalFieldsRamification

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [Module.Finite K L]

section Galois

variable [IsGalois K L]

variable {M : Type*} [MulOneClass M]

/-- The **Artin conductor exponent** of a homomorphism `χ` on the Galois group of a finite Galois
extension of local fields: the least natural number `n` such that `χ` is trivial on the upper
ramification group `G^n`. The minimum is attained
(`upperRamificationGroup_artinConductorExponent_le_ker`). -/
def artinConductorExponent (χ : (L ≃ₐ[K] L) →* M) : ℕ :=
  sInf {n : ℕ | upperRamificationGroup K L ⟨n, Nat.cast_mem_ramificationIndexDomain n⟩ ≤ χ.ker}

/-- **The Artin conductor exponent is attained**: `χ` is trivial on `G^{f(χ)}`. -/
theorem upperRamificationGroup_artinConductorExponent_le_ker (χ : (L ≃ₐ[K] L) →* M) :
    upperRamificationGroup K L ⟨artinConductorExponent K L χ,
      Nat.cast_mem_ramificationIndexDomain _⟩ ≤ χ.ker := by
  obtain ⟨N, hN⟩ := exists_forall_upperRamificationGroup_natCast_eq_bot K L
  exact Nat.sInf_mem (s := {n : ℕ | upperRamificationGroup K L
    ⟨n, Nat.cast_mem_ramificationIndexDomain n⟩ ≤ χ.ker})
    ⟨N, by rw [Set.mem_ofPred_eq, hN N le_rfl]; exact bot_le⟩

/-- **The characterizing property of the Artin conductor exponent**: it is at most `n` exactly
when `χ` is trivial on the upper ramification group `G^n`. -/
theorem artinConductorExponent_le_iff (χ : (L ≃ₐ[K] L) →* M) {n : ℕ} :
    artinConductorExponent K L χ ≤ n ↔
      upperRamificationGroup K L ⟨n, Nat.cast_mem_ramificationIndexDomain n⟩ ≤ χ.ker :=
  ⟨fun h ↦ (upperRamificationGroup_antitone K L (Subtype.mk_le_mk.2 (by exact_mod_cast h))).trans
      (upperRamificationGroup_artinConductorExponent_le_ker K L χ),
    fun h ↦ Nat.sInf_le h⟩

/-- The Artin conductor exponent is at most `n` exactly when `χ` is trivial on the lower
ramification group `G_{ψ(n)}`. -/
theorem artinConductorExponent_le_iff_lowerRamificationGroup_psiNat_le
    (χ : (L ≃ₐ[K] L) →* M) {n : ℕ} :
    artinConductorExponent K L χ ≤ n ↔ lowerRamificationGroup K L (psiNat K L n) ≤ χ.ker := by
  rw [artinConductorExponent_le_iff, upperRamificationGroup_natCast]

/-- A homomorphism has Artin conductor exponent `0` exactly when it is **unramified**, that is,
trivial on the inertia group `G_0`. -/
@[simp]
theorem artinConductorExponent_eq_zero_iff (χ : (L ≃ₐ[K] L) →* M) :
    artinConductorExponent K L χ = 0 ↔ lowerRamificationGroup K L 0 ≤ χ.ker := by
  rw [← Nat.le_zero, artinConductorExponent_le_iff_lowerRamificationGroup_psiNat_le, psiNat_zero,
    Nat.cast_zero]

end Galois

/-! ### Abelian extensions -/

section Abelian

variable [IsAbelianGalois K L] {M : Type*} [MulOneClass M]

/-- If `χ` is nontrivial on `G_t` and trivial on `G_{t+1}`, then by Hasse–Arf
`#G_1 + ⋯ + #G_t = m · #G_0` for a natural number `m`, that is `φ(t) = m`, and `f(χ) = m + 1`. -/
private theorem exists_psiNat_eq_and_artinConductorExponent_eq (χ : (L ≃ₐ[K] L) →* M) {t : ℕ}
    (ht : ¬lowerRamificationGroup K L t ≤ χ.ker)
    (ht' : lowerRamificationGroup K L (t + 1 : ℕ) ≤ χ.ker) :
    ∃ m : ℕ, ∑ i ∈ Finset.range t, Nat.card (lowerRamificationGroup K L (i + 1 : ℕ)) =
        m * Nat.card (lowerRamificationGroup K L 0) ∧
      artinConductorExponent K L χ = m + 1 := by
  -- `t` is a lower break, so `φ(t)` is an upper break, an integer `z` by Hasse–Arf.
  have hlt : lowerRamificationGroup K L ((t : ℤ) + 1) < lowerRamificationGroup K L t := by
    refine lt_of_le_of_ne (lowerRamificationGroup_antitone K L (by omega)) fun h ↦ ht ?_
    rw [← h]
    exact_mod_cast ht'
  have hjump : LowerJump K L ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩ :=
    (lowerJump_intCast_iff K L (i := t) (by simpa using Nat.cast_mem_ramificationIndexDomain t)).2
      (by exact_mod_cast hlt)
  obtain ⟨z, hz⟩ := hasseArf K L ((upperJump_herbrand_iff K L _).2 hjump)
  have hφ := coe_herbrand_of_coe_eq_natCast K L t
    (u := ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩) rfl
  rw [hz, eq_div_iff (by exact_mod_cast Nat.card_pos.ne')] at hφ
  have hz0 : 0 ≤ z := by
    have : (0 : ℝ) ≤ z * Nat.card (lowerRamificationGroup K L 0) := hφ ▸ by positivity
    exact_mod_cast nonneg_of_mul_nonneg_left this (by exact_mod_cast Nat.card_pos)
  lift z to ℕ using hz0
  have hsum : ∑ i ∈ Finset.Icc 1 t, Nat.card (lowerRamificationGroup K L i) =
      z * Nat.card (lowerRamificationGroup K L 0) := by exact_mod_cast hφ.symm
  have hψ : psiNat K L z = t := (psiNat_eq_iff K L).2 hsum
  refine ⟨z, ?_, le_antisymm ?_ ?_⟩
  · rwa [Finset.range_eq_Ico,
      Finset.sum_Ico_add' (fun i : ℕ ↦ Nat.card (lowerRamificationGroup K L i)) 0 t 1, zero_add,
      Finset.Ico_add_one_right_eq_Icc]
  · rw [artinConductorExponent_le_iff_lowerRamificationGroup_psiNat_le]
    refine (lowerRamificationGroup_antitone K L ?_).trans ht'
    have := psiNat_strictMono K L (Nat.lt_add_one z)
    omega
  · by_contra h
    rw [not_le, Nat.lt_succ_iff, artinConductorExponent_le_iff_lowerRamificationGroup_psiNat_le,
      hψ] at h
    exact ht h

/-- **Serre's formula for the Artin conductor**, truncated at any index `n` at which `χ` is
trivial on `G_n`: for a finite abelian extension of local fields,
`f(χ) · #G_0 = ∑_{i < n, χ(G_i) ≠ 1} #G_i`. -/
theorem artinConductorExponent_mul_card_eq_sum_range (χ : (L ≃ₐ[K] L) →* M) {n : ℕ}
    (hn : lowerRamificationGroup K L n ≤ χ.ker) [DecidablePred fun i : ℕ ↦
      lowerRamificationGroup K L i ≤ χ.ker] :
    artinConductorExponent K L χ * Nat.card (lowerRamificationGroup K L 0) =
      ∑ i ∈ Finset.range n, if lowerRamificationGroup K L i ≤ χ.ker then 0
        else Nat.card (lowerRamificationGroup K L i) := by
  have hP : ∃ i : ℕ, lowerRamificationGroup K L i ≤ χ.ker := ⟨n, hn⟩
  -- The indices where `χ` is nontrivial on `G_i` are those below `c`.
  set c := Nat.find hP with hc
  have hiff : ∀ i : ℕ, lowerRamificationGroup K L i ≤ χ.ker ↔ c ≤ i := fun i ↦
    ⟨Nat.find_min' hP, fun h ↦
      (lowerRamificationGroup_antitone K L (by exact_mod_cast h)).trans (Nat.find_spec hP)⟩
  rw [← Finset.sum_range_add_sum_Ico _ ((hiff n).1 hn),
    Finset.sum_congr rfl fun i hi ↦ ite_eq_right ((hiff i).not.2 (by simpa using hi)),
    Finset.sum_congr rfl fun i hi ↦ ite_eq_left ((hiff i).2 (Finset.mem_Ico.1 hi).1),
    Finset.sum_const_zero, add_zero]
  rcases hc0 : c with _ | t
  · rw [Finset.sum_range_zero, mul_eq_zero, artinConductorExponent_eq_zero_iff]
    exact Or.inl ((hiff 0).2 hc0.le)
  · obtain ⟨m, hsum, hf⟩ := exists_psiNat_eq_and_artinConductorExponent_eq K L χ
      ((hiff t).not.2 (by omega)) ((hiff (t + 1)).2 hc0.le)
    rw [hf, Finset.sum_range_succ', hsum, Nat.cast_zero]
    ring

/-- **Serre's formula for the Artin conductor** of a homomorphism on the Galois group of a finite
abelian extension of local fields: `f(χ) · #G_0 = ∑_{i ≥ 0, χ(G_i) ≠ 1} #G_i`. -/
theorem artinConductorExponent_mul_card_lowerRamificationGroup_zero (χ : (L ≃ₐ[K] L) →* M) :
    artinConductorExponent K L χ * Nat.card (lowerRamificationGroup K L 0) =
      ∑ᶠ (i : ℕ) (_ : ¬lowerRamificationGroup K L i ≤ χ.ker),
        Nat.card (lowerRamificationGroup K L i) := by
  classical
  obtain ⟨N, hN⟩ := exists_forall_lowerRamificationGroup_natCast_eq_bot K L
  have hNle : ∀ i : ℕ, N ≤ i → lowerRamificationGroup K L i ≤ χ.ker := fun i hi ↦ by
    rw [hN i hi]
    exact bot_le
  simp only [finsum_eq_if, ite_not]
  rw [artinConductorExponent_mul_card_eq_sum_range K L χ (hNle _ le_rfl)]
  refine (finsum_eq_sum_of_support_subset _ fun i hi ↦ ?_).symm
  simp only [Function.mem_support, ne_eq, ite_eq_left_iff, not_forall] at hi
  simpa using not_le.1 fun h ↦ hi.1 (hNle i h)

end Abelian

end TauCeti.LocalFieldsRamification
