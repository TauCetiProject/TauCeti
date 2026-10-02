/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Different.Hilbert
public import TauCeti.NumberTheory.LocalField.Different.Trace
public import TauCeti.NumberTheory.LocalField.Herbrand.Tower
public import TauCeti.NumberTheory.LocalField.Norm.Basic
import TauCeti.GroupTheory.Solvable
import TauCeti.NumberTheory.LocalField.FiniteExtension.IntermediateField
import TauCeti.NumberTheory.LocalField.Norm.PrimeDegree
import TauCeti.NumberTheory.LocalField.Solvable

/-!
# The norm on the unit filtration, with the Herbrand shift

Let `L/K` be a finite Galois extension of nonarchimedean local fields, and let
`ψℕ_{L/K} : ℕ → ℕ` be its integral inverse Herbrand function. This file proves that the norm
carries the unit filtration of `L` into that of `K` after the Herbrand shift:

`N_{L/K}(U(L, ψℕ_{L/K}(n))) ⊆ U(K, n)`   and   `N_{L/K}(U(L, ψℕ_{L/K}(n) + 1)) ⊆ U(K, n + 1)`

for every `n : ℕ`. The shift cannot be dropped: `N_{L/K}(U(L, n)) ⊆ U(K, n)` fails in general
for ramified extensions. These inclusions are the input to the comparison of the norm group of
an abelian extension with its upper ramification filtration, through which its conductor is
computed.

The proof is Serre's. The trace bound comes first: Hilbert's formula
`d(L/K) = ∑_{i ≥ 0} (#G_i - 1)` and the defining identity `#G_1 + ⋯ + #G_m = n · #G_0` of
`m = ψℕ_{L/K}(n)` give `e(L/K) (n + 1) ≤ ψℕ_{L/K}(n) + 1 + d(L/K)`, so the trace carries
`𝓂[L] ^ (ψℕ_{L/K}(n) + 1)` into `𝓂[K] ^ (n + 1)`. For a Galois extension of prime degree, the
expansion `N(1 + x) = 1 + Tr(x) + Tr(y) + N(x)` with `y ∈ 𝓂[L] ^ (2m)` reduces the inclusion to
this bound and to `N(𝓂[L] ^ m) ⊆ 𝓂[K] ^ m`. In general the Galois group is solvable, so it has a
normal subgroup of prime index, whose fixed field `F` is Galois of prime degree over `K`; the norm
is transitive, `N_{L/K} = N_{F/K} ∘ N_{L/F}`, and so is the inverse Herbrand function,
`ψℕ_{L/K} = ψℕ_{L/F} ∘ ψℕ_{F/K}`, so induction on the degree concludes.

## Main results

* `TauCeti.intTrace_mem_maximalIdeal_pow_succ_of_mem_psiNat`: for `L/K` finite Galois, the trace
  carries `𝓂[L] ^ (ψℕ_{L/K}(n) + 1)` into `𝓂[K] ^ (n + 1)`.
* `TauCeti.map_normUnits_unitFiltration_psiNat_add_one_le`:
  `N_{L/K}(U(L, ψℕ_{L/K}(n) + 1)) ⊆ U(K, n + 1)`.
* `TauCeti.map_normUnits_unitFiltration_psiNat_le`: `N_{L/K}(U(L, ψℕ_{L/K}(n))) ⊆ U(K, n)`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter V, §3 (Lemmas 4 and 5) and §6
  (Proposition 8).
-/

public section

open ValuativeRel IsLocalRing Module TauCeti.LocalFieldsRamification

universe u v

namespace TauCeti

section Trace

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Module.Finite K L]
  [IsGalois K L]

/-- `e(L/K) (n + 1) ≤ ψℕ_{L/K}(n) + 1 + d(L/K)`: Hilbert's formula, truncated at `ψℕ_{L/K}(n)`,
together with `#G_1 + ⋯ + #G_m = n · #G_0` for `m = ψℕ_{L/K}(n)`. -/
private theorem ramificationIndex_mul_succ_le (n : ℕ) :
    ramificationIndex K L * (n + 1) ≤ psiNat K L n + 1 + differentExponent K L := by
  set m := psiNat K L n
  set g : ℕ → ℕ := fun i ↦ Nat.card (lowerRamificationGroup K L i)
  have hg : ∀ i, 1 ≤ g i := fun i ↦ Nat.card_pos
  -- `#G_0 + #G_1 + ⋯ + #G_m = (n + 1) e(L/K)`.
  have hsum : ∑ i ∈ Finset.range (m + 1), g i = ramificationIndex K L * (n + 1) := by
    have h : ∑ i ∈ Finset.range m, g (i + 1) = n * g 0 := by
      have h₀ := (psiNat_eq_iff K L).1 (rfl : psiNat K L n = m)
      rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
        at h₀
      simp only [g, Nat.cast_zero, ← h₀]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [Nat.add_comm i 1]
    rw [Finset.sum_range_succ', h, ← natCard_lowerRamificationGroup_zero K L]
    simp only [g, Nat.cast_zero]
    ring
  -- Hilbert's formula, truncated at `m`: `∑_{i ≤ m} (#G_i - 1) ≤ d(L/K)`.
  obtain ⟨N, hN⟩ := exists_forall_lowerRamificationGroup_eq_bot K L
  have hsupp : Function.support (fun i : ℕ ↦ g i - 1) ⊆
      ↑(Finset.range (max (m + 1) N.toNat)) := by
    intro i hi
    simp only [Function.mem_support, ne_eq] at hi
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    have hbot : lowerRamificationGroup K L i = ⊥ := hN i (by omega)
    exact hi (by simp only [g, hbot, Subgroup.card_bot, Nat.sub_self])
  have htrunc : ∑ i ∈ Finset.range (m + 1), (g i - 1) ≤ differentExponent K L := by
    rw [differentExponent_eq_finsum_lowerRamificationGroup,
      finsum_eq_sum_of_support_subset _ hsupp]
    exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (le_max_left _ _))
  have hsub : ∑ i ∈ Finset.range (m + 1), (g i - 1) + (m + 1) =
      ∑ i ∈ Finset.range (m + 1), g i := by
    calc ∑ i ∈ Finset.range (m + 1), (g i - 1) + (m + 1)
        = ∑ i ∈ Finset.range (m + 1), (g i - 1 + 1) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
      _ = ∑ i ∈ Finset.range (m + 1), g i :=
          Finset.sum_congr rfl fun i _ ↦ Nat.sub_add_cancel (hg i)
  omega

/-- **The trace below the Herbrand shift.** In a finite Galois extension `L/K` of nonarchimedean
local fields, the integral trace carries `𝓂[L] ^ (ψℕ_{L/K}(n) + 1)` into `𝓂[K] ^ (n + 1)`. -/
theorem intTrace_mem_maximalIdeal_pow_succ_of_mem_psiNat {n : ℕ} {x : 𝒪[L]}
    (hx : x ∈ 𝓂[L] ^ (psiNat K L n + 1)) :
    Algebra.intTrace 𝒪[K] 𝒪[L] x ∈ 𝓂[K] ^ (n + 1) :=
  intTrace_mem_maximalIdeal_pow_of_mem hx (ramificationIndex_mul_succ_le n)

end Trace

section Norm

variable {K : Type u} {L : Type v} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Module.Finite K L]
  [IsGalois K L]

variable (K L) in
/-- The Herbrand-shifted inclusion `N_{L/K}(U(L, ψℕ_{L/K}(n) + 1)) ⊆ U(K, n + 1)`, as a
proposition about the extension `L/K`; the induction on the degree runs through it. -/
private def NormShift : Prop :=
  ∀ n : ℕ, (unitFiltration L (psiNat K L n + 1)).map (Algebra.normUnits K) ≤
    unitFiltration K (n + 1)

/-- The Herbrand-shifted inclusion for a Galois extension of prime degree: the expansion
`N(1 + x) = 1 + Tr(x) + Tr(y) + N(x)` with `y ∈ 𝓂[L] ^ (2m)`, each term of which is bounded
separately. -/
private theorem normShift_of_finrank_prime (hℓ : (finrank K L).Prime) : NormShift K L := by
  intro n
  refine Subgroup.map_le_iff_le_comap.2 fun y hy ↦ ?_
  obtain ⟨u, hu, huy⟩ := mem_unitFiltration_iff_exists.1 hy
  set m := psiNat K L n + 1
  obtain ⟨z, hz, hN⟩ := exists_norm_one_add_eq_of_mem_maximalIdeal_pow hℓ hu
  rw [add_sub_cancel] at hN
  have htr : ∀ w ∈ 𝓂[L] ^ m, Algebra.trace 𝒪[K] 𝒪[L] w ∈ 𝓂[K] ^ (n + 1) := fun w hw ↦ by
    rw [← Algebra.intTrace_eq_trace]
    exact intTrace_mem_maximalIdeal_pow_succ_of_mem_psiNat hw
  have hnorm : Algebra.norm 𝒪[K] ((u : 𝒪[L]) - 1) ∈ 𝓂[K] ^ (n + 1) := by
    have hf := inertiaDegree_pos (K := K) (L := L)
    have hn : n + 1 ≤ m := Nat.succ_le_succ (self_le_psiNat K L n)
    have h := norm_mem_maximalIdeal_pow_of_mem K hu
    exact Ideal.pow_le_pow_right (by nlinarith) h
  have hz' : z ∈ 𝓂[L] ^ m := Ideal.pow_le_pow_right (by omega) hz
  refine mem_unitFiltration_iff_exists.2 ⟨Algebra.normUnits 𝒪[K] u, ?_, ?_⟩
  · convert add_mem (add_mem (htr _ hu) (htr _ hz')) hnorm using 1
    rw [Algebra.coe_normUnits, hN]
    ring
  · rw [Algebra.coe_normUnits, Algebra.coe_normUnits, coe_norm_integerRing, huy]

/-- The Herbrand-shifted inclusion passes up a tower `L/F/K` in which `F/K` is Galois: the norm is
transitive, `N_{L/K} = N_{F/K} ∘ N_{L/F}`, and so is the integral inverse Herbrand function,
`ψℕ_{L/K} = ψℕ_{L/F} ∘ ψℕ_{F/K}`. -/
private theorem NormShift.trans {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Algebra K F] [ValuativeExtension K F] [Module.Finite K F]
    [IsGalois K F] [Algebra F L] [ValuativeExtension F L] [Module.Finite F L] [IsGalois F L]
    [IsScalarTower K F L] (hKF : NormShift K F)
    (hFL : NormShift F L) : NormShift K L := by
  intro n
  refine Subgroup.map_le_iff_le_comap.2 fun y hy ↦ ?_
  rw [congrFun (psiNat_tower K F L) n, Function.comp_apply] at hy
  have h := hKF n (Subgroup.mem_map_of_mem _ (hFL _ (Subgroup.mem_map_of_mem _ hy)))
  have hnorm : Algebra.normUnits K (Algebra.normUnits F y) = Algebra.normUnits K y :=
    Units.ext (by simp [Algebra.norm_norm])
  rwa [hnorm] at h

/-- The induction step: if the Herbrand-shifted inclusion holds for `L` over every local field
over which `L` has smaller degree than over `K`, it holds for `L/K`. A trivial Galois group makes
`L/K` unramified, where `ψℕ_{L/K}` is the identity; otherwise the Galois group, being solvable, has
a normal subgroup of prime index, and its fixed field `F` gives a tower `L/F/K` with `F/K` Galois
of prime degree. -/
private theorem normShift_of_forall_finrank_lt
    (ih : ∀ (F : Type v) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F] [Algebra F L] [ValuativeExtension F L] [Module.Finite F L]
      [IsGalois F L], finrank F L < finrank K L → NormShift F L) :
    NormShift K L := by
  rcases subsingleton_or_nontrivial (L ≃ₐ[K] L) with hG | hG
  · -- A trivial Galois group: `ψℕ_{L/K}` is the identity and `e(L/K) = 1`.
    intro n
    have hψ : psiNat K L n = n := (psiNat_eq_self_iff K L).2 (Subsingleton.elim _ _)
    have he : ramificationIndex K L = 1 := by
      rw [← natCard_lowerRamificationGroup_zero K L,
        Subgroup.eq_bot_of_subsingleton (lowerRamificationGroup K L 0), Subgroup.card_bot]
    simpa [hψ, he] using map_normUnits_unitFiltration_le K L (n + 1)
  · obtain ⟨H, hH, hp⟩ := Group.IsSolvable.exists_normal_index_prime (L ≃ₐ[K] L)
    let F := IntermediateField.fixedField H
    let _ := finiteIntermediateFieldValuativeRel K L F
    let _ := finiteIntermediateFieldTopology K L F
    have := finiteIntermediateField_isNonarchimedeanLocalField K L F
    have := finiteIntermediateField_valuativeExtension K L F
    have := IsGalois.tower_top_of_isGalois K F L
    have hF : finrank K F = H.index := by
      rw [IntermediateField.finrank_eq_fixingSubgroup_index,
        IntermediateField.fixingSubgroup_fixedField]
    have hlt : finrank F L < finrank K L := by
      rw [← Module.finrank_mul_finrank K F L, hF]
      have := hp.two_le
      have := Module.finrank_pos (R := F) (M := L)
      nlinarith
    exact NormShift.trans (normShift_of_finrank_prime (hF ▸ hp)) (ih F hlt)

/-- The Herbrand-shifted inclusion for every finite Galois extension `L/F` with `F` in the
universe of `L` and `[L : F] ≤ d`, by induction on `d`. -/
private theorem normShift_of_finrank_le (d : ℕ) :
    ∀ (F : Type v) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F] [Algebra F L] [ValuativeExtension F L] [Module.Finite F L]
      [IsGalois F L], finrank F L ≤ d → NormShift F L := by
  induction d with
  | zero =>
    intro F _ _ _ _ _ _ _ _ h
    exact absurd h (Nat.not_le.2 Module.finrank_pos)
  | succ d ih =>
    intro F _ _ _ _ _ _ _ _ h
    exact normShift_of_forall_finrank_lt fun F' _ _ _ _ _ _ _ _ h' ↦ ih F' (by omega)

variable (K L) in
/-- **The norm on the unit filtration, with the Herbrand shift.** For a finite Galois extension
`L/K` of nonarchimedean local fields, `N_{L/K}(U(L, ψℕ_{L/K}(n) + 1)) ⊆ U(K, n + 1)`. -/
theorem map_normUnits_unitFiltration_psiNat_add_one_le (n : ℕ) :
    (unitFiltration L (psiNat K L n + 1)).map (Algebra.normUnits K) ≤
      unitFiltration K (n + 1) :=
  normShift_of_forall_finrank_lt (fun F _ _ _ _ _ _ _ _ _ ↦ normShift_of_finrank_le _ F le_rfl) n

variable (K L) in
/-- **The norm on the unit filtration, with the Herbrand shift.** For a finite Galois extension
`L/K` of nonarchimedean local fields, `N_{L/K}(U(L, ψℕ_{L/K}(n))) ⊆ U(K, n)`. Without the shift
the inclusion `N_{L/K}(U(L, n)) ⊆ U(K, n)` fails in general for ramified extensions. -/
theorem map_normUnits_unitFiltration_psiNat_le (n : ℕ) :
    (unitFiltration L (psiNat K L n)).map (Algebra.normUnits K) ≤ unitFiltration K n := by
  cases n with
  | zero => simpa using map_normUnits_unitFiltration_le K L 0
  | succ n =>
    exact (Subgroup.map_mono (unitFiltration_antitone
      (Nat.succ_le_of_lt (psiNat_strictMono K L n.lt_succ_self)))).trans
      (map_normUnits_unitFiltration_psiNat_add_one_le K L n)

end Norm

end TauCeti
