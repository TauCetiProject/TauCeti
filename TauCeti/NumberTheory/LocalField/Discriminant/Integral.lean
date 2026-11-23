/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.NumberTheory.LocalField.Discriminant.Basic
public import TauCeti.NumberTheory.LocalField.Herbrand.Subextension
import TauCeti.Algebra.BigOperators.Group.List
import TauCeti.NumberTheory.LocalField.Different.Hilbert
import TauCeti.NumberTheory.LocalField.Different.Tower

/-!
# The discriminant exponent as an upper-numbering integral and sum over Artin slopes

For a finite separable extension `L/K` of nonarchimedean local fields in a finite Galois extension
`M/K` (`G = Gal(M/K)`, `H = embeddingSubgroup K L M`), Hilbert's formula and transitivity of the
different yield `#G_0 · δ(L/K) = ∑_{i < N} ([L : K] - [G : G_i H]) #G_i`. Herbrand's change of
variables converts this to `δ(L/K) = ∫_{u > -1} ([L : K] - [G : G^u H]) du`, and summation by parts
yields the height identity in terms of `artinSlopeList K L M` and the Galois mean slope.

## Main results

* `TauCeti.natCard_lowerRamificationGroup_zero_mul_discriminantExponent`: discrete lower-index
  formula.
* `TauCeti.intervalIntegrable_embeddingOrbitCount`,
  `TauCeti.intervalIntegrable_const_sub_embeddingOrbitCount`,
  `TauCeti.intervalIntegrable_finrank_sub_embeddingOrbitCount`,
  `TauCeti.integrableOn_finrank_sub_embeddingOrbitCount_Ioi`,
  `TauCeti.discriminantExponent_eq_integral`,
  `TauCeti.discriminantExponent_eq_intervalIntegral_of_upperRamificationGroup_le`: upper-numbering
  discriminant integral and finite truncation.
* `TauCeti.discriminantExponent_eq_sum_artinSlopeList`,
  `TauCeti.discriminantExponent_div_finrank_eq`: height identity and Galois mean slope.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter III, §4 and Chapter IV, §§1–3.
* P. Deligne, *Les corps locaux de caractéristique p, limites de corps locaux de caractéristique 0*,
  in *Représentations des groupes réductifs sur un corps local*, Hermann, 1984, Appendix, §A.6.
* J. W. Jones and D. P. Roberts, *A database of local fields*, J. Symbolic Comput. 41 (2006),
  80–97 (arXiv:math/0309309), §§3–4.
* The LMFDB Collaboration, *The L-functions and modular forms database*, local-field knowls
  `lf.galois_mean_slope` and `lf.herbrand_invariant`.
-/

public section
noncomputable section

open ValuativeRel IsLocalRing MeasureTheory TauCeti.LocalFieldsRamification

namespace TauCeti

/-! ### Discrete lower-index formula and upper-numbering integral -/

section Integral

variable (K L M : Type*)
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [ValuativeExtension K M] [Module.Finite K M] [IsGalois K M]

omit [ValuativeExtension K L] in
/-- In a tower `M/L/K` with `M/K` finite Galois, `[G : G_i H] · #G_i = [L : K] · #G_i(M/L)`. -/
private theorem index_sup_embeddingSubgroup_mul_natCard_lowerRamificationGroup
    [ValuativeExtension L M] [Module.Finite L M] (i : ℤ) :
    (lowerRamificationGroup K M i ⊔ embeddingSubgroup K L M).index *
        Nat.card (lowerRamificationGroup K M i) =
      Module.finrank K L * Nat.card (lowerRamificationGroup L M i) := by
  have : Module.Finite K L := .left K L M; have := IsGalois.tower_top_of_isGalois K L M
  set Gi := lowerRamificationGroup K M i; set H := embeddingSubgroup K L M
  have hrel_H : Gi.relIndex H * Nat.card (lowerRamificationGroup L M i) = Module.finrank L M := by
    rw [relIndex_lowerRamificationGroup_embeddingSubgroup K L M i, Subgroup.index_mul_card,
      IsGalois.card_aut_eq_finrank L M]
  have hrel_G : Gi.relIndex H * ((Gi ⊔ H).index * Nat.card Gi) =
      Module.finrank K L * Module.finrank L M := by
    rw [← Subgroup.relIndex_sup_left, ← mul_assoc, Subgroup.relIndex_mul_index le_sup_left,
      Gi.index_mul_card, IsGalois.card_aut_eq_finrank K M, Module.finrank_mul_finrank K L M]
  have hrel_pos : 0 < Gi.relIndex H :=
    Nat.pos_of_ne_zero fun h0 ↦ Module.finrank_pos.ne' (by simpa [h0] using hrel_H.symm)
  refine Nat.eq_of_mul_eq_mul_left hrel_pos ?_; rw [hrel_G, ← hrel_H]; ring

/-- **Discrete lower-index formula for the discriminant exponent.** For any `N : ℕ` with
`lowerRamificationGroup K M N = ⊥`,
`#G_0 · δ(L/K) = ∑_{i < N} ([L : K] - [G : G_i H]) · #G_i`. -/
theorem natCard_lowerRamificationGroup_zero_mul_discriminantExponent [Algebra.IsSeparable K L]
    {N : ℕ} (hN : lowerRamificationGroup K M N = ⊥) :
    Nat.card (lowerRamificationGroup K M 0) * discriminantExponent K L =
      ∑ i ∈ Finset.range N,
        (Module.finrank K L - (lowerRamificationGroup K M i ⊔ embeddingSubgroup K L M).index) *
          Nat.card (lowerRamificationGroup K M i) := by
  have := Algebra.IsAlgebraic.of_finite K M; have := Algebra.IsAlgebraic.tower_bot K L M
  have : ValuativeExtension L M := .of_isScalarTower (K := K)
  have : Module.Finite K L := .left K L M
  have : Module.Finite L M := .of_restrictScalars_finite K L M
  have := IsGalois.tower_top_of_isGalois K L M
  have hNL : lowerRamificationGroup L M N = ⊥ := by
    rw [← comap_restrictScalarsHom_lowerRamificationGroup K M L N, hN, eq_bot_iff]
    exact fun σ hσ ↦ Subgroup.mem_bot.2
      (AlgEquiv.restrictScalarsHom_injective K ((Subgroup.mem_bot.1 hσ).trans (map_one _).symm))
  have hcard_le (i : ℕ) :
      Nat.card (lowerRamificationGroup L M i) ≤ Nat.card (lowerRamificationGroup K M i) := by
    rw [← comap_restrictScalarsHom_lowerRamificationGroup K M L i,
      ← Subgroup.card_map_of_injective (AlgEquiv.restrictScalarsHom_injective K)]
    exact Subgroup.card_le_of_le (Subgroup.map_comap_le _ _)
  have hterm (i : ℕ) :
      (Module.finrank K L - (lowerRamificationGroup K M i ⊔ embeddingSubgroup K L M).index) *
          Nat.card (lowerRamificationGroup K M i) =
        Module.finrank K L * (Nat.card (lowerRamificationGroup K M i) - 1) -
          Module.finrank K L * (Nat.card (lowerRamificationGroup L M i) - 1) := by
    rw [Nat.sub_mul, index_sup_embeddingSubgroup_mul_natCard_lowerRamificationGroup K L M i,
      ← Nat.mul_sub, ← Nat.mul_sub]
    have := Nat.card_pos (α := lowerRamificationGroup K M i)
    have := Nat.card_pos (α := lowerRamificationGroup L M i)
    have := hcard_le i; congr 1; omega
  calc Nat.card (lowerRamificationGroup K M 0) * discriminantExponent K L
      = Module.finrank K L * (ramificationIndex L M * differentExponent K L) := by
        rw [natCard_lowerRamificationGroup_zero K M,
          discriminantExponent_eq_inertiaDegree_mul_differentExponent K L,
          ramificationIndex_tower (K := K) (L := L) M,
          ← ramificationIndex_mul_inertiaDegree (K := K) (L := L)]; ring
    _ = Module.finrank K L * differentExponent K M -
          Module.finrank K L * differentExponent L M := by
        rw [differentExponent_tower K L M, Nat.mul_add, Nat.add_sub_cancel_left]
    _ = ∑ i ∈ Finset.range N, (Module.finrank K L * (Nat.card (lowerRamificationGroup K M i) - 1) -
          Module.finrank K L * (Nat.card (lowerRamificationGroup L M i) - 1)) := by
        rw [differentExponent_eq_sum_range_lowerRamificationGroup K M hN,
          differentExponent_eq_sum_range_lowerRamificationGroup L M hNL, Finset.mul_sum,
          Finset.mul_sum, ← Finset.sum_tsub_distrib _ fun i _ ↦
            Nat.mul_le_mul_left _ (Nat.sub_le_sub_right (hcard_le i) 1)]
    _ = _ := Finset.sum_congr rfl fun i _ ↦ (hterm i).symm

private def herbrandPartition (k : ℕ) : ℝ :=
  (herbrand K M ⟨(k : ℝ) - 1, Set.mem_Ici.2 (by linarith [Nat.cast_nonneg (α := ℝ) k])⟩ : ℝ)

private theorem herbrandPartition_zero : herbrandPartition K M 0 = -1 := by
  simp [herbrandPartition, herbrand_of_coe_le_zero]

private theorem herbrandPartition_succ (i : ℕ) : herbrandPartition K M (i + 1) =
    (herbrand K M ⟨(i : ℝ), Nat.cast_mem_ramificationIndexDomain i⟩ : ℝ) := by
  simp [herbrandPartition]

private theorem herbrandPartition_one : herbrandPartition K M 1 = 0 := by simp [herbrandPartition]

private theorem herbrandPartition_sub (i : ℕ) :
    herbrandPartition K M (i + 1) - herbrandPartition K M i =
      (Nat.card (lowerRamificationGroup K M i) : ℝ) / Nat.card (lowerRamificationGroup K M 0) := by
  cases i with
  | zero =>
    rw [herbrandPartition_one K M, herbrandPartition_zero K M, Nat.cast_zero,
      div_self (by exact_mod_cast Nat.card_pos.ne' : (Nat.card _ : ℝ) ≠ 0)]; norm_num
  | succ m =>
    rw [herbrandPartition_succ K M (m + 1), herbrandPartition_succ K M m,
      coe_herbrand_of_mem_Icc K M m (by push_cast; linarith) (by push_cast; linarith),
      coe_herbrand_of_coe_eq_natCast K M m rfl]; push_cast; ring

private theorem herbrandPartition_le_succ (i : ℕ) :
    herbrandPartition K M i ≤ herbrandPartition K M (i + 1) := by
  linarith [herbrandPartition_sub K M i,
    div_nonneg (Nat.cast_nonneg (α := ℝ) (Nat.card (lowerRamificationGroup K M i)))
      (Nat.cast_nonneg (α := ℝ) (Nat.card (lowerRamificationGroup K M 0)))]

omit [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L] in
private theorem embeddingOrbitCount_eq_on_herbrandPartition (i : ℕ) {u : ℝ}
    (hu : u ∈ Set.Ioc (herbrandPartition K M i) (herbrandPartition K M (i + 1))) :
    embeddingOrbitCount K L M ⟨max u (-1), le_max_right u (-1)⟩ =
      (lowerRamificationGroup K M i ⊔ embeddingSubgroup K L M).index := by
  have hu_ge : -1 ≤ u := (herbrand K M _).property.trans hu.1.le
  rw [(Subtype.ext (max_eq_left hu_ge) :
    (⟨max u (-1), le_max_right u (-1)⟩ : RamificationIndexDomain) = ⟨u, hu_ge⟩),
    embeddingOrbitCount_def]
  congr 2
  cases i with
  | zero =>
    have hu_le : u ≤ 0 := herbrandPartition_one K M ▸ hu.2
    rw [upperRamificationGroup_of_coe_le_zero K M hu_le]
    exact lowerRamificationGroupReal_eq_of_sub_one_lt_of_le K M (i := 0)
      (by simpa [herbrandPartition_zero K M] using hu.1) (by simpa using hu_le)
  | succ m =>
    rw [herbrandPartition_succ K M m, herbrandPartition_succ K M (m + 1)] at hu
    exact upperRamificationGroup_eq_of_herbrand_lt_of_le K M (Subtype.mk_lt_mk.2 hu.1)
      (Subtype.mk_le_mk.2 hu.2)

omit [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L] in
private theorem finrank_sub_embeddingOrbitCount_eq_zero_on_Ioi {N : ℕ}
    (hN : lowerRamificationGroup K M N = ⊥) :
    Set.EqOn (fun u : ℝ ↦ (Module.finrank K L : ℝ) -
        embeddingOrbitCount K L M ⟨max u (-1), le_max_right u (-1)⟩)
      0 (Set.Ioi (herbrandPartition K M N)) := fun u hu ↦ by
  have hu_ge : -1 ≤ u := (herbrand K M _).property.trans (Set.mem_Ioi.1 hu).le
  have hocc : embeddingOrbitCount K L M ⟨u, hu_ge⟩ = Module.finrank K L :=
    embeddingOrbitCount_eq_finrank_of_lowerRamificationGroup_eq_bot K L M hN
      (Subtype.mk_lt_mk.2 (Set.mem_Ioi.1 hu))
  simp [(Subtype.ext (max_eq_left hu_ge) :
    (⟨max u (-1), le_max_right u (-1)⟩ : RamificationIndexDomain) = ⟨u, hu_ge⟩), hocc]

omit [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L] in
/-- The extended orbit count `u ↦ [G : G^{max u (-1)} H]` is interval-integrable on every compact
interval. -/
theorem intervalIntegrable_embeddingOrbitCount (a b : ℝ) :
    IntervalIntegrable (fun u : ℝ ↦
        (embeddingOrbitCount K L M ⟨max u (-1), le_max_right u (-1)⟩ : ℝ)) volume a b :=
  Monotone.intervalIntegrable fun _ _ h ↦
    Nat.cast_le.2 (embeddingOrbitCount_mono K L M (Subtype.mk_le_mk.2 (max_le_max_right _ h)))

omit [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L] in
/-- For any `c : ℝ`, `u ↦ c - [G : G^{max u (-1)} H]` is interval-integrable on every compact
interval. -/
theorem intervalIntegrable_const_sub_embeddingOrbitCount (c a b : ℝ) :
    IntervalIntegrable (fun u : ℝ ↦
        c - (embeddingOrbitCount K L M ⟨max u (-1), le_max_right u (-1)⟩ : ℝ)) volume a b :=
  intervalIntegrable_const.sub (intervalIntegrable_embeddingOrbitCount K L M a b)

omit [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L] in
/-- `u ↦ [L : K] - [G : G^{max u (-1)} H]` is interval-integrable on every compact interval. -/
theorem intervalIntegrable_finrank_sub_embeddingOrbitCount (a b : ℝ) :
    IntervalIntegrable (fun u : ℝ ↦ (Module.finrank K L : ℝ) -
        embeddingOrbitCount K L M ⟨max u (-1), le_max_right u (-1)⟩) volume a b :=
  intervalIntegrable_const_sub_embeddingOrbitCount K L M _ a b

omit [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L] in
/-- The function `u ↦ [L : K] - [G : G^{max u (-1)} H]` is integrable on `(-1, ∞)`. -/
theorem integrableOn_finrank_sub_embeddingOrbitCount_Ioi :
    IntegrableOn (fun u : ℝ ↦ (Module.finrank K L : ℝ) -
        embeddingOrbitCount K L M ⟨max u (-1), le_max_right u (-1)⟩) (Set.Ioi (-1 : ℝ)) := by
  set N := (largestLowerJump K M).toNat + 1
  have hge : (-1 : ℝ) ≤ herbrandPartition K M N := (herbrand K M _).property
  rw [← Set.Ioc_union_Ioi_eq_Ioi hge]
  exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hge).1
      (intervalIntegrable_finrank_sub_embeddingOrbitCount K L M (-1) _)).union
    ((integrableOn_congr_fun (finrank_sub_embeddingOrbitCount_eq_zero_on_Ioi K L M
      (lowerRamificationGroup_toNat_largestLowerJump_add_one K M)) measurableSet_Ioi).2
      integrableOn_zero)

/-- **The discriminant exponent as an upper-numbering integral.**
`δ(L/K) = ∫_{u > -1} ([L : K] - [G : G^u H]) du`. -/
theorem discriminantExponent_eq_integral [Algebra.IsSeparable K L] :
    (discriminantExponent K L : ℝ) =
      ∫ u in Set.Ioi (-1 : ℝ), ((Module.finrank K L : ℝ) -
        embeddingOrbitCount K L M ⟨max u (-1), le_max_right u (-1)⟩) := by
  set f : ℝ → ℝ := fun u ↦ (Module.finrank K L : ℝ) -
    embeddingOrbitCount K L M ⟨max u (-1), le_max_right u (-1)⟩
  set N := (largestLowerJump K M).toNat + 1
  have hbot := lowerRamificationGroup_toNat_largestLowerJump_add_one K M
  have hIoi := integrableOn_finrank_sub_embeddingOrbitCount_Ioi K L M
  have htail : ∫ u in Set.Ioi (herbrandPartition K M N), f u = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun _ hu ↦
      finrank_sub_embeddingOrbitCount_eq_zero_on_Ioi K L M hbot hu
  have hge : (-1 : ℝ) ≤ herbrandPartition K M N := (herbrand K M _).property
  have h0 : ∫ u in (-1 : ℝ)..herbrandPartition K M N, f u =
      ∫ u in herbrandPartition K M 0..herbrandPartition K M N, f u := by
    rw [herbrandPartition_zero K M]
  rw [← intervalIntegral.integral_interval_add_Ioi hIoi
      (hIoi.mono_set (Set.Ioi_subset_Ioi hge)), htail, add_zero, h0,
    ← intervalIntegral.sum_integral_adjacent_intervals
      (fun k _ ↦ intervalIntegrable_finrank_sub_embeddingOrbitCount K L M _ _)]
  have hstep (k : ℕ) : ∫ u in herbrandPartition K M k..herbrandPartition K M (k + 1), f u =
      ((Module.finrank K L : ℝ) - (lowerRamificationGroup K M k ⊔ embeddingSubgroup K L M).index) *
        ((Nat.card (lowerRamificationGroup K M k) : ℝ) / Nat.card (lowerRamificationGroup K M 0)) :=
    by rw [intervalIntegral.integral_congr_ae (g := fun _ ↦ (Module.finrank K L : ℝ) -
          (lowerRamificationGroup K M k ⊔ embeddingSubgroup K L M).index)
        (Filter.Eventually.of_forall fun _ hu ↦ by
          simp only [f, embeddingOrbitCount_eq_on_herbrandPartition K L M k
            (Set.uIoc_of_le (herbrandPartition_le_succ K M k) ▸ hu)]),
      intervalIntegral.integral_const, smul_eq_mul, herbrandPartition_sub K M k, mul_comm]
  have hG0 : (Nat.card (lowerRamificationGroup K M 0) : ℝ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hnat := congrArg (Nat.cast (R := ℝ))
    (natCard_lowerRamificationGroup_zero_mul_discriminantExponent K L M hbot)
  push_cast at hnat; apply mul_left_cancel₀ hG0
  rw [Finset.sum_congr rfl fun k _ ↦ hstep k, hnat, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Nat.cast_sub (index_embeddingSubgroup K L M ▸ Subgroup.index_antitone le_sup_right)]
  field_simp [hG0]

/-- If `upperRamificationGroup K M v ≤ embeddingSubgroup K L M`, the upper-numbering discriminant
integral truncates to the finite interval `(-1)..v`. -/
theorem discriminantExponent_eq_intervalIntegral_of_upperRamificationGroup_le
    [Algebra.IsSeparable K L] {v : RamificationIndexDomain}
    (hv : upperRamificationGroup K M v ≤ embeddingSubgroup K L M) :
    (discriminantExponent K L : ℝ) =
      ∫ u in (-1 : ℝ)..v, ((Module.finrank K L : ℝ) -
        embeddingOrbitCount K L M ⟨max u (-1), le_max_right u (-1)⟩) := by
  have hIoi := integrableOn_finrank_sub_embeddingOrbitCount_Ioi K L M
  have hv0 : ∫ u in Set.Ioi (v : ℝ), ((Module.finrank K L : ℝ) -
      embeddingOrbitCount K L M ⟨max u (-1), le_max_right u (-1)⟩) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun u hu ↦ by
      have hsub : upperRamificationGroup K M ⟨max u (-1), le_max_right u (-1)⟩ ≤
          embeddingSubgroup K L M := (upperRamificationGroup_antitone K M
        (Subtype.mk_le_mk.2 ((Set.mem_Ioi.1 hu).le.trans (le_max_left _ _)))).trans hv
      rw [(embeddingOrbitCount_eq_finrank_iff K L M _).2 hsub, sub_self]
  rw [discriminantExponent_eq_integral K L M,
    ← intervalIntegral.integral_interval_add_Ioi hIoi (hIoi.mono_set (Set.Ioi_subset_Ioi v.prop)),
    hv0, add_zero]

/-! ### The height identity and Galois mean slope -/

private def wildStepCount (k : ℕ) : ℕ :=
  ∑ r ∈ Finset.range k, Nat.log (ringChar 𝓀[K])
    ((lowerRamificationGroup K M ((r + 2 : ℕ) : ℤ) ⊔ embeddingSubgroup K L M).relIndex
      (lowerRamificationGroup K M ((r + 1 : ℕ) : ℤ) ⊔ embeddingSubgroup K L M))

private def wildIndexRatio (k : ℕ) : ℝ :=
  (ringChar 𝓀[K] : ℝ) ^ wildStepCount K L M k / (ringChar 𝓀[K] : ℝ) ^ wildRamificationExponent K L

private theorem wildStepCount_largestLowerJump :
    wildStepCount K L M (largestLowerJump K M).toNat = wildRamificationExponent K L := by
  have hlen := length_artinSlopeList K L M
  rw [artinSlopeList_def, List.length_flatMap, ← List.sum_toFinset _ List.nodup_range,
    List.toFinset_range] at hlen
  simpa [List.length_replicate, wildStepCount] using hlen

/-- Rewrites `δ(L/K)` as the tame contribution `f (e - 1)` plus the wild lower-step sum weighted
by `wildIndexRatio K L M j`. -/
private theorem discriminantExponent_eq_tame_add_wild_sum [Algebra.IsSeparable K L] :
    (discriminantExponent K L : ℝ) = (inertiaDegree K L : ℝ) * ((ramificationIndex K L : ℝ) - 1) +
      (inertiaDegree K L : ℝ) * (ramificationIndex K L : ℝ) *
        ∑ j ∈ Finset.range (largestLowerJump K M).toNat, (1 - wildIndexRatio K L M j) *
          (herbrandPartition K M (j + 2) - herbrandPartition K M (j + 1)) := by
  have hpw : (ringChar 𝓀[K] : ℝ) ^ wildRamificationExponent K L ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 (CharP.prime_ringChar 𝓀[K]).ne_zero)
  have hG0 : (Nat.card (lowerRamificationGroup K M 0) : ℝ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hnat := congrArg (Nat.cast (R := ℝ))
    (natCard_lowerRamificationGroup_zero_mul_discriminantExponent K L M
      (lowerRamificationGroup_toNat_largestLowerJump_add_one K M))
  push_cast at hnat; rw [Finset.sum_range_succ'] at hnat
  have h0 : (((Module.finrank K L -
      (lowerRamificationGroup K M (0 : ℕ) ⊔ embeddingSubgroup K L M).index : ℕ) : ℝ) *
        Nat.card (lowerRamificationGroup K M (0 : ℕ))) =
      (inertiaDegree K L : ℝ) * ((ramificationIndex K L : ℝ) - 1) *
        Nat.card (lowerRamificationGroup K M 0) := by
    rw [Nat.cast_zero, index_lowerRamificationGroup_zero_sup_embeddingSubgroup K L M,
      Nat.cast_sub (ramificationIndex_mul_inertiaDegree (K := K) (L := L) ▸
        Nat.le_mul_of_pos_left _ ramificationIndex_pos),
      ← ramificationIndex_mul_inertiaDegree (K := K) (L := L)]; push_cast; ring
  have hj (j : ℕ) : (((Module.finrank K L -
      (lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ) ⊔ embeddingSubgroup K L M).index : ℕ) : ℝ) *
        Nat.card (lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ))) =
      (inertiaDegree K L : ℝ) * (ramificationIndex K L : ℝ) * ((1 - wildIndexRatio K L M j) *
        (herbrandPartition K M (j + 2) - herbrandPartition K M (j + 1))) *
          Nat.card (lowerRamificationGroup K M 0) := by
    have hidx : ((lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ) ⊔
        embeddingSubgroup K L M).index : ℝ) =
        (inertiaDegree K L : ℝ) * (ramificationIndex K L : ℝ) * wildIndexRatio K L M j := by
      rw [index_lowerRamificationGroup_succ_sup_embeddingSubgroup K L M j,
        ← tameRamificationIndex_mul_pow_wildRamificationExponent K L]
      dsimp only [wildIndexRatio, wildStepCount]; push_cast; field_simp [hpw]
    rw [Nat.cast_sub (index_embeddingSubgroup K L M ▸ Subgroup.index_antitone le_sup_right), hidx,
      ← ramificationIndex_mul_inertiaDegree (K := K) (L := L), herbrandPartition_sub K M (j + 1)]
    push_cast; field_simp [hG0]
  apply mul_right_cancel₀ hG0
  rw [mul_comm, hnat, h0, Finset.sum_congr rfl fun j _ ↦ hj j, add_mul, mul_assoc, Finset.mul_sum,
    Finset.sum_mul]; ring

/-- Evaluates the Artin-slope weighted sum via `List.sum_get_flatMap_replicate_range` and
geometric telescoping across each wild step block. -/
private theorem sum_artinSlopeList_weight_eq :
    (∑ i : Fin (artinSlopeList K L M).length, ((ringChar 𝓀[K] : ℝ) - 1) *
        ((artinSlopeList K L M).get i - 1) /
        (ringChar 𝓀[K] : ℝ) ^ ((artinSlopeList K L M).length - i.val)) =
      ∑ j ∈ Finset.range (largestLowerJump K M).toNat,
        (wildIndexRatio K L M (j + 1) - wildIndexRatio K L M j) *
          herbrandPartition K M (j + 2) := by
  let p := ringChar 𝓀[K]; let w := wildRamificationExponent K L
  have hp_ne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (CharP.prime_ringChar 𝓀[K]).ne_zero
  have hpw_ne : (p : ℝ) ^ w ≠ 0 := pow_ne_zero w hp_ne
  let d : ℕ → ℕ := fun j ↦ Nat.log p
    ((lowerRamificationGroup K M ((j + 2 : ℕ) : ℤ) ⊔ embeddingSubgroup K L M).relIndex
      (lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ) ⊔ embeddingSubgroup K L M))
  have hlen_in : (∑ i : Fin (artinSlopeList K L M).length,
      ((p : ℝ) - 1) * ((artinSlopeList K L M).get i - 1) /
        (p : ℝ) ^ ((artinSlopeList K L M).length - i.val)) =
      ∑ i : Fin (artinSlopeList K L M).length,
        ((p : ℝ) - 1) * ((artinSlopeList K L M).get i - 1) / (p : ℝ) ^ (w - i.val) :=
    Finset.sum_congr rfl fun i _ ↦ by
      congr 2; exact congrArg (· - i.val) (length_artinSlopeList K L M)
  rw [hlen_in, artinSlopeList_def K L M, List.sum_get_flatMap_replicate_range
    (largestLowerJump K M).toNat d _ (fun a idx ↦ ((p : ℝ) - 1) * (a - 1) / (p : ℝ) ^ (w - idx))]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hSsucc : wildStepCount K L M (j + 1) = wildStepCount K L M j + d j :=
    Finset.sum_range_succ d j
  have hSj1_le : wildStepCount K L M (j + 1) ≤ w :=
    (Finset.sum_le_sum_of_subset (Finset.range_subset_range.2
      (Nat.succ_le_of_lt (Finset.mem_range.1 hj)))).trans_eq (wildStepCount_largestLowerJump K L M)
  have hinner (r : ℕ) (hr : r ∈ Finset.range (d j)) :
      ((p : ℝ) - 1) * (((herbrand K M ⟨((j + 1 : ℕ) : ℝ),
            Nat.cast_mem_ramificationIndexDomain (j + 1)⟩ : ℝ) + 1) - 1) /
          (p : ℝ) ^ (w - (wildStepCount K L M j + r)) =
        (((p : ℝ) ^ (wildStepCount K L M j + (r + 1)) -
            (p : ℝ) ^ (wildStepCount K L M j + r)) / (p : ℝ) ^ w) *
          herbrandPartition K M (j + 2) := by
    have hle_w : wildStepCount K L M j + r ≤ w := by have := Finset.mem_range.1 hr; omega
    have hpow : (p : ℝ) ^ (wildStepCount K L M j + r) *
        (p : ℝ) ^ (w - (wildStepCount K L M j + r)) = (p : ℝ) ^ w := by
      rw [← pow_add, Nat.add_sub_of_le hle_w]
    rw [herbrandPartition_succ K M (j + 1)]
    field_simp [hpw_ne, pow_ne_zero (w - (wildStepCount K L M j + r)) hp_ne]
    rw [← hpow, ← add_assoc, pow_succ]; ring
  have hsum_eq : ∑ k ∈ Finset.range j, d k = wildStepCount K L M j := rfl
  simp only [hsum_eq]
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_mul, ← Finset.sum_div,
    Finset.sum_range_sub (fun r ↦ (p : ℝ) ^ (wildStepCount K L M j + r)) (d j)]
  simp only [add_zero, ← hSsucc, sub_div, wildIndexRatio, p, w]

/-- **The height identity.** For a finite separable extension `L/K` read inside a finite Galois
extension `M/K`,
`δ(L/K) = f (e - 1) + f e ∑_{i < w} (p - 1) (a_i - 1) / p^{w - i}`. -/
theorem discriminantExponent_eq_sum_artinSlopeList [Algebra.IsSeparable K L] :
    (discriminantExponent K L : ℝ) =
      (inertiaDegree K L : ℝ) * ((ramificationIndex K L : ℝ) - 1) +
        (inertiaDegree K L : ℝ) * (ramificationIndex K L : ℝ) *
          ∑ i : Fin (artinSlopeList K L M).length, ((ringChar 𝓀[K] : ℝ) - 1) *
            ((artinSlopeList K L M).get i - 1) /
            (ringChar 𝓀[K] : ℝ) ^ ((artinSlopeList K L M).length - i.val) := by
  have hpw : (ringChar 𝓀[K] : ℝ) ^ wildRamificationExponent K L ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 (CharP.prime_ringChar 𝓀[K]).ne_zero)
  rw [discriminantExponent_eq_tame_add_wild_sum K L M, sum_artinSlopeList_weight_eq K L M]
  congr 2
  have habp : ∑ j ∈ Finset.range (largestLowerJump K M).toNat, (1 - wildIndexRatio K L M j) *
        (herbrandPartition K M (j + 2) - herbrandPartition K M (j + 1)) =
      ∑ j ∈ Finset.range (largestLowerJump K M).toNat,
        (((1 - wildIndexRatio K L M (j + 1)) * herbrandPartition K M (j + 2) -
            (1 - wildIndexRatio K L M j) * herbrandPartition K M (j + 1)) +
          (wildIndexRatio K L M (j + 1) - wildIndexRatio K L M j) *
            herbrandPartition K M (j + 2)) := Finset.sum_congr rfl fun _ _ ↦ by ring
  rw [habp, Finset.sum_add_distrib,
    Finset.sum_range_sub fun k ↦ (1 - wildIndexRatio K L M k) * herbrandPartition K M (k + 1)]
  simp only [wildIndexRatio, wildStepCount_largestLowerJump K L M, div_self hpw,
    herbrandPartition_one K M]; ring

end Integral

/-- **The weighted formula for the Galois mean slope.** Dividing the height identity for a finite
Galois extension `M/K` by `[M : K] = e(M/K) · f(M/K)` expresses `δ(M/K) / [M : K]` in terms of
`[G_0 : G_1]` and `artinSlopeList K M M`. -/
theorem discriminantExponent_div_finrank_eq (K M : Type*)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
    [Algebra K M] [ValuativeExtension K M] [Module.Finite K M] [IsGalois K M] :
    (discriminantExponent K M : ℝ) / Module.finrank K M =
      1 - 1 / (((lowerRamificationGroup K M 1).relIndex (lowerRamificationGroup K M 0) : ℝ) *
          (ringChar 𝓀[K] : ℝ) ^ (artinSlopeList K M M).length) +
        ((ringChar 𝓀[K] : ℝ) - 1) *
          ∑ i : Fin (artinSlopeList K M M).length,
            ((artinSlopeList K M M).get i - 1) /
              (ringChar 𝓀[K] : ℝ) ^ ((artinSlopeList K M M).length - i.val) := by
  have he_eq : ((lowerRamificationGroup K M 1).relIndex (lowerRamificationGroup K M 0) : ℝ) *
      (ringChar 𝓀[K] : ℝ) ^ (artinSlopeList K M M).length = ramificationIndex K M := by
    rw [relIndex_lowerRamificationGroup_one_zero K M, length_artinSlopeList K M M]
    exact_mod_cast tameRamificationIndex_mul_pow_wildRamificationExponent K M
  have hfin : (Module.finrank K M : ℝ) = (ramificationIndex K M : ℝ) * inertiaDegree K M := by
    exact_mod_cast (ramificationIndex_mul_inertiaDegree (K := K) (L := M)).symm
  rw [discriminantExponent_eq_sum_artinSlopeList K M M,
    Finset.sum_congr rfl fun _ _ ↦ mul_div_assoc _ _ _, ← Finset.mul_sum, he_eq, hfin]
  field_simp [(by exact_mod_cast ramificationIndex_pos.ne' : (ramificationIndex K M : ℝ) ≠ 0),
    (by exact_mod_cast inertiaDegree_pos.ne' : (inertiaDegree K M : ℝ) ≠ 0)]

end TauCeti
