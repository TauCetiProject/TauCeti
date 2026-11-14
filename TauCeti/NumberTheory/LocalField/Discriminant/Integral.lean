/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.NumberTheory.LocalField.Discriminant.Basic
public import TauCeti.NumberTheory.LocalField.Herbrand.Subextension
import Mathlib.Data.List.GetD
import TauCeti.NumberTheory.LocalField.Different.Hilbert
import TauCeti.NumberTheory.LocalField.Different.Tower

/-!
# The discriminant exponent as an upper-numbering integral and sum over Artin slopes

Let `L/K` be a finite separable extension of nonarchimedean local fields contained in a finite
Galois extension `M/K`, with `G = Gal(M/K)` and `H = Gal(M/L) = embeddingSubgroup K L M`. Reading
Hilbert's formula `d = ∑_{i ≥ 0} (#G_i - 1)` for `M/K` and `M/L` alongside transitivity of the
different (`d(M/K) = d(M/L) + e(M/L) d(L/K)`) expresses `#G_0 · δ(L/K)` as the finite lower-index
sum

`#G_0 · δ(L/K) = ∑_{i < N} ([L : K] - [G : G_i H]) #G_i`

for any `N` with `G_N = 1`. Changing variables by the Herbrand function `φ_{M/K}` (whose step
lengths are `φ_{M/K}(i) - φ_{M/K}(i - 1) = #G_i / #G_0`) converts this discrete identity into the
upper-numbering integral formula for the discriminant exponent,

`δ(L/K) = ∫_{u > -1} ([L : K] - [G : G^u H]) du`,

and summation by parts along the wild steps `[G_{j+1} H : G_{j+2} H] = p^{d_j}` yields the height
identity expressing `δ(L/K)` through `artinSlopeList K L M`, together with its specialization to
the Galois mean slope `δ(M/K) / [M : K]`.

## Main results

* `TauCeti.natCard_lowerRamificationGroup_zero_mul_discriminantExponent`: the discrete lower-index
  formula `#G_0 · δ(L/K) = ∑_{i < N} ([L : K] - [G : G_i H]) #G_i`.
* `TauCeti.integrableOn_finrank_sub_embeddingOrbitCount_Ioi`: integrability of
  `u ↦ [L : K] - [G : G^u H]` on `(-1, ∞)`.
* `TauCeti.discriminantExponent_eq_integral`: the upper-numbering integral formula
  `δ(L/K) = ∫_{u > -1} ([L : K] - [G : G^u H]) du`.
* `TauCeti.discriminantExponent_eq_intervalIntegral_of_upperRamificationGroup_le`: truncation of
  the discriminant integral to `(-1)..v` whenever `G^v ≤ H`.
* `TauCeti.discriminantExponent_eq_sum_artinSlopeList`: the height identity expressing `δ(L/K)`
  in terms of `inertiaDegree K L`, `ramificationIndex K L`, and `artinSlopeList K L M`.
* `TauCeti.discriminantExponent_div_finrank_eq`: the weighted formula for the Galois mean slope
  `δ(M/K) / [M : K]`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter III, §4 and Chapter IV, §§1–3.
* P. Deligne, *Les corps locaux de caractéristique p, limites de corps locaux de caractéristique 0*,
  Appendix A.6.
-/

public section
noncomputable section

open ValuativeRel IsLocalRing MeasureTheory TauCeti.LocalFieldsRamification

namespace TauCeti

/-! ### List indexing helpers for `flatMap` of `replicate` -/

private theorem sum_fin_get_eq_sum_range_getD (l : List ℝ) (g : ℝ → ℕ → ℝ) :
    ∑ i : Fin l.length, g (l.get i) i.1 =
      ∑ k ∈ Finset.range l.length, g (l.getD k 0) k := by
  have hcongr : (∑ i : Fin l.length, g (l.get i) i.1) =
      ∑ i : Fin l.length, g (l.getD i.1 0) i.1 :=
    Finset.sum_congr rfl fun i _ ↦ by rw [List.getD_eq_get]
  rw [hcongr, Fin.sum_univ_eq_sum_range fun k ↦ g (l.getD k 0) k]

private theorem length_flatMap_replicate_range (n : ℕ) (d : ℕ → ℕ) (val : ℕ → ℝ) :
    ((List.range n).flatMap fun j ↦ List.replicate (d j) (val j)).length =
      ∑ k ∈ Finset.range n, d k := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.length_append,
      List.length_replicate, ih, Finset.sum_range_succ]

private theorem sum_range_getD_flatMap_replicate (n : ℕ) (d : ℕ → ℕ) (val : ℕ → ℝ)
    (g : ℝ → ℕ → ℝ) :
    ∑ k ∈ Finset.range ((List.range n).flatMap fun j ↦ List.replicate (d j) (val j)).length,
        g (((List.range n).flatMap fun j ↦ List.replicate (d j) (val j)).getD k 0) k =
      ∑ j ∈ Finset.range n,
        ∑ r ∈ Finset.range (d j), g (val j) ((∑ k ∈ Finset.range j, d k) + r) := by
  induction n with
  | zero => simp
  | succ m ih =>
    let xs := (List.range m).flatMap fun j ↦ List.replicate (d j) (val j)
    let ys := List.replicate (d m) (val m)
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    change ∑ k ∈ Finset.range (xs ++ ys).length, g ((xs ++ ys).getD k 0) k = _
    rw [List.length_append, Finset.sum_range_add, Finset.sum_range_succ]
    congr 1
    · rw [← ih]
      exact Finset.sum_congr rfl fun k hk ↦ by
        rw [List.getD_append _ _ _ _ (Finset.mem_range.1 hk)]
    · rw [show ys.length = d m from List.length_replicate]
      refine Finset.sum_congr rfl fun r hr ↦ ?_
      rw [List.getD_append_right _ _ _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
      dsimp only [ys, xs]
      rw [List.getD_replicate (h := Finset.mem_range.1 hr), length_flatMap_replicate_range]

/-! ### Discrete lower-index formula and upper-numbering integral -/

section Integral

variable (K L M : Type*)
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [ValuativeExtension K M] [Module.Finite K M] [IsGalois K M]

/-- In a tower `M/L/K` with `M/K` finite Galois, for every lower index `i : ℤ`,
`[G : G_i H] · #G_i = [L : K] · #G_i(M/L)`. -/
private theorem index_sup_embeddingSubgroup_mul_natCard_lowerRamificationGroup (i : ℤ) :
    haveI : Algebra.IsAlgebraic K M := Algebra.IsAlgebraic.of_finite K M
    haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.tower_bot K L M
    haveI : ValuativeExtension L M := .of_isScalarTower (K := K)
    haveI : Module.Finite L M := .of_restrictScalars_finite K L M
    (lowerRamificationGroup K M i ⊔ embeddingSubgroup K L M).index *
        Nat.card (lowerRamificationGroup K M i) =
      Module.finrank K L * Nat.card (lowerRamificationGroup L M i) := by
  have : Algebra.IsAlgebraic K M := Algebra.IsAlgebraic.of_finite K M
  have : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.tower_bot K L M
  have : ValuativeExtension L M := .of_isScalarTower (K := K)
  have : Module.Finite K L := Module.Finite.left K L M
  have : Module.Finite L M := .of_restrictScalars_finite K L M
  set Gi := lowerRamificationGroup K M i
  set H := embeddingSubgroup K L M
  have hcard_sub : Nat.card (Gi.subgroupOf H) = Nat.card (lowerRamificationGroup L M i) := by
    calc Nat.card (Gi.subgroupOf H)
        = Nat.card ↥(Gi ⊓ H) := by
          rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective H.subtype_injective]
      _ = Nat.card ↥((AlgEquiv.restrictScalarsHom (S := L) K :
            (M ≃ₐ[L] M) →* (M ≃ₐ[K] M)).range ⊓ Gi) := by
          rw [range_restrictScalarsHom_eq_embeddingSubgroup K L M, inf_comm]
      _ = Nat.card ↥((Gi.comap (AlgEquiv.restrictScalarsHom (S := L) K)).map
            (AlgEquiv.restrictScalarsHom (S := L) K)) := by
          rw [Subgroup.map_comap_eq]
      _ = Nat.card ↥(Gi.comap (AlgEquiv.restrictScalarsHom (S := L) K)) :=
          Subgroup.card_map_of_injective (AlgEquiv.restrictScalarsHom_injective K)
      _ = Nat.card (lowerRamificationGroup L M i) := by
          rw [comap_restrictScalarsHom_lowerRamificationGroup K M L i]
  have hrel_H : Gi.relIndex H * Nat.card (lowerRamificationGroup L M i) = Module.finrank L M := by
    rw [← hcard_sub, Subgroup.relIndex, Subgroup.index_mul_card, natCard_embeddingSubgroup K L M]
  have hrel_pos : 0 < Gi.relIndex H := by
    by_contra h0
    rw [Nat.not_lt, Nat.le_zero] at h0
    rw [h0, zero_mul] at hrel_H
    exact Module.finrank_pos.ne' hrel_H.symm
  have hrel_G : Gi.relIndex H *
      ((Gi ⊔ H).index * Nat.card Gi) = Module.finrank K L * Module.finrank L M := by
    calc Gi.relIndex H * ((Gi ⊔ H).index * Nat.card Gi)
        = (Gi.relIndex (Gi ⊔ H) * (Gi ⊔ H).index) * Nat.card Gi := by
          rw [Subgroup.relIndex_sup_left, mul_assoc]
      _ = Gi.index * Nat.card Gi := by rw [Subgroup.relIndex_mul_index le_sup_left]
      _ = Nat.card (M ≃ₐ[K] M) := Gi.index_mul_card
      _ = Module.finrank K M := IsGalois.card_aut_eq_finrank K M
      _ = Module.finrank K L * Module.finrank L M := (Module.finrank_mul_finrank K L M).symm
  refine Nat.eq_of_mul_eq_mul_left hrel_pos ?_
  rw [hrel_G, ← hrel_H]
  ring

omit [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L] in
/-- Every index `[G : G_i H]` is at most `[L : K] = [G : H]`. -/
private theorem index_lowerRamificationGroup_sup_embeddingSubgroup_le_finrank (i : ℤ) :
    (lowerRamificationGroup K M i ⊔ embeddingSubgroup K L M).index ≤ Module.finrank K L := by
  have : Module.Finite K L := Module.Finite.left K L M
  have : Module.Finite L M := .of_restrictScalars_finite K L M
  set K₁ := lowerRamificationGroup K M i ⊔ embeddingSubgroup K L M
  set H := embeddingSubgroup K L M
  have hmul := Subgroup.relIndex_mul_index (le_sup_right : H ≤ K₁)
  rw [index_embeddingSubgroup K L M] at hmul
  have hpos : 0 < H.relIndex K₁ := by
    by_contra h0
    rw [Nat.not_lt, Nat.le_zero] at h0
    rw [h0, zero_mul] at hmul
    exact Module.finrank_pos.ne' hmul.symm
  exact hmul ▸ Nat.le_mul_of_pos_left _ hpos

/-- **Discrete lower-index formula for the discriminant exponent.** For any `N : ℕ` with
`lowerRamificationGroup K M N = ⊥`,
`#G_0 · δ(L/K) = ∑_{i < N} ([L : K] - [G : G_i H]) · #G_i`. -/
theorem natCard_lowerRamificationGroup_zero_mul_discriminantExponent [Algebra.IsSeparable K L]
    {N : ℕ} (hN : lowerRamificationGroup K M N = ⊥) :
    Nat.card (lowerRamificationGroup K M 0) * discriminantExponent K L =
      ∑ i ∈ Finset.range N,
        (Module.finrank K L -
          (lowerRamificationGroup K M i ⊔ embeddingSubgroup K L M).index) *
            Nat.card (lowerRamificationGroup K M i) := by
  have : Algebra.IsAlgebraic K M := Algebra.IsAlgebraic.of_finite K M
  have : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.tower_bot K L M
  have : ValuativeExtension L M := .of_isScalarTower (K := K)
  have : Module.Finite K L := Module.Finite.left K L M
  have : Module.Finite L M := .of_restrictScalars_finite K L M
  have := IsGalois.tower_top_of_isGalois K L M
  have hNL : lowerRamificationGroup L M N = ⊥ := by
    rw [← comap_restrictScalarsHom_lowerRamificationGroup K M L N, hN, eq_bot_iff]
    intro σ hσ
    rw [Subgroup.mem_comap, Subgroup.mem_bot] at hσ
    exact AlgEquiv.restrictScalarsHom_injective K (hσ.trans (map_one _).symm)
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
    calc (Module.finrank K L - (lowerRamificationGroup K M i ⊔ embeddingSubgroup K L M).index) *
          Nat.card (lowerRamificationGroup K M i)
        = Module.finrank K L * Nat.card (lowerRamificationGroup K M i) -
            Module.finrank K L * Nat.card (lowerRamificationGroup L M i) := by
          rw [Nat.sub_mul, index_sup_embeddingSubgroup_mul_natCard_lowerRamificationGroup K L M i]
      _ = Module.finrank K L *
            (Nat.card (lowerRamificationGroup K M i) -
              Nat.card (lowerRamificationGroup L M i)) :=
          (Nat.mul_sub _ _ _).symm
      _ = Module.finrank K L *
            ((Nat.card (lowerRamificationGroup K M i) - 1) -
              (Nat.card (lowerRamificationGroup L M i) - 1)) := by
          congr 1
          have : 1 ≤ Nat.card (lowerRamificationGroup K M i) := Nat.card_pos
          have : 1 ≤ Nat.card (lowerRamificationGroup L M i) := Nat.card_pos
          have := hcard_le i
          omega
      _ = Module.finrank K L * (Nat.card (lowerRamificationGroup K M i) - 1) -
            Module.finrank K L * (Nat.card (lowerRamificationGroup L M i) - 1) :=
          Nat.mul_sub _ _ _
  have hle_sum : ∀ i ∈ Finset.range N,
      Module.finrank K L * (Nat.card (lowerRamificationGroup L M i) - 1) ≤
        Module.finrank K L * (Nat.card (lowerRamificationGroup K M i) - 1) :=
    fun i _ ↦ Nat.mul_le_mul_left _ (Nat.sub_le_sub_right (hcard_le i) 1)
  calc Nat.card (lowerRamificationGroup K M 0) * discriminantExponent K L
      = ramificationIndex K M * (inertiaDegree K L * differentExponent K L) := by
        rw [natCard_lowerRamificationGroup_zero K M,
          discriminantExponent_eq_inertiaDegree_mul_differentExponent K L]
    _ = Module.finrank K L * (ramificationIndex L M * differentExponent K L) := by
        rw [ramificationIndex_tower (K := K) (L := L) M,
          ← ramificationIndex_mul_inertiaDegree (K := K) (L := L)]
        ring
    _ = Module.finrank K L * (differentExponent K M - differentExponent L M) := by
        rw [differentExponent_tower K L M, Nat.add_sub_cancel_left]
    _ = Module.finrank K L * differentExponent K M -
          Module.finrank K L * differentExponent L M := Nat.mul_sub _ _ _
    _ = (∑ i ∈ Finset.range N,
          Module.finrank K L * (Nat.card (lowerRamificationGroup K M i) - 1)) -
        ∑ i ∈ Finset.range N,
          Module.finrank K L * (Nat.card (lowerRamificationGroup L M i) - 1) := by
        rw [differentExponent_eq_sum_range_lowerRamificationGroup K M hN,
          differentExponent_eq_sum_range_lowerRamificationGroup L M hNL,
          Finset.mul_sum, Finset.mul_sum]
    _ = ∑ i ∈ Finset.range N,
          (Module.finrank K L * (Nat.card (lowerRamificationGroup K M i) - 1) -
            Module.finrank K L * (Nat.card (lowerRamificationGroup L M i) - 1)) :=
        (Finset.sum_tsub_distrib _ hle_sum).symm
    _ = ∑ i ∈ Finset.range N,
          (Module.finrank K L -
            (lowerRamificationGroup K M i ⊔ embeddingSubgroup K L M).index) *
              Nat.card (lowerRamificationGroup K M i) :=
        Finset.sum_congr rfl fun i _ ↦ (hterm i).symm

/-- Partition points `x_0 = -1` and `x_{i+1} = φ_{M/K}(i)` dividing `(-1, ∞)` into intervals on
which `upperRamificationGroup K M u` is constant. -/
private def herbrandPartition (k : ℕ) : ℝ :=
  match k with
  | 0 => -1
  | i + 1 => (herbrand K M ⟨(i : ℝ), Nat.cast_mem_ramificationIndexDomain i⟩ : ℝ)

private theorem herbrandPartition_one : herbrandPartition K M 1 = 0 := by
  simp only [herbrandPartition]
  rw [herbrand_of_coe_le_zero K M (u := ⟨((0 : ℕ) : ℝ), Nat.cast_mem_ramificationIndexDomain 0⟩)
    (by simp)]
  simp

private theorem herbrandPartition_sub (i : ℕ) :
    herbrandPartition K M (i + 1) - herbrandPartition K M i =
      (Nat.card (lowerRamificationGroup K M i) : ℝ) /
        Nat.card (lowerRamificationGroup K M 0) := by
  cases i with
  | zero =>
    have hcard : (Nat.card (lowerRamificationGroup K M 0) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.card_pos.ne'
    rw [herbrandPartition_one K M]
    simp only [herbrandPartition, zero_sub, neg_neg, Nat.cast_zero, div_self hcard]
  | succ m =>
    simp only [herbrandPartition]
    rw [coe_herbrand_of_mem_Icc K M m (by push_cast; linarith) (by push_cast; linarith),
      coe_herbrand_of_coe_eq_natCast K M m rfl]
    push_cast
    ring

private theorem herbrandPartition_le_succ (i : ℕ) :
    herbrandPartition K M i ≤ herbrandPartition K M (i + 1) := by
  have h := herbrandPartition_sub K M i
  have hnn : (0 : ℝ) ≤ (Nat.card (lowerRamificationGroup K M i) : ℝ) /
      Nat.card (lowerRamificationGroup K M 0) := by positivity
  linarith

private theorem neg_one_le_herbrandPartition (k : ℕ) :
    (-1 : ℝ) ≤ herbrandPartition K M k := by
  cases k with
  | zero => exact le_rfl
  | succ m => exact (herbrand K M _).2

omit [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L] in
private theorem embeddingOrbitCount_eq_on_herbrandPartition (i : ℕ) {u : ℝ}
    (hu : u ∈ Set.Ioc (herbrandPartition K M i) (herbrandPartition K M (i + 1))) :
    embeddingOrbitCount K L M ⟨max u (-1), le_max_right u (-1)⟩ =
      (lowerRamificationGroup K M i ⊔ embeddingSubgroup K L M).index := by
  have hu_ge : -1 ≤ u := (neg_one_le_herbrandPartition K M i).trans hu.1.le
  have hmax : (⟨max u (-1), le_max_right u (-1)⟩ : RamificationIndexDomain) = ⟨u, hu_ge⟩ :=
    Subtype.ext (max_eq_left hu_ge)
  rw [hmax, embeddingOrbitCount_def, upperRamificationGroup_def]
  congr 2
  cases i with
  | zero =>
    have hu_le : u ≤ 0 := herbrandPartition_one K M ▸ hu.2
    have hψ : (inverseHerbrand K M ⟨u, hu_ge⟩ : ℝ) = u :=
      congrArg Subtype.val (inverseHerbrand_of_coe_le_zero K M hu_le)
    rw [hψ]
    exact lowerRamificationGroupReal_eq_of_sub_one_lt_of_le K M (i := 0)
      (by simpa [herbrandPartition] using hu.1) (by simpa using hu_le)
  | succ m =>
    apply lowerRamificationGroupReal_eq_of_sub_one_lt_of_le K M (i := ((m + 1 : ℕ) : ℤ))
    · have hlt : herbrand K M ⟨(m : ℝ), Nat.cast_mem_ramificationIndexDomain m⟩ < ⟨u, hu_ge⟩ :=
        Subtype.mk_lt_mk.2 hu.1
      have hψ := inverseHerbrand_strictMono K M hlt
      rw [inverseHerbrand_herbrand] at hψ
      have hψ' : (m : ℝ) < (inverseHerbrand K M ⟨u, hu_ge⟩ : ℝ) := Subtype.mk_lt_mk.1 hψ
      push_cast
      linarith
    · have hle : (⟨u, hu_ge⟩ : RamificationIndexDomain) ≤
          herbrand K M ⟨((m + 1 : ℕ) : ℝ), Nat.cast_mem_ramificationIndexDomain (m + 1)⟩ :=
        Subtype.mk_le_mk.2 hu.2
      have hψ := (inverseHerbrand_strictMono K M).monotone hle
      rw [inverseHerbrand_herbrand] at hψ
      exact_mod_cast Subtype.mk_le_mk.1 hψ

omit [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L] in
private theorem finrank_sub_embeddingOrbitCount_eq_zero_on_Ioi {N : ℕ}
    (hN : lowerRamificationGroup K M N = ⊥) :
    Set.EqOn
      (fun u : ℝ ↦ (Module.finrank K L : ℝ) -
        embeddingOrbitCount K L M ⟨max u (-1), le_max_right u (-1)⟩)
      0 (Set.Ioi (herbrandPartition K M N)) := by
  intro u hu
  have hu_ge : -1 ≤ u := (neg_one_le_herbrandPartition K M N).trans (Set.mem_Ioi.1 hu).le
  have hmax : (⟨max u (-1), le_max_right u (-1)⟩ : RamificationIndexDomain) = ⟨u, hu_ge⟩ :=
    Subtype.ext (max_eq_left hu_ge)
  have hocc : embeddingOrbitCount K L M ⟨u, hu_ge⟩ = Module.finrank K L := by
    cases N with
    | zero =>
      exact embeddingOrbitCount_eq_finrank_of_lowerRamificationGroup_eq_bot K L M hN
        (Set.mem_Ioi.1 hu)
    | succ m =>
      exact embeddingOrbitCount_eq_finrank_of_lowerRamificationGroup_eq_bot K L M hN
        (Set.mem_Ioi.1 hu)
  simp [hmax, hocc]

omit [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L] in
private theorem intervalIntegrable_herbrandPartition_step (k : ℕ) :
    IntervalIntegrable
      (fun u : ℝ ↦ (Module.finrank K L : ℝ) -
        embeddingOrbitCount K L M ⟨max u (-1), le_max_right u (-1)⟩)
      volume (herbrandPartition K M k) (herbrandPartition K M (k + 1)) := by
  have hle := herbrandPartition_le_succ K M k
  refine (intervalIntegrable_congr (g := fun _ ↦ (Module.finrank K L : ℝ) -
    (lowerRamificationGroup K M k ⊔ embeddingSubgroup K L M).index) ?_).2
    intervalIntegrable_const
  intro u hu
  rw [Set.uIoc_of_le hle] at hu
  simp only [embeddingOrbitCount_eq_on_herbrandPartition K L M k hu]

omit [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L] in
private theorem intervalIntegrable_herbrandPartition_zero (N : ℕ) :
    IntervalIntegrable
      (fun u : ℝ ↦ (Module.finrank K L : ℝ) -
        embeddingOrbitCount K L M ⟨max u (-1), le_max_right u (-1)⟩)
      volume (herbrandPartition K M 0) (herbrandPartition K M N) := by
  induction N with
  | zero => exact IntervalIntegrable.refl
  | succ m ih => exact ih.trans (intervalIntegrable_herbrandPartition_step K L M m)

omit [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L] in
/-- The function `u ↦ [L : K] - [G : G^{max u (-1)} H]` is integrable on `(-1, ∞)`. -/
theorem integrableOn_finrank_sub_embeddingOrbitCount_Ioi :
    IntegrableOn
      (fun u : ℝ ↦ (Module.finrank K L : ℝ) -
        embeddingOrbitCount K L M ⟨max u (-1), le_max_right u (-1)⟩)
      (Set.Ioi (-1 : ℝ)) := by
  set N := (largestLowerJump K M).toNat + 1
  have hbot : lowerRamificationGroup K M N = ⊥ :=
    lowerRamificationGroup_toNat_largestLowerJump_add_one K M
  have hle : (-1 : ℝ) ≤ herbrandPartition K M N := neg_one_le_herbrandPartition K M N
  have hIoc : IntegrableOn
      (fun u : ℝ ↦ (Module.finrank K L : ℝ) -
        embeddingOrbitCount K L M ⟨max u (-1), le_max_right u (-1)⟩)
      (Set.Ioc (-1 : ℝ) (herbrandPartition K M N)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).1
      (intervalIntegrable_herbrandPartition_zero K L M N)
  have hIoi : IntegrableOn
      (fun u : ℝ ↦ (Module.finrank K L : ℝ) -
        embeddingOrbitCount K L M ⟨max u (-1), le_max_right u (-1)⟩)
      (Set.Ioi (herbrandPartition K M N)) :=
    (integrableOn_congr_fun (finrank_sub_embeddingOrbitCount_eq_zero_on_Ioi K L M hbot)
      measurableSet_Ioi).2 integrableOn_zero
  rw [← Set.Ioc_union_Ioi_eq_Ioi hle]
  exact hIoc.union hIoi

omit [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L] in
/-- On any compact interval inside `[-1, ∞)`, the integrand
`u ↦ [L : K] - [G : G^{max u (-1)} H]` is interval-integrable. -/
theorem intervalIntegrable_finrank_sub_embeddingOrbitCount {a b : ℝ}
    (ha : -1 ≤ a) (hb : -1 ≤ b) :
    IntervalIntegrable
      (fun u : ℝ ↦ (Module.finrank K L : ℝ) -
        embeddingOrbitCount K L M ⟨max u (-1), le_max_right u (-1)⟩)
      volume a b := by
  rw [intervalIntegrable_iff]
  refine (integrableOn_finrank_sub_embeddingOrbitCount_Ioi K L M).mono_set fun u hu ↦ ?_
  rw [Set.uIoc, Set.mem_Ioc] at hu
  exact Set.mem_Ioi.2 ((le_min ha hb).trans_lt hu.1)

/-- **The discriminant exponent as an upper-numbering integral.**
`δ(L/K) = ∫_{u > -1} ([L : K] - [G : G^u H]) du`, obtained from Hilbert's formula and
transitivity of the different through Herbrand's change of variables. -/
theorem discriminantExponent_eq_integral [Algebra.IsSeparable K L] :
    (discriminantExponent K L : ℝ) =
      ∫ u in Set.Ioi (-1 : ℝ),
        ((Module.finrank K L : ℝ) -
          embeddingOrbitCount K L M ⟨max u (-1), le_max_right u (-1)⟩) := by
  set f : ℝ → ℝ := fun u ↦ (Module.finrank K L : ℝ) -
    embeddingOrbitCount K L M ⟨max u (-1), le_max_right u (-1)⟩
  set N := (largestLowerJump K M).toNat + 1
  have hbot : lowerRamificationGroup K M N = ⊥ :=
    lowerRamificationGroup_toNat_largestLowerJump_add_one K M
  have hIoi_int : IntegrableOn f (Set.Ioi (-1 : ℝ)) :=
    integrableOn_finrank_sub_embeddingOrbitCount_Ioi K L M
  have htail_int : IntegrableOn f (Set.Ioi (herbrandPartition K M N)) :=
    hIoi_int.mono_set (Set.Ioi_subset_Ioi (neg_one_le_herbrandPartition K M N))
  have htail_zero : ∫ u in Set.Ioi (herbrandPartition K M N), f u = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun u hu ↦
      finrank_sub_embeddingOrbitCount_eq_zero_on_Ioi K L M hbot hu
  have hsplit := intervalIntegral.integral_interval_add_Ioi hIoi_int htail_int
  rw [← hsplit, htail_zero, add_zero]
  change (discriminantExponent K L : ℝ) =
    ∫ u in herbrandPartition K M 0..herbrandPartition K M N, f u
  rw [← intervalIntegral.sum_integral_adjacent_intervals
    (fun k _ ↦ intervalIntegrable_herbrandPartition_step K L M k)]
  have hstep_val (k : ℕ) :
      ∫ u in herbrandPartition K M k..herbrandPartition K M (k + 1), f u =
        ((Module.finrank K L : ℝ) -
          (lowerRamificationGroup K M k ⊔ embeddingSubgroup K L M).index) *
            ((Nat.card (lowerRamificationGroup K M k) : ℝ) /
              Nat.card (lowerRamificationGroup K M 0)) := by
    have hle := herbrandPartition_le_succ K M k
    have hcongr : ∫ u in herbrandPartition K M k..herbrandPartition K M (k + 1), f u =
        ∫ _ in herbrandPartition K M k..herbrandPartition K M (k + 1),
          ((Module.finrank K L : ℝ) -
            (lowerRamificationGroup K M k ⊔ embeddingSubgroup K L M).index) := by
      refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun u hu ↦ ?_)
      rw [Set.uIoc_of_le hle] at hu
      simp only [f, embeddingOrbitCount_eq_on_herbrandPartition K L M k hu]
    rw [hcongr, intervalIntegral.integral_const, smul_eq_mul, herbrandPartition_sub K M k,
      mul_comm]
  rw [Finset.sum_congr rfl fun k _ ↦ hstep_val k]
  have hG0_ne : (Nat.card (lowerRamificationGroup K M 0) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have hdisc : (Nat.card (lowerRamificationGroup K M 0) : ℝ) * discriminantExponent K L =
      ∑ k ∈ Finset.range N,
        ((Module.finrank K L : ℝ) -
          (lowerRamificationGroup K M k ⊔ embeddingSubgroup K L M).index) *
            Nat.card (lowerRamificationGroup K M k) := by
    have hnat := congrArg (Nat.cast (R := ℝ))
      (natCard_lowerRamificationGroup_zero_mul_discriminantExponent K L M hbot)
    push_cast at hnat
    refine hnat.trans (Finset.sum_congr rfl fun k _ ↦ ?_)
    rw [Nat.cast_sub (index_lowerRamificationGroup_sup_embeddingSubgroup_le_finrank K L M k)]
  apply mul_left_cancel₀ hG0_ne
  rw [hdisc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  field_simp [hG0_ne]

/-- If `upperRamificationGroup K M v ≤ embeddingSubgroup K L M`, the upper-numbering discriminant
integral truncates to the finite interval `(-1)..v`. -/
theorem discriminantExponent_eq_intervalIntegral_of_upperRamificationGroup_le
    [Algebra.IsSeparable K L] {v : RamificationIndexDomain}
    (hv : upperRamificationGroup K M v ≤ embeddingSubgroup K L M) :
    (discriminantExponent K L : ℝ) =
      ∫ u in (-1 : ℝ)..v,
        ((Module.finrank K L : ℝ) -
          embeddingOrbitCount K L M ⟨max u (-1), le_max_right u (-1)⟩) := by
  set f : ℝ → ℝ := fun u ↦ (Module.finrank K L : ℝ) -
    embeddingOrbitCount K L M ⟨max u (-1), le_max_right u (-1)⟩
  have hIoi : IntegrableOn f (Set.Ioi (-1 : ℝ)) :=
    integrableOn_finrank_sub_embeddingOrbitCount_Ioi K L M
  have hv_int : IntegrableOn f (Set.Ioi (v : ℝ)) :=
    hIoi.mono_set (Set.Ioi_subset_Ioi v.2)
  have hv_zero : ∫ u in Set.Ioi (v : ℝ), f u = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun u hu ↦ ?_
    have hvu : (v : ℝ) < u := Set.mem_Ioi.1 hu
    have hle : v ≤ ⟨max u (-1), le_max_right u (-1)⟩ :=
      Subtype.mk_le_mk.2 (hvu.le.trans (le_max_left _ _))
    have hsub : upperRamificationGroup K M ⟨max u (-1), le_max_right u (-1)⟩ ≤
        embeddingSubgroup K L M :=
      (upperRamificationGroup_antitone K M hle).trans hv
    dsimp only [f]
    rw [embeddingOrbitCount_def, sup_eq_right.2 hsub, index_embeddingSubgroup K L M, sub_self]
  rw [discriminantExponent_eq_integral K L M,
    ← intervalIntegral.integral_interval_add_Ioi hIoi hv_int, hv_zero, add_zero]

/-! ### The height identity and Galois mean slope -/

/-- **The height identity.** For a finite separable extension `L/K` read inside a finite Galois
extension `M/K`, the discriminant exponent `δ(L/K)` is expressed in terms of `inertiaDegree K L`,
`ramificationIndex K L`, and the sorted list `artinSlopeList K L M` of Artin slopes by
`δ(L/K) = f (e - 1) + f e ∑_{i < w} (p - 1) (a_i - 1) / p^{w - i}`. -/
theorem discriminantExponent_eq_sum_artinSlopeList [Algebra.IsSeparable K L] :
    (discriminantExponent K L : ℝ) =
      (inertiaDegree K L : ℝ) * ((ramificationIndex K L : ℝ) - 1) +
        (inertiaDegree K L : ℝ) * (ramificationIndex K L : ℝ) *
          ∑ i : Fin (artinSlopeList K L M).length,
            ((ringChar 𝓀[K] : ℝ) - 1) * ((artinSlopeList K L M).get i - 1) /
              (ringChar 𝓀[K] : ℝ) ^ ((artinSlopeList K L M).length - i.1) := by
  let p := ringChar 𝓀[K]
  have hp : p.Prime := CharP.prime_ringChar 𝓀[K]
  have hp_ne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  let J := (largestLowerJump K M).toNat
  let H := embeddingSubgroup K L M
  let w := wildRamificationExponent K L
  have hpw_ne : (p : ℝ) ^ w ≠ 0 := pow_ne_zero w hp_ne
  let d : ℕ → ℕ := fun j ↦
    Nat.log p
      ((lowerRamificationGroup K M ((j + 2 : ℕ) : ℤ) ⊔ H).relIndex
        (lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ) ⊔ H))
  let S : ℕ → ℕ := fun k ↦ ∑ r ∈ Finset.range k, d r
  -- Step 1: `[G : G_{k+1} H] = f · ε · p ^ S(k)` for every `k : ℕ`.
  have h_idx (k : ℕ) :
      (lowerRamificationGroup K M ((k + 1 : ℕ) : ℤ) ⊔ H).index =
        inertiaDegree K L * tameRamificationIndex K L * p ^ S k := by
    induction k with
    | zero =>
      simp only [S, Finset.range_zero, Finset.sum_empty, pow_zero, mul_one, zero_add, Nat.cast_one]
      exact index_lowerRamificationGroup_one_sup_embeddingSubgroup K L M
    | succ m ih =>
      have hmul := Subgroup.relIndex_mul_index
        (sup_le_sup_right (lowerRamificationGroup_antitone K M (by omega)) H :
          lowerRamificationGroup K M ((m + 2 : ℕ) : ℤ) ⊔ H ≤
            lowerRamificationGroup K M ((m + 1 : ℕ) : ℤ) ⊔ H)
      have hpow_m : (lowerRamificationGroup K M ((m + 2 : ℕ) : ℤ) ⊔ H).relIndex
          (lowerRamificationGroup K M ((m + 1 : ℕ) : ℤ) ⊔ H) = p ^ d m :=
        (pow_natLog_relIndex_lowerRamificationGroup_sup_embeddingSubgroup K L M m).symm
      rw [← hmul, hpow_m, ih]
      simp only [S, Finset.sum_range_succ, pow_add]
      ring
  have hbot : lowerRamificationGroup K M ((J + 1 : ℕ) : ℤ) = ⊥ :=
    lowerRamificationGroup_toNat_largestLowerJump_add_one K M
  have hSJ : S J = w := by
    have h1 := h_idx J
    rw [hbot, bot_sup_eq, index_embeddingSubgroup K L M,
      ← ramificationIndex_mul_inertiaDegree (K := K) (L := L),
      ← tameRamificationIndex_mul_pow_wildRamificationExponent K L] at h1
    have hpos : 0 < inertiaDegree K L * tameRamificationIndex K L :=
      Nat.mul_pos inertiaDegree_pos (tameRamificationIndex_pos K L)
    apply Nat.pow_right_injective hp.two_le
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    dsimp only [p, w] at h1 ⊢
    linarith
  -- Step 2: discrete lower-index formula at `N = J + 1`, split at `i = 0` and `1 ≤ i ≤ J`.
  let φn : ℕ → ℝ := fun k ↦ herbrandPartition K M (k + 1)
  let q : ℕ → ℝ := fun k ↦ (p : ℝ) ^ S k / (p : ℝ) ^ w
  have hφ0 : φn 0 = 0 := herbrandPartition_one K M
  have hqJ : q J = 1 := by
    simp only [q, hSJ, div_self hpw_ne]
  have hG0_ne : (Nat.card (lowerRamificationGroup K M 0) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have hdisc : (discriminantExponent K L : ℝ) =
      (inertiaDegree K L : ℝ) * ((ramificationIndex K L : ℝ) - 1) +
        (inertiaDegree K L : ℝ) * (ramificationIndex K L : ℝ) *
          ∑ j ∈ Finset.range J, (1 - q j) * (φn (j + 1) - φn j) := by
    have hnat := congrArg (Nat.cast (R := ℝ))
      (natCard_lowerRamificationGroup_zero_mul_discriminantExponent K L M (N := J + 1) hbot)
    push_cast at hnat
    rw [Finset.sum_range_succ'] at hnat
    have h0_term :
        (((Module.finrank K L -
          (lowerRamificationGroup K M (0 : ℕ) ⊔ H).index : ℕ) : ℝ) *
            Nat.card (lowerRamificationGroup K M (0 : ℕ))) =
          (inertiaDegree K L : ℝ) * ((ramificationIndex K L : ℝ) - 1) *
            Nat.card (lowerRamificationGroup K M 0) := by
      have he1 : 1 ≤ ramificationIndex K L := ramificationIndex_pos
      rw [Nat.cast_zero, index_lowerRamificationGroup_zero_sup_embeddingSubgroup K L M,
        Nat.cast_sub (by
          rw [← ramificationIndex_mul_inertiaDegree (K := K) (L := L)]
          exact Nat.le_mul_of_pos_left _ he1),
        ← ramificationIndex_mul_inertiaDegree (K := K) (L := L)]
      push_cast
      ring
    have hj_term (j : ℕ) :
        (((Module.finrank K L -
          (lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ) ⊔ H).index : ℕ) : ℝ) *
            Nat.card (lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ))) =
          (inertiaDegree K L : ℝ) * (ramificationIndex K L : ℝ) *
            ((1 - q j) * (φn (j + 1) - φn j)) *
              Nat.card (lowerRamificationGroup K M 0) := by
      have hsub_φ : φn (j + 1) - φn j =
          (Nat.card (lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ)) : ℝ) /
            Nat.card (lowerRamificationGroup K M 0) :=
        herbrandPartition_sub K M (j + 1)
      have hidx_real : ((lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ) ⊔ H).index : ℝ) =
          (inertiaDegree K L : ℝ) * (ramificationIndex K L : ℝ) * q j := by
        rw [h_idx j, ← tameRamificationIndex_mul_pow_wildRamificationExponent K L]
        push_cast
        change (inertiaDegree K L : ℝ) * tameRamificationIndex K L * (p : ℝ) ^ S j =
          (inertiaDegree K L : ℝ) * (tameRamificationIndex K L * (p : ℝ) ^ w) *
            ((p : ℝ) ^ S j / (p : ℝ) ^ w)
        field_simp [hpw_ne]
      rw [Nat.cast_sub (index_lowerRamificationGroup_sup_embeddingSubgroup_le_finrank K L M _),
        hidx_real, ← ramificationIndex_mul_inertiaDegree (K := K) (L := L), hsub_φ]
      push_cast
      field_simp [hG0_ne]
    apply mul_right_cancel₀ hG0_ne
    have hnat' : (discriminantExponent K L : ℝ) * Nat.card (lowerRamificationGroup K M 0) =
        (∑ k ∈ Finset.range J,
          ((Module.finrank K L -
            (lowerRamificationGroup K M ((k + 1 : ℕ) : ℤ) ⊔ H).index : ℕ) : ℝ) *
              Nat.card (lowerRamificationGroup K M ((k + 1 : ℕ) : ℤ))) +
          ((Module.finrank K L -
            (lowerRamificationGroup K M (0 : ℕ) ⊔ H).index : ℕ) : ℝ) *
              Nat.card (lowerRamificationGroup K M (0 : ℕ)) := by
      linarith
    rw [hnat', h0_term, Finset.sum_congr rfl fun j _ ↦ hj_term j, add_mul, mul_assoc,
      Finset.mul_sum, Finset.sum_mul]
    ring
  -- Step 3: summation by parts + block geometric sums match `artinSlopeList`.
  have habp : ∑ j ∈ Finset.range J, (1 - q j) * (φn (j + 1) - φn j) =
      ∑ j ∈ Finset.range J, (q (j + 1) - q j) * φn (j + 1) := by
    have hid : ∀ j ∈ Finset.range J,
        (1 - q j) * (φn (j + 1) - φn j) =
          ((1 - q (j + 1)) * φn (j + 1) - (1 - q j) * φn j) +
            (q (j + 1) - q j) * φn (j + 1) := fun _ _ ↦ by ring
    rw [Finset.sum_congr rfl hid, Finset.sum_add_distrib,
      Finset.sum_range_sub fun k ↦ (1 - q k) * φn k, hqJ, hφ0]
    ring
  have hlen : (artinSlopeList K L M).length = w := length_artinSlopeList K L M
  have hlist_sum :
      (∑ i : Fin (artinSlopeList K L M).length,
        ((p : ℝ) - 1) * ((artinSlopeList K L M).get i - 1) /
          (p : ℝ) ^ ((artinSlopeList K L M).length - i.1)) =
        ∑ j ∈ Finset.range J, (q (j + 1) - q j) * φn (j + 1) := by
    rw [sum_fin_get_eq_sum_range_getD (artinSlopeList K L M)
        (fun a idx ↦ ((p : ℝ) - 1) * (a - 1) / (p : ℝ) ^ ((artinSlopeList K L M).length - idx))]
    have hcongr_len :
        (∑ k ∈ Finset.range (artinSlopeList K L M).length,
          ((p : ℝ) - 1) * ((artinSlopeList K L M).getD k 0 - 1) /
            (p : ℝ) ^ ((artinSlopeList K L M).length - k)) =
        ∑ k ∈ Finset.range (artinSlopeList K L M).length,
          ((p : ℝ) - 1) * ((artinSlopeList K L M).getD k 0 - 1) / (p : ℝ) ^ (w - k) :=
      Finset.sum_congr rfl fun _ _ ↦ by rw [hlen]
    rw [hcongr_len, artinSlopeList_def K L M]
    change (∑ k ∈ Finset.range ((List.range J).flatMap
        fun j ↦ List.replicate (d j) (φn (j + 1) + 1)).length,
      ((p : ℝ) - 1) * (((List.range J).flatMap
        fun j ↦ List.replicate (d j) (φn (j + 1) + 1)).getD k 0 - 1) /
        (p : ℝ) ^ (w - k)) = _
    rw [sum_range_getD_flatMap_replicate J d (fun j ↦ φn (j + 1) + 1)
      (fun a idx ↦ ((p : ℝ) - 1) * (a - 1) / (p : ℝ) ^ (w - idx))]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hjJ : j < J := Finset.mem_range.1 hj
    have hSj1_le : S (j + 1) ≤ w := by
      rw [← hSJ]
      exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (Nat.succ_le_of_lt hjJ))
    have hinner (r : ℕ) (hr : r ∈ Finset.range (d j)) :
        ((p : ℝ) - 1) * ((φn (j + 1) + 1) - 1) / (p : ℝ) ^ (w - (S j + r)) =
          (((p : ℝ) ^ (S j + (r + 1)) - (p : ℝ) ^ (S j + r)) / (p : ℝ) ^ w) * φn (j + 1) := by
      have hr_lt : r < d j := Finset.mem_range.1 hr
      have hle_w : S j + r ≤ w := by
        have hSsucc : S (j + 1) = S j + d j := Finset.sum_range_succ d j
        omega
      have hpow_split : (p : ℝ) ^ (S j + r) * (p : ℝ) ^ (w - (S j + r)) = (p : ℝ) ^ w := by
        rw [← pow_add, Nat.add_sub_of_le hle_w]
      have hpow_ne' : (p : ℝ) ^ (w - (S j + r)) ≠ 0 := pow_ne_zero _ hp_ne
      field_simp [hpw_ne, hpow_ne']
      rw [← hpow_split, ← add_assoc, pow_succ]
      ring
    rw [Finset.sum_congr rfl hinner, ← Finset.sum_mul, ← Finset.sum_div,
      Finset.sum_range_sub (fun r ↦ (p : ℝ) ^ (S j + r)) (d j)]
    have hSsucc : S (j + 1) = S j + d j := Finset.sum_range_succ d j
    simp only [q, add_zero, hSsucc, sub_div]
  rw [hdisc, habp]
  dsimp only [p] at hlist_sum
  rw [hlist_sum]

end Integral

/-- **The weighted formula for the Galois mean slope.** For a finite Galois extension `M/K` of
nonarchimedean local fields, dividing the height identity by `[M : K] = e(M/K) · f(M/K)` cancels
the unramified degree `f(M/K)` and expresses `δ(M/K) / [M : K]` in terms of the tame degree
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
              (ringChar 𝓀[K] : ℝ) ^ ((artinSlopeList K M M).length - i.1) := by
  have he_eq : ((lowerRamificationGroup K M 1).relIndex (lowerRamificationGroup K M 0) : ℝ) *
      (ringChar 𝓀[K] : ℝ) ^ (artinSlopeList K M M).length = ramificationIndex K M := by
    rw [relIndex_lowerRamificationGroup_one_zero K M, length_artinSlopeList K M M]
    exact_mod_cast tameRamificationIndex_mul_pow_wildRamificationExponent K M
  have hfin : (Module.finrank K M : ℝ) =
      (ramificationIndex K M : ℝ) * inertiaDegree K M := by
    exact_mod_cast (ramificationIndex_mul_inertiaDegree (K := K) (L := M)).symm
  have he_ne : (ramificationIndex K M : ℝ) ≠ 0 := by exact_mod_cast ramificationIndex_pos.ne'
  have hf_ne : (inertiaDegree K M : ℝ) ≠ 0 := by exact_mod_cast inertiaDegree_pos.ne'
  have hpull :
      (∑ i : Fin (artinSlopeList K M M).length,
        ((ringChar 𝓀[K] : ℝ) - 1) * ((artinSlopeList K M M).get i - 1) /
          (ringChar 𝓀[K] : ℝ) ^ ((artinSlopeList K M M).length - i.1)) =
        ((ringChar 𝓀[K] : ℝ) - 1) *
          ∑ i : Fin (artinSlopeList K M M).length,
            ((artinSlopeList K M M).get i - 1) /
              (ringChar 𝓀[K] : ℝ) ^ ((artinSlopeList K M M).length - i.1) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ mul_div_assoc _ _ _
  rw [discriminantExponent_eq_sum_artinSlopeList K M M, hpull, he_eq, hfin]
  field_simp [he_ne, hf_ne]

end TauCeti
