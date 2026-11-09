/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Colored.EditDiscrepancy
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr

/-!
# Padding and restricting colored triple graphs

A coloring extends to a larger vertex set by giving all new triples one default color.
Extending two colorings with the same default creates no new edits. Restriction, however,
can increase the normalized edit discrepancy: its denominator is the cube of the smaller
host size. We prove the exact conservation law for extension and the corresponding upper
bound for arbitrary restriction, including empty hosts.

In particular, an approximation on a padded host of size at most `(1 + ρ) * |V|` restricts
to an approximation on `V` with error multiplied by at most `(1 + ρ)^3`. This accounts for
the normalization loss when auxiliary vertices used to achieve divisibility are removed.

The padding-and-restriction setting is used in Rödl–Schacht, *Regular partitions of
hypergraphs: regularity lemmas* (2007). The constructions here use Mathlib's
`Function.extend` and `Set.powersetCard.map`; no regularity hypothesis is needed.
-/

public section

namespace TauCeti.Colored3Graph

variable {κ V W : Type*}

/-- The edited triples of a restriction inject into the edited triples of the host. -/
theorem ncard_color_ne_comap_le [Finite W]
    (H H' : Colored3Graph κ W) (f : V ↪ W) :
    {s | (H.comap f).color s ≠ (H'.comap f).color s}.ncard ≤
      {s | H.color s ≠ H'.color s}.ncard := by
  apply Set.ncard_le_ncard_of_injOn (Set.powersetCard.map 3 f)
  · intro s hs
    simpa only [Set.mem_ofPred, color_comap] using hs
  · exact (Set.powersetCard.map_injective 3 f).injOn

/-- Extending with a common default color creates exactly the images of the original edits. -/
theorem color_ne_extend_eq_image (H H' : Colored3Graph κ V) (f : V ↪ W) (c : κ) :
    {s | (H.extend f c).color s ≠ (H'.extend f c).color s} =
      Set.powersetCard.map 3 f '' {s | H.color s ≠ H'.color s} := by
  ext s
  by_cases hs : s ∈ Set.range (Set.powersetCard.map 3 f)
  · obtain ⟨t, rfl⟩ := hs
    constructor
    · intro ht
      exact ⟨t, by simpa using ht, rfl⟩
    · rintro ⟨u, hu, h⟩
      rw [← h]
      simpa using hu
  · simp only [Set.mem_ofPred, color_extend_of_notMem_range H f c s hs,
      color_extend_of_notMem_range H' f c s hs, ne_self_iff_false, false_iff]
    rintro ⟨t, _, ht⟩
    exact hs ⟨t, ht⟩

/-- Padding two colorings by the same default preserves the unnormalized number of edits. -/
theorem ncard_color_ne_extend (H H' : Colored3Graph κ V) (f : V ↪ W) (c : κ) :
    {s | (H.extend f c).color s ≠ (H'.extend f c).color s}.ncard =
      {s | H.color s ≠ H'.color s}.ncard := by
  rw [color_ne_extend_eq_image]
  exact Set.ncard_image_of_injective _ (Set.powersetCard.map_injective 3 f)

/-- Restricting a coloring cannot increase its unnormalized edit count. -/
theorem editDiscrepancy3_comap_mul_card_pow_le [Finite W]
    (H H' : Colored3Graph κ W) (f : V ↪ W) :
    (H.comap f).editDiscrepancy3 (H'.comap f) * (Nat.card V : ℚ) ^ 3 ≤
      H.editDiscrepancy3 H' * (Nat.card W : ℚ) ^ 3 := by
  have := Finite.of_injective f f.injective
  rw [editDiscrepancy3_mul_card_pow, editDiscrepancy3_mul_card_pow]
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast H.ncard_color_ne_comap_le H' f)
    (by norm_num)

/-- The normalization loss on restriction is at most the cube of the ratio of host sizes.
On an empty source both sides vanish. -/
theorem editDiscrepancy3_comap_le [Finite W]
    (H H' : Colored3Graph κ W) (f : V ↪ W) :
    (H.comap f).editDiscrepancy3 (H'.comap f) ≤
      H.editDiscrepancy3 H' * ((Nat.card W : ℚ) / Nat.card V) ^ 3 := by
  by_cases hn : Nat.card V = 0
  · simp [editDiscrepancy3_def, hn]
  have hn' : (0 : ℚ) < (Nat.card V : ℚ) ^ 3 := by
    exact_mod_cast pow_pos (Nat.pos_of_ne_zero hn) 3
  have hnq : (Nat.card V : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  apply (mul_le_mul_iff_left₀ hn').mp
  convert H.editDiscrepancy3_comap_mul_card_pow_le H' f using 1
  field_simp [hnq]

/-- Extension with a common default preserves the edit count, with the host-size cubes
accounting exactly for the change of normalization. -/
theorem editDiscrepancy3_extend_mul_card_pow [Finite W]
    (H H' : Colored3Graph κ V) (f : V ↪ W) (c : κ) :
    (H.extend f c).editDiscrepancy3 (H'.extend f c) * (Nat.card W : ℚ) ^ 3 =
      H.editDiscrepancy3 H' * (Nat.card V : ℚ) ^ 3 := by
  have := Finite.of_injective f f.injective
  simp only [editDiscrepancy3_mul_card_pow, ncard_color_ne_extend]

/-- An approximation restricts with the cube of the host-size ratio as error multiplier. -/
theorem Approximates3.comap [Finite W] {H H' : Colored3Graph κ W} {ε : ℝ}
    (h : H.Approximates3 H' ε) (f : V ↪ W) :
    (H.comap f).Approximates3 (H'.comap f)
      (ε * ((Nat.card W : ℝ) / Nat.card V) ^ 3) := by
  rw [approximates3_iff] at *
  calc
    _ ≤ (H.editDiscrepancy3 H' : ℝ) * ((Nat.card W : ℝ) / Nat.card V) ^ 3 := by
      have hb := Rat.cast_le (K := ℝ) |>.mpr (H.editDiscrepancy3_comap_le H' f)
      simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_natCast] using hb
    _ ≤ _ := mul_le_mul_of_nonneg_right h (by positivity)

/-- Removing at most a `ρ`-fraction of auxiliary vertices, measured relative to the original
host, multiplies the approximation error by at most `(1 + ρ)^3`. -/
theorem Approximates3.comap_of_card_le [Finite W]
    {H H' : Colored3Graph κ W} {ε ρ : ℝ} (h : H.Approximates3 H' ε) (f : V ↪ W)
    (hρ : 0 ≤ ρ) (hcard : (Nat.card W : ℝ) ≤ (1 + ρ) * Nat.card V) :
    (H.comap f).Approximates3 (H'.comap f) (ε * (1 + ρ) ^ 3) := by
  have hnonneg : (0 : ℝ) ≤ H.editDiscrepancy3 H' :=
    Rat.cast_nonneg.mpr (H.editDiscrepancy3_nonneg H')
  have hε : 0 ≤ ε := hnonneg.trans ((approximates3_iff _ _ _).mp h)
  apply (h.comap f).mono
  apply mul_le_mul_of_nonneg_left _ hε
  have hratio : (Nat.card W : ℝ) / Nat.card V ≤ 1 + ρ := by
    by_cases hn : Nat.card V = 0
    · simp only [hn, Nat.cast_zero, div_zero]
      exact add_nonneg zero_le_one hρ
    · exact (div_le_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hn)).mpr hcard
  gcongr

end TauCeti.Colored3Graph
