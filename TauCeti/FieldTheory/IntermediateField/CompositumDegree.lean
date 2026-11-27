/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Relrank
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Compositum degrees in a tower

Adjoining a fixed finite extension to a growing finite base gives a relative degree that
can only decrease. It therefore stabilizes: the absolute degrees of the composita are
ultimately a fixed positive multiple of the absolute degrees of the layers. No normality
assumption is needed.
-/

public section

namespace IntermediateField

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- A finite enlargement of the base cannot increase the relative degree of a compositum. -/
theorem relfinrank_sup_le_of_le {A B M : IntermediateField K L} (hAB : A ≤ B)
    (hpos : 0 < A.relfinrank B) : B.relfinrank (B ⊔ M) ≤ A.relfinrank (A ⊔ M) := by
  have hsup : B ⊔ (A ⊔ M) = B ⊔ M := by
    rw [← sup_assoc, sup_eq_left.mpr hAB]
  have hdeg := finrank_sup_le (extendScalars hAB) (extendScalars (le_sup_left : A ≤ A ⊔ M))
  rw [extendScalars_sup] at hdeg
  simp only [← relfinrank_eq_finrank_of_le, hsup] at hdeg
  rw [← relfinrank_mul_relfinrank hAB (le_sup_left : B ≤ B ⊔ M)] at hdeg
  exact Nat.le_of_mul_le_mul_left hdeg hpos

/-- Over a nested sequence of extensions, the degree of the compositum with a fixed finite
extension `M` is ultimately a fixed positive multiple of the degree of the base layer.
If a layer has infinite degree, both finranks are zero from that layer onward. -/
theorem exists_finrank_sup_eq_mul_finrank (M : IntermediateField K L) [FiniteDimensional K M]
    (E : ℕ → IntermediateField K L) (hE : Monotone E) :
    ∃ c : ℕ, 1 ≤ c ∧ c ≤ Module.finrank K M ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      Module.finrank K ↥(E n ⊔ M) = c * Module.finrank K (E n) := by
  classical
  by_cases hInf : ∃ n, ¬ FiniteDimensional K (E n)
  · obtain ⟨n₀, hn₀⟩ := hInf
    refine ⟨1, le_rfl, Module.finrank_pos, n₀, fun n hn ↦ ?_⟩
    have finrank_eq_zero (F : IntermediateField K L) (hF : E n₀ ≤ F) :
        Module.finrank K F = 0 := by
      apply Module.finrank_of_infinite_dimensional
      intro h
      exact hn₀ (FiniteDimensional.of_injective (inclusion hF).toLinearMap (inclusion hF).injective)
    rw [finrank_eq_zero _ (hE hn), finrank_eq_zero _ ((hE hn).trans le_sup_left), mul_zero]
  have : ∀ n, FiniteDimensional K (E n) := fun n ↦ not_not.mp (fun hn ↦ hInf ⟨n, hn⟩)
  let f (n : ℕ) := (E n).relfinrank (E n ⊔ M)
  have hanti : Antitone f := fun i j h ↦
    relfinrank_sup_le_of_le (hE h)
      (Nat.pos_of_dvd_of_pos ((E i).relfinrank_dvd_finrank_bot (E j)) Module.finrank_pos)
  let he : ∃ c : ℕ, c ∈ Set.range f := ⟨f 0, 0, rfl⟩
  obtain ⟨n₀, hn₀⟩ := Nat.find_spec he
  have h₀ (n : ℕ) (hn : n₀ ≤ n) : f n = f n₀ :=
    (hanti hn).antisymm (hn₀ ▸ Nat.find_min' he (Set.mem_range_self n))
  have hdeg (n : ℕ) : Module.finrank K ↥(E n ⊔ M) = Module.finrank K (E n) * f n :=
    (finrank_bot_mul_relfinrank le_sup_left).symm
  have hpos : 1 ≤ f n₀ := by
    have hdim := Module.finrank_pos (R := K) (M := ↥(E n₀ ⊔ M))
    by_contra! hn
    have hz : f n₀ = 0 := Nat.lt_one_iff.mp hn
    simp [hdeg, hz] at hdim
  have hbound : f n₀ ≤ Module.finrank K M := by
    refine (relfinrank_sup_le_of_le (M := M) (bot_le : ⊥ ≤ E n₀) ?_).trans_eq ?_
    · simpa using (Module.finrank_pos : 0 < Module.finrank K (E n₀))
    · simp
  exact ⟨f n₀, hpos, hbound, n₀, fun n hn ↦ by rw [hdeg, h₀ n hn, mul_comm]⟩

end IntermediateField
