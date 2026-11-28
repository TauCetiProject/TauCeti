/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Haar.Basic
import Mathlib.Algebra.Group.Pi.Units
import TauCeti.Algebra.Order.BigOperators.Ring.Multiset
import TauCeti.NumberTheory.LocalField.Topology

/-!
# Additive Haar volume of nonunits in products of local integer rings

In a finite product of nonarchimedean local fields, give each integer ring additive volume one.
The volume of the nonunits in the product of the integer rings is one minus the product of the
local unit volumes. In particular it is bounded above by the sum of the inverse residue-field
sizes. This gives a uniform estimate for the loss from restricting an integral to integral units
at a finite set of places.

The chosen-place application is the volume estimate of
`New.Filling.volume_integers_diff_intUnits_le` in `grh-lean`,
`grh/src/New/Spanning/Frames/FixedLines.lean`, revision `72fead1`.
-/

public section

open MeasureTheory Set ValuativeRel
open scoped ENNReal

namespace TauCeti

variable {ι : Type*} (K : ι → Type*) [∀ i, Field (K i)] [∀ i, ValuativeRel (K i)]

/-- The nonunits of a product of valuation rings, viewed in the product of the ambient fields,
are the integral tuples outside the product of the local unit spheres. -/
theorem image_pi_integer_nonunits :
    (fun x : ∀ i, 𝒪[K i] ↦ fun i ↦ (x i : K i)) '' {x | ¬ IsUnit x} =
      univ.pi (fun i ↦ (𝒪[K i] : Set (K i))) \
        univ.pi (fun i ↦ {x : K i | valuation (K i) x = 1}) := by
  have hunit (x : ∀ i, 𝒪[K i]) : IsUnit x ↔ ∀ i, valuation (K i) (x i : K i) = 1 := by
    rw [Pi.isUnit_iff]
    exact forall_congr' fun i ↦
      (Valuation.valuationSubring.integers (valuation (K i))).isUnit_iff_valuation_eq_one
  ext x
  simp only [mem_image, mem_ofPred_eq, mem_sdiff, mem_univ_pi]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨fun i ↦ (y i).property, fun h ↦ hy ((hunit y).mpr h)⟩
  · rintro ⟨hx, h⟩
    exact ⟨fun i ↦ ⟨x i, hx i⟩, fun hu ↦ h ((hunit _).mp hu), rfl⟩

variable [Fintype ι] [∀ i, TopologicalSpace (K i)] [∀ i, IsNonarchimedeanLocalField (K i)]
  [∀ i, MeasurableSpace (K i)] [∀ i, BorelSpace (K i)]

variable {K} in
/-- A translation-invariant measure on a finite product of nonarchimedean local fields is the
product of the normalized local additive Haar measures exactly when the product of the integer
rings has mass one. -/
theorem _root_.MeasureTheory.Measure.eq_pi_localAddHaar_iff (μ : Measure (∀ i, K i))
    [μ.IsAddLeftInvariant] :
    μ = Measure.pi (fun i ↦ localAddHaar (K i)) ↔
      μ (univ.pi fun i ↦ (𝒪[K i] : Set (K i))) = 1 := by
  let ν := Measure.pi fun i ↦ localAddHaar (K i)
  let S := univ.pi fun i ↦ (𝒪[K i] : Set (K i))
  have hν : ν S = 1 := by simp [ν, S, Measure.pi_pi]
  refine ⟨fun h ↦ h.symm ▸ hν, fun hμ ↦ ?_⟩
  have hcompact : IsCompact S := isCompact_univ_pi fun i ↦ by
    rw [← coe_integerPositiveCompacts]
    exact (integerPositiveCompacts (K i)).isCompact
  have hpos : (interior S).Nonempty := by
    have hopen : IsOpen (univ.pi fun i ↦ interior (𝒪[K i] : Set (K i))) :=
      isOpen_set_pi finite_univ fun _ _ ↦ isOpen_interior
    refine (univ_pi_nonempty_iff.mpr fun i ↦ ?_).mono
      (interior_maximal (pi_mono fun _ _ ↦ interior_subset) hopen)
    rw [← coe_integerPositiveCompacts]
    exact (integerPositiveCompacts (K i)).interior_nonempty
  have hμS : μ S = 1 := hμ
  let _ := Measure.isAddHaarMeasure_of_isCompact_nonempty_interior μ S hcompact hpos
    (by simp [hμS]) (by simp [hμS])
  let S₀ : TopologicalSpace.PositiveCompacts (∀ i, K i) := ⟨⟨S, hcompact⟩, hpos⟩
  calc
    μ = Measure.addHaarMeasure S₀ := ((Measure.addHaarMeasure_eq_iff S₀ μ).mpr hμS).symm
    _ = ν := (Measure.addHaarMeasure_eq_iff S₀ ν).mpr hν

/-- The normalized additive Haar volume of the nonunits of a finite product of local integer
rings is one minus the product of the local unit volumes. -/
theorem pi_localAddHaar_nonunits :
    (Measure.pi fun i ↦ localAddHaar (K i))
      ((fun x : ∀ i, 𝒪[K i] ↦ fun i ↦ (x i : K i)) '' {x | ¬ IsUnit x}) =
      1 - ∏ i, (1 - (Nat.card 𝓀[K i] : ℝ≥0∞)⁻¹) := by
  have hsub : univ.pi (fun i ↦ {x : K i | valuation (K i) x = 1}) ⊆
      univ.pi (fun i ↦ (𝒪[K i] : Set (K i))) := fun x hx ↦ mem_univ_pi.mpr fun i ↦
    (Valuation.mem_valuationSubring_iff (valuation (K i)) (x i)).mpr ((mem_univ_pi.mp hx i).le)
  have htop : (Measure.pi fun i ↦ localAddHaar (K i))
      (univ.pi (fun i ↦ (𝒪[K i] : Set (K i)))) = 1 := by simp [Measure.pi_pi]
  rw [image_pi_integer_nonunits, measure_sdiff hsub
    (MeasurableSet.univ_pi fun _ ↦ measurableSet_setOf_valuation_eq_one).nullMeasurableSet
    (ne_top_of_le_ne_top (by simp [htop]) (measure_mono hsub)), htop, Measure.pi_pi]
  simp

/-- The inverse residue-field sizes bound the additive Haar volume of nonunits in a finite
product of local integer rings. -/
theorem pi_localAddHaar_nonunits_le :
    (Measure.pi fun i ↦ localAddHaar (K i))
      ((fun x : ∀ i, 𝒪[K i] ↦ fun i ↦ (x i : K i)) '' {x | ¬ IsUnit x}) ≤
      ∑ i, (Nat.card 𝓀[K i] : ℝ≥0∞)⁻¹ := by
  let p (i : ι) : ℝ≥0∞ := (Nat.card 𝓀[K i] : ℝ≥0∞)⁻¹
  suffices 1 - ∏ i, (1 - p i) ≤ ∑ i, p i by
    simpa only [pi_localAddHaar_nonunits, p] using this
  have hp (i : ι) : p i ≤ 1 := by
    rw [← inv_one (G := ℝ≥0∞), ENNReal.inv_le_inv]
    exact_mod_cast Nat.card_pos (α := 𝓀[K i])
  have hpfin (i : ι) : p i ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (hp i)
  have hprod : ∏ i, (1 - p i) ≤ 1 :=
    Finset.prod_le_one (fun _ _ ↦ tsub_le_self)
  refine (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
    (ENNReal.sum_ne_top.mpr fun i _ ↦ hpfin i)).mp ?_
  simp only [ENNReal.toReal_sub_of_le hprod ENNReal.one_ne_top, ENNReal.toReal_prod,
    ENNReal.toReal_one, ENNReal.toReal_sub_of_le (hp _) ENNReal.one_ne_top,
    ENNReal.toReal_sum (fun i _ ↦ hpfin i)]
  let s := (Finset.univ : Finset ι).val.map (fun i ↦ (p i).toReal)
  have hs (t : ℝ) (ht : t ∈ s) : 0 ≤ t ∧ t ≤ 1 := by
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp ht
    exact ⟨ENNReal.toReal_nonneg, by simpa using ENNReal.toReal_mono ENNReal.one_ne_top (hp i)⟩
  simpa only [s, Multiset.map_map, Function.comp_def, Finset.prod_map_val,
    Finset.sum_map_val] using
      Multiset.one_sub_prod_map_one_sub_le_sum (fun t ht ↦ (hs t ht).1) (fun t ht ↦ (hs t ht).2)

/-- If there are at most `b` local factors and each residue field has at least `b ^ (n + 1)`
elements, the nonunits of the product of the integer rings have additive Haar volume at most
`1 / b ^ n`. In particular, the exponent is nine when the residue bound is `b ^ 10`. -/
theorem pi_localAddHaar_nonunits_le_inv_pow {b n : ℕ} (hcard : Fintype.card ι ≤ b)
    (hres : ∀ i, b ^ (n + 1) ≤ Nat.card 𝓀[K i]) :
    (Measure.pi fun i ↦ localAddHaar (K i))
      ((fun x : ∀ i, 𝒪[K i] ↦ fun i ↦ (x i : K i)) '' {x | ¬ IsUnit x}) ≤
      ((b : ℝ≥0∞) ^ n)⁻¹ := by
  refine (pi_localAddHaar_nonunits_le K).trans ?_
  by_cases hb : b = 0
  · have hi : IsEmpty ι := Fintype.card_eq_zero_iff.mp (by omega)
    simp [Finset.univ_eq_empty]
  calc
    _ ≤ ∑ _ : ι, ((b : ℝ≥0∞) ^ (n + 1))⁻¹ := by
      gcongr with i
      exact_mod_cast hres i
    _ = (Fintype.card ι : ℝ≥0∞) * ((b : ℝ≥0∞) ^ (n + 1))⁻¹ := by simp
    _ ≤ (b : ℝ≥0∞) * ((b : ℝ≥0∞) ^ (n + 1))⁻¹ := by gcongr
    _ = _ := by
      have hb' : (b : ℝ≥0∞) ≠ 0 := by exact_mod_cast hb
      rw [pow_succ, ENNReal.mul_inv (by simp) (Or.inr hb'), ← mul_assoc,
        mul_comm (b : ℝ≥0∞), mul_assoc, ENNReal.mul_inv_cancel hb' (by simp), mul_one]

end TauCeti
